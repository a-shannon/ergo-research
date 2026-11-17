//! Native inputs for bounded N=3073 owner assembly.
//! This module does not authenticate the prefix or claim proof of work.
use crate::{
    daa_history_roster::{DaaHistoryRoster, BANKS},
    sparse::Term,
    work_tree_fixed_hash as fixed,
    work_tree_history_plan::WorkTreeHistoryPlan,
    work_tree_layout::{self as layout, WIDTH},
    work_tree_leaf_hash as leaf, work_tree_work as work,
};
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use blake2::{digest::consts::U32, Blake2b, Digest};
use num_bigint::BigUint;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::OnceLock;
#[cfg(test)]
#[path = "packed_owner_assembly_c442_tests.rs"]
mod c442_tests;
#[cfg(test)]
#[path = "packed_owner_assembly_c443_tests.rs"]
mod c443_tests;
#[cfg(test)]
#[path = "packed_owner_assembly_c449_tests.rs"]
mod c449_tests;

#[cfg(test)]
mod c450_mixed_tests {
    use super::*;
    use crate::daa_history_roster::OwnerClass;

    fn route() -> MixedMapHeaderRoute {
        MixedMapHeaderRoute {
            owner:C450_MIXED_OWNER,class:OwnerClass::Carry,
            plan_headers:crate::bank53_map::BANK53_N,plan_slot_log:21,plan_slots:1<<21,
            input_header_count:C449_PADDING_OWNER,has_max_adapter:false,
            padding_capture:false,exact_map_pair:true,has_other_source:false,
        }
    }

    fn synthetic_lease() -> Result<(HeaderSourceBinding,Eligible08MapPairLease),String> {
        let binding=HeaderSourceBinding::diagnostic_for_test(C450_MIXED_OWNER);
        let maps=H21EligibleMapStage::source_maps()?;
        let lease=Eligible08MapPairLease::synthetic_valid_for_test(
            binding.clone(),C450_MIXED_OWNER,OwnerClass::Carry,maps,
        )?;
        Ok((binding,lease))
    }

    fn expect_error<T>(result:Result<T,String>,expected:&str) {
        assert_eq!(result.err().as_deref(),Some(expected));
    }

    fn rows_with_actual_mixed_claims(
        binding:&HeaderSourceBinding,lease:&Eligible08MapPairLease,
    )->Result<OwnedRows,String> {
        let selection=OwnerSelection::Single {
            owner:C450_MIXED_OWNER,class:OwnerClass::Carry,
        };
        let mut rows=OwnedRows::new(selection);
        rows.begin_mixed_map_header_capture(binding.clone())?;
        for context in 0..BANK53_CONTEXTS {
            for offset in 0..BANK53_CONTEXT_BITS {
                match crate::bank53_required_writer::required_bank53_writer(
                    C450_MIXED_OWNER,context,offset).map_err(|error|error.to_string())? {
                    crate::bank53_required_writer::RequiredWriter::HeaderZero => {
                        let local=BANK53_BASE+context*BANK53_CONTEXT_BITS+offset;
                        rows.claim_header_seed(C450_MIXED_OWNER,local,Fr::zero())?;
                    }
                    crate::bank53_required_writer::RequiredWriter::Map { context: expected }
                        if expected==context && offset<BANK53_MAP_LIVE_BITS => {}
                    _=>return Err("C450 test unexpected required writer".into()),
                }
            }
        }
        claim_map_pair_live(&mut rows,lease,binding,C450_MIXED_OWNER,OwnerClass::Carry)?;
        Ok(rows)
    }

    fn synthetic_packed_row(
        binding:&HeaderSourceBinding,rows:&OwnedRows,
    )->Result<NativePackedRow,String> {
        Ok(NativePackedRow {
            owner:C450_MIXED_OWNER,class:OwnerClass::Carry,
            root:binding.root,total:binding.total,bytes:rows.bytes(0)?,
            header_source_binding:Some(binding.clone()),cap0_source:None,cap1_source:None,
            max_binding:None,map_binding:None,map_context:None,
            #[cfg(test)] legacy_binding:None,
        })
    }

    fn synthetic_parts(
        binding:&HeaderSourceBinding,lease:&Eligible08MapPairLease,
    )->Result<(NativePackedRow,MixedMapHeaderCapture),String> {
        let mut rows=rows_with_actual_mixed_claims(binding,lease)?;
        let row=synthetic_packed_row(binding,&rows)?;
        let capture=rows.finish_mixed_map_header_capture(&row)?;
        Ok((row,capture))
    }

    fn synthetic_row<'m>(
        binding:&HeaderSourceBinding,lease:&'m Eligible08MapPairLease,
    )->Result<NativeMixedMapHeaderRow<'m>,String> {
        let (row,capture)=synthetic_parts(binding,lease)?;
        NativeMixedMapHeaderRow::from_producer(row,capture,binding.clone(),lease)
    }

    #[test]
    fn c450_mixed_actual_claim_paths_finish_and_mint_same_row_receipt() {
        let (binding,lease)=synthetic_lease().unwrap();
        let token=synthetic_row(&binding,&lease).unwrap();
        token.validate_all(&binding).unwrap();
        assert_eq!(token.capture.claims.iter().filter(|claim|
            claim.is_some_and(|claim|claim.author==MixedMapHeaderAuthor::Map)).count(),
            2*BANK53_MAP_LIVE_BITS);
        assert_eq!(token.capture.claims.iter().filter(|claim|
            claim.is_some_and(|claim|claim.author==MixedMapHeaderAuthor::HeaderSeed)).count(),
            2*(BANK53_CONTEXT_BITS-BANK53_MAP_LIVE_BITS));
    }

    #[test]
    fn c450_mixed_finish_rejects_incomplete_and_extra_capture_coverage() {
        let (binding,lease)=synthetic_lease().unwrap();
        let mut missing=rows_with_actual_mixed_claims(&binding,&lease).unwrap();
        missing.mixed_map_header_capture.as_mut().unwrap().claims.pop();
        let row=synthetic_packed_row(&binding,&missing).unwrap();
        assert_eq!(missing.finish_mixed_map_header_capture(&row).err().as_deref(),
            Some("C450 mixed final row/binding/class geometry"),"short capture coverage");

        let mut extra=rows_with_actual_mixed_claims(&binding,&lease).unwrap();
        extra.mixed_map_header_capture.as_mut().unwrap().claims.push(None);
        let row=synthetic_packed_row(&binding,&extra).unwrap();
        assert_eq!(extra.finish_mixed_map_header_capture(&row).err().as_deref(),
            Some("C450 mixed final row/binding/class geometry"),"extra capture coverage");
    }

    #[test]
    fn c450_mixed_actual_writer_rejects_header_map_boundary_and_bad_context() {
        let (binding,lease)=synthetic_lease().unwrap();
        let mut rows=OwnedRows::new(OwnerSelection::Single {
            owner:C450_MIXED_OWNER,class:OwnerClass::Carry,
        });
        rows.begin_mixed_map_header_capture(binding.clone()).unwrap();
        let last_map=BANK53_BASE+BANK53_MAP_LIVE_BITS-1;
        let first_header_zero=BANK53_BASE+BANK53_MAP_LIVE_BITS;
        assert_eq!(rows.claim_header_seed(C450_MIXED_OWNER,last_map,Fr::zero()).err().as_deref(),
            Some("C450 HEADER claim on non-HEADER cell wire677500"),
            "HEADER seeder cannot claim Map offset 5756");
        rows.record_mixed_map_claim(C450_MIXED_OWNER,last_map,false)
            .expect("Map capture accepts offset 5756");
        assert_eq!(rows.record_mixed_map_claim(C450_MIXED_OWNER,first_header_zero,false)
            .err().as_deref(),Some("C450 Map claim on non-Map cell wire677501"),
            "Map writer cannot claim HeaderZero offset 5757");
        rows.claim_header_seed(C450_MIXED_OWNER,first_header_zero,Fr::zero())
            .expect("HEADER seeder accepts offset 5757 once");
        assert_eq!(rows.claim_header_seed(C450_MIXED_OWNER,first_header_zero,Fr::zero())
            .unwrap_err(),"C450 exclusive claim overlaps mixed source wire677501",
            "duplicate HEADER-zero seed at offset 5757");

        let context_one_last_map=BANK53_BASE+BANK53_CONTEXT_BITS+BANK53_MAP_LIVE_BITS-1;
        let context_one_first_zero=BANK53_BASE+BANK53_CONTEXT_BITS+BANK53_MAP_LIVE_BITS;
        assert_eq!(rows.claim_header_seed(C450_MIXED_OWNER,context_one_last_map,Fr::zero())
            .err().as_deref(),Some("C450 HEADER claim on non-HEADER cell wire685692"),
            "context 1 HEADER cannot claim Map offset 5756");
        rows.record_mixed_map_claim(C450_MIXED_OWNER,context_one_last_map,false)
            .expect("context 1 Map capture accepts offset 5756");
        assert_eq!(rows.record_mixed_map_claim(C450_MIXED_OWNER,context_one_first_zero,false)
            .err().as_deref(),Some("C450 Map claim on non-Map cell wire685693"),
            "context 1 Map cannot claim HeaderZero offset 5757");
        rows.claim_header_seed(C450_MIXED_OWNER,context_one_first_zero,Fr::zero())
            .expect("context 1 HEADER accepts offset 5757");
        assert_eq!(rows.claim_header_seed(C450_MIXED_OWNER,context_one_first_zero,Fr::zero())
            .unwrap_err(),"C450 exclusive claim overlaps mixed source wire685693",
            "context 1 duplicate HEADER-zero seed");

        let mut wrong_context=lease.clone();
        wrong_context.swap_cell_contexts_for_test();
        let mut fresh=OwnedRows::new(OwnerSelection::Single {
            owner:C450_MIXED_OWNER,class:OwnerClass::Carry,
        });
        fresh.begin_mixed_map_header_capture(binding.clone()).unwrap();
        assert_eq!(claim_map_pair_live(&mut fresh,&wrong_context,&binding,
            C450_MIXED_OWNER,OwnerClass::Carry).unwrap_err(),
            "C438 Map pair ordered live cell/domain/Boolean","Map context substitution");
        assert_eq!(fresh.claimed[0].iter().filter(|claimed|**claimed).count(),0,
            "context failure precedes Map mutation");
    }

    #[test]
    fn c450_mixed_receipt_rejects_a_substituted_map_lease() {
        let (binding,lease)=synthetic_lease().unwrap();
        let (row,capture)=synthetic_parts(&binding,&lease).unwrap();
        let wrong_binding=binding.mutated_field_for_test(0);
        let maps=H21EligibleMapStage::source_maps().unwrap();
        let wrong_lease=Eligible08MapPairLease::synthetic_valid_for_test(
            wrong_binding,C450_MIXED_OWNER,OwnerClass::Carry,maps,
        ).unwrap();
        assert_eq!(NativeMixedMapHeaderRow::from_producer(
            row,capture,binding,&wrong_lease,
        ).err().as_deref(),Some("C450 mixed receipt owner/class/parent binding"),
        "substituted parent-bound Map lease");
    }

    #[test]
    fn c450_mixed_route_fails_closed_by_owner_class_and_route() {
        assert!(require_mixed_map_header_route(&route()).is_ok());
        let mut bad=route();bad.owner-=1;
        expect_error(require_mixed_map_header_route(&bad),
            "C450 mixed capture requires isolated owner845760 Carry/Map route");
        let mut bad=route();bad.class=OwnerClass::FixedV2;
        expect_error(require_mixed_map_header_route(&bad),
            "C450 mixed capture requires isolated owner845760 Carry/Map route");
        let mut bad=route();bad.plan_headers-=1;
        expect_error(require_mixed_map_header_route(&bad),
            "C450 mixed capture requires isolated owner845760 Carry/Map route");
        let mut bad=route();bad.plan_slot_log-=1;
        expect_error(require_mixed_map_header_route(&bad),
            "C450 mixed capture requires isolated owner845760 Carry/Map route");
        let mut bad=route();bad.plan_slots-=1;
        expect_error(require_mixed_map_header_route(&bad),
            "C450 mixed capture requires isolated owner845760 Carry/Map route");
        let mut bad=route();bad.input_header_count-=1;
        expect_error(require_mixed_map_header_route(&bad),
            "C450 mixed capture requires isolated owner845760 Carry/Map route");
        let mut bad=route();bad.has_max_adapter=true;
        expect_error(require_mixed_map_header_route(&bad),
            "C450 mixed capture requires isolated owner845760 Carry/Map route");
        let mut bad=route();bad.padding_capture=true;
        expect_error(require_mixed_map_header_route(&bad),
            "C450 mixed capture requires isolated owner845760 Carry/Map route");
        let mut bad=route();bad.exact_map_pair=false;
        expect_error(require_mixed_map_header_route(&bad),
            "C450 mixed capture requires isolated owner845760 Carry/Map route");
        let mut bad=route();bad.has_other_source=true;
        expect_error(require_mixed_map_header_route(&bad),
            "C450 mixed capture requires isolated owner845760 Carry/Map route");
    }

    #[test]
    fn c450_mixed_capture_rejects_missing_duplicate_wrong_author_and_nonzero_claims() {
        let (binding,lease)=synthetic_lease().unwrap();
        let mut rows=rows_with_actual_mixed_claims(&binding,&lease).unwrap();
        let header_local=BANK53_BASE+BANK53_MAP_LIVE_BITS;
        expect_error(rows.claim_header_seed(C450_MIXED_OWNER,header_local,Fr::zero()),
            "C450 exclusive claim overlaps mixed source wire677501");
        expect_error(rows.record_mixed_map_claim(C450_MIXED_OWNER,BANK53_BASE,false),
            "C450 duplicate mixed source claim wire671744");

        let mut token=synthetic_row(&binding,&lease).unwrap();
        token.capture.claims[BANK53_MAP_LIVE_BITS]=None;
        expect_error(token.validate_all(&binding),"C450 mixed full source claim absent wire677501");
        let mut token=synthetic_row(&binding,&lease).unwrap();
        token.capture.claims[BANK53_MAP_LIVE_BITS]=Some(MixedMapHeaderClaim {
            author:MixedMapHeaderAuthor::Map,value:false,
        });
        expect_error(token.validate_all(&binding),"C450 mixed full HEADER-zero mismatch wire677501");
        let mut token=synthetic_row(&binding,&lease).unwrap();
        token.capture.claims[BANK53_MAP_LIVE_BITS]=Some(MixedMapHeaderClaim {
            author:MixedMapHeaderAuthor::HeaderSeed,value:true,
        });
        expect_error(token.validate_all(&binding),"C450 mixed full HEADER-zero mismatch wire677501");
    }

    #[test]
    fn c450_mixed_capture_rejects_map_value_and_final_bit_mutants() {
        let (binding,lease)=synthetic_lease().unwrap();
        let mut token=synthetic_row(&binding,&lease).unwrap();
        token.capture.claims[0]=Some(MixedMapHeaderClaim {
            author:MixedMapHeaderAuthor::Map,value:true,
        });
        expect_error(token.validate_all(&binding),"C450 mixed full Map source mismatch wire671744");

        let mut token=synthetic_row(&binding,&lease).unwrap();
        token.row.bytes[BANK53_BASE/8]^=1<<(BANK53_BASE%8);
        expect_error(token.validate_all(&binding),"C450 mixed full Map source mismatch wire671744");

        let mut token=synthetic_row(&binding,&lease).unwrap();
        let zero_local=BANK53_BASE+BANK53_MAP_LIVE_BITS;
        token.row.bytes[zero_local/8]^=1<<(zero_local%8);
        expect_error(token.validate_all(&binding),"C450 mixed full HEADER-zero mismatch wire677501");
    }

    #[test]
    fn c450_mixed_capture_rejects_map_header_overlap_and_binding_mutants() {
        let (binding,lease)=synthetic_lease().unwrap();
        let mut token=synthetic_row(&binding,&lease).unwrap();
        token.capture.claims[0]=Some(MixedMapHeaderClaim {
            author:MixedMapHeaderAuthor::HeaderSeed,value:false,
        });
        expect_error(token.validate_all(&binding),"C450 mixed full Map source mismatch wire671744");

        let mut token=synthetic_row(&binding,&lease).unwrap();
        token.capture.claims[BANK53_MAP_LIVE_BITS]=Some(MixedMapHeaderClaim {
            author:MixedMapHeaderAuthor::Map,value:false,
        });
        expect_error(token.validate_all(&binding),"C450 mixed full HEADER-zero mismatch wire677501");

        let mut token=synthetic_row(&binding,&lease).unwrap();
        token.capture.claims[0]=None;
        expect_error(token.validate_all(&binding),"C450 mixed full source claim absent wire671744");

        for field in 0..6 {
            let token=synthetic_row(&binding,&lease).unwrap();
            let wrong=binding.mutated_field_for_test(field);
            expect_error(token.validate_all(&wrong),"C450 mixed read parent binding mismatch");
        }
    }

    #[test]
    fn c450_mixed_receipt_rejects_owner_and_class_substitution() {
        let (binding,lease)=synthetic_lease().unwrap();
        let mut token=synthetic_row(&binding,&lease).unwrap();
        token.row.owner+=1;
        expect_error(token.validate_all(&binding),
            "native packed ROW source root/total/profile/cut/layout/owner/class");
        let mut token=synthetic_row(&binding,&lease).unwrap();
        token.row.class=OwnerClass::Padding;
        expect_error(token.validate_all(&binding),
            "native packed ROW source root/total/profile/cut/layout/owner/class");
    }

    #[test]
    fn c450_mixed_rows_reject_later_equal_value_overlaps() {
        let owner=C450_MIXED_OWNER;
        let (binding,lease)=synthetic_lease().unwrap();
        let selection=OwnerSelection::Single { owner,class:OwnerClass::Carry };
        let mut header_rows=OwnedRows::new(selection);
        header_rows.begin_mixed_map_header_capture(binding.clone()).unwrap();
        let header_local=BANK53_BASE+BANK53_MAP_LIVE_BITS;
        header_rows.claim_header_seed(owner,header_local,Fr::zero()).unwrap();
        expect_error(header_rows.claim(owner,header_local,Fr::zero()),
            "C450 later claim overlaps mixed source wire677501");
        expect_error(header_rows.claim_exclusive(owner,header_local,Fr::zero()),
            "C450 exclusive claim overlaps mixed source wire677501");

        let mut map_rows=rows_with_actual_mixed_claims(&binding,&lease).unwrap();
        expect_error(map_rows.claim(owner,BANK53_BASE,Fr::zero()),
            "C450 later claim overlaps mixed source wire671744");
        expect_error(map_rows.claim_exclusive(owner,BANK53_BASE,Fr::zero()),
            "C450 exclusive claim overlaps mixed source wire671744");
    }
}

// C512e: source-only geometry and claim-path falsifier. This does not mint a
// regular-owner author census or admit the packed row into common X.
#[cfg(test)]
mod c512e_regular_owner_author_partition_tests {
    use super::*;
    use std::ops::Range;

    const OWNER: usize = 845_887;
    const HEADER: u8 = 0;
    const TREE: u8 = 1;
    const DAA: u8 = 2;
    const SCORED: u8 = 3;
    const ABSENT: u8 = 255;

    fn mark(tags: &mut [u8], range: Range<usize>, author: u8) -> Result<(), String> {
        if range.start >= range.end || range.end > tags.len() {
            return Err("C512e author domain outside owner row".into());
        }
        for local in range {
            if tags[local] != HEADER {
                return Err(format!("C512e author domain overlaps wire{local}"));
            }
            tags[local] = author;
        }
        Ok(())
    }

    fn fixed_partition(plan: &WorkTreeHistoryPlan) -> Result<(Vec<u8>, [usize; 4]), String> {
        let tree = plan.physical_assignment_replacement_mask(OWNER as u64)?;
        let score = h21_eligible_context::Eligible08RegularScoreOwner::classify(OWNER)?;
        if tree.len() != WIDTH || score.active() != [true, true]
            || score.typed_cell_count() != 20_480
            || crate::h21_scheduled_max_cap::Plan::eligible08().max_calendar()
                .iter().any(|(owner, _)| *owner == OWNER)
        {
            return Err("C512e exact regular owner, tree width or MAX calendar".into());
        }
        let mut tags = vec![HEADER; WIDTH];
        for (wire, replaced) in tree.into_iter().enumerate() {
            if replaced { tags[wire] = TREE; }
        }
        for &(start, end) in &BANKS {
            mark(&mut tags, start..end, DAA)?;
        }
        for context in 0..2 {
            for range in [
                H21EligibleMapStage::map_live(context)?,
                H21EligibleMapStage::score_live(context)?,
                H21EligibleMapStage::slack_live(context)?,
                H21EligibleMapStage::cap_live(context)?,
            ] {
                mark(&mut tags, range, SCORED)?;
            }
        }
        if tags[crate::segment_points::POINT_OFFSET
            ..crate::segment_points::POINT_OFFSET + crate::point_membership::POINT_WIDTH]
            .iter().any(|author| *author != HEADER)
            || tags[999_424..1_000_770].iter().any(|author| *author != HEADER)
        {
            return Err("C512e Point or unscheduled MAX lost HEADER author".into());
        }
        let mut counts = [0usize; 4];
        for &author in &tags {
            counts[usize::from(author)] += 1;
        }
        if counts != [544_814, 401_362, 81_920, 20_480] {
            return Err(format!("C512e exact regular physical partition {counts:?}"));
        }
        Ok((tags, counts))
    }

    fn require_author_records(expected: &[u8], observed: &[u8]) -> Result<(), String> {
        if expected.len() != WIDTH || observed.len() != WIDTH {
            return Err("C512e complete regular author record width".into());
        }
        for (wire, (&wanted, &found)) in expected.iter().zip(observed).enumerate() {
            if found == ABSENT || found != wanted {
                return Err(format!("C512e missing or wrong author wire{wire}"));
            }
        }
        Ok(())
    }

    #[test]
    fn c512e_no_frame_four_author_shape_and_zero_claim_hazards() {
        use h21_eligible_context::ScoredOwnerPackedCell;
        let plan = WorkTreeHistoryPlan::compile(
            1_827_840, 21, [0x5a; 32], [0x42; 28],
        ).unwrap();
        let (expected, counts) = fixed_partition(&plan).unwrap();
        assert_eq!(counts.iter().sum::<usize>(), WIDTH);
        let point = crate::segment_points::POINT_OFFSET;
        let max0 = 999_424;
        let max1 = 1_000_097;
        let score = H21EligibleMapStage::score_live(0).unwrap().start;
        assert_eq!((expected[point], expected[max0], expected[max1], expected[score]),
            (HEADER, HEADER, HEADER, SCORED));

        // A zero bit still needs a claim. These records are synthetic and do
        // not stand in for claims captured from the native producer.
        let mut observed = expected.clone();
        require_author_records(&expected, &observed).unwrap();
        for wire in [point, max0, max1] {
            observed[wire] = ABSENT;
            assert!(require_author_records(&expected, &observed).is_err());
            observed[wire] = HEADER;
        }
        observed[score] = DAA;
        assert!(require_author_records(&expected, &observed).is_err());

        // The current generic claim path accepts an equal-zero repetition;
        // a future regular-owner recorder must use exclusive claim semantics.
        let selection = OwnerSelection::Single {
            owner: OWNER, class: crate::daa_history_roster::OwnerClass::Carry,
        };
        let mut ordinary = OwnedRows::new(selection);
        ordinary.claim(OWNER, point, Fr::zero()).unwrap();
        ordinary.claim(OWNER, point, Fr::zero()).unwrap();
        let mut exclusive = OwnedRows::new(selection);
        exclusive.claim_exclusive(OWNER, point, Fr::zero()).unwrap();
        assert!(exclusive.claim_exclusive(OWNER, point, Fr::zero()).is_err());

        let wrong = ScoredOwnerPackedCell::synthetic_for_test(
            OWNER * WIDTH + score,
            ScoredOwnerPackedAuthor::Cap { context: 0, origin: OWNER + 1 },
            false,
        );
        assert!(scored_owner_cell_local(OWNER, &wrong).is_err());
    }

    #[test]
    fn c512e_actual_recorder_rejects_duplicate_zero_and_wrong_phase_no_frame() {
        use NativeRegularPhysicalAuthor::{Header, Tree, Daa, Scored};
        let selection = OwnerSelection::Single {
            owner: OWNER, class: crate::daa_history_roster::OwnerClass::Carry,
        };
        let mut rows = OwnedRows::new(selection);
        rows.begin_regular_author_census().unwrap();
        assert!(rows.author_census.is_none(), "C374 capture stays separate");
        assert!(rows.set_regular_author(Tree).is_err());
        rows.set_regular_author(Header).unwrap();
        assert!(rows.set_regular_author(Scored).is_err());

        let point = crate::segment_points::POINT_OFFSET;
        rows.claim_header_seed(OWNER, point, Fr::zero()).unwrap();
        assert!(rows.claim_header_seed(OWNER, point, Fr::zero()).is_err(),
            "a second HEADER claim of zero must fail");
        assert!(rows.claim(OWNER - 1, point + 1, Fr::zero()).is_err());
        assert!(rows.claim(OWNER, point + 1, Fr::from(2u64)).is_err());
        assert_eq!(rows.regular_author_census.as_ref().unwrap()[point], Some(Header));
        assert_eq!(rows.regular_author_census.as_ref().unwrap()[point + 1], None);

        rows.set_regular_author(Tree).unwrap();
        rows.claim(OWNER, 0, Fr::zero()).unwrap();
        rows.set_regular_author(Daa).unwrap();
        rows.claim_exclusive(OWNER, BANKS[0].0, Fr::zero()).unwrap();
        rows.set_regular_author(Scored).unwrap();
        let score = H21EligibleMapStage::score_live(0).unwrap().start;
        rows.claim_exclusive(OWNER, score, Fr::zero()).unwrap();
        assert!(rows.claim_exclusive(OWNER, score, Fr::zero()).is_err());
        assert!(rows.set_regular_author(Scored).is_err());
        assert!(rows.begin_author_census().is_err(),
            "C374 census may not mix after regular claims");
        let authors = rows.regular_author_census.as_ref().unwrap();
        assert_eq!((authors[point], authors[0], authors[BANKS[0].0], authors[score]),
            (Some(Header), Some(Tree), Some(Daa), Some(Scored)));

        let mut c374 = OwnedRows::new(OwnerSelection::Single {
            owner: 845_759, class: crate::daa_history_roster::OwnerClass::Carry,
        });
        assert!(c374.begin_regular_author_census().is_err());
        c374.begin_author_census().unwrap();
        c374.set_author(NativePhysicalAuthor::Header).unwrap();
    }

    #[test]
    fn c512e_sealed_bit_mismatch_revokes_complete_gate_no_frame() {
        let checked = Cell::new(true);
        let sealed = [0u8];
        let honest = [0u8];
        assert!(!NativeRegularOwnerAuthorCensus::checked_sealed_bit(
            &checked, &honest, &sealed, 0).unwrap());
        let substituted = [1u8];
        assert!(NativeRegularOwnerAuthorCensus::checked_sealed_bit(
            &checked, &substituted, &sealed, 0).is_err());
        assert!(!checked.get());
        // Both the C509 view and local checked-cell paths call this gate.
        assert!(NativeRegularOwnerAuthorCensus::require_complete_checked(&checked).is_err());
        assert!(NativeRegularOwnerAuthorCensus::checked_sealed_bit(
            &checked, &honest, &sealed, 0).is_err());
    }
}
#[cfg(test)]
mod c503_early_mixed_tests {
    use super::*;
    use crate::daa_history_roster::OwnerClass;
    use crate::header_daa_row_placement::{
        ActiveOperand, C503Bank53Read, C503EarlyCarryMapHeaderRow, OperandSide,
        Relation, RowPlan,
    };

    fn ordered_open_complement(
        operands:&[ActiveOperand], reads:&[C503Bank53Read],
    )->Result<Vec<ActiveOperand>,String> {
        let mut open=Vec::new();
        let mut read_index=0usize;
        for operand in operands {
            let Some(read)=reads.get(read_index) else {
                open.push(*operand);
                continue;
            };
            let claimed=read.operand;
            let claimed_precedes=claimed.occurrence<operand.occurrence
                || (claimed.occurrence==operand.occurrence
                    && matches!((claimed.side,operand.side),
                        (OperandSide::Left,OperandSide::Right)));
            let same_position=claimed.occurrence==operand.occurrence
                && claimed.side==operand.side;
            if same_position {
                if claimed!=*operand {
                    return Err("C503 complement read identity mismatch".into());
                }
                read_index+=1;
            } else if claimed_precedes {
                return Err("C503 complement has unmatched, duplicate, or reordered read".into());
            } else {
                open.push(*operand);
            }
        }
        if read_index!=reads.len() {
            return Err("C503 complement has extra retained read".into());
        }
        Ok(open)
    }

    fn fixture(owner: usize) -> Result<(HeaderSourceBinding, Eligible08MapPairLease), String> {
        let binding = HeaderSourceBinding::diagnostic_for_test(owner);
        let maps = H21EligibleMapStage::source_maps()?;
        let lease = Eligible08MapPairLease::synthetic_valid_for_test(
            binding.clone(), owner, OwnerClass::Carry, maps,
        )?;
        Ok((binding, lease))
    }

    fn claimed_rows(
        owner: usize, binding: &HeaderSourceBinding, lease: &Eligible08MapPairLease,
    ) -> Result<OwnedRows, String> {
        let mut rows = OwnedRows::new(OwnerSelection::Single {
            owner, class: OwnerClass::Carry,
        });
        rows.begin_mixed_map_header_capture(binding.clone())?;
        for context in 0..BANK53_CONTEXTS {
            for offset in 0..BANK53_CONTEXT_BITS {
                let writer = crate::bank53_required_writer::required_bank53_writer(
                    owner, context, offset).map_err(str::to_string)?;
                match writer {
                    crate::bank53_required_writer::RequiredWriter::HeaderZero => {
                        rows.claim_header_seed(
                            owner, BANK53_BASE + context * BANK53_CONTEXT_BITS + offset,
                            Fr::zero(),
                        )?;
                    }
                    crate::bank53_required_writer::RequiredWriter::Map { context: found }
                        if found == context => {}
                    _ => return Err("C503 fixture unexpected Bank53 writer".into()),
                }
            }
        }
        claim_map_pair_live(&mut rows, lease, binding, owner, OwnerClass::Carry)?;
        Ok(rows)
    }

    fn packed_row(owner: usize, binding: &HeaderSourceBinding, rows: &OwnedRows)
        -> Result<NativePackedRow, String> {
        Ok(NativePackedRow {
            owner, class: OwnerClass::Carry, root: binding.root,
            total: binding.total, bytes: rows.bytes(0)?,
            header_source_binding: Some(binding.clone()),
            cap0_source: None, cap1_source: None, max_binding: None,
            map_binding: None, map_context: None,
            legacy_binding: None,
        })
    }

    fn checked_fixture<'m>(owner: usize, binding: &HeaderSourceBinding,
        lease: &'m Eligible08MapPairLease) -> Result<NativeMixedMapHeaderRow<'m>, String> {
        let mut rows = claimed_rows(owner, binding, lease)?;
        let row = packed_row(owner, binding, &rows)?;
        let capture = rows.finish_mixed_map_header_capture(&row)?;
        NativeMixedMapHeaderRow::from_producer(row, capture, binding.clone(), lease)
    }

    #[test]
    fn c503_early_mixed_same_row_claims_and_nonzero_map_transfer_no_frame() {
        for owner in C503_EARLY_MIXED_OWNERS {
            let (binding, mut lease) = fixture(owner).unwrap();
            require_mixed_map_header_no_scheduled(owner, crate::daa_history_roster::OwnerClass::Carry).unwrap();
            lease.reseal_cell_value_for_test(0, 1).unwrap();
            let row = checked_fixture(owner, &binding, &lease).unwrap();
            row.validate_all(&binding).unwrap();
            assert!(row.read_map(&binding, 0, 0).unwrap(),
                "new Map bit may be one after old HEADER zero at owner {owner}");
            assert!(!row.read_header_zero(&binding, 0, BANK53_MAP_LIVE_BITS).unwrap());
            assert_eq!(row.capture.claims.iter().filter(|claim|
                claim.is_some_and(|claim| claim.author == MixedMapHeaderAuthor::Map)).count(),
                2 * BANK53_MAP_LIVE_BITS);
            assert_eq!(row.capture.claims.iter().filter(|claim|
                claim.is_some_and(|claim| claim.author == MixedMapHeaderAuthor::HeaderSeed)).count(),
                2 * (BANK53_CONTEXT_BITS - BANK53_MAP_LIVE_BITS));
        }
        assert!(mixed_map_header_class_allowed(844_675, crate::daa_history_roster::OwnerClass::Carry));
        assert!(mixed_map_header_class_allowed(2, crate::daa_history_roster::OwnerClass::Carry));
        assert!(mixed_map_header_class_allowed(C450_MIXED_OWNER, crate::daa_history_roster::OwnerClass::Carry));
        let schedule = mixed_map_header_schedule();
        for owner in [417_790, 845_758, 844_670] {
            assert!(crate::bank53_required_writer::require_ordinary_unscored_carry_map_header(
                owner, crate::daa_history_roster::OwnerClass::Carry, schedule,
            ).is_err(), "Score, Slack, or scheduled owner {owner} must stay excluded");
        }
        for class in [crate::daa_history_roster::OwnerClass::Genesis,
            crate::daa_history_roster::OwnerClass::Initial,
            crate::daa_history_roster::OwnerClass::FixedV2] {
            assert!(crate::bank53_required_writer::require_ordinary_unscored_carry_map_header(
                2, class, schedule,
            ).is_err(), "wrong class {class:?} must stay excluded");
        }
    }

    #[test]
    fn c503_early_mixed_preseed_rejects_one_old_value_mask_or_writer_fault() {
        for owner in C503_EARLY_MIXED_OWNERS {
            let (binding, lease) = fixture(owner).unwrap();
            let mut mask = vec![false; WIDTH];
            let mut native = vec![Fr::zero(); WIDTH];
            let mut reserved = preflight_map_pair_reservation(
                &lease, &binding, owner, OwnerClass::Carry, &mask).unwrap();
            preflight_mixed_map_header_seed(owner, OwnerClass::Carry, &mask, &native, &reserved).unwrap();
            native[BANK53_BASE] = Fr::one();
            assert!(preflight_mixed_map_header_seed(owner, OwnerClass::Carry, &mask, &native, &reserved)
                .unwrap_err().contains("old HEADER nonzero/replaced"));
            native[BANK53_BASE] = Fr::zero();
            preflight_mixed_map_header_seed(owner, OwnerClass::Carry, &mask, &native, &reserved).unwrap();
            let zero = BANK53_BASE + BANK53_MAP_LIVE_BITS;
            mask[zero] = true;
            assert!(preflight_mixed_map_header_seed(owner, OwnerClass::Carry, &mask, &native, &reserved)
                .unwrap_err().contains("old HEADER nonzero/replaced"));
            mask[zero] = false;
            reserved[zero] = true;
            assert!(preflight_mixed_map_header_seed(owner, OwnerClass::Carry, &mask, &native, &reserved)
                .unwrap_err().contains("writer/reservation"));
            reserved[zero] = false;
            preflight_mixed_map_header_seed(owner, OwnerClass::Carry, &mask, &native, &reserved).unwrap();
        }
    }

    #[test]
    fn c503_early_mixed_missing_duplicate_and_wrong_parent_reject_no_frame() {
        for owner in C503_EARLY_MIXED_OWNERS {
            let (binding, lease) = fixture(owner).unwrap();
            let clean = checked_fixture(owner, &binding, &lease).unwrap();
            clean.validate_all(&binding).unwrap();
            let first_score_zero = BANK53_BASE + BANK53_MAP_LIVE_BITS;
            let first_slack_zero = BANK53_BASE + 7_805;
            for local in [first_score_zero, first_slack_zero] {
                let mut rows = claimed_rows(owner, &binding, &lease).unwrap();
                assert!(rows.claim_header_seed(owner, local, Fr::zero())
                    .unwrap_err().contains("overlaps mixed source"));
                let mut rows = claimed_rows(owner, &binding, &lease).unwrap();
                rows.mixed_map_header_capture.as_mut().unwrap()
                    .claims[local - BANK53_BASE] = None;
                let row = packed_row(owner, &binding, &rows).unwrap();
                assert!(rows.finish_mixed_map_header_capture(&row)
                    .err().expect("missing HEADER claim must reject")
                    .contains("missing source claim"));
                checked_fixture(owner, &binding, &lease).unwrap()
                    .validate_all(&binding).unwrap();
            }
            assert!(clean.validate_all(&binding.mutated_field_for_test(0)).is_err());
            let other_owner = if owner == C503_EARLY_MIXED_OWNERS[0] {
                C503_EARLY_MIXED_OWNERS[1]
            } else { C503_EARLY_MIXED_OWNERS[0] };
            let (_, wrong_lease) = fixture(other_owner).unwrap();
            assert!(clean.read_map(wrong_lease.binding(), 0, 0).is_err());
        }
    }

    #[test]
    fn c503_early_row_join_preserves_source_order_and_open_reads_no_frame() {
        let plan = WorkTreeHistoryPlan::compile(
            1_827_840, 21, [0x52; 32], [0x53; 28],
        ).unwrap();
        let roster = crate::daa_history_roster::DaaHistoryRoster::compile(&plan).unwrap();
        let scheduled = crate::h21_scheduled_max_cap::Plan::eligible08();
        let row_plan = RowPlan::new(&roster, &scheduled).unwrap();
        for owner in C503_EARLY_MIXED_OWNERS {
            let binding = HeaderSourceBinding::for_plan(&plan, owner).unwrap();
            let lease = Eligible08MapPairLease::synthetic_valid_for_test(
                binding.clone(), owner, OwnerClass::Carry,
                H21EligibleMapStage::source_maps().unwrap(),
            ).unwrap();
            let receipt=checked_fixture(owner,&binding,&lease).unwrap();
            let mut joined=C503EarlyCarryMapHeaderRow::from_producer(&row_plan,receipt).unwrap();
            joined.validate().unwrap();
            assert!(joined.open_read_count() > 0,
                "non-Bank53 obligations must stay open");
            assert!(joined.bank53_reads().iter().any(|read|
                read.author == crate::header_daa_row_placement::C503Bank53Author::Map(0)));
            assert_eq!(joined.batch().owner(), owner);

            if owner==2 {
                let map0_author=crate::header_daa_row_placement::C503Bank53Author::Map(0);
                let map0_index=joined.bank53_reads().iter()
                    .position(|read|read.author==map0_author)
                    .expect("owner2 C503 row has an active Map0 read");
                let original=joined.bank53_reads()[map0_index];

                joined.bank53_reads_mut_for_test()[map0_index].author=
                    crate::header_daa_row_placement::C503Bank53Author::HeaderZero;
                let wrong_author=joined.bank53_reads()[map0_index];
                assert_eq!(wrong_author.author,
                    crate::header_daa_row_placement::C503Bank53Author::HeaderZero,
                    "wrong-author mutant must select HEADER-zero");
                assert_eq!(wrong_author.operand,original.operand,
                    "wrong-author mutant must preserve operand");
                assert_eq!(wrong_author.value,original.value,
                    "wrong-author mutant must preserve value");
                assert_eq!(joined.validate().unwrap_err(),
                    "C503 ROW missing/reordered/changed active read");
                joined.bank53_reads_mut_for_test()[map0_index]=original;
                joined.validate().unwrap();

                let replacement_wire=joined.bank53_reads().iter()
                    .find(|read|read.author==map0_author
                        && read.operand.wire!=original.operand.wire
                        && read.operand.relation==original.operand.relation
                        && read.value==original.value)
                    .map(|read|read.operand.wire)
                    .expect("owner2 C503 row has a same-class Map0 coordinate");
                joined.bank53_reads_mut_for_test()[map0_index].operand.wire=replacement_wire;
                let wrong_coordinate=joined.bank53_reads()[map0_index];
                let mut expected_operand=original.operand;
                expected_operand.wire=replacement_wire;
                assert_eq!(wrong_coordinate.operand,expected_operand,
                    "coordinate mutant must change only wire");
                assert_eq!(wrong_coordinate.author,original.author,
                    "coordinate mutant must preserve author");
                assert_eq!(wrong_coordinate.value,original.value,
                    "coordinate mutant must preserve value");
                assert_eq!(wrong_coordinate.operand.relation,original.operand.relation,
                    "coordinate mutant must preserve relation");
                assert_ne!(wrong_coordinate.operand.wire,original.operand.wire,
                    "coordinate mutant must change wire");
                assert_eq!(joined.validate().unwrap_err(),
                    "C503 ROW missing/reordered/changed active read");
                joined.bank53_reads_mut_for_test()[map0_index]=original;
                joined.validate().unwrap();
            }

            let owner_base=owner.checked_mul(WIDTH).unwrap();
            let in_owner_bank53=|operand:&ActiveOperand| {
                operand.wire.checked_sub(owner_base).is_some_and(|local|
                    (BANK53_BASE..BANK53_BASE+BANK53_CONTEXTS*BANK53_CONTEXT_BITS).contains(&local))
            };
            let operands:Vec<_>=joined.batch().active_operands().collect();
            let expected_header_zero=operands.iter().filter(|operand| {
                operand.wire.checked_sub(owner_base).is_some_and(|local|
                    (BANK53_BASE..BANK53_BASE+BANK53_CONTEXTS*BANK53_CONTEXT_BITS).contains(&local)
                    && (local-BANK53_BASE)%BANK53_CONTEXT_BITS>=BANK53_MAP_LIVE_BITS)
            }).count();
            let observed_header_zero=joined.bank53_reads().iter().filter(|read|
                read.author==crate::header_daa_row_placement::C503Bank53Author::HeaderZero
            ).count();
            assert_eq!(observed_header_zero,expected_header_zero,
                "active HEADER-zero census must equal C503 reads for owner {owner}");
            if owner==2 { assert_eq!(expected_header_zero,0,
                "owner2 paired Map row has no active HEADER-zero operand"); }
            let expected_open:Vec<_>=operands.iter().copied()
                .filter(|operand|!in_owner_bank53(operand)).collect();
            let observed_open=ordered_open_complement(&operands,joined.bank53_reads()).unwrap();
            assert_eq!(expected_open,observed_open,
                "independent ordered open-read complement for owner {owner}");
            assert_eq!(joined.open_read_count(),expected_open.len(),
                "open-read count must match the independent complement for owner {owner}");

            let injected=expected_open.first().copied()
                .expect("C503 fixture retains an otherwise-open active operand");
            joined.insert_closed_non_bank53_read_for_test(injected).unwrap();
            let misclassified_open=ordered_open_complement(
                &operands,joined.bank53_reads()).unwrap();
            assert_ne!(expected_open,misclassified_open,
                "independent complement must detect a falsely closed open read");
            assert_ne!(joined.open_read_count(),misclassified_open.len(),
                "a false closure must disagree with the retained open count");
            assert!(joined.validate().is_err(),
                "consumer must reject a falsely closed non-Bank53 read");
            joined.remove_closed_non_bank53_read_for_test(injected).unwrap();
            assert_eq!(expected_open,
                ordered_open_complement(&operands,joined.bank53_reads()).unwrap());
            joined.validate().unwrap();

            let anchor_index = joined.batch().base_terms().enumerate()
                .find(|(_, (relation, term))|
                    *relation == Relation::Header
                    && term.row == owner * (1 << 19) + 356_632)
                .map(|(index, _)| index)
                .expect("retained HEADER anchor occurrence");
            let header_left=joined.batch_mut_for_test()
                .base_term_mut_for_test(anchor_index).1.gate.left;
            joined.batch_mut_for_test().base_term_mut_for_test(anchor_index)
                .1.gate.left ^= 1;
            assert!(joined.validate().is_err(),
                "wrong-side or wrong-wire HEADER anchor must reject");
            joined.batch_mut_for_test().base_term_mut_for_test(anchor_index)
                .1.gate.left=header_left;
            joined.validate().unwrap();

            let original_map_row={
                let map_terms=joined.batch_mut_for_test().map_terms_mut_for_test(0);
                let original=map_terms[0].row;
                map_terms[0].row=owner*(1<<19)+356_632;
                original
            };
            assert!(joined.validate().is_err(),
                "Map occurrence moved onto HEADER anchor must reject");
            joined.batch_mut_for_test().map_terms_mut_for_test(0)[0].row=original_map_row;
            joined.validate().unwrap();

            joined.remove_first_bank53_read_for_test();
            assert!(joined.validate().is_err(),
                "missing active Map/HEADER-zero read must reject");
            drop(joined);

            let wrong_binding = HeaderSourceBinding::diagnostic_for_test(owner);
            let wrong_lease = Eligible08MapPairLease::synthetic_valid_for_test(
                wrong_binding.clone(), owner, OwnerClass::Carry,
                H21EligibleMapStage::source_maps().unwrap(),
            ).unwrap();
            let wrong_receipt = checked_fixture(owner, &wrong_binding, &wrong_lease).unwrap();
            assert!(C503EarlyCarryMapHeaderRow::from_producer(&row_plan, wrong_receipt)
                .err().expect("wrong parent must reject").contains("source binding"));
        }
    }
}
use std::cell::Cell;

#[cfg(test)]
use crate::sparse_stream_roster::EdgeTerm;

const PREFIX_HEADERS: usize = 3073;
const MAX_NATIVE_HEADERS: usize = 1 << 21;

const BANK53_BASE: usize = 671_744;
const FIRST_MODERN_CAP0_OWNER: usize = 845_759;
const FIRST_MODERN_CAP0_BASE: usize = 1_000_770;
const FIRST_MODERN_CAP0_CELLS: usize = 2_048;
const FIRST_MODERN_CAP1_BASE: usize = 1_002_818;
const FIRST_MODERN_CAP1_CELLS: usize = 2_048;
const BANK53_CONTEXT_BITS: usize = 8_192;
const BANK53_CONTEXTS: usize = 2;
const BANK53_MAP_LIVE_BITS: usize = 5_757;
const BANK53_SLACK_BITS: usize = 387;
const C449_PADDING_OWNER: usize = 1_827_840;
const C449_PADDING_BANK53_CELLS: usize = BANK53_CONTEXTS * BANK53_CONTEXT_BITS;
const C450_MIXED_OWNER: usize = 845_760;
const C503_EARLY_MIXED_OWNERS: [usize; 3] = [2, 844_673, 844_674];

fn mixed_map_header_schedule() -> &'static crate::h21_scheduled_max_cap::Plan {
    static SCHEDULE: OnceLock<crate::h21_scheduled_max_cap::Plan> = OnceLock::new();
    SCHEDULE.get_or_init(crate::h21_scheduled_max_cap::Plan::eligible08)
}

fn mixed_map_header_class_allowed(owner: usize, class: crate::daa_history_roster::OwnerClass) -> bool {
    use crate::daa_history_roster::OwnerClass;
    if owner == 1 && class == OwnerClass::Initial {
        return !mixed_map_header_schedule().has_owner_writer(owner).unwrap_or(true);
    }
    crate::bank53_required_writer::require_ordinary_unscored_carry_map_header(
        owner, class, mixed_map_header_schedule(),
    ).is_ok()
}

#[cfg(test)]
mod c505_initial_capture_tests {
    use super::*;
    use crate::daa_history_roster::OwnerClass;
    use crate::header_daa_row_placement::{
        C503Bank53Author, C503Bank53Read, C506InitialMapHeaderRow,
        OperandSide, Relation, RowPlan,
    };

    fn fixture() -> (HeaderSourceBinding, Eligible08MapPairLease) {
        let binding = HeaderSourceBinding::diagnostic_for_test(1);
        let lease = Eligible08MapPairLease::synthetic_valid_for_test(binding.clone(), 1,
            OwnerClass::Initial, H21EligibleMapStage::source_maps().unwrap()).unwrap();
        (binding, lease)
    }
    fn rows(binding: &HeaderSourceBinding, lease: &Eligible08MapPairLease) -> OwnedRows {
        let mut rows = OwnedRows::new(OwnerSelection::Single { owner: 1, class: OwnerClass::Initial });
        rows.begin_mixed_map_header_capture(binding.clone()).unwrap();
        for context in 0..2 {
            for offset in BANK53_MAP_LIVE_BITS..BANK53_CONTEXT_BITS {
                rows.claim_header_seed(1, BANK53_BASE + context * BANK53_CONTEXT_BITS + offset,
                    Fr::zero()).unwrap();
            }
        }
        claim_map_pair_live(&mut rows, lease, binding, 1, OwnerClass::Initial).unwrap();
        rows
    }
    fn packed(binding: &HeaderSourceBinding, rows: &OwnedRows) -> NativePackedRow {
        NativePackedRow { owner: 1, class: OwnerClass::Initial, root: binding.root,
            total: binding.total, bytes: rows.bytes(0).unwrap(),
            header_source_binding: Some(binding.clone()), cap0_source: None, cap1_source: None,
            max_binding: None, map_binding: None, map_context: None, legacy_binding: None }
    }
    fn checked<'a>(binding: &HeaderSourceBinding, lease: &'a Eligible08MapPairLease)
        -> Result<NativeMixedMapHeaderRow<'a>, String> {
        let mut r = rows(binding, lease);
        let row = packed(binding, &r);
        let capture = r.finish_mixed_map_header_capture(&row)?;
        NativeMixedMapHeaderRow::from_producer(row, capture, binding.clone(), lease)
    }
    #[test]
    fn c505_initial_policy_capture_and_single_faults_no_frame() {
        let (binding, mut lease) = fixture();
        let mask = vec![false; WIDTH];
        let native = vec![Fr::zero(); WIDTH];
        let reserved = preflight_map_pair_reservation(&lease, &binding, 1, OwnerClass::Initial, &mask).unwrap();
        preflight_mixed_map_header_seed(1, OwnerClass::Initial, &mask, &native, &reserved).unwrap();
        lease.reseal_cell_value_for_test(0, 1).unwrap();
        let result = checked(&binding, &lease).unwrap();
        assert!(result.read_map(&binding, 0, 0).unwrap());
        assert!(!result.read_header_zero(&binding, 0, BANK53_MAP_LIVE_BITS).unwrap());
        assert!(result.validate_all(&binding.mutated_field_for_test(0)).is_err());
        let zero = BANK53_BASE + BANK53_MAP_LIVE_BITS;
        let mut wrong_native = native.clone(); wrong_native[zero] = Fr::one();
        assert!(preflight_mixed_map_header_seed(1, OwnerClass::Initial, &mask, &wrong_native, &reserved).is_err());
        let mut wrong_mask = mask.clone(); wrong_mask[zero] = true;
        assert!(preflight_mixed_map_header_seed(1, OwnerClass::Initial, &wrong_mask, &native, &reserved).is_err());
        for (owner, class) in [(0, OwnerClass::Genesis), (1, OwnerClass::Carry)] {
            assert!(!mixed_map_header_class_allowed(owner, class));
        }
        let mut missing = rows(&binding, &lease);
        missing.mixed_map_header_capture.as_mut().unwrap().claims[zero - BANK53_BASE] = None;
        let row = packed(&binding, &missing);
        assert!(missing.finish_mixed_map_header_capture(&row).is_err());
        let mut duplicate = rows(&binding, &lease);
        assert!(duplicate.claim_header_seed(1, zero, Fr::zero()).is_err());
        let mut competing = rows(&binding, &lease);
        assert!(competing.claim(1, zero, Fr::zero()).is_err());
        let mut flipped = rows(&binding, &lease);
        let mut row = packed(&binding, &flipped); row.bytes[BANK53_BASE / 8] ^= 1;
        assert!(flipped.finish_mixed_map_header_capture(&row).is_err());
        let mut wrong_value = rows(&binding, &lease);
        wrong_value.mixed_map_header_capture.as_mut().unwrap().claims[0].as_mut().unwrap().value = false;
        let row = packed(&binding, &wrong_value);
        assert!(wrong_value.finish_mixed_map_header_capture(&row).is_err());
        let mut wrong_maps = H21EligibleMapStage::source_maps().unwrap();
        wrong_maps.swap(0, 1);
        let wrong_cut = Eligible08MapPairLease::synthetic_valid_for_test(
            binding.clone(), 1, OwnerClass::Initial, wrong_maps);
        if let Ok(wrong_cut) = wrong_cut {
            assert!(preflight_map_pair_reservation(&wrong_cut, &binding, 1, OwnerClass::Initial, &mask).is_err());
        }
        let mut other_rows = rows(&binding, &lease);
        let row = packed(&binding, &other_rows);
        let capture = other_rows.finish_mixed_map_header_capture(&row).unwrap();
        let other_lease = lease.clone();
        assert!(!std::ptr::eq(&lease, &other_lease));
        assert_eq!(lease.checked_cells(&binding, 1, OwnerClass::Initial).unwrap(),
            other_lease.checked_cells(&binding, 1, OwnerClass::Initial).unwrap());
        assert_eq!(lease.terms(0).unwrap(), other_lease.terms(0).unwrap());
        assert_eq!(NativeMixedMapHeaderRow::from_producer(
            row, capture, binding.clone(), &other_lease).err().as_deref(),
            Some("C450 mixed receipt owner/class/parent binding"));
        checked(&binding, &lease).unwrap().validate_all(&binding).unwrap();
    }

    fn c506_fixture_for_plan(plan:&WorkTreeHistoryPlan)
        -> (HeaderSourceBinding, Eligible08MapPairLease) {
        let binding = HeaderSourceBinding::for_plan(plan, 1).unwrap();
        let mut lease = Eligible08MapPairLease::synthetic_valid_for_test(
            binding.clone(), 1, OwnerClass::Initial,
            H21EligibleMapStage::source_maps().unwrap(),
        ).unwrap();
        lease.reseal_cell_value_for_test(0, 1).unwrap();
        (binding, lease)
    }

    fn c506_fixture() -> (HeaderSourceBinding, Eligible08MapPairLease) {
        let plan=WorkTreeHistoryPlan::compile(
            1_827_840,21,[0x52;32],[0x53;28],
        ).unwrap();
        c506_fixture_for_plan(&plan)
    }

    fn c506_join<'a>(row_plan:&RowPlan<'_, '_>,receipt: NativeMixedMapHeaderRow<'a>)
        -> Result<C506InitialMapHeaderRow<'a>, String> {
        C506InitialMapHeaderRow::from_producer(row_plan, receipt)
    }

    fn c506_fresh_with_plan<'a>(row_plan:&RowPlan<'_, '_>,binding: &HeaderSourceBinding,
        lease: &'a Eligible08MapPairLease) -> C506InitialMapHeaderRow<'a> {
        c506_join(row_plan,checked(binding, lease).unwrap()).unwrap()
    }

    fn c506_fresh<'a>(binding:&HeaderSourceBinding,
        lease:&'a Eligible08MapPairLease) -> C506InitialMapHeaderRow<'a> {
        let plan=WorkTreeHistoryPlan::compile(
            1_827_840,21,[0x52;32],[0x53;28],
        ).unwrap();
        let roster=crate::daa_history_roster::DaaHistoryRoster::compile(&plan).unwrap();
        let scheduled=crate::h21_scheduled_max_cap::Plan::eligible08();
        let row_plan=RowPlan::new(&roster,&scheduled).unwrap();
        c506_fresh_with_plan(&row_plan,binding,lease)
    }

    #[test]
    fn c506_initial_row_join_and_each_binding_field_no_frame() {
        let plan=WorkTreeHistoryPlan::compile(
            1_827_840,21,[0x52;32],[0x53;28],
        ).unwrap();
        let roster=crate::daa_history_roster::DaaHistoryRoster::compile(&plan).unwrap();
        let scheduled=crate::h21_scheduled_max_cap::Plan::eligible08();
        let row_plan=RowPlan::new(&roster,&scheduled).unwrap();
        let (binding, lease) = c506_fixture_for_plan(&plan);
        let receipt = checked(&binding, &lease).unwrap();
        assert!(!receipt.read_header_zero(
            &binding, 0, BANK53_MAP_LIVE_BITS,
        ).unwrap(), "the producer owns the HEADER-zero complement");
        let joined = c506_join(&row_plan,receipt.clone_for_test()).unwrap();
        joined.validate().unwrap();
        assert!(joined.bank53_reads().iter().any(|read|
            read.author == C503Bank53Author::Map(0) && read.value));
        assert!(joined.open_read_count() > 0);
        assert_eq!(joined.batch().owner(), 1);
        assert_eq!(joined.batch().class(), OwnerClass::Initial);
        for field in 0..6 {
            let mut receipt=receipt.clone_for_test();
            receipt.binding = binding.mutated_field_for_test(field);
            assert!(c506_join(&row_plan,receipt).is_err(),
                "binding field {field} must reject at the ROW join");
        }
        let mut wrong_class=receipt.clone_for_test();
        wrong_class.row.class = OwnerClass::Carry;
        assert!(c506_join(&row_plan,wrong_class).is_err());
        let mut wrong_owner=receipt.clone_for_test();
        wrong_owner.row.owner = 2;
        assert!(c506_join(&row_plan,wrong_owner).is_err());
        c506_fresh_with_plan(&row_plan,&binding, &lease).validate().unwrap();
    }

    fn c506_reject_read_fault(
        joined: &mut C506InitialMapHeaderRow<'_>,
        clean: &[C503Bank53Read],
        mutate: impl FnOnce(&mut Vec<C503Bank53Read>),
    ) {
        *joined.bank53_reads_mut_for_test() = clean.to_vec();
        joined.validate().unwrap();
        mutate(joined.bank53_reads_mut_for_test());
        assert!(joined.validate().unwrap_err()
            .contains("C506 ROW missing/reordered/changed active read"));
        *joined.bank53_reads_mut_for_test() = clean.to_vec();
        joined.validate().unwrap();
    }

    #[test]
    fn c506_initial_row_each_active_read_fault_no_frame() {
        let (binding, lease) = c506_fixture();
        let mut joined = c506_fresh(&binding, &lease);
        let clean = joined.bank53_reads().to_vec();
        assert!(clean.len() > 2);
        c506_reject_read_fault(&mut joined, &clean, |reads| { reads.remove(0); });
        c506_reject_read_fault(&mut joined, &clean, |reads| { reads.push(clean[0]); });
        c506_reject_read_fault(&mut joined, &clean, |reads| { reads.swap(0, 1); });
        c506_reject_read_fault(&mut joined, &clean, |reads| {
            reads[0].operand.occurrence += 1;
        });
        c506_reject_read_fault(&mut joined, &clean, |reads| {
            reads[0].operand.side = match reads[0].operand.side {
                OperandSide::Left => OperandSide::Right,
                OperandSide::Right => OperandSide::Left,
            };
        });
        c506_reject_read_fault(&mut joined, &clean, |reads| {
            reads[0].operand.wire ^= 1;
        });
        c506_reject_read_fault(&mut joined, &clean, |reads| {
            reads[0].operand.c1_active = !reads[0].operand.c1_active;
        });
        c506_reject_read_fault(&mut joined, &clean, |reads| {
            reads[0].author = match reads[0].author {
                C503Bank53Author::Map(_) => C503Bank53Author::HeaderZero,
                C503Bank53Author::HeaderZero => C503Bank53Author::Map(0),
            };
        });
        c506_reject_read_fault(&mut joined, &clean, |reads| {
            reads[0].value = !reads[0].value;
        });
        c506_reject_read_fault(&mut joined, &clean, |reads| {
            reads[0].operand.wire = WIDTH + BANK53_BASE + 2 * BANK53_CONTEXT_BITS;
        });
    }

    #[test]
    fn c506_initial_row_source_term_faults_no_frame() {
        let (binding, lease) = c506_fixture();
        let mut joined = c506_fresh(&binding, &lease);
        let clean = joined.batch().clone();
        let ordinary_terms = joined.batch().base_terms().len();
        let map_read = joined.bank53_reads().iter().copied()
            .find(|read| read.operand.relation == Relation::Map(0))
            .expect("active Map0 Bank53 read");
        let map_index = map_read.operand.occurrence - ordinary_terms;

        joined.batch_mut_for_test().map_terms_mut_for_test(0)[map_index].row =
            (1 << 19) + 356_632;
        assert!(joined.validate().is_err(), "Map ROW relocation must reject");
        *joined.batch_mut_for_test() = clean.clone();
        joined.validate().unwrap();

        let term = &mut joined.batch_mut_for_test()
            .map_terms_mut_for_test(0)[map_index];
        match map_read.operand.side {
            OperandSide::Left => term.gate.left ^= 1,
            OperandSide::Right => term.gate.right ^= 1,
        }
        assert!(joined.validate().is_err(), "active Map wire drift must reject");
        *joined.batch_mut_for_test() = clean;
        joined.validate().unwrap();
    }
}

fn require_mixed_map_header_no_scheduled(
    owner: usize, class: crate::daa_history_roster::OwnerClass,
) -> Result<(), String> {
    use crate::daa_history_roster::OwnerClass;
    if owner == 1 && class == OwnerClass::Initial {
        if mixed_map_header_schedule().has_owner_writer(owner)? {
            return Err("C506 Initial Map/HEADER-zero route has scheduled MAX/Cap writer".into());
        }
        return Ok(());
    }
    crate::bank53_required_writer::require_ordinary_unscored_carry_map_header(
        owner, class, mixed_map_header_schedule(),
    )
}

const C512I_WORK_OWNERS: [usize; 2] = [845_885, 845_886];
const C512I_UPPER_BASE: usize = 987_450;
const C512I_WORK_D_BASE: usize = 987_674;
const C512I_ENDPOINT_BITS: usize = 224;
const C512I_CAPTURE_BITS: usize = 2 * C512I_ENDPOINT_BITS;

// Compile-only real-type boundary. No caller or ordinary admission uses it.
#[allow(dead_code, unexpected_cfgs)]
#[path = "c580_coactive_type_harness.rs"]
mod c580_coactive_type_harness;

#[cfg(test)]
pub(crate) fn c581_native_coactive_probe(producer: &NativeOwnerProducer<'_>,
    stream: &crate::h21_scheduled_max_cap::MaxStream<'_>,
    other_stream: &crate::h21_scheduled_max_cap::MaxStream<'_>) -> Result<(), String> {
    c580_coactive_type_harness::native_coactive_probe(producer, stream, other_stream)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum NativeWorkEndpointAuthor { Tree }

fn c578_ordinary_work_policy(owner:usize,class:crate::daa_history_roster::OwnerClass)
    -> Result<(),String> {
    if owner==0 {return Err("C578 ordinary Work excludes genesis".into());}
    crate::bank53_required_writer::require_ordinary_unscored_carry_map_header(
        owner,class,mixed_map_header_schedule())
}
#[cfg(test)]
pub(crate) fn c578_factory_controls_for_test() -> Result<(),String> {
    use crate::daa_history_roster::OwnerClass;
    for owner in [845_885,845_886,846_014] {
        c578_ordinary_work_policy(owner,OwnerClass::Carry)?;
    }
    for owner in [0,845_759,846_015,1_810_840,1_827_840,1<<21] {
        if c578_ordinary_work_policy(owner,OwnerClass::Carry).is_ok() {
            return Err("C578 ordinary Work accepted genesis/scored/scheduled/padding".into());
        }
    }
    if c578_ordinary_work_policy(846_014,OwnerClass::Initial).is_ok() {
        return Err("C578 ordinary Work accepted non-Carry class".into());
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum WorkEndpointPhase { BeforeTree, Tree, AfterTree }

/// Events are appended only after successful calls to the actual ROW writer.
/// The source Tree mask, packed bit, and zero-inclusive event are distinct.
struct WorkEndpointCapture {
    owner: usize,
    phase: WorkEndpointPhase,
    // Preserve the actual ROW claim before any Boolean reader conversion.
    events: Vec<(usize, NativeWorkEndpointAuthor, Fr)>,
    // Local custody only: the nonempty immutable Vec keeps its allocation
    // through moves. This is neither a serialized nor a cryptographic identity.
    packed_identity: Option<usize>,
}
impl WorkEndpointCapture {
    fn index(local: usize) -> Option<usize> {
        if (C512I_UPPER_BASE..C512I_WORK_D_BASE).contains(&local) {
            Some(local - C512I_UPPER_BASE)
        } else if (C512I_WORK_D_BASE..C512I_WORK_D_BASE + C512I_ENDPOINT_BITS).contains(&local) {
            Some(C512I_ENDPOINT_BITS + local - C512I_WORK_D_BASE)
        } else { None }
    }
    fn expected_local(index: usize) -> Result<usize, String> {
        if index < C512I_ENDPOINT_BITS { Ok(C512I_UPPER_BASE + index) }
        else if index < C512I_CAPTURE_BITS {
            Ok(C512I_WORK_D_BASE + index - C512I_ENDPOINT_BITS)
        } else { Err("C512i Work endpoint event outside exact census".into()) }
    }
    fn new(owner: usize) -> Result<Self, String> {
        // Generic capture geometry, not permission to construct a native lease.
        // The ordinary producer still enforces its existing owner/route guards.
        let genuine = crate::bank53_map::CutDescriptor::eligible08().terminals()[0] - 1;
        if owner == 0 || owner >= genuine { return Err("C577 Work capture genuine H21 owner".into()); }
        let endpoints = &crate::work_tree_layout::shared_baseline()?.endpoints;
        if endpoints.upper != (C512I_UPPER_BASE..C512I_WORK_D_BASE).collect::<Vec<_>>()
            || endpoints.work != (C512I_WORK_D_BASE..C512I_WORK_D_BASE+C512I_ENDPOINT_BITS).collect::<Vec<_>>() {
            return Err("C512i exact Upper/Work-D endpoint layout".into());
        }
        Ok(Self { owner, phase: WorkEndpointPhase::BeforeTree,
            events: Vec::with_capacity(C512I_CAPTURE_BITS), packed_identity: None })
    }
    fn check_claim(&self, owner: usize, local: usize, already_claimed: bool) -> Result<(), String> {
        if let Some(index) = Self::index(local) {
            if owner != self.owner || self.phase != WorkEndpointPhase::Tree
                || already_claimed || index != self.events.len() {
                return Err(format!("C512i Work endpoint wrong author, order or duplicate wire{local}"));
            }
        }
        Ok(())
    }
    fn record_claim(&mut self, local: usize, value: Fr) {
        if Self::index(local).is_some() {
            self.events.push((local, NativeWorkEndpointAuthor::Tree, value));
        }
    }
    fn finish_tree(&mut self) -> Result<(), String> {
        if self.phase != WorkEndpointPhase::Tree || self.events.len() != C512I_CAPTURE_BITS {
            return Err("C512i incomplete Tree endpoint claim census".into());
        }
        for (index, &(local, author, _)) in self.events.iter().enumerate() {
            if local != Self::expected_local(index)? || author != NativeWorkEndpointAuthor::Tree {
                return Err("C512i Tree endpoint event domain/order/author".into());
            }
        }
        self.phase = WorkEndpointPhase::AfterTree;
        Ok(())
    }
    fn check_image(&self, packed: &[u8],
        mut source_bit: impl FnMut(usize) -> Result<Option<bool>, String>)
        -> Result<(), String> {
        if self.phase != WorkEndpointPhase::AfterTree
            || self.events.len() != C512I_CAPTURE_BITS || packed.len() != OWNER_BYTES {
            return Err("C512i complete Work endpoint claim/image width".into());
        }
        for (index, &(local, author, value)) in self.events.iter().enumerate() {
            if local != Self::expected_local(index)? || author != NativeWorkEndpointAuthor::Tree {
                return Err("C512i Tree endpoint event domain/order/author".into());
            }
            if value != Fr::zero() && value != Fr::one() {
                return Err("C577 original Work endpoint Fr is not Boolean".into());
            }
            let wanted = source_bit(local)?
                .ok_or_else(|| format!("C512i missing Tree source mask wire{local}"))?;
            let packed_value = packed[local/8] & (1u8 << (local%8)) != 0;
            if value != Fr::from(wanted as u64) || packed_value != wanted {
                return Err(format!("C512i Tree claim/source/packed wire{local}"));
            }
        }
        Ok(())
    }
    fn seal_row(&mut self, row: &NativePackedRow) -> Result<(), String> {
        if self.packed_identity.is_some() || self.phase != WorkEndpointPhase::AfterTree
            || self.events.len() != C512I_CAPTURE_BITS || row.owner != self.owner
            || row.class != crate::daa_history_roster::OwnerClass::Carry
            || row.bytes.len() != OWNER_BYTES {
            return Err("C512j Work capture requires one final same-owner packed row".into());
        }
        self.packed_identity = Some(row.bytes.as_ptr() as usize);
        Ok(())
    }
    fn check_identity(&self, binding: &HeaderSourceBinding, expected: &HeaderSourceBinding,
        parent: &crate::h21_work_local_source::Parent,
        expected_parent: &crate::h21_work_local_source::Parent,
        height: usize, row: &NativePackedRow) -> Result<(), String> {
        use crate::daa_history_roster::OwnerClass;
        let owner = expected.owner();
        if binding != expected
            || parent != expected_parent || height != owner + 2
            || self.owner != owner || row.owner != owner || row.class != OwnerClass::Carry {
            return Err("C512i Work endpoint exact owner, parent, row or height".into());
        }
        row.require_header_source_binding(expected, owner, OwnerClass::Carry)?;
        self.require_same_row(row)
    }
    fn require_same_row(&self, row: &NativePackedRow) -> Result<(), String> {
        if row.bytes.len() != OWNER_BYTES
            || self.packed_identity != Some(row.bytes.as_ptr() as usize) {
            return Err("C512j Work capture requires its original packed allocation".into());
        }
        Ok(())
    }
    fn check_source_packed(&self, binding: &HeaderSourceBinding, row: &NativePackedRow,
        tree: &NativeTreeSourceLease) -> Result<(), String> {
        if self.owner != binding.owner() {
            return Err("C512i complete Work endpoint claim/row owner".into());
        }
        self.require_same_row(row)?;
        tree.check_binding(binding)?; tree.check_author()?;
        let base = self.owner.checked_mul(WIDTH).ok_or("C512i Work source owner overflow")?;
        self.check_image(&row.bytes, |local| {
            let wire = base.checked_add(local).ok_or("C512i Work endpoint wire overflow")?;
            tree.read_tree_bit(binding, wire)
        })
    }
    fn require_complete_checked(checked: &Cell<bool>) -> Result<(), String> {
        if !checked.get() {
            return Err("C512i Work endpoint checked read needs complete census".into());
        }
        Ok(())
    }
    fn checked_endpoint(&self, checked: &Cell<bool>, binding: &HeaderSourceBinding,
        row: &NativePackedRow, tree: &NativeTreeSourceLease, physical_wire: usize)
        -> Result<(NativeWorkEndpointAuthor, bool), String> {
        self.checked_endpoint_fr(checked, binding, row, tree, physical_wire)
            .map(|(author, value)| (author, value.is_one()))
    }
    fn checked_endpoint_fr(&self, checked: &Cell<bool>, binding: &HeaderSourceBinding,
        row: &NativePackedRow, tree: &NativeTreeSourceLease, physical_wire: usize)
        -> Result<(NativeWorkEndpointAuthor, Fr), String> {
        Self::require_complete_checked(checked)?;
        let result = (|| {
            self.require_same_row(row)?;
            if self.phase != WorkEndpointPhase::AfterTree || self.events.len() != C512I_CAPTURE_BITS {
                return Err("C512i complete Work endpoint claim census changed".into());
            }
            if binding.owner() != self.owner || row.owner != self.owner {
                return Err("C512i Work endpoint checked owner binding".into());
            }
            row.require_header_source_binding(binding, self.owner,
                crate::daa_history_roster::OwnerClass::Carry)?;
            let base = self.owner.checked_mul(WIDTH)
                .ok_or("C512i Work endpoint owner base overflow")?;
            let local = physical_wire.checked_sub(base).filter(|local| *local < WIDTH)
                .ok_or("C512i Work endpoint read owner")?;
            let index = Self::index(local)
                .ok_or("C512i read outside Upper/Work-D Tree endpoints")?;
            let event = self.events.get(index).copied()
                .ok_or("C512i missing zero-inclusive Work endpoint event")?;
            if event.2 != Fr::zero() && event.2 != Fr::one() {
                return Err("C577 original Work endpoint Fr is not Boolean".into());
            }
            let source = tree.read_tree_bit(binding, physical_wire)?
                .ok_or("C512i Work endpoint missing Tree source")?;
            let packed = row.bytes[local/8] & (1u8 << (local%8)) != 0;
            if event != (local, NativeWorkEndpointAuthor::Tree, Fr::from(source as u64)) || packed != source {
                return Err("C512i Work endpoint event/source/packed changed".into());
            }
            Ok((NativeWorkEndpointAuthor::Tree, event.2))
        })();
        if result.is_err() { checked.set(false); }
        result
    }
}

#[cfg(test)]
mod c512i_work_endpoint_capture_tests {
    use super::*;
    use crate::daa_history_roster::OwnerClass;

    fn fresh(owner: usize) -> OwnedRows {
        let mut rows = OwnedRows::new(OwnerSelection::Single {owner,class:OwnerClass::Carry});
        rows.begin_work_endpoint_capture(owner).unwrap();
        rows
    }

    #[test]
    fn c512i_no_frame_zero_claim_order_source_and_row_mutants() {
        let owner=C512I_WORK_OWNERS[0];
        let mut rows=fresh(owner);
        assert!(rows.claim(owner,C512I_UPPER_BASE,Fr::zero()).is_err(),
            "HEADER phase must not claim a reserved Tree endpoint");
        assert!(!rows.claimed[0][C512I_UPPER_BASE]);
        assert!(rows.begin_author_census().is_err(),
            "C374 cannot mix after a Work endpoint capture");
        rows.begin_work_endpoint_tree_phase().unwrap();
        rows.claim(owner,C512I_UPPER_BASE-1,Fr::zero()).unwrap();
        assert!(rows.work_endpoint_capture.as_ref().unwrap().events.is_empty(),
            "ordinary Tree claims outside endpoints remain valid and unlabeled");
        assert!(rows.claim(owner,C512I_UPPER_BASE,Fr::from(2u64)).is_err());
        rows.claim(owner,C512I_UPPER_BASE,Fr::zero()).unwrap();
        assert!(rows.claim(owner,C512I_UPPER_BASE,Fr::zero()).is_err(),
            "same-author equal-zero duplicate must fail");
        assert!(rows.claim(owner+1,C512I_UPPER_BASE+1,Fr::zero()).is_err());
        assert!(rows.claim(owner,C512I_WORK_D_BASE,Fr::zero()).is_err(),
            "Work-D cannot precede the remaining Upper claims");
        for local in C512I_UPPER_BASE+1..C512I_WORK_D_BASE {
            rows.claim(owner,local,Fr::zero()).unwrap();
        }
        rows.claim(owner,C512I_WORK_D_BASE,Fr::zero()).unwrap();
        assert!(rows.claim(owner,C512I_WORK_D_BASE,Fr::zero()).is_err(),
            "Work-D equal-zero duplicate must fail");
        for local in C512I_WORK_D_BASE+1..C512I_WORK_D_BASE+C512I_ENDPOINT_BITS {
            rows.claim(owner,local,Fr::zero()).unwrap();
        }
        rows.finish_work_endpoint_tree_phase().unwrap();
        assert!(rows.claim(owner,C512I_UPPER_BASE,Fr::zero()).is_err(),
            "late Work endpoint claim must fail");
        rows.claim(owner,C512I_WORK_D_BASE+C512I_ENDPOINT_BITS,Fr::zero()).unwrap();
        let mut capture=rows.work_endpoint_capture.take().unwrap();
        let packed=rows.bytes(0).unwrap();
        capture.check_image(&packed, |_| Ok(Some(false))).unwrap();
        assert_eq!(capture.events.len(),C512I_CAPTURE_BITS);
        assert_eq!(capture.events.iter().filter(|(_,_,value)| value.is_zero()).count(),C512I_CAPTURE_BITS);
        let mut wrong_row=packed.clone();wrong_row[C512I_UPPER_BASE/8]^=1u8<<(C512I_UPPER_BASE%8);
        assert!(capture.check_image(&wrong_row, |_| Ok(Some(false))).is_err());
        assert!(capture.check_image(&packed, |local|
            Ok(if local==C512I_WORK_D_BASE {None}else{Some(false)})).is_err());
        assert!(capture.check_image(&packed, |local|
            Ok(Some(local==C512I_UPPER_BASE))).is_err());
        capture.events.push((C512I_WORK_D_BASE+C512I_ENDPOINT_BITS,
            NativeWorkEndpointAuthor::Tree,Fr::zero()));
        assert!(capture.check_image(&packed, |_| Ok(Some(false))).is_err(),
            "extra Work-endpoint-labeled event outside the domain must fail");

        let mut missing_upper=fresh(owner);
        missing_upper.begin_work_endpoint_tree_phase().unwrap();
        assert!(missing_upper.claim(owner,C512I_UPPER_BASE+1,Fr::zero()).is_err());
        assert!(missing_upper.finish_work_endpoint_tree_phase().is_err());
        let mut missing_work=fresh(owner);
        missing_work.begin_work_endpoint_tree_phase().unwrap();
        for local in C512I_UPPER_BASE..C512I_WORK_D_BASE {
            missing_work.claim(owner,local,Fr::zero()).unwrap();
        }
        assert!(missing_work.claim(owner,C512I_WORK_D_BASE+1,Fr::zero()).is_err());
        assert!(missing_work.finish_work_endpoint_tree_phase().is_err());
        let mut wrong_owner=WorkEndpointCapture::new(owner).unwrap();
        wrong_owner.phase=WorkEndpointPhase::Tree;
        assert!(wrong_owner.check_claim(C512I_WORK_OWNERS[1],C512I_UPPER_BASE,false).is_err());
        WorkEndpointCapture::new(owner-1).unwrap();
        assert!(WorkEndpointCapture::new(0).is_err());
        assert!(WorkEndpointCapture::new(1_827_839).is_err());
    }

    #[test]
    fn c512i_no_frame_h21_tree_replacement_mask_covers_both_work_sources() {
        let plan=WorkTreeHistoryPlan::compile(1_827_840,21,[0x61;32],[0x62;28]).unwrap();
        for owner in C512I_WORK_OWNERS {
            let mask=plan.physical_assignment_replacement_mask(owner as u64).unwrap();
            assert_eq!(mask.len(),WIDTH);
            for index in 0..C512I_CAPTURE_BITS {
                assert!(mask[WorkEndpointCapture::expected_local(index).unwrap()],
                    "all zero-inclusive Work endpoints must be Tree replacements");
            }
        }
    }

    fn captured_zeroes(owner: usize) -> WorkEndpointCapture {
        let mut capture = WorkEndpointCapture::new(owner).unwrap();
        capture.phase = WorkEndpointPhase::Tree;
        for local in (C512I_UPPER_BASE..C512I_UPPER_BASE + C512I_ENDPOINT_BITS)
            .chain(C512I_WORK_D_BASE..C512I_WORK_D_BASE + C512I_ENDPOINT_BITS) {
            capture.check_claim(owner, local, false).unwrap();
            capture.record_claim(local, Fr::zero());
        }
        capture
    }

    // Small checker-sensitivity inputs, never a synthetic producer or native
    // history. The same private checks below are called by the real token.
    fn isolated_parts() -> (WorkEndpointCapture, HeaderSourceBinding, NativePackedRow,
        NativeTreeSourceLease, crate::h21_work_local_source::Parent) {
        let owner = C512I_WORK_OWNERS[0];
        let binding = HeaderSourceBinding::from_sink_for_test([0x61;32], [0x62;28], [0x63;32],
            crate::bank53_map::CutDescriptor::eligible08().canonical_identity(), owner);
        let row = NativePackedRow { owner, class: OwnerClass::Carry,
            root: binding.root, total: binding.total, bytes: vec![0;OWNER_BYTES],
            header_source_binding: Some(binding.clone()), cap0_source: None, cap1_source: None,
            max_binding: None, map_binding: None, map_context: None, legacy_binding: None };
        let mut capture = captured_zeroes(owner);
        capture.finish_tree().unwrap();
        capture.seal_row(&row).unwrap();
        let mut tree = NativeTreeSourceLease { binding: binding.clone(),
            author: TreeLeaseAuthor::NativeTree, values: vec![0;OWNER_BYTES],
            owned: vec![0;OWNER_BYTES] };
        for local in C512I_UPPER_BASE..C512I_WORK_D_BASE + C512I_ENDPOINT_BITS {
            tree.owned[local/8] |= 1u8 << (local%8);
        }
        let parent = crate::h21_work_local_source::Parent { root: binding.root,
            total: binding.total, profile: binding.profile, headers: 1_827_840,
            slots: 1 << 21, cut: binding.cut.clone() };
        (capture, binding, row, tree, parent)
    }

    #[test]
    fn c512j_no_frame_final_census_single_missing_zero_upper_and_work_d() {
        for index in [C512I_ENDPOINT_BITS - 1, C512I_CAPTURE_BITS - 1] {
            let mut capture = captured_zeroes(C512I_WORK_OWNERS[0]);
            let missing = capture.events.remove(index);
            assert!(missing.2.is_zero());
            assert_eq!(capture.events.len(), C512I_CAPTURE_BITS - 1);
            // No subsequent claim is attempted: the final census itself must
            // reject one omitted zero from either endpoint domain.
            assert_eq!(capture.finish_tree().unwrap_err(),
                "C512i incomplete Tree endpoint claim census");
            assert_eq!(capture.phase, WorkEndpointPhase::Tree);
        }
    }

    #[test]
    fn c512j_no_frame_work_capture_exclusions_and_max_pairing() {
        c512j_require_separate_work_options(true,false,false,false,false).unwrap();
        c512j_require_separate_work_options(false,true,false,false,false).unwrap();
        c512j_require_separate_work_options(false,false,true,false,false).unwrap();
        c512j_require_separate_work_options(false,false,false,true,true).unwrap();
        for (c374,regular,source,claims) in [
            (true,false,false,false), (false,true,false,false),
            (false,false,true,false), (false,false,false,true), (false,false,true,true),
        ] {
            assert!(c512j_require_separate_work_options(true,c374,regular,source,claims).is_err());
        }
        for work in [false,true] {
            assert!(c512j_require_separate_work_options(work,false,false,true,false).is_err());
            assert!(c512j_require_separate_work_options(work,false,false,false,true).is_err());
        }
        let owner = C512I_WORK_OWNERS[0];
        let mut c374 = OwnedRows::new(OwnerSelection::Single { owner, class: OwnerClass::Carry });
        c374.begin_author_census().unwrap();
        assert!(c374.begin_work_endpoint_capture(owner).is_err());
        let mut work = fresh(owner);
        assert!(work.begin_author_census().is_err());
        assert_eq!(work.begin_regular_author_census().unwrap_err(),
            "C512j regular census cannot mix after Work capture");
        let mut regular = OwnedRows::new(OwnerSelection::Single {
            owner: 845_887, class: OwnerClass::Carry });
        regular.begin_regular_author_census().unwrap();
        assert!(regular.begin_work_endpoint_capture(owner).is_err());
    }

    #[test]
    fn c512j_no_frame_exact_binding_parent_height_and_same_row_custody() {
        let (mut capture,binding,mut row,tree,parent) = isolated_parts();
        let height = binding.owner() + 2;
        capture.check_identity(&binding,&binding,&parent,&parent,height,&row).unwrap();
        capture.check_source_packed(&binding,&row,&tree).unwrap();
        for field in 0..6 {
            let changed = binding.mutated_field_for_test(field);
            assert!(capture.check_identity(&changed,&binding,&parent,&parent,height,&row).is_err(),
                "isolated binding field {field}");
        }
        for field in 0..6 {
            let mut changed = parent.clone();
            match field { 0 => changed.root[0]^=1, 1 => changed.total[0]^=1,
                2 => changed.profile[0]^=1, 3 => changed.cut.push(0),
                4 => changed.headers+=1, 5 => changed.slots+=1, _ => unreachable!() }
            assert!(capture.check_identity(&binding,&binding,&changed,&parent,height,&row).is_err(),
                "isolated Work parent field {field}");
        }
        assert!(capture.check_identity(&binding,&binding,&parent,&parent,height+1,&row).is_err());
        capture.owner+=1;
        assert!(capture.check_identity(&binding,&binding,&parent,&parent,height,&row).is_err());
        capture.owner-=1;
        row.owner+=1;
        assert!(capture.check_identity(&binding,&binding,&parent,&parent,height,&row).is_err());
        row.owner-=1;
        row.class=OwnerClass::Genesis;
        assert!(capture.check_identity(&binding,&binding,&parent,&parent,height,&row).is_err());
        row.class=OwnerClass::Carry;
        row.root[0]^=1;
        assert!(capture.check_identity(&binding,&binding,&parent,&parent,height,&row).is_err());
        row.root[0]^=1;
        row.total[0]^=1;
        assert!(capture.check_identity(&binding,&binding,&parent,&parent,height,&row).is_err());
        row.total[0]^=1;
        row.header_source_binding=Some(binding.mutated_field_for_test(3));
        assert!(capture.check_identity(&binding,&binding,&parent,&parent,height,&row).is_err());
        row.header_source_binding=Some(binding.clone());
        let equal_bytes = row.clone();
        assert_eq!(equal_bytes.bytes,row.bytes);
        assert_ne!(equal_bytes.bytes.as_ptr(),row.bytes.as_ptr());
        assert!(capture.check_identity(&binding,&binding,&parent,&parent,height,&equal_bytes)
            .unwrap_err().contains("original packed allocation"));
        let moved_row = row;
        capture.check_identity(&binding,&binding,&parent,&parent,height,&moved_row).unwrap();
        assert!(capture.seal_row(&moved_row).is_err(), "seal cannot be renewed");
        capture.packed_identity=None;
        assert!(capture.check_identity(&binding,&binding,&parent,&parent,height,&moved_row).is_err());
    }

    #[test]
    fn c512j_no_frame_tree_source_and_event_single_faults() {
        let (mut capture,binding,row,tree,_) = isolated_parts();
        capture.check_source_packed(&binding,&row,&tree).unwrap();
        for field in 0..6 {
            let mut changed = tree.clone();
            changed.binding=binding.mutated_field_for_test(field);
            assert!(capture.check_source_packed(&binding,&row,&changed).is_err());
        }
        let mut wrong_author=tree.clone(); wrong_author.author=TreeLeaseAuthor::Other;
        assert!(capture.check_source_packed(&binding,&row,&wrong_author).is_err());
        for local in [C512I_UPPER_BASE,C512I_WORK_D_BASE] {
            let mut missing_mask=tree.clone(); missing_mask.owned[local/8]^=1u8<<(local%8);
            assert!(capture.check_source_packed(&binding,&row,&missing_mask).is_err());
            let mut wrong_value=tree.clone(); wrong_value.values[local/8]^=1u8<<(local%8);
            assert!(capture.check_source_packed(&binding,&row,&wrong_value).is_err());
        }
        capture.events[0].0=usize::MAX;
        let mut source_read=false;
        assert!(capture.check_image(&row.bytes, |_| {source_read=true;Ok(Some(false))}).is_err());
        assert!(!source_read, "invalid event coordinates fail before lookup or indexing");
        capture.events[0].0=C512I_UPPER_BASE;
        capture.events.push((C512I_WORK_D_BASE+C512I_ENDPOINT_BITS,NativeWorkEndpointAuthor::Tree,Fr::zero()));
        assert!(capture.check_source_packed(&binding,&row,&tree).is_err(),
            "an extra endpoint-labeled event is not an ordinary Tree claim");
    }

    /// Actual class/read/roster/Tree policies, never a substitute native source.
    #[test]
    fn c577_no_frame_all_score_work_upper_donors_and_activity() {
        use h21_eligible_context::{ClassEquationPlan, ScoreRelationReadAuthor as Read};
        let parent=WorkTreeHistoryPlan::compile(1_827_840,21,[0x61;32],[0x62;28]).unwrap();
        let roster=DaaHistoryRoster::compile(&parent).unwrap();
        let schedule=mixed_map_header_schedule();
        let descriptor=crate::bank53_map::CutDescriptor::eligible08();
        let calendar:BTreeMap<_,_>=schedule.max_calendar().into_iter().collect();
        let mut destinations=BTreeSet::new();let mut donors=BTreeSet::new();
        let mut kinds=[0usize;3];let mut context_reads=[0usize;2];
        let mut coactive=Vec::new();let mut ordinary_edge=false;let mut sampled_edge=false;
        for item in ClassEquationPlan::members() {
            let recipe=item.unwrap();let destination=recipe.owner();let donor=destination-1;
            assert!(destinations.insert(destination));assert!(donors.insert(donor));
            assert!(donor>0 && donor<(parent.headers()-1) as usize);
            assert!(donor<parent.slots());
            assert_eq!(roster.owner_class(donor as u64).unwrap(),OwnerClass::Carry);
            let active=recipe.active();
            if let Ok(regular)=Eligible08RegularScoreOwner::classify(destination) {
                assert_eq!(regular.active(),active);kinds[0]+=1;
            } else {
                let context=descriptor.guards().iter().position(|g| destination==g-1).unwrap();
                assert_eq!(active,std::array::from_fn(|c| c==context));kinds[context+1]+=1;
            }
            let (max,cap)=schedule.owner_activity(donor).unwrap();
            let calendar_active=calendar.get(&donor).map_or([false,false],|steps|
                steps.map(|step| step.is_some()));
            assert_eq!(max,calendar_active);assert_eq!(cap,[false,false]);
            if max.iter().any(|v| *v) {coactive.push((destination,donor,max));}

            // Use the real per-owner policy. No local shadow mask, native
            // prefix, count-only term visitor or cached acceptance is used.
            let tree=parent.physical_assignment_replacement_mask(donor as u64).unwrap();
            assert_eq!(tree.len(),WIDTH);
            for index in 0..448 {assert!(tree[WorkEndpointCapture::expected_local(index).unwrap()]);}
            assert!(tree[991_232..999_424].iter().all(|v| !*v));
            for context in 0..2 {
                assert!(tree[C512C_MAX_BASE[context]..C512C_MAX_BASE[context]+673].iter().all(|v| !*v));
            }
            let reads:Vec<_>=recipe.reads().into_iter()
                .filter(|(_,author)| matches!(author,Read::WorkUpper{..})).collect();
            let mut cursor=0;let mut unique=BTreeSet::new();
            for context in 0..2 {if active[context] {
                for bit in 0..224 {
                    let (wire,author)=reads[cursor];cursor+=1;
                    assert_eq!(author,Read::WorkUpper{owner:donor,height:destination+1});
                    assert_eq!(wire,donor*WIDTH+C512I_UPPER_BASE+bit);
                    assert!(tree[wire%WIDTH]);unique.insert(wire);context_reads[context]+=1;
                }
            }}
            assert_eq!(cursor,reads.len());assert_eq!(unique.len(),224);
            assert_eq!(reads.len(),224*active.iter().filter(|v| **v).count());
            if destination==846_015 {
                assert_eq!(donor,846_014);assert_eq!(active,[true,true]);
                assert_eq!(reads.len(),448);assert_eq!(unique.len(),224);
                assert_eq!(2*reads.len(),896);ordinary_edge=true;
            }
            if donor==1_810_903 {
                assert_eq!(active,[true,false]);assert_eq!(reads.len(),224);sampled_edge=true;
            }
        }
        assert_eq!(kinds,[7540,1,1]);assert_eq!(destinations.len(),7542);
        assert_eq!(donors.len(),7542);assert_eq!(context_reads,[7541*224,7540*224]);
        assert!(ordinary_edge && sampled_edge);
        assert_eq!(coactive,vec![(1_810_841,1_810_840,[false,true])],
            "a uniform unscheduled-donor admission is false at the exact clip");
        for owner in [1usize,845_886,846_014,1_810_840,1_810_903,1_827_838] {
            WorkEndpointCapture::new(owner).unwrap();
        }
        for owner in [0usize,1_827_839,1<<21] {assert!(WorkEndpointCapture::new(owner).is_err());}
        assert!(Eligible08RegularScoreOwner::equation_plan(846_014).is_err());
        assert!(schedule.owner_activity(1<<21).is_err());
        assert!(parent.physical_assignment_replacement_mask(1<<21).is_err());
    }

    /// Structural ownership/composition only. No NativePrefix, closed stream,
    /// native author lease or successful Score join is constructed here.
    #[test]
    fn c577_no_frame_exact_tail_one_allocation_tree_then_max_controls() {
        use crate::h21_scheduled_max_cap::{MaxReplayAuthor, Writer};
        let owner=1_810_840;
        let member=scheduled_max_class(owner).unwrap();
        assert_eq!(member.active,[false,true]);
        assert_eq!(mixed_map_header_schedule().owner_activity(owner).unwrap(),
            ([false,true],[false,false]));
        // The existing ordinary factory's Work/MAX exclusion stays intact.
        assert!(c512j_require_separate_work_options(true,false,false,true,true).is_err());
        let mut rows=fresh(owner);
        assert!(rows.claim(owner,C512I_UPPER_BASE,Fr::zero()).unwrap_err()
            .contains("wrong author, order or duplicate"));
        assert!(!rows.claimed[0][C512I_UPPER_BASE]);
        rows.begin_work_endpoint_tree_phase().unwrap();
        assert!(rows.claim(owner,C512I_WORK_D_BASE,Fr::zero()).is_err(),
            "same-owner zero cannot be retagged from Upper to Work-D");
        for index in 0..C512I_CAPTURE_BITS {
            let local=WorkEndpointCapture::expected_local(index).unwrap();
            let value=Fr::from((index>=224 && index%2==1) as u64);
            rows.claim(owner,local,value).unwrap();
            assert_eq!(rows.work_endpoint_capture.as_ref().unwrap().events[index],
                (local,NativeWorkEndpointAuthor::Tree,value));
        }
        assert_eq!(rows.work_endpoint_capture.as_ref().unwrap().events.len(),448);
        assert!(rows.work_endpoint_capture.as_ref().unwrap()
            .check_image(&vec![0;OWNER_BYTES], |_| Ok(Some(false))).unwrap_err()
            .contains("complete Work endpoint claim/image width"));
        rows.finish_work_endpoint_tree_phase().unwrap();
        assert!(rows.claim(owner,C512I_UPPER_BASE,Fr::zero()).is_err(),
            "a later author cannot relabel an existing zero Tree event");

        // These are structural typed MAX inputs, not a fabricated closed stream.
        // Its Work-D inputs use exactly the preceding ROW claim Fr values.
        let mut cells=Vec::new();
        for bit in 0..224 {
            cells.push((owner*WIDTH+C512I_WORK_D_BASE+bit,
                MaxReplayAuthor::NativeWorkD{height:owner+2},
                rows.values[0][C512I_WORK_D_BASE+bit]));
        }
        for bit in 0..673 {
            cells.push((owner*WIDTH+C512C_MAX_BASE[1]+bit,
                MaxReplayAuthor::Scheduled(Writer::Max{context:1,end:owner+2}),
                Fr::from((bit%3==1) as u64)));
        }
        let max=c512c_checked_max_cells(owner,&cells).unwrap();
        assert!(max[0].is_empty());assert_eq!(max[1].len(),673);
        for fault in 0..7 {
            let mut bad=cells.clone();
            match fault {
                0=>bad[224].1=MaxReplayAuthor::NativeWorkD{height:owner+2},
                1=>bad[224].0=owner*WIDTH+C512I_UPPER_BASE,
                2=>{bad[224].0=owner*WIDTH+C512C_MAX_BASE[0];
                    bad[224].1=MaxReplayAuthor::Scheduled(Writer::Max{context:0,end:owner+2});},
                3=>bad[224].1=MaxReplayAuthor::Scheduled(Writer::Max{context:1,end:owner+3}),
                4=>bad[224].2=Fr::from(2u64),
                5=>bad[225]=bad[224],
                6=>{bad.pop();},
                _=>unreachable!(),
            }
            let expected=if fault==6 {"C512c exact scheduled MAX owner/cell census"}
                else {"C512c exact MAX writer context/end/coordinate/value"};
            assert_eq!(c512c_checked_max_cells(owner,&bad).unwrap_err(),expected,
                "isolated MAX fault {fault}");
            assert!(!rows.claimed[0][C512C_MAX_BASE[1]],
                "typed input refusal precedes any structural MAX claim");
        }
        let mut extra=cells.clone();extra.push(cells[224]);
        assert_eq!(c512c_checked_max_cells(owner,&extra).unwrap_err(),
            "C512c exact scheduled MAX owner/cell census");
        let mut claims=Vec::new();
        for &(local,value) in &max[1] {
            assert!((1_000_097..1_000_770).contains(&local));
            assert!(!(987_450..987_898).contains(&local));
            assert!(!(991_232..999_424).contains(&local));
            rows.claim_exclusive(owner,local,value).unwrap();
            claims.push((local,MaxReplayAuthor::Scheduled(Writer::Max{context:1,end:owner+2}),value.is_one()));
        }
        assert_eq!(claims.len(),673);
        assert!(rows.claim_exclusive(owner,C512C_MAX_BASE[1],Fr::zero()).unwrap_err()
            .contains("exclusive claim overlaps"),"duplicate zero is exclusive");
        assert_eq!(rows.work_endpoint_capture.as_ref().unwrap().events.len(),448,
            "MAX claims cannot be appended as Work endpoint events");
        assert!(rows.claimed[0][999_424..1_000_097].iter().all(|v| !*v));
        assert!(rows.claimed[0][991_232..999_424].iter().all(|v| !*v));
        assert_eq!(rows.claimed[0].iter().filter(|v| **v).count(),448+673);

        // Pack once after both claim phases and seal that allocation once.
        let row=NativePackedRow{owner,class:OwnerClass::Carry,root:[0x61;32],total:[0x62;28],
            bytes:rows.bytes(0).unwrap(),header_source_binding:None,cap0_source:None,cap1_source:None,
            max_binding:None,map_binding:None,map_context:None,legacy_binding:None};
        let mut capture=rows.work_endpoint_capture.take().unwrap();
        capture.check_image(&row.bytes,|local| Ok(Some(rows.values[0][local].is_one()))).unwrap();
        for &(wire,author,value) in &cells[224..] {
            assert_eq!(c576_physical_max_read(member,&cells,&claims,&row.bytes,wire).unwrap(),(author,value));
        }
        assert_eq!(c576_physical_max_read(member,&cells,&claims,&row.bytes,
            owner*WIDTH+C512C_MAX_BASE[0]).unwrap_err(),"C576 inactive MAX context");
        capture.events[0].2=Fr::from(2u64);
        let mut source_reads=0;
        assert_eq!(capture.check_image(&row.bytes, |_| {source_reads+=1;Ok(Some(false))})
            .unwrap_err(),"C577 original Work endpoint Fr is not Boolean");
        assert_eq!(source_reads,0,"Fr2 refusal precedes Boolean source conversion");
        capture.events[0].2=Fr::zero();
        capture.check_image(&row.bytes,|local| Ok(Some(rows.values[0][local].is_one()))).unwrap();
        capture.seal_row(&row).unwrap();
        capture.require_same_row(&row).unwrap();
        let foreign=row.clone();
        assert_eq!(foreign.bytes,row.bytes);
        assert_ne!(foreign.bytes.as_ptr(),row.bytes.as_ptr());
        assert_eq!(capture.require_same_row(&foreign).unwrap_err(),
            "C512j Work capture requires its original packed allocation");
        assert!(capture.seal_row(&row).is_err(),"no second final seal");
        capture.require_same_row(&row).unwrap();
    }

    fn rejected_read(capture: &WorkEndpointCapture, binding: &HeaderSourceBinding,
        row: &NativePackedRow, tree: &NativeTreeSourceLease, wire: usize) {
        let checked=Cell::new(true);
        assert!(capture.checked_endpoint(&checked,binding,row,tree,wire).is_err());
        assert!(!checked.get(), "every failed checked read revokes the gate");
        assert!(WorkEndpointCapture::require_complete_checked(&checked).is_err(),
            "checked_local uses this same revoked gate");
        assert!(capture.checked_endpoint(&checked,binding,row,tree,
            binding.owner()*WIDTH+C512I_UPPER_BASE).is_err());
    }

    #[test]
    fn c512j_no_frame_checked_endpoint_faults_revoke_local_and_endpoint_gate() {
        let (mut capture,binding,mut row,tree,_) = isolated_parts();
        let wire=binding.owner()*WIDTH+C512I_UPPER_BASE;
        assert_eq!(capture.checked_endpoint(&Cell::new(true),&binding,&row,&tree,wire).unwrap(),
            (NativeWorkEndpointAuthor::Tree,false));
        assert!(capture.checked_endpoint(&Cell::new(false),&binding,&row,&tree,wire).is_err());
        rejected_read(&capture,&binding,&row,&tree,wire-WIDTH);
        rejected_read(&capture,&binding,&row,&tree,binding.owner()*WIDTH);
        for field in 0..6 {
            rejected_read(&capture,&binding.mutated_field_for_test(field),&row,&tree,wire);
        }
        let substitute=row.clone();
        rejected_read(&capture,&binding,&substitute,&tree,wire);
        row.bytes[C512I_UPPER_BASE/8]^=1u8<<(C512I_UPPER_BASE%8);
        rejected_read(&capture,&binding,&row,&tree,wire);
        row.bytes[C512I_UPPER_BASE/8]^=1u8<<(C512I_UPPER_BASE%8);
        let mut changed=tree.clone(); changed.author=TreeLeaseAuthor::Other;
        rejected_read(&capture,&binding,&row,&changed,wire);
        let mut changed=tree.clone(); changed.owned[C512I_UPPER_BASE/8]^=1u8<<(C512I_UPPER_BASE%8);
        rejected_read(&capture,&binding,&row,&changed,wire);
        let mut changed=tree.clone(); changed.values[C512I_UPPER_BASE/8]^=1u8<<(C512I_UPPER_BASE%8);
        rejected_read(&capture,&binding,&row,&changed,wire);
        capture.events[0].2=Fr::one();
        rejected_read(&capture,&binding,&row,&tree,wire);
        capture.events[0].2=Fr::from(2u64);
        let checked=Cell::new(true);
        assert_eq!(capture.checked_endpoint_fr(&checked,&binding,&row,&tree,wire)
            .unwrap_err(), "C577 original Work endpoint Fr is not Boolean");
        assert!(!checked.get());
        capture.events[0].2=Fr::zero();
        assert_eq!(capture.checked_endpoint_fr(&Cell::new(true),&binding,&row,&tree,wire)
            .unwrap(),(NativeWorkEndpointAuthor::Tree,Fr::zero()));
        capture.events.pop();
        rejected_read(&capture,&binding,&row,&tree,wire);
    }
}

struct MixedMapHeaderRoute {
    owner:usize,
    class:crate::daa_history_roster::OwnerClass,
    plan_headers:u64,
    plan_slot_log:usize,
    plan_slots:usize,
    input_header_count:usize,
    has_max_adapter:bool,
    padding_capture:bool,
    exact_map_pair:bool,
    has_other_source:bool,
}

fn require_mixed_map_header_route(route:&MixedMapHeaderRoute)->Result<(),String> {
    if !mixed_map_header_class_allowed(route.owner, route.class)
        || route.plan_headers!=crate::bank53_map::BANK53_N
        || route.plan_slot_log!=21 || route.plan_slots!=1<<21
        || route.input_header_count!=C449_PADDING_OWNER
        || route.has_max_adapter || route.padding_capture
        || !route.exact_map_pair || route.has_other_source {
        return Err("C450 mixed capture requires isolated owner845760 Carry/Map route".into());
    }
    require_mixed_map_header_no_scheduled(route.owner, route.class)
}

// Test-only physical writer seam for the two-context bank53 proposal. These
// constants are deliberately absent from production builds.
#[cfg(test)]
const BANK53_TEST_BASE: usize = BANK53_BASE;
#[cfg(test)]
const BANK53_TEST_CONTEXT_BITS: usize = BANK53_CONTEXT_BITS;
#[cfg(test)]
const BANK53_TEST_CONTEXTS: usize = BANK53_CONTEXTS;
#[cfg(test)]
const BANK53_TEST_LIVE_BITS: usize = 5_757 + crate::origin_score::LIVE;

pub(crate) struct NativePrefix {
    raws: Vec<Vec<u8>>,
    timestamps: Vec<i64>,
    compact_n_bits: Vec<u32>,
    root: [u8; 32],
    total: [u8; 28],
    profile: [u8; 32],
    lower: Vec<[u8; 28]>,
    upper: Vec<[u8; 28]>,
    leaves: Vec<[u8; 32]>,
    nodes: Vec<[u8; 32]>,
}

impl std::fmt::Debug for NativePrefix {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NativePrefix")
            .field("headers", &self.raws.len())
            .field("scalar_bytes", &(self.timestamps.len() * 12))
            .field("root", &self.root)
            .field("total", &self.total)
            .finish()
    }
}

impl NativePrefix {
    pub(crate) fn from_raw_headers(raws: &[Vec<u8>]) -> Result<Self, String> {
        if raws.len() != PREFIX_HEADERS {
            return Err("native prefix requires exactly 3073 headers".into());
        }
        Self::from_raw_iter(PREFIX_HEADERS, raws.iter().map(|raw| Ok(raw.clone())))
    }

    pub(crate) fn from_raw_iter<I>(expected_n: usize, raws: I) -> Result<Self, String>
    where
        I: IntoIterator<Item = Result<Vec<u8>, String>>,
    {
        if !(3..=MAX_NATIVE_HEADERS).contains(&expected_n) {
            return Err("native prefix count outside plan domain".into());
        }
        let mut owned_raws = Vec::new();
        owned_raws
            .try_reserve_exact(expected_n)
            .map_err(|_| "native prefix RAW allocation failed")?;
        let mut lower = Vec::new();
        lower
            .try_reserve_exact(expected_n)
            .map_err(|_| "native prefix lower-work allocation failed")?;
        lower.resize(expected_n, [0u8; 28]);
        let mut timestamps = Vec::new();
        timestamps
            .try_reserve_exact(expected_n)
            .map_err(|_| "native prefix timestamp allocation failed")?;
        let mut compact_n_bits = Vec::new();
        compact_n_bits
            .try_reserve_exact(expected_n)
            .map_err(|_| "native prefix compact allocation failed")?;
        let mut upper = Vec::new();
        upper
            .try_reserve_exact(expected_n)
            .map_err(|_| "native prefix upper-work allocation failed")?;
        upper.resize(expected_n, [0u8; 28]);

        let mut previous = [0u8; 32];
        let mut cumulative = BigUint::from(0u8);
        let mut raws = raws.into_iter();
        for index in 0..expected_n {
            let height = index + 1;
            let raw = raws
                .next()
                .ok_or_else(|| format!("native prefix RAW missing at height {height}"))??;
            if raw.is_empty() || raw.len() > 514 {
                return Err("native prefix RAW length".into());
            }
            let header = ergo_header_core::Header::decode(&raw, None)
                .map_err(|error| format!("native prefix decode: {error:?}"))?;
            if header.height != height as u32
                || header.parent_id != previous
                || header
                    .encode()
                    .map_err(|error| format!("native prefix encode: {error:?}"))?
                    != raw
            {
                return Err(format!(
                    "native prefix header {height} is not canonical"
                ));
            }
            previous = ergo_header_core::blake2b256(&raw);
            if index == 0 && previous != crate::header_order::MAINNET_GENESIS {
                return Err("native prefix genesis identity".into());
            }
            if index > 0 {
                lower[index] = u224_be28(&cumulative)?;
                let work = crate::work_tree_work::native_decode(header.n_bits)?;
                if work == BigUint::from(0u8) {
                    return Err(format!("native prefix header {height} has zero work"));
                }
                cumulative += work;
                upper[index] = u224_be28(&cumulative)?;
            }
            timestamps.push(header.timestamp);
            compact_n_bits.push(header.n_bits);
            owned_raws.push(raw);
        }
        if raws.next().is_some() {
            return Err("native prefix has extra RAW records".into());
        }

        let mut profile = crate::work_tree_fixed_hash::PROFILE_PREFIX.to_vec();
        profile.extend_from_slice(&crate::header_order::MAINNET_GENESIS);
        let profile: [u8; 32] = Blake2b::<U32>::digest(profile).into();
        let total = u224_be28(&cumulative)?;
        let (root, leaves, nodes) =
            derive_tree_root(expected_n, &owned_raws, &lower, &upper, profile)?;
        Ok(Self {
            raws: owned_raws,
            timestamps,
            compact_n_bits,
            root,
            total,
            profile,
            lower,
            upper,
            leaves,
            nodes,
        })
    }

    pub(crate) fn header_count(&self) -> usize {
        self.raws.len()
    }
    pub(crate) fn genuine_count(&self) -> usize {
        self.raws.len() - 1
    }
    pub(crate) fn slot_count(&self) -> usize {
        self.raws.len().next_power_of_two()
    }
    pub(crate) fn leaf_count(&self) -> usize {
        self.leaves.len()
    }
    pub(crate) fn node_count(&self) -> usize {
        self.nodes.len()
    }

    pub(crate) fn root(&self) -> [u8; 32] {
        self.root
    }
    pub(crate) fn total_be28(&self) -> [u8; 28] {
        self.total
    }
    pub(crate) fn profile(&self) -> [u8; 32] {
        self.profile
    }
    pub(crate) fn interval(&self, height: usize) -> Result<([u8; 28], [u8; 28]), String> {
        let index = height
            .checked_sub(1)
            .filter(|i| *i < self.header_count())
            .ok_or("interval height outside prefix")?;
        Ok((self.lower[index], self.upper[index]))
    }
    pub(crate) fn leaf_digest(&self, slot: usize) -> Result<[u8; 32], String> {
        self.leaves
            .get(slot)
            .copied()
            .ok_or_else(|| "native leaf outside prefix tree".into())
    }
    pub(crate) fn node_digest(&self, slot: usize) -> Result<[u8; 32], String> {
        self.nodes
            .get(slot)
            .copied()
            .ok_or_else(|| "native node outside prefix tree".into())
    }
    pub(crate) fn header(&self, height: usize) -> Result<ergo_header_core::Header, String> {
        let index = height.checked_sub(1).ok_or("height zero")?;
        let index = (index < self.header_count())
            .then_some(index)
            .ok_or_else(|| format!("prefix header {height} absent"))?;
        let header = ergo_header_core::Header::decode(&self.raws[index], None)
            .map_err(|error| format!("native prefix decode: {error:?}"))?;
        if header.height as usize != height
            || header.timestamp != self.timestamps[index]
            || header.n_bits != self.compact_n_bits[index]
        {
            return Err(format!("prefix header {height} scalar mismatch"));
        }
        Ok(header)
    }
    pub(crate) fn timestamp(&self, height: usize) -> Result<i64, String> {
        let index = height.checked_sub(1).ok_or("height zero")?;
        self.timestamps
            .get(index)
            .copied()
            .ok_or_else(|| format!("prefix header {height} absent"))
    }
    pub(crate) fn compact_n_bits(&self, height: usize) -> Result<u32, String> {
        let index = height.checked_sub(1).ok_or("height zero")?;
        self.compact_n_bits
            .get(index)
            .copied()
            .ok_or_else(|| format!("prefix header {height} absent"))
    }
    pub(crate) fn header_exists(&self, height: usize) -> bool {
        height != 0 && height <= self.header_count()
    }
    pub(crate) fn raw(&self, height: usize) -> Result<&[u8], String> {
        self.raws
            .get(height.checked_sub(1).ok_or("height zero")?)
            .map(Vec::as_slice)
            .ok_or_else(|| format!("prefix RAW {height} absent"))
    }
}

pub(crate) fn validate_native_plan_input(
    plan: &WorkTreeHistoryPlan,
    input: &NativePrefix,
) -> Result<(), String> {
    let n = input.header_count();
    if !(3..=MAX_NATIVE_HEADERS).contains(&n) || plan.headers() != n as u64 {
        return Err("native history plan/input count mismatch".into());
    }
    let descriptor = plan.descriptor();
    if descriptor.headers != n
        || descriptor.genuine != input.genuine_count()
        || descriptor.slots != input.slot_count()
        || descriptor.leaves != input.leaf_count()
        || descriptor.slots != input.node_count()
        || input.raws.len() != n
        || input.timestamps.len() != n
        || input.compact_n_bits.len() != n
        || input.lower.len() != n
        || input.upper.len() != n
    {
        return Err("native history plan/input shape mismatch".into());
    }
    if descriptor.root != input.root
        || plan.work_profile().total_be28 != input.total
        || plan.fixed_profile().tree != *descriptor
        || plan.leaf_profile().tree != *descriptor
        || plan.work_profile().tree != *descriptor
    {
        return Err("native history plan/input root, total or profile mismatch".into());
    }
    let mut profile_bytes = crate::work_tree_fixed_hash::PROFILE_PREFIX.to_vec();
    profile_bytes.extend_from_slice(&crate::header_order::MAINNET_GENESIS);
    let profile: [u8; 32] = Blake2b::<U32>::digest(profile_bytes).into();
    if input.profile != profile
        || plan.fixed_profile().genesis != crate::header_order::MAINNET_GENESIS
        || plan.fixed_profile().prefix.as_slice()
            != crate::work_tree_fixed_hash::PROFILE_PREFIX.as_slice()
        || plan.fixed_profile().native_work_sha256
            != crate::work_tree_fixed_hash::NATIVE_WORK_SHA256
        || plan.leaf_profile().native_work_sha256
            != crate::work_tree_fixed_hash::NATIVE_WORK_SHA256
        || plan.work_profile().native_work_sha256
            != crate::work_tree_fixed_hash::NATIVE_WORK_SHA256
    {
        return Err("native history mainnet profile mismatch".into());
    }
    plan.descriptor().validate()?;
    Ok(())
}

fn u224_be28(value: &BigUint) -> Result<[u8; 28], String> {
    if value.bits() > 224 {
        return Err("native prefix cumulative work exceeds U224".into());
    }
    let bytes = value.to_bytes_be();
    let mut output = [0u8; 28];
    output[28 - bytes.len()..].copy_from_slice(&bytes);
    Ok(output)
}

fn derive_tree_root(
    header_count: usize,
    raws: &[Vec<u8>],
    lower: &[[u8; 28]],
    upper: &[[u8; 28]],
    profile: [u8; 32],
) -> Result<([u8; 32], Vec<[u8; 32]>, Vec<[u8; 32]>), String> {
    use crate::work_tree_leaf_hash::{Envelope, LeafProfile};
    if raws.len() != header_count || lower.len() != header_count || upper.len() != header_count {
        return Err("native prefix tree input shape mismatch".into());
    }
    let leaf_profile = LeafProfile::new(header_count, [0; 32])?;
    let fixed_profile = crate::work_tree_fixed_hash::FixedProfile::new(header_count, [0; 32])?;
    if leaf_profile.tree.slots != fixed_profile.tree.slots
        || leaf_profile.tree.leaves != fixed_profile.tree.leaves
        || leaf_profile.tree.genuine != fixed_profile.tree.genuine
    {
        return Err("native prefix tree profile mismatch".into());
    }
    let mut leaves = Vec::with_capacity(leaf_profile.tree.leaves);
    for slot in 0..leaf_profile.tree.leaves {
        let envelope = if slot < leaf_profile.tree.genuine {
            let height = slot + 2;
            Envelope {
                raw: raws[height - 1].clone(),
                height: height as u32,
                lower: lower[height - 1],
                upper: upper[height - 1],
                profile,
            }
        } else {
            Envelope {
                raw: Vec::new(),
                height: 0,
                lower: [0; 28],
                upper: [0; 28],
                profile,
            }
        };
        leaves.push(crate::work_tree_leaf_hash::native_digest(
            &leaf_profile,
            slot,
            &envelope,
        )?);
    }
    let mut previous = leaves.clone();
    let mut nodes = vec![[0u8; 32]; leaf_profile.tree.slots];
    nodes[leaf_profile.tree.profile_node_slot] = profile;
    let mut root = [0u8; 32];
    for level in 1..=leaf_profile.tree.leaves.trailing_zeros() as usize {
        let (start, count) = leaf_profile.tree.level(level)?;
        let mut current = Vec::with_capacity(count);
        for position in 0..count {
            let mut node = Vec::with_capacity(70);
            node.push(b'N');
            node.push(level as u8);
            node.extend_from_slice(&(position as u32).to_be_bytes());
            node.extend_from_slice(&previous[2 * position]);
            node.extend_from_slice(&previous[2 * position + 1]);
            let digest = crate::work_tree_leaf_hash::native_fixed_preimage_hash(
                &fixed_profile,
                start + position,
                &node,
            )?;
            nodes[start + position] = digest;
            current.push(digest);
        }
        root = *current.last().ok_or("native prefix level is empty")?;
        previous = current;
    }
    Ok((root, leaves, nodes))
}

pub(crate) struct PreparedOwnerWindow {
    selection: OwnerSelection,
    bytes: Vec<u8>,
    receipt: AssemblyReceipt,
}

impl std::fmt::Debug for PreparedOwnerWindow {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PreparedOwnerWindow")
            .field("bytes", &self.bytes.len())
            .field("receipt", &self.receipt)
            .finish()
    }
}
#[cfg(test)]
mod max_join_tests {
    use super::*;
    use crate::max_header_adapter::{MaxHeaderAdapter, BASE};
    use std::io::Read;

    // Existing bounded bundle, never a nativeFrame rescan or downloaded input.
    fn bounded_input() -> NativePrefix {
        bounded_input_n(3)
    }
    pub(super) fn bounded_input_n(n:usize) -> NativePrefix {
        assert!((3..=17).contains(&n) || n == 1984);
        let dir = std::env::var_os("NIPOPOW_OWNER_ASSEMBLY_FIXTURE_DIR")
            .expect("existing frozen prefix fixture directory");
        let path = std::path::PathBuf::from(dir).join("mainnet-prefix-first-3073-u32le-v1.bin");
        let bundle = std::fs::read(path).expect("existing bounded prefix bundle");
        assert_eq!(bundle.len(), 869449);
        let digest = Blake2b::<U32>::digest(&bundle);
        let expected = "8CDB90DA475E646280113D97C9469BE7EB86A1D04F20404C64239187284FC009";
        assert_eq!(digest.iter().map(|b|format!("{b:02X}")).collect::<String>(),expected);
        let mut source = std::io::Cursor::new(bundle);
        let mut raws = Vec::new();
        for _ in 0..n {
            let mut length = [0;4]; source.read_exact(&mut length).unwrap();
            let length = u32::from_le_bytes(length) as usize;
            assert!((1..=514).contains(&length));
            let mut raw=vec![0;length]; source.read_exact(&mut raw).unwrap(); raws.push(raw);
        }
        NativePrefix::from_raw_iter(n,raws.into_iter().map(Ok)).unwrap()
    }
    fn bit(row:&NativePackedRow,wire:usize)->bool {row.bytes[wire/8] & (1<<(wire%8)) != 0}
    #[test]
    fn max_n3_native_join_and_consumer_binding() {
        let input = bounded_input();
        let plan = WorkTreeHistoryPlan::compile(3,2,input.root(),input.total_be28()).unwrap();
        let adapter = MaxHeaderAdapter::compile(&plan).unwrap();
        let producer = NativeOwnerProducer::new_for_max_history(&plan,&input,&adapter).unwrap();
        let old = NativeOwnerProducer::new_for_history(&plan,&input).unwrap();
        let exports = crate::native_owner_exports::NativeExports::new_for_history(&plan,&input).unwrap();
        let d0 = work::native_decode(input.compact_n_bits(2).unwrap()).unwrap();
        let d1 = work::native_decode(input.compact_n_bits(3).unwrap()).unwrap();
        assert!(d0>BigUint::from(0u8) && d1>BigUint::from(0u8));
        for owner in 0..4 {
            let row = producer.produce(owner).unwrap();
            let legacy = producer.produce_legacy_header_for_test(owner).unwrap();
            assert_eq!(row.bytes,legacy.bytes,"both seeders use identical bound permission");
            let old_row = old.produce(owner).unwrap();
            for wire in 0..WIDTH {
                if !(BASE..BASE+673).contains(&wire) {assert_eq!(bit(&row,wire),bit(&old_row,wire),"owner{owner} wire{wire}");}
            }
            let values=adapter.helpers(&input,owner).unwrap();
            assert_eq!((0..673).map(|i|Fr::from(bit(&row,BASE+i) as u64)).collect::<Vec<_>>(),values);
            if owner<2 {
                let current=if owner==0 {&d0} else {&d1};
                let next=if owner==0 {d1.clone()} else {BigUint::from(0u8)};
                let expected=current.clone().max(next.clone());
                for b in 0..224 {
                    assert_eq!(bit(&row,BASE+b),expected.bit(b as u64));
                    assert_eq!(bit(&row,BASE+224+b),next.bit(b as u64));
                    assert_eq!(bit(&row,crate::suffix_max::D_BASE+b),current.bit(b as u64),"work H=owner+2");
                }
                assert_eq!(bit(&row,BASE+672),current<&next);
            } else {assert!(values.iter().all(|v|v.is_zero()),"sentinel and padding keep zero helpers");}
            let receipt=validate_native_max_row_for_history_test(&adapter,&input,&row).unwrap();
            assert_eq!(receipt.groups.len(),6);
            assert!(validate_native_row_for_history_test(&plan,&input,&row,|index|exports.bit(index)).err().unwrap().contains("MAX consumer binding"));
            assert!(validate_native_max_row_for_history_test(&adapter,&input,&old_row).err().unwrap().contains("MAX consumer binding"));
            let mut rebound=producer.produce(owner).unwrap();
            rebound.max_binding.as_mut().unwrap()[0] ^= 1;
            assert_eq!(validate_native_max_row_for_history_test(&adapter,&input,&rebound).err().unwrap(),"native row MAX consumer binding mismatch");
            let mut mutant=producer.produce(owner).unwrap();
            flip_native_row_bit_for_test(&mut mutant,BASE).unwrap();
            assert!(validate_native_max_row_for_history_test(&adapter,&input,&mutant).is_err(),"active MAX/inactive zero single fault owner{owner}");
        }
        let wrong=WorkTreeHistoryPlan::compile(3,2,[0x73;32],input.total_be28()).unwrap();
        assert!(NativeOwnerProducer::new_for_max_history(&wrong,&input,&adapter).is_err());
        let different=MaxHeaderAdapter::compile(&wrong).unwrap();
        assert!(validate_native_max_row_for_history_test(&different,&input,&producer.produce(0).unwrap()).is_err());
    }
    #[test]
    fn max_structural_tie_assignment_and_selector_fault() {
        // Synthetic structural linked headers. This is not chain-validity evidence.
        let base=bounded_input();
        let mut raws=(1..=3).map(|h|base.raw(h).unwrap().to_vec()).collect::<Vec<_>>();
        let compact=base.compact_n_bits(2).unwrap();
        let mut h3=ergo_header_core::Header::decode(&raws[2],None).unwrap();
        h3.n_bits=compact; raws[2]=h3.encode().unwrap();
        let input=NativePrefix::from_raw_iter(3,raws.into_iter().map(Ok)).unwrap();
        let plan=WorkTreeHistoryPlan::compile(3,2,input.root(),input.total_be28()).unwrap();
        let adapter=MaxHeaderAdapter::compile(&plan).unwrap();
        let producer=NativeOwnerProducer::new_for_max_history(&plan,&input,&adapter).unwrap();
        let mut row=producer.produce(0).unwrap();
        assert!(!bit(&row,BASE+672),"tie chooses zero selector");
        assert!((BASE+448..BASE+672).all(|w|!bit(&row,w)),"tie delta zero");
        validate_native_max_row_for_history_test(&adapter,&input,&row).unwrap();
        flip_native_row_bit_for_test(&mut row,BASE+672).unwrap();
        assert!(validate_native_max_row_for_history_test(&adapter,&input,&row).is_err());
    }
    fn check_max_only(adapter:&MaxHeaderAdapter<'_>,input:&NativePrefix,row:&NativePackedRow)->Result<(),String> {
        let selection=OwnerSelection::Single{owner:row.owner,class:row.class};
        let mut rows=OwnedRows::new(selection);
        for wire in 0..WIDTH {rows.claim(row.owner,wire,Fr::from(bit(row,wire) as u64))?;}
        let mut terms=Vec::new();adapter.max().emit_owner(row.owner,|t|{terms.push(t);Ok(())})?;
        let mut group=Group{name:format!("MAX/{}",row.owner),terms};
        let mut support=BTreeSet::new();
        for term in &group.terms {reads(term,&mut |index|add_foreign(selection,4*WIDTH,&mut support,index))?;}
        let exports=crate::native_owner_exports::NativeExports::new_for_history(adapter.parent(),input)?;
        let mut helper_cache=BTreeMap::<usize,Vec<Fr>>::new();
        let mut reader=ForeignReader{read:|index:usize| {
            let owner=index/WIDTH;let local=index%WIDTH;
            if (BASE..BASE+673).contains(&local) {
                if !helper_cache.contains_key(&owner) {helper_cache.insert(owner,adapter.helpers(input,owner)?);}
                Ok(helper_cache[&owner][local-BASE].is_one())
            } else {exports.bit(index)}
        },support,cache:BTreeMap::new()};
        check_group(&mut group,&rows,&mut reader)
    }
    fn overwrite_integer(row:&mut NativePackedRow,base:usize,value:&BigUint) {
        for bit in 0..224 {let wire=base+bit;let mask=1u8<<(wire%8);
            row.bytes[wire/8]=(row.bytes[wire/8]&!mask) | if value.bit(bit as u64){mask}else{0};}
    }
    #[test]
    fn max_distinct_structural_suffix_and_same_x_import_faults() {
        // Structurally linked canonical encoding; intentionally violates DAA Carry.
        let base=bounded_input();
        let mut raws=(1..=3).map(|h|base.raw(h).unwrap().to_vec()).collect::<Vec<_>>();
        let mut h2=ergo_header_core::Header::decode(&raws[1],None).unwrap();
        h2.n_bits=0x03000002;raws[1]=h2.encode().unwrap();
        let mut h3=ergo_header_core::Header::decode(&raws[2],None).unwrap();
        h3.parent_id=ergo_header_core::blake2b256(&raws[1]);h3.n_bits=0x03000005;raws[2]=h3.encode().unwrap();
        let input=NativePrefix::from_raw_iter(3,raws.into_iter().map(Ok)).unwrap();
        let plan=WorkTreeHistoryPlan::compile(3,2,input.root(),input.total_be28()).unwrap();
        let adapter=MaxHeaderAdapter::compile(&plan).unwrap();
        let producer=NativeOwnerProducer::new_for_max_history(&plan,&input,&adapter).unwrap();
        let exports=crate::native_owner_exports::NativeExports::new_for_history(&plan,&input).unwrap();
        let mut first=producer.produce(0).unwrap();
        let mut second=producer.produce(1).unwrap();
        let terminal=producer.produce(2).unwrap();
        assert_eq!(work::native_decode(input.compact_n_bits(2).unwrap()).unwrap(),BigUint::from(2u8));
        assert_eq!(work::native_decode(input.compact_n_bits(3).unwrap()).unwrap(),BigUint::from(5u8));
        assert!(bit(&first,BASE+672),"D2 < suffix D3 requires selector1");
        assert!(!bit(&second,BASE+672),"last work owner compares D3 with zero terminal");
        for (row,m,next) in [(&first,5u8,5u8),(&second,5u8,0u8)] {
            for b in 0..224 {assert_eq!(bit(row,BASE+b),BigUint::from(m).bit(b as u64));
                assert_eq!(bit(row,BASE+224+b),BigUint::from(next).bit(b as u64));}
            check_max_only(&adapter,&input,row).unwrap();
        }
        check_max_only(&adapter,&input,&terminal).unwrap();
        let daa_error=validate_native_max_row_for_history_test(&adapter,&input,&terminal).err().unwrap();
        assert!(daa_error.starts_with("DAA/2 residual"),"proper Carry boundary: {daa_error}");
        // Shift only D from work owner0 to owner1, leaving every MAX helper unchanged.
        for b in 0..224 {let wire=crate::suffix_max::D_BASE+b;let mask=1u8<<(wire%8);
            let shifted=exports.bit(WIDTH+wire).unwrap();
            first.bytes[wire/8]=(first.bytes[wire/8]&!mask) | if shifted{mask}else{0};}
        assert!(check_max_only(&adapter,&input,&first).err().unwrap().starts_with("MAX/0 residual"));
        // Header H3 owner2 differs from its work owner1: copying H2's D is isolated.
        let wrong_header_d=work::native_decode(input.compact_n_bits(second.owner+1).unwrap()).unwrap();
        overwrite_integer(&mut second,crate::suffix_max::D_BASE,&wrong_header_d);
        assert!(check_max_only(&adapter,&input,&second).err().unwrap().starts_with("MAX/1 residual"));
        let mut forward=producer.produce(0).unwrap();
        overwrite_integer(&mut forward,BASE,&BigUint::from(2u8));
        assert!(check_max_only(&adapter,&input,&forward).err().unwrap().starts_with("MAX/0 residual"),"prefix direction cannot replace suffix MAX");
    }
    #[test]
    fn legacy_collector_admits_all_callback_rows_before_output_creation() {
        let output_dir=std::path::PathBuf::from(std::env::var_os("NIPOPOW_MAX_ADAPTER_TEST_OUTPUT_DIR")
            .expect("fresh owned MAX adapter test output directory"));
        assert!(output_dir.is_dir(),"runtime must provide its owned output directory");
        let input=bounded_input_n(17);
        let plan=WorkTreeHistoryPlan::compile(17,5,input.root(),input.total_be28()).unwrap();
        let producer=NativeOwnerProducer::new_for_history(&plan,&input).unwrap();
        for (bad_owner,kind,expected) in [(0,0,"rejects MAX rows"),(15,0,"rejects MAX rows"),
            (15,1,"original owner mismatch"),(15,2,"root/total mismatch"),
            (15,3,"root/total mismatch"),(15,4,"class mismatch"),(15,5,"row length mismatch")] {
            let path=output_dir.join(format!("collector-rejected-{kind}-{bad_owner}.bits"));
            assert!(!path.exists());let mut called=0;
            let result=write_native_window_for_test(&producer,&path,16,|owner| {
                called+=1;
                // Collector metadata fixture only; no row algebra claim.
                let mut row=NativePackedRow{owner,class:producer.roster.owner_class(owner as u64)?,
                    root:input.root(),total:input.total_be28(),bytes:vec![0;OWNER_BYTES],
                    header_source_binding:None,cap0_source:None,cap1_source:None,max_binding:None,
                    map_binding:None,map_context:None,legacy_binding:None};
                if owner==bad_owner {match kind {0=>row.max_binding=Some([9;32]),1=>row.owner+=1,
                    2=>row.root[0]^=1,3=>row.total[0]^=1,4=>row.class=crate::daa_history_roster::OwnerClass::Genesis,
                    _=>{row.bytes.pop();}}}
                Ok(row)
            });
            assert!(result.err().unwrap().contains(expected));
            assert_eq!(called,bad_owner+1);
            assert!(!path.exists(),"every rejected callback leaves destination absent");
        }
        // Successful transport fixture only; these metadata rows make no algebra claim.
        // The pattern varies within each owner and distinguishes adjacent owners.
        let expected=(0..16usize).flat_map(|owner|(0..OWNER_BYTES).map(move |offset|
            (offset as u8).wrapping_mul(37).wrapping_add((owner as u8)*11)^0xa5))
            .collect::<Vec<_>>();
        let expected_hash=Blake2b::<U32>::digest(&expected);
        let path=output_dir.join("collector-success-16-metadata.bits");
        assert!(!path.exists(),"successful artifact must be fresh and retained");
        let mut called=Vec::new();
        let result=write_native_window_for_test(&producer,&path,16,|owner| {
            called.push(owner);
            Ok(NativePackedRow{owner,class:producer.roster.owner_class(owner as u64)?,
                root:input.root(),total:input.total_be28(),
                bytes:expected[owner*OWNER_BYTES..(owner+1)*OWNER_BYTES].to_vec(),
                 header_source_binding:None,cap0_source:None,cap1_source:None,max_binding:None,
                map_binding:None,map_context:None,legacy_binding:None})
        }).unwrap();
        assert_eq!(called,(0..16).collect::<Vec<_>>());
        assert_eq!(result.source.input_len(),16*WIDTH);
        let actual=std::fs::read(&path).unwrap();
        assert_eq!(actual.len(),16*OWNER_BYTES);
        assert!(actual==expected,"exact packed bytes and owner order");
        assert_eq!(Blake2b::<U32>::digest(&actual),expected_hash,"packed transport hash oracle");
        for owner in 0..16 {
            for offset in [0,1,OWNER_BYTES/2,OWNER_BYTES-1] {
                let byte_index=owner*OWNER_BYTES+offset;
                let values=result.source.read_copy(8,byte_index).unwrap();
                for (bit,value) in values.iter().enumerate() {
                    assert_eq!(*value,Fr::from(((expected[byte_index]>>bit)&1) as u64),"LSB reader owner{owner} offset{offset} bit{bit}");
                }
            }
        }
        assert!(result.source.read_copy(8,16*OWNER_BYTES).is_err(),"reader stops at exact frame boundary");
        let io=result.source.io_metrics_snapshot();
        assert_eq!(io.write_calls,16);
        assert_eq!(io.write_bytes,(16*OWNER_BYTES) as u64);
        println!("collector_metadata_transport owners=16 bytes={} blake2b256={}",actual.len(),
            expected_hash.iter().map(|b|format!("{b:02X}")).collect::<String>());
    }
}

impl PreparedOwnerWindow {
    pub(crate) fn receipt(&self) -> &AssemblyReceipt {
        &self.receipt
    }
    pub(crate) fn first_owner(&self) -> u64 {
        self.selection.first_owner() as u64
    }
    pub(crate) fn owner_count(&self) -> usize {
        2
    }
    pub(crate) fn packed_bytes(&self) -> &[u8] {
        &self.bytes
    }
    pub(crate) fn row_bytes(&self, owner: u64) -> Option<&[u8]> {
        let index = usize::try_from(owner.checked_sub(self.first_owner())?).ok()?;
        (index < 2).then(|| &self.bytes[index * 131072..(index + 1) * 131072])
    }
}

pub(crate) const MAX_EXTERNAL_CELLS: usize = 8192;
pub(crate) const MAX_M1_EXTERNAL_CELLS: usize = 16384;
const OWNER_BYTES: usize = WIDTH / 8;

/// The caller cannot choose an arbitrary pair, schedule, class or cache bound.
#[derive(Clone, Copy)]
enum OwnerSelection {
    M1,
    M2,
    Single {
        owner: usize,
        class: crate::daa_history_roster::OwnerClass,
    },
}
impl OwnerSelection {
    fn first_owner(self) -> usize {
        match self {
            Self::M1 => 2047,
            Self::M2 => 3071,
            Self::Single { owner, .. } => owner,
        }
    }
    fn child_height(self) -> u32 {
        (self.first_owner() + self.count()) as u32
    }
    fn terminal_class(self) -> crate::daa_history_roster::OwnerClass {
        use crate::daa_history_roster::OwnerClass;
        match self {
            Self::M1 => OwnerClass::M1,
            Self::M2 => OwnerClass::Short(crate::short_daa_layout::Profile::M2),
            Self::Single { class, .. } => class,
        }
    }
    fn external_cap(self) -> usize {
        match self {
            Self::M1 => MAX_M1_EXTERNAL_CELLS,
            Self::M2 => MAX_EXTERNAL_CELLS,
            Self::Single { .. } => MAX_M1_EXTERNAL_CELLS,
        }
    }
    fn owners(self) -> std::ops::Range<usize> {
        self.first_owner()..self.first_owner() + self.count()
    }
    fn count(self) -> usize {
        match self {
            Self::M1 | Self::M2 => 2,
            Self::Single { .. } => 1,
        }
    }
}

#[derive(Debug)]
pub(crate) struct AssemblyReceipt {
    pub(crate) external_cells: usize,
    pub(crate) foreign_census: usize,
    pub(crate) groups: Vec<(String, usize)>,
}

#[derive(Clone, Copy)]
pub(crate) enum AssemblyFault {
    None,
    #[cfg(test)]
    ConflictingClaim {
        owner: u64,
        wire: usize,
    },
    #[cfg(test)]
    MissingClaim {
        owner: u64,
        wire: usize,
    },
    #[cfg(test)]
    NonBooleanClaim {
        owner: u64,
        wire: usize,
    },
    #[cfg(test)]
    FlipBit {
        owner: u64,
        wire: usize,
    },
    #[cfg(test)]
    FixedChildBit {
        owner: u64,
        branch: usize,
        bit: usize,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum NativePhysicalAuthor {
    Header,
    PointMembership,
    Tree,
    Daa,
    Bank53,
    Cap,
}
impl NativePhysicalAuthor {
    fn index(self) -> usize {
        match self {
            Self::Header => 0,
            Self::PointMembership => 1,
            Self::Tree => 2,
            Self::Daa => 3,
            Self::Bank53 => 4,
            Self::Cap => 5,
        }
    }
}

// C512c's scheduled MAX writer is distinct from the N3 diagnostic adapter
// and from the C374 owner-845759 six-author census.
const C512C_MAX_OWNER: usize = 844_798;
const C512C_MAX_BASE: [usize; 2] = [999_424, 1_000_097];
const C512C_MAX_BITS: usize = 673;
const C512C_WORK_D_BASE: usize = 987_674;
const C512C_WORK_D_BITS: usize = 224;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ScheduledMaxClass { owner: usize, active: [bool; 2] }
impl ScheduledMaxClass {
    fn rank(self, context: usize) -> Result<usize, String> {
        if context >= 2 || !self.active[context] { return Err("C576 inactive MAX context".into()); }
        Ok(self.active[..context].iter().filter(|active| **active).count())
    }
    fn count(self) -> usize { self.active.iter().filter(|active| **active).count() }
    fn reserves(self, local: usize) -> bool {
        (0..2).any(|c| self.active[c] && (C512C_MAX_BASE[c]..C512C_MAX_BASE[c]+C512C_MAX_BITS).contains(&local))
    }
}
fn scheduled_max_class(owner: usize) -> Result<ScheduledMaxClass, String> {
    use crate::h21_scheduled_max_cap::{MaxStep, Plan};
    static CALENDAR: OnceLock<Vec<(usize,[Option<MaxStep>;2])>> = OnceLock::new();
    let calendar = CALENDAR.get_or_init(|| Plan::eligible08().max_calendar());
    let index = calendar.binary_search_by(|(at,_)| at.cmp(&owner).reverse())
        .map_err(|_| "C576 owner outside scheduled MAX calendar")?;
    let steps = calendar[index].1;
    if steps.iter().flatten().any(|step| step.end != owner+2) {
        return Err("C576 MAX calendar end".into());
    }
    Ok(ScheduledMaxClass { owner, active: steps.map(|step| step.is_some()) })
}

fn c576_max_route(owner: usize, class: crate::daa_history_roster::OwnerClass) -> Result<ScheduledMaxClass,String> {
    let member=scheduled_max_class(owner)?;
    if class != crate::daa_history_roster::OwnerClass::Carry {
        return Err("C576 MAX physical route requires Carry".into());
    }
    let (max,cap)=mixed_map_header_schedule().owner_activity(owner)?;
    if cap != [false,false] || max != member.active {
        return Err("C576 MAX physical route activity/Cap coactivity".into());
    }
    Ok(member)
}
/// Conservative local retained-buffer budget, not a whole-Job memory limit.
pub(crate) fn c576_max_retained_bound(owner:usize)->Result<usize,String> {
    let member=scheduled_max_class(owner)?;
    let cells=224+673*member.count();let claims=673*member.count();
    let parts=[OWNER_BYTES.checked_mul(2),
        cells.checked_mul(2*std::mem::size_of::<(usize,crate::h21_scheduled_max_cap::MaxReplayAuthor,Fr)>()),
        claims.checked_mul(2*std::mem::size_of::<(usize,crate::h21_scheduled_max_cap::MaxReplayAuthor,bool)>()),
        claims.checked_mul(2*std::mem::size_of::<(usize,Fr)>()),
        Some(8*crate::bank53_map::CutDescriptor::eligible08().canonical_identity().len()),
        Some(8*std::mem::size_of::<CarryZeroBankClaim>()),Some(std::mem::size_of::<NativeScheduledMaxRow<'_, '_, '_>>())];
    parts.into_iter().try_fold(0usize,|sum,n|sum.checked_add(n?)).ok_or_else(||"C576 retained bound overflow".into())
}

fn c512f_require_separate_writer_options(
    regular: bool, max_source: bool, max_claims: bool,
) -> Result<(), String> {
    if regular && (max_source || max_claims) {
        return Err("C512f regular author capture cannot mix with scheduled MAX writer".into());
    }
    if max_source != max_claims {
        return Err("C512c MAX source and physical claim output must be paired".into());
    }
    Ok(())
}

fn c512f_reserves_header_max_window(owner: usize, has_max_source: bool, local: usize) -> bool {
    has_max_source && scheduled_max_class(owner).is_ok_and(|member| member.reserves(local))
}

fn c512j_require_separate_work_options(
    work: bool, c374: bool, regular: bool, max_source: bool, max_claims: bool,
) -> Result<(), String> {
    c512f_require_separate_writer_options(regular, max_source, max_claims)?;
    if work && (c374 || regular || max_source || max_claims) {
        return Err("C512j Work capture cannot mix with C374, regular or MAX capture".into());
    }
    Ok(())
}

struct NativeScheduledMaxSource<'s, 'm> {
    stream: &'s crate::h21_scheduled_max_cap::MaxStream<'m>,
    binding: HeaderSourceBinding,
    cells: Vec<(usize, crate::h21_scheduled_max_cap::MaxReplayAuthor, Fr)>,
    max: [Vec<(usize, Fr)>; 2],
    class: ScheduledMaxClass,
}

fn c512c_checked_max_cells(
    owner: usize,
    cells: &[(usize, crate::h21_scheduled_max_cap::MaxReplayAuthor, Fr)],
) -> Result<[Vec<(usize, Fr)>; 2], String> {
    use crate::h21_scheduled_max_cap::{MaxReplayAuthor, Writer};
    let member=scheduled_max_class(owner)?;
    if cells.len() != C512C_WORK_D_BITS + member.count() * C512C_MAX_BITS {
        return Err("C512c exact scheduled MAX owner/cell census".into());
    }
    let base = owner.checked_mul(WIDTH).ok_or("C512c MAX owner base overflow")?;
    for bit in 0..C512C_WORK_D_BITS {
        let (wire, author, value) = cells[bit];
        if wire != base + C512C_WORK_D_BASE + bit
            || author != (MaxReplayAuthor::NativeWorkD { height: owner + 2 })
            || !(value.is_zero() || value.is_one()) {
            return Err("C512c separate exact Work-D source cells".into());
        }
    }
    let mut max: [Vec<(usize,Fr)>;2] = std::array::from_fn(|_| Vec::new());
    for context in 0..2 {
        if !member.active[context] { continue; }
        max[context].try_reserve_exact(C512C_MAX_BITS).map_err(|_| "C576 MAX projection allocation")?;
        let rank=member.rank(context)?;
        for bit in 0..C512C_MAX_BITS {
            let (wire, author, value) = cells[C512C_WORK_D_BITS + rank*C512C_MAX_BITS + bit];
            let local = C512C_MAX_BASE[context] + bit;
            if wire != base + local
                || author != MaxReplayAuthor::Scheduled(Writer::Max {
                    context, end: owner + 2,
                }) || !(value.is_zero() || value.is_one()) {
                return Err("C512c exact MAX writer context/end/coordinate/value".into());
            }
            max[context].push((local, value));
        }
    }
    Ok(max)
}

fn c512c_require_header_max_reservation(
    owner: usize,
    cells: &[(usize, crate::h21_scheduled_max_cap::MaxReplayAuthor, Fr)],
    native: &[Fr],
    replacement_mask: &[bool],
) -> Result<(), String> {
    let max = c512c_checked_max_cells(owner, cells)?;
    if native.len() != WIDTH || replacement_mask.len() != WIDTH {
        return Err("C512c HEADER MAX reservation source widths".into());
    }
    for context in 0..2 {
        for &(local, _) in &max[context] {
            if replacement_mask[local] || !native[local].is_zero()
                || BANKS.iter().any(|&(start, end)| (start..end).contains(&local)) {
                return Err("C512c HEADER MAX reservation overlaps or replaces nonzero source".into());
            }
        }
    }
    Ok(())
}

/// The MAX token does not claim Work-D authorship. It does require the 224
/// Work-D values read from the same closed stream to match this packed row.
fn c512c_require_work_d_packed_source(
    cells: &[(usize, crate::h21_scheduled_max_cap::MaxReplayAuthor, Fr)],
    packed: &[u8],
) -> Result<(), String> {
    c576_require_work_d_packed_source(C512C_MAX_OWNER,cells,packed)
}
fn c576_require_work_d_packed_source(owner:usize,
    cells:&[(usize,crate::h21_scheduled_max_cap::MaxReplayAuthor,Fr)],packed:&[u8]) -> Result<(),String> {
    c512c_checked_max_cells(owner, cells)?;
    if packed.len() != OWNER_BYTES {
        return Err("C512c Work-D packed source width".into());
    }
    for bit in 0..C512C_WORK_D_BITS {
        let local = C512C_WORK_D_BASE + bit;
        let actual = packed[local / 8] & (1u8 << (local % 8)) != 0;
        if actual != cells[bit].2.is_one() {
            return Err(format!("C512c same-row Work-D source/packed wire{local}"));
        }
    }
    Ok(())
}

fn c576_physical_max_read(member:ScheduledMaxClass,
    cells:&[(usize,crate::h21_scheduled_max_cap::MaxReplayAuthor,Fr)],
    claims:&[(usize,crate::h21_scheduled_max_cap::MaxReplayAuthor,bool)],
    packed:&[u8],physical_wire:usize) -> Result<(crate::h21_scheduled_max_cap::MaxReplayAuthor,Fr),String> {
    use crate::h21_scheduled_max_cap::{MaxReplayAuthor,Writer};
    let local=physical_wire.checked_sub(member.owner.checked_mul(WIDTH).ok_or("C576 owner base overflow")?)
        .filter(|wire|*wire<WIDTH).ok_or("C512c MAX read outside source owner")?;
    let context=(0..2).find(|c|(C512C_MAX_BASE[*c]..C512C_MAX_BASE[*c]+C512C_MAX_BITS).contains(&local))
        .ok_or("C512c read outside scheduled MAX writer")?;
    let rank=member.rank(context)?;let bit=local-C512C_MAX_BASE[context];
    if cells.len()!=224+673*member.count() || claims.len()!=673*member.count() || packed.len()!=OWNER_BYTES {
        return Err("C576 physical MAX read extent".into());
    }
    let (wire,author,value)=cells[224+rank*673+bit];
    if value!=Fr::zero() && value!=Fr::one() { return Err("C576 original MAX Fr is not Boolean".into()); }
    let expected=MaxReplayAuthor::Scheduled(Writer::Max{context,end:member.owner+2});
    if wire!=physical_wire || author!=expected || claims[rank*673+bit]!=(local,expected,value.is_one())
        || (packed[local/8]>>(local%8)&1!=0)!=value.is_one() {
        return Err("C512c checked MAX author/source/row changed".into());
    }
    Ok((author,value))
}

/// One successful owner-local MAX write, captured from the actual exclusive
/// claim path. This does not install a global X cell or authenticate a PCS.
#[allow(dead_code)]
pub(crate) struct NativeScheduledMaxRow<'p, 'a, 'm> {
    row: NativePackedRow,
    daa: NativeDaaSourceLease<'p, 'a>,
    source: NativeScheduledMaxSource<'p, 'm>,
    claims: Vec<(usize, crate::h21_scheduled_max_cap::MaxReplayAuthor, bool)>,
    complete_checked: Cell<bool>,
}

// The ordinary MAX wrapper and the coactive borrowed view use one source,
// original-Fr, row, and zero-inclusive claim checker.
fn c581_check_max_on_row(row: &NativePackedRow, daa: &NativeDaaSourceLease<'_, '_>,
    source: &NativeScheduledMaxSource<'_, '_>,
    claims: &[(usize, crate::h21_scheduled_max_cap::MaxReplayAuthor, bool)])
    -> Result<(), String> {
    use crate::daa_history_roster::OwnerClass;
    use crate::h21_scheduled_max_cap::{MaxReplayAuthor, Writer};
    let producer = daa._source;
    let owner = source.class.owner;
    let member = c576_max_route(owner, row.class)?;
    source.stream.closed_native_snapshot(producer.plan, producer.input)?;
    let expected = HeaderSourceBinding::for_plan(producer.plan, owner)?;
    if source.binding != expected || source.binding.profile() != producer.input.profile()
        || row.owner != owner || row.class != OwnerClass::Carry || source.class != member
        || row.bytes.len() != OWNER_BYTES || row.max_binding.is_some()
        || row.cap0_source.is_some() || row.cap1_source.is_some()
        || row.map_binding.is_some() || row.map_context.is_some()
        || source.cells != source.stream.closed_owner_cells(owner)?
        || source.max != c512c_checked_max_cells(owner, &source.cells)?
        || claims.len() != member.count() * C512C_MAX_BITS {
        return Err("C512c sealed same-parent MAX source/row/census".into());
    }
    #[cfg(test)]
    if row.legacy_binding.is_some() {
        return Err("C512c MAX source rejects legacy row".into());
    }
    row.require_header_source_binding(&expected, owner, OwnerClass::Carry)?;
    daa.check_carry_zero_source(&expected)?;
    c576_require_work_d_packed_source(owner, &source.cells, &row.bytes)?;
    for context in 0..2 {
        if !member.active[context] { continue; }
        let rank = member.rank(context)?;
        for bit in 0..C512C_MAX_BITS {
            let (local, value) = source.max[context][bit];
            let author = MaxReplayAuthor::Scheduled(Writer::Max {
                context, end: owner + 2,
            });
            if claims[rank * C512C_MAX_BITS + bit]
                != (local, author, value.is_one())
                || (row.bytes[local / 8] & (1u8 << (local % 8)) != 0) != value.is_one() {
                return Err(format!("C512c physical MAX author/source/packed wire{local}"));
            }
        }
    }
    Ok(())
}

#[allow(dead_code)]
impl NativeScheduledMaxRow<'_, '_, '_> {
    fn bit(bytes: &[u8], local: usize) -> bool {
        bytes[local / 8] & (1u8 << (local % 8)) != 0
    }

    pub(crate) fn binding(&self) -> &HeaderSourceBinding { &self.source.binding }

    /// Live-reference custody gate. It performs NO completion or value reads.
    pub(crate) fn require_live_source(&self, producer:&NativeOwnerProducer<'_>,
        stream:&crate::h21_scheduled_max_cap::MaxStream<'_>) -> Result<(),String> {
        if !std::ptr::eq(self.source.stream,stream) { return Err("C576 physical MAX closed-stream identity".into()); }
        if !std::ptr::eq(self.daa._source,producer) { return Err("C576 physical MAX producer identity".into()); }
        let expected=HeaderSourceBinding::for_plan(producer.plan,self.source.class.owner)?;
        if self.source.binding!=expected || expected.profile()!=producer.input.profile() {
            return Err("C576 physical MAX live parent binding".into());
        }
        Ok(())
    }

    pub(crate) fn retained_capacity_bytes(&self)->Result<usize,String> {
        let mut size=self.row.bytes.capacity().checked_add(std::mem::size_of_val(self)).ok_or("C576 retained size overflow")?;
        for part in [self.source.cells.capacity().checked_mul(std::mem::size_of::<(usize,crate::h21_scheduled_max_cap::MaxReplayAuthor,Fr)>()),
            self.claims.capacity().checked_mul(std::mem::size_of::<(usize,crate::h21_scheduled_max_cap::MaxReplayAuthor,bool)>())] {
            size=size.checked_add(part.ok_or("C576 retained size overflow")?).ok_or("C576 retained size overflow")?;
        }
        for span in &self.source.max { size=size.checked_add(span.capacity().checked_mul(std::mem::size_of::<(usize,Fr)>())
            .ok_or("C576 retained size overflow")?).ok_or("C576 retained size overflow")?; }
        let DaaSourcePayload::CarryZero(banks)=&self.daa.source else {return Err("C576 retained non-CarryZero source".into());};
        for part in [Some(self.source.binding.cut.capacity()),Some(self.daa.binding.cut.capacity()),
            Some(self.row.header_source_binding.as_ref().map_or(0,|binding|binding.cut.capacity())),
            banks.banks.capacity().checked_mul(std::mem::size_of::<CarryZeroBankClaim>())] {
            size=size.checked_add(part.ok_or("C576 retained size overflow")?).ok_or("C576 retained size overflow")?;
        }
        Ok(size)
    }

    pub(crate) fn check_complete(&self) -> Result<(), String> {
        self.complete_checked.set(false);
        c581_check_max_on_row(&self.row, &self.daa, &self.source, &self.claims)?;
        self.complete_checked.set(true);
        Ok(())
    }

    pub(crate) fn checked_max_cell(&self, physical_wire: usize)
        -> Result<(crate::h21_scheduled_max_cap::MaxReplayAuthor, bool), String> {
        self.checked_max_cell_fr(physical_wire).map(|(author,value)|(author,value.is_one()))
    }

    pub(crate) fn checked_max_cell_fr(&self,physical_wire:usize)
        ->Result<(crate::h21_scheduled_max_cap::MaxReplayAuthor,Fr),String> {
        if !self.complete_checked.get() {
            return Err("C512c complete MAX writer census required".into());
        }
        let result=c576_physical_max_read(self.source.class,&self.source.cells,&self.claims,&self.row.bytes,physical_wire);
        if result.is_err(){self.complete_checked.set(false);}
        result
    }

    #[cfg(test)]
    pub(crate) fn c576_native_fr_read_controls(&mut self)->Result<(),String> {
        let index=self.source.cells.iter().enumerate().skip(224).find(|(_,cell)|cell.2.is_zero())
            .map(|(i,_)|i).ok_or("C576 genuine zero MAX read control unavailable")?;
        let original=self.source.cells[index];
        let baseline=self.checked_max_cell_fr(original.0)?;
        if baseline!=(original.1,original.2){return Err("C576 native original Fr read baseline".into());}
        self.source.cells[index].2=Fr::from(2u8);
        let result=self.checked_max_cell_fr(original.0);
        self.source.cells[index]=original;
        if result.err().as_deref()!=Some("C576 original MAX Fr is not Boolean") || self.complete_checked.get() {
            return Err("C576 original Fr2 must revoke physical readability".into());
        }
        if self.checked_max_cell_fr(original.0).err().as_deref()!=Some("C512c complete MAX writer census required") {
            return Err("C576 failed read retained a success gate".into());
        }
        self.check_complete()?;
        if self.checked_max_cell_fr(original.0)?!=baseline{return Err("C576 native Fr read recovery".into());}
        Ok(())
    }
}

#[cfg(test)]
mod c512c_scheduled_max_writer_tests {
    use super::*;
    use crate::daa_history_roster::OwnerClass;
    use crate::h21_scheduled_max_cap::{MaxReplayAuthor, Plan, Writer};

    fn cells() -> Vec<(usize, MaxReplayAuthor, Fr)> {
        let owner = C512C_MAX_OWNER;
        let base = owner * WIDTH;
        let mut out = Vec::with_capacity(C512C_WORK_D_BITS + 2*C512C_MAX_BITS);
        for bit in 0..C512C_WORK_D_BITS {
            out.push((base+C512C_WORK_D_BASE+bit,
                MaxReplayAuthor::NativeWorkD { height: owner+2 },
                Fr::from((bit%2) as u64)));
        }
        for context in 0..2 {
            for bit in 0..C512C_MAX_BITS {
                out.push((base+C512C_MAX_BASE[context]+bit,
                    MaxReplayAuthor::Scheduled(Writer::Max { context, end: owner+2 }),
                    Fr::from(((bit+context)%5==0) as u64)));
            }
        }
        out
    }

    fn generic_cells(owner:usize)->Vec<(usize,MaxReplayAuthor,Fr)> {
        let member=scheduled_max_class(owner).unwrap();let mut out=Vec::new();
        for bit in 0..224 {out.push((owner*WIDTH+987_674+bit,MaxReplayAuthor::NativeWorkD{height:owner+2},Fr::zero()));}
        for context in 0..2 {if member.active[context] {for bit in 0..673 {
            out.push((owner*WIDTH+C512C_MAX_BASE[context]+bit,
                MaxReplayAuthor::Scheduled(Writer::Max{context,end:owner+2}),Fr::zero()));
        }}}
        out
    }
    fn generic_physical(owner:usize)->(Vec<(usize,MaxReplayAuthor,Fr)>,Vec<(usize,MaxReplayAuthor,bool)>,Vec<u8>) {
        let cells=generic_cells(owner);
        let claims=cells[224..].iter().map(|&(wire,author,_)|(wire%WIDTH,author,false)).collect();
        (cells,claims,vec![0;OWNER_BYTES])
    }
    fn c576_family_controls() {
        let plan=WorkTreeHistoryPlan::compile(1_827_840,21,[0x61;32],[0x62;28]).unwrap();
        let roster=DaaHistoryRoster::compile(&plan).unwrap();let calendar=mixed_map_header_schedule().max_calendar();
        let mut masks=[0usize;3];let mut seen=std::collections::BTreeSet::new();
        for &(owner,steps) in &calendar {
            assert!(seen.insert(owner));let class=c576_max_route(owner,roster.owner_class(owner as u64).unwrap()).unwrap();
            assert_eq!(class.active,steps.map(|step|step.is_some()));
            match class.active {[true,true]=>masks[0]+=1,[false,true]=>masks[1]+=1,[true,false]=>masks[2]+=1,_=>panic!("empty MAX class")}
            for context in 0..2 {for bit in [0,672] {
                assert_eq!(class.reserves(C512C_MAX_BASE[context]+bit),class.active[context]);
            }}
            for protected in [0,524_288,677_501,685_693,786_432,917_504,987_674,999_423,1_000_770,1_002_818] {
                assert!(!class.reserves(protected));
            }
        }
        assert_eq!((calendar.len(),masks),(7683,[7549,1,133]));
        assert_eq!(scheduled_max_class(1_810_840).unwrap().active,[false,true]);
        assert_eq!(scheduled_max_class(1_827_838).unwrap().active,[true,false]);
        for owner in [844_669,844_671,844_800,845_759,845_887,846_015,1_810_841,1_810_904,1_827_840,1<<21] {
            assert!(scheduled_max_class(owner).is_err(),"invalid owner {owner}");
        }
        assert!(c576_max_route(844_926,OwnerClass::Padding).is_err());
        for owner in [844_670,844_798,844_926,1_810_814,1_810_840,1_810_942,1_827_838] {
            let member=scheduled_max_class(owner).unwrap();let(cells,claims,packed)=generic_physical(owner);
            let spans=c512c_checked_max_cells(owner,&cells).unwrap();
            for context in 0..2 {
                assert_eq!(spans[context].len(),if member.active[context]{673}else{0});
                for bit in [0,224,448,672] {
                    let wire=owner*WIDTH+C512C_MAX_BASE[context]+bit;
                    let got=c576_physical_max_read(member,&cells,&claims,&packed,wire);
                    assert_eq!(got.is_ok(),member.active[context]);
                    if member.active[context] {assert_eq!(got.unwrap(),(MaxReplayAuthor::Scheduled(Writer::Max{context,end:owner+2}),Fr::zero()));}
                }
            }
            c512c_require_header_max_reservation(owner,&cells,&vec![Fr::zero();WIDTH],&vec![false;WIDTH]).unwrap();
            // Mutate one consumed field at a time, including zero occurrences.
            for index in [0,223,224,cells.len()-1] {for field in 0..8 {
                let mut bad=cells.clone();
                match field {0=>{bad.remove(index);},1=>{bad.push(bad[index]);},
                    2=>bad[index].0+=1,3=>bad[index].1=MaxReplayAuthor::NativeWorkD{height:owner+3},
                    4=>bad[index].1=MaxReplayAuthor::Scheduled(Writer::Max{context:2,end:owner+2}),
                    5=>bad[index].1=MaxReplayAuthor::Scheduled(Writer::Max{context:0,end:owner+3}),
                    6=>bad[index].2=Fr::from(2u8),_=>bad.swap(index,if index==0{1}else{0})}
                assert!(c512c_checked_max_cells(owner,&bad).is_err(),"{owner}/{index}/{field}");
                c512c_checked_max_cells(owner,&cells).unwrap();
            }}
            let context=if member.active[0]{0}else{1};let local=C512C_MAX_BASE[context];
            let mut native=vec![Fr::zero();WIDTH];native[local]=Fr::one();
            assert!(c512c_require_header_max_reservation(owner,&cells,&native,&vec![false;WIDTH]).is_err());
            native[local]=Fr::zero();let mut mask=vec![false;WIDTH];mask[local]=true;
            assert!(c512c_require_header_max_reservation(owner,&cells,&native,&mask).is_err());
            if member.count()==1 {
                let inactive=C512C_MAX_BASE[1-context];native[inactive]=Fr::one();mask[inactive]=true;mask[local]=false;
                c512c_require_header_max_reservation(owner,&cells,&native,&mask).unwrap();
                assert!(!member.reserves(inactive));
            }
            let wire=owner*WIDTH+local;
            for field in 0..5 {
                let mut bad_cells=cells.clone();let mut bad_claims=claims.clone();let mut bad_packed=packed.clone();
                match field {0=>bad_cells[224].2=Fr::from(2u8),1=>bad_claims[0].1=MaxReplayAuthor::NativeWorkD{height:owner+2},
                    2=>{bad_claims.pop();},3=>bad_packed[local/8]^=1<<(local%8),_=>bad_cells[224].0+=1}
                assert!(c576_physical_max_read(member,&bad_cells,&bad_claims,&bad_packed,wire).is_err());
                c576_physical_max_read(member,&cells,&claims,&packed,wire).unwrap();
            }
        }
        let member=scheduled_max_class(1_810_840).unwrap();let(mut cells,claims,packed)=generic_physical(member.owner);
        assert_eq!(member.rank(1).unwrap(),0);
        assert!(member.rank(0).is_err());
        cells[224].0=member.owner*WIDTH+999_424;
        cells[224].1=MaxReplayAuthor::Scheduled(Writer::Max{context:0,end:member.owner+2});
        assert!(c512c_checked_max_cells(member.owner,&cells).is_err());
        assert!(c576_physical_max_read(member,&cells,&claims,&packed,member.owner*WIDTH+999_424).is_err());
    }

    #[test]
    fn c512c_no_frame_calendar_header_reservation_and_zero_claim_mutants() {
        crate::h21_scheduled_max_cap::c576_owner_activity_controls();
        c576_family_controls();
        let calendar = Plan::eligible08().max_calendar();
        let selected = calendar.iter().filter(|(owner, _)| *owner==C512C_MAX_OWNER)
            .collect::<Vec<_>>();
        assert_eq!(selected.len(),1);
        assert!(selected[0].1.iter().all(|step| step.is_some_and(|step|
            step.end==C512C_MAX_OWNER+2)));
        assert!(!calendar.iter().any(|(owner, _)| *owner==845_759),
            "first-modern owner keeps ordinary HEADER MAX-window authorship");

        let honest = cells();
        let projected = c512c_checked_max_cells(C512C_MAX_OWNER,&honest).unwrap();
        assert_eq!(projected.map(|span|span.len()),[C512C_MAX_BITS;2]);
        let mut packed_work_d = vec![0u8; OWNER_BYTES];
        for bit in 0..C512C_WORK_D_BITS {
            let local = C512C_WORK_D_BASE + bit;
            if honest[bit].2.is_one() {
                packed_work_d[local/8] |= 1u8 << (local%8);
            }
        }
        c512c_require_work_d_packed_source(&honest,&packed_work_d).unwrap();
        packed_work_d[C512C_WORK_D_BASE/8] ^= 1u8 << (C512C_WORK_D_BASE%8);
        assert!(c512c_require_work_d_packed_source(&honest,&packed_work_d).is_err(),
            "MAX source does not authorize a different Work-D value in the same row");
        let native = vec![Fr::zero(); WIDTH];
        let mask = vec![false; WIDTH];
        c512c_require_header_max_reservation(C512C_MAX_OWNER,&honest,&native,&mask).unwrap();

        let mut missing = honest.clone();missing.pop();
        assert!(c512c_checked_max_cells(C512C_MAX_OWNER,&missing).is_err());
        let mut duplicate = honest.clone();duplicate[C512C_WORK_D_BITS+1] = duplicate[C512C_WORK_D_BITS];
        assert!(c512c_checked_max_cells(C512C_MAX_OWNER,&duplicate).is_err());
        let mut wrong_owner = honest.clone();wrong_owner[C512C_WORK_D_BITS].0 -= WIDTH;
        assert!(c512c_checked_max_cells(C512C_MAX_OWNER,&wrong_owner).is_err());
        let mut wrong_context = honest.clone();wrong_context[C512C_WORK_D_BITS].1 =
            MaxReplayAuthor::Scheduled(Writer::Max {context:1,end:C512C_MAX_OWNER+2});
        assert!(c512c_checked_max_cells(C512C_MAX_OWNER,&wrong_context).is_err());
        let mut wrong_end = honest.clone();wrong_end[C512C_WORK_D_BITS].1 =
            MaxReplayAuthor::Scheduled(Writer::Max {context:0,end:C512C_MAX_OWNER+3});
        assert!(c512c_checked_max_cells(C512C_MAX_OWNER,&wrong_end).is_err());
        let mut wrong_work_d = honest.clone();wrong_work_d[0].1 =
            MaxReplayAuthor::NativeWorkD {height:C512C_MAX_OWNER+1};
        assert!(c512c_checked_max_cells(C512C_MAX_OWNER,&wrong_work_d).is_err());
        let mut nonboolean = honest.clone();nonboolean[C512C_WORK_D_BITS].2 = Fr::from(2u64);
        assert!(c512c_checked_max_cells(C512C_MAX_OWNER,&nonboolean).is_err());
        assert!(c512c_checked_max_cells(845_759,&honest).is_err());

        let mut nonzero_header = native.clone();nonzero_header[C512C_MAX_BASE[0]] = Fr::one();
        assert!(c512c_require_header_max_reservation(C512C_MAX_OWNER,&honest,
            &nonzero_header,&mask).is_err());
        let mut tree_overlap = mask.clone();tree_overlap[C512C_MAX_BASE[1]] = true;
        assert!(c512c_require_header_max_reservation(C512C_MAX_OWNER,&honest,
            &native,&tree_overlap).is_err());
        assert!(c512c_require_header_max_reservation(845_759,&honest,&native,&mask).is_err());

        let mut rows = OwnedRows::new(OwnerSelection::Single {
            owner:C512C_MAX_OWNER,class:OwnerClass::Carry,
        });
        let local = C512C_MAX_BASE[0];
        rows.claim_exclusive(C512C_MAX_OWNER,local,Fr::zero()).unwrap();
        assert!(rows.claim_exclusive(C512C_MAX_OWNER,local,Fr::zero()).is_err(),
            "an authored zero is still an exclusive physical claim");
    }

    #[test]
    fn c512c_old_diagnostic_adapter_rejects_h21_no_frame() {
        let plan = WorkTreeHistoryPlan::compile(1_827_840,21,[0x61;32],[0x62;28]).unwrap();
        assert!(crate::max_header_adapter::MaxHeaderAdapter::compile(&plan)
            .err().unwrap().contains("requires N3/C4/S2"));
    }

    #[test]
    fn c512f_writer_options_and_unscheduled_header_window_no_frame() {
        c512f_require_separate_writer_options(false, false, false).unwrap();
        c512f_require_separate_writer_options(true, false, false).unwrap();
        c512f_require_separate_writer_options(false, true, true).unwrap();
        for (regular, source, claims) in [
            (true, true, true), (true, true, false), (true, false, true),
            (false, true, false), (false, false, true),
        ] {
            assert!(c512f_require_separate_writer_options(regular, source, claims).is_err());
        }
        let calendar = Plan::eligible08().max_calendar();
        for owner in [845_759, 845_887] {
            assert!(!calendar.iter().any(|(scheduled, _)| *scheduled == owner));
            for local in [C512C_MAX_BASE[0], C512C_MAX_BASE[1],
                C512C_MAX_BASE[1] + C512C_MAX_BITS - 1] {
                assert!(!c512f_reserves_header_max_window(owner, true, local));
                assert!(!c512f_reserves_header_max_window(owner, false, local));
            }
        }
        assert!(!c512f_reserves_header_max_window(C512C_MAX_OWNER, false, C512C_MAX_BASE[0]));
        assert!(c512f_reserves_header_max_window(C512C_MAX_OWNER, true, C512C_MAX_BASE[0]));
        assert!(!c512f_reserves_header_max_window(C512C_MAX_OWNER, true,
            C512C_MAX_BASE[1] + C512C_MAX_BITS));
    }
}

/// Separate physical claim phases for one regular Score owner. C374's six
/// classes and Point reservation remain specific to owner 845759.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum NativeRegularPhysicalAuthor { Header, Tree, Daa, Scored }

// The old C509/C514 admissions remain fixed845887. This private dispatch is
// shared only by the two actual complete physical writer routes.
fn c574_regular_owner(owner: usize) -> Result<(), String> {
    if matches!(owner, 845_887 | 846_015) { Ok(()) }
    else { Err("C574 complete regular writer requires fixed845887 or846015".into()) }
}

pub(crate) fn c574_require_binding(actual: &HeaderSourceBinding,
    expected: &HeaderSourceBinding) -> Result<(), String> {
    c574_regular_owner(actual.owner())?;
    if actual != expected { return Err("C574 retained native source parent/cut/owner".into()); }
    Ok(())
}

#[cfg(test)]
pub(crate) fn c574_writer_controls_for_test() -> Result<(), String> {
    c574_regular_owner(845_887)?;
    c574_regular_owner(846_015)?;
    for owner in [845_759, 845_888, 846_143, 1_810_904, 1 << 21] {
        if c574_regular_owner(owner).is_ok() { return Err("C574 broad owner admission".into()); }
    }
    let expected = HeaderSourceBinding::diagnostic_for_test(846_015);
    c574_require_binding(&expected, &expected)?;
    for fault in 0..6 {
        let mut changed = expected.clone();
        match fault {
            0 => changed.root[0] ^= 1, 1 => changed.total[0] ^= 1,
            2 => changed.profile[0] ^= 1, 3 => changed.layout[0] ^= 1,
            4 => changed.cut.push(1), _ => changed.owner = 845_887,
        }
        if c574_require_binding(&changed, &expected).is_ok() { return Err("C574 changed source binding".into()); }
    }
    for owner in [845_887, 846_015] {
        let map = H21EligibleMapStage::map_live(0)?.start;
        c574_required_bank53_author(owner, map, true, false, false, Fr::zero())?;
        if c574_required_bank53_author(owner, map, false, false, false, Fr::zero()).is_ok()
            || c574_required_bank53_author(owner, map, true, true, false, Fr::zero()).is_ok()
            || c574_required_bank53_author(owner, map, true, false, true, Fr::zero()).is_ok() {
            return Err("C574 missing/overlapping required Map author".into());
        }
        let slack = H21EligibleMapStage::slack_live(0)?.start;
        c574_required_bank53_author(owner, slack, true, false, false, Fr::zero())?;
        if c574_required_bank53_author(owner, slack, false, false, false, Fr::zero()).is_ok() {
            return Err("C574 missing dedicated Slack author".into());
        }
        for local in [crate::segment_points::POINT_OFFSET, 999_424, slack] {
            let fake = h21_eligible_context::ScoredOwnerPackedCell::synthetic_for_test(
                owner * WIDTH + local, ScoredOwnerPackedAuthor::Score(
                    h21_eligible_context::ScoreReplayAuthor {context:0,origin:owner+1,
                        previous_owner:owner-128,max_owner:owner-1089,cap_owner:owner}), false);
            if scored_owner_cell_local(owner, &fake).is_ok() { return Err("C574 source writer domain escaped".into()); }
        }
    }
    let inactive_score = H21EligibleMapStage::score_live(0)?.start;
    c574_required_bank53_author(845_888, inactive_score, false, false, false, Fr::zero())?;
    if c574_required_bank53_author(845_888, inactive_score, true, false, false, Fr::zero()).is_ok()
        || c574_required_bank53_author(845_888, inactive_score, false, false, false, Fr::from(2u64)).is_ok() {
        return Err("C574 inactive HEADER-zero policy".into());
    }
    Ok(())
}

fn c574_required_bank53_author(owner: usize, local: usize, scored: bool,
    tree: bool, daa: bool, header: Fr) -> Result<(), String> {
    use crate::bank53_required_writer::{required_bank53_writer, RequiredWriter};
    for context in 0..2 {
        let base = H21EligibleMapStage::map_live(context)?.start;
        if let Some(offset) = local.checked_sub(base).filter(|offset| *offset < 8192) {
            let required = required_bank53_writer(owner, context, offset)?;
            let valid = match required {
                RequiredWriter::HeaderZero => !scored && !tree && !daa && header.is_zero(),
                RequiredWriter::Map { .. } | RequiredWriter::ScoreReplay { .. }
                    | RequiredWriter::Slack { .. } => scored && !tree && !daa,
                RequiredWriter::ScoreAnchor { .. } => false,
            };
            if !valid { return Err(format!("C574 required writer owner{owner} local{local} {required:?}")); }
        }
    }
    Ok(())
}

/// Named, data-only facts needed to admit the one padded-owner capture route.
struct PaddingHeaderZeroRoute {
    capture_requested: bool,
    owner: usize,
    class: crate::daa_history_roster::OwnerClass,
    plan_headers: u64,
    plan_slot_log: usize,
    plan_slots: usize,
    input_header_count: usize,
    has_max_adapter: bool,
    test_header_route: bool,
    has_bank53_map: bool,
    has_cap0: bool,
    has_cap1: bool,
    has_overlay: bool,
    has_census: bool,
    has_scored_source: bool,
    has_map_source: bool,
    has_daa_source_out: bool,
}

fn require_padding_header_zero_route(route: &PaddingHeaderZeroRoute) -> Result<(), String> {
    use crate::daa_history_roster::OwnerClass;
    if !route.capture_requested {
        return Ok(());
    }
    if route.owner < C449_PADDING_OWNER
        || route.owner >= MAX_NATIVE_HEADERS
        || route.class != OwnerClass::Padding
        || route.plan_headers != crate::bank53_map::BANK53_N
        || route.plan_slot_log != 21
        || route.plan_slots != 1 << 21
        || route.input_header_count != C449_PADDING_OWNER
        || route.has_max_adapter
        || route.test_header_route
        || route.has_bank53_map
        || route.has_cap0
        || route.has_cap1
        || route.has_overlay
        || route.has_census
        || route.has_scored_source
        || route.has_map_source
        || route.has_daa_source_out
    {
        return Err("C449 padding HEADER-zero capture requires isolated native seed route".into());
    }
    Ok(())
}

struct OwnedRows {
    selection: OwnerSelection,
    values: Vec<Vec<Fr>>,
    claimed: Vec<Vec<bool>>,
    author_census: Option<Vec<Option<NativePhysicalAuthor>>>,
    current_author: Option<NativePhysicalAuthor>,
    regular_author_census: Option<Vec<Option<NativeRegularPhysicalAuthor>>>,
    current_regular_author: Option<NativeRegularPhysicalAuthor>,
    work_endpoint_capture: Option<WorkEndpointCapture>,
    padding_header_zero_capture: Option<PaddingHeaderZeroCapture>,
    mixed_map_header_capture: Option<MixedMapHeaderCapture>,
    c491_genesis_header_zero_capture: Option<C491GenesisHeaderZeroClaims>,
    c496_clipped_header_zero_capture: Option<C496ClippedHeaderZeroClaims>,
    c498_clipped_score_capture: Option<C498ClippedScoreClaims>,
}

/// A source relation borrow and its original Map Pair remain live through packing.
/// Foreign read addresses and values are checked; their physical authors are not.
pub(crate) struct C498ClippedScoreSource<'r, 'src, 'm> {
    relation: &'r h21_eligible_context::H21ClosedScoreOwnerRelation<'src>,
    lease: &'m Eligible08MapPairLease,
    binding: HeaderSourceBinding,
    context: usize,
}

impl<'r, 'src, 'm> C498ClippedScoreSource<'r, 'src, 'm> {
    pub(crate) fn new(
        relation: &'r h21_eligible_context::H21ClosedScoreOwnerRelation<'src>,
        binding: &HeaderSourceBinding, lease: &'m Eligible08MapPairLease,
        context: usize,
    ) -> Result<Self, String> {
        let source = Self { relation, lease, binding: binding.clone(), context };
        source.validate()?;
        Ok(source)
    }

    fn validate(&self) -> Result<(), String> {
        use h21_eligible_context::{ScoreRelationReadAuthor as Read, ScoreReplayAuthor};
        use crate::{origin_score as score, gkr::Gate};
        let (owner, previous, max_owner) = match self.context {
            0 => (1_810_904, 1_810_879, 1_809_918),
            1 => (1_810_841, 1_810_751, 1_809_790),
            _ => return Err("C498 clipped context".into()),
        };
        let c = self.context;
        let relation = self.relation;
        c496_require_binding(&self.binding, c)?;
        if relation.owner() != owner || self.binding.owner() != owner
            || !self.binding.matches_sink(relation.parent_root(), relation.parent_total(),
                relation.parent_profile(), relation.cut_identity(), owner)
            || self.lease.binding() != &self.binding {
            return Err("C498 source parent/owner identity".into());
        }
        self.lease.checked_cells(&self.binding, owner, crate::daa_history_roster::OwnerClass::Carry)?;
        relation.require_original_map_bindings([
            self.lease.map_binding(0)?, self.lease.map_binding(1)?])?;
        let author = ScoreReplayAuthor { context: c, origin: owner + 1,
            previous_owner: previous, max_owner, cap_owner: owner };
        if relation.authors()[c] != Some(author) || relation.authors()[1-c].is_some()
            || !relation.terms(1-c)?.is_empty() || relation.cells().len() != 2_048 {
            return Err("C498 active source census".into());
        }
        let input = (owner << 20) + [677_501, 685_693][c];
        let prior = (previous << 20) + [677_501, 685_693][c];
        for (ordinal, &(wire, found, value)) in relation.cells().iter().enumerate() {
            if wire != input + ordinal || found != author
                || (value != Fr::zero() && value != Fr::one())
                || (ordinal >= 1_994 && value != Fr::zero()) {
                return Err(format!("C498 source cell ordinal {ordinal}"));
            }
        }
        let spec = score::Spec { active: true, origin_one: false, reducing: true,
            first: false, terminal: false, empty_terminal: false,
            maturity: [4_995, 2_090][c], guard_total: None, expected: BigUint::from(0u8) };
        let mut terms = Vec::with_capacity(8_545);
        score::emit_local(&spec, |local| {
            let t = local.term;
            terms.push(Term { row: (owner << 19) + [487_421, 502_652][c] + t.row,
                gate: Gate { left: if local.previous { prior + t.gate.left }
                    else { input + t.gate.left }, right: input + t.gate.right,
                    c0: t.gate.c0, c1: t.gate.c1, c2: t.gate.c2, c3: t.gate.c3 } });
        })?;
        let layout = score::Layout::new();
        let cap = (owner << 20) + [1_000_770, 1_002_818][c] + 740;
        let work = ((owner - 1) << 20) + 987_450;
        let zero = Fr::zero(); let one = Fr::one();
        let mut reads = Vec::with_capacity(514);
        for bit in 0..225 {
            reads.push((prior + layout.r.start + bit,
                Read::PreviousR { context: c, owner: previous },
                relation.cells()[layout.p.start + bit].2));
        }
        for bit in 0..65 {
            terms.push(Term { row: (owner << 19) + [491_629, 506_860][c] + bit,
                gate: Gate { left: input + layout.sv.start + bit, right: cap + bit,
                    c0: zero, c1: one, c2: -one, c3: zero } });
            reads.push((cap + bit, Read::Cap { context: c, origin: owner + 1,
                max_owner, cap_owner: owner }, relation.cells()[layout.sv.start + bit].2));
        }
        for bit in 0..224 {
            let row = (owner << 19) + [491_694, 506_925][c] + bit;
            terms.push(Term { row, gate: Gate { left: input + layout.sw.start + bit,
                right: 0, c0: zero, c1: one, c2: zero, c3: zero } });
            terms.push(Term { row, gate: Gate { left: work + bit,
                right: 0, c0: zero, c1: -one, c2: zero, c3: zero } });
            reads.push((work + bit, Read::WorkUpper { owner: owner - 1, height: owner + 1 },
                relation.cells()[layout.sw.start + bit].2));
        }
        if terms.len() != 8_545 || relation.terms(c)?.len() != terms.len()
            || reads.len() != 514 || relation.reads().len() != reads.len() {
            return Err("C498 term/read census".into());
        }
        for (ordinal, (found, expected)) in relation.terms(c)?.iter().zip(&terms).enumerate() {
            if found != expected { return Err(format!("C498 term ordinal {ordinal}")); }
        }
        for (ordinal, (found, expected)) in relation.reads().iter().zip(&reads).enumerate() {
            if found != expected { return Err(format!("C498 read ordinal {ordinal}")); }
        }
        Ok(())
    }
}

struct C498ClippedScoreClaims {
    binding: HeaderSourceBinding,
    context: usize,
    lease_identity: *const Eligible08MapPairLease,
    expected: Vec<Fr>,
    cells: Vec<Option<bool>>,
    prepared: bool,
}

impl C498ClippedScoreClaims {
    fn index(&self, local: usize) -> Option<usize> {
        local.checked_sub([677_501, 685_693][self.context]).filter(|&i| i < 2_048)
    }
}

/// Opaque, bounded custody. There is no row/byte export or admission operation.
/// No native Score, foreign physical reads, full row, X, ROW, Eq26, PCS,
/// proof, or client claim follows from this result.
pub(crate) struct C498ClippedScoreRow<'r, 'src, 'm> {
    header_zero: NativeClippedHeaderZeroRow<'m>,
    source: C498ClippedScoreSource<'r, 'src, 'm>,
    cells: Vec<Option<bool>>,
}

impl<'r, 'src, 'm> C498ClippedScoreRow<'r, 'src, 'm> {
    pub(crate) fn validate_for(&self, binding: &HeaderSourceBinding,
        lease: &'m Eligible08MapPairLease) -> Result<(), String> {
        self.source.validate()?;
        self.header_zero.validate_for(binding, lease)?;
        if binding != &self.source.binding || !std::ptr::eq(lease, self.source.lease)
            || self.cells.len() != 2_048 {
            return Err("C498 retained source identity".into());
        }
        for (i, &(wire, _, value)) in self.source.relation.cells().iter().enumerate() {
            let bit = value == Fr::one();
            if self.cells[i] != Some(bit)
                || NativeHeaderSourceLease::bit(&self.header_zero.row.bytes, wire % WIDTH) != bit {
                return Err(format!("C498 final packed Score ordinal {i}"));
            }
        }
        Ok(())
    }
    pub(crate) fn census(&self) -> (usize, usize, usize, usize) {
        (2_048, 8_545, 514, C496_CLIPPED_HEADER_ZERO_CELLS)
    }
}

/// Claims recorded only by the actual native HEADER seeding call path.
/// `None` means no claim occurred; `Some(false)` is an exclusive zero claim.
struct PaddingHeaderZeroCapture {
    owner: usize,
    binding: HeaderSourceBinding,
    cells: Vec<Option<bool>>,
}

/// Source claims captured only while the mixed owner's ordinary producer is
/// writing Map and seeding its HEADER complement.
struct MixedMapHeaderCapture {
    binding: HeaderSourceBinding,
    owner: usize,
    class: crate::daa_history_roster::OwnerClass,
    lease_identity: Option<*const Eligible08MapPairLease>,
    claims: Vec<Option<MixedMapHeaderClaim>>,
}

const C491_HEADER_ZERO_FIRST_OFFSET: usize = 5_757;
const C491_HEADER_ZERO_LAST_OFFSET: usize = 7_804;
const C491_HEADER_ZERO_OFFSETS_PER_CONTEXT: usize =
    C491_HEADER_ZERO_LAST_OFFSET - C491_HEADER_ZERO_FIRST_OFFSET + 1;
const C491_HEADER_ZERO_CELLS: usize =
    BANK53_CONTEXTS * C491_HEADER_ZERO_OFFSETS_PER_CONTEXT;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum C491GenesisHeaderZeroRoute {
    GenesisMapSlackBundle,
    Other,
}

const C496_CLIPPED_HEADER_ZERO_CELLS: usize = 2_822;

fn c496_clipped_header_zero_locals(owner: usize, active_context: usize)
    -> Result<Vec<usize>, String> {
    let ranges = match (owner, active_context) {
        (1_810_904, 0) => [679_549..679_936, 685_693..688_128],
        (1_810_841, 1) => [677_501..679_936, 687_741..688_128],
        _ => return Err("C496 clipped owner/context identity".into()),
    };
    let locals: Vec<_> = ranges.into_iter().flatten().collect();
    let required: Vec<_> = (0..BANK53_CONTEXTS).flat_map(|context|
        (0..BANK53_CONTEXT_BITS).map(move |offset| (context, offset)))
        .map(|(context, offset)| {
            crate::bank53_required_writer::required_bank53_writer(owner, context, offset)
                .map(|writer| (BANK53_BASE + context * BANK53_CONTEXT_BITS + offset, writer))
                .map_err(|error| error.to_string())
        }).collect::<Result<Vec<_>, _>>()?.into_iter()
        .filter_map(|(local, writer)|
            (writer == crate::bank53_required_writer::RequiredWriter::HeaderZero)
                .then_some(local)).collect();
    if locals.len() != C496_CLIPPED_HEADER_ZERO_CELLS || locals != required {
        return Err("C496 exact policy HeaderZero census".into());
    }
    Ok(locals)
}

fn c496_require_binding(binding: &HeaderSourceBinding, active_context: usize)
    -> Result<Vec<usize>, String> {
    let locals = c496_clipped_header_zero_locals(binding.owner(), active_context)?;
    let mut profile_bytes = fixed::PROFILE_PREFIX.to_vec();
    profile_bytes.extend_from_slice(&crate::header_order::MAINNET_GENESIS);
    let profile: [u8; 32] = Blake2b::<U32>::digest(profile_bytes).into();
    if binding.profile != profile
        || binding.cut != crate::bank53_map::CutDescriptor::eligible08().canonical_identity()
        || binding.layout != crate::header_daa_row_placement::Layout::fixed().digest() {
        return Err("C496 fixed H21 profile/cut/layout".into());
    }
    Ok(locals)
}

/// Private census of actual HEADER seed assignments. The pointer is used only
/// for identity comparison; the producer retains the immutable lease borrow.
struct C496ClippedHeaderZeroClaims {
    binding: HeaderSourceBinding,
    active_context: usize,
    lease_identity: *const Eligible08MapPairLease,
    locals: Vec<usize>,
    cells: Vec<Option<bool>>,
    prepared: bool,
}

impl C496ClippedHeaderZeroClaims {
    fn recorded(&self, local: usize) -> bool {
        self.locals.binary_search(&local).is_ok_and(|index| self.cells[index].is_some())
    }
}

pub(crate) struct C496ClippedHeaderZeroCapture<'m> {
    binding: HeaderSourceBinding,
    active_context: usize,
    lease: &'m Eligible08MapPairLease,
    cells: Vec<Option<bool>>,
}

/// Custody for the clipped owner's policy HeaderZero subset only. This does
/// not authenticate clipped Score, a complete owner row, X, ROW, or Eq26.
pub(crate) struct NativeClippedHeaderZeroRow<'m> {
    row: NativePackedRow,
    capture: C496ClippedHeaderZeroCapture<'m>,
}

impl<'m> NativeClippedHeaderZeroRow<'m> {
    pub(crate) fn validate_for(&self, expected: &HeaderSourceBinding,
        lease: &'m Eligible08MapPairLease) -> Result<(), String> {
        use crate::daa_history_roster::OwnerClass;
        let locals = c496_require_binding(expected, self.capture.active_context)?;
        if &self.capture.binding != expected || !std::ptr::eq(self.capture.lease, lease)
            || self.row.header_source_binding.as_ref() != Some(expected)
            || self.row.owner != expected.owner() || self.row.class != OwnerClass::Carry
            || self.row.root != expected.root || self.row.total != expected.total
            || self.row.bytes.len() != OWNER_BYTES
            || self.capture.cells.len() != C496_CLIPPED_HEADER_ZERO_CELLS
            || self.capture.cells.iter().any(|cell| *cell != Some(false)) {
            return Err("C496 HeaderZero row/capture/lease binding".into());
        }
        require_map_pair_packed(&self.row.bytes, lease, expected,
            expected.owner(), OwnerClass::Carry)?;
        for local in locals {
            if NativeHeaderSourceLease::bit(&self.row.bytes, local) {
                return Err("C496 HeaderZero final packed bit is nonzero".into());
            }
        }
        Ok(())
    }
}

/// Claims are recorded only by the actual `OwnedRows::claim_header_seed`
/// route. The packed row is not published with this census until it is complete.
struct C491GenesisHeaderZeroClaims {
    owner: usize,
    binding: HeaderSourceBinding,
    cells: Vec<Option<bool>>,
}

impl C491GenesisHeaderZeroClaims {
    fn index(context: usize, offset: usize) -> Option<usize> {
        if context >= BANK53_CONTEXTS
            || !(C491_HEADER_ZERO_FIRST_OFFSET..=C491_HEADER_ZERO_LAST_OFFSET)
                .contains(&offset)
        {
            return None;
        }
        Some(context * C491_HEADER_ZERO_OFFSETS_PER_CONTEXT
            + offset - C491_HEADER_ZERO_FIRST_OFFSET)
    }

    fn index_for_local(local: usize) -> Option<usize> {
        let index = local.checked_sub(BANK53_BASE)?;
        let context = index / BANK53_CONTEXT_BITS;
        let offset = index % BANK53_CONTEXT_BITS;
        Self::index(context, offset)
    }

    fn recorded(&self, local: usize) -> bool {
        Self::index_for_local(local).is_some_and(|index| self.cells[index].is_some())
    }

    fn record(&mut self, context: usize, offset: usize, value: Fr) -> Result<(), String> {
        let index = Self::index(context, offset)
            .ok_or("C491 HeaderZero claim outside owner0 Genesis census")?;
        if value != Fr::zero() {
            return Err("C491 HeaderZero seed must be zero".into());
        }
        if self.cells[index].is_some() {
            return Err("C491 duplicate HeaderZero seed claim".into());
        }
        self.cells[index] = Some(false);
        Ok(())
    }
}

/// Opaque custody for the exact owner0 Genesis HeaderZero cells. Retaining a
/// borrow of the source bundle binds this value to that exact immutable input.
pub(crate) struct C491GenesisHeaderZeroCapture<'b> {
    binding: HeaderSourceBinding,
    bundle: &'b Eligible08MapSlackBundle,
    cells: Vec<Option<bool>>,
}

pub(crate) struct NativeGenesisHeaderZeroRow<'b> {
    row: NativePackedRow,
    capture: C491GenesisHeaderZeroCapture<'b>,
}

impl<'b> NativeGenesisHeaderZeroRow<'b> {
    pub(crate) fn row(&self) -> &NativePackedRow { &self.row }

    pub(crate) fn validate_for(
        &self,
        expected: &HeaderSourceBinding,
        bundle: &'b Eligible08MapSlackBundle,
    ) -> Result<(), String> {
        if &self.capture.binding != expected
            || !std::ptr::eq(self.capture.bundle, bundle)
            || self.row.header_source_binding.as_ref() != Some(expected)
            || self.row.owner != 0
            || self.row.class != crate::daa_history_roster::OwnerClass::Genesis
            || self.row.root != expected.root
            || self.row.total != expected.total
            || self.row.bytes.len() != OWNER_BYTES
            || self.capture.cells.len() != C491_HEADER_ZERO_CELLS
            || self.capture.cells.iter().any(|claim| *claim != Some(false))
        {
            return Err("C491 HeaderZero row/capture source binding mismatch".into());
        }
        bundle.map_lease().checked_cells(expected, 0,
            crate::daa_history_roster::OwnerClass::Genesis)?;
        bundle.checked_slack_cells(expected, 0,
            crate::daa_history_roster::OwnerClass::Genesis)?;
        for context in 0..BANK53_CONTEXTS {
            for offset in C491_HEADER_ZERO_FIRST_OFFSET..=C491_HEADER_ZERO_LAST_OFFSET {
                let local = BANK53_BASE + context * BANK53_CONTEXT_BITS + offset;
                if NativeHeaderSourceLease::bit(&self.row.bytes, local) {
                    return Err("C491 HeaderZero final packed bit is nonzero".into());
                }
            }
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum MixedMapHeaderAuthor {
    Map,
    HeaderSeed,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct MixedMapHeaderClaim {
    author: MixedMapHeaderAuthor,
    value: bool,
}

impl MixedMapHeaderCapture {
    fn index(local_wire: usize) -> Option<usize> {
        local_wire.checked_sub(BANK53_BASE)
            .filter(|index| *index < BANK53_CONTEXTS * BANK53_CONTEXT_BITS)
    }

    fn record(&mut self, local_wire: usize, author: MixedMapHeaderAuthor,
        value: bool) -> Result<(), String> {
        let index=Self::index(local_wire).ok_or("C450 claim outside Bank53")?;
        if self.claims[index].replace(MixedMapHeaderClaim { author, value }).is_some() {
            return Err(format!("C450 duplicate mixed source claim wire{local_wire}"));
        }
        Ok(())
    }

    fn recorded(&self, local_wire: usize) -> bool {
        Self::index(local_wire).is_some_and(|index|self.claims[index].is_some())
    }
}

impl PaddingHeaderZeroCapture {
    fn index(local_wire: usize) -> Option<usize> {
        local_wire.checked_sub(BANK53_BASE)
            .filter(|index| *index < C449_PADDING_BANK53_CELLS)
    }
    fn recorded(&self, local_wire: usize) -> bool {
        Self::index(local_wire).is_some_and(|index| self.cells[index].is_some())
    }
    fn record(&mut self, local_wire: usize, value: bool) -> Result<(), String> {
        let index=Self::index(local_wire).ok_or("C449 HEADER-zero capture outside Bank53")?;
        if self.cells[index].replace(value).is_some() {
            return Err(format!("C449 duplicate HEADER-zero seed claim wire{local_wire}"));
        }
        Ok(())
    }
}

impl OwnedRows {
    fn new(selection: OwnerSelection) -> Self {
        Self {
            selection,
            values: (0..selection.count())
                .map(|_| vec![Fr::zero(); WIDTH])
                .collect(),
            claimed: (0..selection.count()).map(|_| vec![false; WIDTH]).collect(),
            author_census: None,
            current_author: None,
            regular_author_census: None,
            current_regular_author: None,
            work_endpoint_capture: None,
            padding_header_zero_capture: None,
            mixed_map_header_capture: None,
            c491_genesis_header_zero_capture: None,
            c496_clipped_header_zero_capture: None,
            c498_clipped_score_capture: None,
        }
    }
    fn begin_c498_clipped_score_capture(&mut self, source: &C498ClippedScoreSource<'_, '_, '_>)
        -> Result<(), String> {
        source.validate()?;
        let header = self.c496_clipped_header_zero_capture.as_ref()
            .ok_or("C498 requires C496 capture")?;
        if self.c498_clipped_score_capture.is_some() || header.binding != source.binding
            || header.active_context != source.context || header.prepared
            || !std::ptr::eq(header.lease_identity, source.lease as *const _) {
            return Err("C498 capture parent/context/Map identity".into());
        }
        // Every prior claim, including a zero tail, is checked before mutation.
        for &(wire, _, _) in source.relation.cells() {
            let (row, local) = self.local(source.binding.owner(), wire % WIDTH)?;
            if self.claimed[row][local] || header.locals.binary_search(&local).is_ok() {
                return Err("C498 prior claim or HeaderZero overlap".into());
            }
        }
        self.c498_clipped_score_capture = Some(C498ClippedScoreClaims {
            binding: source.binding.clone(), context: source.context,
            lease_identity: source.lease as *const _,
            expected: source.relation.cells().iter().map(|cell| cell.2).collect(),
            cells: vec![None; 2_048], prepared: false,
        });
        Ok(())
    }

    fn check_c498_clipped_score_seed(&self, owner: usize, mask: &[bool],
        map_reserved: &[bool], native: &[Fr], daa_banks: &[(usize, usize)])
        -> Result<(), String> {
        let capture = self.c498_clipped_score_capture.as_ref().ok_or("C498 capture absent")?;
        let header = self.c496_clipped_header_zero_capture.as_ref().ok_or("C498 C496 absent")?;
        if capture.prepared || capture.binding.owner() != owner
            || capture.binding != header.binding || capture.context != header.active_context
            || capture.lease_identity != header.lease_identity
            || mask.len() != WIDTH || map_reserved.len() != WIDTH || native.len() != WIDTH
            || capture.cells.len() != 2_048 || capture.expected.len() != 2_048 {
            return Err("C498 preseed geometry/identity".into());
        }
        let start = [677_501, 685_693][capture.context];
        for local in start..start + 2_048 {
            let (row, wire) = self.local(owner, local)?;
            let required = crate::bank53_required_writer::required_bank53_writer(
                owner, capture.context, BANK53_MAP_LIVE_BITS + local - start)
                .map_err(str::to_string)?;
            if mask[wire] || map_reserved[wire] || native[wire] != Fr::zero()
                || daa_banks.iter().any(|&(lo, hi)| (lo..hi).contains(&wire))
                || self.claimed[row][wire] || header.locals.binary_search(&wire).is_ok()
                || required != (crate::bank53_required_writer::RequiredWriter::ScoreReplay {
                    context: capture.context,
                    endpoint: crate::bank53_required_writer::ScoreEndpointKind::Clipped }) {
                return Err(format!("C498 preseed target unavailable wire{wire}"));
            }
        }
        Ok(())
    }

    fn prepare_c498_and_c496_seed(&mut self, owner: usize, mask: &[bool],
        map_reserved: &[bool], native: &[Fr], daa_banks: &[(usize, usize)])
        -> Result<(), String> {
        self.check_c498_clipped_score_seed(owner, mask, map_reserved, native, daa_banks)?;
        self.prepare_c496_clipped_header_zero_seed(owner, mask, map_reserved, native, daa_banks)?;
        self.c498_clipped_score_capture.as_mut().ok_or("C498 capture absent")?.prepared = true;
        Ok(())
    }

    fn claim_c498_clipped_score(&mut self, owner: usize, wire: usize, value: Fr)
        -> Result<(), String> {
        let (row, local) = self.local(owner, wire)?;
        let capture = self.c498_clipped_score_capture.as_ref().ok_or("C498 capture absent")?;
        let index = capture.index(local).ok_or("C498 claim outside Score")?;
        if !capture.prepared || owner != capture.binding.owner()
            || capture.cells[index].is_some() || self.claimed[row][local]
            || value != capture.expected[index] || (value != Fr::zero() && value != Fr::one())
            || self.c496_clipped_header_zero_capture.as_ref()
                .is_none_or(|header| header.locals.binary_search(&local).is_ok()) {
            return Err("C498 exclusive source claim identity/value/duplicate".into());
        }
        self.check_author_claim(row, local)?;
        self.values[row][local] = value;
        self.claimed[row][local] = true;
        self.record_author_claim(local);
        self.c498_clipped_score_capture.as_mut().ok_or("C498 capture absent")?
            .cells[index] = Some(value == Fr::one());
        Ok(())
    }

    fn check_c498_clipped_score_capture(&self, row: &NativePackedRow,
        source: &C498ClippedScoreSource<'_, '_, '_>) -> Result<Vec<Option<bool>>, String> {
        source.validate()?;
        let capture = self.c498_clipped_score_capture.as_ref().ok_or("C498 capture absent")?;
        if !capture.prepared || capture.binding != source.binding || capture.context != source.context
            || !std::ptr::eq(capture.lease_identity, source.lease as *const _)
            || row.owner != source.binding.owner() || row.bytes.len() != OWNER_BYTES
            || row.class != crate::daa_history_roster::OwnerClass::Carry
            || row.root != source.binding.root || row.total != source.binding.total
            || row.header_source_binding.as_ref() != Some(&source.binding)
            || capture.cells.len() != 2_048 || capture.expected.len() != 2_048 {
            return Err("C498 final source identity".into());
        }
        for (index, &(wire, _, value)) in source.relation.cells().iter().enumerate() {
            let local = wire % WIDTH;
            if capture.cells[index] != Some(value == Fr::one()) || capture.expected[index] != value
                || !self.claimed[0][local] || self.values[0][local] != value
                || NativeHeaderSourceLease::bit(&row.bytes, local) != (value == Fr::one()) {
                return Err(format!("C498 final source claim ordinal {index}"));
            }
        }
        Ok(capture.cells.clone())
    }
    fn begin_c496_clipped_header_zero_capture(&mut self, binding: HeaderSourceBinding,
        active_context: usize, lease: &Eligible08MapPairLease) -> Result<(), String> {
        use crate::daa_history_roster::OwnerClass;
        let locals = c496_require_binding(&binding, active_context)?;
        if self.selection.count() != 1 || self.selection.first_owner() != binding.owner()
            || self.selection.terminal_class() != OwnerClass::Carry
            || lease.binding() != &binding
            || self.padding_header_zero_capture.is_some()
            || self.mixed_map_header_capture.is_some()
            || self.c491_genesis_header_zero_capture.is_some()
            || self.c496_clipped_header_zero_capture.is_some() {
            return Err("C496 capture requires isolated clipped Carry Map pair".into());
        }
        lease.checked_cells(&binding, binding.owner(), OwnerClass::Carry)?;
        self.c496_clipped_header_zero_capture = Some(C496ClippedHeaderZeroClaims {
            binding, active_context, lease_identity: lease as *const _, locals,
            cells: vec![None; C496_CLIPPED_HEADER_ZERO_CELLS], prepared: false,
        });
        Ok(())
    }

    fn prepare_c496_clipped_header_zero_seed(&mut self, owner: usize,
        mask: &[bool], map_reserved: &[bool], native: &[Fr],
        daa_banks: &[(usize, usize)]) -> Result<(), String> {
        let capture = self.c496_clipped_header_zero_capture.as_ref()
            .ok_or("C496 preseed capture absent")?;
        if capture.prepared || capture.binding.owner() != owner
            || mask.len() != WIDTH || map_reserved.len() != WIDTH || native.len() != WIDTH
            || capture.locals != c496_require_binding(&capture.binding, capture.active_context)? {
            return Err("C496 preseed identity/geometry".into());
        }
        for &local in &capture.locals {
            let (row, wire) = self.local(owner, local)?;
            if mask[wire] || map_reserved[wire]
                || daa_banks.iter().any(|&(lo, hi)| (lo..hi).contains(&wire))
                || native[wire] != Fr::zero() || self.claimed[row][wire] {
                return Err(format!("C496 preseed target unavailable wire{wire}"));
            }
        }
        self.c496_clipped_header_zero_capture.as_mut()
            .ok_or("C496 preseed capture disappeared")?.prepared = true;
        Ok(())
    }

    fn finish_c496_clipped_header_zero_capture<'m>(&mut self, row: &NativePackedRow,
        lease: &'m Eligible08MapPairLease) -> Result<C496ClippedHeaderZeroCapture<'m>, String> {
        use crate::daa_history_roster::OwnerClass;
        let capture = self.c496_clipped_header_zero_capture.as_ref()
            .ok_or("C496 HeaderZero final capture absent")?;
        if !capture.prepared || !std::ptr::eq(capture.lease_identity, lease as *const _)
            || row.owner != capture.binding.owner() || row.class != OwnerClass::Carry
            || row.root != capture.binding.root || row.total != capture.binding.total
            || row.header_source_binding.as_ref() != Some(&capture.binding)
            || row.bytes.len() != OWNER_BYTES || lease.binding() != &capture.binding
            || capture.locals != c496_require_binding(&capture.binding, capture.active_context)?
            || capture.cells.len() != C496_CLIPPED_HEADER_ZERO_CELLS {
            return Err("C496 HeaderZero final row/lease identity".into());
        }
        require_map_pair_packed(&row.bytes, lease, &capture.binding,
            row.owner, OwnerClass::Carry)?;
        for (index, &local) in capture.locals.iter().enumerate() {
            if capture.cells[index] != Some(false) || !self.claimed[0][local]
                || self.values[0][local] != Fr::zero()
                || NativeHeaderSourceLease::bit(&row.bytes, local) {
                return Err(format!("C496 HeaderZero seed/final claim mismatch wire{local}"));
            }
        }
        let result = C496ClippedHeaderZeroCapture {
            binding: capture.binding.clone(), active_context: capture.active_context,
            lease, cells: capture.cells.clone(),
        };
        self.c496_clipped_header_zero_capture.take();
        Ok(result)
    }
    fn begin_c491_genesis_header_zero_capture(
        &mut self,
        route: C491GenesisHeaderZeroRoute,
        binding: HeaderSourceBinding,
    ) -> Result<(), String> {
        use crate::daa_history_roster::OwnerClass;
        if route != C491GenesisHeaderZeroRoute::GenesisMapSlackBundle
            || self.selection.count() != 1
            || self.selection.first_owner() != 0
            || self.selection.terminal_class() != OwnerClass::Genesis
            || binding.owner() != 0
            || binding.cut != crate::bank53_map::CutDescriptor::eligible08()
                .canonical_identity()
            || self.padding_header_zero_capture.is_some()
            || self.mixed_map_header_capture.is_some()
            || self.c491_genesis_header_zero_capture.is_some()
        {
            return Err("C491 HeaderZero capture requires fresh owner0 Genesis Map+Slack route".into());
        }
        self.c491_genesis_header_zero_capture = Some(C491GenesisHeaderZeroClaims {
            owner: 0,
            binding,
            cells: vec![None; C491_HEADER_ZERO_CELLS],
        });
        Ok(())
    }
    fn begin_padding_header_zero_capture(
        &mut self, binding: HeaderSourceBinding,
    ) -> Result<(), String> {
        let owner=binding.owner();
        if self.selection.count()!=1
            || self.selection.first_owner()!=owner
            || self.selection.terminal_class()!=crate::daa_history_roster::OwnerClass::Padding
            || owner<C449_PADDING_OWNER || owner>=MAX_NATIVE_HEADERS
            || binding.owner()!=owner
            || self.padding_header_zero_capture.is_some() {
            return Err("C449 HEADER-zero capture requires fresh padding owner binding".into());
        }
        self.padding_header_zero_capture=Some(PaddingHeaderZeroCapture {
            owner, binding, cells:vec![None;C449_PADDING_BANK53_CELLS],
        });
        Ok(())
    }
    fn begin_mixed_map_header_capture(
        &mut self, binding: HeaderSourceBinding,
    ) -> Result<(), String> {
        let owner=binding.owner();
        let class=self.selection.terminal_class();
        if self.selection.count()!=1 || self.selection.first_owner()!=owner
            || !mixed_map_header_class_allowed(owner, class)
            || self.padding_header_zero_capture.is_some()
            || self.mixed_map_header_capture.is_some() {
            return Err("C450 mixed capture requires fresh owner845760/Carry binding".into());
        }
        require_mixed_map_header_no_scheduled(owner, class)?;
        self.mixed_map_header_capture=Some(MixedMapHeaderCapture {
            binding, owner, class, lease_identity: None,
            claims:vec![None;BANK53_CONTEXTS*BANK53_CONTEXT_BITS],
        });
        Ok(())
    }
    fn claim_header_seed(&mut self, owner:usize, wire:usize, value:Fr)
        ->Result<(),String> {
        let (_,local)=self.local(owner,wire)?;
        if self.c498_clipped_score_capture.as_ref().is_some_and(|capture| capture.index(local).is_some()) {
            return Err("C498 HEADER claim overlaps reserved Score".into());
        }
        let c496_index = self.c496_clipped_header_zero_capture.as_ref()
            .and_then(|capture| capture.locals.binary_search(&local).ok());
        if let Some(index) = c496_index {
            let capture = self.c496_clipped_header_zero_capture.as_ref()
                .ok_or("C496 HeaderZero capture disappeared")?;
            let relative = local.checked_sub(BANK53_BASE)
                .ok_or("C496 HeaderZero local coordinate")?;
            if !capture.prepared || owner != capture.binding.owner()
                || capture.cells[index].is_some() || value != Fr::zero()
                || crate::bank53_required_writer::required_bank53_writer(owner,
                    relative / BANK53_CONTEXT_BITS, relative % BANK53_CONTEXT_BITS)
                    .map_err(|error| error.to_string())?
                    != crate::bank53_required_writer::RequiredWriter::HeaderZero {
                return Err("C496 HeaderZero seed author/value/identity".into());
            }
            self.claim_exclusive(owner, wire, value)?;
            self.c496_clipped_header_zero_capture.as_mut()
                .ok_or("C496 HeaderZero capture disappeared")?.cells[index] = Some(false);
            return Ok(());
        }
        let c491_index = self.c491_genesis_header_zero_capture.as_ref()
            .and_then(|_| C491GenesisHeaderZeroClaims::index_for_local(local));
        if let Some(index) = c491_index {
            let capture = self.c491_genesis_header_zero_capture.as_ref()
                .ok_or("C491 HeaderZero capture disappeared")?;
            if owner != capture.owner || owner != 0 {
                return Err("C491 HeaderZero seed owner mismatch".into());
            }
            let context = index / C491_HEADER_ZERO_OFFSETS_PER_CONTEXT;
            let offset = C491_HEADER_ZERO_FIRST_OFFSET
                + index % C491_HEADER_ZERO_OFFSETS_PER_CONTEXT;
            if crate::bank53_required_writer::required_bank53_writer(owner, context, offset)
                .map_err(|error| error.to_string())?
                != crate::bank53_required_writer::RequiredWriter::HeaderZero
            {
                return Err("C491 capture reached a non-HeaderZero required writer".into());
            }
            if value != Fr::zero() {
                return Err("C491 HeaderZero seed must be zero".into());
            }
            if capture.cells[index].is_some() {
                return Err("C491 duplicate HeaderZero seed claim".into());
            }
            self.claim_exclusive(owner, wire, value)?;
            self.c491_genesis_header_zero_capture.as_mut()
                .ok_or("C491 HeaderZero capture disappeared")?
                .record(context, offset, value)?;
            return Ok(());
        }
        if let Some(capture)=self.mixed_map_header_capture.as_ref() {
            if owner!=capture.owner { return Err("C450 HEADER source owner mismatch".into()); }
            if let Some(index)=MixedMapHeaderCapture::index(local) {
                let context=index/BANK53_CONTEXT_BITS;
                let offset=index%BANK53_CONTEXT_BITS;
                let required=crate::bank53_required_writer::required_bank53_writer(
                    owner,context,offset).map_err(|error|error.to_string())?;
                if required!=crate::bank53_required_writer::RequiredWriter::HeaderZero {
                    return Err(format!("C450 HEADER claim on non-HEADER cell wire{local}"));
                }
                if value!=Fr::zero() {
                    return Err(format!("C450 nonzero HEADER-zero seed claim wire{local}"));
                }
                self.claim_exclusive(owner,wire,value)?;
                self.mixed_map_header_capture.as_mut()
                    .ok_or("C450 mixed capture disappeared")?
                    .record(local,MixedMapHeaderAuthor::HeaderSeed,false)?;
                return Ok(());
            }
        }
        let capture_index=self.padding_header_zero_capture.as_ref()
            .and_then(|capture|PaddingHeaderZeroCapture::index(local));
        if let Some(index)=capture_index {
            let capture_owner=self.padding_header_zero_capture.as_ref()
                .ok_or("C460 HEADER-zero capture disappeared")?.owner;
            if owner!=capture_owner {
                return Err("C460 HEADER-zero claim owner mismatch".into());
            }
            let context=index/BANK53_CONTEXT_BITS;
            let offset=index%BANK53_CONTEXT_BITS;
            if crate::bank53_required_writer::required_bank53_writer(owner,context,offset)
                .map_err(|error|error.to_string())?
                != crate::bank53_required_writer::RequiredWriter::HeaderZero {
                return Err(format!("C460 HEADER-zero claim on non-HEADER cell wire{local}"));
            }
            if value!=Fr::zero() {
                return Err(format!("C449 nonzero HEADER-zero seed claim wire{local}"));
            }
            if self.padding_header_zero_capture.as_ref()
                .is_some_and(|capture|capture.cells[index].is_some()) {
                return Err(format!("C449 duplicate HEADER-zero seed claim wire{local}"));
            }
            self.claim_exclusive(owner,wire,value)?;
            self.padding_header_zero_capture.as_mut()
                .ok_or("C449 HEADER-zero capture disappeared")?
                .record(local,false)?;
            Ok(())
        } else {
            self.claim(owner,wire,value)
        }
    }
    fn finish_padding_header_zero_capture(
        &mut self,row:&NativePackedRow,
    )->Result<PaddingHeaderZeroCapture,String> {
        let capture=self.padding_header_zero_capture.take()
            .ok_or("C449 HEADER-zero capture absent at final row")?;
        if capture.owner<C449_PADDING_OWNER || capture.owner>=MAX_NATIVE_HEADERS
            || capture.binding.owner()!=capture.owner
            || row.owner!=capture.owner
            || row.class!=crate::daa_history_roster::OwnerClass::Padding
            || row.root!=capture.binding.root || row.total!=capture.binding.total
            || row.header_source_binding.as_ref()!=Some(&capture.binding)
            || row.bytes.len()!=OWNER_BYTES {
            return Err("C449 HEADER-zero final row binding/geometry".into());
        }
        for (index,claim) in capture.cells.iter().enumerate() {
            let local=BANK53_BASE+index;
            if *claim!=Some(false) || !self.claimed[0][local]
                || !self.values[0][local].is_zero()
                || NativeHeaderSourceLease::bit(&row.bytes,local) {
                return Err(format!("C449 HEADER-zero seed/final claim mismatch wire{local}"));
            }
        }
        Ok(capture)
    }
    fn finish_c491_genesis_header_zero_capture<'b>(
        &mut self,
        row: &NativePackedRow,
        bundle: &'b Eligible08MapSlackBundle,
    ) -> Result<C491GenesisHeaderZeroCapture<'b>, String> {
        use crate::daa_history_roster::OwnerClass;
        let capture = self.c491_genesis_header_zero_capture.take()
            .ok_or("C491 HeaderZero capture absent at final row")?;
        if capture.owner != 0 || capture.binding.owner() != 0
            || row.owner != 0 || row.class != OwnerClass::Genesis
            || row.root != capture.binding.root || row.total != capture.binding.total
            || row.header_source_binding.as_ref() != Some(&capture.binding)
            || row.bytes.len() != OWNER_BYTES
            || capture.cells.len() != C491_HEADER_ZERO_CELLS
            || bundle.map_lease().binding() != &capture.binding
        {
            return Err("C491 HeaderZero final row/bundle/binding geometry".into());
        }
        bundle.map_lease().checked_cells(&capture.binding, 0, OwnerClass::Genesis)?;
        bundle.checked_slack_cells(&capture.binding, 0, OwnerClass::Genesis)?;
        for context in 0..BANK53_CONTEXTS {
            for relative in 0..C491_HEADER_ZERO_OFFSETS_PER_CONTEXT {
                let index = context * C491_HEADER_ZERO_OFFSETS_PER_CONTEXT + relative;
                let offset = C491_HEADER_ZERO_FIRST_OFFSET + relative;
                let local = BANK53_BASE + context * BANK53_CONTEXT_BITS + offset;
                if capture.cells[index] != Some(false)
                    || !self.claimed[0][local]
                    || !self.values[0][local].is_zero()
                    || NativeHeaderSourceLease::bit(&row.bytes, local)
                {
                    return Err(format!("C491 HeaderZero seed/final claim mismatch wire{local}"));
                }
            }
        }
        Ok(C491GenesisHeaderZeroCapture {
            binding: capture.binding,
            bundle,
            cells: capture.cells,
        })
    }
    fn record_mixed_map_claim(
        &mut self, owner:usize, local_wire:usize, value:bool,
    )->Result<(),String> {
        let Some(capture)=self.mixed_map_header_capture.as_ref() else { return Ok(()); };
        if owner!=capture.owner { return Err("C450 Map source owner mismatch".into()); }
        let index=MixedMapHeaderCapture::index(local_wire)
            .ok_or("C450 Map claim outside Bank53")?;
        let context=index/BANK53_CONTEXT_BITS;
        let offset=index%BANK53_CONTEXT_BITS;
        if crate::bank53_required_writer::required_bank53_writer(owner,context,offset)
            .map_err(|error|error.to_string())?
            != (crate::bank53_required_writer::RequiredWriter::Map { context }) {
            return Err(format!("C450 Map claim on non-Map cell wire{local_wire}"));
        }
        self.mixed_map_header_capture.as_mut()
            .ok_or("C450 mixed capture disappeared")?
            .record(local_wire,MixedMapHeaderAuthor::Map,value)
    }
    fn finish_mixed_map_header_capture(
        &mut self, row:&NativePackedRow,
    )->Result<MixedMapHeaderCapture,String> {
        let capture=self.mixed_map_header_capture.take()
            .ok_or("C450 mixed capture absent at final row")?;
        require_mixed_map_header_no_scheduled(capture.owner, capture.class)?;
        if !mixed_map_header_class_allowed(capture.owner, capture.class)
            || capture.binding.owner()!=capture.owner || row.owner!=capture.owner
            || row.class!=capture.class || row.root!=capture.binding.root
            || row.total!=capture.binding.total
            || row.header_source_binding.as_ref()!=Some(&capture.binding)
            || row.bytes.len()!=OWNER_BYTES
            || capture.claims.len()!=BANK53_CONTEXTS*BANK53_CONTEXT_BITS {
            return Err("C450 mixed final row/binding/class geometry".into());
        }
        let mut map_count=0usize;
        let mut zero_count=0usize;
        for context in 0..BANK53_CONTEXTS {
            for offset in 0..BANK53_CONTEXT_BITS {
                let index=context*BANK53_CONTEXT_BITS+offset;
                let local=BANK53_BASE+index;
                let actual=capture.claims[index]
                    .ok_or_else(||format!("C450 missing source claim wire{local}"))?;
                let packed=NativeHeaderSourceLease::bit(&row.bytes,local);
                let required=crate::bank53_required_writer::required_bank53_writer(
                    capture.owner,context,offset).map_err(|error|error.to_string())?;
                match required {
                    crate::bank53_required_writer::RequiredWriter::Map { context: expected }
                        if expected==context => {
                            if actual.author!=MixedMapHeaderAuthor::Map || actual.value!=packed {
                                return Err(format!("C450 Map source/packed author mismatch wire{local}"));
                            }
                            map_count+=1;
                        }
                    crate::bank53_required_writer::RequiredWriter::HeaderZero => {
                        if actual.author!=MixedMapHeaderAuthor::HeaderSeed
                            || actual.value || packed {
                            return Err(format!("C450 HEADER-zero source/packed mismatch wire{local}"));
                        }
                        zero_count+=1;
                    }
                    _ => return Err(format!("C450 unexpected required writer wire{local}")),
                }
            }
        }
        if map_count!=2*BANK53_MAP_LIVE_BITS || zero_count!=2*(BANK53_CONTEXT_BITS-BANK53_MAP_LIVE_BITS) {
            return Err(format!("C450 mixed author census Map={map_count} HeaderZero={zero_count}"));
        }
        Ok(capture)
    }
    fn begin_author_census(&mut self) -> Result<(), String> {
        if self.selection.count() != 1 || self.author_census.is_some()
            || self.regular_author_census.is_some() || self.work_endpoint_capture.is_some() {
            return Err("C374 author census requires one fresh owner row".into());
        }
        self.author_census = Some(vec![None; WIDTH]);
        Ok(())
    }
    fn begin_work_endpoint_capture(&mut self, owner: usize) -> Result<(), String> {
        use crate::daa_history_roster::OwnerClass;
        if !matches!(self.selection, OwnerSelection::Single {
                owner: selected, class: OwnerClass::Carry,
            } if selected == owner)
            || self.author_census.is_some() || self.work_endpoint_capture.is_some()
            || self.regular_author_census.is_some()
            || self.padding_header_zero_capture.is_some()
            || self.mixed_map_header_capture.is_some()
            || self.c491_genesis_header_zero_capture.is_some()
            || self.c496_clipped_header_zero_capture.is_some()
            || self.c498_clipped_score_capture.is_some()
            || self.claimed.len() != 1 || self.claimed[0].iter().any(|claimed| *claimed) {
            return Err("C512i Work endpoint capture requires fresh isolated Carry row".into());
        }
        self.work_endpoint_capture = Some(WorkEndpointCapture::new(owner)?);
        Ok(())
    }
    fn begin_work_endpoint_tree_phase(&mut self) -> Result<(), String> {
        let capture = self.work_endpoint_capture.as_mut()
            .ok_or("C512i Work endpoint capture absent before Tree")?;
        if capture.phase != WorkEndpointPhase::BeforeTree || !capture.events.is_empty() {
            return Err("C512i Work endpoint Tree phase order".into());
        }
        capture.phase = WorkEndpointPhase::Tree;
        Ok(())
    }
    fn finish_work_endpoint_tree_phase(&mut self) -> Result<(), String> {
        self.work_endpoint_capture.as_mut()
            .ok_or("C512i Work endpoint capture absent after Tree")?.finish_tree()
    }
    fn check_work_endpoint_claim(&self, row: usize, owner: usize, local: usize)
        -> Result<(), String> {
        if let Some(capture) = self.work_endpoint_capture.as_ref() {
            if row != 0 { return Err("C512i Work endpoint capture row".into()); }
            capture.check_claim(owner, local, self.claimed[row][local])?;
        }
        Ok(())
    }
    fn record_work_endpoint_claim(&mut self, local: usize, value: Fr) {
        if let Some(capture) = self.work_endpoint_capture.as_mut() {
            capture.record_claim(local, value);
        }
    }
    fn set_author(&mut self, author: NativePhysicalAuthor) -> Result<(), String> {
        if self.author_census.is_none() {
            return Err("C374 author phase without census".into());
        }
        self.current_author = Some(author);
        Ok(())
    }
    fn begin_regular_author_census(&mut self) -> Result<(), String> {
        if self.work_endpoint_capture.is_some() {
            return Err("C512j regular census cannot mix after Work capture".into());
        }
        use crate::daa_history_roster::OwnerClass;
        if !matches!(self.selection, OwnerSelection::Single {
                owner: 845_887 | 846_015, class: OwnerClass::Carry,
            }) || self.author_census.is_some() || self.regular_author_census.is_some()
            || self.claimed.len() != 1 || self.claimed[0].iter().any(|claimed| *claimed)
        {
            return Err("C574 regular author capture requires fresh fixed Carry row".into());
        }
        self.regular_author_census = Some(vec![None; WIDTH]);
        Ok(())
    }
    fn set_regular_author(&mut self, author: NativeRegularPhysicalAuthor) -> Result<(), String> {
        use NativeRegularPhysicalAuthor::{Header, Tree, Daa, Scored};
        if self.regular_author_census.is_none() || self.author_census.is_some()
            || !matches!((self.current_regular_author, author),
                (None, Header) | (Some(Header), Tree) | (Some(Tree), Daa)
                    | (Some(Daa), Scored))
        {
            return Err("C512e regular author phase order".into());
        }
        self.current_regular_author = Some(author);
        Ok(())
    }
    fn check_regular_author_claim(&self, row: usize, wire: usize) -> Result<(), String> {
        if let Some(census) = self.regular_author_census.as_ref() {
            if row != 0 || self.current_regular_author.is_none()
                || census[wire].is_some() || self.claimed[row][wire]
            {
                return Err(format!("C512e duplicate or unauthored regular claim wire{wire}"));
            }
        }
        Ok(())
    }
    fn record_regular_author_claim(&mut self, wire: usize) {
        if let Some(census) = self.regular_author_census.as_mut() {
            census[wire] = self.current_regular_author;
        }
    }
    fn check_author_claim(&self, row: usize, wire: usize) -> Result<(), String> {
        if let Some(census) = self.author_census.as_ref() {
            if row != 0 { return Err("C374 author census row mismatch".into()); }
            let author = self.current_author.ok_or("C374 claim has no physical author")?;
            if let Some(previous) = census[wire] {
                if previous != author {
                    return Err(format!("C374 cross-author duplicate wire{wire}: {previous:?}/{author:?}"));
                }
            }
        }
        Ok(())
    }
    fn record_author_claim(&mut self, wire: usize) {
        if let Some(census) = self.author_census.as_mut() {
            census[wire] = self.current_author;
        }
    }
    fn local(&self, owner: usize, wire: usize) -> Result<(usize, usize), String> {
        if !self.selection.owners().contains(&owner) || wire >= WIDTH {
            return Err("claim outside selected owners".into());
        }
        Ok((owner - self.selection.first_owner(), wire))
    }
    fn claim(&mut self, owner: usize, wire: usize, value: Fr) -> Result<(), String> {
        let (row, wire) = self.local(owner, wire)?;
        if self.c498_clipped_score_capture.as_ref().is_some_and(|capture| capture.index(wire).is_some()) {
            return Err("C498 ordinary claim overlaps reserved Score".into());
        }
        if self.c496_clipped_header_zero_capture.as_ref()
            .is_some_and(|capture| capture.recorded(wire)) {
            return Err(format!("C496 later claim overlaps HeaderZero source wire{wire}"));
        }
        if self.mixed_map_header_capture.as_ref()
            .is_some_and(|capture|capture.recorded(wire)) {
            return Err(format!("C450 later claim overlaps mixed source wire{wire}"));
        }
        if self.padding_header_zero_capture.as_ref()
            .is_some_and(|capture|capture.recorded(wire)) {
            return Err(format!("C449 later claim overlaps HEADER-zero wire{wire}"));
        }
        if self.c491_genesis_header_zero_capture.as_ref()
            .is_some_and(|capture| capture.recorded(wire)) {
            return Err(format!("C491 later claim overlaps HeaderZero source wire{wire}"));
        }
        if value != Fr::zero() && value != Fr::one() {
            return Err("non-Boolean claim".into());
        }
        self.check_author_claim(row, wire)?;
        self.check_regular_author_claim(row, wire)?;
        self.check_work_endpoint_claim(row, owner, wire)?;
        if self.current_author == Some(NativePhysicalAuthor::Tree)
            && self.author_census.is_some() && self.claimed[row][wire]
        {
            return Err(format!("C376 Tree duplicate claim owner{owner} wire{wire}"));
        }
        if self.claimed[row][wire] && self.values[row][wire] != value {
            return Err(format!("claim conflict owner{owner} wire{wire}"));
        }
        self.values[row][wire] = value;
        self.claimed[row][wire] = true;
        self.record_author_claim(wire);
        self.record_regular_author_claim(wire);
        self.record_work_endpoint_claim(wire, value);
        Ok(())
    }
    fn claim_exclusive(&mut self, owner: usize, wire: usize, value: Fr) -> Result<(), String> {
        let (row, wire) = self.local(owner, wire)?;
        if self.c498_clipped_score_capture.as_ref().is_some_and(|capture| capture.index(wire).is_some()) {
            return Err("C498 exclusive claim overlaps reserved Score".into());
        }
        if self.c496_clipped_header_zero_capture.as_ref()
            .is_some_and(|capture| capture.recorded(wire)) {
            return Err(format!("C496 later exclusive claim overlaps HeaderZero source wire{wire}"));
        }
        if self.mixed_map_header_capture.as_ref()
            .is_some_and(|capture|capture.recorded(wire)) {
            return Err(format!("C450 exclusive claim overlaps mixed source wire{wire}"));
        }
        if self.padding_header_zero_capture.as_ref()
            .is_some_and(|capture|capture.recorded(wire)) {
            return Err(format!("C449 exclusive claim overlaps HEADER-zero wire{wire}"));
        }
        if value != Fr::zero() && value != Fr::one() {
            return Err("non-Boolean exclusive claim".into());
        }
        self.check_author_claim(row, wire)?;
        self.check_regular_author_claim(row, wire)?;
        self.check_work_endpoint_claim(row, owner, wire)?;
        if self.claimed[row][wire] {
            return Err(format!("exclusive claim overlaps owner{owner} wire{wire}"));
        }
        self.values[row][wire] = value;
        self.claimed[row][wire] = true;
        self.record_author_claim(wire);
        self.record_regular_author_claim(wire);
        self.record_work_endpoint_claim(wire, value);
        Ok(())
    }
    fn native(
        &mut self,
        owner: usize,
        map: &BTreeMap<usize, Fr>,
        domain: &[usize],
    ) -> Result<(), String> {
        let allowed: BTreeSet<_> = domain.iter().copied().collect();
        if map.keys().any(|w| !allowed.contains(w)) {
            return Err("native assignment outside declared domain".into());
        }
        for &wire in domain {
            self.claim(
                owner,
                wire,
                map.get(&wire).copied().unwrap_or_else(Fr::zero),
            )?;
        }
        Ok(())
    }
    fn integer(&mut self, owner: usize, wires: &[usize], value: &BigUint) -> Result<(), String> {
        if value.bits() > wires.len() as u64 {
            return Err("native integer exceeds endpoint".into());
        }
        for (bit, &wire) in wires.iter().enumerate() {
            self.claim(owner, wire, Fr::from(value.bit(bit as u64) as u64))?;
        }
        Ok(())
    }
    fn check_integer_claimed(
        &self, owner: usize, wires: &[usize], value: &BigUint,
    ) -> Result<(), String> {
        if value.bits() > wires.len() as u64 {
            return Err("C376 Tree repeated integer exceeds endpoint".into());
        }
        for (bit, &wire) in wires.iter().enumerate() {
            let (row, local) = self.local(owner, wire)?;
            if !self.claimed[row][local]
                || self.values[row][local] != Fr::from(value.bit(bit as u64) as u64)
            {
                return Err(format!("C376 Tree repeated endpoint differs owner{owner} wire{wire}"));
            }
        }
        Ok(())
    }
    /// The ordinary first post-EIP Carry writer has exactly three physical
    /// authors. A zero in the packed row is not evidence that anyone claimed
    /// it: check the claim and its author at every physical bit.
    fn require_carry_full_author_partition(
        &self, owner: usize, tree_mask: &[bool],
    ) -> Result<[usize; 3], String> {
        use crate::daa_history_roster::OwnerClass;
        if owner != MATURE_EIP_SOURCE_OWNER + 1
            || !matches!(self.selection, OwnerSelection::Single {
                owner: selected, class: OwnerClass::Carry,
            } if selected == owner)
            || self.values.len() != 1 || self.claimed.len() != 1
            || self.values[0].len() != WIDTH || self.claimed[0].len() != WIDTH
            || tree_mask.len() != WIDTH
        {
            return Err("C388 Carry full-author owner/width/selection".into());
        }
        let authors = self.author_census.as_ref()
            .filter(|authors| authors.len() == WIDTH)
            .ok_or("C388 Carry missing full-author census")?;
        let mut counts = [0usize; 3]; // HEADER, Tree, DAA.
        for wire in 0..WIDTH {
            let daa = BANKS.iter().any(|&(lo, hi)| (lo..hi).contains(&wire));
            if daa && tree_mask[wire] {
                return Err(format!("C388 Carry Tree/DAA mask overlap wire{wire}"));
            }
            let (expected, index) = if daa {
                (NativePhysicalAuthor::Daa, 2)
            } else if tree_mask[wire] {
                (NativePhysicalAuthor::Tree, 1)
            } else {
                (NativePhysicalAuthor::Header, 0)
            };
            if !self.claimed[0][wire] {
                return Err(format!("C388 Carry unclaimed physical bit wire{wire}"));
            }
            if authors[wire] != Some(expected) {
                return Err(format!("C388 Carry wrong physical author wire{wire}"));
            }
            let value = self.values[0][wire];
            if value != Fr::zero() && value != Fr::one() {
                return Err(format!("C388 Carry non-Boolean physical bit wire{wire}"));
            }
            counts[index] += 1;
        }
        if counts != [MATURE_EIP_HEADER_CELLS, MATURE_EIP_TREE_CELLS, MATURE_EIP_DAA_CELLS]
            || (989_658..989_730).any(|wire| authors[wire] != Some(NativePhysicalAuthor::Header))
        {
            return Err(format!("C388 Carry exact three-author counts/endpoints {counts:?}"));
        }
        Ok(counts)
    }
    /// Compare the complete replayed row with source images obtained from the
    /// prefix and plan, then with the actual packed bytes. This is private so
    /// callers cannot turn a synthetic image into a producer lease.
    fn require_carry_full_source_values(
        &self,
        owner: usize,
        tree_mask: &[bool],
        canonical_header: &[Fr],
        tree_owned: &[u8],
        tree_values: &[u8],
        point_witness: &[bool],
        packed: &[u8],
    ) -> Result<[usize; 3], String> {
        let counts = self.require_carry_full_author_partition(owner, tree_mask)?;
        if canonical_header.len() != WIDTH || tree_owned.len() != OWNER_BYTES
            || tree_values.len() != OWNER_BYTES || packed.len() != OWNER_BYTES
            || point_witness.len() != crate::point_membership::POINT_WIDTH
        {
            return Err("C388 Carry full canonical source/packed widths".into());
        }
        let authors = self.author_census.as_ref()
            .ok_or("C388 Carry author census disappeared after partition")?;
        let point_start = crate::segment_points::POINT_OFFSET;
        let point_end = point_start + crate::point_membership::POINT_WIDTH;
        for wire in 0..WIDTH {
            let source_tree_owned = NativeHeaderSourceLease::bit(tree_owned, wire);
            let source_tree_value = NativeHeaderSourceLease::bit(tree_values, wire);
            if source_tree_owned != tree_mask[wire]
                || (!source_tree_owned && source_tree_value)
            {
                return Err(format!("C388 Carry independent Tree mask/value wire{wire}"));
            }
            if (989_730..991_232).contains(&wire) && source_tree_value {
                return Err(format!("C388 Carry Tree zero pad wire{wire}"));
            }
            let expected = match authors[wire] {
                Some(NativePhysicalAuthor::Header) => {
                    let value = canonical_header[wire];
                    if value != Fr::zero() && value != Fr::one() {
                        return Err(format!("C388 Carry non-Boolean HEADER template wire{wire}"));
                    }
                    if (point_start..point_end).contains(&wire)
                        && value != Fr::from(point_witness[wire - point_start] as u64)
                    {
                        return Err(format!("C388 Carry full Point witness wire{wire}"));
                    }
                    if ((BANK53_BASE..BANK53_BASE + BANK53_CONTEXTS * BANK53_CONTEXT_BITS)
                        .contains(&wire) || MATURE_EIP_MAX_CAP.contains(&wire))
                        && value != Fr::zero()
                    {
                        return Err(format!("C388 Carry reserved HEADER zero wire{wire}"));
                    }
                    value
                }
                Some(NativePhysicalAuthor::Tree) => Fr::from(source_tree_value as u64),
                Some(NativePhysicalAuthor::Daa) => Fr::zero(),
                _ => return Err(format!("C388 Carry unexpected full-row author wire{wire}")),
            };
            let actual = self.values[0][wire];
            let packed = Fr::from(((packed[wire / 8] >> (wire % 8)) & 1) as u64);
            if actual != expected || packed != expected {
                return Err(format!("C388 Carry full source/packed bit wire{wire}"));
            }
        }
        Ok(counts)
    }
    fn bytes(&self, row: usize) -> Result<Vec<u8>, String> {
        let mut bytes = vec![0u8; OWNER_BYTES];
        for (wire, &value) in self.values[row].iter().enumerate() {
            if value != Fr::zero() && value != Fr::one() {
                return Err("Boolean packed row".into());
            }
            if value == Fr::one() {
                bytes[wire / 8] |= 1 << (wire % 8);
            }
        }
        Ok(bytes)
    }
}

#[cfg(test)]
mod c388_carry_full_author_partition_tests {
    use super::*;

    // A checker-sensitivity fixture only. It is not minted by the native
    // producer and does not establish a valid H21 history or packed source.
    fn zero_fixture() -> (OwnedRows, Vec<bool>) {
        let owner = MATURE_EIP_SOURCE_OWNER + 1;
        let mut tree_mask = vec![false; WIDTH];
        let tree_pad = 989_730;
        let header_anchor = 999_424;
        tree_mask[tree_pad] = true;
        let mut remaining = MATURE_EIP_TREE_CELLS - 1;
        for wire in 0..WIDTH {
            if remaining == 0 { break; }
            if wire == tree_pad || wire == header_anchor
                || BANKS.iter().any(|&(lo, hi)| (lo..hi).contains(&wire))
            {
                continue;
            }
            tree_mask[wire] = true;
            remaining -= 1;
        }
        assert_eq!(remaining, 0);
        let mut rows = OwnedRows::new(OwnerSelection::Single {
            owner, class: crate::daa_history_roster::OwnerClass::Carry,
        });
        rows.begin_author_census().unwrap();
        rows.claimed[0].fill(true);
        let authors = rows.author_census.as_mut().unwrap();
        for wire in 0..WIDTH {
            authors[wire] = Some(if BANKS.iter().any(|&(lo, hi)| (lo..hi).contains(&wire)) {
                NativePhysicalAuthor::Daa
            } else if tree_mask[wire] {
                NativePhysicalAuthor::Tree
            } else {
                NativePhysicalAuthor::Header
            });
        }
        (rows, tree_mask)
    }

    #[test]
    fn c388_no_frame_carry_zero_claim_and_author_mutants() {
        let owner = MATURE_EIP_SOURCE_OWNER + 1;
        let (mut rows, mask) = zero_fixture();
        let counts = [MATURE_EIP_HEADER_CELLS, MATURE_EIP_TREE_CELLS, MATURE_EIP_DAA_CELLS];
        assert_eq!(rows.require_carry_full_author_partition(owner, &mask), Ok(counts));
        let cases = [
            (999_424, NativePhysicalAuthor::Header, NativePhysicalAuthor::Tree),
            (989_730, NativePhysicalAuthor::Tree, NativePhysicalAuthor::Header),
            (BANKS[0].0, NativePhysicalAuthor::Daa, NativePhysicalAuthor::Header),
        ];
        for (wire, right, wrong) in cases {
            assert_eq!(rows.values[0][wire], Fr::zero());
            assert_eq!(rows.author_census.as_ref().unwrap()[wire], Some(right));
            rows.claimed[0][wire] = false;
            assert!(rows.require_carry_full_author_partition(owner, &mask)
                .unwrap_err().contains("unclaimed physical bit"));
            rows.claimed[0][wire] = true;
            rows.author_census.as_mut().unwrap()[wire] = None;
            assert!(rows.require_carry_full_author_partition(owner, &mask)
                .unwrap_err().contains("wrong physical author"));
            rows.author_census.as_mut().unwrap()[wire] = Some(wrong);
            assert!(rows.require_carry_full_author_partition(owner, &mask)
                .unwrap_err().contains("wrong physical author"));
            rows.author_census.as_mut().unwrap()[wire] = Some(right);
        }

        // Swapping two equal-zero authors preserves the packed row and each
        // aggregate count. The per-wire author guard is the deciding check.
        let authors = rows.author_census.as_mut().unwrap();
        authors[999_424] = Some(NativePhysicalAuthor::Tree);
        authors[989_730] = Some(NativePhysicalAuthor::Header);
        let mut count_only = [0usize; 3];
        for author in authors.iter().flatten() {
            count_only[match author {
                NativePhysicalAuthor::Header => 0,
                NativePhysicalAuthor::Tree => 1,
                NativePhysicalAuthor::Daa => 2,
                _ => panic!("unexpected synthetic Carry author"),
            }] += 1;
        }
        assert_eq!(count_only, counts);
        assert_eq!(rows.bytes(0).unwrap(), vec![0u8; OWNER_BYTES]);
        assert!(rows.require_carry_full_author_partition(owner, &mask)
            .unwrap_err().contains("wrong physical author"));
        println!("C388_NO_FRAME_CARRY_FULL_AUTHOR_MUTANTS_PASS owner={owner} header={} tree={} daa={} missing_zero=3 retagged_zero=3 equal_zero_swapped_count_mutant=true frame=false proof=false client=false",
            counts[0], counts[1], counts[2]);
    }

    #[test]
    fn c388_no_frame_carry_full_source_value_mutants() {
        let owner = MATURE_EIP_SOURCE_OWNER + 1;
        let (mut rows, mask) = zero_fixture();
        let header = vec![Fr::zero(); WIDTH];
        let mut tree_owned = vec![0u8; OWNER_BYTES];
        for (wire, owned) in mask.iter().enumerate() {
            if *owned { NativeHeaderSourceLease::set(&mut tree_owned, wire); }
        }
        let tree_values = vec![0u8; OWNER_BYTES];
        let point_witness = vec![false; crate::point_membership::POINT_WIDTH];
        let mut packed = vec![0u8; OWNER_BYTES];
        let counts = [MATURE_EIP_HEADER_CELLS, MATURE_EIP_TREE_CELLS, MATURE_EIP_DAA_CELLS];
        assert_eq!(rows.require_carry_full_source_values(
            owner, &mask, &header, &tree_owned, &tree_values, &point_witness, &packed,
        ), Ok(counts));
        for wire in [999_424, 989_730, BANKS[0].0] {
            assert_eq!(rows.values[0][wire], Fr::zero());
            rows.values[0][wire] = Fr::one();
            NativeHeaderSourceLease::set(&mut packed, wire);
            assert_eq!(rows.bytes(0).unwrap(), packed,
                "the old whole-row byte equality must accept the value mutant");
            assert!(rows.require_carry_full_source_values(
                owner, &mask, &header, &tree_owned, &tree_values, &point_witness, &packed,
            ).unwrap_err().contains("full source/packed bit"),
                "independent source must reject the equal-packed value mutant wire{wire}");
            rows.values[0][wire] = Fr::zero();
            packed[wire / 8] &= !(1 << (wire % 8));
        }
        println!("C388_NO_FRAME_CARRY_FULL_VALUE_MUTANTS_PASS owner={owner} header_anchor=true tree_zero_pad=true daa_bank=true old_byte_equality_passes=true frame=false proof=false client=false");
    }
}

fn generate_bank53_map_assignment(
    plan: &WorkTreeHistoryPlan,
    input: &NativePrefix,
    exports: &crate::native_owner_exports::NativeExports<'_>,
    map: &crate::legacy_envelope_map::Map,
    owner: usize,
    context: usize,
) -> Result<Bank53MapAssignment, String> {
    let small = matches!(plan.headers(), 3 | 4) && plan.slot_log() == 2 && plan.slots() == 4;
    let first_anchor = plan.headers() == 1984 && plan.slot_log() == 11 && plan.slots() == 2048;
    if !small && !first_anchor {
        return Err("bank53 Map writer requires an admitted N3/N4/N1984 plan".into());
    }
    if context >= BANK53_CONTEXTS {
        return Err("bank53 Map context outside two-context lane".into());
    }
    if owner >= plan.slots() as usize
        || plan.descriptor().root != input.root
        || plan.work_profile().total_be28 != input.total
        || map.n() != plan.headers()
        || map.h() != plan.slot_log()
        || map.slots() != plan.slots() as u64
    {
        return Err("bank53 Map parent geometry or identity mismatch".into());
    }
    let binding = map.binding();
    if binding.parent_root != Some(plan.descriptor().root) {
        return Err("bank53 Map binding is not tied to parent root".into());
    }

    let mut inputs = crate::legacy_envelope_map::Inputs::default();
    for import in map.imports(owner as u64)? {
        let mut value = num_bigint::BigInt::from(0u8);
        for bit in 0..import.width {
            if exports.bit(map.input_index(import, bit)?)? {
                value += num_bigint::BigInt::from(1u8) << bit;
            }
        }
        inputs.put(map, import, &value)?;
    }
    let generated = map.generate(owner as u64, &inputs)?;
    map.check_row(&generated)?;
    if generated.owner != owner as u64 || generated.binding != binding
        || generated.bits.len() != crate::legacy_envelope_map::BANK
        || generated.bits[BANK53_MAP_LIVE_BITS..].iter().any(|bit| *bit)
    {
        return Err("bank53 Map generated row identity, width, or retired tail mismatch".into());
    }
    let mut values = vec![false; BANK53_CONTEXT_BITS];
    values[..BANK53_MAP_LIVE_BITS].copy_from_slice(&generated.bits[..BANK53_MAP_LIVE_BITS]);
    Ok(Bank53MapAssignment {
        owner,
        context,
        binding,
        values,
        #[cfg(test)] h21_test_only: false,
    })
}

/// H21-only ownership preflight for the separate physical Map experiment.
/// This does not widen the production/N3/N4/N1984 writer admission.
#[cfg(test)]
pub(crate) fn validate_h21_bank53_map_lane_for_test(
    plan: &WorkTreeHistoryPlan,
    owner: usize,
    context: usize,
) -> Result<(), String> {
    if (plan.headers(), plan.slot_log(), plan.slots()) != (
        crate::bank53_map::BANK53_N,
        21,
        1usize << 21,
    ) {
        return Err("H21 Bank53 test lane requires the exact admitted history geometry".into());
    }
    if owner >= plan.slots() as usize || context >= BANK53_CONTEXTS {
        return Err("H21 Bank53 test owner/context outside reserved domain".into());
    }
    let mask = plan.physical_assignment_replacement_mask(owner as u64)?;
    let reserved_end = BANK53_BASE + BANK53_CONTEXTS * BANK53_CONTEXT_BITS;
    if mask.len() != WIDTH || reserved_end > WIDTH
        || mask[BANK53_BASE..reserved_end].iter().any(|replaced| *replaced)
    {
        return Err("H21 Bank53 contexts are not wholly HEADER-owned in parent mask".into());
    }
    Ok(())
}

/// Generate the source-owned assignment for an exact H21 parent in test code.
/// Imports are read from NativeExports and Map::generate; no caller bitmap is
/// accepted. The production writer retains its N3/N4/N1984 guard above.
#[cfg(test)]
fn generate_h21_bank53_map_assignment_for_test(
    plan: &WorkTreeHistoryPlan,
    input: &NativePrefix,
    exports: &crate::native_owner_exports::NativeExports<'_>,
    map: &crate::legacy_envelope_map::Map,
    owner: usize,
    context: usize,
) -> Result<Bank53MapAssignment, String> {
    validate_h21_bank53_map_lane_for_test(plan, owner, context)?;
    if plan.descriptor().root != input.root
        || plan.work_profile().total_be28 != input.total
        || map.n() != plan.headers()
        || map.h() != 21
        || map.slots() != (1u64 << 21)
        || map.binding().parent_root != Some(plan.descriptor().root)
    {
        return Err("H21 Bank53 test Map parent identity/geometry mismatch".into());
    }
    let mut inputs = crate::legacy_envelope_map::Inputs::default();
    for import in map.imports(owner as u64)? {
        let mut value = num_bigint::BigInt::from(0u8);
        for bit in 0..import.width {
            if exports.bit(map.input_index(import, bit)?)? {
                value += num_bigint::BigInt::from(1u8) << bit;
            }
        }
        inputs.put(map, import, &value)?;
    }
    let generated = map.generate(owner as u64, &inputs)?;
    map.check_row(&generated)?;
    if generated.owner != owner as u64
        || generated.binding != map.binding()
        || generated.bits.len() != crate::legacy_envelope_map::BANK
        || generated.bits[BANK53_MAP_LIVE_BITS..].iter().any(|bit| *bit)
    {
        return Err("H21 Bank53 test Map generated row identity/width/tail mismatch".into());
    }
    let mut values = vec![false; BANK53_CONTEXT_BITS];
    values[..BANK53_MAP_LIVE_BITS].copy_from_slice(&generated.bits[..BANK53_MAP_LIVE_BITS]);
    Ok(Bank53MapAssignment {
        owner,
        context,
        binding: map.binding(),
        values,
        h21_test_only: true,
    })
}

/// Admission for the separately reviewed c146 Map1 cut. The Binding is
/// intentionally rootless; source identity is supplied by the enclosing
/// producer/consumer call, which validates this exact plan and prefix.
#[cfg(test)]
fn validate_h21_map1_cut_gate_for_test(
    plan: &WorkTreeHistoryPlan,
    map: &crate::legacy_envelope_map::Map,
    owner: usize,
    context: usize,
    approved_binding: &crate::legacy_envelope_map::Binding,
) -> Result<(), String> {
    const OWNER: usize = 844_670;
    const CUT: u64 = 1_827_775;
    use crate::legacy_envelope_map::{LowerBranch, LowerSelector, LowerSource};

    validate_h21_bank53_map_lane_for_test(plan, owner, context)?;
    if owner != OWNER || context != 1 {
        return Err("c149 Map1 cut requires owner844670/context1".into());
    }
    if (plan.headers(), plan.slot_log(), plan.slots()) != (1_827_840, 21, 1 << 21)
        || map.n() != CUT
        || map.h() != 21
        || map.slots() != (1u64 << 21)
        || map.binding().parent_root.is_some()
    {
        return Err("c149 Map1 cut source geometry/root binding mismatch".into());
    }
    let expected = crate::legacy_envelope_map::Map::new_modern_global_u_selected_lower(
        CUT,
        21,
        55,
        LowerSelector {
            source: LowerSource::HeaderDifficulty { height: 841_729 },
            branch: LowerBranch::Pivot(54),
        },
    )?;
    if map.binding() != expected.binding() || approved_binding != &expected.binding() {
        return Err("c149 Map1 cut binding differs from approved e55/D841729/Pivot54".into());
    }
    Ok(())
}

#[cfg(test)]
fn generate_h21_map1_cut_assignment_for_test(
    plan: &WorkTreeHistoryPlan,
    input: &NativePrefix,
    exports: &crate::native_owner_exports::NativeExports<'_>,
    map: &crate::legacy_envelope_map::Map,
    owner: usize,
    context: usize,
    approved_binding: &crate::legacy_envelope_map::Binding,
) -> Result<Bank53MapAssignment, String> {
    validate_native_plan_input(plan, input)?;
    if plan.descriptor().root != input.root
        || plan.work_profile().total_be28 != input.total
    {
        return Err("c149 Map1 cut plan/prefix identity mismatch".into());
    }
    validate_h21_map1_cut_gate_for_test(plan, map, owner, context, approved_binding)?;
    let mut inputs = crate::legacy_envelope_map::Inputs::default();
    for import in map.imports(owner as u64)? {
        let mut value = num_bigint::BigInt::from(0u8);
        for bit in 0..import.width {
            if exports.bit(map.input_index(import, bit)?)? {
                value += num_bigint::BigInt::from(1u8) << bit;
            }
        }
        inputs.put(map, import, &value)?;
    }
    let generated = map.generate(owner as u64, &inputs)?;
    map.check_row(&generated)?;
    if generated.owner != owner as u64
        || generated.binding != map.binding()
        || generated.bits.len() != crate::legacy_envelope_map::BANK
        || generated.bits[BANK53_MAP_LIVE_BITS..].iter().any(|bit| *bit)
    {
        return Err("c149 Map1 cut generated row identity/width/tail mismatch".into());
    }
    let mut values = vec![false; BANK53_CONTEXT_BITS];
    values[..BANK53_MAP_LIVE_BITS].copy_from_slice(&generated.bits[..BANK53_MAP_LIVE_BITS]);
    Ok(Bank53MapAssignment {
        owner,
        context,
        binding: map.binding(),
        values,
        h21_test_only: true,
    })
}

fn write_bank53_map_assignment(
    rows: &mut OwnedRows,
    assignment: &Bank53MapAssignment,
) -> Result<(), String> {
    if assignment.context >= BANK53_CONTEXTS {
        return Err("bank53 Map assignment context mismatch".into());
    }
    if assignment.values.len() != BANK53_CONTEXT_BITS
        || assignment.values[BANK53_MAP_LIVE_BITS..].iter().any(|bit| *bit)
    {
        return Err("bank53 Map assignment tail/slack must be zero".into());
    }
    if !rows.selection.owners().contains(&assignment.owner) {
        return Err("bank53 Map assignment owner outside selected row".into());
    }
    let start = BANK53_BASE + assignment.context * BANK53_CONTEXT_BITS;
    for offset in 0..BANK53_CONTEXT_BITS {
        let (row, local_wire) = rows.local(assignment.owner, start + offset)?;
        if rows.claimed[row][local_wire] {
            return Err(format!("bank53 Map bit already claimed at {}", start + offset));
        }
    }
    for (offset, &value) in assignment.values.iter().enumerate() {
        rows.claim(assignment.owner, start + offset, Fr::from(value as u64))?;
    }
    let row = assignment.owner - rows.selection.first_owner();
    if (start..start + BANK53_CONTEXT_BITS).any(|wire| !rows.claimed[row][wire]) {
        return Err("bank53 Map context assignment is incomplete".into());
    }
    Ok(())
}

fn scored_owner_source_local(
    view: &ScoredOwnerPackingView,
    owner: usize,
    binding: &HeaderSourceBinding,
) -> Result<(), String> {
    let schedule = h21_eligible_context::Eligible08RegularScoreOwner::classify(owner)?;
    if view.owner() != owner
        || view.binding() != binding || binding.owner() != owner
        || view.cells().len() != schedule.typed_cell_count()
        || view.selected_open_reads().is_empty()
        || view.source_term_counts()[0] == 0 || view.source_term_counts()[2] == 0
        || (schedule.active().iter().any(|active| *active)
            && (view.source_term_counts()[1] == 0 || view.source_term_counts()[3] == 0))
        || view.retained_header_daa_active_operand_count() == 0 {
        return Err("C396 packed source owner/binding/custody census".into());
    }
    view.validate_for_packing(binding, owner)?;
    let mut seen = BTreeSet::new();
    let base = owner.checked_mul(WIDTH).ok_or("C396 source owner base overflow")?;
    for (index, cell) in view.cells().iter().enumerate() {
        let local = scored_owner_cell_local(owner, cell)?;
        if !seen.insert(local) || BANKS.iter().any(|&(start, end)| (start..end).contains(&local)) {
            return Err("C396 source duplicate or DAA-overlapping local wire".into());
        }
        if cell.wire() != base + local {
            return Err(format!("C396 source author/address at cell {index}"));
        }
    }
    Ok(())
}

fn scored_owner_cell_local(
    owner: usize,
    cell: &h21_eligible_context::ScoredOwnerPackedCell,
) -> Result<usize, String> {
    let schedule = h21_eligible_context::Eligible08RegularScoreOwner::classify(owner)?;
    let base = owner.checked_mul(WIDTH).ok_or("C396 source owner base overflow")?;
    let local = cell.wire().checked_sub(base).filter(|local| *local < WIDTH)
        .ok_or("C396 source wire outside selected owner")?;
    let expected = match cell.author() {
        ScoredOwnerPackedAuthor::Map(context) if context < 2 =>
            H21EligibleMapStage::map_live(context)?.contains(&local),
        ScoredOwnerPackedAuthor::Score(author) if author.context < 2
            && schedule.active()[author.context]
            && author.origin == owner + 1 && author.cap_owner == owner
            && author.previous_owner == schedule.previous_r_owner()
            && author.max_owner == schedule.max_owner() =>
            H21EligibleMapStage::score_live(author.context)?.contains(&local),
        ScoredOwnerPackedAuthor::Slack(context) if context < 2 =>
            H21EligibleMapStage::slack_live(context)?.contains(&local),
        ScoredOwnerPackedAuthor::Cap { context, origin }
            if context < 2 && schedule.active()[context] && origin == owner + 1 =>
            H21EligibleMapStage::cap_live(context)?.contains(&local),
        _ => false,
    };
    if !expected { return Err("C396 source author/address domain".into()); }
    Ok(local)
}

fn claim_scored_owner_source(
    rows: &mut OwnedRows,
    view: &ScoredOwnerPackingView,
    binding: &HeaderSourceBinding,
) -> Result<(), String> {
    let owner = view.owner();
    scored_owner_source_local(view, owner, binding)?;
    claim_scored_owner_cells(rows, owner, view.cells())
}

fn claim_scored_owner_cells(
    rows: &mut OwnedRows,
    owner: usize,
    cells: &[h21_eligible_context::ScoredOwnerPackedCell],
) -> Result<(), String> {
    let mut seen = BTreeSet::new();
    for cell in cells {
        let local = scored_owner_cell_local(owner, cell)?;
        if !seen.insert(local) {
            return Err(format!("C396 duplicate source cell owner{owner} wire{local}"));
        }
        let (row, wire) = rows.local(owner, local)?;
        if rows.claimed[row][wire] {
            return Err(format!("C396 exclusive source claim overlaps owner{owner} wire{local}"));
        }
    }
    for cell in cells {
        let local = scored_owner_cell_local(owner, cell)?;
        rows.claim_exclusive(owner, local, Fr::from(cell.value() as u64))?;
    }
    Ok(())
}

fn require_scored_owner_source_packed(
    packed: &[u8],
    view: &ScoredOwnerPackingView,
    binding: &HeaderSourceBinding,
) -> Result<(), String> {
    let owner = view.owner();
    scored_owner_source_local(view, owner, binding)?;
    if packed.len() != OWNER_BYTES {
        return Err("C396 packed source owner byte width".into());
    }
    for cell in view.cells() {
        let local = scored_owner_cell_local(owner, cell)?;
        if ((packed[local / 8] >> (local % 8)) & 1 != 0) != cell.value() {
            return Err(format!("C396 packed source author/value wire{local}"));
        }
    }
    Ok(())
}

#[cfg(test)]
mod c396_scored_owner_packed_source_tests {
    use super::*;
    use h21_eligible_context::ScoredOwnerPackedCell;

    const OWNER: usize = 845_887;

    #[test]
    fn c396_physical_map_and_cap_addresses_require_their_typed_author() {
        let map = H21EligibleMapStage::map_live(0).unwrap().start;
        let cap = H21EligibleMapStage::cap_live(0).unwrap().start;
        let map_cell = ScoredOwnerPackedCell::synthetic_for_test(
            OWNER * WIDTH + map, ScoredOwnerPackedAuthor::Map(0), false,
        );
        let cap_cell = ScoredOwnerPackedCell::synthetic_for_test(
            OWNER * WIDTH + cap, ScoredOwnerPackedAuthor::Cap { context: 0, origin: OWNER + 1 }, false,
        );
        assert_eq!(scored_owner_cell_local(OWNER, &map_cell).unwrap(), map);
        assert_eq!(scored_owner_cell_local(OWNER, &cap_cell).unwrap(), cap);
        let wrong_map_author = ScoredOwnerPackedCell::synthetic_for_test(
            map_cell.wire(), ScoredOwnerPackedAuthor::Slack(0), false,
        );
        assert!(scored_owner_cell_local(OWNER, &wrong_map_author).is_err());
        let outside_cap_domain = ScoredOwnerPackedCell::synthetic_for_test(
            OWNER * WIDTH + H21EligibleMapStage::cap_live(0).unwrap().end,
            cap_cell.author(), false,
        );
        assert!(scored_owner_cell_local(OWNER, &outside_cap_domain).is_err());
        let wrong_cap_context = ScoredOwnerPackedCell::synthetic_for_test(
            cap_cell.wire(), ScoredOwnerPackedAuthor::Cap { context: 1, origin: OWNER + 1 }, false,
        );
        assert!(scored_owner_cell_local(OWNER, &wrong_cap_context).is_err());
        let wrong_first_modern_source = ScoredOwnerPackedCell::synthetic_for_test(
            FIRST_MODERN_CAP0_OWNER * WIDTH + map,
            ScoredOwnerPackedAuthor::Map(0), false,
        );
        assert!(scored_owner_cell_local(OWNER, &wrong_first_modern_source).is_err());
        assert!(scored_owner_cell_local(OWNER - 1, &map_cell).is_err());
    }

    #[test]
    fn c396_duplicate_or_prior_x_claim_fails_before_mutation() {
        let owner = OWNER;
        let local = H21EligibleMapStage::map_live(0).unwrap().start;
        let cell = ScoredOwnerPackedCell::synthetic_for_test(
            owner * WIDTH + local, ScoredOwnerPackedAuthor::Map(0), false,
        );
        let mut duplicate = OwnedRows::new(OwnerSelection::Single {
            owner, class: crate::daa_history_roster::OwnerClass::Carry,
        });
        assert!(claim_scored_owner_cells(&mut duplicate, owner, &[cell, cell]).is_err());
        assert_eq!(duplicate.claimed[0].iter().filter(|claimed| **claimed).count(), 0);

        let mut prior = OwnedRows::new(OwnerSelection::Single {
            owner, class: crate::daa_history_roster::OwnerClass::Carry,
        });
        prior.claim(owner, local, Fr::zero()).unwrap();
        assert!(claim_scored_owner_cells(&mut prior, owner, &[cell]).is_err());
        assert_eq!(prior.claimed[0].iter().filter(|claimed| **claimed).count(), 1);
    }
}

#[cfg(test)]
#[path = "packed_owner_assembly_c444_tests.rs"]
mod c444_tests;

fn claim_eligible08_overlay_map(
    rows: &mut OwnedRows, owner: usize,
    lease: &Bank53TypedSourceLease,
    expected: &HeaderSourceBinding,
) -> Result<(), String> {
    lease.validate(expected, owner)?;
    let cells = lease.entries();
    if owner != FIRST_MODERN_CAP0_OWNER || cells.len() != BANK53_CONTEXTS * BANK53_CONTEXT_BITS {
        return Err("C373 exact two-context Map/Score/Slack claim census".into());
    }
    // Check the complete domain and all prior claims before mutating one bit.
    for (index, cell) in cells.iter().enumerate() {
        let local = cell.physical_wire().checked_sub(owner.checked_mul(WIDTH)
            .ok_or("C373 Bank53 owner base overflow")?).ok_or("C373 Bank53 physical owner")?;
        if local != BANK53_BASE + index {
            return Err("C373 Map/Score/Slack exact ordered Bank53 domain".into());
        }
        let (row, wire) = rows.local(owner, local)?;
        if rows.claimed[row][wire] {
            return Err(format!("C373 exclusive Bank53 claim overlaps owner{owner} wire{local}"));
        }
    }
    for cell in cells {
        let local = cell.physical_wire() % WIDTH;
        rows.claim_exclusive(owner, local, Fr::from(cell.value() as u64))?;
    }
    Ok(())
}

/// Validate the complete Map-only domain before HEADER gives up any cell.
/// This is also the no-frame test entry point: production and tests use the
/// same shape, parent, mask and two-range checks.
pub(crate) fn preflight_map_pair_reservation(
    lease: &Eligible08MapPairLease,
    expected: &HeaderSourceBinding,
    owner: usize,
    class: crate::daa_history_roster::OwnerClass,
    mask: &[bool],
) -> Result<Vec<bool>, String> {
    if mask.len() != WIDTH {
        return Err("C438 Map pair HEADER replacement mask width".into());
    }
    let cells = lease.checked_cells(expected, owner, class)?;
    if cells.len() != 2 * BANK53_MAP_LIVE_BITS {
        return Err("C438 Map pair live-cell census".into());
    }
    let base = owner.checked_mul(WIDTH).ok_or("C438 Map pair owner base overflow")?;
    let mut reserved = vec![false; WIDTH];
    for (index, cell) in cells.iter().enumerate() {
        let context = index / BANK53_MAP_LIVE_BITS;
        let offset = index % BANK53_MAP_LIVE_BITS;
        let local = BANK53_BASE + context * BANK53_CONTEXT_BITS + offset;
        if cell.context() != context
            || cell.physical_wire() != base + local
            || mask[local]
            || reserved[local]
        {
            return Err(format!("C438 Map pair exact HEADER reservation index{index}"));
        }
        reserved[local] = true;
    }
    Ok(reserved)
}

/// Before transferring Map LIVE, prove that both it and the HEADER-zero
/// complement are ordinary zero HEADER assignments on this exact owner.
fn preflight_mixed_map_header_seed(
    owner: usize, class: crate::daa_history_roster::OwnerClass,
    mask: &[bool], native: &[Fr], reserved: &[bool],
) -> Result<(), String> {
    if !mixed_map_header_class_allowed(owner, class)
        || mask.len()!=WIDTH || native.len()!=WIDTH || reserved.len()!=WIDTH {
        return Err("C503 mixed HEADER preseed owner/width".into());
    }
    require_mixed_map_header_no_scheduled(owner, class)?;
    let mut map=0usize;
    let mut zero=0usize;
    for context in 0..BANK53_CONTEXTS {
        for offset in 0..BANK53_CONTEXT_BITS {
            let local=BANK53_BASE+context*BANK53_CONTEXT_BITS+offset;
            if mask[local] || native[local]!=Fr::zero() {
                return Err(format!("C503 mixed old HEADER nonzero/replaced wire{local}"));
            }
            match crate::bank53_required_writer::required_bank53_writer(
                owner,context,offset).map_err(|error|error.to_string())? {
                crate::bank53_required_writer::RequiredWriter::Map {context: found}
                    if found==context && reserved[local] => {map+=1;}
                crate::bank53_required_writer::RequiredWriter::HeaderZero
                    if !reserved[local] => {zero+=1;}
                _=>return Err(format!("C503 mixed preseed writer/reservation wire{local}")),
            }
        }
    }
    if map!=2*BANK53_MAP_LIVE_BITS
        || zero!=2*(BANK53_CONTEXT_BITS-BANK53_MAP_LIVE_BITS) {
        return Err("C503 mixed preseed exact Map/HeaderZero census".into());
    }
    Ok(())
}

#[derive(Clone, Copy)]
enum MapPhysicalSource<'a> {
    Pair(&'a Eligible08MapPairLease),
    PairSlack(&'a Eligible08MapSlackBundle),
    PairSlackAnchor(&'a Eligible08MapSlackAnchorBundle),
    PairSlackSecondAnchor(&'a Eligible08MapSlackSecondAnchorBundle, &'a NativePackedRow),
}

impl MapPhysicalSource<'_> {
    fn map_lease(&self) -> &Eligible08MapPairLease {
        match self {
            Self::Pair(lease) => lease,
            Self::PairSlack(bundle) => bundle.map_lease(),
            Self::PairSlackAnchor(bundle) => bundle.map_slack().map_lease(),
            Self::PairSlackSecondAnchor(bundle, _) => bundle.map_slack().map_lease(),
        }
    }
}

trait AnchorBank53Bundle {
    const OWNER: usize;
    fn map_slack(&self) -> &Eligible08MapSlackBundle;
    fn checked_score_cells(&self, expected: &HeaderSourceBinding,
        owner: usize, class: crate::daa_history_roster::OwnerClass,
    ) -> Result<Vec<Eligible08ScoreAnchorCell>, String>;
    fn checked_score_terms_len(&self, expected: &HeaderSourceBinding,
        owner: usize, class: crate::daa_history_roster::OwnerClass, context: usize,
    ) -> Result<usize, String>;
}

impl AnchorBank53Bundle for Eligible08MapSlackAnchorBundle {
    const OWNER: usize = 417_790;
    fn map_slack(&self) -> &Eligible08MapSlackBundle {
        Eligible08MapSlackAnchorBundle::map_slack(self)
    }
    fn checked_score_cells(&self, expected: &HeaderSourceBinding,
        owner: usize, class: crate::daa_history_roster::OwnerClass,
    ) -> Result<Vec<Eligible08ScoreAnchorCell>, String> {
        Eligible08MapSlackAnchorBundle::checked_score_cells(self, expected, owner, class)
    }
    fn checked_score_terms_len(&self, expected: &HeaderSourceBinding,
        owner: usize, class: crate::daa_history_roster::OwnerClass, context: usize,
    ) -> Result<usize, String> {
        Ok(Eligible08MapSlackAnchorBundle::checked_score_terms(
            self, expected, owner, class, context,
        )?.len())
    }
}

impl AnchorBank53Bundle for Eligible08MapSlackSecondAnchorBundle {
    const OWNER: usize = 845_758;
    fn map_slack(&self) -> &Eligible08MapSlackBundle {
        Eligible08MapSlackSecondAnchorBundle::map_slack(self)
    }
    fn checked_score_cells(&self, expected: &HeaderSourceBinding,
        owner: usize, class: crate::daa_history_roster::OwnerClass,
    ) -> Result<Vec<Eligible08ScoreAnchorCell>, String> {
        Eligible08MapSlackSecondAnchorBundle::checked_score_cells(self, expected, owner, class)
    }
    fn checked_score_terms_len(&self, expected: &HeaderSourceBinding,
        owner: usize, class: crate::daa_history_roster::OwnerClass, context: usize,
    ) -> Result<usize, String> {
        Ok(Eligible08MapSlackSecondAnchorBundle::checked_score_terms(
            self, expected, owner, class, context,
        )?.len())
    }
}

/// One complete ordered Bank53 partition from the selected opaque anchor
/// source. This owner-local physical check does not admit global ROW.
fn checked_anchor_bank53_cells<B: AnchorBank53Bundle>(
    bundle: &B,
    expected: &HeaderSourceBinding,
    owner: usize,
    class: crate::daa_history_roster::OwnerClass,
) -> Result<Vec<(usize, bool)>, String> {
    use crate::daa_history_roster::OwnerClass;
    if owner != B::OWNER || class != OwnerClass::Carry {
        return Err("C443 exact ScoreAnchor Carry owner".into());
    }
    let map_slack = bundle.map_slack();
    let maps = map_slack.map_lease().checked_cells(expected, owner, class)?;
    let scores = bundle.checked_score_cells(expected, owner, class)?;
    let slack = map_slack.checked_slack_cells(expected, owner, class)?;
    if maps.len() != BANK53_CONTEXTS * BANK53_MAP_LIVE_BITS
        || scores.len() != BANK53_CONTEXTS * crate::origin_score::INPUT
        || slack.len() != BANK53_CONTEXTS * BANK53_SLACK_BITS
    {
        return Err("C441 exact Map/ScoreAnchor/Slack cell census".into());
    }
    let base = owner.checked_mul(WIDTH).ok_or("C441 owner base overflow")?;
    let mut cells = Vec::with_capacity(BANK53_CONTEXTS * BANK53_CONTEXT_BITS);
    for context in 0..BANK53_CONTEXTS {
        let start = BANK53_BASE + context * BANK53_CONTEXT_BITS;
        if bundle.checked_score_terms_len(expected, owner, class, context)? == 0
            || map_slack.checked_slack_terms(expected, owner, class, context)?.len()
                != BANK53_SLACK_BITS
        {
            return Err(format!("C441 Score/Slack ROW source census context{context}"));
        }
        for offset in 0..BANK53_MAP_LIVE_BITS {
            let cell = &maps[context * BANK53_MAP_LIVE_BITS + offset];
            let local = start + offset;
            if cell.context() != context || cell.physical_wire() != base + local {
                return Err(format!("C441 exact Map cell context{context} offset{offset}"));
            }
            cells.push((local, cell.value()));
        }
        for offset in 0..crate::origin_score::INPUT {
            let cell = &scores[context * crate::origin_score::INPUT + offset];
            let local = start + BANK53_MAP_LIVE_BITS + offset;
            if cell.context() != context || cell.physical_wire() != base + local {
                return Err(format!("C441 exact ScoreAnchor cell context{context} offset{offset}"));
            }
            cells.push((local, cell.value()));
        }
        for offset in 0..BANK53_SLACK_BITS {
            let cell = &slack[context * BANK53_SLACK_BITS + offset];
            let local = start + BANK53_MAP_LIVE_BITS + crate::origin_score::INPUT + offset;
            if cell.context() != context || cell.physical_wire() != base + local || cell.value() {
                return Err(format!("C441 exact Slack zero context{context} offset{offset}"));
            }
            cells.push((local, false));
        }
    }
    if cells.len() != BANK53_CONTEXTS * BANK53_CONTEXT_BITS
        || cells.iter().enumerate().any(|(index, (local, _))|
            *local != BANK53_BASE + index)
    {
        return Err("C441 complete ordered Bank53 physical partition".into());
    }
    Ok(cells)
}

fn preflight_map_slack_anchor_reservation<B: AnchorBank53Bundle>(
    bundle: &B,
    expected: &HeaderSourceBinding,
    owner: usize,
    class: crate::daa_history_roster::OwnerClass,
    mask: &[bool],
) -> Result<Vec<bool>, String> {
    if mask.len() != WIDTH { return Err("C441 HEADER mask width".into()); }
    let cells = checked_anchor_bank53_cells(bundle, expected, owner, class)?;
    let mut reserved = vec![false; WIDTH];
    for (local, _) in cells {
        if mask[local] || reserved[local] {
            return Err(format!("C441 HEADER reservation overlap wire{local}"));
        }
        reserved[local] = true;
    }
    Ok(reserved)
}

/// Check the entire selected source and all prior claims before any write.
fn claim_map_slack_anchor_live<B: AnchorBank53Bundle>(
    rows: &mut OwnedRows,
    bundle: &B,
    expected: &HeaderSourceBinding,
    owner: usize,
    class: crate::daa_history_roster::OwnerClass,
) -> Result<(), String> {
    let cells = checked_anchor_bank53_cells(bundle, expected, owner, class)?;
    for &(local, _) in &cells {
        let (row, wire) = rows.local(owner, local)?;
        if rows.claimed[row][wire] {
            return Err(format!("C441 exclusive Bank53 overlap wire{local}"));
        }
    }
    for (local, value) in cells {
        rows.claim_exclusive(owner, local, Fr::from(value as u64))?;
    }
    Ok(())
}

fn require_map_slack_anchor_claim_census<B: AnchorBank53Bundle>(
    rows: &OwnedRows,
    bundle: &B,
    expected: &HeaderSourceBinding,
    owner: usize,
    class: crate::daa_history_roster::OwnerClass,
) -> Result<(), String> {
    for (local, value) in checked_anchor_bank53_cells(bundle, expected, owner, class)? {
        let (row, wire) = rows.local(owner, local)?;
        if !rows.claimed[row][wire] || rows.values[row][wire] != Fr::from(value as u64) {
            return Err(format!("C441 missing or changed Bank53 claim wire{local}"));
        }
    }
    Ok(())
}

fn require_map_slack_anchor_packed<B: AnchorBank53Bundle>(
    packed: &[u8], bundle: &B,
    expected: &HeaderSourceBinding, owner: usize,
    class: crate::daa_history_roster::OwnerClass,
) -> Result<(), String> {
    if packed.len() != OWNER_BYTES { return Err("C441 packed owner width".into()); }
    for (local, value) in checked_anchor_bank53_cells(bundle, expected, owner, class)? {
        let actual = (packed[local / 8] >> (local % 8)) & 1 != 0;
        if actual != value {
            return Err(format!("C441 packed Bank53 source value wire{local}"));
        }
    }
    Ok(())
}

/// Retire only the two exact Map spans and two exact Slack tails from HEADER.
/// The intervening Score cells remain explicit HEADER zeros on this path.
fn preflight_map_slack_reservation(
    bundle: &Eligible08MapSlackBundle,
    expected: &HeaderSourceBinding,
    owner: usize,
    class: crate::daa_history_roster::OwnerClass,
    mask: &[bool],
    header_native: &[Fr],
) -> Result<Vec<bool>, String> {
    if header_native.len() != WIDTH { return Err("C440 HEADER native width".into()); }
    if owner == FIRST_MODERN_CAP0_OWNER
        || h21_eligible_context::Eligible08RegularScoreOwner::classify(owner).is_ok() {
        return Err("C440 ordinary Map+Slack path rejects special owner".into());
    }
    if owner != 0 || class != crate::daa_history_roster::OwnerClass::Genesis {
        return Err("C441 Map+Slack path only authorizes proven Genesis owner0".into());
    }
    let mut reserved = preflight_map_pair_reservation(
        bundle.map_lease(), expected, owner, class, mask,
    )?;
    let cells = bundle.checked_slack_cells(expected, owner, class)?;
    if cells.len() != BANK53_CONTEXTS * BANK53_SLACK_BITS {
        return Err("C440 Slack exact two-context cell census".into());
    }
    let base = owner.checked_mul(WIDTH).ok_or("C440 Slack owner base overflow")?;
    for (index, cell) in cells.iter().enumerate() {
        let context = index / BANK53_SLACK_BITS;
        let offset = index % BANK53_SLACK_BITS;
        let local = BANK53_BASE + context * BANK53_CONTEXT_BITS
            + BANK53_MAP_LIVE_BITS + crate::origin_score::INPUT + offset;
        if cell.context() != context || cell.physical_wire() != base + local
            || cell.value() || mask[local] || reserved[local]
        {
            return Err(format!("C440 Slack exact HEADER reservation index{index}"));
        }
        reserved[local] = true;
    }
    for context in 0..BANK53_CONTEXTS {
        let terms = bundle.checked_slack_terms(expected, owner, class, context)?;
        if terms.len() != BANK53_SLACK_BITS {
            return Err(format!("C440 Slack ROW source census context{context}"));
        }
        let score = BANK53_BASE + context * BANK53_CONTEXT_BITS + BANK53_MAP_LIVE_BITS;
        for local in score..score + crate::origin_score::INPUT {
            if mask[local] || reserved[local] || header_native[local] != Fr::zero() {
                return Err(format!("C440 inactive Score must remain HEADER zero wire{local}"));
            }
        }
    }
    Ok(reserved)
}

fn claim_map_pair_live(
    rows: &mut OwnedRows,
    lease: &Eligible08MapPairLease,
    expected: &HeaderSourceBinding,
    owner: usize,
    class: crate::daa_history_roster::OwnerClass,
) -> Result<(), String> {
    let cells = lease.checked_cells(expected, owner, class)?;
    if let Some(capture) = rows.mixed_map_header_capture.as_mut() {
        if capture.lease_identity.is_some() {
            return Err("C505 mixed Map lease already claimed".into());
        }
        capture.lease_identity = Some(lease as *const Eligible08MapPairLease);
    }
    if cells.len() != 2 * BANK53_MAP_LIVE_BITS {
        return Err("C438 Map pair claim census".into());
    }
    let base = owner.checked_mul(WIDTH).ok_or("C438 Map pair owner base overflow")?;
    for (index, cell) in cells.iter().enumerate() {
        let context = index / BANK53_MAP_LIVE_BITS;
        let local = BANK53_BASE + context * BANK53_CONTEXT_BITS
            + index % BANK53_MAP_LIVE_BITS;
        if cell.context() != context || cell.physical_wire() != base + local {
            return Err(format!("C438 Map pair exact claim order index{index}"));
        }
        let (row, wire) = rows.local(owner, local)?;
        if rows.claimed[row][wire] {
            return Err(format!("C438 Map pair exclusive claim overlaps wire{local}"));
        }
    }
    for cell in cells {
        let local = cell.physical_wire() - base;
        rows.claim_exclusive(owner, local, Fr::from(cell.value() as u64))?;
        rows.record_mixed_map_claim(owner,local,cell.value())?;
    }
    Ok(())
}

/// Validate every prior claim before writing any Map or Slack bit. Equal-zero
/// overlap is a second author and is rejected just like a differing value.
fn claim_map_slack_live(
    rows: &mut OwnedRows,
    bundle: &Eligible08MapSlackBundle,
    expected: &HeaderSourceBinding,
    owner: usize,
    class: crate::daa_history_roster::OwnerClass,
) -> Result<(), String> {
    let maps = bundle.map_lease().checked_cells(expected, owner, class)?;
    let slack = bundle.checked_slack_cells(expected, owner, class)?;
    if maps.len() != BANK53_CONTEXTS * BANK53_MAP_LIVE_BITS
        || slack.len() != BANK53_CONTEXTS * BANK53_SLACK_BITS
    {
        return Err("C440 Map+Slack physical claim census".into());
    }
    let base = owner.checked_mul(WIDTH).ok_or("C440 Map+Slack owner base overflow")?;
    for (index, cell) in maps.iter().enumerate() {
        let context = index / BANK53_MAP_LIVE_BITS;
        let local = BANK53_BASE + context * BANK53_CONTEXT_BITS
            + index % BANK53_MAP_LIVE_BITS;
        if cell.context() != context || cell.physical_wire() != base + local {
            return Err(format!("C440 Map claim order index{index}"));
        }
        let (row, wire) = rows.local(owner, local)?;
        if rows.claimed[row][wire] {
            return Err(format!("C440 Map+Slack exclusive claim overlaps wire{local}"));
        }
    }
    for (index, cell) in slack.iter().enumerate() {
        let context = index / BANK53_SLACK_BITS;
        let local = BANK53_BASE + context * BANK53_CONTEXT_BITS
            + BANK53_MAP_LIVE_BITS + crate::origin_score::INPUT
            + index % BANK53_SLACK_BITS;
        if cell.context() != context || cell.physical_wire() != base + local || cell.value() {
            return Err(format!("C440 Slack claim order/value index{index}"));
        }
        let (row, wire) = rows.local(owner, local)?;
        if rows.claimed[row][wire] {
            return Err(format!("C440 Map+Slack exclusive claim overlaps wire{local}"));
        }
    }
    for cell in maps {
        rows.claim_exclusive(owner, cell.physical_wire() - base,
            Fr::from(cell.value() as u64))?;
    }
    for cell in slack {
        rows.claim_exclusive(owner, cell.physical_wire() - base,
            Fr::from(cell.value() as u64))?;
    }
    Ok(())
}

fn require_map_slack_claim_census(
    rows: &OwnedRows,
    bundle: &Eligible08MapSlackBundle,
    expected: &HeaderSourceBinding,
    owner: usize,
    class: crate::daa_history_roster::OwnerClass,
) -> Result<(), String> {
    let base = owner.checked_mul(WIDTH).ok_or("C440 claim census owner base overflow")?;
    let maps = bundle.map_lease().checked_cells(expected, owner, class)?;
    let slack = bundle.checked_slack_cells(expected, owner, class)?;
    if maps.len() != BANK53_CONTEXTS * BANK53_MAP_LIVE_BITS
        || slack.len() != BANK53_CONTEXTS * BANK53_SLACK_BITS {
        return Err("C440 claim census source extent".into());
    }
    for (local, value) in maps.iter().map(|cell| {
        (cell.physical_wire() - base, cell.value())
    }).chain(slack.iter().map(|cell| {
        (cell.physical_wire() - base, cell.value())
    })) {
        let (row, wire) = rows.local(owner, local)?;
        if !rows.claimed[row][wire] || rows.values[row][wire] != Fr::from(value as u64) {
            return Err(format!("C440 missing or changed Map+Slack claim wire{local}"));
        }
    }
    for context in 0..BANK53_CONTEXTS {
        let score = BANK53_BASE + context * BANK53_CONTEXT_BITS + BANK53_MAP_LIVE_BITS;
        for local in score..score + crate::origin_score::INPUT {
            let (row, wire) = rows.local(owner, local)?;
            if !rows.claimed[row][wire] || rows.values[row][wire] != Fr::zero() {
                return Err(format!("C440 missing or changed HEADER Score zero wire{local}"));
            }
        }
    }
    Ok(())
}

/// A no-frame probe of the exact production preflight and exclusive claim.
/// On rejection, verify that no Map claim was partially written.
#[cfg(test)]
pub(crate) fn c438_map_pair_claim_probe_for_test(
    lease: &Eligible08MapPairLease,
    expected: &HeaderSourceBinding,
    owner: usize,
    class: crate::daa_history_roster::OwnerClass,
    mask: &[bool],
    prior_local: Option<usize>,
) -> Result<usize, String> {
    let reserved = preflight_map_pair_reservation(lease, expected, owner, class, mask)?;
    let mut rows = OwnedRows::new(OwnerSelection::Single { owner, class });
    let mut prior_value = Fr::one();
    if let Some(local) = prior_local {
        if *reserved.get(local).ok_or("C438 prior claim outside owner")? {
            let base = owner.checked_mul(WIDTH).ok_or("C438 owner base overflow")?;
            let cell = lease.checked_cells(expected, owner, class)?.iter()
                .find(|cell| cell.physical_wire() == base + local)
                .ok_or("C438 reserved prior cell absent")?;
            prior_value = Fr::from(cell.value() as u64);
        }
        rows.claim_exclusive(owner, local, prior_value)?;
    }
    let prior_claims = rows.claimed[0].clone();
    let prior_values = rows.values[0].clone();
    if let Err(error) = claim_map_pair_live(&mut rows, lease, expected, owner, class) {
        if rows.claimed[0] != prior_claims || rows.values[0] != prior_values {
            return Err("C438 Map pair claim mutated before rejection".into());
        }
        return Err(error);
    }
    if let Some(local) = prior_local {
        if !rows.claimed[0][local] || rows.values[0][local] != prior_value {
            return Err("C438 non-Map prior claim changed".into());
        }
    }
    for (wire, &is_reserved) in reserved.iter().enumerate() {
        if is_reserved && !rows.claimed[0][wire] {
            return Err("C438 reserved Map cell not claimed".into());
        }
        if !is_reserved && prior_local != Some(wire) && rows.claimed[0][wire] {
            return Err("C438 Map claim escaped live reservation".into());
        }
    }
    Ok(reserved.iter().filter(|bit| **bit).count())
}

fn require_map_pair_packed(
    packed: &[u8], lease: &Eligible08MapPairLease,
    expected: &HeaderSourceBinding, owner: usize,
    class: crate::daa_history_roster::OwnerClass,
) -> Result<(), String> {
    if packed.len() != OWNER_BYTES {
        return Err("C438 Map pair packed owner width".into());
    }
    let base = owner.checked_mul(WIDTH).ok_or("C438 Map pair owner base overflow")?;
    for cell in lease.checked_cells(expected, owner, class)? {
        let local = cell.physical_wire() - base;
        let value = (packed[local / 8] >> (local % 8)) & 1 != 0;
        if value != cell.value() {
            return Err(format!("C438 Map pair packed source value wire{local}"));
        }
    }
    Ok(())
}

fn require_map_slack_packed(
    packed: &[u8], bundle: &Eligible08MapSlackBundle,
    expected: &HeaderSourceBinding, owner: usize,
    class: crate::daa_history_roster::OwnerClass,
) -> Result<(), String> {
    require_map_pair_packed(packed, bundle.map_lease(), expected, owner, class)?;
    let base = owner.checked_mul(WIDTH).ok_or("C440 packed owner base overflow")?;
    for cell in bundle.checked_slack_cells(expected, owner, class)? {
        let local = cell.physical_wire() - base;
        if (packed[local / 8] >> (local % 8)) & 1 != 0 || cell.value() {
            return Err(format!("C440 packed Slack source value wire{local}"));
        }
    }
    for context in 0..BANK53_CONTEXTS {
        let score = BANK53_BASE + context * BANK53_CONTEXT_BITS + BANK53_MAP_LIVE_BITS;
        for local in score..score + crate::origin_score::INPUT {
            if (packed[local / 8] >> (local % 8)) & 1 != 0 {
                return Err(format!("C440 packed inactive Score zero wire{local}"));
            }
        }
    }
    Ok(())
}

fn require_eligible08_overlay_packed(
    owner: usize, packed: &[u8], cells: &Eligible08CheckedLocalCells,
    expected: &HeaderSourceBinding,
) -> Result<(), String> {
    if owner != FIRST_MODERN_CAP0_OWNER || packed.len() != OWNER_BYTES
        || cells.map_score_slack.entries().len() != BANK53_CONTEXTS * BANK53_CONTEXT_BITS
        || cells.cap.len() != FIRST_MODERN_CAP0_CELLS + FIRST_MODERN_CAP1_CELLS
        || cells.work_d.len() != 224 {
        return Err("C373 packed overlay exact owner/width/20,704-cell census".into());
    }
    let packed_bit = |local: usize| -> Result<bool, String> {
        if local >= WIDTH { return Err("C373 packed overlay local wire extent".into()); }
        Ok((packed[local / 8] >> (local % 8)) & 1 != 0)
    };
    cells.map_score_slack.validate(expected, owner)?;
    for (index, cell) in cells.map_score_slack.entries().iter().enumerate() {
        let local = cell.physical_wire() % WIDTH;
        if cell.physical_wire() / WIDTH != owner || local != BANK53_BASE + index
            || packed_bit(local)? != cell.value() {
            return Err(format!("C373 packed Map/Score/Slack author/value wire{local}"));
        }
    }
    let mut cap_seen = BTreeSet::new();
    for &(local, value) in &cells.cap {
        let in_cap = (FIRST_MODERN_CAP0_BASE..FIRST_MODERN_CAP0_BASE + FIRST_MODERN_CAP0_CELLS)
            .contains(&local)
            || (FIRST_MODERN_CAP1_BASE..FIRST_MODERN_CAP1_BASE + FIRST_MODERN_CAP1_CELLS)
                .contains(&local);
        if !in_cap || !cap_seen.insert(local) || packed_bit(local)? != value {
            return Err(format!("C373 packed Cap author/value wire{local}"));
        }
    }
    if cap_seen.len() != 4_096 {
        return Err("C373 packed Cap exact two-context domain".into());
    }
    for (bit, &(local, value)) in cells.work_d.iter().enumerate() {
        if local != crate::legacy_envelope_map::D_LOCAL + bit || packed_bit(local)? != value {
            return Err(format!("C373 packed Work-D author/value wire{local}"));
        }
    }
    Ok(())
}

#[cfg(test)]
mod c373_overlay_prepack_tests {
    use super::*;

    fn checked_local_zeros() -> Eligible08CheckedLocalCells {
        let binding = HeaderSourceBinding::diagnostic_for_test(FIRST_MODERN_CAP0_OWNER);
        let cap = (FIRST_MODERN_CAP0_BASE..FIRST_MODERN_CAP0_BASE + FIRST_MODERN_CAP0_CELLS)
            .chain(FIRST_MODERN_CAP1_BASE..FIRST_MODERN_CAP1_BASE + FIRST_MODERN_CAP1_CELLS)
            .map(|wire| (wire, false)).collect();
        Eligible08CheckedLocalCells {
            map_score_slack: Bank53TypedSourceLease::synthetic_for_test(
                binding, FIRST_MODERN_CAP0_OWNER).unwrap(),
            cap,
            work_d: (crate::legacy_envelope_map::D_LOCAL
                ..crate::legacy_envelope_map::D_LOCAL + 224)
                .map(|wire| (wire, false)).collect(),
        }
    }

    #[test]
    fn c373_two_context_claim_is_exclusive_even_for_equal_prior_values() {
        let owner = FIRST_MODERN_CAP0_OWNER;
        let selection = OwnerSelection::Single {
            owner, class: crate::daa_history_roster::OwnerClass::Carry,
        };
        let mut rows = OwnedRows::new(selection);
        let unrelated = BANK53_BASE - 1;
        rows.claim(owner, unrelated, Fr::zero()).unwrap();
        rows.claim(owner, unrelated, Fr::zero()).unwrap();
        let binding = HeaderSourceBinding::diagnostic_for_test(owner);
        let cells = Bank53TypedSourceLease::synthetic_for_test(binding.clone(), owner).unwrap();
        claim_eligible08_overlay_map(&mut rows, owner, &cells, &binding).unwrap();
        assert!(rows.claimed[0][BANK53_BASE]);
        assert!(rows.claimed[0][BANK53_BASE + 2 * BANK53_CONTEXT_BITS - 1]);
        assert!(claim_eligible08_overlay_map(&mut rows, owner, &cells, &binding).unwrap_err()
            .contains("exclusive Bank53 claim overlaps"));

        let mut equal_prior = OwnedRows::new(selection);
        equal_prior.claim(owner, BANK53_BASE + 1, Fr::zero()).unwrap();
        let claimed_before = equal_prior.claimed[0].iter().filter(|bit| **bit).count();
        assert!(claim_eligible08_overlay_map(&mut equal_prior, owner, &cells, &binding).unwrap_err()
            .contains("exclusive Bank53 claim overlaps"));
        assert_eq!(equal_prior.claimed[0].iter().filter(|bit| **bit).count(), claimed_before);
        let mut wrong_domain = Bank53TypedSourceLease::synthetic_for_test(
            binding.clone(), owner).unwrap();
        wrong_domain.mutate_entry_for_test(0, Some(owner * WIDTH + BANK53_BASE + 1), None, None);
        assert_eq!(claim_eligible08_overlay_map(&mut OwnedRows::new(selection), owner,
            &wrong_domain, &binding).unwrap_err(), "C375 Bank53 exact geometry/typed domain index0");
        assert!(claim_eligible08_overlay_map(&mut OwnedRows::new(selection), owner - 1,
            &cells, &binding).is_err());
    }

    #[test]
    fn c373_same_binding_wrong_map_cap_and_work_values_fail_separately() {
        // Only a value changes in each mutant; the producer's binding gate is
        // exercised by the same entry point before this final local comparison.
        let packed = vec![0u8; OWNER_BYTES];
        let cells = checked_local_zeros();
        let binding = cells.map_score_slack.binding().clone();
        require_eligible08_overlay_packed(FIRST_MODERN_CAP0_OWNER, &packed, &cells, &binding).unwrap();
        let mut wrong_map = checked_local_zeros();
        wrong_map.map_score_slack.mutate_entry_for_test(0, None, None, Some(true));
        assert!(require_eligible08_overlay_packed(FIRST_MODERN_CAP0_OWNER,
            &packed, &wrong_map, &binding).unwrap_err().contains("packed Map/Score/Slack"));
        let mut wrong_cap = checked_local_zeros();
        wrong_cap.cap[FIRST_MODERN_CAP0_CELLS].1 = true;
        assert!(require_eligible08_overlay_packed(FIRST_MODERN_CAP0_OWNER,
            &packed, &wrong_cap, &binding).unwrap_err().contains("packed Cap"));
        let mut wrong_work = checked_local_zeros();
        wrong_work.work_d[0].1 = true;
        assert!(require_eligible08_overlay_packed(FIRST_MODERN_CAP0_OWNER,
            &packed, &wrong_work, &binding).unwrap_err().contains("packed Work-D"));
        let mut duplicate_cap = checked_local_zeros();
        duplicate_cap.cap[1].0 = duplicate_cap.cap[0].0;
        assert!(require_eligible08_overlay_packed(FIRST_MODERN_CAP0_OWNER,
            &packed, &duplicate_cap, &binding).unwrap_err().contains("packed Cap"));
    }
}

// Test instrumentation wraps the original expression. Production builds
// erase the clock and timing parameter, retaining the expression unchanged.
macro_rules! native_timed {
    ($timings:ident, $field:ident, $expression:expr) => {{
        #[cfg(test)]
        let started = $timings.as_ref().map(|_| std::time::Instant::now());
        let result = $expression;
        #[cfg(test)]
        if let Some(started) = started {
            if let Some(timings) = $timings.as_deref_mut() {
                timings.$field += started.elapsed().as_nanos();
            }
        }
        result
    }};
}

#[cfg(test)]
#[derive(Default, Debug)]
pub(crate) struct NativePhaseTimings {
    pub(crate) allocation_ns: u128,
    pub(crate) header_fields_ns: u128,
    pub(crate) header_boundary_ns: u128,
    pub(crate) header_order_ns: u128,
    pub(crate) header_claims_ns: u128,
    pub(crate) tree_ns: u128,
    pub(crate) pack_initial_ns: u128,
    pub(crate) retarget_ns: u128,
    pub(crate) bank_claims_ns: u128,
    pub(crate) completeness_ns: u128,
    pub(crate) pack_final_ns: u128,
    pub(crate) total_ns: u128,
}

fn seed_header(
    plan: &WorkTreeHistoryPlan,
    max_adapter: Option<&crate::max_header_adapter::MaxHeaderAdapter<'_>>,
    #[cfg(test)] legacy_adapter: Option<&crate::legacy_native_adapter::LegacyNativeAdapter<'_>>,
    input: &NativePrefix,
    owner: usize,
    rows: &mut OwnedRows,
    #[cfg(test)] mut timings: Option<&mut NativePhaseTimings>,
) -> Result<(), String> {
    // Header constraints remain active in physical padding slots. Their
    // native assignment is the tip and its actual predecessor, as in the
    // existing small historical-prefix witness; adjacency ends at N.
    let height = (owner + 1).min(input.header_count());
    let header = input.header(height)?;
    let previous = if height == 1 {
        None
    } else {
        Some(input.header(height - 1)?)
    };
    let fields = native_timed!(
        timings,
        header_fields_ns,
        crate::serializer::Fields::from_header(&header)
    )?;
    let mut joined = native_timed!(
        timings,
        header_boundary_ns,
        crate::daa_history_layout::full_header_boundary(Some(&fields))
    )?;
    native_timed!(
        timings,
        header_order_ns,
        crate::header_compact_links::assign_order(
            &mut joined,
            &fields,
            previous.as_ref().map_or(0, |h| h.height),
            previous.as_ref().map_or(0, |h| h.timestamp),
            height == 1,
        )
    )?;
    let native = joined
        .base
        .base
        .base
        .input
        .as_ref()
        .ok_or("header native witness absent")?;
    if native.len() != WIDTH {
        return Err("header native witness width".into());
    }
    native_timed!(timings, header_claims_ns, {
        let mask = if let Some(adapter) = max_adapter {
            adapter.check_parent(plan)?;
            adapter.physical_assignment_replacement_mask(owner)?
        } else { plan.physical_assignment_replacement_mask(owner as u64)? };
        #[cfg(test)]
        let mask = legacy_header_mask(plan, input, owner, max_adapter, legacy_adapter, mask)?;
        for (wire, &value) in native.iter().enumerate() {
            if !mask[wire] && !BANKS.iter().any(|&(lo, hi)| (lo..hi).contains(&wire)) {
                rows.claim(owner, wire, value)?;
            }
        }
    });
    Ok(())
}

fn seed_header_from_template(
    template: &crate::daa_history_layout::HeaderAssignmentTemplate,
    plan: &WorkTreeHistoryPlan,
    max_adapter: Option<&crate::max_header_adapter::MaxHeaderAdapter<'_>>,
    #[cfg(test)] legacy_adapter: Option<&crate::legacy_native_adapter::LegacyNativeAdapter<'_>>,
    input: &NativePrefix,
    owner: usize,
    rows: &mut OwnedRows,
    #[cfg(test)] mut timings: Option<&mut NativePhaseTimings>,
    cap0: Option<&NativeCap0Source>,
    cap1: Option<&NativeCap1Source>,
    reserve_eligible08: bool,
    scored_source: Option<&ScoredOwnerPackingView>,
    map_source: Option<&MapPhysicalSource<'_>>,
    scheduled_max_source: Option<&NativeScheduledMaxSource<'_, '_>>,
) -> Result<(), String> {
    let height = (owner + 1).min(input.header_count());
    let header = input.header(height)?;
    let previous = if height == 1 { None } else { Some(input.header(height - 1)?) };
    let fields = native_timed!(
        timings, header_fields_ns, crate::serializer::Fields::from_header(&header)
    )?;
    let mut native = native_timed!(timings, header_boundary_ns, template.assign(&fields))?;
    native_timed!(
        timings,
        header_order_ns,
        template.assign_order(
            &mut native,
            &fields,
            previous.as_ref().map_or(0, |h| h.height),
            previous.as_ref().map_or(0, |h| h.timestamp),
            height == 1,
        )
    )?;
    if native.len() != WIDTH { return Err("header native witness width".into()); }
    native_timed!(timings, header_claims_ns, {
        let mask = if let Some(adapter) = max_adapter {
            adapter.check_parent(plan)?;
            adapter.physical_assignment_replacement_mask(owner)?
        } else { plan.physical_assignment_replacement_mask(owner as u64)? };
        #[cfg(test)]
        let mask = legacy_header_mask(plan, input, owner, max_adapter, legacy_adapter, mask)?;
        if let Some(source) = scheduled_max_source {
            if source.class.owner != owner || max_adapter.is_some()
                || cap0.is_some() || cap1.is_some() || reserve_eligible08
                || scored_source.is_some() || map_source.is_some()
                || source.binding != HeaderSourceBinding::for_plan(plan, owner)? {
                return Err("C512c isolated scheduled MAX HEADER reservation".into());
            }
            #[cfg(test)]
            if legacy_adapter.is_some() {
                return Err("C512c scheduled MAX rejects legacy HEADER adapter".into());
            }
            source.stream.closed_native_snapshot(plan, input)?;
            c512c_require_header_max_reservation(owner, &source.cells, &native, &mask)?;
        }
        if let Some(cap0) = cap0 {
            let binding = HeaderSourceBinding::for_plan(plan, owner)?;
            cap0.require_header_reservation(owner, &binding, &mask)?;
        }
        if let Some(cap1) = cap1 {
            let binding = HeaderSourceBinding::for_plan(plan, owner)?;
            cap1.require_header_reservation(owner, &binding, &mask)?;
        }
        let bank53_end = BANK53_BASE + BANK53_CONTEXTS * BANK53_CONTEXT_BITS;
        if reserve_eligible08 {
            if owner != FIRST_MODERN_CAP0_OWNER || max_adapter.is_some()
                || cap0.is_none() || cap1.is_none() || bank53_end > WIDTH
                || mask[BANK53_BASE..bank53_end].iter().any(|replaced| *replaced) {
                return Err("C373 both Bank53 contexts require ordinary HEADER ownership".into());
            }
            #[cfg(test)]
            if legacy_adapter.is_some() {
                return Err("C373 Bank53 reservation rejects legacy HEADER".into());
            }
        }
        let map_pair_reserved = if let Some(source) = map_source {
            if reserve_eligible08 || scored_source.is_some() || cap0.is_some()
                || cap1.is_some() || max_adapter.is_some()
                || rows.selection.count() != 1
                || rows.selection.first_owner() != owner
            {
                return Err("C438 Map pair requires isolated ordinary HEADER owner".into());
            }
            #[cfg(test)]
            if legacy_adapter.is_some() {
                return Err("C438 Map pair rejects legacy HEADER".into());
            }
            let binding = HeaderSourceBinding::for_plan(plan, owner)?;
            if binding.profile() != input.profile() {
                return Err("C438 Map pair HEADER profile drift".into());
            }
            let class = rows.selection.terminal_class();
            Some(match source {
                MapPhysicalSource::Pair(lease) => preflight_map_pair_reservation(
                    lease, &binding, owner, class, &mask,
                )?,
                MapPhysicalSource::PairSlack(bundle) => preflight_map_slack_reservation(
                    bundle, &binding, owner, class, &mask, &native,
                )?,
                MapPhysicalSource::PairSlackAnchor(bundle) =>
                    preflight_map_slack_anchor_reservation(
                        *bundle, &binding, owner, class, &mask,
                    )?,
                MapPhysicalSource::PairSlackSecondAnchor(bundle, first) => {
                    bundle.checked_predecessor_packed(first)?;
                    preflight_map_slack_anchor_reservation(
                        *bundle, &binding, owner, class, &mask,
                    )?
                }
            })
        } else { None };
        if rows.mixed_map_header_capture.is_some() {
            preflight_mixed_map_header_seed(owner, rows.selection.terminal_class(), &mask, &native,
                map_pair_reserved.as_deref()
                    .ok_or("C503 mixed Map reservation missing before HEADER seed")?)?;
        }
        let scored_reserved = if let Some(source) = scored_source {
            let schedule = h21_eligible_context::Eligible08RegularScoreOwner::classify(owner)?;
            let owner_class = rows.selection.terminal_class();
            if reserve_eligible08 || cap0.is_some() || cap1.is_some()
                || owner_class != crate::daa_history_roster::OwnerClass::Carry
                || rows.selection.count() != 1
                || rows.selection.first_owner() != owner
                || max_adapter.is_some() {
                return Err("C396 source requires isolated ordinary HEADER reservation".into());
            }
            let binding = HeaderSourceBinding::for_plan(plan, owner)?;
            scored_owner_source_local(source, owner, &binding)?;
            for context in 0..2 {
                if !schedule.active()[context] {
                    let inactive_score = H21EligibleMapStage::score_live(context)?;
                    if mask[inactive_score.clone()].iter().any(|replaced| *replaced)
                        || native[inactive_score].iter().any(|value| *value != Fr::zero()) {
                        return Err("C396 inactive Score must remain HEADER zero".into());
                    }
                }
            }
            for cell in source.cells() {
                if mask[cell.wire() % WIDTH] {
                    return Err("C396 source domain is not HEADER-owned".into());
                }
            }
            let mut reserved = vec![false; WIDTH];
            for cell in source.cells() { reserved[cell.wire() % WIDTH] = true; }
            if reserved.iter().filter(|reserved| **reserved).count()
                != schedule.typed_cell_count() {
                return Err("C396 exact scored-source HEADER reservation census".into());
            }
            Some(reserved)
        } else { None };
        if rows.c498_clipped_score_capture.is_some() {
            rows.prepare_c498_and_c496_seed(owner, &mask,
                map_pair_reserved.as_deref().ok_or("C498 exact Map reservation absent")?,
                &native, &BANKS)?;
        }
        else if rows.c496_clipped_header_zero_capture.is_some() {
            rows.prepare_c496_clipped_header_zero_seed(owner, &mask,
                map_pair_reserved.as_deref().ok_or("C496 exact Map reservation absent")?,
                &native, &BANKS)?;
        }
        let carry_header_census = owner == MATURE_EIP_SOURCE_OWNER + 1
            && !reserve_eligible08 && max_adapter.is_none()
            && cap0.is_none() && cap1.is_none();
        #[cfg(test)]
        let carry_header_census = carry_header_census && legacy_adapter.is_none();
        if rows.author_census.is_some() && !carry_header_census {
            let point = crate::segment_points::POINT_OFFSET
                ..crate::segment_points::POINT_OFFSET + crate::point_membership::POINT_WIDTH;
            if owner != POINT_MEMBERSHIP_OWNER || !reserve_eligible08
                || mask[point].iter().any(|replaced| *replaced)
            {
                return Err("C374 Point bank must be ordinary HEADER before reservation".into());
            }
        }
        for (wire, &value) in native.iter().enumerate() {
            if !mask[wire] && !BANKS.iter().any(|&(lo, hi)| (lo..hi).contains(&wire)) {
                if rows.author_census.is_some() && !carry_header_census
                    && (crate::segment_points::POINT_OFFSET
                        ..crate::segment_points::POINT_OFFSET + crate::point_membership::POINT_WIDTH)
                        .contains(&wire)
                {
                    continue;
                }
                if reserve_eligible08 && (BANK53_BASE..bank53_end).contains(&wire) {
                    continue;
                }
                if map_pair_reserved.as_ref().is_some_and(|reserved| reserved[wire]) {
                    continue;
                }
                if scored_reserved.as_ref().is_some_and(|reserved| reserved[wire]) {
                    continue;
                }
                if rows.c498_clipped_score_capture.as_ref()
                    .is_some_and(|capture| capture.index(wire).is_some()) {
                    continue;
                }
                if cap0.is_some_and(|source| source.reserves_header_local_wire(owner, wire))
                    || cap1.is_some_and(|source| source.reserves_header_local_wire(owner, wire)) {
                    continue;
                }
                if scheduled_max_source.is_some_and(|source| source.class.reserves(wire)) {
                    continue;
                }
                rows.claim_header_seed(owner, wire, value)?;
            }
        }
    });
    Ok(())
}

/// Reserve one Bank53 Map context from the code-owned Map assignment while
/// preserving the parent plan's full two-context HEADER ownership mask.
fn seed_header_from_template_bank53_map(
    template: &crate::daa_history_layout::HeaderAssignmentTemplate,
    plan: &WorkTreeHistoryPlan,
    input: &NativePrefix,
    owner: usize,
    context: usize,
    rows: &mut OwnedRows,
) -> Result<(), String> {
    if context >= BANK53_CONTEXTS {
        return Err("bank53 Map context outside two-context lane".into());
    }
    let small = matches!(plan.headers(), 3 | 4) && plan.slot_log() == 2 && plan.slots() == 4;
    let first_anchor = plan.headers() == 1984 && plan.slot_log() == 11 && plan.slots() == 2048;
    if !small && !first_anchor {
        return Err("bank53 Map writer requires an admitted N3/N4/N1984 plan".into());
    }
    if owner >= plan.slots() as usize
        || rows.selection.owners().len() != 1
        || !rows.selection.owners().contains(&owner)
    {
        return Err("bank53 Map writer owner/selection mismatch".into());
    }

    let parent_mask = plan.physical_assignment_replacement_mask(owner as u64)?;
    let bank_start = BANK53_BASE + context * BANK53_CONTEXT_BITS;
    let bank_end = bank_start + BANK53_CONTEXT_BITS;
    let both_banks_end = BANK53_BASE + BANK53_CONTEXTS * BANK53_CONTEXT_BITS;
    if bank_end > WIDTH || parent_mask.len() != WIDTH
        || both_banks_end > WIDTH
        || parent_mask[BANK53_BASE..both_banks_end].iter().any(|replaced| *replaced)
    {
        return Err("bank53 Map contexts are not wholly HEADER-owned in parent mask".into());
    }
    let mut reserved_mask = parent_mask.clone();
    reserved_mask[bank_start..bank_end].fill(true);
    for wire in 0..WIDTH {
        if reserved_mask[wire] != (parent_mask[wire] || (bank_start..bank_end).contains(&wire)) {
            return Err("bank53 Map reservation changed coordinates outside its context".into());
        }
    }

    let height = (owner + 1).min(input.header_count());
    let header = input.header(height)?;
    let previous = if height == 1 { None } else { Some(input.header(height - 1)?) };
    let fields = crate::serializer::Fields::from_header(&header)?;
    let mut native = template.assign(&fields)?;
    template.assign_order(
        &mut native,
        &fields,
        previous.as_ref().map_or(0, |h| h.height),
        previous.as_ref().map_or(0, |h| h.timestamp),
        height == 1,
    )?;
    if native.len() != WIDTH {
        return Err("bank53 Map HEADER assignment width".into());
    }
    for (wire, &value) in native.iter().enumerate() {
        if !reserved_mask[wire] && !BANKS.iter().any(|&(lo, hi)| (lo..hi).contains(&wire)) {
            rows.claim(owner, wire, value)?;
        }
    }
    Ok(())
}

/// Test-only H21 counterpart to the bounded production seed above. It repeats
/// the parent-mask/lane reservation checks, then seeds the exact native HEADER
/// assignment around one selected Bank53 context.
#[cfg(test)]
fn seed_header_from_template_bank53_map_h21_for_test(
    template: &crate::daa_history_layout::HeaderAssignmentTemplate,
    plan: &WorkTreeHistoryPlan,
    input: &NativePrefix,
    owner: usize,
    context: usize,
    rows: &mut OwnedRows,
) -> Result<(), String> {
    validate_h21_bank53_map_lane_for_test(plan, owner, context)?;
    if rows.selection.owners().len() != 1 || !rows.selection.owners().contains(&owner) {
        return Err("H21 Bank53 test owner/selection mismatch".into());
    }
    let parent_mask = plan.physical_assignment_replacement_mask(owner as u64)?;
    let bank_start = BANK53_BASE + context * BANK53_CONTEXT_BITS;
    let bank_end = bank_start + BANK53_CONTEXT_BITS;
    let both_banks_end = BANK53_BASE + BANK53_CONTEXTS * BANK53_CONTEXT_BITS;
    if parent_mask.len() != WIDTH || bank_end > WIDTH || both_banks_end > WIDTH
        || parent_mask[BANK53_BASE..both_banks_end].iter().any(|replaced| *replaced)
    {
        return Err("H21 Bank53 test lane is not wholly HEADER-owned in parent mask".into());
    }
    let mut reserved_mask = parent_mask.clone();
    reserved_mask[bank_start..bank_end].fill(true);
    for wire in 0..WIDTH {
        if reserved_mask[wire] != (parent_mask[wire] || (bank_start..bank_end).contains(&wire)) {
            return Err("H21 Bank53 test reservation changed coordinates outside its context".into());
        }
    }

    let height = (owner + 1).min(input.header_count());
    let header = input.header(height)?;
    let previous = if height == 1 { None } else { Some(input.header(height - 1)?) };
    let fields = crate::serializer::Fields::from_header(&header)?;
    let mut native = template.assign(&fields)?;
    template.assign_order(
        &mut native,
        &fields,
        previous.as_ref().map_or(0, |h| h.height),
        previous.as_ref().map_or(0, |h| h.timestamp),
        height == 1,
    )?;
    if native.len() != WIDTH {
        return Err("H21 Bank53 test HEADER assignment width".into());
    }
    for (wire, &value) in native.iter().enumerate() {
        if !reserved_mask[wire] && !BANKS.iter().any(|&(lo, hi)| (lo..hi).contains(&wire)) {
            rows.claim(owner, wire, value)?;
        }
    }
    Ok(())
}

#[cfg(test)]
fn seed_header_from_template_bank53_for_test(
    template: &crate::daa_history_layout::HeaderAssignmentTemplate,
    plan: &WorkTreeHistoryPlan,
    input: &NativePrefix,
    owner: usize,
    context: usize,
    rows: &mut OwnedRows,
) -> Result<(), String> {
    if context >= BANK53_TEST_CONTEXTS {
        return Err("bank53 test context outside two-context lane".into());
    }
    let small = matches!(plan.headers(), 3 | 4) && plan.slot_log() == 2 && plan.slots() == 4;
    let first_anchor = plan.headers() == 1984 && plan.slot_log() == 11 && plan.slots() == 2048;
    if !small && !first_anchor {
        return Err("bank53 test writer requires an admitted N3/N4/N1984 native plan".into());
    }
    if owner >= plan.slots()
        || rows.selection.owners().len() != 1
        || !rows.selection.owners().contains(&owner)
    {
        return Err("bank53 test writer owner/selection mismatch".into());
    }

    // The parent plan owns the complete existing mask. Confirm its chosen
    // owner and preserve every bit exactly, except the selected B context.
    let parent_mask = plan.physical_assignment_replacement_mask(owner as u64)?;
    let bank_start = BANK53_TEST_BASE + context * BANK53_TEST_CONTEXT_BITS;
    let bank_end = bank_start + BANK53_TEST_CONTEXT_BITS;
    if bank_end > WIDTH || parent_mask.len() != WIDTH
        || parent_mask[BANK53_TEST_BASE..BANK53_TEST_BASE +
            BANK53_TEST_CONTEXTS * BANK53_TEST_CONTEXT_BITS]
            .iter().any(|replaced| *replaced)
    {
        return Err("bank53 test lane is not wholly HEADER-owned in parent mask".into());
    }
    let mut reserved_mask = parent_mask.clone();
    reserved_mask[bank_start..bank_end].fill(true);
    for wire in 0..WIDTH {
        let expected = parent_mask[wire] || (bank_start..bank_end).contains(&wire);
        if reserved_mask[wire] != expected {
            return Err("bank53 reservation changed coordinates outside its context".into());
        }
    }

    let height = (owner + 1).min(input.header_count());
    let header = input.header(height)?;
    let previous = if height == 1 { None } else { Some(input.header(height - 1)?) };
    let fields = crate::serializer::Fields::from_header(&header)?;
    let mut native = template.assign(&fields)?;
    template.assign_order(
        &mut native,
        &fields,
        previous.as_ref().map_or(0, |h| h.height),
        previous.as_ref().map_or(0, |h| h.timestamp),
        height == 1,
    )?;
    if native.len() != WIDTH {
        return Err("bank53 test HEADER assignment width".into());
    }
    for (wire, &value) in native.iter().enumerate() {
        if !reserved_mask[wire] && !BANKS.iter().any(|&(lo, hi)| (lo..hi).contains(&wire)) {
            rows.claim(owner, wire, value)?;
        }
    }
    Ok(())
}

/// Explicit test input for the bank53 physical writer. The type and all entry
/// points are cfg(test); its bits are ownership fixtures, never source claims.
#[cfg(test)]
pub(crate) struct Bank53TestWitness {
    owner: usize,
    context: usize,
    values: Vec<Fr>,
}

#[cfg(test)]
impl Bank53TestWitness {
    pub(crate) fn new(owner: usize, context: usize, values: Vec<Fr>) -> Self {
        Self { owner, context, values }
    }
}

#[cfg(test)]
fn write_bank53_witness_for_test(
    rows: &mut OwnedRows,
    owner: usize,
    reserved_context: usize,
    witness: &Bank53TestWitness,
) -> Result<(), String> {
    if reserved_context >= BANK53_TEST_CONTEXTS || witness.context != reserved_context {
        return Err("bank53 test witness context mismatch".into());
    }
    if witness.owner != owner {
        return Err("bank53 test witness owner mismatch".into());
    }
    if witness.values.len() != BANK53_TEST_CONTEXT_BITS {
        return Err("bank53 test witness length mismatch".into());
    }
    if witness.values[BANK53_TEST_LIVE_BITS..].iter().any(|value| !value.is_zero()) {
        return Err("bank53 test Score padding/slack must be zero".into());
    }
    if !rows.selection.owners().contains(&owner) {
        return Err("bank53 test witness owner outside selected row".into());
    }
    let start = BANK53_TEST_BASE + reserved_context * BANK53_TEST_CONTEXT_BITS;
    for (offset, &value) in witness.values.iter().enumerate() {
        let wire = start + offset;
        if value != Fr::zero() && value != Fr::one() {
            return Err(format!("bank53 test witness is non-Boolean at bit{offset}"));
        }
        let (row, local_wire) = rows.local(owner, wire)?;
        // Validate the complete claim set before the first write. OwnedRows
        // permits an identical duplicate; this adapter requires exclusive
        // ownership, including for same-value claims.
        if rows.claimed[row][local_wire] {
            return Err(format!("bank53 test witness bit already claimed at {wire}"));
        }
    }
    for (offset, &value) in witness.values.iter().enumerate() {
        let wire = start + offset;
        let (row, local_wire) = rows.local(owner, wire)?;
        if rows.claimed[row][local_wire] {
            return Err(format!("bank53 test witness bit already claimed at {wire}"));
        }
        rows.claim(owner, wire, value)?;
    }
    let row = owner - rows.selection.first_owner();
    if (start..start + BANK53_TEST_CONTEXT_BITS).any(|wire| !rows.claimed[row][wire]) {
        return Err("bank53 test witness is incomplete".into());
    }
    Ok(())
}

#[cfg(test)]
fn legacy_header_mask(
    plan: &WorkTreeHistoryPlan, input: &NativePrefix, owner: usize,
    max_adapter: Option<&crate::max_header_adapter::MaxHeaderAdapter<'_>>,
    legacy_adapter: Option<&crate::legacy_native_adapter::LegacyNativeAdapter<'_>>,
    mask: Vec<bool>,
) -> Result<Vec<bool>, String> {
    if let Some(adapter) = legacy_adapter {
        if max_adapter.is_some() { return Err("legacy native MAX mixing".into()); }
        adapter.check(plan, input)?;
        adapter.extend_mask(owner, mask)
    } else { Ok(mask) }
}

fn seed_tree(
    plan: &WorkTreeHistoryPlan,
    input: &NativePrefix,
    owner: usize,
    rows: &mut OwnedRows,
    fault: AssemblyFault,
) -> Result<(), String> {
    let engine = fixed::engine()?;
    let e = &engine.base.endpoints;
    let genuine = plan.leaf_profile().role(owner)? == leaf::Role::Genuine;
    let assigned = if genuine {
        let height = owner + 2;
        let (lower, upper) = input.interval(height)?;
        leaf::assign_header_leaf(
            engine,
            plan.leaf_boundary(),
            owner,
            &input.header(height)?,
            lower,
            upper,
            input.profile,
        )?
    } else {
        leaf::assign_inactive_leaf(engine, plan.leaf_boundary(), owner, input.profile)?
    };
    let mut domain = Vec::new();
    for base in leaf::CORES {
        domain.extend(base..base + layout::CORE);
    }
    domain.extend(leaf::AUX..leaf::AUX + leaf::AUX_BITS);
    for wires in [
        &e.raw, &e.length, &e.height, &e.lower, &e.upper, &e.leaf, &e.profile,
    ] {
        domain.extend(wires);
    }
    rows.native(owner, &assigned.values, &domain)?;
    let role = plan.fixed_profile().role(owner)?;
    let bytes = if let fixed::Role::Node { level, position } = role {
        let level = level as usize;
        let position = position as usize;
        let base = if level == 1 {
            0
        } else {
            plan.descriptor().level(level - 1)?.0
        };
        let child = |slot| {
            if level == 1 {
                input.leaf_digest(slot)
            } else {
                input.node_digest(slot)
            }
        };
        let mut children = [child(base + 2 * position)?, child(base + 2 * position + 1)?];
        #[cfg(test)]
        if let AssemblyFault::FixedChildBit {
            owner: target,
            branch,
            bit,
        } = fault
        {
            if target == owner as u64 {
                if branch >= 2 || bit >= 256 {
                    return Err("fixed child fault domain".into());
                }
                children[branch][bit / 8] ^= 1 << (bit % 8);
            }
        }
        #[cfg(not(test))]
        let _ = fault;
        let mut bytes = vec![b'N', level as u8];
        bytes.extend_from_slice(&(position as u32).to_be_bytes());
        bytes.extend_from_slice(&children[0]);
        bytes.extend_from_slice(&children[1]);
        bytes
    } else if role == fixed::Role::Profile {
        let mut bytes = fixed::PROFILE_PREFIX.to_vec();
        bytes.extend_from_slice(&crate::header_order::MAINNET_GENESIS);
        bytes
    } else if role == fixed::Role::Dummy {
        Vec::new()
    } else {
        return Err("native owner source has no admitted fixed Dummy role".into());
    };
    let node = leaf::assign_fixed_slot_native(engine, plan.fixed_profile(), owner, &bytes)?;
    let mut domain: Vec<_> = (fixed::NODE_CORE..fixed::NODE_CORE + layout::CORE).collect();
    for wires in [&e.node_left, &e.node_right, &e.node] {
        domain.extend(wires);
    }
    rows.native(owner, &node.values, &domain)?;
    if genuine {
        let header = input.header(owner + 2)?;
        let (lower, upper) = input.interval(owner + 2)?;
        let difficulty = work::native_decode(header.n_bits)?;
        if difficulty.is_zero() {
            return Err("zero native work".into());
        }
        rows.integer(owner, &e.n_bits, &BigUint::from(header.n_bits))?;
        rows.check_integer_claimed(owner, &e.lower, &BigUint::from_bytes_be(&lower))?;
        rows.check_integer_claimed(owner, &e.upper, &BigUint::from_bytes_be(&upper))?;
        rows.integer(owner, &e.work, &difficulty)?;
        rows.integer(
            owner,
            &e.work_minus_one,
            &(&difficulty - BigUint::from(1u8)),
        )?;
        for (exponent, &wire) in e.exponent.iter().enumerate() {
            rows.claim(
                owner,
                wire,
                Fr::from((exponent == (header.n_bits >> 24) as usize) as u64),
            )?;
        }
    } else {
        for &wire in e
            .n_bits
            .iter()
            .chain(&e.work)
            .chain(&e.work_minus_one)
            .chain(&e.exponent)
        {
            rows.claim(owner, wire, Fr::zero())?;
        }
        rows.check_integer_claimed(owner, &e.lower, &BigUint::from(0u8))?;
        rows.check_integer_claimed(owner, &e.upper, &BigUint::from(0u8))?;
    }
    for wire in layout::ENDPOINT_BASE + e.used..layout::ENDPOINT_BASE + layout::ENDPOINT_WIDTH {
        rows.claim(owner, wire, Fr::zero())?;
    }
    Ok(())
}

/// A pure image of the Tree author, computed from the canonical prefix and
/// admitted plan before any physical row is allocated or written.
struct NativeTreeSourceImage {
    values: Vec<u8>,
    owned: Vec<u8>,
}

struct NativeTreeImageBuilder {
    values: Vec<u8>,
    owned: Vec<u8>,
    mask: Vec<bool>,
}
impl NativeTreeImageBuilder {
    fn new(plan: &WorkTreeHistoryPlan, owner: usize) -> Result<Self, String> {
        let mask = plan.physical_assignment_replacement_mask(owner as u64)?;
        if mask.len() != WIDTH || mask.iter().filter(|bit| **bit).count() != 401_362 {
            return Err("C376 Tree source exact mask/count".into());
        }
        Ok(Self { values: vec![0; OWNER_BYTES], owned: vec![0; OWNER_BYTES], mask })
    }
    fn bit(bits: &[u8], wire: usize) -> bool {
        bits[wire / 8] & (1 << (wire % 8)) != 0
    }
    fn set(bits: &mut [u8], wire: usize) {
        bits[wire / 8] |= 1 << (wire % 8);
    }
    fn put(&mut self, wire: usize, value: bool) -> Result<(), String> {
        if self.mask.get(wire) != Some(&true) {
            return Err(format!("C376 Tree source outside mask wire{wire}"));
        }
        if Self::bit(&self.owned, wire) {
            return Err(format!("C376 Tree source duplicate wire{wire}"));
        }
        Self::set(&mut self.owned, wire);
        if value { Self::set(&mut self.values, wire); }
        Ok(())
    }
    fn assignment(
        &mut self, map: &BTreeMap<usize, Fr>, domain: &[usize],
    ) -> Result<(), String> {
        let allowed: BTreeSet<_> = domain.iter().copied().collect();
        if map.keys().any(|wire| !allowed.contains(wire)) {
            return Err("C376 Tree source assignment outside domain".into());
        }
        for &wire in domain {
            let value = map.get(&wire).copied().unwrap_or_else(Fr::zero);
            if value != Fr::zero() && value != Fr::one() {
                return Err("C376 Tree source nonboolean assignment".into());
            }
            self.put(wire, value == Fr::one())?;
        }
        Ok(())
    }
    fn integer(&mut self, wires: &[usize], value: &BigUint) -> Result<(), String> {
        if value.bits() > wires.len() as u64 {
            return Err("C376 Tree source integer exceeds endpoint".into());
        }
        for (bit, &wire) in wires.iter().enumerate() {
            self.put(wire, value.bit(bit as u64))?;
        }
        Ok(())
    }
    fn check_integer(&self, wires: &[usize], value: &BigUint) -> Result<(), String> {
        if value.bits() > wires.len() as u64 {
            return Err("C376 Tree source repeated integer exceeds endpoint".into());
        }
        for (bit, &wire) in wires.iter().enumerate() {
            if !Self::bit(&self.owned, wire)
                || Self::bit(&self.values, wire) != value.bit(bit as u64)
            {
                return Err(format!("C376 Tree source repeated endpoint wire{wire}"));
            }
        }
        Ok(())
    }
    fn finish(self) -> Result<NativeTreeSourceImage, String> {
        for (wire, &expected) in self.mask.iter().enumerate() {
            if Self::bit(&self.owned, wire) != expected {
                return Err(format!("C376 Tree source incomplete mask wire{wire}"));
            }
        }
        if (989_658..989_730).any(|wire| Self::bit(&self.owned, wire))
            || (989_730..991_232).any(|wire| {
                !Self::bit(&self.owned, wire) || Self::bit(&self.values, wire)
            })
        {
            return Err("C376 Tree source protected HEADER or nonzero pad".into());
        }
        Ok(NativeTreeSourceImage { values: self.values, owned: self.owned })
    }
}

fn tree_source_image(
    plan: &WorkTreeHistoryPlan, input: &NativePrefix, owner: usize,
) -> Result<NativeTreeSourceImage, String> {
    let engine = fixed::engine()?;
    let e = &engine.base.endpoints;
    let mut image = NativeTreeImageBuilder::new(plan, owner)?;
    let genuine = plan.leaf_profile().role(owner)? == leaf::Role::Genuine;
    let leaf_assignment = if genuine {
        let height = owner + 2;
        let (lower, upper) = input.interval(height)?;
        leaf::assign_header_leaf(
            engine, plan.leaf_boundary(), owner, &input.header(height)?,
            lower, upper, input.profile,
        )?
    } else {
        leaf::assign_inactive_leaf(engine, plan.leaf_boundary(), owner, input.profile)?
    };
    let mut leaf_domain = Vec::new();
    for base in leaf::CORES {
        leaf_domain.extend(base..base + layout::CORE);
    }
    leaf_domain.extend(leaf::AUX..leaf::AUX + leaf::AUX_BITS);
    for wires in [&e.raw, &e.length, &e.height, &e.lower, &e.upper, &e.leaf, &e.profile] {
        leaf_domain.extend(wires);
    }
    image.assignment(&leaf_assignment.values, &leaf_domain)?;

    let role = plan.fixed_profile().role(owner)?;
    let preimage = if let fixed::Role::Node { level, position } = role {
        let level = level as usize;
        let position = position as usize;
        let base = if level == 1 { 0 } else { plan.descriptor().level(level - 1)?.0 };
        let child = |slot| {
            if level == 1 { input.leaf_digest(slot) } else { input.node_digest(slot) }
        };
        let left = child(base + 2 * position)?;
        let right = child(base + 2 * position + 1)?;
        let mut bytes = vec![b'N', level as u8];
        bytes.extend_from_slice(&(position as u32).to_be_bytes());
        bytes.extend_from_slice(&left);
        bytes.extend_from_slice(&right);
        bytes
    } else if role == fixed::Role::Profile {
        let mut bytes = fixed::PROFILE_PREFIX.to_vec();
        bytes.extend_from_slice(&crate::header_order::MAINNET_GENESIS);
        bytes
    } else if role == fixed::Role::Dummy {
        Vec::new()
    } else {
        return Err("C376 Tree source fixed role outside admitted domain".into());
    };
    let node_assignment =
        leaf::assign_fixed_slot_native(engine, plan.fixed_profile(), owner, &preimage)?;
    let mut node_domain: Vec<_> = (fixed::NODE_CORE..fixed::NODE_CORE + layout::CORE).collect();
    for wires in [&e.node_left, &e.node_right, &e.node] { node_domain.extend(wires); }
    image.assignment(&node_assignment.values, &node_domain)?;

    if genuine {
        let header = input.header(owner + 2)?;
        let (lower, upper) = input.interval(owner + 2)?;
        let difficulty = work::native_decode(header.n_bits)?;
        if difficulty.is_zero() { return Err("C376 Tree source zero native work".into()); }
        image.integer(&e.n_bits, &BigUint::from(header.n_bits))?;
        image.check_integer(&e.lower, &BigUint::from_bytes_be(&lower))?;
        image.check_integer(&e.upper, &BigUint::from_bytes_be(&upper))?;
        image.integer(&e.work, &difficulty)?;
        image.integer(&e.work_minus_one, &(&difficulty - BigUint::from(1u8)))?;
        for (exponent, &wire) in e.exponent.iter().enumerate() {
            image.put(wire, exponent == (header.n_bits >> 24) as usize)?;
        }
    } else {
        for &wire in e.n_bits.iter().chain(&e.work).chain(&e.work_minus_one).chain(&e.exponent) {
            image.put(wire, false)?;
        }
        image.check_integer(&e.lower, &BigUint::from(0u8))?;
        image.check_integer(&e.upper, &BigUint::from(0u8))?;
    }
    for wire in layout::ENDPOINT_BASE + e.used..layout::ENDPOINT_BASE + layout::ENDPOINT_WIDTH {
        image.put(wire, false)?;
    }
    image.finish()
}

struct Group {
    name: String,
    terms: Vec<Term>,
}
fn local_groups(
    plan: &WorkTreeHistoryPlan,
    roster: &DaaHistoryRoster<'_>,
    selection: OwnerSelection,
    max_adapter: Option<&crate::max_header_adapter::MaxHeaderAdapter<'_>>,
) -> Result<Vec<Group>, String> {
    let engine = fixed::engine()?;
    let mut out = Vec::new();
    for owner in selection.owners() {
        let mut terms = Vec::new();
        if let Some(adapter) = max_adapter {
            adapter.check_parent(plan)?;
            adapter.visit_header_terms(owner, |t| { terms.push(t); Ok(()) })?;
        } else {
            roster.visit_header_terms(owner as u64, |t| { terms.push(t); Ok(()) })?;
        }
        out.push(Group {
            name: format!("Header/{owner}"),
            terms,
        });
        let mut terms = Vec::new();
        roster.visit_owner_terms(owner as u64, |t| {
            terms.push(t);
            Ok(())
        })?;
        out.push(Group {
            name: format!("DAA/{owner}"),
            terms,
        });
        let mut terms = Vec::new();
        leaf::Boundary::emit_slot(plan.leaf_boundary(), owner, |t| terms.push(t))?;
        out.push(Group {
            name: format!("Leaf/{owner}"),
            terms,
        });
        let mut terms = Vec::new();
        fixed::emit_slot(engine, plan.fixed_profile(), owner, |t| terms.push(t))?;
        out.push(Group {
            name: format!("Fixed/{owner}"),
            terms,
        });
        let mut terms = Vec::new();
        plan.work_boundary().emit_slot(owner, |t| terms.push(t))?;
        out.push(Group {
            name: format!("Work/{owner}"),
            terms,
        });
        if let Some(adapter) = max_adapter {
            let mut terms = Vec::new();
            adapter.max().emit_owner(owner, |t| { terms.push(t); Ok(()) })?;
            out.push(Group { name: format!("MAX/{owner}"), terms });
        }
    }
    Ok(out)
}

fn groups(
    plan: &WorkTreeHistoryPlan,
    roster: &DaaHistoryRoster<'_>,
    selection: OwnerSelection,
) -> Result<Vec<Group>, String> {
    let mut out = local_groups(plan, roster, selection, None)?;
    for (kind, families) in [
        ("Topology", plan.topology().families.as_slice()),
        ("WorkLink", plan.work_boundary().links().as_slice()),
    ] {
        for family in families {
            let mut rows = BTreeMap::<usize, Term>::new();
            for owner in selection.owners() {
                for left in [true, false] {
                    family.emit_endpoint_terms(plan.descriptor(), left, owner, |_, _, term| {
                        if let Some(previous) = rows.get(&term.row) {
                            if previous != &term {
                                return Err("incident duplicate row differs".into());
                            }
                        } else {
                            rows.insert(term.row, term);
                        }
                        Ok(())
                    })?;
                }
            }
            out.push(Group {
                name: format!("{kind}/{}", family.name),
                terms: rows.into_values().collect(),
            });
        }
    }
    Ok(out)
}

/// Test-only endpoint stream for the non-local topology families.
///
/// The native owner assembler still has no global proof witness.  This hook
/// exposes only the topology/work-link producer in the same `EdgeTerm`
/// shape consumed by the bounded edge streamer.  Its family geometry is
/// derived from the reviewed family counts; Header/DAA/Leaf/Fixed families
/// remain on their existing owner-local path until their row normalization is
/// specified separately.
#[cfg(test)]
pub(crate) fn visit_m2_nonlocal_edge_endpoint(
    plan: &WorkTreeHistoryPlan,
    left: bool,
    slot: usize,
    sink: &mut dyn FnMut(EdgeTerm) -> Result<(), String>,
) -> Result<(), String> {
    let (slot_bits, base_row_bits, family_bits, member_row_bits) = m2_nonlocal_edge_geometry(plan)?;
    let slots = 1usize
        .checked_shl(slot_bits as u32)
        .ok_or("M2 edge slot width overflow")?;
    if slot >= slots {
        return Err("M2 edge endpoint slot outside declared domain".into());
    }
    let mut family_index = 0usize;
    let mut visit_family = |family: &crate::work_tree_wiring::Family| -> Result<(), String> {
        let index = family_index;
        let local_bits = member_row_bits
            .get(index)
            .copied()
            .ok_or("M2 edge family index outside geometry")?;
        family.emit_endpoint_terms(
            plan.descriptor(),
            left,
            slot,
            |source_slot, local_row, term| {
                if local_row
                    >= 1usize
                        .checked_shl(local_bits as u32)
                        .ok_or("M2 edge local row overflow")?
                {
                    return Err("M2 edge local row outside declared member".into());
                }
                let family_row = index
                    .checked_shl(base_row_bits as u32)
                    .and_then(|prefix| prefix.checked_add(local_row))
                    .ok_or("M2 edge family row overflow")?;
                sink(EdgeTerm {
                    source_slot,
                    family_row,
                    term,
                })
            },
        )?;
        family_index = family_index
            .checked_add(1)
            .ok_or("M2 edge family index overflow")?;
        Ok(())
    };
    for family in &plan.topology().families {
        visit_family(family)?;
    }
    for family in plan.work_boundary().links() {
        visit_family(family)?;
    }
    if family_index != member_row_bits.len() {
        return Err("M2 edge family geometry traversal drift".into());
    }
    if family_index
        > 1usize
            .checked_shl(family_bits as u32)
            .ok_or("M2 edge family tag overflow")?
    {
        return Err("M2 edge family tag domain overflow".into());
    }
    Ok(())
}

#[cfg(test)]
pub(crate) fn m2_nonlocal_edge_geometry(
    plan: &WorkTreeHistoryPlan,
) -> Result<(usize, usize, usize, Vec<usize>), String> {
    if plan.headers() != 3073 || plan.slot_log() != 12 || plan.slots() != 4096 {
        return Err("M2 nonlocal edge stream requires N3073/S12".into());
    }
    let slot_bits = plan.slot_log();
    let mut member_row_bits = Vec::new();
    for family in plan
        .topology()
        .families
        .iter()
        .chain(plan.work_boundary().links().iter())
    {
        let row_log = family.count(plan.descriptor())?.row_log;
        let local_bits = row_log
            .checked_sub(slot_bits)
            .ok_or("M2 edge family row width below slot width")?;
        member_row_bits.push(local_bits);
    }
    let base_row_bits = member_row_bits
        .iter()
        .copied()
        .max()
        .ok_or("M2 edge family geometry is empty")?;
    let family_bits = member_row_bits
        .len()
        .checked_next_power_of_two()
        .ok_or("M2 edge family count overflow")?
        .trailing_zeros() as usize;
    if family_bits >= usize::BITS as usize {
        return Err("M2 edge family tag width overflow".into());
    }
    Ok((slot_bits, base_row_bits, family_bits, member_row_bits))
}

fn reads(term: &Term, mut add: impl FnMut(usize) -> Result<(), String>) -> Result<(), String> {
    if !term.gate.c1.is_zero() || !term.gate.c3.is_zero() {
        add(term.gate.left)?;
    }
    if !term.gate.c2.is_zero() || !term.gate.c3.is_zero() {
        add(term.gate.right)?;
    }
    Ok(())
}
fn add_foreign(
    selection: OwnerSelection,
    input_len: usize,
    support: &mut BTreeSet<usize>,
    index: usize,
) -> Result<(), String> {
    if index >= input_len {
        return Err("consumer read outside admitted namespace".into());
    }
    if !selection.owners().contains(&(index / WIDTH)) {
        support.insert(index);
        if support.len() > selection.external_cap() {
            return Err(format!(
                "foreign census exceeds {}",
                selection.external_cap()
            ));
        }
    }
    Ok(())
}
#[cfg(test)]
pub(crate) fn foreign_census_for_test(
    m1: bool,
    indices: impl IntoIterator<Item = usize>,
) -> Result<BTreeSet<usize>, String> {
    let selection = if m1 {
        OwnerSelection::M1
    } else {
        OwnerSelection::M2
    };
    let mut support = BTreeSet::new();
    for index in indices {
        add_foreign(selection, 4096 * WIDTH, &mut support, index)?;
    }
    Ok(support)
}

/// Returns the exact foreign support generated by the native assembly graph.
///
/// This is deliberately test-only: it lets a bounded producer registry use
/// the consumer's own `groups`/`census` path instead of maintaining a second
/// hand-written list of imported cells. It does not materialize a global
/// witness or expose a production registry.
#[cfg(test)]
pub(crate) fn external_support_for_test(
    plan: &WorkTreeHistoryPlan,
    input: &NativePrefix,
    m1: bool,
) -> Result<BTreeSet<usize>, String> {
    let selection = if m1 {
        OwnerSelection::M1
    } else {
        OwnerSelection::M2
    };
    let roster = DaaHistoryRoster::compile(plan)?;
    let groups = groups(plan, &roster, selection)?;
    census(&groups, plan, input, selection)
}
fn census(
    groups: &[Group],
    plan: &WorkTreeHistoryPlan,
    input: &NativePrefix,
    selection: OwnerSelection,
) -> Result<BTreeSet<usize>, String> {
    let limit = plan
        .slots()
        .checked_mul(WIDTH)
        .ok_or("input width overflow")?;
    let mut support = BTreeSet::new();
    let mut add = |index| add_foreign(selection, limit, &mut support, index);
    for group in groups {
        for term in &group.terms {
            reads(term, &mut add)?;
        }
    }
    // The producer validates RAW ports in addition to the alias equations.
    let layout = crate::serializer::build(None)?.layout.fields;
    let schedule = crate::daa_header_window::for_child_height(selection.child_height())?;
    let mut heights = schedule.sample_heights().to_vec();
    heights.extend([selection.child_height() - 1, selection.child_height()]);
    for height in heights {
        if !input.header_exists(height as usize) {
            return Err(format!("prefix header {} absent", height));
        }
        for &wire in layout
            .timestamp
            .iter()
            .chain(&layout.n_bits)
            .chain(&layout.height)
        {
            add((height as usize - 1) * WIDTH + 524288 + wire)?;
        }
    }
    Ok(support)
}

struct ForeignReader<F> {
    read: F,
    support: BTreeSet<usize>,
    cache: BTreeMap<usize, bool>,
}
impl<F: FnMut(usize) -> Result<bool, String>> ForeignReader<F> {
    fn get(&mut self, rows: &OwnedRows, index: usize) -> Result<Fr, String> {
        let owner = index / WIDTH;
        let wire = index % WIDTH;
        if rows.selection.owners().contains(&owner) {
            return Ok(rows.values[owner - rows.selection.first_owner()][wire]);
        }
        if !self.support.contains(&index) {
            return Err(format!("read outside foreign census at {index}"));
        }
        let value = if let Some(&value) = self.cache.get(&index) {
            value
        } else {
            let value = (self.read)(index)?;
            self.cache.insert(index, value);
            value
        };
        Ok(Fr::from(value as u64))
    }
}

fn check_group<F: FnMut(usize) -> Result<bool, String>>(
    group: &mut Group,
    rows: &OwnedRows,
    reader: &mut ForeignReader<F>,
) -> Result<(), String> {
    group.terms.sort_unstable_by_key(|t| t.row);
    let mut previous = None;
    let mut sum = Fr::zero();
    for term in &group.terms {
        if previous != Some(term.row) {
            if previous.is_some() && !sum.is_zero() {
                return Err(format!("{} residual row{:?}", group.name, previous));
            }
            previous = Some(term.row);
            sum = Fr::zero();
        }
        let g = &term.gate;
        let mut value = g.c0;
        let left = if !g.c1.is_zero() || !g.c3.is_zero() {
            reader.get(rows, g.left)?
        } else {
            Fr::zero()
        };
        let right = if !g.c2.is_zero() || !g.c3.is_zero() {
            reader.get(rows, g.right)?
        } else {
            Fr::zero()
        };
        value += g.c1 * left + g.c2 * right + g.c3 * left * right;
        sum += value;
    }
    if !sum.is_zero() {
        return Err(format!("{} residual row{:?}", group.name, previous));
    }
    Ok(())
}

fn check_cores(rows: &OwnedRows) -> Result<(), String> {
    let engine = fixed::engine()?;
    for row in 0..rows.values.len() {
        for base in layout::CORE_OFFSETS {
            let input = &rows.values[row][base..base + layout::CORE];
            let mut previous = None;
            let mut sum = Fr::zero();
            for term in &engine.core.terms {
                if previous != Some(term.row) {
                    if previous.is_some() && !sum.is_zero() {
                        return Err(format!(
                            "Core owner{} bank{base} row{:?}",
                            rows.selection.first_owner() + row,
                            previous
                        ));
                    }
                    previous = Some(term.row);
                    sum = Fr::zero();
                }
                sum += term.gate.evaluate(input);
            }
            if !sum.is_zero() {
                return Err("Core final residual".into());
            }
        }
    }
    Ok(())
}

/// One complete owner-local native Cap0 assignment. Production does not
/// authenticate this row or the foreign rows under a commitment.
#[derive(Clone,Debug,PartialEq,Eq)]
pub(crate) struct NativeCap0Source {
    binding: HeaderSourceBinding,
    writer: crate::h21_scheduled_max_cap::Writer,
    cells: Vec<(usize,bool)>,
}
impl NativeCap0Source {
    fn from_first_modern_lease(
        plan:&WorkTreeHistoryPlan,input:&NativePrefix,owner:usize,
        snapshot:&crate::h21_scheduled_max_cap::Eligible08NativeSnapshot,
        cap:&crate::h21_scheduled_max_cap::FirstModernCapLease,
    )->Result<Self,String> {
        if owner!=FIRST_MODERN_CAP0_OWNER {
            return Err("Cap0 packed source fixed owner".into());
        }
        validate_native_plan_input(plan,input)?;
        cap.require_exact_native_snapshot(snapshot,plan,input)?;
        let binding=HeaderSourceBinding::for_plan(plan,owner)?;
        if binding.profile!=input.profile() {
            return Err("Cap0 packed source native profile drift".into());
        }
        let writer=crate::h21_scheduled_max_cap::Writer::Cap{context:0,
            origin:owner.checked_add(1).ok_or("Cap0 packed source origin overflow")?};
        let cells=cap.cap_cells(0)?;
        let source=Self{binding,writer,cells};
        source.validate_domain(owner)?;
        Ok(source)
    }

    fn validate_domain(&self,owner:usize)->Result<(),String> {
        let writer=crate::h21_scheduled_max_cap::Writer::Cap{context:0,
            origin:owner.checked_add(1).ok_or("Cap0 packed source origin overflow")?};
        let base=FIRST_MODERN_CAP0_BASE;
        if owner!=FIRST_MODERN_CAP0_OWNER || self.binding.owner!=owner || self.writer!=writer
            || self.cells.len()!=FIRST_MODERN_CAP0_CELLS
            || self.cells.iter().enumerate().any(|(i,(wire,_))|*wire!=base+i) {
            return Err("Cap0 packed source owner/writer/domain mismatch".into());
        }
        Ok(())
    }

    fn require_header_reservation(&self,owner:usize,binding:&HeaderSourceBinding,
        replacement_mask:&[bool])->Result<(),String> {
        self.validate_domain(owner)?;
        let end=FIRST_MODERN_CAP0_BASE.checked_add(FIRST_MODERN_CAP0_CELLS)
            .ok_or("Cap0 HEADER reservation extent overflow")?;
        if &self.binding!=binding || replacement_mask.len()!=WIDTH || end>replacement_mask.len()
            || replacement_mask[FIRST_MODERN_CAP0_BASE..end].iter().any(|replaced|*replaced) {
            return Err("Cap0 source cannot reserve non-HEADER-owned domain".into());
        }
        Ok(())
    }

    fn reserves_header_local_wire(&self,owner:usize,local:usize)->bool {
        owner==FIRST_MODERN_CAP0_OWNER
            && (FIRST_MODERN_CAP0_BASE..FIRST_MODERN_CAP0_BASE+FIRST_MODERN_CAP0_CELLS).contains(&local)
    }

    fn claim_exclusive(&self,owner:usize,rows:&mut OwnedRows)->Result<(),String> {
        self.validate_domain(owner)?;
        for &(local,_) in &self.cells {
            let (row,wire)=rows.local(owner,local)?;
            if rows.claimed[row][wire] {
                return Err(format!("exclusive Cap0 source claim overlaps owner{owner} wire{local}"));
            }
        }
        for &(local,value) in &self.cells {
            rows.claim_exclusive(owner,local,Fr::from(value as u64))?;
        }
        Ok(())
    }

    pub(crate) fn binding(&self)->&HeaderSourceBinding {&self.binding}
    pub(crate) fn writer(&self)->crate::h21_scheduled_max_cap::Writer {self.writer}
    pub(crate) fn cells(&self)->&[(usize,bool)] {&self.cells}

    #[cfg(test)]
    fn synthetic_for_test(binding:HeaderSourceBinding,cells:Vec<(usize,bool)>)->Self {
        Self{binding,writer:crate::h21_scheduled_max_cap::Writer::Cap{
            context:0,origin:FIRST_MODERN_CAP0_OWNER+1},cells}
    }
}

/// The second fixed Cap assignment for the same first-modern owner. It is
/// derived from the same checked lease as Cap0 and occupies a disjoint
/// HEADER-owned range. The packed row remains unauthenticated at this stage.
#[derive(Clone,Debug,PartialEq,Eq)]
pub(crate) struct NativeCap1Source {
    binding: HeaderSourceBinding,
    writer: crate::h21_scheduled_max_cap::Writer,
    cells: Vec<(usize,bool)>,
}
impl NativeCap1Source {
    fn from_first_modern_lease(
        plan:&WorkTreeHistoryPlan,input:&NativePrefix,owner:usize,
        snapshot:&crate::h21_scheduled_max_cap::Eligible08NativeSnapshot,
        cap:&crate::h21_scheduled_max_cap::FirstModernCapLease,
    )->Result<Self,String> {
        if owner!=FIRST_MODERN_CAP0_OWNER {
            return Err("Cap1 packed source fixed owner".into());
        }
        validate_native_plan_input(plan,input)?;
        cap.require_exact_native_snapshot(snapshot,plan,input)?;
        let binding=HeaderSourceBinding::for_plan(plan,owner)?;
        if binding.profile!=input.profile() {
            return Err("Cap1 packed source native profile drift".into());
        }
        let writer=crate::h21_scheduled_max_cap::Writer::Cap{context:1,
            origin:owner.checked_add(1).ok_or("Cap1 packed source origin overflow")?};
        let cells=cap.cap_cells(1)?;
        let source=Self{binding,writer,cells};
        source.validate_domain(owner)?;
        Ok(source)
    }

    fn validate_domain(&self,owner:usize)->Result<(),String> {
        let writer=crate::h21_scheduled_max_cap::Writer::Cap{context:1,
            origin:owner.checked_add(1).ok_or("Cap1 packed source origin overflow")?};
        if owner!=FIRST_MODERN_CAP0_OWNER || self.binding.owner!=owner || self.writer!=writer
            || self.cells.len()!=FIRST_MODERN_CAP1_CELLS
            || self.cells.iter().enumerate().any(|(i,(wire,_))|*wire!=FIRST_MODERN_CAP1_BASE+i) {
            return Err("Cap1 packed source owner/writer/domain mismatch".into());
        }
        Ok(())
    }

    fn require_header_reservation(&self,owner:usize,binding:&HeaderSourceBinding,
        replacement_mask:&[bool])->Result<(),String> {
        self.validate_domain(owner)?;
        let end=FIRST_MODERN_CAP1_BASE.checked_add(FIRST_MODERN_CAP1_CELLS)
            .ok_or("Cap1 HEADER reservation extent overflow")?;
        if &self.binding!=binding || replacement_mask.len()!=WIDTH || end>replacement_mask.len()
            || replacement_mask[FIRST_MODERN_CAP1_BASE..end].iter().any(|replaced|*replaced) {
            return Err("Cap1 source cannot reserve non-HEADER-owned domain".into());
        }
        Ok(())
    }

    fn reserves_header_local_wire(&self,owner:usize,local:usize)->bool {
        owner==FIRST_MODERN_CAP0_OWNER
            && (FIRST_MODERN_CAP1_BASE..FIRST_MODERN_CAP1_BASE+FIRST_MODERN_CAP1_CELLS).contains(&local)
    }

    fn claim_exclusive(&self,owner:usize,rows:&mut OwnedRows)->Result<(),String> {
        self.validate_domain(owner)?;
        for &(local,_) in &self.cells {
            let (row,wire)=rows.local(owner,local)?;
            if rows.claimed[row][wire] {
                return Err(format!("exclusive Cap1 source claim overlaps owner{owner} wire{local}"));
            }
        }
        for &(local,value) in &self.cells {
            rows.claim_exclusive(owner,local,Fr::from(value as u64))?;
        }
        Ok(())
    }

    pub(crate) fn binding(&self)->&HeaderSourceBinding {&self.binding}
    pub(crate) fn writer(&self)->crate::h21_scheduled_max_cap::Writer {self.writer}
    pub(crate) fn cells(&self)->&[(usize,bool)] {&self.cells}

    #[cfg(test)]
    fn synthetic_for_test(binding:HeaderSourceBinding,cells:Vec<(usize,bool)>)->Self {
        Self{binding,writer:crate::h21_scheduled_max_cap::Writer::Cap{
            context:1,origin:FIRST_MODERN_CAP0_OWNER+1},cells}
    }
}

#[cfg(test)]
mod cap0_packed_source_tests {
    use super::*;

    fn cells() -> Vec<(usize, bool)> {
        let base = FIRST_MODERN_CAP0_BASE;
        (0..FIRST_MODERN_CAP0_CELLS)
            .map(|index| (base + index, index == 17 || index == 1_771))
            .collect()
    }

    #[test]
    fn cap0_source_claims_only_reserved_header_domain_and_matches_packed_bits() {
        let owner = FIRST_MODERN_CAP0_OWNER;
        let binding = HeaderSourceBinding::diagnostic_for_test(owner);
        let cap0 = NativeCap0Source::synthetic_for_test(binding.clone(), cells());
        let mut mask = vec![false; WIDTH];
        cap0.require_header_reservation(owner, &binding, &mask).unwrap();
        let skipped=(0..WIDTH).filter(|local|cap0.reserves_header_local_wire(owner,*local)).count();
        assert_eq!(skipped,FIRST_MODERN_CAP0_CELLS,"header seeder skips exactly Cap0 cells");
        let mut rows = OwnedRows::new(OwnerSelection::Single {
            owner,
            class: crate::daa_history_roster::OwnerClass::Carry,
        });
        for local in 0..WIDTH {
            if !cap0.reserves_header_local_wire(owner,local)
                && !BANKS.iter().any(|&(start,end)|(start..end).contains(&local)) {
                // Non-Cap values are deliberately mixed; this test does not
                // assume the native HEADER template is zero in Cap0's domain.
                rows.claim(owner,local,Fr::from((local & 1) as u64)).unwrap();
            }
        }
        assert_eq!(rows.claimed[0][FIRST_MODERN_CAP0_BASE..FIRST_MODERN_CAP0_BASE+FIRST_MODERN_CAP0_CELLS]
            .iter().filter(|claimed|**claimed).count(),0,"Cap0 HEADER domain stays unclaimed before Cap0 author");
        for (start,end) in BANKS {
            for local in start..end { rows.claim(owner,local,Fr::zero()).unwrap(); }
        }
        cap0.claim_exclusive(owner, &mut rows).unwrap();
        assert_eq!(rows.claimed[0][FIRST_MODERN_CAP0_BASE..FIRST_MODERN_CAP0_BASE+FIRST_MODERN_CAP0_CELLS]
            .iter().filter(|claimed|**claimed).count(),FIRST_MODERN_CAP0_CELLS);
        let bytes = rows.bytes(0).unwrap();
        assert!(cap0.cells().iter().any(|(_, value)| *value));
        assert!(cap0.cells().iter().any(|(_, value)| !*value));
        let row = NativePackedRow {
            owner,
            class: crate::daa_history_roster::OwnerClass::Carry,
            root: binding.root,
            total: binding.total,
            bytes,
            header_source_binding: Some(binding.clone()),
            cap0_source: Some(cap0.clone()),
            cap1_source: None,
            max_binding: None,
            map_binding: None,
            map_context: None,
            #[cfg(test)]
            legacy_binding: None,
        };
        row.require_cap0_source(
            &binding,
            crate::h21_scheduled_max_cap::Writer::Cap {
                context: 0,
                origin: owner + 1,
            },
            cap0.cells(),
        ).unwrap();
        let mut flipped = row.clone();
        let local = cap0.cells().iter().find(|(_, value)| *value).unwrap().0;
        flipped.bytes[local / 8] ^= 1 << (local % 8);
        assert!(flipped.require_cap0_source(
            &binding, cap0.writer(), cap0.cells(),
        ).is_err(), "true Cap0 packed-bit mutation must fail");

        let mut wrong_mask = mask.clone();
        wrong_mask[FIRST_MODERN_CAP0_BASE + 17] = true;
        assert!(cap0.require_header_reservation(owner, &binding, &wrong_mask).is_err());
        let wrong_binding = HeaderSourceBinding::diagnostic_for_test(owner + 1);
        assert!(cap0.require_header_reservation(owner, &wrong_binding, &mask).is_err());
        assert!(row.require_cap0_source(&wrong_binding, cap0.writer(), cap0.cells()).is_err());
        assert!(row.require_cap0_source(
            &binding,
            crate::h21_scheduled_max_cap::Writer::Cap { context: 1, origin: owner + 1 },
            cap0.cells(),
        ).is_err());
        let mut wrong_cells = cap0.cells().to_vec();
        wrong_cells[0].1 = true;
        assert!(row.require_cap0_source(&binding, cap0.writer(), &wrong_cells).is_err());

        let mut overlap = OwnedRows::new(OwnerSelection::Single {
            owner,
            class: crate::daa_history_roster::OwnerClass::Carry,
        });
        overlap.claim(owner, FIRST_MODERN_CAP0_BASE + 17, Fr::zero()).unwrap();
        assert!(cap0.claim_exclusive(owner, &mut overlap).unwrap_err().contains("overlaps"));
    }
}

#[cfg(test)]
mod cap1_packed_source_tests {
    use super::*;

    fn cells(base: usize, count: usize) -> Vec<(usize, bool)> {
        (0..count).map(|i| (base + i, i == 19 || i == 1_777)).collect()
    }

    #[test]
    fn cap01_sources_reserve_disjoint_header_ranges_and_match_packed_bits() {
        use crate::daa_history_roster::OwnerClass;
        use crate::h21_scheduled_max_cap::Writer;

        let owner = FIRST_MODERN_CAP0_OWNER;
        let binding = HeaderSourceBinding::diagnostic_for_test(owner);
        let cap0 = NativeCap0Source::synthetic_for_test(
            binding.clone(), cells(FIRST_MODERN_CAP0_BASE, FIRST_MODERN_CAP0_CELLS),
        );
        let cap1 = NativeCap1Source::synthetic_for_test(
            binding.clone(), cells(FIRST_MODERN_CAP1_BASE, FIRST_MODERN_CAP1_CELLS),
        );
        let cap0_end = FIRST_MODERN_CAP0_BASE + FIRST_MODERN_CAP0_CELLS;
        assert!(cap0_end <= FIRST_MODERN_CAP1_BASE, "Cap HEADER ranges must not overlap");
        let mut mask = vec![false; WIDTH];
        cap0.require_header_reservation(owner, &binding, &mask).unwrap();
        cap1.require_header_reservation(owner, &binding, &mask).unwrap();
        assert_eq!((0..WIDTH).filter(|wire| cap0.reserves_header_local_wire(owner, *wire)).count(),
            FIRST_MODERN_CAP0_CELLS);
        assert_eq!((0..WIDTH).filter(|wire| cap1.reserves_header_local_wire(owner, *wire)).count(),
            FIRST_MODERN_CAP1_CELLS);

        let mut rows = OwnedRows::new(OwnerSelection::Single { owner, class: OwnerClass::Carry });
        for wire in 0..WIDTH {
            if !cap0.reserves_header_local_wire(owner, wire)
                && !cap1.reserves_header_local_wire(owner, wire)
                && !BANKS.iter().any(|&(lo, hi)| (lo..hi).contains(&wire))
            {
                rows.claim(owner, wire, Fr::from((wire & 1) as u64)).unwrap();
            }
        }
        for (lo, hi) in BANKS {
            for wire in lo..hi { rows.claim(owner, wire, Fr::zero()).unwrap(); }
        }
        cap0.claim_exclusive(owner, &mut rows).unwrap();
        cap1.claim_exclusive(owner, &mut rows).unwrap();
        let bytes = rows.bytes(0).unwrap();
        assert!(cap0.cells().iter().any(|(_, bit)| *bit));
        assert!(cap1.cells().iter().any(|(_, bit)| *bit));
        let row = NativePackedRow {
            owner, class: OwnerClass::Carry, root: binding.root, total: binding.total,
            bytes, header_source_binding: Some(binding.clone()), cap0_source: Some(cap0.clone()),
            cap1_source: Some(cap1.clone()), max_binding: None, map_binding: None,
            map_context: None,
            #[cfg(test)] legacy_binding: None,
        };
        row.require_cap0_source(
            &binding, Writer::Cap { context: 0, origin: owner + 1 }, cap0.cells(),
        ).unwrap();
        row.require_cap1_source(
            &binding, Writer::Cap { context: 1, origin: owner + 1 }, cap1.cells(),
        ).unwrap();

        let mut flipped = row.clone();
        let true_wire = cap1.cells().iter().find(|(_, bit)| *bit).unwrap().0;
        flipped.bytes[true_wire / 8] ^= 1 << (true_wire % 8);
        assert!(flipped.require_cap1_source(&binding, cap1.writer(), cap1.cells()).is_err(),
            "Cap1 packed-bit mutation must fail");
        let wrong_binding = HeaderSourceBinding::diagnostic_for_test(owner + 1);
        assert!(row.require_cap1_source(&wrong_binding, cap1.writer(), cap1.cells()).is_err());
        assert!(row.require_cap1_source(
            &binding, Writer::Cap { context: 0, origin: owner + 1 }, cap1.cells(),
        ).is_err(), "wrong Cap context must fail");
        let mut wrong_domain = cap1.cells().to_vec();
        wrong_domain[0].0 = FIRST_MODERN_CAP0_BASE;
        assert!(row.require_cap1_source(&binding, cap1.writer(), &wrong_domain).is_err());
        let mut cap0_bit_mutant = row.clone();
        let cap0_true_wire = cap0.cells().iter().find(|(_, bit)| *bit).unwrap().0;
        cap0_bit_mutant.bytes[cap0_true_wire / 8] ^= 1 << (cap0_true_wire % 8);
        assert!(cap0_bit_mutant.require_cap1_source(&binding, cap1.writer(), cap1.cells()).is_err(),
            "Cap1 admission must recheck paired Cap0 packed bits");

        let mut wrong_mask = mask.clone();
        wrong_mask[FIRST_MODERN_CAP1_BASE + 19] = true;
        assert!(cap1.require_header_reservation(owner, &binding, &wrong_mask).is_err());
        let mut wrong_writer_source = cap1.clone();
        wrong_writer_source.writer = Writer::Cap { context: 0, origin: owner + 1 };
        let wrong_writer_row = NativePackedRow {
            cap1_source: Some(wrong_writer_source), ..row.clone()
        };
        assert!(wrong_writer_row.require_cap1_source(&binding, cap1.writer(), cap1.cells()).is_err());

        let mut collision = OwnedRows::new(OwnerSelection::Single { owner, class: OwnerClass::Carry });
        collision.claim(owner, FIRST_MODERN_CAP1_BASE + 19, Fr::one()).unwrap();
        assert!(cap1.claim_exclusive(owner, &mut collision).unwrap_err().contains("overlaps"),
            "same-value duplicate ownership must fail");
        assert_eq!(collision.claimed[0].iter().filter(|claimed| **claimed).count(), 1,
            "a rejected Cap1 reservation must not partially write preceding cells");

        let cap1_only = NativePackedRow { cap0_source: None, ..row };
        assert!(cap1_only.require_cap1_source(&binding, cap1.writer(), cap1.cells())
            .unwrap_err().contains("paired Cap0"));
        mask[FIRST_MODERN_CAP0_BASE] = true;
        assert!(cap0.require_header_reservation(owner, &binding, &mask).is_err());
    }
}

/// An ordinary-owner byte candidate with its source join, selected open reads,
/// and DAA author retained together. It is deliberately not a checked slice.
pub(crate) struct NativePartialScoredOwnerPackedCandidate<'p, 'a> {
    row: NativePackedRow,
    daa: NativeDaaSourceLease<'p, 'a>,
    source: ScoredOwnerPackingView,
}

impl NativePartialScoredOwnerPackedCandidate<'_, '_> {
    pub(crate) fn owner(&self) -> usize { self.row.owner() }
    pub(crate) fn partial_packed_bytes(&self) -> &[u8] { self.row.packed_bytes() }
    pub(crate) fn binding(&self) -> Result<&HeaderSourceBinding, String> {
        let source = self.source.binding();
        if self.row.owner() != source.owner()
            || self.row.header_source_binding.as_ref() != Some(source) {
            return Err("C396 partial packed candidate row/source binding mismatch".into());
        }
        Ok(source)
    }
    /// Borrow the regular-owner source only from the same retained physical
    /// candidate. Its partial packed cells are checked again, while all
    /// remaining X/ROW operands stay outside this source view's authority.
    pub(crate) fn c509_regular_row_source(
        &self,
    ) -> Result<C509RegularRowSourceView<'_>, String> {
        const OWNER: usize = 845_887;
        let binding = self.binding()?;
        if self.owner() != OWNER || self.row.class() != crate::daa_history_roster::OwnerClass::Carry
            || self.row.packed_bytes().len() != OWNER_BYTES
            || self.source.cells().len() != 20_480 {
            return Err("C509 retained packed candidate owner/class/cell census".into());
        }
        self.check_daa_author()?;
        for cell in self.source.cells() {
            let local = scored_owner_cell_local(OWNER, cell)?;
            if NativeHeaderSourceLease::bit(self.row.packed_bytes(), local) != cell.value() {
                return Err(format!("C509 retained source/packed bit mismatch wire{}", cell.wire()));
            }
        }
        self.source.c509_regular_row_source(binding)
    }
    pub(crate) fn source_cells(&self) -> &[h21_eligible_context::ScoredOwnerPackedCell] {
        self.source.cells()
    }
    pub(crate) fn selected_open_reads(&self) -> &[OpenScoredRead] {
        self.source.selected_open_reads()
    }
    pub(crate) fn source_term_counts(&self) -> [usize; 4] {
        self.source.source_term_counts()
    }
    pub(crate) fn retained_header_daa_active_operand_count(&self) -> usize {
        self.source.retained_header_daa_active_operand_count()
    }
    pub(crate) fn check_daa_author(&self) -> Result<(), String> {
        self.daa.check_carry_zero_source(self.binding()?)
    }

    #[cfg(test)]
    pub(crate) fn require_source_x_conflict_rejected_for_test(&self) -> Result<(), String> {
        let binding = self.binding()?;
        let owner = self.owner();
        let cell = self.source.cells().last().ok_or("C396 test source cell absent")?;
        let local = scored_owner_cell_local(owner, cell)?;
        let mut rows = OwnedRows::new(OwnerSelection::Single {
            owner, class: crate::daa_history_roster::OwnerClass::Carry,
        });
        rows.claim(owner, local, Fr::from(cell.value() as u64))?;
        let initial_claims = rows.claimed[0].iter().filter(|claimed| **claimed).count();
        let error = claim_scored_owner_source(&mut rows, &self.source, binding)
            .err().ok_or("C396 duplicate source X claim unexpectedly admitted")?;
        if !error.contains("overlaps") || initial_claims != 1
            || rows.claimed[0].iter().filter(|claimed| **claimed).count() != initial_claims
            || rows.values[0][local] != Fr::from(cell.value() as u64) {
            return Err("C396 source X conflict failed for an unrelated reason".into());
        }
        Ok(())
    }
}

/// One regular owner's actual packed writer and its source-bound claim image.
/// Construction is private to the owner-845887 producer route. It does not
/// install the row in global X or admit the C509 ROW relation.
#[allow(dead_code)]
pub(crate) struct NativeRegularOwnerAuthorCensus<'p, 'a> {
    candidate: NativePartialScoredOwnerPackedCandidate<'p, 'a>,
    authors: Vec<Option<NativeRegularPhysicalAuthor>>,
    sealed_bits: Vec<u8>,
    complete_checked: Cell<bool>,
}

#[allow(dead_code)]
impl NativeRegularOwnerAuthorCensus<'_, '_> {
    pub(crate) fn c574_score_cell(&self, wire: usize)
        -> Result<(h21_eligible_context::ScoreReplayAuthor, bool), String> {
        let (physical, value) = self.checked_cell(wire)?;
        let (_, _, view) = self.c574_source()?;
        let cell = view.cells().iter().find(|cell| cell.wire() == wire)
            .ok_or("C574 Score cell missing typed author")?;
        let ScoredOwnerPackedAuthor::Score(author) = cell.author() else {
            return Err("C574 cell lacks typed Score author".into());
        };
        if physical != NativeRegularPhysicalAuthor::Scored || cell.value() != value {
            return Err("C574 typed/physical/sealed Score mismatch".into());
        }
        Ok((author, value))
    }
    pub(crate) fn c574_source(&self) -> Result<(&[u8],
        &[Option<NativeRegularPhysicalAuthor>], &ScoredOwnerPackingView), String> {
        c574_regular_owner(self.candidate.owner())?;
        Self::require_complete_checked(&self.complete_checked)?;
        if self.candidate.row.bytes != self.sealed_bits {
            self.complete_checked.set(false);
            return Err("C574 packed source changed after seal".into());
        }
        Ok((&self.sealed_bits, &self.authors, &self.candidate.source))
    }
    fn bit(bytes: &[u8], local: usize) -> bool {
        bytes[local / 8] & (1u8 << (local % 8)) != 0
    }

    fn require_complete_checked(checked: &Cell<bool>) -> Result<(), String> {
        if !checked.get() {
            return Err("C512e regular census not completely checked".into());
        }
        Ok(())
    }

    fn checked_sealed_bit(checked: &Cell<bool>, packed: &[u8], sealed: &[u8],
        local: usize) -> Result<bool, String> {
        Self::require_complete_checked(checked)?;
        if local >= WIDTH || packed.len() <= local / 8 || sealed.len() <= local / 8 {
            checked.set(false);
            return Err("C512e regular sealed bit bounds changed".into());
        }
        let value = Self::bit(packed, local);
        if value != Self::bit(sealed, local) {
            checked.set(false);
            return Err("C512e physical row changed after complete check".into());
        }
        Ok(value)
    }

    pub(crate) fn binding(&self) -> Result<&HeaderSourceBinding, String> {
        self.candidate.binding()
    }

    pub(crate) fn c509_regular_row_source(&self)
        -> Result<C509RegularRowSourceView<'_>, String> {
        Self::require_complete_checked(&self.complete_checked)?;
        self.candidate.c509_regular_row_source()
    }

    /// Rebuild source values from the same native producer retained by the
    /// CarryZero lease, and compare every claimed bit with the packed row.
    pub(crate) fn check_complete(&self) -> Result<[usize; 4], String> {
        use crate::daa_history_roster::OwnerClass;
        let owner = self.candidate.owner();
        c574_regular_owner(owner)?;
        self.complete_checked.set(false);
        let candidate = &self.candidate;
        let producer = candidate.daa._source;
        let binding = candidate.binding()?;
        let row = &candidate.row;
        let expected_binding = HeaderSourceBinding::for_plan(producer.plan, owner)?;
        if candidate.owner() != owner || binding != &expected_binding
            || self.authors.len() != WIDTH || self.sealed_bits.len() != OWNER_BYTES
            || row.bytes != self.sealed_bits
            || producer.plan.headers() != 1_827_840 || producer.plan.slot_log() != 21
            || producer.plan.slots() != 1 << 21
            || producer.input.header_count() != 1_827_840
            || binding.profile() != producer.input.profile()
            || producer.roster.owner_class(owner as u64)? != OwnerClass::Carry
            || crate::h21_scheduled_max_cap::Plan::eligible08().max_calendar()
                .iter().any(|(scheduled_owner, _)| *scheduled_owner == owner)
        {
            return Err("C512e regular census exact owner, row, parent or schedule".into());
        }
        row.require_header_source_binding(binding, owner, OwnerClass::Carry)?;
        candidate.daa.check_carry_zero_source(binding)?;
        scored_owner_source_local(&candidate.source, owner, binding)?;

        let child = producer.input.header(owner + 1)?;
        let previous = producer.input.header(owner)?;
        for header in [&previous, &child] {
            if header.encode().map_err(|error| format!("C512e HEADER encode: {error:?}"))?
                != producer.input.raw(header.height as usize)?
            {
                return Err("C512e canonical HEADER source bytes".into());
            }
        }
        let fields = crate::serializer::Fields::from_header(&child)?;
        let mut header = producer.header_template.assign(&fields)?;
        producer.header_template.assign_order(
            &mut header, &fields, previous.height, previous.timestamp, false,
        )?;
        let tree_mask = producer.plan.physical_assignment_replacement_mask(owner as u64)?;
        let tree = NativeTreeSourceLease::from_prefix(producer.plan, producer.input, owner)?;
        tree.check_binding(binding)?;
        tree.check_author()?;
        if header.len() != WIDTH || tree_mask.len() != WIDTH
            || tree.owned.len() != OWNER_BYTES || tree.values.len() != OWNER_BYTES
            || candidate.source.cells().len() != h21_eligible_context::Eligible08RegularScoreOwner::classify(owner)?.typed_cell_count()
        {
            return Err("C512e complete regular source image widths".into());
        }
        let mut scored = vec![None; WIDTH];
        for cell in candidate.source.cells() {
            let local = scored_owner_cell_local(owner, cell)?;
            if scored[local].replace(cell.value()).is_some() {
                return Err(format!("C512e duplicate typed Scored source wire{local}"));
            }
        }
        let mut counts = [0usize; 4];
        for local in 0..WIDTH {
            let tree_owned = Self::bit(&tree.owned, local);
            let tree_value = Self::bit(&tree.values, local);
            if tree_owned != tree_mask[local] || (!tree_owned && tree_value) {
                return Err(format!("C512e independent Tree mask/value wire{local}"));
            }
            let daa = BANKS.iter().any(|&(start, end)| (start..end).contains(&local));
            if (tree_mask[local] && daa)
                || (scored[local].is_some() && (tree_mask[local] || daa))
            {
                return Err(format!("C512e regular writer domain overlap wire{local}"));
            }
            c574_required_bank53_author(owner, local, scored[local].is_some(),
                tree_mask[local], daa, header[local])?;
            let (author, value, index) = if tree_mask[local] {
                (NativeRegularPhysicalAuthor::Tree, tree_value, 1)
            } else if daa {
                (NativeRegularPhysicalAuthor::Daa, false, 2)
            } else if let Some(value) = scored[local] {
                (NativeRegularPhysicalAuthor::Scored, value, 3)
            } else {
                let value = header[local];
                if value != Fr::zero() && value != Fr::one() {
                    return Err(format!("C512e non-Boolean canonical HEADER wire{local}"));
                }
                (NativeRegularPhysicalAuthor::Header, value.is_one(), 0)
            };
            if self.authors[local] != Some(author)
                || Self::bit(&row.bytes, local) != value
            {
                return Err(format!("C512e physical author/source/packed wire{local}"));
            }
            counts[index] += 1;
        }
        let point = crate::segment_points::POINT_OFFSET;
        let point_end = point + crate::point_membership::POINT_WIDTH;
        if (owner == 845_887 && counts != [544_814, 401_362, 81_920, 20_480])
            || counts.iter().sum::<usize>() != WIDTH
            || counts[3] != candidate.source.cells().len()
            || self.authors[point..point_end].iter().any(|author|
                *author != Some(NativeRegularPhysicalAuthor::Header))
            || self.authors[999_424..1_000_770].iter().any(|author|
                *author != Some(NativeRegularPhysicalAuthor::Header))
        {
            return Err(format!("C512e exact four-author counts/Point/MAX {counts:?}"));
        }
        self.complete_checked.set(true);
        Ok(counts)
    }

    /// Constant-time read of an already checked local physical writer. The
    /// consumer must preserve C509 occurrence identity separately.
    pub(crate) fn checked_cell(&self, physical_wire: usize)
        -> Result<(NativeRegularPhysicalAuthor, bool), String> {
        Self::require_complete_checked(&self.complete_checked)?;
        let binding = self.candidate.binding()?;
        let base = binding.owner().checked_mul(WIDTH)
            .ok_or("C512e owner base overflow")?;
        let local = physical_wire.checked_sub(base).filter(|local| *local < WIDTH)
            .ok_or("C512e physical read outside selected owner")?;
        let author = self.authors[local]
            .ok_or("C512e physical read missing zero-inclusive claim")?;
        let value = Self::checked_sealed_bit(&self.complete_checked,
            &self.candidate.row.bytes, &self.sealed_bits, local)?;
        Ok((author, value))
    }
}

/// Producer-owned custody of one first-anchor row and its exact checked source.
/// The immutable bundle borrow retains the typed Map/ScoreAnchor/Slack authors.
pub(crate) struct NativeFirstAnchorPacked<'b> {
    row: NativePackedRow,
    bundle: &'b Eligible08MapSlackAnchorBundle,
    binding: HeaderSourceBinding,
}

impl<'b> NativeFirstAnchorPacked<'b> {
    pub(crate) fn row(&self) -> &NativePackedRow { &self.row }
    pub(crate) fn bundle(&self) -> &'b Eligible08MapSlackAnchorBundle { self.bundle }
    pub(crate) fn binding(&self) -> &HeaderSourceBinding { &self.binding }
}

#[cfg_attr(test, derive(Clone))]
pub(crate) struct NativePackedRow {
    owner: usize,
    class: crate::daa_history_roster::OwnerClass,
    root: [u8; 32],
    total: [u8; 28],
    bytes: Vec<u8>,
    /// Present only for an unadapted, producer-owned H21 row. Other native
    /// rows remain valid for their existing consumers without this authority.
    header_source_binding: Option<HeaderSourceBinding>,
    cap0_source: Option<NativeCap0Source>,
    cap1_source: Option<NativeCap1Source>,
    max_binding: Option<[u8; 32]>,
    map_binding: Option<crate::legacy_envelope_map::Binding>,
    map_context: Option<usize>,
    #[cfg(test)]
    legacy_binding: Option<[u8; 32]>,
}
impl NativePackedRow {
    pub(crate) fn owner(&self) -> usize {
        self.owner
    }
    pub(crate) fn class(&self) -> crate::daa_history_roster::OwnerClass {
        self.class
    }
    pub(crate) fn packed_bytes(&self) -> &[u8] {
        &self.bytes
    }
    pub(crate) fn require_cap0_source(
        &self,
        expected: &HeaderSourceBinding,
        writer: crate::h21_scheduled_max_cap::Writer,
        cells: &[(usize, bool)],
    ) -> Result<(), String> {
        let source = self.cap0_source.as_ref()
            .ok_or("native packed ROW has no Cap0 source provenance")?;
        source.validate_domain(self.owner)?;
        if source.binding() != expected || source.writer() != writer || source.cells() != cells
            || self.bytes.len() != OWNER_BYTES
        {
            return Err("native packed ROW Cap0 source binding/writer/cells mismatch".into());
        }
        for &(wire, value) in cells {
            if !(FIRST_MODERN_CAP0_BASE..FIRST_MODERN_CAP0_BASE+FIRST_MODERN_CAP0_CELLS)
                .contains(&wire) {
                return Err("native packed ROW Cap0 source wire outside domain".into());
            }
            if ((self.bytes[wire / 8] >> (wire % 8)) & 1 != 0) != value {
                return Err("native packed ROW Cap0 source/packed mismatch".into());
            }
        }
        Ok(())
    }
    pub(crate) fn require_cap1_source(
        &self,
        expected: &HeaderSourceBinding,
        writer: crate::h21_scheduled_max_cap::Writer,
        cells: &[(usize, bool)],
    ) -> Result<(), String> {
        let source = self.cap1_source.as_ref()
            .ok_or("native packed ROW has no Cap1 source provenance")?;
        let cap0 = self.cap0_source.as_ref()
            .ok_or("native packed ROW Cap1 source has no paired Cap0 provenance")?;
        source.validate_domain(self.owner)?;
        cap0.validate_domain(self.owner)?;
        if self.class != crate::daa_history_roster::OwnerClass::Carry
            || self.header_source_binding.as_ref() != Some(expected)
            || source.binding() != expected || cap0.binding() != expected
            || source.writer() != writer || cap0.writer() != (crate::h21_scheduled_max_cap::Writer::Cap {
                context: 0, origin: self.owner.checked_add(1).ok_or("Cap1 row origin overflow")?,
            })
            || source.cells() != cells || self.bytes.len() != OWNER_BYTES
        {
            return Err("native packed ROW Cap0/Cap1 source binding/writer/cells mismatch".into());
        }
        self.require_cap0_source(
            expected,
            crate::h21_scheduled_max_cap::Writer::Cap {
                context: 0,
                origin: self.owner.checked_add(1).ok_or("Cap1 row origin overflow")?,
            },
            cap0.cells(),
        )?;
        for &(wire, value) in cells {
            if !(FIRST_MODERN_CAP1_BASE..FIRST_MODERN_CAP1_BASE + FIRST_MODERN_CAP1_CELLS)
                .contains(&wire)
            {
                return Err("native packed ROW Cap1 source wire outside domain".into());
            }
            if ((self.bytes[wire / 8] >> (wire % 8)) & 1 != 0) != value {
                return Err("native packed ROW Cap1 source/packed mismatch".into());
            }
        }
        Ok(())
    }
    pub(crate) fn require_header_source_binding(
        &self, expected: &HeaderSourceBinding, owner: usize,
        class: crate::daa_history_roster::OwnerClass,
    ) -> Result<(), String> {
        #[cfg(test)]
        let legacy_adapted = self.legacy_binding.is_some();
        #[cfg(not(test))]
        let legacy_adapted = false;
        if self.owner != owner || self.class != class || self.root != expected.root
            || self.total != expected.total || self.bytes.len() != OWNER_BYTES
            || self.header_source_binding.as_ref() != Some(expected)
            || self.max_binding.is_some() || self.map_binding.is_some()
            || self.map_context.is_some() || legacy_adapted
        {
            return Err("native packed ROW source root/total/profile/cut/layout/owner/class".into());
        }
        Ok(())
    }
    /// Cheap test-only metadata gate; does not validate packed row equations.
    #[cfg(test)]
    pub(crate) fn validate_bank53_map_identity_for_history_test(
        &self,
        plan: &WorkTreeHistoryPlan,
        map: &crate::legacy_envelope_map::Map,
        owner: usize,
        context: usize,
    ) -> Result<(), String> {
        if context >= BANK53_CONTEXTS || owner >= plan.slots() as usize
            || self.owner != owner || self.bytes.len() != OWNER_BYTES
            || self.root != plan.descriptor().root
            || self.total != plan.work_profile().total_be28
            || map.n() != plan.headers() || map.h() != plan.slot_log()
            || map.slots() != plan.slots() as u64
            || map.binding().parent_root != Some(plan.descriptor().root)
            || self.map_binding.as_ref() != Some(&map.binding())
            || self.map_context != Some(context)
            || self.max_binding.is_some() || self.legacy_binding.is_some()
        {
            return Err("native Bank53 Map row identity/binding/context".into());
        }
        Ok(())
    }
    /// Test-only metadata gate for a selected row in a larger native bundle.
    /// It does not validate all row equations or authenticate packed bytes.
    #[cfg(test)]
    pub(crate) fn validate_identity_for_history_test(
        &self,
        plan: &WorkTreeHistoryPlan,
        input: &NativePrefix,
        owner: usize,
    ) -> Result<(), String> {
        validate_native_plan_input(plan, input)?;
        let roster = DaaHistoryRoster::compile(plan)?;
        if self.owner != owner
            || self.class != roster.owner_class(owner as u64)?
            || self.root != input.root()
            || self.total != input.total_be28()
            || self.bytes.len() != WIDTH / 8
            || self.max_binding.is_some()
            || self.map_binding.is_some()
            || self.legacy_binding.is_some()
        {
            return Err("native selected row parent/owner identity".into());
        }
        Ok(())
    }
    /// Cheaply recheck a mutable candidate copy against a source row whose
    /// full parent identity was validated when the candidate was staged.
    #[cfg(test)]
    pub(crate) fn validate_source_copy_for_history_test(
        &self,
        source: &Self,
        owner: usize,
        root: [u8; 32],
        total: [u8; 28],
    ) -> Result<(), String> {
        let clean_metadata = |row: &Self| {
            row.owner == owner
                && row.root == root
                && row.total == total
                && row.bytes.len() == WIDTH / 8
                && row.max_binding.is_none()
                && row.map_binding.is_none()
                && row.map_context.is_none()
                && row.legacy_binding.is_none()
        };
        if !clean_metadata(self) || !clean_metadata(source) || self.class != source.class {
            return Err("native selected row parent/owner identity".into());
        }
        if self.bytes != source.bytes {
            return Err("native source row bytes mismatch".into());
        }
        Ok(())
    }
    /// Preserve source-produced metadata while testing bytes read back from a
    /// selected packed PCS file. This does not commit the metadata itself.
    #[cfg(test)]
    pub(crate) fn with_packed_bytes_for_test(&self, packed: &[u8]) -> Result<Self, String> {
        if self.bytes.len() != OWNER_BYTES || packed.len() != OWNER_BYTES {
            return Err("test packed owner byte width".into());
        }
        let mut hydrated = self.clone();
        hydrated.bytes = packed.to_vec();
        Ok(hydrated)
    }
    #[cfg(test)]
    pub(crate) fn reject_legacy_for_test(&self) -> Result<(), String> {
        if self.legacy_binding.is_some() {
            Err("legacy native consumer binding mismatch".into())
        } else { Ok(()) }
    }
    #[cfg(test)]
    pub(crate) fn admit_legacy_for_test(
        &self, adapter: &crate::legacy_native_adapter::LegacyNativeAdapter<'_>, owner: usize,
    ) -> Result<(), String> {
        if self.owner != owner { return Err("legacy native row owner mismatch".into()); }
        if self.max_binding.is_some() { return Err("legacy native MAX mixing".into()); }
        if self.legacy_binding != Some(adapter.binding()) {
            return Err("legacy native consumer binding mismatch".into());
        }
        if owner >= adapter.parent().slots() || self.root != adapter.input().root()
            || self.total != adapter.input().total_be28() || self.bytes.len() != OWNER_BYTES
            || self.class != adapter.roster().owner_class(owner as u64)? {
            return Err("legacy native row identity mismatch".into());
        }
        Ok(())
    }
    #[cfg(test)]
    pub(crate) fn set_legacy_binding_for_test(&mut self, binding: Option<[u8;32]>) {
        self.legacy_binding = binding;
    }
    #[cfg(test)]
    pub(crate) fn set_max_binding_for_test(&mut self, binding: Option<[u8;32]>) {
        self.max_binding = binding;
    }
}

/// Source-owned, four-slot N=3 witness for the bounded log22 PCS join. Owner
/// zero is the genesis sentinel; owners one and two are genuine, and owner
/// three is physical padding with active header constraints. Every pass starts
/// at owner zero and retains no more than one full owner assignment.
pub(crate) struct NativePcsSource<'p, 'a> {
    producer: &'p NativeOwnerProducer<'a>,
    binding: [u8; 32],
    #[cfg(test)]
    passes: Cell<usize>,
    #[cfg(test)]
    fault: Cell<Option<NativePcsFault>>,
}

#[cfg(test)]
#[derive(Clone, Copy, Debug)]
pub(crate) enum NativePcsFaultKind { Reorder, Short, Flip, Omit }

#[cfg(test)]
#[derive(Clone, Copy, Debug)]
pub(crate) struct NativePcsFault {
    pub(crate) pass: usize,
    pub(crate) row: usize,
    pub(crate) kind: NativePcsFaultKind,
}

impl<'p, 'a> NativePcsSource<'p, 'a> {
    pub(crate) const LOG_N: usize = 22;
    pub(crate) const ROW_BITS: usize = 1 << 11;
    pub(crate) const ROWS_PER_OWNER: usize = WIDTH / Self::ROW_BITS;
    pub(crate) const ROWS: usize = 4 * Self::ROWS_PER_OWNER;

    pub(crate) fn new(producer: &'p NativeOwnerProducer<'a>) -> Result<Self, String> {
        Self::check_source(producer)?;
        Ok(Self {
            producer,
            binding: Self::derive_binding(producer),
            #[cfg(test)] passes: Cell::new(0),
            #[cfg(test)] fault: Cell::new(None),
        })
    }

    pub(crate) fn require_parent(
        &self,
        expected: &crate::work_tree_history_plan::WorkTreeHistoryPlan,
    ) -> Result<(), String> {
        self.check_identity()?;
        if !std::ptr::eq(self.producer.plan, expected) {
            return Err("native PCS source parent identity mismatch".into());
        }
        Ok(())
    }

    fn check_source(producer: &NativeOwnerProducer<'_>) -> Result<(), String> {
        validate_native_plan_input(producer.plan, producer.input)?;
        if producer.plan.headers() != 3 || producer.plan.slot_log() != 2
            || producer.plan.slots() != 4 || producer.input.header_count() != 3
            || producer.input.slot_count() != 4 || producer.max_adapter.is_some()
        {
            return Err("native PCS requires unadapted N3/H2/four-slot source".into());
        }
        #[cfg(test)]
        if producer.legacy_adapter.is_some() {
            return Err("native PCS rejects legacy source".into());
        }
        Ok(())
    }

    fn derive_binding(producer: &NativeOwnerProducer<'_>) -> [u8; 32] {
        Self::derive_binding_fields(
            producer.plan.headers(),
            producer.plan.slot_log(),
            producer.plan.slots(),
            producer.input.root(),
            producer.input.total_be28(),
            producer.input.profile(),
        )
    }

    fn derive_binding_fields(
        headers: u64,
        slot_log: usize,
        slots: usize,
        root: [u8; 32],
        total_be28: [u8; 28],
        profile: [u8; 32],
    ) -> [u8; 32] {
        let mut hash = Blake2b::<U32>::new();
        hash.update(b"nipopow-native-owner-pcs-source-n3-h2-v1");
        hash.update(headers.to_le_bytes());
        hash.update((slot_log as u64).to_le_bytes());
        hash.update((slots as u64).to_le_bytes());
        hash.update((WIDTH as u64).to_le_bytes());
        hash.update((Self::ROW_BITS as u64).to_le_bytes());
        hash.update(root);
        hash.update(total_be28);
        hash.update(profile);
        hash.finalize().into()
    }

    /// Derive the N3/H2 native PCS source identity from the public history
    /// statement. The profile is fixed by the code-owned mainnet prefix and is
    /// independent of any RAW header or native witness state.
    pub(crate) fn public_binding(
        plan: &crate::work_tree_history_plan::WorkTreeHistoryPlan,
    ) -> Result<[u8; 32], String> {
        if plan.headers() != 3 || plan.slot_log() != 2 || plan.slots() != 4 {
            return Err("native PCS public binding requires exact N3/H2/four-slot plan".into());
        }
        let mut profile_bytes = fixed::PROFILE_PREFIX.to_vec();
        profile_bytes.extend_from_slice(&crate::header_order::MAINNET_GENESIS);
        let profile: [u8; 32] = Blake2b::<U32>::digest(profile_bytes).into();
        Ok(Self::derive_binding_fields(
            plan.headers(),
            plan.slot_log(),
            plan.slots(),
            plan.descriptor().root,
            plan.work_profile().total_be28,
            profile,
        ))
    }

    fn check_identity(&self) -> Result<(), String> {
        Self::check_source(self.producer)?;
        if Self::derive_binding(self.producer) != self.binding {
            return Err("native PCS source identity drift".into());
        }
        Ok(())
    }

    fn validate_owner_row(
        &self,
        owner: usize,
        row: &NativePackedRow,
    ) -> Result<(), String> {
        if row.owner != owner || row.class != self.producer.roster.owner_class(owner as u64)?
            || row.root != self.producer.input.root || row.total != self.producer.input.total
            || row.bytes.len() != OWNER_BYTES || row.max_binding.is_some()
            || row.map_binding.is_some() || row.map_context.is_some()
        {
            return Err("native PCS owner identity or byte width drift".into());
        }
        #[cfg(test)]
        if row.legacy_binding.is_some() {
            return Err("native PCS legacy row binding".into());
        }
        Ok(())
    }

    pub(crate) fn read_owner(&self, owner: usize) -> Result<NativePackedRow, String> {
        self.check_identity()?;
        if owner >= 4 {
            return Err("native PCS owner outside N3 source".into());
        }
        let row = self.producer.produce(owner)?;
        self.validate_owner_row(owner, &row)?;
        Ok(row)
    }

    pub(crate) fn binding(&self) -> [u8; 32] { self.binding }
    pub(crate) fn input_len(&self) -> usize { 1 << Self::LOG_N }

    #[cfg(test)]
    pub(crate) fn set_fault_for_test(&self, fault: Option<NativePcsFault>) {
        self.fault.set(fault);
    }
    #[cfg(test)]
    pub(crate) fn pass_count_for_test(&self) -> usize { self.passes.get() }

    pub(crate) fn scan_rows(
        &self,
        mut consume: impl FnMut(usize, &[u8]) -> Result<(), String>,
    ) -> Result<(), String> {
        self.check_identity()?;
        #[cfg(test)]
        let pass = { let pass = self.passes.get(); self.passes.set(pass + 1); pass };
        let mut emitted = 0usize;
        for owner in 0..4 {
            let row = self.read_owner(owner)?;
            for (local, bytes) in row.bytes.chunks_exact(Self::ROW_BITS / 8).enumerate() {
                let index = owner * Self::ROWS_PER_OWNER + local;
                #[cfg(test)]
                if let Some(fault) = self.fault.get().filter(|f| f.pass == pass && f.row == index) {
                    match fault.kind {
                        NativePcsFaultKind::Reorder => { consume(index + 1, bytes)?; emitted += 1; continue; }
                        NativePcsFaultKind::Short => { consume(index, &bytes[..bytes.len() - 1])?; emitted += 1; continue; }
                        NativePcsFaultKind::Flip => {
                            let mut changed = bytes.to_vec(); changed[0] ^= 1;
                            consume(index, &changed)?; emitted += 1; continue;
                        }
                        NativePcsFaultKind::Omit => continue,
                    }
                }
                consume(index, bytes)?;
                emitted += 1;
            }
        }
        if emitted != Self::ROWS { return Err("native PCS complete row count drift".into()); }
        Ok(())
    }
}

/// Reuses the admitted plan and immutable native inputs for successive rows;
/// at most one expanded row is retained by production. No caller controls the
/// imported coordinates or their values.
#[derive(Clone,Debug,PartialEq,Eq)]
pub(crate) struct HeaderSourceBinding {
    root:[u8;32],total:[u8;28],profile:[u8;32],cut:Vec<u8>,
    layout:[u8;32],owner:usize,
}
impl HeaderSourceBinding {
    pub(crate) fn for_plan(plan:&WorkTreeHistoryPlan,owner:usize)->Result<Self,String> {
        if plan.headers()!=1_827_840 || plan.slot_log()!=21 || plan.slots()!=1<<21
            || owner>=plan.slots() {
            return Err("HEADER source requires fixed H21 owner/plan".into());
        }
        let mut profile_bytes=fixed::PROFILE_PREFIX.to_vec();
        profile_bytes.extend_from_slice(&crate::header_order::MAINNET_GENESIS);
        let profile=Blake2b::<U32>::digest(profile_bytes).into();
        Ok(Self{root:plan.descriptor().root,total:plan.work_profile().total_be28,
            profile,cut:crate::bank53_map::CutDescriptor::eligible08().canonical_identity(),
            layout:crate::header_daa_row_placement::Layout::fixed().digest(),owner})
    }
    pub(crate) fn profile(&self)->[u8;32] {self.profile}
    pub(crate) fn owner(&self)->usize {self.owner}
    pub(crate) fn matches_sink(&self,root:[u8;32],total:[u8;28],profile:[u8;32],
        cut:&[u8],owner:usize)->bool {
        self.root==root && self.total==total && self.profile==profile
            && self.cut==cut && self.layout==crate::header_daa_row_placement::Layout::fixed().digest()
            && self.owner==owner
    }
    #[cfg(test)]
    pub(crate) fn from_sink_for_test(root:[u8;32],total:[u8;28],profile:[u8;32],
        cut:Vec<u8>,owner:usize)->Self {
        Self{root,total,profile,cut,
            layout:crate::header_daa_row_placement::Layout::fixed().digest(),owner}
    }
    #[cfg(test)]
    pub(crate) fn diagnostic_for_test(owner:usize)->Self {
        Self{root:[0;32],total:[0;28],profile:[0;32],cut:Vec::new(),
            layout:crate::header_daa_row_placement::Layout::fixed().digest(),owner}
    }
    #[cfg(test)]
    pub(crate) fn mutated_field_for_test(&self,field:usize)->Self {
        let mut wrong=self.clone();
        match field {
            0=>wrong.root[0]^=1,
            1=>wrong.total[0]^=1,
            2=>wrong.profile[0]^=1,
            3=>wrong.cut.push(0),
            4=>wrong.layout[0]^=1,
            5=>wrong.owner=wrong.owner.saturating_add(1),
            _=>panic!("unknown HeaderSourceBinding test field"),
        }
        wrong
    }
}

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
enum ObservedPaddingHeaderZeroAuthor { HeaderSeed, Other }

fn check_padding_header_zero_observation(
    required:crate::bank53_required_writer::RequiredWriter,
    observed:Option<ObservedPaddingHeaderZeroAuthor>,
    source_bit:Option<bool>,
    packed_bit:bool,
)->Result<bool,String> {
    use crate::bank53_required_writer::RequiredWriter;
    if required!=RequiredWriter::HeaderZero {
        return Err("C449 required writer is not HEADER-zero".into());
    }
    if observed!=Some(ObservedPaddingHeaderZeroAuthor::HeaderSeed) {
        return Err("C449 HEADER-zero physical claim absent or wrong author".into());
    }
    let source_bit=source_bit.ok_or("C449 HEADER-zero source claim absent")?;
    if source_bit || packed_bit || source_bit!=packed_bit {
        return Err("C449 HEADER-zero source/final packed bit mismatch".into());
    }
    Ok(false)
}

/// Opaque production custody for the padded owner's actual HEADER seed row.
/// The captured claims and final row cannot be separated or replaced.
pub(crate) struct NativePaddingHeaderZeroRow {
    row: NativePackedRow,
    capture: PaddingHeaderZeroCapture,
}

/// Opaque same-row custody for the C450 Map/HeaderZero partition. The lease
/// borrow keeps the typed Map source alive with its physical packed row.
pub(crate) struct NativeMixedMapHeaderRow<'m> {
    row: NativePackedRow,
    capture: MixedMapHeaderCapture,
    binding: HeaderSourceBinding,
    map_lease: &'m Eligible08MapPairLease,
}

impl<'m> NativeMixedMapHeaderRow<'m> {
    fn from_producer(
        row:NativePackedRow,
        capture:MixedMapHeaderCapture,
        binding:HeaderSourceBinding,
        map_lease:&'m Eligible08MapPairLease,
    )->Result<Self,String> {
        let owner=binding.owner();
        let class=capture.class;
        if !mixed_map_header_class_allowed(owner,class) || binding!=capture.binding
            || map_lease.binding()!=&binding
            || capture.lease_identity!=Some(map_lease as *const Eligible08MapPairLease)
            || row.owner!=owner || row.class!=class {
            return Err("C450 mixed receipt owner/class/parent binding".into());
        }
        require_mixed_map_header_no_scheduled(owner, class)?;
        row.require_header_source_binding(&binding,owner,class)?;
        let cells=map_lease.checked_cells(&binding,owner,class)?;
        if cells.len()!=2*BANK53_MAP_LIVE_BITS {
            return Err("C450 mixed receipt Map cell census".into());
        }
        let base=owner.checked_mul(WIDTH)
            .ok_or("C450 mixed receipt owner base overflow")?;
        for (index,cell) in cells.iter().enumerate() {
            let context=index/BANK53_MAP_LIVE_BITS;
            let offset=index%BANK53_MAP_LIVE_BITS;
            let local=BANK53_BASE+context*BANK53_CONTEXT_BITS+offset;
            let claim=capture.claims.get(context*BANK53_CONTEXT_BITS+offset)
                .copied().flatten().ok_or("C450 mixed receipt Map claim absent")?;
            if cell.context()!=context || cell.offset()!=offset
                || cell.physical_wire()!=base+local
                || claim.author!=MixedMapHeaderAuthor::Map
                || claim.value!=cell.value() {
                return Err(format!("C450 mixed receipt typed Map claim mismatch wire{local}"));
            }
        }
        require_map_pair_packed(row.packed_bytes(),map_lease,&binding,
            owner,class)?;
        let result=Self { row,capture,binding,map_lease };
        result.validate_all(&result.binding)?;
        Ok(result)
    }

    #[cfg(test)]
    fn clone_for_test(&self)->Self {
        Self {
            row:self.row.clone(),
            capture:MixedMapHeaderCapture {
                binding:self.capture.binding.clone(),
                owner:self.capture.owner,
                class:self.capture.class,
                lease_identity:self.capture.lease_identity,
                claims:self.capture.claims.clone(),
            },
            binding:self.binding.clone(),
            map_lease:self.map_lease,
        }
    }

    pub(crate) fn row(&self)->&NativePackedRow { &self.row }
    pub(crate) fn binding(&self)->&HeaderSourceBinding { &self.binding }
    pub(crate) fn map_lease(&self)->&'m Eligible08MapPairLease { self.map_lease }
    pub(crate) fn owner(&self)->usize { self.binding.owner() }

    fn checked_binding(&self,expected:&HeaderSourceBinding)->Result<(),String> {
        if expected!=&self.binding || self.map_lease.binding()!=expected {
            return Err("C450 mixed read parent binding mismatch".into());
        }
        self.row.require_header_source_binding(expected,self.owner(),
            self.capture.class)
    }

    fn validate_all(&self,expected:&HeaderSourceBinding)->Result<(),String> {
        self.checked_binding(expected)?;
        let cells=self.map_lease.checked_cells(expected,self.owner(),self.capture.class)?;
        if cells.len()!=2*BANK53_MAP_LIVE_BITS
            || self.capture.claims.len()!=BANK53_CONTEXTS*BANK53_CONTEXT_BITS {
            return Err("C450 mixed full source census geometry".into());
        }
        let mut map_cuts=[0usize;BANK53_CONTEXTS];
        for (context,cut) in map_cuts.iter_mut().enumerate() {
            *cut=crate::bank53_required_writer::require_map_header_region_cut(
                self.owner(),context,
            )?;
            if *cut!=BANK53_MAP_LIVE_BITS {
                return Err(format!("C450 mixed source author-region cut mismatch context{context}"));
            }
        }
        let mut map_index=0usize;
        for context in 0..BANK53_CONTEXTS {
            let map_cut=map_cuts[context];
            for offset in 0..BANK53_CONTEXT_BITS {
                let index=context*BANK53_CONTEXT_BITS+offset;
                let local=BANK53_BASE+index;
                let claim=self.capture.claims[index]
                    .ok_or_else(||format!("C450 mixed full source claim absent wire{local}"))?;
                let packed=NativeHeaderSourceLease::bit(self.row.packed_bytes(),local);
                if offset<map_cut {
                    let cell=&cells[map_index];
                    if cell.context()!=context || cell.offset()!=offset
                        || claim.author!=MixedMapHeaderAuthor::Map
                        || claim.value!=cell.value() || packed!=cell.value() {
                        return Err(format!("C450 mixed full Map source mismatch wire{local}"));
                    }
                    map_index+=1;
                } else if claim.author!=MixedMapHeaderAuthor::HeaderSeed
                    || claim.value || packed {
                    return Err(format!("C450 mixed full HEADER-zero mismatch wire{local}"));
                }
            }
        }
        if map_index!=cells.len() {
            return Err("C450 mixed full Map source cardinality".into());
        }
        require_map_pair_packed(self.row.packed_bytes(),self.map_lease,expected,
            self.owner(),self.capture.class)
    }

    pub(crate) fn read_map(
        &self,expected:&HeaderSourceBinding,context:usize,offset:usize,
    )->Result<bool,String> {
        self.checked_binding(expected)?;
        if crate::bank53_required_writer::required_bank53_writer(
            self.owner(),context,offset)
            .map_err(|error|error.to_string())?
            != (crate::bank53_required_writer::RequiredWriter::Map { context }) {
            return Err("C450 mixed read expected Map writer".into());
        }
        let index=context.checked_mul(BANK53_CONTEXT_BITS)
            .and_then(|base|base.checked_add(offset))
            .filter(|index|*index<self.capture.claims.len())
            .ok_or("C450 mixed Map context/offset")?;
        let claim=self.capture.claims[index]
            .ok_or("C450 mixed Map source claim missing")?;
        if claim.author!=MixedMapHeaderAuthor::Map {
            return Err("C450 mixed Map wrong author".into());
        }
        let local=BANK53_BASE+index;
        if NativeHeaderSourceLease::bit(self.row.packed_bytes(),local)!=claim.value {
            return Err(format!("C450 mixed Map final packed mismatch wire{local}"));
        }
        Ok(claim.value)
    }

    pub(crate) fn read_header_zero(
        &self,expected:&HeaderSourceBinding,context:usize,offset:usize,
    )->Result<bool,String> {
        self.checked_binding(expected)?;
        if crate::bank53_required_writer::required_bank53_writer(
            self.owner(),context,offset)
            .map_err(|error|error.to_string())?
            != crate::bank53_required_writer::RequiredWriter::HeaderZero {
            return Err("C450 mixed read expected HEADER-zero writer".into());
        }
        let index=context.checked_mul(BANK53_CONTEXT_BITS)
            .and_then(|base|base.checked_add(offset))
            .filter(|index|*index<self.capture.claims.len())
            .ok_or("C450 mixed HEADER-zero context/offset")?;
        let claim=self.capture.claims[index]
            .ok_or("C450 mixed HEADER-zero source claim missing")?;
        let local=BANK53_BASE+index;
        if claim.author!=MixedMapHeaderAuthor::HeaderSeed || claim.value
            || NativeHeaderSourceLease::bit(self.row.packed_bytes(),local) {
            return Err(format!("C450 mixed HEADER-zero source/packed mismatch wire{local}"));
        }
        Ok(false)
    }
}
impl NativePaddingHeaderZeroRow {
    fn from_producer(
        row:NativePackedRow,capture:PaddingHeaderZeroCapture,
    )->Result<Self,String> {
        use crate::daa_history_roster::OwnerClass;
        if capture.cells.len()!=C449_PADDING_BANK53_CELLS
            || capture.cells.iter().any(|cell|*cell!=Some(false))
            || capture.owner<C449_PADDING_OWNER || capture.owner>=MAX_NATIVE_HEADERS
            || capture.binding.owner()!=capture.owner {
            return Err("C449 native padding HEADER-zero capture incomplete".into());
        }
        row.require_header_source_binding(&capture.binding,capture.owner,OwnerClass::Padding)?;
        if (BANK53_BASE..BANK53_BASE+C449_PADDING_BANK53_CELLS)
            .any(|wire|NativeHeaderSourceLease::bit(row.packed_bytes(),wire)) {
            return Err("C449 native padding HEADER-zero final packed image".into());
        }
        Ok(Self{row,capture})
    }
    pub(crate) fn row(&self)->&NativePackedRow { &self.row }
    pub(crate) fn read_header_zero(
        &self,expected:&HeaderSourceBinding,context:usize,offset:usize,
    )->Result<bool,String> {
        use crate::daa_history_roster::OwnerClass;
        use crate::bank53_required_writer::required_bank53_writer;
        let owner=self.capture.owner;
        if owner<C449_PADDING_OWNER || owner>=MAX_NATIVE_HEADERS
            || self.capture.binding.owner()!=owner {
            return Err("C460 padding HEADER-zero receipt owner binding".into());
        }
        let required=required_bank53_writer(owner,context,offset)
            .map_err(|error|error.to_owned())?;
        self.row.require_header_source_binding(expected,owner,OwnerClass::Padding)?;
        if &self.capture.binding!=expected {
            return Err("C449 padding HEADER-zero receipt parent binding".into());
        }
        let index=context.checked_mul(BANK53_CONTEXT_BITS)
            .and_then(|base|base.checked_add(offset))
            .filter(|index|*index<C449_PADDING_BANK53_CELLS)
            .ok_or("C449 padding HEADER-zero context/offset")?;
        let source_bit=self.capture.cells.get(index).copied().flatten();
        let wire=BANK53_BASE+index;
        let packed_bit=NativeHeaderSourceLease::bit(self.row.packed_bytes(),wire);
        check_padding_header_zero_observation(required,
            source_bit.map(|_|ObservedPaddingHeaderZeroAuthor::HeaderSeed),
            source_bit,packed_bit)
    }
}

/// One producer-checked physical owner row. Only the native producer can mint
/// this token in production; its private fields and lack of Clone keep an
/// unqualified bitmap out of the adjacent-owner file boundary.
pub(crate) struct CheckedOwnerSlice {
    binding: HeaderSourceBinding,
    bytes: Vec<u8>,
}
impl CheckedOwnerSlice {
    pub(crate) fn binding(&self) -> &HeaderSourceBinding { &self.binding }
    pub(crate) fn packed_bytes(&self) -> &[u8] { &self.bytes }
}

impl NativeOwnerProducer<'_> {
    /// Reconcile the ordinary Mature(Eip) ROW with the separately reconstructed
    /// complete HEADER/Tree/DAA physical image before releasing its bytes.
    pub(crate) fn checked_mature_eip_slice(&self) -> Result<CheckedOwnerSlice, String> {
        let owner = MATURE_EIP_SOURCE_OWNER;
        let binding = HeaderSourceBinding::for_plan(self.plan, owner)?;
        let row = self.produce(owner)?;
        row.require_header_source_binding(
            &binding, owner, self.roster.owner_class(owner as u64)?,
        )?;
        let resolved = NativeMatureEipResolvedSource::from_producer(self)?;
        resolved.check_complete(self.plan)?;
        if row.packed_bytes() != resolved.packed_bytes() {
            return Err("C389 Mature(Eip) complete physical source/ROW bytes".into());
        }
        Ok(CheckedOwnerSlice { binding, bytes: row.bytes })
    }

    /// Carry's token is minted only after the actual CarryZero ROW and the
    /// independent full-bit HEADER/Tree/DAA replay agree with the same batch.
    pub(crate) fn checked_carry_slice(
        &self, batch: &crate::header_daa_row_placement::Batch,
    ) -> Result<CheckedOwnerSlice, String> {
        let owner = MATURE_EIP_SOURCE_OWNER + 1;
        batch.require_owner_parent(self.plan, owner)?;
        let binding = HeaderSourceBinding::for_plan(self.plan, owner)?;
        let (row, daa) = self.produce_with_carry_zero_daa_source_lease(owner)?;
        row.require_header_source_binding(
            &binding, owner, crate::daa_history_roster::OwnerClass::Carry,
        )?;
        daa.check_carry_zero_source(&binding)?;
        let (header, counts) = self.carry_header_source_lease_for_row(batch, &row)?;
        header.check_binding(&binding)?;
        header.check_author()?;
        if counts != [565_294, 401_362, 81_920] {
            return Err("C389 Carry complete physical author counts".into());
        }
        Ok(CheckedOwnerSlice { binding, bytes: row.bytes })
    }
}

fn check_checked_owner_pair(
    first: &CheckedOwnerSlice, second: &CheckedOwnerSlice,
) -> Result<(), String> {
    if first.binding.owner != MATURE_EIP_SOURCE_OWNER
        || second.binding.owner != MATURE_EIP_SOURCE_OWNER + 1
    {
        return Err("C389 checked pair exact ordered physical owners".into());
    }
    if first.binding.root != second.binding.root
        || first.binding.total != second.binding.total
        || first.binding.profile != second.binding.profile
        || first.binding.cut != second.binding.cut
        || first.binding.layout != second.binding.layout
    {
        return Err("C389 checked pair exact parent/profile/cut/layout".into());
    }
    if first.bytes.len() != OWNER_BYTES || second.bytes.len() != OWNER_BYTES {
        return Err("C389 checked pair complete owner byte widths".into());
    }
    Ok(())
}

/// A 2^21-bit source-byte fragment, not a global X or a proof. Admission is
/// complete before create_new; the reopened file is checked byte for byte.
pub(crate) fn write_checked_owner_pair(
    path: impl AsRef<std::path::Path>,
    first: CheckedOwnerSlice,
    second: CheckedOwnerSlice,
) -> Result<crate::packed::PackedFile, String> {
    check_checked_owner_pair(&first, &second)?;
    let mut writer = crate::packed::PackedFileWriter::create_new(path, 21)?;
    writer.write_bytes(&first.bytes)?;
    writer.write_bytes(&second.bytes)?;
    let source = writer.finish()?;
    if source.read_row_bits(WIDTH, 0)? != first.bytes
        || source.read_row_bits(WIDTH, 1)? != second.bytes
    {
        return Err("C389 checked pair immutable file readback".into());
    }
    Ok(source)
}

#[cfg(test)]
mod c389_checked_owner_pair_tests {
    use super::*;

    fn synthetic(owner: usize) -> CheckedOwnerSlice {
        CheckedOwnerSlice {
            binding: HeaderSourceBinding::diagnostic_for_test(owner),
            bytes: vec![0; OWNER_BYTES],
        }
    }

    #[test]
    fn c389_no_frame_checked_pair_guards_and_file() {
        let path = std::env::temp_dir().join(format!(
            "nipopow-c389-checked-pair-{}-{}.bits",
            std::process::id(),
            std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH)
                .expect("test clock").as_nanos(),
        ));
        assert!(!path.exists(), "create-only pair destination");
        let first_owner = MATURE_EIP_SOURCE_OWNER;
        let second_owner = first_owner + 1;
        let mut faults = Vec::new();
        faults.push((synthetic(second_owner), synthetic(second_owner))); // equal bytes, duplicate owner
        faults.push((synthetic(second_owner), synthetic(first_owner))); // swapped owners
        for field in 0..5 {
            let first = synthetic(first_owner);
            let mut second = synthetic(second_owner);
            second.binding = second.binding.mutated_field_for_test(field);
            faults.push((first, second));
        }
        let mut short_first = synthetic(first_owner);
        short_first.bytes.pop();
        faults.push((short_first, synthetic(second_owner)));
        let mut short_second = synthetic(second_owner);
        short_second.bytes.pop();
        faults.push((synthetic(first_owner), short_second));
        for (first, second) in faults {
            assert!(write_checked_owner_pair(&path, first, second).is_err());
            assert!(!path.exists(), "pair guard must fail before file creation");
        }

        // This checks file geometry and byte order only; these synthetic rows
        // have no native H21 source authority.
        let mut first = synthetic(first_owner);
        let mut second = synthetic(second_owner);
        first.bytes[0] = 0x5a;
        second.bytes[0] = 0xa5;
        let expected_first = first.bytes.clone();
        let expected_second = second.bytes.clone();
        let source = write_checked_owner_pair(&path, first, second)
            .expect("create and reopen two-owner packed file");
        assert_eq!(source.input_len(), 1 << 21);
        assert_eq!(std::fs::metadata(&path).expect("pair file metadata").len(), 262_144);
        assert_eq!(source.read_row_bits(WIDTH, 0).unwrap(), expected_first);
        assert_eq!(source.read_row_bits(WIDTH, 1).unwrap(), expected_second);
        drop(source);
        std::fs::remove_file(&path).expect("remove synthetic test file");
        println!("C389_NO_FRAME_CHECKED_PAIR_GUARD_PASS mutants=9 bytes=262144 synthetic=true frame=false proof=false client=false");
    }
}

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
enum HeaderLeaseAuthor {NativeHeader,#[cfg(test)] Other}

/// One owner's actual native HEADER template bits and plan-authorized mask.
/// It carries no owner slice, publication seal or authority for other writers.
#[cfg_attr(test, derive(Clone))]
pub(crate) struct NativeHeaderSourceLease {
    binding:HeaderSourceBinding,
    author:HeaderLeaseAuthor,
    values:Vec<u8>,owned:Vec<u8>,
    #[cfg(test)] read_count:Cell<usize>,
}
impl NativeHeaderSourceLease {
    fn bit(bits:&[u8],wire:usize)->bool {(bits[wire/8]>>(wire%8))&1!=0}
    fn set(bits:&mut [u8],wire:usize) {bits[wire/8]|=1<<(wire%8);}
    pub(crate) fn check_binding(&self,expected:&HeaderSourceBinding)->Result<(),String> {
        if &self.binding!=expected {return Err("HEADER source root/total/profile/cut/layout/owner".into());}
        Ok(())
    }
    pub(crate) fn check_author(&self)->Result<(),String> {
        if self.author!=HeaderLeaseAuthor::NativeHeader {
            return Err("HEADER source author mismatch before read admission".into());
        }
        Ok(())
    }
    fn read_inner(&self,expected:&HeaderSourceBinding,physical_wire:usize,
        enforce_author:bool)->Result<Option<bool>,String> {
        self.check_binding(expected)?;
        if enforce_author && self.author!=HeaderLeaseAuthor::NativeHeader {
            return Err("HEADER source author mismatch before read admission".into());
        }
        let base=self.binding.owner.checked_mul(WIDTH).ok_or("HEADER source owner overflow")?;
        let local=physical_wire.checked_sub(base).filter(|wire|*wire<WIDTH)
            .ok_or("HEADER source physical owner")?;
        if self.values.len()!=OWNER_BYTES || self.owned.len()!=OWNER_BYTES {
            return Err("HEADER source packed width".into());
        }
        if !Self::bit(&self.owned,local){return Ok(None);}
        #[cfg(test)] self.read_count.set(self.read_count.get()+1);
        Ok(Some(Self::bit(&self.values,local)))
    }
    pub(crate) fn read_header_bit(&self,expected:&HeaderSourceBinding,
        physical_wire:usize)->Result<Option<bool>,String> {
        self.read_inner(expected,physical_wire,true)
    }
    #[cfg(test)]
    pub(crate) fn wrong_author_for_test(binding:HeaderSourceBinding,
        physical_wire:usize,value:bool)->Self {
        let mut values=vec![0;OWNER_BYTES];let mut owned=vec![0;OWNER_BYTES];
        let local=physical_wire-binding.owner*WIDTH;
        Self::set(&mut owned,local);if value {Self::set(&mut values,local);}
        Self{binding,author:HeaderLeaseAuthor::Other,values,owned,read_count:Cell::new(0)}
    }
    #[cfg(test)]
    pub(crate) fn native_author_shape_for_test(mut self)->Self {
        self.author=HeaderLeaseAuthor::NativeHeader;self
    }
    #[cfg(test)]
    pub(crate) fn read_count_for_test(&self)->usize {self.read_count.get()}
    #[cfg(test)]
    pub(crate) fn wrong_author_mutant_for_test(&mut self) {self.author=HeaderLeaseAuthor::Other;}
    #[cfg(test)]
    pub(crate) fn flip_source_value_for_test(&mut self,local:usize) {
        assert!(local<WIDTH && Self::bit(&self.owned,local));
        self.values[local/8]^=1<<(local%8);
    }
    #[cfg(test)]
    pub(crate) fn removed_author_check_mutant_for_test(&self,
        expected:&HeaderSourceBinding,physical_wire:usize)->Result<Option<bool>,String> {
        self.read_inner(expected,physical_wire,false)
    }
}

const POINT_MEMBERSHIP_OWNER: usize = 845_759;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PointMembershipSourceAuthor {
    NativePointMembership,
    #[cfg(test)] Other,
}

/// Complete immutable point-membership witness derived from one canonical
/// prefix header. ROW reads are limited to the two compressed source points.
pub(crate) struct NativePointMembershipSourceLease {
    binding: HeaderSourceBinding,
    author: PointMembershipSourceAuthor,
    owner: usize,
    height: usize,
    bits: Vec<bool>,
    #[cfg(test)] read_count: Cell<usize>,
}

impl NativePointMembershipSourceLease {
    fn from_fields(
        binding: HeaderSourceBinding,
        owner: usize,
        fields: &crate::serializer::Fields,
    ) -> Result<Self, String> {
        if owner != POINT_MEMBERSHIP_OWNER || binding.owner != owner {
            return Err("point-membership source fixed owner/binding".into());
        }
        let height = owner.checked_add(1).ok_or("point-membership source height overflow")?;
        if fields.height as usize != height {
            return Err("point-membership source header height binding".into());
        }
        let bits = crate::point_membership::witness(fields.pk, fields.w)?;
        if bits.len() != crate::point_membership::POINT_WIDTH {
            return Err("point-membership source witness width".into());
        }
        Ok(Self {
            binding,
            author: PointMembershipSourceAuthor::NativePointMembership,
            owner,
            height,
            bits,
            #[cfg(test)] read_count: Cell::new(0),
        })
    }

    pub(crate) fn check_binding(&self, expected: &HeaderSourceBinding) -> Result<(), String> {
        if &self.binding != expected || self.owner != self.binding.owner
            || self.owner != POINT_MEMBERSHIP_OWNER
            || self.height != self.owner.checked_add(1).ok_or("point-membership source height overflow")?
        {
            return Err("point-membership source root/total/profile/cut/layout/owner/header".into());
        }
        Ok(())
    }

    pub(crate) fn check_author(&self) -> Result<(), String> {
        if self.author != PointMembershipSourceAuthor::NativePointMembership {
            return Err("point-membership source author mismatch before read admission".into());
        }
        Ok(())
    }

    pub(crate) fn read_point_bit(
        &self,
        expected: &HeaderSourceBinding,
        physical_wire: usize,
    ) -> Result<bool, String> {
        self.check_binding(expected)?;
        self.check_author()?;
        let base = self.owner.checked_mul(WIDTH)
            .and_then(|wire| wire.checked_add(crate::segment_points::POINT_OFFSET))
            .ok_or("point-membership source physical base overflow")?;
        let local = physical_wire.checked_sub(base)
            .filter(|wire| (1..=2*33*8).contains(wire))
            .ok_or("point-membership source physical wire outside point input bytes")?;
        if self.bits.len() != crate::point_membership::POINT_WIDTH {
            return Err("point-membership source packed width".into());
        }
        #[cfg(test)] self.read_count.set(self.read_count.get() + 1);
        Ok(self.bits[local])
    }

    #[cfg(test)]
    pub(crate) fn mutate_binding_field_for_test(&mut self, field: usize) {
        self.binding = self.binding.mutated_field_for_test(field);
    }

    #[cfg(test)]
    pub(crate) fn wrong_author_mutant_for_test(&mut self) {
        self.author = PointMembershipSourceAuthor::Other;
    }

    #[cfg(test)]
    pub(crate) fn flip_source_value_for_test(&mut self, local: usize) {
        self.bits[local] = !self.bits[local];
    }

    #[cfg(test)]
    fn read_count_for_test(&self) -> usize { self.read_count.get() }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TreeLeaseAuthor { NativeTree, #[cfg(test)] Other }

/// Prefix-derived Tree values, minted before the physical ROW writer runs.
/// The owned mask includes every zero Tree cell and excludes HEADER endpoints.
#[cfg_attr(test, derive(Clone))]
pub(crate) struct NativeTreeSourceLease {
    binding: HeaderSourceBinding,
    author: TreeLeaseAuthor,
    values: Vec<u8>,
    owned: Vec<u8>,
}
impl NativeTreeSourceLease {
    pub(crate) fn from_prefix(
        plan: &WorkTreeHistoryPlan, input: &NativePrefix, owner: usize,
    ) -> Result<Self, String> {
        let binding = HeaderSourceBinding::for_plan(plan, owner)?;
        if binding.root != input.root() || binding.total != input.total_be28()
            || binding.profile != input.profile()
        {
            return Err("C376 Tree source canonical parent/profile".into());
        }
        let image = tree_source_image(plan, input, owner)?;
        Ok(Self {
            binding, author: TreeLeaseAuthor::NativeTree,
            values: image.values, owned: image.owned,
        })
    }
    fn check_binding(&self, expected: &HeaderSourceBinding) -> Result<(), String> {
        if &self.binding != expected {
            return Err("C376 Tree source root/total/profile/cut/layout/owner".into());
        }
        Ok(())
    }
    fn check_author(&self) -> Result<(), String> {
        if self.author != TreeLeaseAuthor::NativeTree {
            return Err("C376 Tree source author mismatch".into());
        }
        Ok(())
    }

    /// Resolve one physical Tree-owned source bit. A value at a coordinate
    /// owned by another producer is not a Tree import, even when equal.
    pub(crate) fn read_tree_bit(
        &self, expected: &HeaderSourceBinding, physical_wire: usize,
    ) -> Result<Option<bool>, String> {
        self.check_binding(expected)?;
        self.check_author()?;
        let base = self.binding.owner.checked_mul(WIDTH)
            .ok_or("Tree source owner overflow")?;
        let local = physical_wire.checked_sub(base)
            .filter(|wire| *wire < WIDTH)
            .ok_or("Tree source physical owner")?;
        if self.values.len() != OWNER_BYTES || self.owned.len() != OWNER_BYTES {
            return Err("Tree source packed width".into());
        }
        if !NativeHeaderSourceLease::bit(&self.owned, local) {
            return Ok(None);
        }
        Ok(Some(NativeHeaderSourceLease::bit(&self.values, local)))
    }
}

const MATURE_EIP_SOURCE_OWNER: usize = 844_672;
const MATURE_EIP_HEADER_CELLS: usize = 565_294;
const MATURE_EIP_TREE_CELLS: usize = 401_362;
const MATURE_EIP_DAA_CELLS: usize = 81_920;
const MATURE_EIP_MAX_CAP: std::ops::Range<usize> = 999_424..1_004_866;

fn require_no_scheduled_max_cap(owner: usize) -> Result<(), String> {
    let counts = crate::h21_scheduled_max_cap::Plan::eligible08()
        .visit_owner(owner, |_, _| Ok(()))?;
    if counts.max != [0, 0] || counts.cap != [0, 0] {
        return Err("C377 source matrix active MAX/Cap writer".into());
    }
    Ok(())
}

fn require_mature_eip_source_schedule(
    owner: usize,
    class: crate::daa_history_roster::OwnerClass,
) -> Result<(), String> {
    if owner != MATURE_EIP_SOURCE_OWNER
        || class != crate::daa_history_roster::OwnerClass::Mature(crate::daa_integer::Epoch::Eip)
    {
        return Err("C377 source matrix exact Mature(Eip) owner".into());
    }
    require_no_scheduled_max_cap(owner)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MatureEipSourceCell {
    Header(bool),
    Tree(bool),
    DaaUnresolved,
}

/// A prefix-only source partition for the first EIP mature retarget. DAA has
/// exactly a mask here: no DAA value, physical ROW, or patch is admitted.
pub(crate) struct NativeMatureEipSourceMatrix {
    binding: HeaderSourceBinding,
    class: crate::daa_history_roster::OwnerClass,
    header: NativeHeaderSourceLease,
    tree: NativeTreeSourceLease,
    daa_mask: Vec<u8>,
    daa_author: NativePhysicalAuthor,
    point_witness: Vec<bool>,
}

impl NativeMatureEipSourceMatrix {
    pub(crate) fn from_producer(producer: &NativeOwnerProducer<'_>) -> Result<Self, String> {
        let owner = MATURE_EIP_SOURCE_OWNER;
        validate_native_plan_input(producer.plan, producer.input)?;
        if producer.max_adapter.is_some() {
            return Err("C377 source matrix rejects MAX adapter".into());
        }
        #[cfg(test)]
        if producer.legacy_adapter.is_some() {
            return Err("C377 source matrix rejects legacy adapter".into());
        }
        crate::h21_scheduled_max_cap::NativeParent::checked(producer.plan, producer.input)?;
        let class = producer.roster.owner_class(owner as u64)?;
        require_mature_eip_source_schedule(owner, class)?;
        let binding = HeaderSourceBinding::for_plan(producer.plan, owner)?;
        if binding.root != producer.input.root()
            || binding.total != producer.input.total_be28()
            || binding.profile != producer.input.profile()
        {
            return Err("C377 source matrix canonical prefix binding".into());
        }
        let child_height = owner + 1;
        let child = producer.input.header(child_height)?;
        let previous = producer.input.header(owner)?;
        let leaf = producer.input.header(owner + 2)?;
        for header in [&previous, &child, &leaf] {
            if header.encode().map_err(|e| format!("C377 header encode: {e:?}"))?
                != producer.input.raw(header.height as usize)?
            {
                return Err("C377 source matrix canonical header bytes".into());
            }
        }
        let fields = crate::serializer::Fields::from_header(&child)?;
        let mut native = producer.header_template.assign(&fields)?;
        producer.header_template.assign_order(
            &mut native,
            &fields,
            previous.height,
            previous.timestamp,
            false,
        )?;
        if native.len() != WIDTH {
            return Err("C377 source matrix HEADER template width".into());
        }
        let point_witness = crate::point_membership::witness(fields.pk, fields.w)?;
        if point_witness.len() != crate::point_membership::POINT_WIDTH {
            return Err("C377 source matrix Point witness width".into());
        }
        let tree_mask = producer.plan.physical_assignment_replacement_mask(owner as u64)?;
        if tree_mask.len() != WIDTH {
            return Err("C377 source matrix Tree permission width".into());
        }
        let mut daa_mask = vec![0u8; OWNER_BYTES];
        for (start, end) in BANKS {
            for wire in start..end {
                NativeHeaderSourceLease::set(&mut daa_mask, wire);
            }
        }
        let mut header_values = vec![0u8; OWNER_BYTES];
        let mut header_owned = vec![0u8; OWNER_BYTES];
        for (wire, &value) in native.iter().enumerate() {
            if tree_mask[wire] || NativeHeaderSourceLease::bit(&daa_mask, wire) {
                continue;
            }
            if value != Fr::zero() && value != Fr::one() {
                return Err(format!("C377 source matrix non-Boolean HEADER wire{wire}"));
            }
            NativeHeaderSourceLease::set(&mut header_owned, wire);
            if value.is_one() {
                NativeHeaderSourceLease::set(&mut header_values, wire);
            }
        }
        let header = NativeHeaderSourceLease {
            binding: binding.clone(),
            author: HeaderLeaseAuthor::NativeHeader,
            values: header_values,
            owned: header_owned,
            #[cfg(test)]
            read_count: Cell::new(0),
        };
        let tree = NativeTreeSourceLease::from_prefix(producer.plan, producer.input, owner)?;
        let matrix = Self {
            binding,
            class,
            header,
            tree,
            daa_mask,
            daa_author: NativePhysicalAuthor::Daa,
            point_witness,
        };
        matrix.check_complete(producer.plan)?;
        Ok(matrix)
    }

    /// Recheck all source masks against the fixed plan. DAA remains unresolved.
    pub(crate) fn check_complete(
        &self,
        plan: &WorkTreeHistoryPlan,
    ) -> Result<[usize; 3], String> {
        let expected = HeaderSourceBinding::for_plan(plan, MATURE_EIP_SOURCE_OWNER)?;
        if self.binding != expected {
            return Err("C377 source matrix root/total/profile/cut/layout/owner".into());
        }
        require_mature_eip_source_schedule(self.binding.owner, self.class)?;
        self.header.check_binding(&expected)?;
        self.header.check_author()?;
        self.tree.check_binding(&expected)?;
        self.tree.check_author()?;
        if self.daa_author != NativePhysicalAuthor::Daa {
            return Err("C377 source matrix DAA mask author".into());
        }
        if self.header.values.len() != OWNER_BYTES
            || self.header.owned.len() != OWNER_BYTES
            || self.tree.values.len() != OWNER_BYTES
            || self.tree.owned.len() != OWNER_BYTES
            || self.daa_mask.len() != OWNER_BYTES
            || self.point_witness.len() != crate::point_membership::POINT_WIDTH
        {
            return Err("C377 source matrix packed source widths".into());
        }
        let tree_mask = plan.physical_assignment_replacement_mask(MATURE_EIP_SOURCE_OWNER as u64)?;
        if tree_mask.len() != WIDTH {
            return Err("C377 source matrix plan Tree width".into());
        }
        let mut counts = [0usize; 3];
        for wire in 0..WIDTH {
            let header = NativeHeaderSourceLease::bit(&self.header.owned, wire);
            let tree = NativeHeaderSourceLease::bit(&self.tree.owned, wire);
            let daa = NativeHeaderSourceLease::bit(&self.daa_mask, wire);
            let expected_daa = BANKS.iter().any(|&(start, end)| (start..end).contains(&wire));
            if tree != tree_mask[wire] || daa != expected_daa
                || (header as u8 + tree as u8 + daa as u8) != 1
            {
                return Err(format!("C377 source matrix gap/overlap/author wire{wire}"));
            }
            if !header && NativeHeaderSourceLease::bit(&self.header.values, wire) {
                return Err(format!("C377 source matrix HEADER value outside mask wire{wire}"));
            }
            if !tree && NativeHeaderSourceLease::bit(&self.tree.values, wire) {
                return Err(format!("C377 source matrix Tree value outside mask wire{wire}"));
            }
            if header {
                counts[0] += 1;
                if ((BANK53_BASE..BANK53_BASE + BANK53_CONTEXTS * BANK53_CONTEXT_BITS)
                    .contains(&wire)
                    || MATURE_EIP_MAX_CAP.contains(&wire))
                    && NativeHeaderSourceLease::bit(&self.header.values, wire)
                {
                    return Err(format!("C377 source matrix reserved HEADER zero wire{wire}"));
                }
                let point = crate::segment_points::POINT_OFFSET;
                if (point..point + crate::point_membership::POINT_WIDTH).contains(&wire)
                    && NativeHeaderSourceLease::bit(&self.header.values, wire)
                        != self.point_witness[wire - point]
                {
                    return Err(format!("C377 source matrix Point witness wire{wire}"));
                }
            } else if tree {
                counts[1] += 1;
                if (989_730..991_232).contains(&wire)
                    && NativeHeaderSourceLease::bit(&self.tree.values, wire)
                {
                    return Err(format!("C377 source matrix Tree pad zero wire{wire}"));
                }
            } else {
                counts[2] += 1;
            }
        }
        if counts != [MATURE_EIP_HEADER_CELLS, MATURE_EIP_TREE_CELLS, MATURE_EIP_DAA_CELLS]
            || (989_658..989_730).any(|wire| {
                !NativeHeaderSourceLease::bit(&self.header.owned, wire)
                    || NativeHeaderSourceLease::bit(&self.tree.owned, wire)
                    || NativeHeaderSourceLease::bit(&self.daa_mask, wire)
            })
        {
            return Err(format!("C377 source matrix exact counts/endpoints {counts:?}"));
        }
        Ok(counts)
    }

    pub(crate) fn source_cell(
        &self,
        expected_binding: &HeaderSourceBinding,
        physical_wire: usize,
    ) -> Result<MatureEipSourceCell, String> {
        if &self.binding != expected_binding {
            return Err("C377 source matrix read binding mismatch".into());
        }
        self.header.check_binding(expected_binding)?;
        self.header.check_author()?;
        self.tree.check_binding(expected_binding)?;
        self.tree.check_author()?;
        if self.daa_author != NativePhysicalAuthor::Daa {
            return Err("C377 source matrix read DAA author mismatch".into());
        }
        let base = self.binding.owner.checked_mul(WIDTH)
            .ok_or("C377 source matrix physical owner overflow")?;
        let local_wire = physical_wire.checked_sub(base).filter(|wire| *wire < WIDTH)
            .ok_or("C377 source matrix physical wire outside owner")?;
        let header = NativeHeaderSourceLease::bit(&self.header.owned, local_wire);
        let tree = NativeHeaderSourceLease::bit(&self.tree.owned, local_wire);
        let daa = NativeHeaderSourceLease::bit(&self.daa_mask, local_wire);
        match (header, tree, daa) {
            (true, false, false) => Ok(MatureEipSourceCell::Header(
                NativeHeaderSourceLease::bit(&self.header.values, local_wire),
            )),
            (false, true, false) => Ok(MatureEipSourceCell::Tree(
                NativeHeaderSourceLease::bit(&self.tree.values, local_wire),
            )),
            (false, false, true) => Ok(MatureEipSourceCell::DaaUnresolved),
            _ => Err(format!("C377 source matrix ambiguous local wire{local_wire}")),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MatureEipResolvedCell {
    Header(bool),
    Tree(bool),
    Daa(bool),
}

/// Physical owner 844672 assembled from its checked prefix authors. DAA may
/// read this owner's HEADER and Tree cells only after their exact shadow has
/// been constructed; no caller supplies a ROW, RAW window, or bank patch.
pub(crate) struct NativeMatureEipResolvedSource {
    matrix: NativeMatureEipSourceMatrix,
    packed: Vec<u8>,
    patch: crate::daa_history_producer::DaaBankPatch,
}

impl NativeMatureEipResolvedSource {
    fn header_tree_shadow(
        matrix: &NativeMatureEipSourceMatrix,
        plan: &WorkTreeHistoryPlan,
    ) -> Result<Vec<u8>, String> {
        matrix.check_complete(plan)?;
        let mut shadow = vec![0u8; OWNER_BYTES];
        for (byte, value) in shadow.iter_mut().enumerate() {
            let header = matrix.header.values[byte];
            let tree = matrix.tree.values[byte];
            if header & !matrix.header.owned[byte] != 0
                || tree & !matrix.tree.owned[byte] != 0
                || header & tree != 0
                || (header | tree) & matrix.daa_mask[byte] != 0
            {
                return Err(format!("C378 shadow source overlap byte{byte}"));
            }
            *value = header | tree;
        }
        Ok(shadow)
    }

    pub(crate) fn from_producer(producer: &NativeOwnerProducer<'_>) -> Result<Self, String> {
        let matrix = NativeMatureEipSourceMatrix::from_producer(producer)?;
        let owner = MATURE_EIP_SOURCE_OWNER;
        let class = producer.roster.owner_class(owner as u64)?;
        require_mature_eip_source_schedule(owner, class)?;
        let mut packed = Self::header_tree_shadow(&matrix, producer.plan)?;
        let original = packed.clone();
        let schedule = crate::daa_header_window::for_child_height((owner + 1) as u32)?;
        let samples = schedule.sample_heights().iter()
            .map(|&height| producer.input.raw(height as usize))
            .collect::<Result<Vec<_>, _>>()?;
        let raw = crate::daa_history_producer::RawWindow {
            parent: producer.input.raw(owner)?,
            child: producer.input.raw(owner + 1)?,
            samples: &samples,
        };
        let (receipt, patch) = crate::daa_history_producer::write_retarget_with_patch(
            &producer.roster,
            owner as u64,
            raw,
            &mut packed,
            |wire| producer.exports.bit(wire),
        )?;
        if receipt.owner != owner as u64 || receipt.class != class
            || receipt.patched_bytes != crate::daa_history_producer::PATCH_BYTES
            || patch.identity() != (owner as u64, class)
        {
            return Err("C378 DAA writer receipt/patch identity".into());
        }
        for byte in 0..OWNER_BYTES {
            if (original[byte] ^ packed[byte]) & !matrix.daa_mask[byte] != 0 {
                return Err(format!("C378 DAA writer changed non-DAA byte{byte}"));
            }
        }
        let source = Self { matrix, packed, patch };
        source.check_complete(producer.plan)?;
        Ok(source)
    }

    /// Recheck the whole physical image before promotion to a ROW consumer.
    pub(crate) fn check_complete(&self, plan: &WorkTreeHistoryPlan) -> Result<(), String> {
        self.matrix.check_complete(plan)?;
        if self.packed.len() != OWNER_BYTES
            || self.patch.identity() != (MATURE_EIP_SOURCE_OWNER as u64, self.matrix.class)
        {
            return Err("C378 resolved width/DAA patch owner/class".into());
        }
        for byte in 0..OWNER_BYTES {
            let expected = self.matrix.header.values[byte] | self.matrix.tree.values[byte];
            if (self.packed[byte] ^ expected) & !self.matrix.daa_mask[byte] != 0 {
                return Err(format!("C378 resolved Header/Tree mismatch byte{byte}"));
            }
        }
        for (start, end) in BANKS {
            for wire in start..end {
                let patch = self.patch.read_bank_bit(wire)?
                    .ok_or("C378 resolved DAA patch missing bank bit")?;
                if patch != (self.packed[wire / 8] >> (wire % 8) & 1 != 0) {
                    return Err(format!("C378 resolved DAA image/patch mismatch wire{wire}"));
                }
            }
        }
        Ok(())
    }

    pub(crate) fn source_cell(
        &self,
        expected_binding: &HeaderSourceBinding,
        physical_wire: usize,
    ) -> Result<MatureEipResolvedCell, String> {
        if self.patch.identity() != (MATURE_EIP_SOURCE_OWNER as u64, self.matrix.class) {
            return Err("C378 resolved DAA patch owner/class".into());
        }
        let cell = self.matrix.source_cell(expected_binding, physical_wire)?;
        let local = physical_wire - MATURE_EIP_SOURCE_OWNER * WIDTH;
        let packed = self.packed.get(local / 8)
            .ok_or("C378 resolved physical image outside owner")?;
        let value = packed >> (local % 8) & 1 != 0;
        match cell {
            MatureEipSourceCell::Header(source) if source == value => {
                Ok(MatureEipResolvedCell::Header(value))
            }
            MatureEipSourceCell::Tree(source) if source == value => {
                Ok(MatureEipResolvedCell::Tree(value))
            }
            MatureEipSourceCell::DaaUnresolved
                if self.patch.read_bank_bit(local)? == Some(value) => {
                    Ok(MatureEipResolvedCell::Daa(value))
                }
            _ => Err(format!("C378 resolved physical author/value mismatch wire{local}")),
        }
    }

    pub(crate) fn packed_bytes(&self) -> &[u8] { &self.packed }
}

/// Physical writers are distinct from ROW relations: a DAA lane may read a
/// Tree-owned Work endpoint in another owner. Only producer leases mint cells.
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) enum NativeTypedAuthor { Header, Tree, Daa }

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) struct NativeAuthoredCell {
    wire:usize,author:NativeTypedAuthor,value:bool,
}
impl NativeAuthoredCell {
    pub(crate) fn wire(&self)->usize {self.wire}
    pub(crate) fn author(&self)->NativeTypedAuthor {self.author}
    pub(crate) fn value(&self)->bool {self.value}
    #[cfg(test)]
    pub(crate) fn with_author_for_test(mut self,author:NativeTypedAuthor)->Self {
        self.author=author;self
    }
}

#[derive(Clone)]
enum NativeTypedSource<'a> {
    MatureEip(&'a NativeMatureEipResolvedSource),
    CarryForeignTreeWork {cells:Vec<(usize,bool)>,author:NativeTypedAuthor},
    MatureForeignSerializer {cells:Vec<(usize,bool)>,author:NativeTypedAuthor},
}

/// Source and destination share the complete parent/profile/cut/layout, but
/// keep separate physical owners. No caller can supply an author in production.
#[derive(Clone)]
pub(crate) struct NativeTypedAuthorLease<'a> {
    destination:HeaderSourceBinding,source:HeaderSourceBinding,
    kind:NativeTypedSource<'a>,
}
impl NativeMatureEipResolvedSource {
    pub(crate) fn typed_author_lease(
        &self,destination:&HeaderSourceBinding,
    )->Result<NativeTypedAuthorLease<'_>,String> {
        if destination!=&self.matrix.binding || destination.owner!=MATURE_EIP_SOURCE_OWNER {
            return Err("typed Mature(Eip) destination/source identity".into());
        }
        Ok(NativeTypedAuthorLease{destination:destination.clone(),
            source:self.matrix.binding.clone(),kind:NativeTypedSource::MatureEip(self)})
    }
}
impl NativeTypedAuthorLease<'_> {
    pub(crate) fn source_owner(&self)->usize {self.source.owner}
    pub(crate) fn check_binding(
        &self,plan:&WorkTreeHistoryPlan,destination:&HeaderSourceBinding,
    )->Result<(),String> {
        if &self.destination!=destination
            || self.destination!=HeaderSourceBinding::for_plan(plan,destination.owner)?
            || self.source!=HeaderSourceBinding::for_plan(plan,self.source.owner)?
            || self.source.root!=destination.root || self.source.total!=destination.total
            || self.source.profile!=destination.profile || self.source.cut!=destination.cut
            || self.source.layout!=destination.layout {
            return Err("typed author source/destination parent/profile/cut/layout/owner".into());
        }
        match &self.kind {
            NativeTypedSource::MatureEip(source) => {
                if self.source.owner!=MATURE_EIP_SOURCE_OWNER
                    || destination.owner!=MATURE_EIP_SOURCE_OWNER
                    || source.matrix.binding!=self.source {
                    return Err("typed Mature(Eip) source owner".into());
                }
                source.check_complete(plan)?;
            }
            NativeTypedSource::CarryForeignTreeWork{cells,author} => {
                if destination.owner!=MATURE_EIP_SOURCE_OWNER+1
                    || ![MATURE_EIP_SOURCE_OWNER-1,MATURE_EIP_SOURCE_OWNER]
                        .contains(&self.source.owner)
                    || *author!=NativeTypedAuthor::Tree || cells.len()!=224 {
                    return Err("typed Carry foreign Tree Work author/owner/census".into());
                }
                let base=self.source.owner.checked_mul(WIDTH)
                    .ok_or("typed Carry source owner overflow")?;
                for (bit,&(wire,_)) in cells.iter().enumerate() {
                    if wire!=base+987_674+bit {
                        return Err("typed Carry foreign Tree Work missing/duplicate coordinate".into());
                    }
                }
            }
            NativeTypedSource::MatureForeignSerializer{cells,author} => {
                if destination.owner!=MATURE_EIP_SOURCE_OWNER
                    || *author!=NativeTypedAuthor::Header {
                    return Err("typed Mature serializer destination/author".into());
                }
                let expected=mature_foreign_serializer_wires(plan,self.source.owner)?;
                if cells.len()!=expected.len()
                    || cells.iter().map(|&(wire,_)|wire).ne(expected.into_iter()) {
                    return Err("typed Mature serializer exact source coordinates".into());
                }
            }
        }
        Ok(())
    }
    pub(crate) fn read_cell(
        &self,destination:&HeaderSourceBinding,wire:usize,
    )->Result<Option<NativeAuthoredCell>,String> {
        if &self.destination!=destination || wire/WIDTH!=self.source.owner {
            return Err("typed author read destination/source physical owner".into());
        }
        let (author,value)=match &self.kind {
            NativeTypedSource::MatureEip(source) => match source.source_cell(&self.source,wire)? {
                MatureEipResolvedCell::Header(value)=>(NativeTypedAuthor::Header,value),
                MatureEipResolvedCell::Tree(value)=>(NativeTypedAuthor::Tree,value),
                MatureEipResolvedCell::Daa(value)=>(NativeTypedAuthor::Daa,value),
            },
            NativeTypedSource::CarryForeignTreeWork{cells,author} => {
                let local=wire%WIDTH;
                if !(987_674..987_898).contains(&local) {return Ok(None);}
                let (actual,value)=cells[local-987_674];
                if actual!=wire {return Err("typed Carry foreign Tree Work coordinate".into());}
                (*author,value)
            }
            NativeTypedSource::MatureForeignSerializer{cells,author} => {
                match cells.binary_search_by_key(&wire,|(at,_)|*at) {
                    Ok(index)=>(*author,cells[index].1),
                    Err(_)=>return Ok(None),
                }
            }
        };
        Ok(Some(NativeAuthoredCell{wire,author,value}))
    }

    #[cfg(test)]
    pub(crate) fn synthetic_carry_for_test(destination:HeaderSourceBinding,
        source_owner:usize)->Self {
        let mut source=destination.clone();source.owner=source_owner;
        Self{destination,source,kind:NativeTypedSource::CarryForeignTreeWork{
            cells:(0..224).map(|bit|(source_owner*WIDTH+987_674+bit,false)).collect(),
            author:NativeTypedAuthor::Tree}}
    }
    #[cfg(test)]
    pub(crate) fn synthetic_mature_serializer_for_test(
        plan:&WorkTreeHistoryPlan,destination:HeaderSourceBinding,source_owner:usize,
    )->Self {
        let source=HeaderSourceBinding::for_plan(plan,source_owner).unwrap();
        let cells=mature_foreign_serializer_wires(plan,source_owner).unwrap()
            .into_iter().map(|wire|(wire,false)).collect();
        Self{destination,source,kind:NativeTypedSource::MatureForeignSerializer{
            cells,author:NativeTypedAuthor::Header}}
    }
    #[cfg(test)]
    pub(crate) fn wrong_author_for_test(&mut self) {
        if let NativeTypedSource::CarryForeignTreeWork{author,..}=&mut self.kind {
            *author=NativeTypedAuthor::Header;
        } else if let NativeTypedSource::MatureForeignSerializer{author,..}=&mut self.kind {
            *author=NativeTypedAuthor::Daa;
        }
    }
    #[cfg(test)]
    pub(crate) fn wrong_parent_for_test(&mut self) {self.source.root[0]^=1;}
    #[cfg(test)]
    pub(crate) fn wrong_source_owner_for_test(&mut self) {self.source.owner+=1;}
    #[cfg(test)]
    pub(crate) fn missing_cell_for_test(&mut self) {
        if let NativeTypedSource::CarryForeignTreeWork{cells,..}=&mut self.kind {cells.pop();}
        else if let NativeTypedSource::MatureForeignSerializer{cells,..}=&mut self.kind {cells.pop();}
    }
    #[cfg(test)]
    pub(crate) fn duplicate_cell_for_test(&mut self) {
        if let NativeTypedSource::CarryForeignTreeWork{cells,..}=&mut self.kind {
            cells.push(cells[0]);
        } else if let NativeTypedSource::MatureForeignSerializer{cells,..}=&mut self.kind {
            cells.push(cells[0]);
        }
    }
}

/// Exact EIP alias source coordinates for one of the nine preceding headers.
/// This is a geometry check, not a value or author certificate.
fn mature_foreign_serializer_wires(
    plan:&WorkTreeHistoryPlan,source_owner:usize,
)->Result<Vec<usize>,String> {
    const SOURCES:[usize;9]=[
        843_647,843_775,843_903,844_031,844_159,844_287,844_415,844_543,844_671,
    ];
    const COUNTS:[usize;9]=[64,128,96,96,96,96,96,96,96];
    if plan.headers()!=1_827_840 || plan.slot_log()!=21
        || source_owner>=MATURE_EIP_SOURCE_OWNER {
        return Err("typed Mature serializer source owner/plan".into());
    }
    let source_index=SOURCES.iter().position(|&owner|owner==source_owner)
        .ok_or("typed Mature serializer exact source roster")?;
    let schedule=crate::daa_header_window::for_child_height(
        (MATURE_EIP_SOURCE_OWNER+1) as u32)?;
    if schedule.action()!=crate::daa_header_window::Action::Retarget(
        crate::daa_integer::Epoch::Eip)
        || schedule.sample_heights().len()!=SOURCES.len()
        || schedule.sample_heights().iter().zip(SOURCES).any(|(&height,owner)|
            height as usize!=owner+1) {
        return Err("typed Mature serializer exact native sample-owner schedule".into());
    }
    let ports=crate::daa_schedule_wiring::DaaScheduleWiring::compile()?;
    let all=ports.ports(crate::daa_integer::Epoch::Eip);
    if all.len()!=896 {return Err("typed Mature serializer exact EIP ports".into());}
    let mut wires=Vec::new();
    for port in all {
        let offset=usize::try_from(port.offset(crate::daa_integer::Epoch::Eip))
            .map_err(|_|"typed Mature serializer offset width")?;
        if offset==0 {continue;}
        let owner=MATURE_EIP_SOURCE_OWNER.checked_sub(offset)
            .ok_or("typed Mature serializer source underflow")?;
        if owner==source_owner {
            let local=crate::header_hash::SERIALIZER_OFFSET
                .checked_add(port.serializer_wire())
                .ok_or("typed Mature serializer local coordinate overflow")?;
            if local>=WIDTH {return Err("typed Mature serializer local coordinate".into());}
            wires.push(owner.checked_mul(WIDTH).and_then(|base|base.checked_add(local))
                .ok_or("typed Mature serializer physical coordinate overflow")?);
        }
    }
    let emitted=wires.len();
    wires.sort_unstable();
    wires.dedup();
    if emitted!=COUNTS[source_index] || wires.len()!=COUNTS[source_index] {
        return Err("typed Mature serializer source census/duplicate".into());
    }
    Ok(wires)
}

fn check_mature_serializer_three_way(
    header:bool,exported:bool,packed:bool,
)->Result<(),String> {
    if header!=exported || header!=packed {
        return Err("typed Mature serializer HEADER/export/packed value".into());
    }
    Ok(())
}

#[cfg(test)]
mod c397_serializer_value_tests {
    use super::*;

    #[test]
    fn no_frame_three_way_equal_zero_value_faults() {
        assert!(check_mature_serializer_three_way(false,false,false).is_ok());
        assert!(check_mature_serializer_three_way(false,true,false).is_err());
        assert!(check_mature_serializer_three_way(false,false,true).is_err());
        assert!(check_mature_serializer_three_way(true,false,true).is_err());
    }
}

#[cfg(test)]
pub(crate) mod c377_mature_eip_source_matrix_tests {
    use super::*;

    fn fixture() -> (WorkTreeHistoryPlan, NativeMatureEipSourceMatrix) {
        // This fixture checks the source partition, not a native history.
        let plan = WorkTreeHistoryPlan::compile(
            1_827_840, 21, [0x5a; 32], [0x42; 28],
        ).unwrap();
        let binding = HeaderSourceBinding::for_plan(&plan, MATURE_EIP_SOURCE_OWNER).unwrap();
        let permission = plan
            .physical_assignment_replacement_mask(MATURE_EIP_SOURCE_OWNER as u64)
            .unwrap();
        let mut header_owned = vec![0u8; OWNER_BYTES];
        let mut tree_owned = vec![0u8; OWNER_BYTES];
        let mut daa_mask = vec![0u8; OWNER_BYTES];
        for wire in 0..WIDTH {
            if BANKS.iter().any(|&(start, end)| (start..end).contains(&wire)) {
                NativeHeaderSourceLease::set(&mut daa_mask, wire);
            } else if permission[wire] {
                NativeHeaderSourceLease::set(&mut tree_owned, wire);
            } else {
                NativeHeaderSourceLease::set(&mut header_owned, wire);
            }
        }
        let matrix = NativeMatureEipSourceMatrix {
            binding: binding.clone(),
            class: crate::daa_history_roster::OwnerClass::Mature(crate::daa_integer::Epoch::Eip),
            header: NativeHeaderSourceLease {
                binding: binding.clone(),
                author: HeaderLeaseAuthor::NativeHeader,
                values: vec![0; OWNER_BYTES],
                owned: header_owned,
                read_count: Cell::new(0),
            },
            tree: NativeTreeSourceLease {
                binding,
                author: TreeLeaseAuthor::NativeTree,
                values: vec![0; OWNER_BYTES],
                owned: tree_owned,
            },
            daa_mask,
            daa_author: NativePhysicalAuthor::Daa,
            point_witness: vec![false; crate::point_membership::POINT_WIDTH],
        };
        (plan, matrix)
    }

    fn copy(source: &NativeMatureEipSourceMatrix) -> NativeMatureEipSourceMatrix {
        NativeMatureEipSourceMatrix {
            binding: source.binding.clone(),
            class: source.class,
            header: NativeHeaderSourceLease {
                binding: source.header.binding.clone(),
                author: source.header.author,
                values: source.header.values.clone(),
                owned: source.header.owned.clone(),
                read_count: Cell::new(0),
            },
            tree: NativeTreeSourceLease {
                binding: source.tree.binding.clone(),
                author: source.tree.author,
                values: source.tree.values.clone(),
                owned: source.tree.owned.clone(),
            },
            daa_mask: source.daa_mask.clone(),
            daa_author: source.daa_author,
            point_witness: source.point_witness.clone(),
        }
    }

    fn reject_one(
        plan: &WorkTreeHistoryPlan,
        base: &NativeMatureEipSourceMatrix,
        mutate: impl FnOnce(&mut NativeMatureEipSourceMatrix),
    ) {
        let mut altered = copy(base);
        mutate(&mut altered);
        assert!(altered.check_complete(plan).is_err());
    }

    #[test]
    fn c377_three_exact_masks_and_unresolved_daa_source() {
        let (plan, mut matrix) = fixture();
        assert_eq!(matrix.check_complete(&plan).unwrap(), [565_294, 401_362, 81_920]);
        let physical_base = MATURE_EIP_SOURCE_OWNER * WIDTH;
        assert_eq!(matrix.source_cell(&matrix.binding, physical_base + BANKS[0].0).unwrap(), MatureEipSourceCell::DaaUnresolved);
        assert_eq!(matrix.source_cell(&matrix.binding, physical_base + BANK53_BASE).unwrap(), MatureEipSourceCell::Header(false));
        assert_eq!(matrix.source_cell(&matrix.binding, physical_base + 989_658).unwrap(), MatureEipSourceCell::Header(false));
        assert_eq!(matrix.source_cell(&matrix.binding, physical_base + 989_730).unwrap(), MatureEipSourceCell::Tree(false));
        assert!(matrix.source_cell(&matrix.binding, physical_base + WIDTH).is_err());
        // The Point window is HEADER-owned even when its independent value is one.
        let point = crate::segment_points::POINT_OFFSET;
        matrix.point_witness[0] = true;
        NativeHeaderSourceLease::set(&mut matrix.header.values, point);
        assert_eq!(matrix.check_complete(&plan).unwrap(), [565_294, 401_362, 81_920]);
        assert_eq!(matrix.source_cell(&matrix.binding, physical_base + point).unwrap(), MatureEipSourceCell::Header(true));
    }

    #[test]
    fn c377_gap_overlap_daa_shift_and_wrong_authors_fail() {
        let (plan, base) = fixture();
        assert_eq!(base.check_complete(&plan).unwrap(), [565_294, 401_362, 81_920]);
        let header_zero = BANK53_BASE;
        reject_one(&plan, &base, |m| m.header.owned[header_zero / 8] &= !(1 << (header_zero % 8)));
        reject_one(&plan, &base, |m| NativeHeaderSourceLease::set(&mut m.tree.owned, header_zero));
        reject_one(&plan, &base, |m| {
            let first = BANKS[0].0;
            m.daa_mask[first / 8] &= !(1 << (first % 8));
            NativeHeaderSourceLease::set(&mut m.daa_mask, BANK53_BASE);
        });
        reject_one(&plan, &base, |m| m.header.author = HeaderLeaseAuthor::Other);
        reject_one(&plan, &base, |m| m.tree.author = TreeLeaseAuthor::Other);
        reject_one(&plan, &base, |m| m.daa_author = NativePhysicalAuthor::Bank53);
        let physical_base = MATURE_EIP_SOURCE_OWNER * WIDTH;
        let header_zero_physical = physical_base + header_zero;
        let mut wrong_header = copy(&base);
        wrong_header.header.author = HeaderLeaseAuthor::Other;
        assert!(wrong_header.source_cell(&base.binding, header_zero_physical).is_err());
        let mut wrong_tree = copy(&base);
        wrong_tree.tree.author = TreeLeaseAuthor::Other;
        assert!(wrong_tree.source_cell(&base.binding, physical_base + 989_730).is_err());
        let mut wrong_daa = copy(&base);
        wrong_daa.daa_author = NativePhysicalAuthor::Bank53;
        assert!(wrong_daa.source_cell(&base.binding, physical_base + BANKS[0].0).is_err());
        let mut missing_zero = copy(&base);
        missing_zero.header.owned[header_zero / 8] &= !(1 << (header_zero % 8));
        assert!(missing_zero.source_cell(&base.binding, header_zero_physical).is_err());
        let mut duplicate_zero = copy(&base);
        NativeHeaderSourceLease::set(&mut duplicate_zero.tree.owned, header_zero);
        assert!(duplicate_zero.source_cell(&base.binding, header_zero_physical).is_err());
    }

    #[test]
    fn c377_reserved_values_pad_endpoints_and_point_witness_fail() {
        let (plan, base) = fixture();
        reject_one(&plan, &base, |m| NativeHeaderSourceLease::set(&mut m.header.values, BANK53_BASE));
        reject_one(&plan, &base, |m| NativeHeaderSourceLease::set(&mut m.header.values, MATURE_EIP_MAX_CAP.start));
        reject_one(&plan, &base, |m| NativeHeaderSourceLease::set(&mut m.header.values, crate::segment_points::POINT_OFFSET));
        reject_one(&plan, &base, |m| NativeHeaderSourceLease::set(&mut m.tree.values, 989_730));
        reject_one(&plan, &base, |m| NativeHeaderSourceLease::set(&mut m.tree.owned, 989_658));
    }

    #[test]
    fn c377_parent_schedule_and_adjacent_owner_fail() {
        let (plan, base) = fixture();
        for field in 0..6 {
            reject_one(&plan, &base, |m| m.binding = m.binding.mutated_field_for_test(field));
        }
        reject_one(&plan, &base, |m| m.header.binding.root[0] ^= 1);
        reject_one(&plan, &base, |m| m.tree.binding.cut.push(0));
        reject_one(&plan, &base, |m| m.class = crate::daa_history_roster::OwnerClass::Carry);
        assert!(require_no_scheduled_max_cap(844_670).is_err());
        assert!(require_mature_eip_source_schedule(
            844_673,
            crate::daa_history_roster::OwnerClass::Mature(crate::daa_integer::Epoch::Eip),
        ).is_err());
        let physical_base = MATURE_EIP_SOURCE_OWNER * WIDTH;
        let same_zero = physical_base + BANK53_BASE;
        assert_eq!(base.source_cell(&base.binding, same_zero).unwrap(), MatureEipSourceCell::Header(false));
        assert!(base.source_cell(&base.binding, same_zero - WIDTH).is_err());
        assert!(base.source_cell(&base.binding, same_zero + WIDTH).is_err());
        let wrong_binding = base.binding.mutated_field_for_test(0);
        assert!(base.source_cell(&wrong_binding, same_zero).is_err());
        assert!(base.source_cell(&base.binding, usize::MAX).is_err());
    }

    pub(crate) fn resolved_fixture() -> (WorkTreeHistoryPlan, NativeMatureEipResolvedSource) {
        let (plan, matrix) = fixture();
        let packed = NativeMatureEipResolvedSource::header_tree_shadow(&matrix, &plan).unwrap();
        let patch = crate::daa_history_producer::DaaBankPatch::zero_for_test(
            MATURE_EIP_SOURCE_OWNER as u64, matrix.class,
        );
        (plan, NativeMatureEipResolvedSource { matrix, packed, patch })
    }

    #[test]
    fn c378_shadow_and_resolved_three_authors_have_exact_physical_reads() {
        let (plan, mut source) = resolved_fixture();
        let base = MATURE_EIP_SOURCE_OWNER * WIDTH;
        assert_eq!(source.packed_bytes().len(), OWNER_BYTES);
        source.check_complete(&plan).unwrap();
        assert_eq!(source.source_cell(&source.matrix.binding, base + BANK53_BASE).unwrap(),
            MatureEipResolvedCell::Header(false));
        assert_eq!(source.source_cell(&source.matrix.binding, base + 989_730).unwrap(),
            MatureEipResolvedCell::Tree(false));
        assert_eq!(source.source_cell(&source.matrix.binding, base + BANKS[0].0).unwrap(),
            MatureEipResolvedCell::Daa(false));

        let point = crate::segment_points::POINT_OFFSET;
        source.matrix.point_witness[0] = true;
        NativeHeaderSourceLease::set(&mut source.matrix.header.values, point);
        NativeHeaderSourceLease::set(&mut source.packed, point);
        let tree = (0..WIDTH).find(|&wire| {
            NativeHeaderSourceLease::bit(&source.matrix.tree.owned, wire)
                && !(989_730..991_232).contains(&wire)
        }).unwrap();
        NativeHeaderSourceLease::set(&mut source.matrix.tree.values, tree);
        NativeHeaderSourceLease::set(&mut source.packed, tree);
        source.check_complete(&plan).unwrap();
        assert_eq!(source.source_cell(&source.matrix.binding, base + point).unwrap(),
            MatureEipResolvedCell::Header(true));
        assert_eq!(source.source_cell(&source.matrix.binding, base + tree).unwrap(),
            MatureEipResolvedCell::Tree(true));
        let wrong = source.matrix.binding.mutated_field_for_test(0);
        assert!(source.source_cell(&wrong, base + point).is_err());
        assert!(source.source_cell(&source.matrix.binding, base + WIDTH).is_err());
        assert!(source.source_cell(&source.matrix.binding, base - 1).is_err());
    }

    #[test]
    fn c378_shadow_values_and_physical_author_mutants_fail_closed() {
        let (plan, mut source) = resolved_fixture();
        source.packed[BANK53_BASE / 8] ^= 1 << (BANK53_BASE % 8);
        assert!(source.check_complete(&plan).is_err());
        let (_, mut source) = resolved_fixture();
        let tree = (0..WIDTH).find(|&wire|
            NativeHeaderSourceLease::bit(&source.matrix.tree.owned, wire)).unwrap();
        source.packed[tree / 8] ^= 1 << (tree % 8);
        assert!(source.check_complete(&plan).is_err());
        let (_, mut source) = resolved_fixture();
        NativeHeaderSourceLease::set(&mut source.packed, BANKS[0].0);
        assert!(source.check_complete(&plan).is_err());
        let (_, mut source) = resolved_fixture();
        source.patch.flip_first_bit_for_test();
        assert!(source.check_complete(&plan).is_err());
        let (_, mut source) = resolved_fixture();
        source.patch.shift_first_bank_for_test();
        assert!(source.check_complete(&plan).is_err());
        let (_, mut source) = resolved_fixture();
        source.patch.wrong_owner_for_test();
        assert!(source.check_complete(&plan).is_err());
        let (_, mut source) = resolved_fixture();
        source.matrix.daa_author = NativePhysicalAuthor::Bank53;
        assert!(source.check_complete(&plan).is_err());
        let (_, mut source) = resolved_fixture();
        source.matrix.tree.author = TreeLeaseAuthor::Other;
        assert!(source.check_complete(&plan).is_err());
    }
}

/// Local custody of the actual physical writes for the fixed Eligible08 owner.
/// It is not a proof or a commitment: only the fully checked sibling producer
/// can mint it, and each read remains bound to that producer's packed row.
pub(crate) struct NativeOwnerAuthorCensus {
    complete_checked: Cell<bool>,
    binding: HeaderSourceBinding,
    authors: Vec<Option<NativePhysicalAuthor>>,
    source_bits: Vec<u8>,
    bank53_source: Bank53TypedSourceLease,
    header_source: NativeHeaderSourceLease,
    point_source: NativePointMembershipSourceLease,
    tree_source: NativeTreeSourceLease,
}
impl NativeOwnerAuthorCensus {
    fn bit(bytes: &[u8], wire: usize) -> bool {
        (bytes[wire / 8] >> (wire % 8)) & 1 != 0
    }

    fn check_row_identity(
        &self, expected: &HeaderSourceBinding, row: &NativePackedRow,
    ) -> Result<(), String> {
        if &self.binding != expected || self.binding.owner != POINT_MEMBERSHIP_OWNER
            || row.owner != self.binding.owner
            || row.root != self.binding.root || row.total != self.binding.total
            || row.class != crate::daa_history_roster::OwnerClass::Carry
            || row.header_source_binding.as_ref() != Some(expected)
            || row.max_binding.is_some() || row.map_binding.is_some()
            || row.map_context.is_some() || row.bytes.len() != OWNER_BYTES
        {
            return Err("C374 census exact owner/parent/row binding".into());
        }
        #[cfg(test)]
        if row.legacy_binding.is_some() {
            return Err("C374 census rejects legacy row".into());
        }
        Ok(())
    }

    fn expected_author(&self, wire: usize) -> NativePhysicalAuthor {
        if (crate::segment_points::POINT_OFFSET
            ..crate::segment_points::POINT_OFFSET + crate::point_membership::POINT_WIDTH)
            .contains(&wire)
        {
            NativePhysicalAuthor::PointMembership
        } else if BANKS.iter().any(|&(start, end)| (start..end).contains(&wire)) {
            NativePhysicalAuthor::Daa
        } else if (BANK53_BASE..BANK53_BASE + BANK53_CONTEXTS * BANK53_CONTEXT_BITS)
            .contains(&wire)
        {
            NativePhysicalAuthor::Bank53
        } else if (FIRST_MODERN_CAP0_BASE..FIRST_MODERN_CAP0_BASE + FIRST_MODERN_CAP0_CELLS)
            .contains(&wire)
            || (FIRST_MODERN_CAP1_BASE..FIRST_MODERN_CAP1_BASE + FIRST_MODERN_CAP1_CELLS)
                .contains(&wire)
        {
            NativePhysicalAuthor::Cap
        } else if Self::bit(&self.header_source.owned, wire) {
            NativePhysicalAuthor::Header
        } else {
            NativePhysicalAuthor::Tree
        }
    }

    /// One full scan at construction or a deciding consumer join. In addition
    /// to exact counts, this checks the independent HEADER and Point leases,
    /// the complete source-value image and every byte of the packed row.
    pub(crate) fn check_complete(
        &self, expected: &HeaderSourceBinding, row: &NativePackedRow,
    ) -> Result<(), String> {
        self.complete_checked.set(false);
        self.check_row_identity(expected, row)?;
        self.header_source.check_binding(expected)?;
        self.header_source.check_author()?;
        self.point_source.check_binding(expected)?;
        self.point_source.check_author()?;
        self.tree_source.check_binding(expected)?;
        self.tree_source.check_author()?;
        if self.authors.len() != WIDTH || self.source_bits.len() != OWNER_BYTES
            || self.header_source.owned.len() != OWNER_BYTES
            || self.header_source.values.len() != OWNER_BYTES
            || self.point_source.bits.len() != crate::point_membership::POINT_WIDTH
            || self.tree_source.owned.len() != OWNER_BYTES
            || self.tree_source.values.len() != OWNER_BYTES
        {
            return Err("C374 census complete source widths".into());
        }
        let cap0 = row.cap0_source.as_ref().ok_or("C374 census missing Cap0 source")?;
        let cap1 = row.cap1_source.as_ref().ok_or("C374 census missing Cap1 source")?;
        cap0.validate_domain(row.owner)?;
        cap1.validate_domain(row.owner)?;
        if cap0.binding() != expected || cap1.binding() != expected {
            return Err("C374 census Cap parent binding".into());
        }
        self.bank53_source.validate(expected, row.owner)?;
        let bank53_base = row.owner.checked_mul(WIDTH).ok_or("C375 census Bank53 owner base")?;
        for entry in self.bank53_source.entries() {
            let wire = entry.physical_wire().checked_sub(bank53_base)
                .filter(|wire| *wire < WIDTH).ok_or("C375 census Bank53 physical wire")?;
            if self.authors[wire] != Some(NativePhysicalAuthor::Bank53)
                || Self::bit(&self.source_bits, wire) != entry.value()
                || Self::bit(&row.bytes, wire) != entry.value() {
                return Err(format!("C375 census Bank53 typed source/packed wire{wire}"));
            }
        }
        for source in [cap0.cells(), cap1.cells()] {
            for &(wire, value) in source {
                if !matches!(self.authors[wire], Some(NativePhysicalAuthor::Cap))
                    || Self::bit(&self.source_bits, wire) != value
                {
                    return Err(format!("C374 census Cap source/value wire{wire}"));
                }
            }
        }
        let mut counts = [0usize; 6];
        for wire in 0..WIDTH {
            let author = self.authors[wire]
                .ok_or_else(|| format!("C374 census missing physical author wire{wire}"))?;
            if author != self.expected_author(wire) {
                return Err(format!("C374 census physical author geometry wire{wire}"));
            }
            let tree_owned = Self::bit(&self.tree_source.owned, wire);
            let tree_value = Self::bit(&self.tree_source.values, wire);
            if tree_owned != (author == NativePhysicalAuthor::Tree) {
                return Err(format!("C376 census Tree exclusive source mask wire{wire}"));
            }
            if !tree_owned && tree_value {
                return Err(format!("C376 census Tree value outside source mask wire{wire}"));
            }
            counts[author.index()] += 1;
            let value = Self::bit(&self.source_bits, wire);
            if value != Self::bit(&row.bytes, wire) {
                return Err(format!("C374 census source/packed bit mismatch wire{wire}"));
            }
            match author {
                NativePhysicalAuthor::Header
                    if value != Self::bit(&self.header_source.values, wire) => {
                        return Err(format!("C374 census HEADER source/packed wire{wire}"));
                    }
                NativePhysicalAuthor::PointMembership
                    if value != self.point_source.bits[wire - crate::segment_points::POINT_OFFSET] => {
                        return Err(format!("C374 census Point source/packed wire{wire}"));
                    }
                NativePhysicalAuthor::Tree if value != tree_value => {
                        return Err(format!("C376 census Tree source/packed wire{wire}"));
                    }
                NativePhysicalAuthor::Daa if value => {
                    return Err(format!("C374 census CarryZero DAA wire{wire}"));
                }
                _ => {}
            }
        }
        if counts != [536_622, 8_192, 401_362, 81_920, 16_384, 4_096] {
            return Err(format!("C374 census six exact physical counts {counts:?}"));
        }
        if self.authors[989_658..989_730].iter()
            .any(|author| *author != Some(NativePhysicalAuthor::Header))
        {
            return Err("C374 census 72 protected HEADER endpoints".into());
        }
        self.complete_checked.set(true);
        Ok(())
    }

    /// Bind a retained Map source to this already checked physical census.
    /// The opaque source identity prevents an equal detached sink from lending
    /// its Map terms or values to this producer's row.
    pub(crate) fn require_map_view(
        &self, expected: &HeaderSourceBinding, row: &NativePackedRow,
        view: &h21_eligible_context::Eligible08MapSourceView<'_>,
    ) -> Result<(), String> {
        if !self.complete_checked.get() {
            return Err("C453 Map read requires complete physical census".into());
        }
        self.check_row_identity(expected, row)?;
        if self.bank53_source.binding() != expected
            || self.bank53_source.entries().len() != BANK53_CONTEXTS * BANK53_CONTEXT_BITS
        {
            return Err("C453 Map read typed lease binding/width".into());
        }
        view.require_typed_source(&self.bank53_source)
    }

    /// O(1) typed Map read after the full census check. Both a zero and a one
    /// require the actual Bank53 claim, retained typed Map(context) custody,
    /// and agreement of source and final packed bits.
    pub(crate) fn checked_map_cell(
        &self, expected: &HeaderSourceBinding, row: &NativePackedRow,
        view: &h21_eligible_context::Eligible08MapSourceView<'_>,
        context: usize, physical_wire: usize,
    ) -> Result<(h21_eligible_context::Bank53TypedAuthor, bool), String> {
        use h21_eligible_context::Bank53TypedAuthor;
        self.require_map_view(expected, row, view)?;
        if context >= BANK53_CONTEXTS {
            return Err("C453 Map read context outside domain".into());
        }
        let base = self.binding.owner.checked_mul(WIDTH)
            .ok_or("C453 Map read owner base")?;
        let wire = physical_wire.checked_sub(base).filter(|wire| *wire < WIDTH)
            .ok_or("C453 Map read physical wire outside owner")?;
        let index = wire.checked_sub(BANK53_BASE)
            .filter(|index| *index < BANK53_CONTEXTS * BANK53_CONTEXT_BITS)
            .ok_or("C453 Map read physical wire outside Bank53")?;
        if index / BANK53_CONTEXT_BITS != context
            || crate::bank53_required_writer::required_bank53_writer(
                self.binding.owner, context, index % BANK53_CONTEXT_BITS)
                != Ok(crate::bank53_required_writer::RequiredWriter::Map { context })
        {
            return Err("C453 Map read required context/author".into());
        }
        let entry = &self.bank53_source.entries()[index];
        if entry.physical_wire() != physical_wire
            || entry.author() != Bank53TypedAuthor::Map(context)
        {
            return Err("C453 Map read typed wire/context/author".into());
        }
        let (author, value) = self.checked_cell(expected, row, physical_wire)?;
        if author != NativePhysicalAuthor::Bank53 || entry.value() != value {
            return Err("C453 Map read physical author/source/packed".into());
        }
        Ok((entry.author(), value))
    }

    /// Bind the retained modern Score/Slack source to this already checked
    /// physical census. This view is minted by the completed sink; equal
    /// bindings or equal values cannot substitute for its source custody.
    pub(crate) fn require_complete_row_view(
        &self, expected: &HeaderSourceBinding, row: &NativePackedRow,
        view: &h21_eligible_context::Eligible08CompleteRowSourceView<'_>,
    ) -> Result<(), String> {
        if !self.complete_checked.get() {
            return Err("C455 Score/Slack read requires complete physical census".into());
        }
        self.check_row_identity(expected, row)?;
        if self.bank53_source.binding() != expected
            || self.bank53_source.entries().len() != BANK53_CONTEXTS * BANK53_CONTEXT_BITS
            || view.binding() != expected
        {
            return Err("C455 Score/Slack read typed lease/view binding or width".into());
        }
        view.require_typed_source(&self.bank53_source)
    }

    /// O(1) typed modern Score/Slack read after the full physical census.
    /// Both a zero and a one require the selected owner's actual Bank53 claim,
    /// exact modern Score or context Slack authorship, retained sink custody,
    /// and agreement among typed source, source image, and packed row.
    pub(crate) fn checked_score_slack_cell(
        &self, expected: &HeaderSourceBinding, row: &NativePackedRow,
        view: &h21_eligible_context::Eligible08CompleteRowSourceView<'_>,
        context: usize, physical_wire: usize,
    ) -> Result<(h21_eligible_context::Bank53TypedAuthor, bool), String> {
        use h21_eligible_context::{Bank53TypedAuthor, ScoreReplayAuthor};
        self.require_complete_row_view(expected, row, view)?;
        if context >= BANK53_CONTEXTS {
            return Err("C455 Score/Slack read context outside domain".into());
        }
        let base = self.binding.owner.checked_mul(WIDTH)
            .ok_or("C455 Score/Slack read owner base")?;
        let wire = physical_wire.checked_sub(base).filter(|wire| *wire < WIDTH)
            .ok_or("C455 Score/Slack read physical wire outside owner")?;
        let index = wire.checked_sub(BANK53_BASE)
            .filter(|index| *index < BANK53_CONTEXTS * BANK53_CONTEXT_BITS)
            .ok_or("C455 Score/Slack read physical wire outside Bank53")?;
        if index / BANK53_CONTEXT_BITS != context {
            return Err("C455 Score/Slack read physical context mismatch".into());
        }
        let offset = index % BANK53_CONTEXT_BITS;
        let required = crate::bank53_required_writer::required_bank53_writer(
            self.binding.owner, context, offset,
        ).map_err(|error| format!("C455 Score/Slack required writer: {error}"))?;
        let expected_author = match required {
            crate::bank53_required_writer::RequiredWriter::ScoreReplay {
                context: required_context,
                endpoint: crate::bank53_required_writer::ScoreEndpointKind::FirstModern,
            } if required_context == context => Bank53TypedAuthor::Score(ScoreReplayAuthor {
                context,
                origin: POINT_MEMBERSHIP_OWNER + 1,
                previous_owner: POINT_MEMBERSHIP_OWNER - 1,
                max_owner: 844_670,
                cap_owner: POINT_MEMBERSHIP_OWNER,
            }),
            crate::bank53_required_writer::RequiredWriter::Slack { context: required_context }
                if required_context == context => Bank53TypedAuthor::Slack(context),
            _ => return Err("C455 Score/Slack read required Bank53 writer".into()),
        };
        let entry = &self.bank53_source.entries()[index];
        if entry.physical_wire() != physical_wire || entry.author() != expected_author {
            return Err("C455 Score/Slack read typed wire/context/author".into());
        }
        let (author, value) = self.checked_cell(expected, row, physical_wire)?;
        if author != NativePhysicalAuthor::Bank53 || entry.value() != value {
            return Err("C455 Score/Slack read physical author/source/packed".into());
        }
        if matches!(expected_author, Bank53TypedAuthor::Slack(_)) && value {
            return Err("C455 Score/Slack read nonzero Slack source".into());
        }
        Ok((entry.author(), value))
    }

    /// O(1) physical read after the complete census was sealed by the producer.
    pub(crate) fn checked_cell(
        &self, expected: &HeaderSourceBinding, row: &NativePackedRow,
        physical_wire: usize,
    ) -> Result<(NativePhysicalAuthor, bool), String> {
        self.check_row_identity(expected, row)?;
        self.tree_source.check_binding(expected)?;
        self.tree_source.check_author()?;
        if self.authors.len() != WIDTH || self.source_bits.len() != OWNER_BYTES {
            return Err("C374 census read width".into());
        }
        let base = self.binding.owner.checked_mul(WIDTH).ok_or("C374 census owner base")?;
        let wire = physical_wire.checked_sub(base).filter(|wire| *wire < WIDTH)
            .ok_or("C374 census physical wire outside owner")?;
        let author = self.authors[wire]
            .ok_or_else(|| format!("C374 census read missing physical author wire{wire}"))?;
        let value = Self::bit(&self.source_bits, wire);
        if value != Self::bit(&row.bytes, wire) {
            return Err(format!("C374 census read source/packed mismatch wire{wire}"));
        }
        if author == NativePhysicalAuthor::Tree
            && (self.tree_source.values.len() != OWNER_BYTES
                || self.tree_source.owned.len() != OWNER_BYTES
                || !Self::bit(&self.tree_source.owned, wire)
                || value != Self::bit(&self.tree_source.values, wire))
        {
            return Err(format!("C376 census read Tree source/packed wire{wire}"));
        }
        Ok((author, value))
    }
}

#[cfg(test)]
mod c374_author_census_tests {
    use super::*;

    // A tiny-authority synthetic row exercises the census admission boundary
    // without reading the real 1.3 GB frame or claiming a valid history.
    fn fixture() -> (HeaderSourceBinding, NativePackedRow, NativeOwnerAuthorCensus) {
        fixture_with_binding(HeaderSourceBinding::diagnostic_for_test(POINT_MEMBERSHIP_OWNER))
    }

    pub(super) fn fixture_with_binding(binding: HeaderSourceBinding)
        -> (HeaderSourceBinding, NativePackedRow, NativeOwnerAuthorCensus) {
        let owner = POINT_MEMBERSHIP_OWNER;
        let mut authors = vec![None; WIDTH];
        let mut header_owned = vec![0u8; OWNER_BYTES];
        let mut tree_owned = vec![0u8; OWNER_BYTES];
        let mut ordinary_header_left = 536_622 - 72;
        for wire in 0..WIDTH {
            let author = if (crate::segment_points::POINT_OFFSET
                ..crate::segment_points::POINT_OFFSET + crate::point_membership::POINT_WIDTH)
                .contains(&wire)
            {
                NativePhysicalAuthor::PointMembership
            } else if BANKS.iter().any(|&(start, end)| (start..end).contains(&wire)) {
                NativePhysicalAuthor::Daa
            } else if (BANK53_BASE..BANK53_BASE + BANK53_CONTEXTS * BANK53_CONTEXT_BITS)
                .contains(&wire)
            {
                NativePhysicalAuthor::Bank53
            } else if (FIRST_MODERN_CAP0_BASE..FIRST_MODERN_CAP0_BASE + FIRST_MODERN_CAP0_CELLS)
                .contains(&wire)
                || (FIRST_MODERN_CAP1_BASE..FIRST_MODERN_CAP1_BASE + FIRST_MODERN_CAP1_CELLS)
                    .contains(&wire)
            {
                NativePhysicalAuthor::Cap
            } else if (989_658..989_730).contains(&wire) {
                NativePhysicalAuthor::Header
            } else if ordinary_header_left > 0 {
                ordinary_header_left -= 1;
                NativePhysicalAuthor::Header
            } else {
                NativePhysicalAuthor::Tree
            };
            if author == NativePhysicalAuthor::Header {
                NativeHeaderSourceLease::set(&mut header_owned, wire);
            } else if author == NativePhysicalAuthor::Tree {
                NativeHeaderSourceLease::set(&mut tree_owned, wire);
            }
            authors[wire] = Some(author);
        }
        assert_eq!(ordinary_header_left, 0);
        let cap0 = NativeCap0Source::synthetic_for_test(
            binding.clone(),
            (FIRST_MODERN_CAP0_BASE..FIRST_MODERN_CAP0_BASE + FIRST_MODERN_CAP0_CELLS)
                .map(|wire| (wire, false)).collect(),
        );
        let cap1 = NativeCap1Source::synthetic_for_test(
            binding.clone(),
            (FIRST_MODERN_CAP1_BASE..FIRST_MODERN_CAP1_BASE + FIRST_MODERN_CAP1_CELLS)
                .map(|wire| (wire, false)).collect(),
        );
        let row = NativePackedRow {
            owner,
            class: crate::daa_history_roster::OwnerClass::Carry,
            root: binding.root,
            total: binding.total,
            bytes: vec![0; OWNER_BYTES],
            header_source_binding: Some(binding.clone()),
            cap0_source: Some(cap0),
            cap1_source: Some(cap1),
            max_binding: None,
            map_binding: None,
            map_context: None,
            legacy_binding: None,
        };
        let census = NativeOwnerAuthorCensus {
            complete_checked: Cell::new(false),
            binding: binding.clone(),
            authors,
            source_bits: vec![0; OWNER_BYTES],
            bank53_source: Bank53TypedSourceLease::synthetic_for_test(
                binding.clone(), owner).unwrap(),
            header_source: NativeHeaderSourceLease {
                binding: binding.clone(),
                author: HeaderLeaseAuthor::NativeHeader,
                values: vec![0; OWNER_BYTES],
                owned: header_owned,
                read_count: Cell::new(0),
            },
            point_source: NativePointMembershipSourceLease {
                binding: binding.clone(),
                author: PointMembershipSourceAuthor::NativePointMembership,
                owner,
                height: owner + 1,
                bits: vec![false; crate::point_membership::POINT_WIDTH],
                read_count: Cell::new(0),
            },
            tree_source: NativeTreeSourceLease {
                binding: binding.clone(),
                author: TreeLeaseAuthor::NativeTree,
                values: vec![0; OWNER_BYTES],
                owned: tree_owned,
            },
        };
        (binding, row, census)
    }

    #[test]
    fn c374_missing_point_equal_cross_author_and_independent_point_bits_fail() {
        let (binding, row, mut census) = fixture();
        let owner = POINT_MEMBERSHIP_OWNER;
        census.check_complete(&binding, &row).unwrap();
        let base = POINT_MEMBERSHIP_OWNER * WIDTH;
        assert_eq!(
            census.checked_cell(&binding, &row, base + crate::segment_points::POINT_OFFSET)
                .unwrap(),
            (NativePhysicalAuthor::PointMembership, false),
        );
        let missing = crate::segment_points::POINT_OFFSET + 528;
        census.authors[missing] = None;
        assert!(census.check_complete(&binding, &row).unwrap_err().contains("missing physical author"));
        census.authors[missing] = Some(NativePhysicalAuthor::PointMembership);
        for bit in [0usize, 8_061] {
            census.point_source.bits[bit] = true;
            assert!(census.check_complete(&binding, &row).unwrap_err().contains("Point source/packed"));
            census.point_source.bits[bit] = false;
        }

        let mut rows = OwnedRows::new(OwnerSelection::Single {
            owner,
            class: crate::daa_history_roster::OwnerClass::Carry,
        });
        rows.begin_author_census().unwrap();
        rows.set_author(NativePhysicalAuthor::Header).unwrap();
        for (wire, value) in [(17usize, Fr::zero()), (18, Fr::one())] {
            rows.claim(owner, wire, value).unwrap();
        }
        rows.set_author(NativePhysicalAuthor::Tree).unwrap();
        for (wire, value) in [(17usize, Fr::zero()), (18, Fr::one())] {
            assert!(rows.claim(owner, wire, value).unwrap_err().contains("cross-author duplicate"));
            assert_eq!(rows.values[0][wire], value);
            assert_eq!(rows.author_census.as_ref().unwrap()[wire], Some(NativePhysicalAuthor::Header));
        }
    }

    #[test]
    fn c374_protected_endpoints_and_parent_are_fail_closed() {
        let (binding, mut row, mut census) = fixture();
        census.check_complete(&binding, &row).unwrap();
        assert_eq!(crate::work_tree_layout::Endpoints::new().used, 6_690);
        let endpoint = 989_658;
        census.authors[endpoint] = Some(NativePhysicalAuthor::Tree);
        assert!(census.check_complete(&binding, &row).unwrap_err().contains("physical author geometry"));
        census.authors[endpoint] = Some(NativePhysicalAuthor::Header);
        let wrong = binding.mutated_field_for_test(0);
        assert!(census.check_complete(&wrong, &row).unwrap_err().contains("owner/parent/row binding"));
        row.bytes[endpoint / 8] ^= 1 << (endpoint % 8);
        assert!(census.check_complete(&binding, &row).unwrap_err().contains("source/packed"));
    }

    #[test]
    fn c375_bank53_typed_source_rejects_bit_duplicate_retag_and_parent_mutants() {
        let (binding, row, mut changed_bit) = fixture();
        changed_bit.bank53_source.mutate_entry_for_test(0, None, None, Some(true));
        assert!(changed_bit.check_complete(&binding, &row).unwrap_err()
            .contains("C375 census Bank53 typed source/packed"));

        let (binding, row, mut duplicate) = fixture();
        let first_wire = duplicate.bank53_source.entries()[0].physical_wire();
        duplicate.bank53_source.mutate_entry_for_test(1, Some(first_wire), None, None);
        assert!(duplicate.check_complete(&binding, &row).unwrap_err()
            .contains("C375 Bank53 exact geometry/typed domain"));

        let (binding, row, mut retagged) = fixture();
        retagged.bank53_source.mutate_entry_for_test(0, None,
            Some(super::h21_eligible_context::Bank53TypedAuthor::Slack(1)), None);
        assert!(retagged.check_complete(&binding, &row).unwrap_err()
            .contains("C375 Bank53 exact geometry/typed domain"));

        let (binding, row, mut wrong_parent) = fixture();
        wrong_parent.bank53_source.mutate_binding_for_test(0);
        assert!(wrong_parent.check_complete(&binding, &row).unwrap_err()
            .contains("C375 Bank53 typed lease parent/owner/census"));
    }

    #[test]
    fn c376_tree_source_zero_mask_retag_parent_and_duplicate_zero_fail() {
        let (binding, row, census) = fixture();
        census.check_complete(&binding, &row).unwrap();
        let wire = fixed::NODE_CORE;
        assert_eq!(census.authors[wire], Some(NativePhysicalAuthor::Tree));
        assert!(!NativeOwnerAuthorCensus::bit(&census.tree_source.values, wire));

        let (binding, row, mut changed_zero) = fixture();
        NativeHeaderSourceLease::set(&mut changed_zero.tree_source.values, wire);
        assert!(changed_zero.check_complete(&binding, &row).unwrap_err()
            .contains("C376 census Tree source/packed"));

        let (binding, row, mut missing_zero) = fixture();
        missing_zero.tree_source.owned[wire / 8] &= !(1 << (wire % 8));
        assert!(missing_zero.check_complete(&binding, &row).unwrap_err()
            .contains("C376 census Tree exclusive source mask"));

        let (binding, row, mut retagged) = fixture();
        retagged.tree_source.author = TreeLeaseAuthor::Other;
        assert!(retagged.check_complete(&binding, &row).unwrap_err()
            .contains("C376 Tree source author mismatch"));

        for field in 0..6 {
            let (binding, row, mut wrong_parent) = fixture();
            wrong_parent.tree_source.binding = binding.mutated_field_for_test(field);
            assert!(wrong_parent.check_complete(&binding, &row).unwrap_err()
                .contains("C376 Tree source root/total/profile/cut/layout/owner"));
        }

        let owner = POINT_MEMBERSHIP_OWNER;
        let mut rows = OwnedRows::new(OwnerSelection::Single {
            owner, class: crate::daa_history_roster::OwnerClass::Carry,
        });
        rows.begin_author_census().unwrap();
        rows.set_author(NativePhysicalAuthor::Tree).unwrap();
        rows.claim(owner, wire, Fr::zero()).unwrap();
        assert!(rows.claim(owner, wire, Fr::zero()).unwrap_err()
            .contains("C376 Tree duplicate claim"));
    }

    #[test]
    fn c453_map_census_zero_author_claim_and_value_no_frame() {
        use h21_eligible_context::{Bank53TypedAuthor, Eligible08OwnerSink};
        let sink = Eligible08OwnerSink::synthetic_map_source_for_test();
        let view = sink.map_source_view_for_test().unwrap();
        let (binding, mut row, mut census) = fixture_with_binding(view.binding().clone());
        census.bank53_source = view.typed_source_for_test().unwrap();
        let base = POINT_MEMBERSHIP_OWNER * WIDTH;
        let local = BANK53_BASE;
        let physical = base + local;
        assert!(census.checked_map_cell(&binding, &row, &view, 0, physical)
            .unwrap_err().contains("requires complete"));
        census.check_complete(&binding, &row).unwrap();
        for context in 0..BANK53_CONTEXTS {
            assert_eq!(census.checked_map_cell(&binding, &row, &view, context,
                base + BANK53_BASE + context * BANK53_CONTEXT_BITS).unwrap(),
                (Bank53TypedAuthor::Map(context), false));
        }
        for wrong_author in [Some(NativePhysicalAuthor::Header), None] {
            census.authors[local] = wrong_author;
            assert!(census.checked_map_cell(&binding, &row, &view, 0, physical).is_err());
            census.authors[local] = Some(NativePhysicalAuthor::Bank53);
        }
        let original_author = census.bank53_source.entries()[0].author();
        let score_author = census.bank53_source.entries()[crate::bank53_map::MAP_LIVE].author();
        for wrong_author in [Bank53TypedAuthor::Map(1), score_author, Bank53TypedAuthor::Slack(0)] {
            census.bank53_source.mutate_entry_for_test(0, None, Some(wrong_author), None);
            assert!(census.checked_map_cell(&binding, &row, &view, 0, physical)
                .unwrap_err().contains("typed wire/context/author"));
        }
        census.bank53_source.mutate_entry_for_test(0, None, Some(original_author), Some(true));
        assert!(census.checked_map_cell(&binding, &row, &view, 0, physical)
            .unwrap_err().contains("physical author/source/packed"));
        census.bank53_source.mutate_entry_for_test(0, None, None, Some(false));
        census.source_bits[local / 8] ^= 1 << (local % 8);
        assert!(census.checked_map_cell(&binding, &row, &view, 0, physical)
            .unwrap_err().contains("source/packed mismatch"));
        census.source_bits[local / 8] ^= 1 << (local % 8);
        row.bytes[local / 8] ^= 1 << (local % 8);
        assert!(census.checked_map_cell(&binding, &row, &view, 0, physical)
            .unwrap_err().contains("source/packed mismatch"));
        assert!(census.check_complete(&binding, &row).is_err());
        row.bytes[local / 8] ^= 1 << (local % 8);
        assert!(census.checked_map_cell(&binding, &row, &view, 0, physical)
            .unwrap_err().contains("requires complete"));
        census.check_complete(&binding, &row).unwrap();
        assert_eq!(census.checked_map_cell(&binding, &row, &view, 0, physical).unwrap(),
            (Bank53TypedAuthor::Map(0), false));
    }

    #[test]
    fn c453_map_census_identity_domains_and_work_tree_no_frame() {
        use h21_eligible_context::Eligible08OwnerSink;
        let sink = Eligible08OwnerSink::synthetic_map_source_for_test();
        let view = sink.map_source_view_for_test().unwrap();
        let (binding, row, mut census) = fixture_with_binding(view.binding().clone());
        census.bank53_source = view.typed_source_for_test().unwrap();
        census.check_complete(&binding, &row).unwrap();
        let base = POINT_MEMBERSHIP_OWNER * WIDTH;
        let physical = base + BANK53_BASE;
        let detached_sink = Eligible08OwnerSink::synthetic_map_source_for_test();
        let detached_view = detached_sink.map_source_view_for_test().unwrap();
        assert_eq!(view.binding(), detached_view.binding());
        assert!(census.checked_map_cell(&binding, &row, &detached_view, 0, physical)
            .unwrap_err().contains("retained sink/source custody"));
        for context in [1, BANK53_CONTEXTS, usize::MAX] {
            assert!(census.checked_map_cell(&binding, &row, &view, context, physical).is_err());
        }
        for wire in [base - 1, base + WIDTH, base + BANK53_BASE - 1,
            physical + crate::bank53_map::MAP_LIVE,
            physical + crate::bank53_slack::SLACK_INPUT_START] {
            assert!(census.checked_map_cell(&binding, &row, &view, 0, wire).is_err());
        }
        for field in 0..6 {
            assert!(census.checked_map_cell(&binding.mutated_field_for_test(field),
                &row, &view, 0, physical).is_err());
        }
        let work_local = 987_674;
        assert_eq!(census.checked_cell(&binding, &row, base + work_local).unwrap(),
            (NativePhysicalAuthor::Tree, false));
        census.authors[work_local] = Some(NativePhysicalAuthor::Header);
        assert_ne!(census.checked_cell(&binding, &row, base + work_local).unwrap().0,
            NativePhysicalAuthor::Tree);
        census.authors[work_local] = None;
        assert!(census.checked_cell(&binding, &row, base + work_local).is_err());
        census.authors[work_local] = Some(NativePhysicalAuthor::Tree);
        census.tree_source.owned[work_local / 8] &= !(1 << (work_local % 8));
        assert!(census.checked_cell(&binding, &row, base + work_local)
            .unwrap_err().contains("Tree source/packed"));
    }

    fn c455_fixture_for_view(
        view: &h21_eligible_context::Eligible08CompleteRowSourceView<'_>,
    ) -> (HeaderSourceBinding, NativePackedRow, NativeOwnerAuthorCensus) {
        let map_view = view.map_view();
        let (binding, row, mut census) = fixture_with_binding(view.binding().clone());
        census.bank53_source = map_view.typed_source_for_test().unwrap();
        (binding, row, census)
    }

    fn c455_score_author(context: usize) -> h21_eligible_context::Bank53TypedAuthor {
        h21_eligible_context::Bank53TypedAuthor::Score(
            h21_eligible_context::ScoreReplayAuthor {
                context,
                origin: POINT_MEMBERSHIP_OWNER + 1,
                previous_owner: POINT_MEMBERSHIP_OWNER - 1,
                max_owner: 844_670,
                cap_owner: POINT_MEMBERSHIP_OWNER,
            },
        )
    }

    fn c455_set_bit(bytes: &mut [u8], wire: usize, value: bool) {
        let mask = 1u8 << (wire % 8);
        if value {
            bytes[wire / 8] |= mask;
        } else {
            bytes[wire / 8] &= !mask;
        }
    }

    #[test]
    fn c455_score_slack_reader_requires_complete_census_and_retained_custody_no_frame() {
        use h21_eligible_context::{Bank53TypedAuthor, Eligible08OwnerSink};
        let sink = Eligible08OwnerSink::synthetic_map_source_for_test();
        let view = sink.local_source_view_for_test().unwrap();
        let (binding, row, mut census) = c455_fixture_for_view(&view);
        let base = POINT_MEMBERSHIP_OWNER * WIDTH;
        let score_index = crate::bank53_map::MAP_LIVE;
        let score_local = BANK53_BASE + score_index;
        let score_wire = base + score_local;
        let slack_index = crate::bank53_slack::SLACK_INPUT_START;
        let slack_local = BANK53_BASE + slack_index;
        let slack_wire = base + slack_local;

        assert!(census.checked_score_slack_cell(&binding, &row, &view, 0, score_wire)
            .unwrap_err().contains("requires complete"));
        census.check_complete(&binding, &row).unwrap();
        assert_eq!(census.checked_score_slack_cell(&binding, &row, &view, 0, score_wire)
            .unwrap(), (c455_score_author(0), false));
        assert_eq!(census.checked_score_slack_cell(&binding, &row, &view, 0, slack_wire)
            .unwrap(), (Bank53TypedAuthor::Slack(0), false));

        let context_one_score = base + BANK53_BASE + BANK53_CONTEXT_BITS + score_index;
        assert_eq!(census.checked_score_slack_cell(&binding, &row, &view, 1,
            context_one_score).unwrap(), (c455_score_author(1), false));
        assert!(census.checked_score_slack_cell(&binding, &row, &view, 1, score_wire).is_err());
        for context in [BANK53_CONTEXTS, usize::MAX] {
            assert!(census.checked_score_slack_cell(&binding, &row, &view,
                context, score_wire).is_err());
        }
        for wire in [base - 1, base + WIDTH, base + BANK53_BASE - 1] {
            assert!(census.checked_score_slack_cell(&binding, &row, &view, 0, wire).is_err());
        }

        let detached_sink = Eligible08OwnerSink::synthetic_map_source_for_test();
        let detached = detached_sink.local_source_view_for_test().unwrap();
        assert_eq!(view.binding(), detached.binding());
        assert!(census.checked_score_slack_cell(&binding, &row, &detached, 0, score_wire)
            .unwrap_err().to_ascii_lowercase().contains("custody"));
        for field in 0..6 {
            assert!(census.checked_score_slack_cell(&binding.mutated_field_for_test(field),
                &row, &view, 0, score_wire).is_err());
        }
    }

    #[test]
    fn c455_score_slack_reader_rejects_wrong_policy_and_missing_claim_no_frame() {
        use h21_eligible_context::{Bank53TypedAuthor, Eligible08OwnerSink, ScoreReplayAuthor};
        let sink = Eligible08OwnerSink::synthetic_map_source_for_test();
        let view = sink.local_source_view_for_test().unwrap();
        let (binding, row, mut census) = c455_fixture_for_view(&view);
        census.check_complete(&binding, &row).unwrap();
        let base = POINT_MEMBERSHIP_OWNER * WIDTH;
        let score_index = crate::bank53_map::MAP_LIVE;
        let score_local = BANK53_BASE + score_index;
        let score_wire = base + score_local;
        let slack_index = crate::bank53_slack::SLACK_INPUT_START;
        let slack_wire = base + BANK53_BASE + slack_index;
        let original_score = census.bank53_source.entries()[score_index].author();
        let wrong_score_authors = [
            Bank53TypedAuthor::Map(0),
            Bank53TypedAuthor::Slack(0),
            Bank53TypedAuthor::Score(ScoreReplayAuthor {
                context: 1, origin: POINT_MEMBERSHIP_OWNER + 1,
                previous_owner: POINT_MEMBERSHIP_OWNER - 1,
                max_owner: 844_670, cap_owner: POINT_MEMBERSHIP_OWNER,
            }),
            Bank53TypedAuthor::Score(ScoreReplayAuthor {
                context: 0, origin: POINT_MEMBERSHIP_OWNER,
                previous_owner: POINT_MEMBERSHIP_OWNER - 1,
                max_owner: 844_670, cap_owner: POINT_MEMBERSHIP_OWNER,
            }),
            Bank53TypedAuthor::Score(ScoreReplayAuthor {
                context: 0, origin: POINT_MEMBERSHIP_OWNER + 1,
                previous_owner: POINT_MEMBERSHIP_OWNER - 2,
                max_owner: 844_670, cap_owner: POINT_MEMBERSHIP_OWNER,
            }),
            Bank53TypedAuthor::Score(ScoreReplayAuthor {
                context: 0, origin: POINT_MEMBERSHIP_OWNER + 1,
                previous_owner: POINT_MEMBERSHIP_OWNER - 1,
                max_owner: 844_671, cap_owner: POINT_MEMBERSHIP_OWNER,
            }),
            Bank53TypedAuthor::Score(ScoreReplayAuthor {
                context: 0, origin: POINT_MEMBERSHIP_OWNER + 1,
                previous_owner: POINT_MEMBERSHIP_OWNER - 1,
                max_owner: 844_670, cap_owner: POINT_MEMBERSHIP_OWNER - 1,
            }),
        ];
        for wrong in wrong_score_authors {
            census.bank53_source.mutate_entry_for_test(score_index, None, Some(wrong), None);
            assert!(census.checked_score_slack_cell(&binding, &row, &view, 0, score_wire).is_err());
        }
        census.bank53_source.mutate_entry_for_test(score_index, None, Some(original_score), None);

        let map_wire = base + BANK53_BASE;
        assert!(census.checked_score_slack_cell(&binding, &row, &view, 0, map_wire)
            .unwrap_err().contains("required Bank53 writer"));
        // A HEADER-zero claim cannot stand in for an equal-valued modern cell.
        census.authors[score_local] = Some(NativePhysicalAuthor::Header);
        assert!(census.checked_score_slack_cell(&binding, &row, &view, 0, score_wire).is_err());
        census.authors[score_local] = Some(NativePhysicalAuthor::Bank53);
        census.authors[score_local] = None;
        assert!(census.checked_score_slack_cell(&binding, &row, &view, 0, score_wire).is_err());
        census.authors[score_local] = Some(NativePhysicalAuthor::Bank53);

        let original_wire = census.bank53_source.entries()[score_index].physical_wire();
        census.bank53_source.mutate_entry_for_test(score_index,
            Some(score_wire + 1), None, None);
        assert!(census.checked_score_slack_cell(&binding, &row, &view, 0, score_wire).is_err());
        census.bank53_source.mutate_entry_for_test(score_index, Some(original_wire), None, None);

        let original_slack = census.bank53_source.entries()[slack_index].author();
        for wrong in [Bank53TypedAuthor::Slack(1), c455_score_author(0)] {
            census.bank53_source.mutate_entry_for_test(slack_index, None, Some(wrong), None);
            assert!(census.checked_score_slack_cell(&binding, &row, &view, 0, slack_wire).is_err());
        }
        census.bank53_source.mutate_entry_for_test(slack_index, None, Some(original_slack), None);
    }

    #[test]
    fn c455_score_slack_reader_requires_source_packed_agreement_and_zero_slack_no_frame() {
        use h21_eligible_context::{Bank53TypedAuthor, Eligible08OwnerSink};
        let sink = Eligible08OwnerSink::synthetic_map_source_for_test();
        let view = sink.local_source_view_for_test().unwrap();
        let (binding, mut row, mut census) = c455_fixture_for_view(&view);
        census.check_complete(&binding, &row).unwrap();
        let base = POINT_MEMBERSHIP_OWNER * WIDTH;
        let score_index = crate::bank53_map::MAP_LIVE;
        let score_local = BANK53_BASE + score_index;
        let score_wire = base + score_local;
        let score_mask = 1u8 << (score_local % 8);

        // Synthetic local mechanics only: all three copies are changed
        // together to show that a typed modern Score one is readable.
        census.bank53_source.mutate_entry_for_test(score_index, None, None, Some(true));
        c455_set_bit(&mut census.source_bits, score_local, true);
        c455_set_bit(&mut row.bytes, score_local, true);
        assert_eq!(census.checked_score_slack_cell(&binding, &row, &view, 0, score_wire)
            .unwrap(), (c455_score_author(0), true));
        census.bank53_source.mutate_entry_for_test(score_index, None, None, Some(false));
        c455_set_bit(&mut census.source_bits, score_local, false);
        c455_set_bit(&mut row.bytes, score_local, false);

        c455_set_bit(&mut census.source_bits, score_local, true);
        assert!(census.checked_score_slack_cell(&binding, &row, &view, 0, score_wire)
            .unwrap_err().contains("source/packed mismatch"));
        c455_set_bit(&mut census.source_bits, score_local, false);
        c455_set_bit(&mut row.bytes, score_local, true);
        assert!(census.checked_score_slack_cell(&binding, &row, &view, 0, score_wire)
            .unwrap_err().contains("source/packed mismatch"));
        c455_set_bit(&mut row.bytes, score_local, false);
        assert_eq!(census.bank53_source.entries()[score_index].value(), false);
        assert_eq!(score_mask, 1u8 << (score_local % 8));

        let slack_index = crate::bank53_slack::SLACK_INPUT_START;
        let slack_local = BANK53_BASE + slack_index;
        let slack_wire = base + slack_local;
        assert_eq!(census.checked_score_slack_cell(&binding, &row, &view, 0, slack_wire)
            .unwrap(), (Bank53TypedAuthor::Slack(0), false));
        // Even coordinated equality cannot turn an authored Slack zero into one.
        census.bank53_source.mutate_entry_for_test(slack_index, None, None, Some(true));
        c455_set_bit(&mut census.source_bits, slack_local, true);
        c455_set_bit(&mut row.bytes, slack_local, true);
        assert!(census.checked_score_slack_cell(&binding, &row, &view, 0, slack_wire)
            .unwrap_err().contains("nonzero Slack"));
    }
}

/// A bounded zero-valued physical row/census tied to one retained synthetic
/// sink. Only no-frame ROW consumer tests may use this fixture.
#[cfg(test)]
pub(crate) fn c453_coactive_fixture_for_test(
    view:&Eligible08MapSourceView<'_>,
)->Result<(NativePackedRow,NativeOwnerAuthorCensus),String> {
    let (binding,row,mut census)=c374_author_census_tests::fixture_with_binding(
        view.binding().clone());
    census.bank53_source=view.typed_source_for_test()?;
    census.check_complete(&binding,&row)?;
    Ok((row,census))
}

#[cfg(test)]
impl NativeOwnerAuthorCensus {
    pub(crate) fn c453_set_author_for_test(&mut self,local:usize,
        author:Option<NativePhysicalAuthor>) {
        self.authors[local]=author;self.complete_checked.set(false);
    }
    pub(crate) fn c453_flip_tree_source_bit_for_test(&mut self,local:usize) {
        self.tree_source.values[local/8]^=1<<(local%8);
        self.complete_checked.set(false);
    }
    pub(crate) fn c453_remove_tree_source_for_test(&mut self,local:usize) {
        self.tree_source.owned[local/8]&=!(1<<(local%8));
        self.complete_checked.set(false);
    }
}

#[cfg(test)]
mod c376_tree_source_tests {
    use super::*;

    #[test]
    fn c376_tree_image_genuine_and_inactive_n3_matches_single_writer() {
        let input = super::max_join_tests::bounded_input_n(3);
        let plan = WorkTreeHistoryPlan::compile(3, 2, input.root(), input.total_be28()).unwrap();
        for owner in [0usize, 3usize] {
            let image = tree_source_image(&plan, &input, owner).unwrap();
            let replacement_mask=plan.physical_assignment_replacement_mask(owner as u64).unwrap();
            let mut rows = OwnedRows::new(OwnerSelection::Single {
                owner, class: crate::daa_history_roster::OwnerClass::Carry,
            });
            seed_tree(&plan, &input, owner, &mut rows, AssemblyFault::None).unwrap();
            let mut count = 0usize;
            for wire in 0..WIDTH {
                let owned = NativeTreeImageBuilder::bit(&image.owned, wire);
                assert_eq!(owned, rows.claimed[0][wire], "owner{owner} wire{wire} ownership");
                if owned {
                    count += 1;
                    assert_eq!(
                        NativeTreeImageBuilder::bit(&image.values, wire),
                        rows.values[0][wire] == Fr::one(),
                        "owner{owner} wire{wire} value",
                    );
                }
            }
            assert_eq!(count, 401_362);
            assert!((989_658..989_730)
                .all(|wire| !NativeTreeImageBuilder::bit(&image.owned, wire)));
            assert!((989_730..991_232).all(|wire| {
                NativeTreeImageBuilder::bit(&image.owned, wire)
                    && !NativeTreeImageBuilder::bit(&image.values, wire)
            }));
            for local in [
                987_672usize, 987_673, 987_898, 987_899,
                987_900, 987_901, 987_902, 987_903,
            ] {
                let tree_owned=NativeTreeImageBuilder::bit(&image.owned,local);
                let single_writer_owned=rows.claimed[0][local];
                let tree_value=NativeTreeImageBuilder::bit(&image.values,local);
                let single_writer_value=rows.values[0][local]==Fr::one();
                assert!(tree_owned,"C434 Tree boundary local{local} Tree image ownership owner{owner}");
                assert_eq!(tree_owned,replacement_mask[local],
                    "C434 Tree boundary local{local} exact plan replacement mask owner{owner}");
                assert!(single_writer_owned,
                    "C434 Tree boundary local{local} single Tree writer ownership owner{owner}");
                assert_eq!(tree_value,single_writer_value,
                    "C434 Tree boundary local{local} Tree image/single-writer value owner{owner}");
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum DaaSourceAuthor { NativeRetarget, CarryZero, FullZero, #[cfg(test)] Other }

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct CarryZeroBankClaim { start: usize, end: usize, claimed_bits: usize }

/// Private author evidence for four exclusive zero writes performed by the
/// native owner producer before its first pack. It cannot be built from the
/// row's initialized zero bytes or from a retarget patch.
#[derive(Clone, Debug, PartialEq, Eq)]
struct CarryZeroBankClaims {
    owner: u64,
    class: crate::daa_history_roster::OwnerClass,
    banks: Vec<CarryZeroBankClaim>,
}
impl CarryZeroBankClaims {
    fn check_identity(
        &self,
        owner: u64,
        class: crate::daa_history_roster::OwnerClass,
    ) -> Result<(), String> {
        use crate::daa_history_roster::OwnerClass;
        if self.owner != owner || self.class != class || class != OwnerClass::Carry {
            return Err("CarryZero DAA source owner/class".into());
        }
        if self.banks.len() != BANKS.len() {
            return Err("CarryZero DAA source requires exactly four banks".into());
        }
        let mut total = 0usize;
        for (claim, &(start, end)) in self.banks.iter().zip(BANKS.iter()) {
            if start >= end || end > WIDTH || start % 8 != 0 || end % 8 != 0
                || claim.start != start || claim.end != end
                || claim.claimed_bits != end - start {
                return Err("CarryZero DAA source bank geometry/claim count".into());
            }
            total = total.checked_add(claim.claimed_bits)
                .ok_or("CarryZero DAA source claim count overflow")?;
        }
        if total != 81_920 {
            return Err("CarryZero DAA source exact 81,920-bit census".into());
        }
        Ok(())
    }

    fn read_bank_bit(&self, local_wire: usize) -> Result<Option<bool>, String> {
        self.check_identity(self.owner, self.class)?;
        if self.banks.iter().any(|bank| (bank.start..bank.end).contains(&local_wire)) {
            Ok(Some(false))
        } else {
            Ok(None)
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct FullZeroBankClaim { start: usize, end: usize, claimed_bits: usize }

/// Private author evidence for the four full-template DAA banks. Each bit is
/// claimed exclusively as zero before the owner row is packed.
#[derive(Clone, Debug, PartialEq, Eq)]
struct FullZeroBankClaims {
    owner: u64,
    class: crate::daa_history_roster::OwnerClass,
    banks: Vec<FullZeroBankClaim>,
}
impl FullZeroBankClaims {
    fn check_identity(
        &self,
        owner: u64,
        class: crate::daa_history_roster::OwnerClass,
    ) -> Result<(), String> {
        if self.owner != owner || self.class != class || !is_full_zero_daa_class(class) {
            return Err("FullZero DAA source owner/class".into());
        }
        if self.banks.len() != BANKS.len() {
            return Err("FullZero DAA source requires exactly four banks".into());
        }
        let mut total = 0usize;
        for (claim, &(start, end)) in self.banks.iter().zip(BANKS.iter()) {
            if start >= end || end > WIDTH || start % 8 != 0 || end % 8 != 0
                || claim.start != start || claim.end != end
                || claim.claimed_bits != end - start {
                return Err("FullZero DAA source bank geometry/claim count".into());
            }
            total = total.checked_add(claim.claimed_bits)
                .ok_or("FullZero DAA source claim count overflow")?;
        }
        if total != 81_920 {
            return Err("FullZero DAA source exact 81,920-bit census".into());
        }
        Ok(())
    }

    fn check_claimed_rows(&self, rows: &OwnedRows, owner: usize) -> Result<(), String> {
        let owner_u64 = u64::try_from(owner).map_err(|_| "FullZero DAA owner width")?;
        self.check_identity(owner_u64, self.class)?;
        if self.owner != owner_u64 {
            return Err("FullZero DAA captured owner differs from rows".into());
        }
        for bank in &self.banks {
            for wire in bank.start..bank.end {
                let (row, local) = rows.local(owner, wire)?;
                if !rows.claimed[row][local] || rows.values[row][local] != Fr::zero() {
                    return Err(format!("FullZero missing or changed exclusive zero claim wire{wire}"));
                }
            }
        }
        Ok(())
    }

    fn read_bank_bit(&self, local_wire: usize) -> Result<Option<bool>, String> {
        self.check_identity(self.owner, self.class)?;
        if self.banks.iter().any(|bank| (bank.start..bank.end).contains(&local_wire)) {
            Ok(Some(false))
        } else {
            Ok(None)
        }
    }
}

fn check_full_zero_packed_banks(
    bytes: &[u8],
    claims: &FullZeroBankClaims,
    owner: u64,
    class: crate::daa_history_roster::OwnerClass,
) -> Result<(), String> {
    claims.check_identity(owner, class)?;
    if bytes.len() != OWNER_BYTES {
        return Err("FullZero DAA packed owner row width".into());
    }
    if claims.banks.iter().any(|bank| bytes[bank.start / 8..bank.end / 8]
        .iter().any(|byte| *byte != 0)) {
        return Err("FullZero explicit claims differ from final packed banks".into());
    }
    Ok(())
}

fn is_full_zero_daa_class(class: crate::daa_history_roster::OwnerClass) -> bool {
    use crate::daa_history_roster::OwnerClass;
    matches!(class,
        OwnerClass::Genesis | OwnerClass::Initial | OwnerClass::FixedV2
            | OwnerClass::Singleton | OwnerClass::Padding)
}

enum DaaSourcePayload {
    NativeRetarget(crate::daa_history_producer::DaaBankPatch),
    CarryZero(CarryZeroBankClaims),
    FullZero(FullZeroBankClaims),
}

#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CarryZeroLeaseFault {
    WrongBindingOwner,
    WrongRoot,
    WrongTotal,
    WrongProfile,
    WrongCut,
    WrongLayout,
    WrongPayloadOwner,
    WrongClass,
    WrongAuthor,
    WrongSourceVariant,
    IncompleteDomain,
    DuplicateDomain,
    ExtendedDomain,
    OverlappingDomain,
    WrongClaimCount,
    ShiftedDomainStart,
}

/// Read authority for bank bits emitted by this producer's validated retarget
/// write. It is scoped to one exact producer, owner, and native author.
pub(crate) struct NativeDaaSourceLease<'p, 'a> {
    _source: &'p NativeOwnerProducer<'a>,
    binding: HeaderSourceBinding,
    author: DaaSourceAuthor,
    source: DaaSourcePayload,
    #[cfg(test)] read_count: std::cell::Cell<usize>,
    #[cfg(test)] synthetic_class: Option<crate::daa_history_roster::OwnerClass>,
}

const FOREIGN_DAA_WORK_DESTINATION_OWNER: usize = 845_759;
const FOREIGN_DAA_WORK_SOURCE_OWNERS: [usize; 2] = [845_757, 845_758];
const FOREIGN_DAA_WORK_START: usize = 987_674;
const FOREIGN_DAA_WORK_END: usize = 987_898;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ForeignDaaWorkAuthor { NativeWorkD, #[cfg(test)] Other }

#[derive(Clone, Debug, PartialEq, Eq)]
struct ForeignDaaWorkParent {
    root: [u8; 32],
    total: [u8; 28],
    profile: [u8; 32],
    cut: Vec<u8>,
}
impl ForeignDaaWorkParent {
    fn from_binding(binding: &HeaderSourceBinding) -> Self {
        Self { root: binding.root, total: binding.total, profile: binding.profile,
            cut: binding.cut.clone() }
    }
    fn matches_binding(&self, binding: &HeaderSourceBinding) -> bool {
        self.root == binding.root && self.total == binding.total
            && self.profile == binding.profile && self.cut == binding.cut
    }
}

/// Read authority for the 224 ordered foreign numeric DAA Work-D endpoints.
/// Construction in production requires an exact producer replay of NativeWorkDLease.
#[derive(Clone)]
pub(crate) struct ForeignDaaWorkReadLease {
    destination: HeaderSourceBinding,
    source: HeaderSourceBinding,
    source_owner: usize,
    author: ForeignDaaWorkAuthor,
    parent: ForeignDaaWorkParent,
    cells: Vec<(usize, Fr)>,
}

impl ForeignDaaWorkReadLease {
    pub(crate) fn source_owner(&self) -> usize { self.source_owner }

    pub(crate) fn require_destination(
        &self, destination: &HeaderSourceBinding, owner: usize,
    ) -> Result<(), String> {
        if owner != FOREIGN_DAA_WORK_DESTINATION_OWNER || self.destination != *destination
            || !FOREIGN_DAA_WORK_SOURCE_OWNERS.contains(&self.source_owner)
            || self.source.owner != self.source_owner
            || self.source.root != destination.root || self.source.total != destination.total
            || self.source.profile != destination.profile || self.source.cut != destination.cut
            || self.source.layout != destination.layout
            || !self.parent.matches_binding(&self.source)
            || !self.parent.matches_binding(destination)
            || self.author != ForeignDaaWorkAuthor::NativeWorkD
        {
            return Err("foreign DAA Work-D destination/source parent/owner/author".into());
        }
        let expected_len = FOREIGN_DAA_WORK_END - FOREIGN_DAA_WORK_START;
        if self.cells.len() != expected_len {
            return Err("foreign DAA Work-D exact 224-cell census".into());
        }
        let base = self.source_owner.checked_mul(WIDTH)
            .ok_or("foreign DAA Work-D source owner overflow")?;
        for (bit, &(wire, value)) in self.cells.iter().enumerate() {
            let local = FOREIGN_DAA_WORK_START.checked_add(bit)
                .ok_or("foreign DAA Work-D endpoint overflow")?;
            let expected_wire = base.checked_add(local)
                .ok_or("foreign DAA Work-D wire overflow")?;
            if wire != expected_wire {
                return Err("foreign DAA Work-D exact ordered endpoint domain".into());
            }
            if value != Fr::zero() && value != Fr::one() {
                return Err("foreign DAA Work-D nonboolean source".into());
            }
        }
        Ok(())
    }

    pub(crate) fn read(
        &self, destination: &HeaderSourceBinding, dest_owner: usize, wire: usize,
    ) -> Result<bool, String> {
        self.require_destination(destination, dest_owner)?;
        let base = self.source_owner.checked_mul(WIDTH)
            .ok_or("foreign DAA Work-D source owner overflow")?;
        let local = wire.checked_sub(base)
            .filter(|local| (FOREIGN_DAA_WORK_START..FOREIGN_DAA_WORK_END).contains(local))
            .ok_or("foreign DAA Work-D read outside ordered work endpoints")?;
        let index = local - FOREIGN_DAA_WORK_START;
        let (_, value) = self.cells.get(index)
            .ok_or("foreign DAA Work-D source endpoint missing")?;
        if *value == Fr::one() { Ok(true) } else if *value == Fr::zero() { Ok(false) }
        else { Err("foreign DAA Work-D nonboolean source".into()) }
    }

    #[cfg(test)]
    pub(crate) fn synthetic_for_test(
        destination: HeaderSourceBinding, source_owner: usize, values: [bool; 224],
    ) -> Self {
        let mut source = destination.clone();
        source.owner = source_owner;
        let base = source_owner * WIDTH;
        let cells = values.into_iter().enumerate().map(|(bit, value)|
            (base + FOREIGN_DAA_WORK_START + bit, Fr::from(value as u64))).collect();
        Self { parent: ForeignDaaWorkParent::from_binding(&source), destination, source,
            source_owner, author: ForeignDaaWorkAuthor::NativeWorkD, cells }
    }

    #[cfg(test)]
    pub(crate) fn mutate_source_owner_for_test(&mut self, owner: usize) {
        self.source_owner = owner;
    }
    #[cfg(test)]
    pub(crate) fn mutate_source_parent_for_test(&mut self) { self.source.root[0] ^= 1; }
    #[cfg(test)]
    pub(crate) fn mutate_source_identity_for_test(&mut self) { self.source.owner += 1; }
    #[cfg(test)]
    pub(crate) fn mutate_author_for_test(&mut self) { self.author = ForeignDaaWorkAuthor::Other; }
    #[cfg(test)]
    pub(crate) fn mutate_value_for_test(&mut self) { self.cells[0].1 = Fr::from(2u64); }
}

#[cfg(test)]
mod foreign_daa_work_read_lease_tests {
    use super::*;

    fn fixture() -> (HeaderSourceBinding, ForeignDaaWorkReadLease) {
        let destination = HeaderSourceBinding::diagnostic_for_test(FOREIGN_DAA_WORK_DESTINATION_OWNER);
        let values = std::array::from_fn(|bit| bit == 0 || bit == 223);
        let lease = ForeignDaaWorkReadLease::synthetic_for_test(
            destination.clone(), FOREIGN_DAA_WORK_SOURCE_OWNERS[0], values);
        (destination, lease)
    }

    #[test]
    fn reads_only_ordered_boolean_work_endpoints() {
        let (destination, lease) = fixture();
        assert_eq!(lease.source_owner(), FOREIGN_DAA_WORK_SOURCE_OWNERS[0]);
        assert!(lease.require_destination(&destination, FOREIGN_DAA_WORK_DESTINATION_OWNER).is_ok());
        let base = FOREIGN_DAA_WORK_SOURCE_OWNERS[0] * WIDTH;
        assert_eq!(lease.read(&destination, FOREIGN_DAA_WORK_DESTINATION_OWNER,
            base + FOREIGN_DAA_WORK_START).unwrap(), true);
        assert_eq!(lease.read(&destination, FOREIGN_DAA_WORK_DESTINATION_OWNER,
            base + FOREIGN_DAA_WORK_END - 1).unwrap(), true);
        assert_eq!(lease.read(&destination, FOREIGN_DAA_WORK_DESTINATION_OWNER,
            base + FOREIGN_DAA_WORK_START + 1).unwrap(), false);
        assert!(lease.read(&destination, FOREIGN_DAA_WORK_DESTINATION_OWNER,
            base + FOREIGN_DAA_WORK_START - 1).is_err());
        assert!(lease.read(&destination, FOREIGN_DAA_WORK_DESTINATION_OWNER,
            base + FOREIGN_DAA_WORK_END).is_err());
    }

    #[test]
    fn rejects_wrong_destination_source_parent_author_and_nonboolean_value() {
        let (destination, mut wrong_owner) = fixture();
        wrong_owner.mutate_source_owner_for_test(845_756);
        assert!(wrong_owner.require_destination(&destination, FOREIGN_DAA_WORK_DESTINATION_OWNER).is_err());

        let (destination, mut wrong_parent) = fixture();
        wrong_parent.mutate_source_parent_for_test();
        assert!(wrong_parent.require_destination(&destination, FOREIGN_DAA_WORK_DESTINATION_OWNER).is_err());

        let (destination, mut wrong_source) = fixture();
        wrong_source.mutate_source_identity_for_test();
        assert!(wrong_source.require_destination(&destination, FOREIGN_DAA_WORK_DESTINATION_OWNER).is_err());

        let (destination, mut wrong_author) = fixture();
        wrong_author.mutate_author_for_test();
        assert!(wrong_author.require_destination(&destination, FOREIGN_DAA_WORK_DESTINATION_OWNER).is_err());

        let (destination, mut nonboolean) = fixture();
        nonboolean.mutate_value_for_test();
        assert!(nonboolean.require_destination(&destination, FOREIGN_DAA_WORK_DESTINATION_OWNER).is_err());

        let (destination, lease) = fixture();
        assert!(lease.require_destination(&destination, FOREIGN_DAA_WORK_DESTINATION_OWNER - 1).is_err());
    }
}
impl<'p, 'a> NativeDaaSourceLease<'p, 'a> {
    #[cfg(test)]
    pub(crate) fn synthetic_full_zero_for_test(
        source: &'p NativeOwnerProducer<'a>,
        binding: HeaderSourceBinding,
        class: crate::daa_history_roster::OwnerClass,
    ) -> Self {
        let banks = BANKS.iter().map(|&(start, end)| FullZeroBankClaim {
            start,
            end,
            claimed_bits: end - start,
        }).collect();
        Self {
            _source: source,
            binding: binding.clone(),
            author: DaaSourceAuthor::FullZero,
            source: DaaSourcePayload::FullZero(FullZeroBankClaims {
                owner: binding.owner as u64,
                class,
                banks,
            }),
            read_count: std::cell::Cell::new(0),
            synthetic_class: Some(class),
        }
    }
}

impl NativeDaaSourceLease<'_, '_> {
    pub(crate) fn check_binding(&self, expected: &HeaderSourceBinding) -> Result<(), String> {
        if &self.binding != expected {
            return Err("DAA source root/total/profile/cut/layout/owner".into());
        }
        Ok(())
    }

    pub(crate) fn check_author(&self) -> Result<(), String> {
        use crate::daa_history_roster::OwnerClass;
        let owner = u64::try_from(self.binding.owner).map_err(|_| "DAA source owner width")?;
        #[cfg(test)]
        let class = match self.synthetic_class {
            Some(class) => class,
            None => self._source.roster.owner_class(owner)?,
        };
        #[cfg(not(test))]
        let class = self._source.roster.owner_class(owner)?;
        let valid = match (&self.author, &self.source) {
            (DaaSourceAuthor::NativeRetarget, DaaSourcePayload::NativeRetarget(patch)) => {
                matches!(class, OwnerClass::M1 | OwnerClass::Short(_) | OwnerClass::Mature(_))
                    && patch.identity() == (owner, class)
            }
            (DaaSourceAuthor::CarryZero, DaaSourcePayload::CarryZero(claims)) => {
                claims.check_identity(owner, class).is_ok()
            }
            (DaaSourceAuthor::FullZero, DaaSourcePayload::FullZero(claims)) => {
                claims.check_identity(owner, class).is_ok()
            }
            _ => false,
        };
        if !valid {
            return Err("DAA source author mismatch before read admission".into());
        }
        Ok(())
    }

    pub(crate) fn check_carry_zero_source(
        &self,
        expected: &HeaderSourceBinding,
    ) -> Result<(), String> {
        self.check_binding(expected)?;
        self.check_author()?;
        if !matches!(&self.source, DaaSourcePayload::CarryZero(_)) {
            return Err("DAA source variant is not CarryZero".into());
        }
        Ok(())
    }

    pub(crate) fn check_full_zero_source(
        &self,
        expected: &HeaderSourceBinding,
    ) -> Result<(), String> {
        self.check_binding(expected)?;
        self.check_author()?;
        if !matches!(&self.source, DaaSourcePayload::FullZero(_)) {
            return Err("DAA source variant is not FullZero".into());
        }
        Ok(())
    }

    pub(crate) fn read_daa_bit(
        &self,
        expected: &HeaderSourceBinding,
        physical_wire: usize,
    ) -> Result<Option<bool>, String> {
        self.check_binding(expected)?;
        self.check_author()?;
        let base = self.binding.owner.checked_mul(WIDTH).ok_or("DAA source owner overflow")?;
        let local = physical_wire.checked_sub(base).filter(|wire| *wire < WIDTH)
            .ok_or("DAA source physical owner")?;
        let value = match &self.source {
            DaaSourcePayload::NativeRetarget(patch) => patch.read_bank_bit(local)?,
            DaaSourcePayload::CarryZero(claims) => claims.read_bank_bit(local)?,
            DaaSourcePayload::FullZero(claims) => claims.read_bank_bit(local)?,
        };
        #[cfg(test)]
        if value.is_some() { self.read_count.set(self.read_count.get() + 1); }
        Ok(value)
    }

    #[cfg(test)]
    pub(crate) fn wrong_author_mutant_for_test(&mut self) {
        self.author = DaaSourceAuthor::Other;
    }

    #[cfg(test)]
    pub(crate) fn read_count_for_test(&self) -> usize { self.read_count.get() }

    #[cfg(test)]
    pub(crate) fn with_carry_zero_fault_for_test(
        &self,
        fault: CarryZeroLeaseFault,
    ) -> Result<Self, String> {
        use crate::daa_history_roster::OwnerClass;
        let DaaSourcePayload::CarryZero(original) = &self.source else {
            return Err("CarryZero test fault requires CarryZero source".into());
        };
        let mut claims = original.clone();
        let mut binding = self.binding.clone();
        let mut author = self.author;
        match fault {
            CarryZeroLeaseFault::WrongBindingOwner => {
                binding.owner = binding.owner.checked_add(1).ok_or("test owner overflow")?;
            }
            CarryZeroLeaseFault::WrongRoot => binding.root[0] ^= 1,
            CarryZeroLeaseFault::WrongTotal => binding.total[0] ^= 1,
            CarryZeroLeaseFault::WrongProfile => binding.profile[0] ^= 1,
            CarryZeroLeaseFault::WrongCut => {
                let first = binding.cut.first_mut().ok_or("test Eligible08 cut missing")?;
                *first ^= 1;
            }
            CarryZeroLeaseFault::WrongLayout => binding.layout[0] ^= 1,
            CarryZeroLeaseFault::WrongPayloadOwner => {
                claims.owner = claims.owner.checked_add(1).ok_or("test owner overflow")?;
            }
            CarryZeroLeaseFault::WrongClass => claims.class = OwnerClass::Initial,
            CarryZeroLeaseFault::WrongAuthor => author = DaaSourceAuthor::Other,
            CarryZeroLeaseFault::WrongSourceVariant => author = DaaSourceAuthor::NativeRetarget,
            CarryZeroLeaseFault::IncompleteDomain => { claims.banks.pop(); }
            CarryZeroLeaseFault::DuplicateDomain => {
                let first = *claims.banks.first().ok_or("test CarryZero bank missing")?;
                claims.banks.push(first);
            }
            CarryZeroLeaseFault::ExtendedDomain => {
                let first = claims.banks.first_mut().ok_or("test CarryZero bank missing")?;
                first.end = first.end.checked_add(1).ok_or("test bank end overflow")?;
                first.claimed_bits = first.claimed_bits.checked_add(1)
                    .ok_or("test claim count overflow")?;
            }
            CarryZeroLeaseFault::OverlappingDomain => {
                let first = claims.banks.first_mut().ok_or("test CarryZero bank missing")?;
                first.end = BANKS[1].0.checked_add(1).ok_or("test overlapping end overflow")?;
                first.claimed_bits = first.end.checked_sub(first.start)
                    .ok_or("test overlapping claim count underflow")?;
            }
            CarryZeroLeaseFault::WrongClaimCount => {
                let first = claims.banks.first_mut().ok_or("test CarryZero bank missing")?;
                first.claimed_bits = first.claimed_bits.checked_sub(1)
                    .ok_or("test claim count underflow")?;
            }
            CarryZeroLeaseFault::ShiftedDomainStart => {
                let first = claims.banks.first_mut().ok_or("test CarryZero bank missing")?;
                first.start = first.start.checked_add(1).ok_or("test bank start overflow")?;
            }
        }
        Ok(Self {
            _source: self._source,
            binding,
            author,
            source: DaaSourcePayload::CarryZero(claims),
            read_count: std::cell::Cell::new(0),
            synthetic_class: self.synthetic_class,
        })
    }
}

pub(crate) struct NativeOwnerProducer<'a> {
    plan: &'a WorkTreeHistoryPlan,
    input: &'a NativePrefix,
    roster: DaaHistoryRoster<'a>,
    exports: crate::native_owner_exports::NativeExports<'a>,
    header_template: crate::daa_history_layout::HeaderAssignmentTemplate,
    max_adapter: Option<&'a crate::max_header_adapter::MaxHeaderAdapter<'a>>,
    #[cfg(test)]
    legacy_adapter: Option<&'a crate::legacy_native_adapter::LegacyNativeAdapter<'a>>,
}

/// Opaque, non-cloneable authority over one genuine Work LOCAL source. The
/// borrow prevents mutation/replacement of the producer while custody is live.
pub(crate) struct WorkLocalLease<'a> {
    source:&'a NativeOwnerProducer<'a>,
    parent:crate::h21_work_local_source::Parent,
    owner:usize,height:usize,row:NativePackedRow,
    terms:Vec<crate::h21_work_local_source::TaggedTerm>,
    operands:Vec<(usize,Fr)>,d:Vec<(usize,Fr)>,
}
impl WorkLocalLease<'_> {
    pub(crate) fn terms(&self)->&[crate::h21_work_local_source::TaggedTerm]{&self.terms}
    pub(crate) fn operands(&self)->&[(usize,Fr)]{&self.operands}
    pub(crate) fn d(&self)->&[(usize,Fr)]{&self.d}
}
/// Claim-event authority over the same packed Work LOCAL row. The Tree
/// source image is checked independently, but cannot replace these events.
#[allow(dead_code)]
pub(crate) struct NativeWorkEndpointAuthorLease<'w> {
    local: WorkLocalLease<'w>,
    tree: NativeTreeSourceLease,
    capture: WorkEndpointCapture,
    binding: HeaderSourceBinding,
    complete_checked: Cell<bool>,
}
/// Retained source and bounded single-fault scratch; native per-owner assembly
/// scratch remains governed by its existing producer/resource checks.
pub(crate) fn c578_work_retained_bound() -> Result<usize, String> {
    let mut size = std::mem::size_of::<NativeWorkEndpointAuthorLease<'_>>();
    let cut = crate::bank53_map::CutDescriptor::eligible08().canonical_identity().len();
    for part in [OWNER_BYTES.checked_mul(8),
        6530usize.checked_mul(std::mem::size_of::<crate::h21_work_local_source::TaggedTerm>()),
        2368usize.checked_mul(std::mem::size_of::<(usize,Fr)>()),
        448usize.checked_mul(std::mem::size_of::<(usize,Fr)>()),
        896usize.checked_mul(std::mem::size_of::<(usize,NativeWorkEndpointAuthor,Fr)>()),
        cut.checked_mul(16)] {
        size = size.checked_add(part.ok_or("C578 retained bound overflow")?)
            .ok_or("C578 retained bound overflow")?;
    }
    Ok(size)
}
#[cfg(test)]
thread_local! { static C578_NATIVE_ASSEMBLIES: Cell<Option<usize>> = const { Cell::new(None) }; }
#[cfg(test)]
pub(crate) fn c578_with_native_assembly_checks<R>(
    perform: impl FnOnce() -> Result<R,String>) -> Result<R,String> {
    C578_NATIVE_ASSEMBLIES.with(|count| -> Result<(),String> {
        if count.get().is_some() {return Err("C578 nested assembly counter".into());}
        count.set(Some(0)); Ok(())
    })?;
    let result = perform();
    let actual = C578_NATIVE_ASSEMBLIES.with(|count| count.replace(None));
    let out = result?;
    if actual != Some(6) {return Err("C578 requires six actual physical assemblies".into());}
    Ok(out)
}
#[cfg(test)]
fn c578_record_native_assembly() -> Result<(),String> {
    C578_NATIVE_ASSEMBLIES.with(|count| {
        if let Some(n) = count.get() {
            count.set(Some(n.checked_add(1).ok_or("C578 assembly counter overflow")?));
        }
        Ok(())
    })
}
#[allow(dead_code)]
impl NativeWorkEndpointAuthorLease<'_> {
    /// No completion or value read occurs before expected live-source identity.
    pub(crate) fn require_live_source(&self, producer:&NativeOwnerProducer<'_>)
        -> Result<(),String> {
        let result = (|| {
        if !std::ptr::eq(self.local.source,producer) {
            return Err("C578 physical Work producer identity".into());
        }
        let owner = self.local.owner;
        let expected = HeaderSourceBinding::for_plan(producer.plan,owner)?;
        if self.binding != expected || self.local.parent != producer.work_local_parent(owner)?
            || self.local.height != owner + 2 || expected.profile() != producer.input.profile() {
            return Err("C578 physical Work live parent/height binding".into());
        }
        Ok(())
        })();
        if result.is_err() { self.complete_checked.set(false); }
        result
    }
    pub(crate) fn checked_upper_fr(&self, physical_wire:usize)
        -> Result<(NativeWorkEndpointAuthor,Fr),String> {
        let result = (|| {
        WorkEndpointCapture::require_complete_checked(&self.complete_checked)?;
        let base = self.binding.owner().checked_mul(WIDTH)
            .and_then(|base|base.checked_add(C512I_UPPER_BASE))
            .ok_or("C578 Upper address overflow")?;
        if !(base..base+C512I_ENDPOINT_BITS).contains(&physical_wire) {
            return Err("C578 physical Upper domain".into());
        }
        if self.capture.events.len()!=C512I_CAPTURE_BITS {
            return Err("C578 Upper event census".into());
        }
        let index=physical_wire-base;
        let event=self.capture.events[index];
        if event.0!=C512I_UPPER_BASE+index || event.1!=NativeWorkEndpointAuthor::Tree {
            return Err("C578 Upper Tree event domain/author/order".into());
        }
        self.capture.checked_endpoint_fr(&self.complete_checked,&self.binding,
            &self.local.row,&self.tree,physical_wire)
        })();
        if result.is_err() { self.complete_checked.set(false); }
        result
    }
    pub(crate) fn retained_capacity_bytes(&self) -> Result<usize,String> {
        let mut size = std::mem::size_of_val(self);
        let cut = self.local.row.header_source_binding.as_ref()
            .map_or(0,|binding|binding.cut.capacity());
        for part in [Some(self.local.row.bytes.capacity()),Some(self.tree.values.capacity()),
            Some(self.tree.owned.capacity()),Some(self.binding.cut.capacity()),
            Some(self.tree.binding.cut.capacity()),Some(self.local.parent.cut.capacity()),Some(cut),
            self.local.terms.capacity().checked_mul(std::mem::size_of::<crate::h21_work_local_source::TaggedTerm>()),
            self.local.operands.capacity().checked_mul(std::mem::size_of::<(usize,Fr)>()),
            self.local.d.capacity().checked_mul(std::mem::size_of::<(usize,Fr)>()),
            self.capture.events.capacity().checked_mul(std::mem::size_of::<(usize,NativeWorkEndpointAuthor,Fr)>())] {
            size = size.checked_add(part.ok_or("C578 actual retained overflow")?)
                .ok_or("C578 actual retained overflow")?;
        }
        Ok(size)
    }
    #[cfg(test)]
    pub(crate) fn c578_native_source_controls(&mut self, producer:&NativeOwnerProducer<'_>)
        -> Result<(),String> {
        self.require_live_source(producer)?;self.check_complete()?;
        let base=self.local.owner*WIDTH;
        let wire=base+C512I_UPPER_BASE;
        self.complete_checked.set(false);
        if self.checked_upper_fr(wire).err().as_deref()!=Some("C512i Work endpoint checked read needs complete census") {
            return Err("C578 before-qualification control".into());
        }
        self.check_complete()?;
        let binding=self.binding.clone();
        for fault in 0..6 {
            match fault {0=>self.binding.root[0]^=1,1=>self.binding.total[0]^=1,
                2=>self.binding.profile[0]^=1,3=>self.binding.cut.push(1),
                4=>self.binding.layout[0]^=1,_=>self.binding.owner^=1}
            let rejected=self.require_live_source(producer).err().as_deref()
                ==Some("C578 physical Work live parent/height binding");
            self.binding=binding.clone();
            if !rejected || self.checked_upper_fr(wire).is_ok() {
                return Err("C578 binding fault must revoke reads".into());
            }
        }
        let parent=self.local.parent.clone();
        for fault in 0..6 {
            match fault {0=>self.local.parent.root[0]^=1,1=>self.local.parent.total[0]^=1,
                2=>self.local.parent.profile[0]^=1,3=>self.local.parent.cut.push(1),
                4=>self.local.parent.headers+=1,_=>self.local.parent.slots+=1}
            let rejected=self.require_live_source(producer).err().as_deref()
                ==Some("C578 physical Work live parent/height binding");
            self.local.parent=parent.clone();
            if !rejected || self.checked_upper_fr(wire).is_ok() {
                return Err("C578 LOCAL parent fault must revoke reads".into());
            }
        }
        self.local.height+=1;
        let wrong_height=self.require_live_source(producer).err().as_deref()
            ==Some("C578 physical Work live parent/height binding");
        self.local.height-=1;
        if !wrong_height {return Err("C578 physical height fault".into());}
        self.require_live_source(producer)?;self.check_complete()?;
        let zero=self.capture.events[..224].iter().position(|(_,_,value)|value.is_zero())
            .ok_or("C578 real Upper has no zero for original-Fr control")?;
        let zero_wire=base+C512I_UPPER_BASE+zero;
        self.capture.events[zero].2=Fr::from(2u64);
        let nonboolean=self.checked_upper_fr(zero_wire).err().as_deref()
            ==Some("C577 original Work endpoint Fr is not Boolean");
        self.capture.events[zero].2=Fr::zero();
        if !nonboolean || self.checked_upper_fr(zero_wire).is_ok() {
            return Err("C578 Fr2 before bool/after-revocation control".into());
        }
        self.check_complete()?;
        self.capture.events[zero].0=C512I_WORK_D_BASE+zero;
        let wrong_domain=self.checked_upper_fr(zero_wire).err().as_deref()
            ==Some("C578 Upper Tree event domain/author/order");
        self.capture.events[zero].0=C512I_UPPER_BASE+zero;
        if !wrong_domain {return Err("C578 zero Upper retagged Work-D".into());}
        self.check_complete()?;
        let byte=(C512I_UPPER_BASE+zero)/8;let mask=1u8<<((C512I_UPPER_BASE+zero)%8);
        for fault in 0..2 {
            if fault==0 {self.local.row.bytes[byte]^=mask;} else {self.tree.values[byte]^=mask;}
            let rejected=self.checked_upper_fr(zero_wire).err().as_deref()
                ==Some("C512i Work endpoint event/source/packed changed");
            if fault==0 {self.local.row.bytes[byte]^=mask;} else {self.tree.values[byte]^=mask;}
            if !rejected {return Err("C578 physical packed/source disagreement".into());}
            self.check_complete()?;
        }
        self.tree.owned[byte]^=mask;
        let missing_source=self.checked_upper_fr(zero_wire).err().as_deref()
            ==Some("C512i Work endpoint missing Tree source");
        self.tree.owned[byte]^=mask;
        if !missing_source {return Err("C578 missing Tree source mask".into());}
        self.check_complete()?;
        self.tree.author=TreeLeaseAuthor::Other;
        let wrong_tree=self.checked_upper_fr(wire).err().as_deref()
            ==Some("C376 Tree source author mismatch");
        self.tree.author=TreeLeaseAuthor::NativeTree;
        if !wrong_tree {return Err("C578 physical Tree author".into());}
        self.check_complete()?;
        self.capture.phase=WorkEndpointPhase::BeforeTree;
        let wrong_phase=self.checked_upper_fr(wire).err().as_deref()
            ==Some("C512i complete Work endpoint claim census changed");
        self.capture.phase=WorkEndpointPhase::AfterTree;
        if !wrong_phase {return Err("C578 actual Tree phase".into());}
        self.check_complete()?;
        let last=self.capture.events.pop().ok_or("C578 event control empty")?;
        let missing=self.checked_upper_fr(wire).err().as_deref()==Some("C578 Upper event census");
        self.capture.events.push(last);
        if !missing {return Err("C578 missing zero-inclusive event".into());}
        self.check_complete()?;
        let second=self.capture.events[1];self.capture.events[1]=self.capture.events[0];
        let duplicate=self.checked_upper_fr(wire+1).err().as_deref()
            ==Some("C578 Upper Tree event domain/author/order");
        self.capture.events[1]=second;
        if !duplicate {return Err("C578 duplicate event".into());}
        self.check_complete()?;
        self.capture.events.swap(0,1);
        let order=self.checked_upper_fr(wire).err().as_deref()
            ==Some("C578 Upper Tree event domain/author/order");
        self.capture.events.swap(0,1);
        if !order {return Err("C578 event occurrence order".into());}
        self.check_complete()?;
        if self.checked_upper_fr(base+C512I_WORK_D_BASE).err().as_deref()
            !=Some("C578 physical Upper domain") {return Err("C578 Work-D read is not Upper".into());}
        self.check_complete()?;
        let foreign=self.local.row.clone();
        if foreign.bytes!=self.local.row.bytes || foreign.bytes.as_ptr()==self.local.row.bytes.as_ptr() {
            return Err("C578 foreign equal-byte allocation control premise".into());
        }
        let original=std::mem::replace(&mut self.local.row,foreign);
        let foreign_rejected=self.checked_upper_fr(wire).err().as_deref()
            ==Some("C512j Work capture requires its original packed allocation");
        self.local.row=original;
        if !foreign_rejected {return Err("C578 foreign equal-byte row accepted".into());}
        self.require_live_source(producer)?;self.check_complete()?;
        if self.checked_upper_fr(zero_wire)?.1!=Fr::zero() {
            return Err("C578 pristine source not restored".into());
        }
        Ok(())
    }
    pub(crate) fn checked_local(&self) -> Result<&WorkLocalLease<'_>, String> {
        WorkEndpointCapture::require_complete_checked(&self.complete_checked)?;
        Ok(&self.local)
    }
    pub(crate) fn binding(&self) -> &HeaderSourceBinding { &self.binding }
    pub(crate) fn check_complete(&self) -> Result<usize, String> {
        self.complete_checked.set(false);
        let producer = self.local.source;
        let owner = self.local.owner;
        let expected = HeaderSourceBinding::for_plan(producer.plan, owner)?;
        let parent = producer.work_local_parent(owner)?;
        self.capture.check_identity(&self.binding, &expected, &self.local.parent,
            &parent, self.local.height, &self.local.row)?;
        producer.require_work_local_lease(owner, &self.local)?;
        self.capture.check_source_packed(&expected, &self.local.row, &self.tree)?;
        self.complete_checked.set(true);
        Ok(C512I_CAPTURE_BITS)
    }
    pub(crate) fn checked_endpoint(&self, physical_wire: usize)
        -> Result<(NativeWorkEndpointAuthor, bool), String> {
        self.capture.checked_endpoint(&self.complete_checked, &self.binding,
            &self.local.row, &self.tree, physical_wire)
    }
}
/// Distinct native type: a generic local lease cannot enter the H21 wrapper.
pub(crate) struct NativeWorkLocalLease<'a> {
    parent:crate::h21_scheduled_max_cap::NativeParent,local:WorkLocalLease<'a>,
}
impl<'a> NativeWorkLocalLease<'a> {
    pub(crate) fn local(&self)->&WorkLocalLease<'a>{&self.local}
}
/// Owned physical Upper publication, minted only after the complete packed
/// LOCAL lease has passed its source, canonical-term and residual checks.
/// The retained LOCAL namespace is separate from the consumer's ROW19 lease.
#[derive(Clone,PartialEq,Eq)]
pub(crate) struct WorkUpperPublication {
    parent:crate::h21_work_local_source::Parent, owner:usize, height:usize,
    terms:Vec<crate::h21_work_local_source::TaggedTerm>, operands:Vec<(usize,Fr)>,
    upper:Vec<(usize,Fr)>,
}
impl WorkUpperPublication {
    pub(crate) fn checked_upper(&self,root:[u8;32],total:[u8;28],profile:[u8;32],
        cut:&[u8],owner:usize)->Result<&[(usize,Fr)],String> {
        if self.parent.root!=root || self.parent.total!=total || self.parent.profile!=profile
            || self.parent.cut!=cut || self.owner!=owner || self.height!=owner+2 {
            return Err("Work Upper exact parent/cut/owner/height".into());
        }
        if self.terms.len()!=3265 || self.operands.len()!=1184 || self.upper.len()!=224 {
            return Err("Work Upper complete LOCAL/Upper census".into());
        }
        for (bit,&(wire,value)) in self.upper.iter().enumerate() {
            if wire!=owner*WIDTH+987450+bit || !(value.is_zero()||value.is_one())
                || !self.operands.iter().any(|&(w,v)|w==wire&&v==value) {
                return Err("Work Upper exact physical operand projection".into());
            }
        }
        Ok(&self.upper)
    }
    /// Test-only isolated corruption after native publication. The retained
    /// operand stays intact, so checked_upper must reject this Upper value.
    #[cfg(test)]
    pub(crate) fn c455_flip_upper_value_for_test(&mut self)->Result<(),String> {
        let (_,value)=self.upper.first_mut().ok_or("C455 test Upper source absent")?;
        if !(*value==Fr::zero()||*value==Fr::one()) {
            return Err("C455 test Upper source is non-Boolean".into());
        }
        *value=Fr::one()-*value;
        Ok(())
    }
    pub(crate) fn retained_counts(&self)->(usize,usize){(self.terms.len(),self.operands.len())}
}
#[cfg(test)]
pub(crate) fn small_work_upper_fixture(mutation:Option<usize>)
    ->Result<(WorkUpperPublication,crate::h21_work_local_source::Parent),String> {
    let (plan,input)=work_local_source_tests::fixture();
    let producer=NativeOwnerProducer::new_for_history(plan,input)?;
    let mut lease=producer.work_local_lease(0)?;
    if let Some(kind)=mutation {
        match kind {
            0=>{let i=lease.operands.iter().position(|(w,_)|*w==987450).unwrap();
                lease.operands[i].1=Fr::one()-lease.operands[i].1;},
            1=>lease.owner+=1,
            2=>lease.height+=1,
            3=>lease.terms[0].term.gate.c0+=Fr::one(),
            _=>panic!("unknown Work Upper source mutation"),
        }
    }
    Ok((producer.work_upper_publication(0,&lease)?,lease.parent.clone()))
}
#[cfg(test)]
mod c455_work_upper_recheck_tests {
    use super::*;
    #[test]
    fn c455_retained_upper_flip_rejects_checked_projection_no_frame() {
        let (mut publication,parent)=small_work_upper_fixture(None).unwrap();
        publication.checked_upper(parent.root,parent.total,parent.profile,&parent.cut,0).unwrap();
        publication.c455_flip_upper_value_for_test().unwrap();
        assert_eq!(publication.checked_upper(parent.root,parent.total,parent.profile,
            &parent.cut,0).unwrap_err(),
            "Work Upper exact physical operand projection");
    }
}
#[cfg(test)]
#[path="h21_work_local_source_tests.rs"]
mod work_local_source_tests;

/// Narrow physical HEADER Work-D author. Production construction is confined
/// to NativeOwnerProducer and its checked NativeExports; no caller bitmap.
#[derive(Clone,Debug,PartialEq,Eq)]
pub(crate) struct NativeWorkDLease {
    parent:crate::h21_scheduled_max_cap::NativeParent,
    owner:usize,height:usize,cells:Vec<(usize,Fr)>,
}
impl NativeWorkDLease {
    pub(crate) fn checked_cells(&self,parent:&crate::h21_scheduled_max_cap::NativeParent,
        owner:usize)->Result<&[(usize,Fr)],String> {
        if &self.parent!=parent || self.owner!=owner || self.height!=owner.checked_add(2).ok_or("native Work-D height overflow")? {
            return Err("native Work-D parent/cut/owner/height".into());
        }
        if self.cells.len()!=224 {return Err("native Work-D exact 224-cell census".into());}
        for (bit,&(wire,value)) in self.cells.iter().enumerate() {
            if wire!=owner*WIDTH+987674+bit {return Err("native Work-D exact ordered domain".into());}
            if value!=Fr::zero() && value!=Fr::one() {return Err("native Work-D nonboolean source".into());}
        }
        Ok(&self.cells)
    }
    #[cfg(test)]
    pub(crate) fn synthetic_for_test(parent:crate::h21_scheduled_max_cap::NativeParent,
        owner:usize,d:u64)->Self {
        Self{parent,owner,height:owner+2,cells:(0..224).map(|bit|
            (owner*WIDTH+987674+bit,Fr::from(if bit<64 {(d>>bit)&1}else{0}))).collect()}
    }
    #[cfg(test)]
    pub(crate) fn mutate_for_test(&mut self,kind:usize) {
        match kind {
            0=>self.cells[0].1=Fr::one()-self.cells[0].1,
            1=>self.owner+=1,
            2=>self.height+=1,
            3=>{self.cells.pop();},
            4=>self.cells.push(self.cells[0]),
            5=>self.cells[0].0+=1,
            6=>self.cells[0].1=Fr::from(2u64),
            7=>self.cells[0].0-=1,
            8=>self.cells[223].0+=1,
            _=>panic!("unknown native Work-D test mutation"),
        }
    }
}

#[cfg(test)]
mod native_work_d_projection_tests {
    use super::*;
    #[test]
    fn c184_small_native_projection_matches_existing_row_and_exports_without_h21_claim() {
        let prefix=crate::packed_owner_assembly_tests::legacy_prefix_for_test();
        let plan=crate::packed_owner_assembly_tests::legacy_assembly_plan_for_test();
        let producer=NativeOwnerProducer::new_for_history(plan,prefix).unwrap();
        for owner in [0usize,1] {
            let projected=producer.native_work_d_projection(owner).unwrap();
            assert_eq!(projected.len(),224);
            let row=producer.produce(owner).unwrap();
            for (bit,(wire,value)) in projected.into_iter().enumerate() {
                assert_eq!(wire,owner*WIDTH+987674+bit);
                let bytes=row.packed_bytes();let local=wire%WIDTH;
                let packed=(bytes[local/8]>>(local%8))&1;
                assert_eq!(value,Fr::from(packed as u64));
                assert_eq!(value,Fr::from(producer.exports.bit(wire).unwrap()as u64));
            }
        }
        assert!(producer.native_work_d_projection(plan.descriptor().genuine).is_err());
        assert!(producer.native_work_d_lease(0).is_err(),"small native projection is not an Eligible08 H21 lease");
    }
}

/// Internally generated Map assignment for one explicitly selected Bank53
/// context. Callers can select the Map binding and context, but cannot supply
/// helper or import bits.
struct Bank53MapAssignment {
    owner: usize,
    context: usize,
    binding: crate::legacy_envelope_map::Binding,
    values: Vec<bool>,
    #[cfg(test)]
    h21_test_only: bool,
}

/// An incomplete Eligible08 owner assignment. This is deliberately distinct
/// from NativePackedRow: Map owns only its live helpers, while the remaining
/// HEADER/Score/Slack/MAX/Cap leases still need their own source authors.
/// There is no byte export or finish operation for this stage.
#[allow(dead_code)]
#[derive(Clone, PartialEq, Eq)]
pub(crate) struct H21EligibleMapStage {
    owner: usize,
    class: crate::daa_history_roster::OwnerClass,
    parent_root: [u8; 32],
    parent_total: [u8; 28],
    parent_profile: [u8; 32],
    cut_identity: Vec<u8>,
    map_bindings: [crate::legacy_envelope_map::Binding; 2],
    map_reservations: [std::ops::Range<usize>; 2],
    claims: BTreeMap<usize, (H21StageAuthor, bool)>,
    map_terms: [Vec<Term>; 2],
    score_terms: [Vec<Term>; 2],
    cap_terms: [Vec<Term>; 2],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum H21StageAuthor {
    Map(usize),
    Slack(usize),
    ScoreAnchor(usize),
    ScoreModern(usize),
    Cap(usize),
    #[cfg(test)]
    ScoreProbe(usize),
}

impl H21EligibleMapStage {
    fn descriptor() -> crate::bank53_map::CutDescriptor {
        crate::bank53_map::CutDescriptor::eligible08()
    }

    #[cfg(test)]
    fn source_maps() -> Result<[crate::legacy_envelope_map::Map; 2], String> {
        use crate::legacy_envelope_map::{LowerBranch, LowerSelector, LowerSource, Map};
        let descriptor = Self::descriptor();
        let lower = LowerSelector {
            source: LowerSource::HeaderDifficulty { height: 841_729 },
            branch: LowerBranch::Pivot(54),
        };
        // Both c168 Map bindings are symbolic/rootless. The enclosing stage
        // binds their source to the one exact full parent, not a fictitious
        // root for the cut tree.
        let cuts = descriptor.terminals();
        Ok([
            Map::new_modern_global_u_selected_lower(cuts[0] as u64, 21, 55, lower)?,
            Map::new_modern_global_u_selected_lower(cuts[1] as u64, 21, 55, lower)?,
        ])
    }

    /// Test-only identity carrier for source extraction tests that do not
    /// exercise parent-plan admission or Map/ROW coactivity.
    #[cfg(test)]
    pub(super) fn test_identity_only(owner: usize) -> Result<Self, String> {
        let descriptor = Self::descriptor();
        let maps = Self::source_maps()?;
        Ok(Self {
            owner,
            class: crate::daa_history_roster::OwnerClass::Genesis,
            parent_root: [0x51; 32],
            parent_total: [0x52; 28],
            parent_profile: [0x53; 32],
            cut_identity: descriptor.canonical_identity(),
            map_bindings: [maps[0].binding(), maps[1].binding()],
            map_reservations: [Self::map_live(0)?, Self::map_live(1)?],
            claims: BTreeMap::new(),
            map_terms: [Vec::new(), Vec::new()],
            score_terms: [Vec::new(), Vec::new()],
            cap_terms: [Vec::new(), Vec::new()],
        })
    }

    fn map_live(context: usize) -> Result<std::ops::Range<usize>, String> {
        if context >= BANK53_CONTEXTS { return Err("c170 Map context".into()); }
        let start = BANK53_BASE + context * BANK53_CONTEXT_BITS;
        Ok(start..start + BANK53_MAP_LIVE_BITS)
    }

    fn score_live(context: usize) -> Result<std::ops::Range<usize>, String> {
        if context >= BANK53_CONTEXTS { return Err("Eligible08 Score context".into()); }
        let start = BANK53_BASE + context * BANK53_CONTEXT_BITS + BANK53_MAP_LIVE_BITS;
        Ok(start..start + crate::origin_score::INPUT)
    }

    fn slack_live(context: usize) -> Result<std::ops::Range<usize>, String> {
        if context >= BANK53_CONTEXTS { return Err("Eligible08 Slack context".into()); }
        let start = Self::score_live(context)?.end;
        let end = start.checked_add(BANK53_SLACK_BITS)
            .ok_or("Eligible08 Slack LIVE overflow")?;
        let bank_end = BANK53_BASE + (context + 1) * BANK53_CONTEXT_BITS;
        if end != bank_end || end - start != BANK53_SLACK_BITS {
            return Err("Eligible08 Slack LIVE geometry".into());
        }
        Ok(start..end)
    }

    fn cap_live(context: usize) -> Result<std::ops::Range<usize>, String> {
        if context >= BANK53_CONTEXTS { return Err("Eligible08 Cap context".into()); }
        let start = [1_000_770, 1_002_818][context];
        Ok(start..start + 2_048)
    }

    /// The parent HEADER zero-assignment may be transferred only at the
    /// scheduled source MAX and first-modern Cap cells. This is not yet a
    /// retirement of their HEADER rows in the final merger.
    fn require_header_owned_first_modern_scheduled(mask: &[bool]) -> Result<(), String> {
        if mask.len() != WIDTH { return Err("Eligible08 scheduled parent mask width".into()); }
        for domain in [999_424..1_000_097, 1_000_097..1_000_770,
            Self::cap_live(0)?, Self::cap_live(1)?] {
            if domain.end > WIDTH || mask[domain].iter().any(|replaced| *replaced) {
                return Err("Eligible08 MAX/Cap LIVE must be HEADER-owned in parent mask".into());
            }
        }
        Ok(())
    }

    fn require_header_owned_map_live(mask: &[bool]) -> Result<(), String> {
        if mask.len() != WIDTH {
            return Err("c170 parent replacement mask width".into());
        }
        for context in 0..BANK53_CONTEXTS {
            let live = Self::map_live(context)?;
            if live.end > WIDTH || mask[live].iter().any(|replaced| *replaced) {
                return Err("c170 Map LIVE must be HEADER-owned in parent mask".into());
            }
        }
        Ok(())
    }

    fn require_header_owned_score_live(mask: &[bool]) -> Result<(), String> {
        if mask.len() != WIDTH {
            return Err("Eligible08 parent replacement mask width".into());
        }
        for context in 0..BANK53_CONTEXTS {
            let live = Self::score_live(context)?;
            if live.end > WIDTH || mask[live].iter().any(|replaced| *replaced) {
                return Err("Eligible08 Score LIVE must be HEADER-owned in parent mask".into());
            }
        }
        Ok(())
    }

    fn require_header_owned_slack_live(mask: &[bool]) -> Result<(), String> {
        if mask.len() != WIDTH {
            return Err("Eligible08 Slack parent replacement mask width".into());
        }
        for context in 0..BANK53_CONTEXTS {
            let live = Self::slack_live(context)?;
            if live.end > WIDTH || mask[live].iter().any(|replaced| *replaced) {
                return Err("Eligible08 Slack LIVE must be HEADER-owned in parent mask".into());
            }
        }
        Ok(())
    }

    fn new_bound(
        plan: &WorkTreeHistoryPlan,
        parent_profile: [u8; 32],
        owner: usize,
        class: crate::daa_history_roster::OwnerClass,
        descriptor: crate::bank53_map::CutDescriptor,
        maps: &[crate::legacy_envelope_map::Map; 2],
        parent_mask: &[bool],
    ) -> Result<Self, String> {
        if descriptor != Self::descriptor()
            || plan.headers() != crate::bank53_map::BANK53_N
            || plan.slot_log() != 21
            || plan.slots() != 1 << 21
            || owner >= plan.slots()
        {
            return Err("c170 Eligible08 parent/cut/owner geometry".into());
        }
        plan.descriptor().validate()?;
        Self::require_header_owned_map_live(parent_mask)?;
        Self::require_header_owned_score_live(parent_mask)?;
        if maps.iter().enumerate().any(|(context, map)|
            map.n() != descriptor.terminals()[context] as u64
                || map.h() != 21 || map.slots() != 1 << 21
                || map.binding().parent_root.is_some()) {
            return Err("c170 rootless Map context/cut/source binding".into());
        }
        Ok(Self {
            owner, class,
            parent_root: plan.descriptor().root,
            parent_total: plan.work_profile().total_be28,
            parent_profile,
            cut_identity: descriptor.canonical_identity(),
            map_bindings: [maps[0].binding(), maps[1].binding()],
            map_reservations: [Self::map_live(0)?, Self::map_live(1)?],
            claims: BTreeMap::new(),
            map_terms: [Vec::new(), Vec::new()],
            score_terms: [Vec::new(), Vec::new()],
            cap_terms: [Vec::new(), Vec::new()],
        })
    }

    #[cfg(test)]
    fn new_empty(
        plan: &WorkTreeHistoryPlan,
        parent_profile: [u8; 32],
        owner: usize,
        descriptor: crate::bank53_map::CutDescriptor,
        maps: &[crate::legacy_envelope_map::Map; 2],
    ) -> Result<Self, String> {
        let expected = Self::source_maps()?;
        if maps.iter().zip(expected.iter()).any(|(map, want)| map.binding() != want.binding()) {
            return Err("c170 rootless Map context/cut/source binding".into());
        }
        let class = DaaHistoryRoster::compile(plan)?.owner_class(owner as u64)?;
        let mask = plan.physical_assignment_replacement_mask(owner as u64)?;
        Self::new_bound(plan, parent_profile, owner, class, descriptor, maps, &mask)
    }

    fn validate_identity(
        &self,
        plan: &WorkTreeHistoryPlan,
        profile: [u8; 32],
        descriptor: crate::bank53_map::CutDescriptor,
        maps: &[crate::legacy_envelope_map::Map; 2],
    ) -> Result<(), String> {
        self.validate_identity_with_classifier(plan, profile, descriptor, maps,
            || DaaHistoryRoster::compile(plan)?.owner_class(self.owner as u64))
    }

    fn validate_identity_with_roster(
        &self,
        plan: &WorkTreeHistoryPlan,
        profile: [u8; 32],
        descriptor: crate::bank53_map::CutDescriptor,
        maps: &[crate::legacy_envelope_map::Map; 2],
        roster: &DaaHistoryRoster<'_>,
    ) -> Result<(), String> {
        self.validate_identity_with_classifier(plan, profile, descriptor, maps, || {
            if !std::ptr::eq(roster.endpoint_parent(), plan) {
                return Err("c170 borrowed stage roster has another parent".into());
            }
            roster.owner_class(self.owner as u64)
        })
    }

    // Keep classification lazy: the original entry must still reject every
    // earlier metadata mismatch before constructing a large DAA roster.
    fn validate_identity_with_classifier(
        &self,
        plan: &WorkTreeHistoryPlan,
        profile: [u8; 32],
        descriptor: crate::bank53_map::CutDescriptor,
        maps: &[crate::legacy_envelope_map::Map; 2],
        classify: impl FnOnce() -> Result<crate::daa_history_roster::OwnerClass, String>,
    ) -> Result<(), String> {
        if descriptor != Self::descriptor()
            || self.cut_identity != descriptor.canonical_identity()
            || plan.headers() != crate::bank53_map::BANK53_N
            || plan.slot_log() != 21
            || plan.slots() != 1 << 21
            || self.owner >= plan.slots()
            || self.parent_root != plan.descriptor().root
            || self.parent_total != plan.work_profile().total_be28
            || self.parent_profile != profile
            || self.class != classify()?
            || self.map_bindings != [maps[0].binding(), maps[1].binding()]
            || self.map_bindings.iter().any(|binding| binding.parent_root.is_some())
        {
            return Err("c170 Eligible08 stage parent/cut/source identity".into());
        }
        Ok(())
    }

    fn claim_cell(&mut self, author: H21StageAuthor, cell: usize, value: bool) -> Result<(), String> {
        let allowed = match author {
            H21StageAuthor::Map(context) => self.map_reservations.get(context)
                .is_some_and(|domain| domain.contains(&cell)),
            H21StageAuthor::Slack(_) => false,
            H21StageAuthor::ScoreAnchor(context) => {
                (self.owner == 417_790 || self.owner == 845_758)
                    && Self::score_live(context).is_ok_and(|domain| domain.contains(&cell))
            }
            H21StageAuthor::ScoreModern(context) => {
                self.owner == 845_759
                    && Self::score_live(context).is_ok_and(|domain| domain.contains(&cell))
            }
            H21StageAuthor::Cap(context) => {
                self.owner == 845_759
                    && Self::cap_live(context).is_ok_and(|domain| domain.contains(&cell))
            }
            #[cfg(test)]
            H21StageAuthor::ScoreProbe(context) => {
                self.owner == 845_759 && context < 2 &&
                    (BANK53_BASE + context * BANK53_CONTEXT_BITS + BANK53_MAP_LIVE_BITS
                    ..BANK53_BASE + context * BANK53_CONTEXT_BITS + BANK53_MAP_LIVE_BITS + 2_048)
                        .contains(&cell)
            }
        };
        if !allowed { return Err("c170 cell outside author lease".into()); }
        if self.claims.contains_key(&cell) {
            return Err("c170 duplicate cell author even with equal value".into());
        }
        self.claims.insert(cell, (author, value));
        Ok(())
    }

    fn claim_map_live(&mut self, context: usize, bits: &[bool]) -> Result<(), String> {
        if bits.len() != BANK53_MAP_LIVE_BITS {
            return Err("c170 Map live source length".into());
        }
        let domain = Self::map_live(context)?;
        if domain.clone().any(|cell| self.claims.contains_key(&cell)) {
            return Err("c170 duplicate cell author even with equal value".into());
        }
        // Failure is checked before any mutation. A zero is still an authored
        // live bit; a zero in the Map tail is not an authored Score/Slack bit.
        for (cell, &bit) in domain.zip(bits) {
            self.claim_cell(H21StageAuthor::Map(context), cell, bit)?;
        }
        Ok(())
    }

}

#[path = "h21_eligible_context.rs"]
mod h21_eligible_context;
pub(crate) use h21_eligible_context::{H21EligibleContext, RequiredAuthor,
    Eligible08MapPairLease, Eligible08MapSlackBundle, Eligible08MapSlackAnchorBundle,
    Eligible08MapSlackSecondAnchorBundle,
    MapPairSourceAuthor,
    resolve_typed_map_import};
pub(crate) use h21_eligible_context::H21ClosedOwnerSource;
#[cfg(test)]
pub(crate) use h21_eligible_context::structural_roster as h21_structural_roster;
#[cfg(test)]
pub(crate) use h21_eligible_context::native_owner_values::{NativeH21OwnerValues, H21ValueCensus};
pub(crate) use h21_eligible_context::{ScoredOwnerPackingView, C509RegularRowSourceView};
pub(crate) use h21_eligible_context::ScoredOwnerPackedAuthor;
pub(crate) use h21_eligible_context::OpenScoredReadAuthor;
pub(crate) use h21_eligible_context::Eligible08RegularScoreOwner;
pub(crate) use h21_eligible_context::{Eligible08ForeignMaxCell, Eligible08ForeignMaxReadLease};
pub(crate) use h21_eligible_context::Eligible08MapSourceView;
pub(crate) use h21_eligible_context::{Eligible08CompleteRowSourceView,
    Eligible08ScoreImportKind, Eligible08SlackCellAuthor, Bank53TypedAuthor,
    ScoreRelationReadAuthor, ScoreReplayAuthor};
#[cfg(test)]
pub(crate) use h21_eligible_context::Eligible08OwnerSink;
use h21_eligible_context::{Bank53TypedSourceLease, Eligible08CheckedLocalCells,
    Eligible08PackedOverlay, Eligible08ScoreAnchorCell, OpenScoredRead,
};

#[path = "h21_clipped_score_read_authors.rs"]
mod h21_clipped_score_read_authors;
pub(crate) use h21_clipped_score_read_authors::ClippedScoreReadAuthorBundle;

#[path = "h21_eligible_slack.rs"]
mod h21_eligible_slack;

#[path = "h21_first_modern_ledger.rs"]
mod h21_first_modern_ledger;
pub(crate) use h21_first_modern_ledger::FirstModernDestination;

#[cfg(test)]
mod c170_eligible_stage_tests {
    use super::*;

    fn parent(root: [u8; 32], total: [u8; 28]) -> WorkTreeHistoryPlan {
        WorkTreeHistoryPlan::compile(1_827_840, 21, root, total).unwrap()
    }

    #[test]
    fn map_live_parent_mask_is_exact_and_exclusive() {
        let plan = parent([0x5a; 32], [0x31; 28]);
        let mask = plan.physical_assignment_replacement_mask(845_759).unwrap();
        H21EligibleMapStage::require_header_owned_map_live(&mask).unwrap();
        let mut wrong = mask.clone(); wrong[H21EligibleMapStage::map_live(0).unwrap().start] = true;
        assert_eq!(H21EligibleMapStage::require_header_owned_map_live(&wrong).unwrap_err(),
            "c170 Map LIVE must be HEADER-owned in parent mask");
        let mut wrong = mask.clone(); wrong[H21EligibleMapStage::map_live(1).unwrap().end - 1] = true;
        assert_eq!(H21EligibleMapStage::require_header_owned_map_live(&wrong).unwrap_err(),
            "c170 Map LIVE must be HEADER-owned in parent mask");
        assert_eq!(H21EligibleMapStage::require_header_owned_map_live(&mask[..WIDTH - 1]).unwrap_err(),
            "c170 parent replacement mask width");
    }

    #[test]
    fn map_live_tail_and_score_probe_keep_distinct_authors() {
        let plan = parent([0x5a; 32], [0x31; 28]);
        let maps = H21EligibleMapStage::source_maps().unwrap();
        let mut stage = H21EligibleMapStage::new_empty(
            &plan, [0x42; 32], 845_759, H21EligibleMapStage::descriptor(), &maps).unwrap();
        stage.claim_map_live(0, &vec![false; BANK53_MAP_LIVE_BITS]).unwrap();
        let score_first = 677_501;
        assert!(!stage.claims.contains_key(&score_first));
        stage.claim_cell(H21StageAuthor::ScoreProbe(0), score_first, false).unwrap();
        assert_eq!(stage.claims.get(&score_first), Some(&(H21StageAuthor::ScoreProbe(0), false)));
        assert_eq!(stage.claim_cell(H21StageAuthor::Map(0), score_first, false).unwrap_err(),
            "c170 cell outside author lease");
        assert_eq!(stage.claim_cell(H21StageAuthor::Map(0), 671_744, false).unwrap_err(),
            "c170 duplicate cell author even with equal value");
        let before = stage.claims.clone();
        assert_eq!(stage.claim_map_live(0, &vec![false; BANK53_MAP_LIVE_BITS]).unwrap_err(),
            "c170 duplicate cell author even with equal value");
        assert_eq!(stage.claims, before);
        assert_eq!(stage.claim_cell(H21StageAuthor::ScoreProbe(0), score_first, false).unwrap_err(),
            "c170 duplicate cell author even with equal value");
        assert_eq!(stage.claim_cell(H21StageAuthor::ScoreProbe(1), score_first, false).unwrap_err(),
            "c170 cell outside author lease");
        let mut inactive = H21EligibleMapStage::new_empty(
            &plan, [0x42; 32], 844_670, H21EligibleMapStage::descriptor(), &maps).unwrap();
        assert_eq!(inactive.claim_cell(H21StageAuthor::ScoreProbe(0), score_first, false).unwrap_err(),
            "c170 cell outside author lease");
        inactive.claim_map_live(1, &vec![false; BANK53_MAP_LIVE_BITS]).unwrap();
        assert!(!inactive.claims.contains_key(&685_693));
    }

    #[test]
    fn stage_rejects_wrong_parent_cut_context_and_rooted_cut_binding() {
        let plan = parent([0x5a; 32], [0x31; 28]);
        let maps = H21EligibleMapStage::source_maps().unwrap();
        let stage = H21EligibleMapStage::new_empty(
            &plan, [0x42; 32], 844_670, H21EligibleMapStage::descriptor(), &maps).unwrap();
        stage.validate_identity(&plan, [0x42; 32], H21EligibleMapStage::descriptor(), &maps).unwrap();
        assert!(stage.validate_identity(&parent([0x5b; 32], [0x31; 28]),
            [0x42; 32], H21EligibleMapStage::descriptor(), &maps).is_err());
        assert!(stage.validate_identity(&parent([0x5a; 32], [0x32; 28]),
            [0x42; 32], H21EligibleMapStage::descriptor(), &maps).is_err());
        assert!(stage.validate_identity(&plan, [0x43; 32], H21EligibleMapStage::descriptor(), &maps).is_err());
        assert!(H21EligibleMapStage::new_empty(&plan, [0x42; 32], 844_670,
            crate::bank53_map::CutDescriptor::diagnostic08(), &maps).is_err());
        let mut swapped = maps.clone(); swapped.swap(0, 1);
        assert!(H21EligibleMapStage::new_empty(&plan, [0x42; 32], 844_670,
            H21EligibleMapStage::descriptor(), &swapped).is_err());
        let mut old_cut = maps.clone();
        old_cut[1] = crate::legacy_envelope_map::Map::new_modern_global_u_selected_lower(
            1_827_775, 21, 55,
            crate::legacy_envelope_map::LowerSelector {
                source: crate::legacy_envelope_map::LowerSource::HeaderDifficulty {height: 841_729},
                branch: crate::legacy_envelope_map::LowerBranch::Pivot(54),
            }).unwrap();
        assert!(H21EligibleMapStage::new_empty(&plan, [0x42; 32], 844_670,
            H21EligibleMapStage::descriptor(), &old_cut).is_err());
        let mut rooted = maps.clone();
        rooted[0] = crate::legacy_envelope_map::Map::from_parent_modern_global_u(
            &plan, 55,
            crate::legacy_envelope_map::LowerSelector {
                source: crate::legacy_envelope_map::LowerSource::HeaderDifficulty {height: 841_729},
                branch: crate::legacy_envelope_map::LowerBranch::Pivot(54),
            }).unwrap();
        assert!(H21EligibleMapStage::new_empty(&plan, [0x42; 32], 844_670,
            H21EligibleMapStage::descriptor(), &rooted).is_err());
        assert!(stage.validate_identity(&plan, [0x42; 32],
            crate::bank53_map::CutDescriptor::diagnostic08(), &maps).is_err());
    }

    #[test]
    fn zero_root_parent_is_bound_by_equality_not_sentinel() {
        let plan = parent([0; 32], [0x31; 28]);
        let maps = H21EligibleMapStage::source_maps().unwrap();
        let stage = H21EligibleMapStage::new_empty(
            &plan, [0x42; 32], 845_759, H21EligibleMapStage::descriptor(), &maps).unwrap();
        assert_eq!(stage.parent_root, [0; 32]);
        stage.validate_identity(&plan, [0x42; 32], H21EligibleMapStage::descriptor(), &maps).unwrap();
        assert!(stage.validate_identity(&parent([1; 32], [0x31; 28]),
            [0x42; 32], H21EligibleMapStage::descriptor(), &maps).is_err());
    }
}
impl<'a> NativeOwnerProducer<'a> {
    pub(crate) fn work_local_parent(&self,owner:usize)->Result<crate::h21_work_local_source::Parent,String> {
        validate_native_plan_input(self.plan,self.input)?;
        if owner>=self.plan.descriptor().genuine || self.max_adapter.is_some() {
            return Err("Work LOCAL genuine unadapted source".into());
        }
        #[cfg(test)]
        if self.legacy_adapter.is_some(){return Err("Work LOCAL legacy adapted source".into());}
        Ok(crate::h21_work_local_source::Parent{root:self.input.root(),total:self.input.total_be28(),
            profile:self.input.profile(),headers:self.plan.headers(),slots:self.plan.slots(),
            cut:crate::bank53_map::CutDescriptor::eligible08().canonical_identity()})
    }
    pub(crate) fn work_local_native_parent(&self)->Result<crate::h21_scheduled_max_cap::NativeParent,String> {
        crate::h21_scheduled_max_cap::NativeParent::checked(self.plan,self.input)
    }
    /// Mint from the actual production packed assignment. The retained immutable
    /// row and exact producer reference are local custody, never a PCS identity.
    pub(crate) fn work_local_lease(&self,owner:usize)->Result<WorkLocalLease<'_>,String> {
        let parent=self.work_local_parent(owner)?;
        let row=self.produce(owner)?;
        let operands=crate::h21_work_local_source::operand_domain(owner)?.into_iter().map(|wire|
            (wire,Fr::from(((row.bytes[(wire%WIDTH)/8]>>((wire%WIDTH)%8))&1)as u64))).collect();
        let lease=WorkLocalLease{source:self,parent,owner,height:owner+2,row,
            terms:crate::h21_work_local_source::canonical_terms(self.plan,owner)?,operands,
            d:self.native_work_d_projection(owner)?};
        self.require_work_local_lease(owner,&lease)?;Ok(lease)
    }
    /// Capture Tree claims during the same single owner-row production that
    /// supplies the Work LOCAL values. No second equal-byte row is accepted.
    pub(crate) fn work_endpoint_author_lease(&self, owner: usize)
        -> Result<NativeWorkEndpointAuthorLease<'_>, String> {
        let _parent = self.work_local_parent(owner)?;
        if !C512I_WORK_OWNERS.contains(&owner)
            || self.plan.headers() != 1_827_840 || self.plan.slot_log() != 21
            || self.plan.slots() != 1 << 21 || self.input.header_count() != 1_827_840 {
            return Err("C512i Work endpoint exact H21 owner/plan".into());
        }
        self.c578_work_endpoint_core(owner)
    }
    /// Generic ordinary policy, not admission for a coactive Work/MAX row.
    fn c578_require_ordinary_work_capture(&self, owner:usize) -> Result<(),String> {
        self.work_local_parent(owner)?;
        let class = self.roster.owner_class(owner as u64)?;
        if owner == 0 || self.plan.headers()!=1_827_840 || self.plan.slot_log()!=21
            || self.plan.slots()!=1<<21 || self.input.header_count()!=1_827_840
            || self.plan.leaf_profile().role(owner)? != leaf::Role::Genuine {
            return Err("C578 ordinary Work genuine H21 geometry".into());
        }
        c578_ordinary_work_policy(owner,class)
    }
    pub(crate) fn ordinary_work_upper_author_lease(&self,owner:usize)
        -> Result<NativeWorkEndpointAuthorLease<'_>,String> {
        self.c578_require_ordinary_work_capture(owner)?;
        self.c578_work_endpoint_core(owner)
    }
    fn c578_work_endpoint_core(&self,owner:usize)
        -> Result<NativeWorkEndpointAuthorLease<'_>,String> {
        let parent = self.work_local_parent(owner)?;
        self.c578_require_ordinary_work_capture(owner)?;
        let binding = HeaderSourceBinding::for_plan(self.plan, owner)?;
        if binding.profile() != self.input.profile() {
            return Err("C512i Work endpoint source profile".into());
        }
        let tree = NativeTreeSourceLease::from_prefix(self.plan, self.input, owner)?;
        tree.check_binding(&binding)?;
        tree.check_author()?;
        let mut capture_out = None;
        let row = self.produce_inner_with_cap0_and_c496(
            owner, AssemblyFault::None, None,
            #[cfg(test)] None,
            #[cfg(test)] false,
            #[cfg(test)] None,
            None, // DAA source output
            None, // Cap0
            None, // Cap1
            None, // overlay
            None, // C374 author census
            None, // Scored source
            None, // Map source
            None, // padding HeaderZero
            None, // mixed Map/Header
            None, // genesis HeaderZero
            None, // C496 clipped HeaderZero
            None, // C498 clipped Score source
            None, // C498 capture output
            None, // regular census
            None, // MAX source
            None, // MAX claims
            Some(&mut capture_out),
            None, // private coactive admission
        )?;
        let operands=crate::h21_work_local_source::operand_domain(owner)?.into_iter().map(|wire|
            (wire,Fr::from(((row.bytes[(wire%WIDTH)/8]>>((wire%WIDTH)%8))&1)as u64))).collect();
        let local=WorkLocalLease{source:self,parent,owner,height:owner+2,row,
            terms:crate::h21_work_local_source::canonical_terms(self.plan,owner)?,operands,
            d:self.native_work_d_projection(owner)?};
        self.require_work_local_lease(owner,&local)?;
        let lease=NativeWorkEndpointAuthorLease {
            local,tree,binding,
            capture:capture_out.ok_or("C512i Tree claim-event capture not returned")?,
            complete_checked:Cell::new(false),
        };
        lease.check_complete()?;
        Ok(lease)
    }
    pub(crate) fn require_work_local_lease(&self,owner:usize,lease:&WorkLocalLease<'_>)->Result<(),String> {
        if !std::ptr::eq(self,lease.source) {
            return Err("Work LOCAL exact producer source identity".into());
        }
        let parent=self.work_local_parent(owner)?;
        if lease.parent!=parent || lease.owner!=owner || lease.height!=owner+2 {
            return Err("Work LOCAL exact parent/cut/owner/height".into());
        }
        let row=&lease.row;
        if row.owner!=owner || row.root!=parent.root || row.total!=parent.total
            || row.class!=self.roster.owner_class(owner as u64)? || row.bytes.len()!=WIDTH/8
            || row.max_binding.is_some() || row.map_binding.is_some() || row.map_context.is_some() {
            return Err("Work LOCAL packed source row identity".into());
        }
        #[cfg(test)]
        if row.legacy_binding.is_some(){return Err("Work LOCAL legacy packed source".into());}
        let domain=crate::h21_work_local_source::operand_domain(owner)?;
        if lease.operands.len()!=domain.len(){return Err("Work LOCAL complete operand census".into());}
        for (&wire,&(actual,value)) in domain.iter().zip(&lease.operands) {
            let local=wire%WIDTH;
            let packed=Fr::from(((row.bytes[local/8]>>(local%8))&1)as u64);
            if actual!=wire || value!=packed || value!=Fr::from(self.exports.bit(wire)?as u64) {
                return Err("Work LOCAL exact packed/native active operand".into());
            }
        }
        if lease.d!=self.native_work_d_projection(owner)? {
            return Err("Work LOCAL exact native D projection".into());
        }
        for &(wire,value) in &lease.d {
            if !lease.operands.iter().any(|&(w,v)|w==wire&&v==value) {
                return Err("Work LOCAL packed D mismatch".into());
            }
        }
        if lease.terms!=crate::h21_work_local_source::canonical_terms(self.plan,owner)? {
            return Err("Work LOCAL exact canonical tagged term occurrences".into());
        }
        crate::h21_work_local_source::require_zero_residual(&lease.terms,&lease.operands)?;
        Ok(())
    }
    pub(crate) fn native_work_local_lease(&self)->Result<NativeWorkLocalLease<'_>,String> {
        self.native_work_local_lease_for_owner(crate::h21_work_local_source::H21_OWNER)
    }
    pub(crate) fn native_work_local_lease_for_owner(&self,owner:usize)->Result<NativeWorkLocalLease<'_>,String> {
        let parent=self.work_local_native_parent()?;
        let local=self.work_local_lease(owner)?;
        Ok(NativeWorkLocalLease{parent,local})
    }
    pub(crate) fn require_native_work_local_lease(&self,parent:&crate::h21_scheduled_max_cap::NativeParent,
        lease:&NativeWorkLocalLease<'_>)->Result<(),String> {
        self.require_native_work_local_lease_for_owner(parent,crate::h21_work_local_source::H21_OWNER,lease)
    }
    pub(crate) fn require_native_work_local_lease_for_owner(&self,parent:&crate::h21_scheduled_max_cap::NativeParent,
        owner:usize,lease:&NativeWorkLocalLease<'_>)->Result<(),String> {
        let expected=self.work_local_native_parent()?;
        if parent!=&expected || lease.parent!=expected {
            return Err("Work LOCAL exact NativeParent/cut".into());
        }
        self.require_work_local_lease(owner,&lease.local)
    }
    #[cfg(test)]
    pub(crate) fn c432_worklocal_boundary_authors(
        &self,
        parent:&crate::h21_scheduled_max_cap::NativeParent,
        owner:usize,
        lease:&NativeWorkLocalLease<'_>,
        fault:Option<C433TreeAuthorFault>,
    )->Result<[(usize,NativePhysicalAuthor,bool);4],String> {
        self.require_native_work_local_lease_for_owner(parent,owner,lease)?;
        if !matches!(owner,845_757|845_758) {
            return Err("C432 boundary source owner".into());
        }
        let binding=HeaderSourceBinding::for_plan(self.plan,owner)?;
        let mut header=self.header_source_lease(owner)?;
        let mut tree=NativeTreeSourceLease::from_prefix(self.plan,self.input,owner)?;
        match fault {
            Some(C433TreeAuthorFault::TreeAuthor)=>tree.author=TreeLeaseAuthor::Other,
            Some(C433TreeAuthorFault::TreeBinding)=>tree.binding.owner+=1,
            Some(C433TreeAuthorFault::UpperTreeOmission)=>tree.owned[987_672/8]&=!(1<<(987_672%8)),
            Some(C433TreeAuthorFault::ExponentTreeOmission)=>tree.owned[987_898/8]&=!(1<<(987_898%8)),
            Some(C433TreeAuthorFault::UpperHeaderMask)=>NativeHeaderSourceLease::set(
                &mut header.owned,987_672),
            Some(C433TreeAuthorFault::ExponentHeaderMask)=>NativeHeaderSourceLease::set(
                &mut header.owned,987_898),
            Some(C433TreeAuthorFault::UpperTreeValue)=>tree.values[987_672/8]^=1<<(987_672%8),
            Some(C433TreeAuthorFault::ExponentTreeValue)=>tree.values[987_898/8]^=1<<(987_898%8),
            None=>(),
        }
        self.c432_check_worklocal_boundary_authority(parent,owner,lease,&binding,&header,&tree)
    }
    #[cfg(test)]
    fn c432_check_worklocal_boundary_authority(
        &self,
        parent:&crate::h21_scheduled_max_cap::NativeParent,
        owner:usize,
        lease:&NativeWorkLocalLease<'_>,
        binding:&HeaderSourceBinding,
        header:&NativeHeaderSourceLease,
        tree:&NativeTreeSourceLease,
    )->Result<[(usize,NativePhysicalAuthor,bool);4],String> {
        self.require_native_work_local_lease_for_owner(parent,owner,lease)?;
        if owner!=845_757&&owner!=845_758 {
            return Err("C432 boundary source owner".into());
        }
        let expected_binding=HeaderSourceBinding::for_plan(self.plan,owner)?;
        if binding!=&expected_binding {return Err("C432 boundary expected binding".into());}
        header.check_binding(binding)?;
        header.check_author()?;
        tree.check_binding(binding)?;
        tree.check_author()?;
        let replacement_mask=self.plan.physical_assignment_replacement_mask(owner as u64)?;
        if replacement_mask.len()!=WIDTH {return Err("C433 Tree replacement mask width".into());}
        let owner_base=owner.checked_mul(WIDTH).ok_or("C432 WorkLocal owner overflow")?;
        let row=&lease.local.row;
        let cells=[987_672usize,987_673,987_898,987_899];
        let mut result=[(0,NativePhysicalAuthor::Tree,false);4];
        for (index,local) in cells.into_iter().enumerate() {
            let wire=owner_base.checked_add(local).ok_or("C432 boundary wire overflow")?;
            let operand=lease.local.operands.iter().find(|(candidate,_)|*candidate==wire)
                .ok_or("C432 boundary missing checked WorkLocal operand")?;
            let packed=((row.bytes[local/8]>>(local%8))&1)!=0;
            let value=operand.1==Fr::one();
            if operand.1!=Fr::zero()&&operand.1!=Fr::one() || value!=packed {
                return Err(format!("C432 WorkLocal packed/operand mismatch wire={wire}"));
            }
            if header.read_header_bit(binding,wire)?.is_some() {
                return Err(format!("C433 Tree boundary has opposing HEADER author wire={wire}"));
            }
            if !replacement_mask[local]||!NativeHeaderSourceLease::bit(&tree.owned,local) {
                return Err(format!("C433 missing Tree author/mask wire={wire}"));
            }
            let source_value=NativeHeaderSourceLease::bit(&tree.values,local);
            if source_value!=value || source_value!=packed {
                return Err(format!("C433 Tree/WorkLocal value mismatch wire={wire}"));
            }
            result[index]=(wire,NativePhysicalAuthor::Tree,source_value);
        }
        Ok(result)
    }
    #[cfg(test)]
    pub(crate) fn c432_boundary_authority_faults_rejected(
        &self,
        parent:&crate::h21_scheduled_max_cap::NativeParent,
        owner:usize,
        lease:&NativeWorkLocalLease<'_>,
    )->Result<(),String> {
        self.require_native_work_local_lease_for_owner(parent,owner,lease)?;
        let binding=HeaderSourceBinding::for_plan(self.plan,owner)?;
        let header=self.header_source_lease(owner)?;
        let tree=NativeTreeSourceLease::from_prefix(self.plan,self.input,owner)?;
        for fault in [
            C433TreeAuthorFault::TreeAuthor,
            C433TreeAuthorFault::TreeBinding,
            C433TreeAuthorFault::UpperTreeOmission,
            C433TreeAuthorFault::ExponentTreeOmission,
            C433TreeAuthorFault::UpperHeaderMask,
            C433TreeAuthorFault::ExponentHeaderMask,
            C433TreeAuthorFault::UpperTreeValue,
            C433TreeAuthorFault::ExponentTreeValue,
        ] {
            let mut changed_header=header.clone();
            let mut changed_tree=tree.clone();
            match fault {
                C433TreeAuthorFault::TreeAuthor=>changed_tree.author=TreeLeaseAuthor::Other,
                C433TreeAuthorFault::TreeBinding=>changed_tree.binding.owner+=1,
                C433TreeAuthorFault::UpperTreeOmission=>changed_tree.owned[987_672/8]&=!(1<<(987_672%8)),
                C433TreeAuthorFault::ExponentTreeOmission=>changed_tree.owned[987_898/8]&=!(1<<(987_898%8)),
                C433TreeAuthorFault::UpperHeaderMask=>NativeHeaderSourceLease::set(
                    &mut changed_header.owned,987_672),
                C433TreeAuthorFault::ExponentHeaderMask=>NativeHeaderSourceLease::set(
                    &mut changed_header.owned,987_898),
                C433TreeAuthorFault::UpperTreeValue=>changed_tree.values[987_672/8]^=1<<(987_672%8),
                C433TreeAuthorFault::ExponentTreeValue=>changed_tree.values[987_898/8]^=1<<(987_898%8),
            }
            if self.c432_check_worklocal_boundary_authority(parent,owner,lease,&binding,
                &changed_header,&changed_tree).is_ok() {
                return Err(format!("C432 author boundary accepted isolated fault {fault:?}"));
            }
        }
        Ok(())
    }
    #[cfg(test)]
    pub(crate) fn c434_exponent_tree_octet_authority(
        &self,
        parent:&crate::h21_scheduled_max_cap::NativeParent,
        owner:usize,
        lease:&NativeWorkLocalLease<'_>,
        fault:Option<C434TreeAuthorFault>,
    )->Result<[(usize,NativePhysicalAuthor,bool);4],String> {
        self.require_native_work_local_lease_for_owner(parent,owner,lease)?;
        if !matches!(owner,845_757|845_758) {
            return Err("C434 exponent Tree source owner".into());
        }
        let binding=HeaderSourceBinding::for_plan(self.plan,owner)?;
        let mut header=self.header_source_lease(owner)?;
        let mut tree=NativeTreeSourceLease::from_prefix(self.plan,self.input,owner)?;
        match fault {
            Some(C434TreeAuthorFault::TreeAuthor)=>tree.author=TreeLeaseAuthor::Other,
            Some(C434TreeAuthorFault::TreeBinding)=>tree.binding.owner+=1,
            Some(C434TreeAuthorFault::TreeOmissionLast)=>
                tree.owned[987_903/8]&=!(1<<(987_903%8)),
            Some(C434TreeAuthorFault::HeaderMaskLast)=>
                NativeHeaderSourceLease::set(&mut header.owned,987_903),
            Some(C434TreeAuthorFault::TreeValueLast)=>
                tree.values[987_903/8]^=1<<(987_903%8),
            None=>(),
        }
        self.c434_check_exponent_tree_octet_authority(
            parent,owner,lease,&binding,&header,&tree)
    }
    #[cfg(test)]
    fn c434_check_exponent_tree_octet_authority(
        &self,
        parent:&crate::h21_scheduled_max_cap::NativeParent,
        owner:usize,
        lease:&NativeWorkLocalLease<'_>,
        binding:&HeaderSourceBinding,
        header:&NativeHeaderSourceLease,
        tree:&NativeTreeSourceLease,
    )->Result<[(usize,NativePhysicalAuthor,bool);4],String> {
        self.require_native_work_local_lease_for_owner(parent,owner,lease)?;
        if owner!=845_757&&owner!=845_758 {
            return Err("C434 exponent Tree source owner".into());
        }
        let expected_binding=HeaderSourceBinding::for_plan(self.plan,owner)?;
        if binding!=&expected_binding {return Err("C434 exponent Tree expected binding".into());}
        header.check_binding(binding)?;
        header.check_author()?;
        tree.check_binding(binding)?;
        tree.check_author()?;
        if tree.values.len()!=WIDTH/8 || tree.owned.len()!=WIDTH/8 {
            return Err("C434 Tree source packed width".into());
        }
        let replacement_mask=self.plan.physical_assignment_replacement_mask(owner as u64)?;
        if replacement_mask.len()!=WIDTH {return Err("C434 Tree replacement mask width".into());}
        let owner_base=owner.checked_mul(WIDTH).ok_or("C434 WorkLocal owner overflow")?;
        let row=&lease.local.row;
        let cells=[987_900usize,987_901,987_902,987_903];
        let mut result=[(0,NativePhysicalAuthor::Tree,false);4];
        for (index,local) in cells.into_iter().enumerate() {
            let wire=owner_base.checked_add(local).ok_or("C434 exponent Tree wire overflow")?;
            let operand=lease.local.operands.iter().find(|(candidate,_)|*candidate==wire)
                .ok_or("C434 missing checked WorkLocal Exponent operand")?;
            let packed=((row.bytes[local/8]>>(local%8))&1)!=0;
            if operand.1!=Fr::zero()&&operand.1!=Fr::one() {
                return Err(format!("C434 WorkLocal Exponent operand nonboolean wire={wire}"));
            }
            let value=operand.1==Fr::one();
            if value!=packed {
                return Err(format!("C434 WorkLocal Exponent packed/operand mismatch wire={wire}"));
            }
            if header.read_header_bit(binding,wire)?.is_some() {
                return Err(format!("C434 Exponent Tree has opposing HEADER author wire={wire}"));
            }
            if !replacement_mask[local]||!NativeHeaderSourceLease::bit(&tree.owned,local) {
                return Err(format!("C434 missing Exponent Tree author/mask wire={wire}"));
            }
            let source_value=NativeHeaderSourceLease::bit(&tree.values,local);
            if source_value!=value||source_value!=packed {
                return Err(format!("C434 Exponent Tree/WorkLocal value mismatch wire={wire}"));
            }
            result[index]=(wire,NativePhysicalAuthor::Tree,source_value);
        }
        Ok(result)
    }
    #[cfg(test)]
    pub(crate) fn c434_exponent_tree_octet_faults_rejected(
        &self,
        parent:&crate::h21_scheduled_max_cap::NativeParent,
        owner:usize,
        lease:&NativeWorkLocalLease<'_>,
    )->Result<(),String> {
        self.require_native_work_local_lease_for_owner(parent,owner,lease)?;
        for fault in [
            C434TreeAuthorFault::TreeAuthor,
            C434TreeAuthorFault::TreeBinding,
            C434TreeAuthorFault::TreeOmissionLast,
            C434TreeAuthorFault::HeaderMaskLast,
            C434TreeAuthorFault::TreeValueLast,
        ] {
            if self.c434_exponent_tree_octet_authority(parent,owner,lease,Some(fault)).is_ok() {
                return Err(format!("C434 accepted isolated Exponent Tree source fault {fault:?}"));
            }
        }
        Ok(())
    }
    pub(crate) fn work_upper_publication(&self,owner:usize,lease:&WorkLocalLease<'_>)
        ->Result<WorkUpperPublication,String> {
        self.require_work_local_lease(owner,lease)?;
        let endpoints=&crate::work_tree_layout::shared_baseline()?.endpoints;
        if endpoints.upper!=(987450..987674).collect::<Vec<_>>() {
            return Err("Work Upper physical endpoint domain changed".into());
        }
        let upper=endpoints.upper.iter().map(|local| {
            let wire=owner*WIDTH+local;
            lease.operands.iter().copied().find(|(w,_)|*w==wire)
                .ok_or_else(||"Work Upper missing physical source operand".to_string())
        }).collect::<Result<Vec<_>,_>>()?;
        let out=WorkUpperPublication{parent:lease.parent.clone(),owner,height:lease.height,
            terms:lease.terms.clone(),operands:lease.operands.clone(),upper};
        out.checked_upper(lease.parent.root,lease.parent.total,lease.parent.profile,&lease.parent.cut,owner)?;
        Ok(out)
    }
    /// Reuses the exact physical endpoint export also written by produce().
    /// This scalar projection never expands a complete owner assignment.
    pub(crate) fn native_work_d_projection(&self,owner:usize)->Result<Vec<(usize,Fr)>,String> {
        if owner>=self.plan.descriptor().genuine {return Err("native Work-D requires genuine work owner".into());}
        let endpoints=&crate::work_tree_layout::shared_baseline()?.endpoints;
        if endpoints.work!=(987674..987898).collect::<Vec<_>>() {
            return Err("native Work-D physical endpoint domain changed".into());
        }
        endpoints.work.iter().map(|local| {
            let wire=owner*WIDTH+local;
            Ok((wire,Fr::from(self.exports.bit(wire)? as u64)))
        }).collect()
    }
    pub(crate) fn native_work_d_lease(&self,owner:usize)->Result<NativeWorkDLease,String> {
        let parent=crate::h21_scheduled_max_cap::NativeParent::checked(self.plan,self.input)?;
        let cells=self.native_work_d_projection(owner)?;
        let lease=NativeWorkDLease{parent,owner,height:owner+2,cells};
        lease.checked_cells(&lease.parent,owner)?;Ok(lease)
    }
    /// Mint the independent native point-membership witness for the fixed
    /// H21 owner directly from its canonical prefix header.
    pub(crate) fn point_membership_source_lease(
        &self,
        owner: usize,
    ) -> Result<NativePointMembershipSourceLease, String> {
        if owner != POINT_MEMBERSHIP_OWNER {
            return Err("point-membership source fixed owner".into());
        }
        // This gate checks canonical H21 plan/input and point-bank layout;
        // its projection helper does not derive point witness values.
        let _projection = self.h21_point_projection()?;
        let binding = HeaderSourceBinding::for_plan(self.plan, owner)?;
        let expected_cut = crate::bank53_map::CutDescriptor::eligible08().canonical_identity();
        if binding.owner != owner || binding.root != self.input.root()
            || binding.total != self.input.total_be28()
            || binding.profile != self.input.profile() || binding.cut != expected_cut
        {
            return Err("point-membership source canonical plan/input/profile/cut binding".into());
        }
        let height = owner.checked_add(1).ok_or("point-membership source height overflow")?;
        let header = self.input.header(height)?;
        if header.height as usize != height
            || header.encode().map_err(|error| format!("point-membership header encode: {error:?}"))?
                != self.input.raw(height)?
        {
            return Err("point-membership source canonical header binding".into());
        }
        let fields = crate::serializer::Fields::from_header(&header)?;
        NativePointMembershipSourceLease::from_fields(binding, owner, &fields)
    }

    /// Mint one HEADER source from the same native template and replacement
    /// mask used by the packed owner writer. Future DAA, Map/Score/Slack,
    /// and active scheduled domains remain unresolved here.
    pub(crate) fn header_source_lease(&self,owner:usize)->Result<NativeHeaderSourceLease,String> {
        crate::h21_scheduled_max_cap::NativeParent::checked(self.plan,self.input)?;
        if self.max_adapter.is_some(){return Err("HEADER source rejects MAX adapter mixing".into());}
        #[cfg(test)]
        if self.legacy_adapter.is_some(){return Err("HEADER source rejects legacy adapter mixing".into());}
        let binding=HeaderSourceBinding::for_plan(self.plan,owner)?;
        if binding.profile!=self.input.profile(){return Err("HEADER source native profile drift".into());}
        let height=(owner+1).min(self.input.header_count());
        let header=self.input.header(height)?;
        let previous=if height==1{None}else{Some(self.input.header(height-1)?)};
        let fields=crate::serializer::Fields::from_header(&header)?;
        let mut native=self.header_template.assign(&fields)?;
        self.header_template.assign_order(&mut native,&fields,
            previous.as_ref().map_or(0,|h|h.height),
            previous.as_ref().map_or(0,|h|h.timestamp),height==1)?;
        let mask=self.plan.physical_assignment_replacement_mask(owner as u64)?;
        if native.len()!=WIDTH || mask.len()!=WIDTH{return Err("HEADER source native assignment/mask width".into());}
        // The first modern Cap owner is not a scheduled MAX owner. Its two
        // MAX-coordinate windows are written by the ordinary HEADER seed;
        // only the adjacent active Cap windows have another author. Check
        // the fixed schedule before exposing these HEADER bits.
        let first_modern_header_max=if owner==845_759 {
            let calendar=crate::h21_scheduled_max_cap::Plan::eligible08().max_calendar();
            if calendar.iter().any(|(at,_)|*at==owner)
                || mask[999_424..1_000_770].iter().any(|replaced|*replaced) {
                return Err("first modern HEADER MAX-window author collision".into());
            }
            true
        } else {false};
        let mut values=vec![0;OWNER_BYTES];let mut owned=vec![0;OWNER_BYTES];
        for (wire,&value) in native.iter().enumerate() {
            let other_author=BANKS.iter().any(|&(lo,hi)|(lo..hi).contains(&wire))
                || (BANK53_BASE..BANK53_BASE+BANK53_CONTEXTS*BANK53_CONTEXT_BITS).contains(&wire)
                || (786_432..794_624).contains(&wire)
                || ((999_424..1_004_866).contains(&wire)
                    && !(first_modern_header_max && (999_424..1_000_770).contains(&wire)));
            if mask[wire] || other_author {continue;}
            if value!=Fr::zero() && value!=Fr::one(){return Err("HEADER source nonboolean native assignment".into());}
            NativeHeaderSourceLease::set(&mut owned,wire);
            if value==Fr::one(){NativeHeaderSourceLease::set(&mut values,wire);}
        }
        Ok(NativeHeaderSourceLease{binding,author:HeaderLeaseAuthor::NativeHeader,
            values,owned,#[cfg(test)] read_count:Cell::new(0)})
    }
    /// Qualify only the active Point and unscheduled MAX/Cap anchor reads of
    /// the first post-EIP Carry ROW. The ordinary HEADER seed writes these
    /// cells at this owner; a physical-author replay rejects even equal-value
    /// writes from Tree or DAA before extending the conservative base lease.
    pub(crate) fn carry_header_source_lease_for_row(
        &self,
        batch: &crate::header_daa_row_placement::Batch,
        row: &NativePackedRow,
    ) -> Result<(NativeHeaderSourceLease, [usize; 3]), String> {
        use crate::daa_history_roster::OwnerClass;
        use crate::header_daa_row_placement::{OperandSide, Relation};

        const OWNER: usize = MATURE_EIP_SOURCE_OWNER + 1;
        const POINT_READS: usize = 528;
        const ANCHOR_START: usize = 999_424;
        const ANCHOR_COUNT: usize = 5_442;
        const ANCHOR_ROW: usize = 356_632;
        let binding = HeaderSourceBinding::for_plan(self.plan, OWNER)?;
        batch.require_owner_parent(self.plan, OWNER)?;
        row.require_header_source_binding(&binding, OWNER, OwnerClass::Carry)?;
        if self.roster.owner_class(OWNER as u64)? != OwnerClass::Carry
            || self.max_adapter.is_some() || row.cap0_source.is_some()
            || row.cap1_source.is_some()
        {
            return Err("C387 Carry HEADER source requires ordinary unspecialized writer".into());
        }
        #[cfg(test)]
        if self.legacy_adapter.is_some() {
            return Err("C387 Carry HEADER source rejects legacy writer".into());
        }
        require_no_scheduled_max_cap(OWNER)?;
        let tree_mask = self.plan.physical_assignment_replacement_mask(OWNER as u64)?;
        if tree_mask.len() != WIDTH {
            return Err("C387 Carry Tree replacement mask width".into());
        }
        let base = OWNER.checked_mul(WIDTH).ok_or("C387 Carry physical base overflow")?;
        let point_start = crate::segment_points::POINT_OFFSET;
        let point_end = point_start + crate::point_membership::POINT_WIDTH;
        let mut point_wires = BTreeSet::new();
        let mut anchor_wires = BTreeSet::new();
        for operand in batch.active_operands() {
            let Some(local) = operand.wire.checked_sub(base).filter(|wire| *wire < WIDTH) else {
                continue;
            };
            let point = (point_start..point_end).contains(&local);
            let anchor = (ANCHOR_START..ANCHOR_START + ANCHOR_COUNT).contains(&local);
            if !point && !anchor { continue; }
            if operand.relation != Relation::Header || operand.side != OperandSide::Left
                || !operand.c1_active || operand.c2_active || operand.c3_active
                || tree_mask[local]
                || BANKS.iter().any(|&(lo, hi)| (lo..hi).contains(&local))
                || (BANK53_BASE..BANK53_BASE + BANK53_CONTEXTS * BANK53_CONTEXT_BITS)
                    .contains(&local)
            {
                return Err(format!("C387 Carry active HEADER physical author wire{local}"));
            }
            if point {
                if !(point_start + 1..point_start + 1 + POINT_READS).contains(&local)
                    || !point_wires.insert(local)
                {
                    return Err(format!("C387 Carry Point ROW source or duplicate wire{local}"));
                }
            } else {
                if operand.row != OWNER * (1 << 19) + ANCHOR_ROW + local - ANCHOR_START
                    || !anchor_wires.insert(local)
                {
                    return Err(format!("C387 Carry anchor ROW source or duplicate wire{local}"));
                }
            }
        }
        if point_wires.len() != POINT_READS
            || anchor_wires.len() != ANCHOR_COUNT
            || !(point_start + 1..point_start + 1 + POINT_READS)
                .all(|wire| point_wires.contains(&wire))
            || !(ANCHOR_START..ANCHOR_START + ANCHOR_COUNT)
                .all(|wire| anchor_wires.contains(&wire))
        {
            return Err("C387 Carry exact active Point/anchor ROW census".into());
        }

        let child = self.input.header(OWNER + 1)?;
        let previous = self.input.header(OWNER)?;
        let fields = crate::serializer::Fields::from_header(&child)?;
        let point_witness = crate::point_membership::witness(fields.pk, fields.w)?;
        if point_witness.len() != crate::point_membership::POINT_WIDTH {
            return Err("C387 Carry canonical Point witness width".into());
        }
        for header in [&previous, &child] {
            if header.encode().map_err(|error| format!("C387 Carry header encode: {error:?}"))?
                != self.input.raw(header.height as usize)?
            {
                return Err("C387 Carry canonical header bytes".into());
            }
        }

        // This replays the same no-adapter/no-Cap/no-Map HEADER -> Tree ->
        // CarryZero DAA writer path used by produce_with_carry_zero_daa_source_lease.
        // The census catches same-zero cross-author claims that OwnedRows::claim
        // would otherwise accept, and full packed equality binds the replay to
        // the actual row supplied to the ROW read join.
        let mut rows = OwnedRows::new(OwnerSelection::Single { owner: OWNER, class: OwnerClass::Carry });
        rows.begin_author_census()?;
        rows.set_author(NativePhysicalAuthor::Header)?;
        seed_header_from_template(
            &self.header_template, self.plan, None,
            #[cfg(test)] None,
            self.input, OWNER, &mut rows,
            #[cfg(test)] None,
            None, None, false, None, None, None,
        )?;
        rows.set_author(NativePhysicalAuthor::Tree)?;
        seed_tree(self.plan, self.input, OWNER, &mut rows, AssemblyFault::None)?;
        rows.set_author(NativePhysicalAuthor::Daa)?;
        self.claim_carry_zero_banks(OWNER, OwnerClass::Carry, &mut rows)?;
        if rows.bytes(0)? != row.bytes {
            return Err("C387 Carry physical-author replay/packed ROW mismatch".into());
        }

        // These images are minted from the canonical prefix and plan, rather
        // than supplied by the caller's packed row. NativePrefix::from_raw_iter
        // has already decoded and re-encoded every RAW, including the Tree
        // leaf at OWNER+2, and checked height and parent continuity.
        let mut canonical_header = self.header_template.assign(&fields)?;
        self.header_template.assign_order(
            &mut canonical_header, &fields, previous.height, previous.timestamp, false,
        )?;
        let tree_source = NativeTreeSourceLease::from_prefix(self.plan, self.input, OWNER)?;
        tree_source.check_binding(&binding)?;
        tree_source.check_author()?;
        let full_counts = rows.require_carry_full_source_values(
            OWNER, &tree_mask, &canonical_header, &tree_source.owned,
            &tree_source.values, &point_witness, &row.bytes,
        )?;

        let mut lease = self.header_source_lease(OWNER)?;
        for local in point_wires.into_iter().chain(anchor_wires) {
            if rows.author_census.as_ref().and_then(|authors| authors[local])
                != Some(NativePhysicalAuthor::Header)
                || NativeHeaderSourceLease::bit(&lease.owned, local)
            {
                return Err(format!("C387 Carry physical HEADER exclusivity wire{local}"));
            }
            let actual = rows.values[0][local];
            let expected = if (point_start..point_end).contains(&local) {
                point_witness[local - point_start]
            } else { false };
            if actual != Fr::from(expected as u64)
                || ((row.bytes[local / 8] >> (local % 8)) & 1 != 0) != expected
            {
                return Err(format!("C387 Carry canonical Point/anchor value wire{local}"));
            }
            NativeHeaderSourceLease::set(&mut lease.owned, local);
            if expected { NativeHeaderSourceLease::set(&mut lease.values, local); }
        }
        Ok((lease, full_counts))
    }
    pub(crate) fn require_work_d_lease(&self,owner:usize,lease:&NativeWorkDLease)->Result<(),String> {
        let expected=self.native_work_d_lease(owner)?;
        lease.checked_cells(&expected.parent,owner)?;
        if *lease!=expected {return Err("native Work-D exact native source replay".into());}
        Ok(())
    }
    pub(crate) fn new(
        plan: &'a WorkTreeHistoryPlan,
        input: &'a NativePrefix,
    ) -> Result<Self, String> {
        if plan.headers() != PREFIX_HEADERS as u64 || plan.slot_log() != 12 || plan.slots() != 4096
        {
            return Err("native owner source requires N3073/S12".into());
        }
        if plan.descriptor().root != input.root || plan.work_profile().total_be28 != input.total {
            return Err("native owner source root/total mismatch".into());
        }
        Self::new_for_history(plan, input)
    }

    pub(crate) fn new_for_history(
        plan: &'a WorkTreeHistoryPlan,
        input: &'a NativePrefix,
    ) -> Result<Self, String> {
        validate_native_plan_input(plan, input)?;
        Ok(Self {
            plan,
            input,
            roster: DaaHistoryRoster::compile(plan)?,
            exports: crate::native_owner_exports::NativeExports::new_for_history(plan, input)?,
            header_template: crate::daa_history_layout::HeaderAssignmentTemplate::new()?,
            max_adapter: None,
            #[cfg(test)]
            legacy_adapter: None,
        })
    }
    pub(crate) fn new_for_max_history(
        plan: &'a WorkTreeHistoryPlan,
        input: &'a NativePrefix,
        adapter: &'a crate::max_header_adapter::MaxHeaderAdapter<'a>,
    ) -> Result<Self, String> {
        adapter.check_parent(plan)?;
        let mut result = Self::new_for_history(plan, input)?;
        result.max_adapter = Some(adapter);
        Ok(result)
    }
    #[cfg(test)]
    pub(crate) fn new_for_legacy_history(
        plan: &'a WorkTreeHistoryPlan, input: &'a NativePrefix,
        adapter: &'a crate::legacy_native_adapter::LegacyNativeAdapter<'a>,
    ) -> Result<Self, String> {
        adapter.check(plan, input)?;
        let mut result = Self::new_for_history(plan, input)?;
        result.legacy_adapter = Some(adapter);
        Ok(result)
    }
    #[cfg(test)]
    pub(crate) fn reject_legacy_for_test(&self) -> Result<(), String> {
        if self.legacy_adapter.is_some() {
            Err("legacy native producer has no old binding transport".into())
        } else { Ok(()) }
    }
    #[cfg(test)]
    pub(crate) fn require_unadapted_cache_for_test(&self) -> Result<(), String> {
        if self.legacy_adapter.is_some() || self.max_adapter.is_some() {
            Err("native row cache has no adapter binding transport".into())
        } else { Ok(()) }
    }
    pub(crate) fn produce(&self, owner: usize) -> Result<NativePackedRow, String> {
        self.produce_inner(
            owner,
            AssemblyFault::None,
            None,
            #[cfg(test)]
            None,
            #[cfg(test)]
            false,
            #[cfg(test)]
            None,
            None,
        )
    }

    /// Produce the one padded owner with custody captured from its actual
    /// native HEADER seed and retained beside that exact packed row.
    pub(crate) fn produce_padding_header_zero_row(
        &self,
    ) -> Result<NativePaddingHeaderZeroRow, String> {
        self.produce_padding_header_zero_row_at(C449_PADDING_OWNER)
    }

    /// Produce one requested padding owner with custody captured from its
    /// actual native HEADER seed and retained beside that exact packed row.
    pub(crate) fn produce_padding_header_zero_row_at(
        &self, owner: usize,
    ) -> Result<NativePaddingHeaderZeroRow, String> {
        use crate::daa_history_roster::OwnerClass;
        let class=self.roster.owner_class(owner as u64)?;
        require_padding_header_zero_route(&PaddingHeaderZeroRoute {
            capture_requested:true,
            owner,
            class,
            plan_headers:self.plan.headers(),
            plan_slot_log:self.plan.slot_log(),
            plan_slots:self.plan.slots(),
            input_header_count:self.input.header_count(),
            has_max_adapter:self.max_adapter.is_some(),
            test_header_route:false,
            has_bank53_map:false,
            has_cap0:false,
            has_cap1:false,
            has_overlay:false,
            has_census:false,
            has_scored_source:false,
            has_map_source:false,
            has_daa_source_out:false,
        })?;
        if self.input.header_count()!=C449_PADDING_OWNER {
            return Err("C449 padding HEADER-zero requires full N-header input".into());
        }
        validate_native_plan_input(self.plan,self.input)?;
        let mut capture_out=None;
        let row=self.produce_inner_with_cap0(
            owner,AssemblyFault::None,None,
            #[cfg(test)] None,
            #[cfg(test)] false,
            #[cfg(test)] None,
            None,None,None,None,None,None,None,
            Some(&mut capture_out),
            None,
            None,
        )?;
        let capture=capture_out.ok_or("C449 padding HEADER-zero capture not returned")?;
        NativePaddingHeaderZeroRow::from_producer(row,capture)
    }

    /// Produce one owner with an exact, parent-bound Map0/Map1 live source.
    /// This does not admit its ROW relation or a complete history proof.
    pub(crate) fn produce_with_map_pair_lease(
        &self, owner: usize, lease: &Eligible08MapPairLease,
    ) -> Result<NativePackedRow, String> {
        self.produce_inner_with_cap0(
            owner, AssemblyFault::None, None,
            #[cfg(test)] None,
            #[cfg(test)] false,
            #[cfg(test)] None,
            None, None, None, None, None, None, Some(MapPhysicalSource::Pair(lease)),
            None,
            None,
            None,
        )
    }

    /// Retain the clipped owner's exclusive HEADER-zero subset from one real
    /// ordinary Map-only production. Clipped Score and full-row closure remain open.
    pub(crate) fn produce_clipped_header_zero_with_map_pair<'m>(&self, owner: usize,
        lease: &'m Eligible08MapPairLease) -> Result<NativeClippedHeaderZeroRow<'m>, String> {
        let mut capture_out = None;
        let row = self.produce_inner_with_cap0_and_c496(
            owner, AssemblyFault::None, None,
            #[cfg(test)] None,
            #[cfg(test)] false,
            #[cfg(test)] None,
            None, None, None, None, None, None, Some(MapPhysicalSource::Pair(lease)),
            None, None, None, Some(&mut capture_out),
            None, None, None, None, None, None, None,
        )?;
        let capture = capture_out.ok_or("C496 HeaderZero capture not returned")?;
        let result = NativeClippedHeaderZeroRow { row, capture };
        result.validate_for(lease.binding(), lease)?;
        Ok(result)
    }

    pub(crate) fn produce_clipped_score_with_map_pair<'r, 'src, 'm>(&self,
        relation: &'r h21_eligible_context::H21ClosedScoreOwnerRelation<'src>,
        lease: &'m Eligible08MapPairLease, context: usize,
    ) -> Result<C498ClippedScoreRow<'r, 'src, 'm>, String> {
        let binding = HeaderSourceBinding::for_plan(self.plan, relation.owner())?;
        let source = C498ClippedScoreSource::new(relation, &binding, lease, context)?;
        let mut header_out = None;
        let mut score_out = None;
        let row = self.produce_inner_with_cap0_and_c496(
            relation.owner(), AssemblyFault::None, None,
            #[cfg(test)] None,
            #[cfg(test)] false,
            #[cfg(test)] None,
            None, None, None, None, None, None, Some(MapPhysicalSource::Pair(lease)),
            None, None, None, Some(&mut header_out), Some(&source), Some(&mut score_out),
            None, None, None, None, None,
        )?;
        let result = C498ClippedScoreRow {
            header_zero: NativeClippedHeaderZeroRow { row,
                capture: header_out.ok_or("C498 C496 capture missing")? },
            source, cells: score_out.ok_or("C498 Score capture missing")?,
        };
        result.validate_for(&binding, lease)?;
        Ok(result)
    }

    /// Produce one eligible mixed Map/HEADER-zero owner from one generated
    /// Map lease. This does not admit ROW or a complete history proof.
    pub(crate) fn produce_mixed_map_header_row<'m>(
        &self, owner:usize, lease:&'m Eligible08MapPairLease,
    )->Result<NativeMixedMapHeaderRow<'m>,String> {
        let class=self.roster.owner_class(owner as u64)?;
        if self.input.header_count()!=C449_PADDING_OWNER
            || self.plan.headers()!=crate::bank53_map::BANK53_N
            || self.plan.slot_log()!=21 || self.plan.slots()!=1<<21
            || !mixed_map_header_class_allowed(owner,class) {
            return Err("C450 mixed producer requires owner845760 H21 Carry parent".into());
        }
        validate_native_plan_input(self.plan,self.input)?;
        require_mixed_map_header_no_scheduled(owner,class)?;
        let binding=HeaderSourceBinding::for_plan(self.plan,owner)?;
        if binding.profile()!=self.input.profile() || lease.binding()!=&binding {
            return Err("C450 mixed producer Map lease parent binding".into());
        }
        let mut capture_out=None;
        let row=self.produce_inner_with_cap0(
            owner,AssemblyFault::None,None,
            #[cfg(test)] None,
            #[cfg(test)] false,
            #[cfg(test)] None,
            None,None,None,None,None,None,Some(MapPhysicalSource::Pair(lease)),
            None,Some(&mut capture_out),
            None,
        )?;
        let capture=capture_out.ok_or("C450 mixed capture not returned")?;
        NativeMixedMapHeaderRow::from_producer(row,capture,binding,lease)
    }

    /// Produce one ordinary owner from a single generated Map+Slack source.
    /// This does not admit ROW globally or establish a complete history proof.
    pub(crate) fn produce_with_map_slack_bundle(
        &self, owner: usize, bundle: &Eligible08MapSlackBundle,
    ) -> Result<NativePackedRow, String> {
        self.produce_inner_with_cap0(
            owner, AssemblyFault::None, None,
            #[cfg(test)] None,
            #[cfg(test)] false,
            #[cfg(test)] None,
            None, None, None, None, None, None,
            Some(MapPhysicalSource::PairSlack(bundle)),
            None,
            None,
            None,
        )
    }

    /// Produce owner0 Genesis with source-owned HeaderZero custody. The
    /// returned capture borrows the exact Map+Slack bundle used by this row.
    pub(crate) fn produce_genesis_header_zero_with_map_slack_bundle<'b>(
        &self,
        owner: usize,
        bundle: &'b Eligible08MapSlackBundle,
    ) -> Result<NativeGenesisHeaderZeroRow<'b>, String> {
        use crate::daa_history_roster::OwnerClass;
        if owner != 0 || self.roster.owner_class(owner as u64)? != OwnerClass::Genesis {
            return Err("C491 HeaderZero producer requires Genesis owner0".into());
        }
        let binding = HeaderSourceBinding::for_plan(self.plan, owner)?;
        if binding.profile() != self.input.profile()
            || bundle.map_lease().binding() != &binding
        {
            return Err("C491 HeaderZero producer Map+Slack binding mismatch".into());
        }
        let mut capture_out = None;
        let row = self.produce_inner_with_cap0(
            owner, AssemblyFault::None, None,
            #[cfg(test)] None,
            #[cfg(test)] false,
            #[cfg(test)] None,
            None, None, None, None, None, None,
            Some(MapPhysicalSource::PairSlack(bundle)),
            None,
            None,
            Some(&mut capture_out),
        )?;
        let capture = capture_out.ok_or("C491 HeaderZero capture not returned")?;
        let result = NativeGenesisHeaderZeroRow { row, capture };
        result.validate_for(&binding, bundle)?;
        Ok(result)
    }

    /// Produce the first premodern ScoreAnchor owner from one checked
    /// Map+Score0/Score1+Slack source package. Global ROW remains separate.
    pub(crate) fn produce_with_map_slack_anchor_bundle(
        &self, owner: usize, bundle: &Eligible08MapSlackAnchorBundle,
    ) -> Result<NativePackedRow, String> {
        self.produce_inner_with_cap0(
            owner, AssemblyFault::None, None,
            #[cfg(test)] None,
            #[cfg(test)] false,
            #[cfg(test)] None,
            None, None, None, None, None, None,
            Some(MapPhysicalSource::PairSlackAnchor(bundle)),
            None,
            None,
            None,
        )
    }

    /// Mint first-anchor custody only after the specialized physical writer and
    /// final source/packed comparison succeed for the exact borrowed bundle.
    pub(crate) fn produce_first_anchor_packed_receipt<'b>(
        &self, owner: usize, bundle: &'b Eligible08MapSlackAnchorBundle,
    ) -> Result<NativeFirstAnchorPacked<'b>, String> {
        use crate::daa_history_roster::OwnerClass;
        if owner != 417_790 || self.roster.owner_class(owner as u64)? != OwnerClass::Carry {
            return Err("C448b first-anchor receipt requires Carry owner417790".into());
        }
        let binding = HeaderSourceBinding::for_plan(self.plan, owner)?;
        if bundle.map_slack().map_lease().binding() != &binding {
            return Err("C448b first-anchor receipt source binding mismatch".into());
        }
        let row = self.produce_with_map_slack_anchor_bundle(owner, bundle)?;
        row.require_header_source_binding(&binding, owner, OwnerClass::Carry)?;
        require_map_slack_anchor_packed(
            row.packed_bytes(), bundle, &binding, owner, OwnerClass::Carry,
        )?;
        Ok(NativeFirstAnchorPacked { row, bundle, binding })
    }

    /// Produce the second premodern ScoreAnchor only with the retained first
    /// packed row and the checked two-anchor source. Global ROW is separate.
    pub(crate) fn produce_with_map_slack_second_anchor_bundle(
        &self, owner: usize, bundle: &Eligible08MapSlackSecondAnchorBundle,
        first: &NativePackedRow,
    ) -> Result<NativePackedRow, String> {
        self.produce_inner_with_cap0(
            owner, AssemblyFault::None, None,
            #[cfg(test)] None,
            #[cfg(test)] false,
            #[cfg(test)] None,
            None, None, None, None, None, None,
            Some(MapPhysicalSource::PairSlackSecondAnchor(bundle, first)),
            None,
            None,
            None,
        )
    }

    pub(crate) fn produce_with_daa_source_lease(
        &self,
        owner: usize,
    ) -> Result<(NativePackedRow, NativeDaaSourceLease<'_, 'a>), String> {
        use crate::daa_history_roster::OwnerClass;
        let class = self.roster.owner_class(owner as u64)?;
        if !matches!(class, OwnerClass::M1 | OwnerClass::Short(_) | OwnerClass::Mature(_)) {
            return Err("native DAA lease requires a retarget owner".into());
        }
        let mut source = None;
        let row = self.produce_inner(
            owner, AssemblyFault::None, None,
            #[cfg(test)]
            None,
            #[cfg(test)]
            false,
            #[cfg(test)]
            None,
            Some(&mut source),
        )?;
        let source = source.ok_or("native DAA lease missing native retarget author")?;
        let DaaSourcePayload::NativeRetarget(patch) = source else {
            return Err("native DAA lease source variant is not retarget".into());
        };
        if self.max_adapter.is_some() {
            return Err("DAA source lease rejects MAX adapter".into());
        }
        #[cfg(test)]
        if self.legacy_adapter.is_some() {
            return Err("DAA source lease rejects legacy adapter".into());
        }
        validate_native_plan_input(self.plan, self.input)?;
        let binding = HeaderSourceBinding::for_plan(self.plan, owner)?;
        let class = self.roster.owner_class(owner as u64)?;
        if !matches!(class, crate::daa_history_roster::OwnerClass::M1
            | crate::daa_history_roster::OwnerClass::Short(_)
            | crate::daa_history_roster::OwnerClass::Mature(_))
            || patch.identity() != (owner as u64, class) {
            return Err("DAA source lease owner/class/retarget mismatch".into());
        }
        let lease = NativeDaaSourceLease {
            _source: self,
            binding,
            author: DaaSourceAuthor::NativeRetarget,
            source: DaaSourcePayload::NativeRetarget(patch),
            #[cfg(test)] read_count: std::cell::Cell::new(0),
            #[cfg(test)] synthetic_class: None,
        };
        Ok((row, lease))
    }

    /// Retain the producer's exclusive full-template DAA zero writes for the
    /// five owner classes whose lane3 template is exactly zero.
    pub(crate) fn produce_with_full_zero_daa_source_lease(
        &self,
        owner: usize,
    ) -> Result<(NativePackedRow, NativeDaaSourceLease<'_, 'a>), String> {
        let class = self.roster.owner_class(owner as u64)?;
        if !is_full_zero_daa_class(class) {
            return Err("FullZero DAA lease requires a full-template owner".into());
        }
        if self.max_adapter.is_some() {
            return Err("FullZero DAA lease rejects MAX adapter".into());
        }
        #[cfg(test)]
        if self.legacy_adapter.is_some() {
            return Err("FullZero DAA lease rejects legacy adapter".into());
        }

        let binding = HeaderSourceBinding::for_plan(self.plan, owner)?;
        validate_native_plan_input(self.plan, self.input)?;
        if binding.profile != self.input.profile() {
            return Err("FullZero DAA source native profile drift".into());
        }
        let mut source = None;
        let row = self.produce_inner(
            owner, AssemblyFault::None, None,
            #[cfg(test)] None,
            #[cfg(test)] false,
            #[cfg(test)] None,
            Some(&mut source),
        )?;
        let source = source.ok_or("FullZero DAA lease missing exclusive bank author")?;
        let DaaSourcePayload::FullZero(claims) = source else {
            return Err("FullZero DAA source variant mismatch".into());
        };
        claims.check_identity(owner as u64, class)?;
        let lease = NativeDaaSourceLease {
            _source: self,
            binding: binding.clone(),
            author: DaaSourceAuthor::FullZero,
            source: DaaSourcePayload::FullZero(claims),
            #[cfg(test)] read_count: std::cell::Cell::new(0),
            #[cfg(test)] synthetic_class: None,
        };
        lease.check_full_zero_source(&binding)?;
        row.require_header_source_binding(&binding, owner, class)?;
        Ok((row, lease))
    }

    /// Admit only a Carry owner and explicitly claim all four fixed DAA banks
    /// as zero before packing. This is a distinct author from retarget output.
    pub(crate) fn produce_with_carry_zero_daa_source_lease(
        &self,
        owner: usize,
    ) -> Result<(NativePackedRow, NativeDaaSourceLease<'_, 'a>), String> {
        self.produce_with_carry_zero_daa_source_lease_and_caps(owner, None, None, None, None, None, None)
    }

    /// Close one scheduled MAX source and record its 1,346 physical claims
    /// through the same owner-row writer. This does not publish global X/ROW.
    pub(crate) fn produce_scheduled_max_844798<'p, 'm>(
        &'p self,
        stream: &'p crate::h21_scheduled_max_cap::MaxStream<'m>,
    ) -> Result<NativeScheduledMaxRow<'p, 'a, 'm>, String> {
        self.produce_scheduled_max_owner(C512C_MAX_OWNER,stream)
    }

    /// Generic fixed-Eligible08 MAX physical author. No caller values/mask.
    pub(crate) fn produce_scheduled_max_owner<'p,'m>(&'p self,owner:usize,
        stream:&'p crate::h21_scheduled_max_cap::MaxStream<'m>) -> Result<NativeScheduledMaxRow<'p,'a,'m>,String> {
        use crate::daa_history_roster::OwnerClass;
        let class=c576_max_route(owner,self.roster.owner_class(owner as u64)?)?;
        let retained_bound=c576_max_retained_bound(owner)?;
        stream.closed_native_snapshot(self.plan, self.input)?;
        let cells = stream.closed_owner_cells(owner)?;
        let max = c512c_checked_max_cells(owner, &cells)?;
        let binding = HeaderSourceBinding::for_plan(self.plan, owner)?;
        if self.roster.owner_class(owner as u64)? != OwnerClass::Carry
            || binding.profile() != self.input.profile() || self.max_adapter.is_some() {
            return Err("C512c scheduled MAX requires exact unadapted Carry parent".into());
        }
        #[cfg(test)]
        if self.legacy_adapter.is_some() {
            return Err("C512c scheduled MAX rejects legacy producer".into());
        }
        let source = NativeScheduledMaxSource { stream, binding: binding.clone(), cells, max, class };
        let mut daa_out = None;
        let mut max_claims_out = None;
        let row = self.produce_inner_with_cap0_and_c496(
            owner, AssemblyFault::None, None,
            #[cfg(test)] None,
            #[cfg(test)] false,
            #[cfg(test)] None,
            Some(&mut daa_out),
            None, None, None, None, None, None,
            None, None, None, None, None, None,
            None, Some(&source), Some(&mut max_claims_out),
            None, None,
        )?;
        let payload = daa_out.ok_or("C512c prepack CarryZero DAA source missing")?;
        let DaaSourcePayload::CarryZero(claims) = payload else {
            return Err("C512c expected prepack CarryZero DAA source".into());
        };
        validate_native_plan_input(self.plan, self.input)?;
        claims.check_identity(owner as u64, OwnerClass::Carry)?;
        let daa = NativeDaaSourceLease {
            _source: self,
            binding: binding.clone(),
            author: DaaSourceAuthor::CarryZero,
            source: DaaSourcePayload::CarryZero(claims),
            #[cfg(test)] read_count: std::cell::Cell::new(0),
            #[cfg(test)] synthetic_class: None,
        };
        daa.check_carry_zero_source(&binding)?;
        row.require_header_source_binding(&binding, owner, OwnerClass::Carry)?;
        let out = NativeScheduledMaxRow {
            row, daa, source,
            claims: max_claims_out.ok_or("C512c physical MAX claim capture missing")?,
            complete_checked: Cell::new(false),
        };
        out.check_complete()?;
        if out.retained_capacity_bytes()?>retained_bound {return Err("C576 retained MAX source exceeds preflight bound".into());}
        Ok(out)
    }

    /// Emit one regular Eligible08 Score owner's source cells into its
    /// HEADER-reserved physical ROW positions. The returned wrapper retains foreign reads and
    /// CarryZero DAA authority; it is not a complete checked owner slice.
    pub(crate) fn produce_scored_owner_packed_source_lease(
        &self,
        source: ScoredOwnerPackingView,
    ) -> Result<NativePartialScoredOwnerPackedCandidate<'_, 'a>, String> {
        let owner = source.owner();
        let binding = HeaderSourceBinding::for_plan(self.plan, owner)?;
        if self.roster.owner_class(owner as u64)? != crate::daa_history_roster::OwnerClass::Carry {
            return Err("C396 packed source requires ordinary Carry owner".into());
        }
        scored_owner_source_local(&source, owner, &binding)?;
        let (row, daa) = self.produce_with_carry_zero_daa_source_lease_and_caps(
            owner, None, None, None, None, Some(&source), None,
        )?;
        row.require_header_source_binding(&binding, owner,
            crate::daa_history_roster::OwnerClass::Carry)?;
        daa.check_carry_zero_source(&binding)?;
        require_scored_owner_source_packed(row.packed_bytes(), &source, &binding)?;
        Ok(NativePartialScoredOwnerPackedCandidate { row, daa, source })
    }

    /// Capture the complete regular-owner physical writer in the same packed
    /// production pass. This does not consume or replace C374 owner845759.
    pub(crate) fn produce_regular_owner845887_author_census(
        &self, source: ScoredOwnerPackingView,
    ) -> Result<NativeRegularOwnerAuthorCensus<'_, 'a>, String> {
        self.c574_produce_regular_author_census(845_887, source)
    }

    pub(crate) fn produce_regular_owner846015_author_census(
        &self, source: ScoredOwnerPackingView,
    ) -> Result<NativeRegularOwnerAuthorCensus<'_, 'a>, String> {
        self.c574_produce_regular_author_census(846_015, source)
    }

    fn c574_produce_regular_author_census(
        &self, owner: usize, source: ScoredOwnerPackingView,
    ) -> Result<NativeRegularOwnerAuthorCensus<'_, 'a>, String> {
        use crate::daa_history_roster::OwnerClass;
        c574_regular_owner(owner)?;
        if source.owner() != owner || self.roster.owner_class(owner as u64)? != OwnerClass::Carry {
            return Err("C512e exact regular Score owner/class".into());
        }
        let binding = HeaderSourceBinding::for_plan(self.plan, owner)?;
        scored_owner_source_local(&source, owner, &binding)?;
        let mut authors = None;
        let (row, daa) = self.produce_with_carry_zero_daa_source_lease_and_caps(
            owner, None, None, None, None, Some(&source), Some(&mut authors),
        )?;
        row.require_header_source_binding(&binding, owner, OwnerClass::Carry)?;
        daa.check_carry_zero_source(&binding)?;
        require_scored_owner_source_packed(row.packed_bytes(), &source, &binding)?;
        let sealed_bits = row.bytes.clone();
        let census = NativeRegularOwnerAuthorCensus {
            candidate: NativePartialScoredOwnerPackedCandidate { row, daa, source },
            authors: authors.ok_or("C512e source-bound regular physical claims absent")?,
            sealed_bits,
            complete_checked: Cell::new(false),
        };
        census.check_complete()?;
        Ok(census)
    }

    /// Mint foreign numeric DAA Work-D reads from a native source owner's
    /// exact 224-endpoint lease, bound to the same-parent destination owner.
    pub(crate) fn foreign_daa_work_read_lease(
        &self, source_owner: usize, destination_owner: usize,
    ) -> Result<ForeignDaaWorkReadLease, String> {
        if destination_owner != FOREIGN_DAA_WORK_DESTINATION_OWNER
            || !FOREIGN_DAA_WORK_SOURCE_OWNERS.contains(&source_owner) {
            return Err("foreign DAA Work-D source/destination owner".into());
        }
        let destination=HeaderSourceBinding::for_plan(self.plan,destination_owner)?;
        let source_binding=HeaderSourceBinding::for_plan(self.plan,source_owner)?;
        let work = self.native_work_d_lease(source_owner)?;
        self.require_work_d_lease(source_owner, &work)?;
        let cells = work.checked_cells(&work.parent, source_owner)?.to_vec();
        let lease = ForeignDaaWorkReadLease {
            parent: ForeignDaaWorkParent::from_binding(&source_binding),
            destination, source: source_binding, source_owner,
            author: ForeignDaaWorkAuthor::NativeWorkD, cells,
        };
        lease.require_destination(&lease.destination, destination_owner)?;
        Ok(lease)
    }

    /// Mint the two adjacent Carry EqualParent Work reads from their actual
    /// source-owner Tree rows and checked native scalar exports. The DAA
    /// relation at the destination does not make these DAA-authored cells.
    pub(crate) fn carry_foreign_tree_work_author_lease(
        &self,source_owner:usize,destination_owner:usize,
    )->Result<NativeTypedAuthorLease<'static>,String> {
        if destination_owner!=MATURE_EIP_SOURCE_OWNER+1
            || ![MATURE_EIP_SOURCE_OWNER-1,MATURE_EIP_SOURCE_OWNER]
                .contains(&source_owner)
            || self.roster.owner_class(destination_owner as u64)?
                !=crate::daa_history_roster::OwnerClass::Carry
            || self.max_adapter.is_some() {
            return Err("typed Carry Work exact destination/source owner/class".into());
        }
        #[cfg(test)]
        if self.legacy_adapter.is_some() {
            return Err("typed Carry Work rejects legacy adapter".into());
        }
        require_no_scheduled_max_cap(destination_owner)?;
        validate_native_plan_input(self.plan,self.input)?;
        let destination=HeaderSourceBinding::for_plan(self.plan,destination_owner)?;
        let source=HeaderSourceBinding::for_plan(self.plan,source_owner)?;
        let work=self.native_work_d_lease(source_owner)?;
        self.require_work_d_lease(source_owner,&work)?;
        let row=self.produce(source_owner)?;
        row.require_header_source_binding(&source,source_owner,
            self.roster.owner_class(source_owner as u64)?)?;
        let tree_mask=self.plan.physical_assignment_replacement_mask(source_owner as u64)?;
        if tree_mask.len()!=WIDTH {return Err("typed Carry source Tree mask width".into());}
        let mut cells=Vec::with_capacity(224);
        for &(wire,scalar) in work.checked_cells(&work.parent,source_owner)? {
            let local=wire.checked_sub(source_owner*WIDTH)
                .filter(|local|(987_674..987_898).contains(local))
                .ok_or("typed Carry Work endpoint outside source owner")?;
            if !tree_mask[local] {return Err("typed Carry Work source is not Tree-owned".into());}
            let bit=if scalar==Fr::one(){true}else if scalar==Fr::zero(){false}
                else{return Err("typed Carry Work non-Boolean scalar".into())};
            if bit!=((row.packed_bytes()[local/8]>>(local%8))&1!=0) {
                return Err("typed Carry Work scalar/actual Tree ROW mismatch".into());
            }
            cells.push((wire,bit));
        }
        let lease=NativeTypedAuthorLease{destination,source,
            kind:NativeTypedSource::CarryForeignTreeWork{
                cells,author:NativeTypedAuthor::Tree}};
        lease.check_binding(self.plan,&lease.destination)?;
        Ok(lease)
    }

    /// Mint one of the nine Mature(Eip) foreign serializer source owners.
    /// Every admitted cell is a HEADER-authored bit in that owner's actual
    /// packed row and the scalar imported by the DAA producer.
    pub(crate) fn mature_foreign_serializer_author_lease(
        &self,source_owner:usize,
    )->Result<NativeTypedAuthorLease<'static>,String> {
        if self.max_adapter.is_some() {
            return Err("typed Mature serializer rejects MAX adapter".into());
        }
        #[cfg(test)]
        if self.legacy_adapter.is_some() {
            return Err("typed Mature serializer rejects legacy adapter".into());
        }
        validate_native_plan_input(self.plan,self.input)?;
        let class=self.roster.owner_class(source_owner as u64)?;
        if class!=crate::daa_history_roster::OwnerClass::Carry {
            return Err("typed Mature serializer exact Carry source class".into());
        }
        require_no_scheduled_max_cap(source_owner)?;
        let destination=HeaderSourceBinding::for_plan(self.plan,MATURE_EIP_SOURCE_OWNER)?;
        let source=HeaderSourceBinding::for_plan(self.plan,source_owner)?;
        let wires=mature_foreign_serializer_wires(self.plan,source_owner)?;
        let tree_mask=self.plan.physical_assignment_replacement_mask(source_owner as u64)?;
        if tree_mask.len()!=WIDTH {
            return Err("typed Mature serializer Tree mask width".into());
        }
        let tree=NativeTreeSourceLease::from_prefix(self.plan,self.input,source_owner)?;
        tree.check_binding(&source)?;
        tree.check_author()?;
        if tree.owned.len()!=OWNER_BYTES {
            return Err("typed Mature serializer Tree source width".into());
        }
        let header=self.header_source_lease(source_owner)?;
        header.check_binding(&source)?;
        header.check_author()?;
        let (row,daa)=self.produce_with_carry_zero_daa_source_lease(source_owner)?;
        row.require_header_source_binding(&source,source_owner,class)?;
        daa.check_binding(&source)?;
        daa.check_author()?;
        let mut cells=Vec::with_capacity(wires.len());
        for wire in wires {
            let local=wire-source_owner*WIDTH;
            let serializer=crate::header_hash::SERIALIZER_OFFSET
                ..crate::header_hash::SERIALIZER_OFFSET+crate::header_hash::SERIALIZER_WIDTH;
            if !serializer.contains(&local) || tree_mask[local]
                || NativeHeaderSourceLease::bit(&tree.owned,local)
                || BANKS.iter().any(|&(lo,hi)|(lo..hi).contains(&local))
                || (crate::segment_points::POINT_OFFSET
                    ..crate::segment_points::POINT_OFFSET+crate::point_membership::POINT_WIDTH)
                    .contains(&local)
                || (BANK53_BASE..BANK53_BASE+BANK53_CONTEXTS*BANK53_CONTEXT_BITS)
                    .contains(&local)
                || MATURE_EIP_MAX_CAP.contains(&local)
                || daa.read_daa_bit(&source,wire)?.is_some() {
                return Err("typed Mature serializer later writer domain overlaps HEADER".into());
            }
            let value=header.read_header_bit(&source,wire)?
                .ok_or("typed Mature serializer source not HEADER-owned")?;
            check_mature_serializer_three_way(value,self.exports.bit(wire)?,
                (row.packed_bytes()[local/8]>>(local%8))&1!=0)?;
            cells.push((wire,value));
        }
        let lease=NativeTypedAuthorLease{destination,source,
            kind:NativeTypedSource::MatureForeignSerializer{
                cells,author:NativeTypedAuthor::Header}};
        lease.check_binding(self.plan,&lease.destination)?;
        Ok(lease)
    }

    /// Materialize the checked first-modern Cap0 lease into the exact reserved
    /// HEADER-owned Cap0 domain before packing. This remains a partial X/ROW
    /// input; Header Cap anchor ROW obligations are retired separately.
    pub(crate) fn produce_with_carry_zero_daa_cap0_source_lease(
        &self,
        owner: usize,
        snapshot: &crate::h21_scheduled_max_cap::Eligible08NativeSnapshot,
        cap: &crate::h21_scheduled_max_cap::FirstModernCapLease,
    ) -> Result<(NativePackedRow, NativeDaaSourceLease<'_, 'a>), String> {
        let cap0 = NativeCap0Source::from_first_modern_lease(
            self.plan, self.input, owner, snapshot, cap,
        )?;
        self.produce_with_carry_zero_daa_source_lease_and_caps(owner, Some(cap0), None, None, None, None, None)
    }

    /// Materialize both checked first-modern Cap contexts from one exact
    /// lease/snapshot into their disjoint HEADER-owned domains before packing.
    pub(crate) fn produce_with_carry_zero_daa_cap01_source_lease(
        &self,
        owner: usize,
        snapshot: &crate::h21_scheduled_max_cap::Eligible08NativeSnapshot,
        cap: &crate::h21_scheduled_max_cap::FirstModernCapLease,
    ) -> Result<(NativePackedRow, NativeDaaSourceLease<'_, 'a>), String> {
        self.produce_with_carry_zero_daa_cap01_overlay_impl(owner, snapshot, cap, None, None)
    }

    /// Install both exact Eligible08 Map/Score/Slack contexts before packing,
    /// retaining the native Cap01 and CarryZero DAA authors. The overlay is
    /// minted only from the completed same-parent owner sink.
    pub(crate) fn produce_with_carry_zero_daa_cap01_overlay_source_lease(
        &self,
        owner: usize,
        snapshot: &crate::h21_scheduled_max_cap::Eligible08NativeSnapshot,
        cap: &crate::h21_scheduled_max_cap::FirstModernCapLease,
        overlay: &Eligible08PackedOverlay<'_>,
    ) -> Result<(NativePackedRow, NativeDaaSourceLease<'_, 'a>), String> {
        self.produce_with_carry_zero_daa_cap01_overlay_impl(owner, snapshot, cap, Some(overlay), None)
    }

    /// C374 sibling: retain the six-author census from the same actual write
    /// path. No caller can supply an author bitmap or packed witness.
    pub(crate) fn produce_with_carry_zero_daa_cap01_overlay_census_source_lease(
        &self,
        owner: usize,
        snapshot: &crate::h21_scheduled_max_cap::Eligible08NativeSnapshot,
        cap: &crate::h21_scheduled_max_cap::FirstModernCapLease,
        overlay: &Eligible08PackedOverlay<'_>,
    ) -> Result<(NativePackedRow, NativeDaaSourceLease<'_, 'a>, NativeOwnerAuthorCensus), String> {
        let mut census = None;
        let (row, daa) = self.produce_with_carry_zero_daa_cap01_overlay_impl(
            owner, snapshot, cap, Some(overlay), Some(&mut census),
        )?;
        Ok((row, daa, census.ok_or("C374 producer did not seal author census")?))
    }

    fn produce_with_carry_zero_daa_cap01_overlay_impl(
        &self,
        owner: usize,
        snapshot: &crate::h21_scheduled_max_cap::Eligible08NativeSnapshot,
        cap: &crate::h21_scheduled_max_cap::FirstModernCapLease,
        overlay: Option<&Eligible08PackedOverlay<'_>>,
        census_out: Option<&mut Option<NativeOwnerAuthorCensus>>,
    ) -> Result<(NativePackedRow, NativeDaaSourceLease<'_, 'a>), String> {
        let cap0 = NativeCap0Source::from_first_modern_lease(
            self.plan, self.input, owner, snapshot, cap,
        )?;
        let cap1 = NativeCap1Source::from_first_modern_lease(
            self.plan, self.input, owner, snapshot, cap,
        )?;
        let cap0_end = FIRST_MODERN_CAP0_BASE.checked_add(FIRST_MODERN_CAP0_CELLS)
            .ok_or("Cap0 domain extent overflow")?;
        let cap1_end = FIRST_MODERN_CAP1_BASE.checked_add(FIRST_MODERN_CAP1_CELLS)
            .ok_or("Cap1 domain extent overflow")?;
        if cap0.binding() != cap1.binding()
            || (FIRST_MODERN_CAP0_BASE < cap1_end && FIRST_MODERN_CAP1_BASE < cap0_end)
        {
            return Err("Cap0/Cap1 source bindings or HEADER domains overlap".into());
        }
        self.produce_with_carry_zero_daa_source_lease_and_caps(
            owner, Some(cap0), Some(cap1), overlay, census_out, None, None)
    }

    fn produce_with_carry_zero_daa_source_lease_and_caps(
        &self,
        owner: usize,
        cap0_source: Option<NativeCap0Source>,
        cap1_source: Option<NativeCap1Source>,
        overlay: Option<&Eligible08PackedOverlay<'_>>,
        census_out: Option<&mut Option<NativeOwnerAuthorCensus>>,
        scored_source: Option<&ScoredOwnerPackingView>,
        regular_authors_out: Option<&mut Option<Vec<Option<NativeRegularPhysicalAuthor>>>>,
    ) -> Result<(NativePackedRow, NativeDaaSourceLease<'_, 'a>), String> {
        use crate::daa_history_roster::OwnerClass;
        if self.roster.owner_class(owner as u64)? != OwnerClass::Carry {
            return Err("CarryZero DAA lease requires a Carry owner".into());
        }
        if self.max_adapter.is_some() {
            return Err("CarryZero DAA lease rejects MAX adapter".into());
        }
        #[cfg(test)]
        if self.legacy_adapter.is_some() {
            return Err("CarryZero DAA lease rejects legacy adapter".into());
        }
        let mut source = None;
        let row = self.produce_inner_with_cap0_and_c496(
            owner, AssemblyFault::None, None,
            #[cfg(test)]
            None,
            #[cfg(test)]
            false,
            #[cfg(test)]
            None,
            Some(&mut source),
            cap0_source,
            cap1_source,
            overlay,
            census_out,
            scored_source,
            None,
            None,
            None,
            None,
            None,
            None,
            None,
            regular_authors_out,
            None,
            None,
            None,
            None,
        )?;
        let source = source.ok_or("CarryZero DAA lease missing explicit bank author")?;
        let DaaSourcePayload::CarryZero(claims) = source else {
            return Err("CarryZero DAA source variant mismatch".into());
        };
        validate_native_plan_input(self.plan, self.input)?;
        let binding = HeaderSourceBinding::for_plan(self.plan, owner)?;
        if binding.profile != self.input.profile() {
            return Err("CarryZero DAA source native profile drift".into());
        }
        claims.check_identity(owner as u64, OwnerClass::Carry)?;
        let lease = NativeDaaSourceLease {
            _source: self,
            binding,
            author: DaaSourceAuthor::CarryZero,
            source: DaaSourcePayload::CarryZero(claims),
            #[cfg(test)] read_count: std::cell::Cell::new(0),
            #[cfg(test)] synthetic_class: None,
        };
        Ok((row, lease))
    }

    /// Build a Map row from immutable native exports and place it in one
    /// explicitly reserved 8,192-bit Bank53 context. The Map helpers and
    /// foreign imports are generated here; no caller-supplied bitmap enters
    /// the production path.
    pub(crate) fn produce_bank53_map(
        &self,
        owner: usize,
        map: &crate::legacy_envelope_map::Map,
        context: usize,
    ) -> Result<NativePackedRow, String> {
        self.require_unadapted_cache_for_map()?;
        let assignment = generate_bank53_map_assignment(
            self.plan,
            self.input,
            &self.exports,
            map,
            owner,
            context,
        )?;
        self.produce_inner(
            owner,
            AssemblyFault::None,
            Some(&assignment),
            #[cfg(test)]
            None,
            #[cfg(test)]
            false,
            #[cfg(test)]
            None,
            None,
        )
    }

    /// Test-only H21 Map producer. Production `produce_bank53_map` retains its
    /// explicit N3/N4/N1984 admission and is not routed through this seam.
    #[cfg(test)]
    pub(crate) fn produce_bank53_map_h21_for_test(
        &self,
        owner: usize,
        map: &crate::legacy_envelope_map::Map,
        context: usize,
    ) -> Result<NativePackedRow, String> {
        self.require_unadapted_cache_for_map()?;
        validate_h21_bank53_map_lane_for_test(self.plan, owner, context)?;
        let assignment = generate_h21_bank53_map_assignment_for_test(
            self.plan,
            self.input,
            &self.exports,
            map,
            owner,
            context,
        )?;
        self.produce_inner(
            owner,
            AssemblyFault::None,
            Some(&assignment),
            None,
            false,
            None,
            None,
        )
    }

    /// Test-only producer for the c146 rootless Map1 cut. Its imports remain
    /// owned by this producer's exact validated parent prefix and typed export.
    #[cfg(test)]
    pub(crate) fn produce_bank53_map1_cut_h21_for_test(
        &self,
        owner: usize,
        context: usize,
        map: &crate::legacy_envelope_map::Map,
        approved_binding: &crate::legacy_envelope_map::Binding,
    ) -> Result<NativePackedRow, String> {
        self.require_unadapted_cache_for_map()?;
        let assignment = generate_h21_map1_cut_assignment_for_test(
            self.plan,
            self.input,
            &self.exports,
            map,
            owner,
            context,
            approved_binding,
        )?;
        self.produce_inner(owner, AssemblyFault::None, Some(&assignment), None, false, None, None)
    }

    fn require_unadapted_cache_for_map(&self) -> Result<(), String> {
        if self.max_adapter.is_some() {
            return Err("bank53 Map writer rejects MAX mixing".into());
        }
        #[cfg(test)]
        if self.legacy_adapter.is_some() {
            return Err("bank53 Map writer rejects legacy mixing".into());
        }
        Ok(())
    }

    fn claim_carry_zero_banks(
        &self,
        owner: usize,
        class: crate::daa_history_roster::OwnerClass,
        rows: &mut OwnedRows,
    ) -> Result<CarryZeroBankClaims, String> {
        use crate::daa_history_roster::OwnerClass;
        if class != OwnerClass::Carry || self.roster.owner_class(owner as u64)? != OwnerClass::Carry {
            return Err("CarryZero explicit claims require a Carry owner".into());
        }
        let mut claims = Vec::with_capacity(BANKS.len());
        for &(start, end) in BANKS.iter() {
            if start >= end || end > WIDTH || start % 8 != 0 || end % 8 != 0 {
                return Err("CarryZero explicit bank geometry".into());
            }
            for wire in start..end {
                rows.claim_exclusive(owner, wire, Fr::zero())?;
            }
            claims.push(CarryZeroBankClaim {
                start,
                end,
                claimed_bits: end - start,
            });
        }
        let evidence = CarryZeroBankClaims { owner: owner as u64, class, banks: claims };
        evidence.check_identity(owner as u64, class)?;
        Ok(evidence)
    }

    fn claim_full_zero_banks(
        &self,
        owner: usize,
        class: crate::daa_history_roster::OwnerClass,
        rows: &mut OwnedRows,
    ) -> Result<FullZeroBankClaims, String> {
        if !is_full_zero_daa_class(class)
            || self.roster.owner_class(owner as u64)? != class {
            return Err("FullZero explicit claims require a full-template owner".into());
        }
        let mut claims = Vec::with_capacity(BANKS.len());
        for &(start, end) in BANKS.iter() {
            if start >= end || end > WIDTH || start % 8 != 0 || end % 8 != 0 {
                return Err("FullZero explicit bank geometry".into());
            }
            for wire in start..end {
                rows.claim_exclusive(owner, wire, Fr::zero())?;
            }
            claims.push(FullZeroBankClaim {
                start,
                end,
                claimed_bits: end - start,
            });
        }
        let evidence = FullZeroBankClaims { owner: owner as u64, class, banks: claims };
        evidence.check_identity(owner as u64, class)?;
        evidence.check_claimed_rows(rows, owner)?;
        Ok(evidence)
    }

    /// Runs the actual native assembly pipeline with one explicitly supplied
    /// test-only B context. The assignment vector is an ownership fixture and
    /// does not establish source provenance or satisfy the Map/Score relation.
    #[cfg(test)]
    pub(crate) fn produce_bank53_for_test(
        &self,
        owner: usize,
        witness: &Bank53TestWitness,
    ) -> Result<NativePackedRow, String> {
        self.require_unadapted_cache_for_test()?;
        if self.max_adapter.is_some() || self.legacy_adapter.is_some() {
            return Err("bank53 test writer rejects MAX/legacy mixing".into());
        }
        if witness.context >= BANK53_TEST_CONTEXTS {
            return Err("bank53 test context outside two-context lane".into());
        }
        self.produce_inner(owner, AssemblyFault::None, None, None, false, Some(witness), None)
    }

    #[cfg(test)]
    pub(crate) fn produce_bank53_fault_for_test(
        &self,
        owner: usize,
        witness: &Bank53TestWitness,
        fault: AssemblyFault,
    ) -> Result<NativePackedRow, String> {
        self.require_unadapted_cache_for_test()?;
        if self.max_adapter.is_some() || self.legacy_adapter.is_some() {
            return Err("bank53 test writer rejects MAX/legacy mixing".into());
        }
        if witness.context >= BANK53_TEST_CONTEXTS {
            return Err("bank53 test context outside two-context lane".into());
        }
        self.produce_inner(owner, fault, None, None, false, Some(witness), None)
    }

    #[cfg(test)]
    fn bank53_same_value_collision_for_test(
        &self,
        owner: usize,
        witness: &Bank53TestWitness,
        offset: usize,
    ) -> Result<(), String> {
        self.require_unadapted_cache_for_test()?;
        if self.max_adapter.is_some() || self.legacy_adapter.is_some() {
            return Err("bank53 test writer rejects MAX/legacy mixing".into());
        }
        if witness.context >= BANK53_TEST_CONTEXTS || offset >= BANK53_TEST_CONTEXT_BITS {
            return Err("bank53 test collision coordinate outside selected lane".into());
        }
        if witness.owner != owner {
            return Err("bank53 test witness owner mismatch".into());
        }
        if witness.values.len() != BANK53_TEST_CONTEXT_BITS {
            return Err("bank53 test witness length mismatch".into());
        }
        let class = self.roster.owner_class(owner as u64)?;
        let selection = OwnerSelection::Single { owner, class };
        let mut rows = OwnedRows::new(selection);
        seed_header_from_template_bank53_for_test(
            &self.header_template,
            self.plan,
            self.input,
            owner,
            witness.context,
            &mut rows,
        )?;
        let wire = BANK53_TEST_BASE + witness.context * BANK53_TEST_CONTEXT_BITS + offset;
        rows.claim(owner, wire, witness.values[offset])?;
        write_bank53_witness_for_test(&mut rows, owner, witness.context, witness)
    }

    #[cfg(test)]
    pub(crate) fn produce_profile_for_test(
        &self,
        owner: usize,
    ) -> Result<(NativePackedRow, NativePhaseTimings), String> {
        let mut timings = NativePhaseTimings::default();
        let started = std::time::Instant::now();
        let row = self.produce_inner(owner, AssemblyFault::None, None, Some(&mut timings), false, None, None)?;
        timings.total_ns = started.elapsed().as_nanos();
        Ok((row, timings))
    }
    #[cfg(test)]
    pub(crate) fn produce_fault_for_test(
        &self,
        owner: usize,
        fault: AssemblyFault,
    ) -> Result<NativePackedRow, String> {
        self.produce_inner(owner, fault, None, None, false, None, None)
    }
    #[cfg(test)]
    pub(crate) fn produce_legacy_header_for_test(&self, owner: usize) -> Result<NativePackedRow, String> {
        self.produce_inner(owner, AssemblyFault::None, None, None, true, None, None)
    }
    fn produce_inner(
        &self,
        owner: usize,
        fault: AssemblyFault,
        bank53_map: Option<&Bank53MapAssignment>,
        #[cfg(test)] mut timings: Option<&mut NativePhaseTimings>,
        #[cfg(test)] legacy_header: bool,
        #[cfg(test)] bank53_witness: Option<&Bank53TestWitness>,
        daa_source_out: Option<&mut Option<DaaSourcePayload>>,
    ) -> Result<NativePackedRow, String> {
        self.produce_inner_with_cap0(
            owner, fault, bank53_map,
            #[cfg(test)]
            timings,
            #[cfg(test)]
            legacy_header,
            #[cfg(test)]
            bank53_witness,
            daa_source_out,
            None,
            None,
            None,
            None,
            None,
            None,
            None,
            None,
            None,
        )
    }

    fn produce_inner_with_cap0<'b>(
        &self,
        owner: usize,
        fault: AssemblyFault,
        bank53_map: Option<&Bank53MapAssignment>,
        #[cfg(test)] timings: Option<&mut NativePhaseTimings>,
        #[cfg(test)] legacy_header: bool,
        #[cfg(test)] bank53_witness: Option<&Bank53TestWitness>,
        daa_source_out: Option<&mut Option<DaaSourcePayload>>,
        cap0_source: Option<NativeCap0Source>,
        cap1_source: Option<NativeCap1Source>,
        overlay: Option<&Eligible08PackedOverlay<'_>>,
        census_out: Option<&mut Option<NativeOwnerAuthorCensus>>,
        scored_source: Option<&ScoredOwnerPackingView>,
        map_source: Option<MapPhysicalSource<'b>>,
        padding_header_zero_capture_out: Option<&mut Option<PaddingHeaderZeroCapture>>,
        mixed_map_header_capture_out: Option<&mut Option<MixedMapHeaderCapture>>,
        c491_genesis_header_zero_capture_out: Option<&mut Option<C491GenesisHeaderZeroCapture<'b>>>,
    ) -> Result<NativePackedRow, String> {
        self.produce_inner_with_cap0_and_c496(owner, fault, bank53_map,
            #[cfg(test)] timings,
            #[cfg(test)] legacy_header,
            #[cfg(test)] bank53_witness,
            daa_source_out, cap0_source, cap1_source, overlay, census_out,
            scored_source, map_source, padding_header_zero_capture_out,
            mixed_map_header_capture_out, c491_genesis_header_zero_capture_out,
            None, None, None, None, None, None, None, None)
    }

    fn produce_inner_with_cap0_and_c496<'b>(
        &self,
        owner: usize,
        fault: AssemblyFault,
        bank53_map: Option<&Bank53MapAssignment>,
        #[cfg(test)] mut timings: Option<&mut NativePhaseTimings>,
        #[cfg(test)] legacy_header: bool,
        #[cfg(test)] bank53_witness: Option<&Bank53TestWitness>,
        mut daa_source_out: Option<&mut Option<DaaSourcePayload>>,
        cap0_source: Option<NativeCap0Source>,
        cap1_source: Option<NativeCap1Source>,
        overlay: Option<&Eligible08PackedOverlay<'_>>,
        census_out: Option<&mut Option<NativeOwnerAuthorCensus>>,
        scored_source: Option<&ScoredOwnerPackingView>,
        map_source: Option<MapPhysicalSource<'b>>,
        mut padding_header_zero_capture_out: Option<&mut Option<PaddingHeaderZeroCapture>>,
        mut mixed_map_header_capture_out: Option<&mut Option<MixedMapHeaderCapture>>,
        mut c491_genesis_header_zero_capture_out:
            Option<&mut Option<C491GenesisHeaderZeroCapture<'b>>>,
        c496_clipped_header_zero_capture_out:
            Option<&mut Option<C496ClippedHeaderZeroCapture<'b>>>,
        c498_source: Option<&C498ClippedScoreSource<'_, '_, '_>>,
        c498_capture_out: Option<&mut Option<Vec<Option<bool>>>>,
        regular_authors_out: Option<&mut Option<Vec<Option<NativeRegularPhysicalAuthor>>>>,
        scheduled_max_source: Option<&NativeScheduledMaxSource<'_, '_>>,
        mut scheduled_max_claims_out: Option<&mut Option<Vec<(
            usize, crate::h21_scheduled_max_cap::MaxReplayAuthor, bool,
        )>>>,
        work_endpoint_capture_out: Option<&mut Option<WorkEndpointCapture>>,
        coactive_admission: Option<&c580_coactive_type_harness::CoactiveAdmission<'_, '_, '_>>,
    ) -> Result<NativePackedRow, String> {
        if c498_source.is_some() != c498_capture_out.is_some()
            || c498_capture_out.as_ref().is_some_and(|out| out.is_some())
            || (c498_source.is_some() && c496_clipped_header_zero_capture_out.is_none()) {
            return Err("C498 requires fresh Score and C496 capture outputs".into());
        }
        if (cap0_source.is_some() || cap1_source.is_some()) && bank53_map.is_some() {
            return Err("Cap packed source cannot mix with Bank53 Map assignment".into());
        }
        #[cfg(test)]
        if (cap0_source.is_some() || cap1_source.is_some())
            && (legacy_header || bank53_witness.is_some()) {
            return Err("Cap packed source requires ordinary HEADER seed".into());
        }
        #[cfg(test)]
        if let Some(adapter) = self.legacy_adapter {
            adapter.check(self.plan, self.input)?;
            if self.max_adapter.is_some() { return Err("legacy native MAX mixing".into()); }
        }
        if owner >= self.plan.slots() {
            return Err("native owner outside original slot domain".into());
        }
        let class = self.roster.owner_class(owner as u64)?;
        let capture_padding=padding_header_zero_capture_out.is_some();
        let capture_mixed=mixed_map_header_capture_out.is_some();
        let capture_c491 = c491_genesis_header_zero_capture_out.is_some();
        let work_capture_enabled = work_endpoint_capture_out.is_some();
        let regular_enabled = regular_authors_out.is_some();
        let coactive = if let Some(admission) = coactive_admission {
            #[cfg(test)]
            let test_route = legacy_header || bank53_witness.is_some()
                || self.legacy_adapter.is_some();
            #[cfg(not(test))]
            let test_route = false;
            admission.check(self, owner, class, scheduled_max_source,
                work_endpoint_capture_out.as_ref().is_some_and(|out| out.is_none()),
                scheduled_max_claims_out.as_ref().is_some_and(|out| out.is_none()),
                daa_source_out.as_ref().is_some_and(|out| out.is_none()),
                bank53_map.is_some() || cap0_source.is_some() || cap1_source.is_some()
                    || overlay.is_some() || census_out.is_some() || regular_enabled
                    || scored_source.is_some() || map_source.is_some() || capture_padding
                    || capture_mixed || capture_c491
                    || c496_clipped_header_zero_capture_out.is_some()
                    || c498_source.is_some() || c498_capture_out.is_some()
                    || self.max_adapter.is_some() || test_route
                    || !matches!(fault, AssemblyFault::None))?;
            true
        } else { false };
        if coactive {
            c512f_require_separate_writer_options(regular_enabled,
                scheduled_max_source.is_some(), scheduled_max_claims_out.is_some())?;
        } else {
            c512j_require_separate_work_options(
                work_capture_enabled, census_out.is_some(), regular_enabled,
                scheduled_max_source.is_some(), scheduled_max_claims_out.is_some())?;
        }
        if work_capture_enabled {
            use crate::daa_history_roster::OwnerClass;
            if !coactive { self.c578_require_ordinary_work_capture(owner)?; }
            if class != OwnerClass::Carry
                || self.plan.headers() != 1_827_840 || self.plan.slot_log() != 21
                || self.plan.slots() != 1 << 21 || self.input.header_count() != 1_827_840
                || self.plan.leaf_profile().role(owner)? != leaf::Role::Genuine
                || self.max_adapter.is_some() || bank53_map.is_some()
                || cap0_source.is_some() || cap1_source.is_some() || overlay.is_some()
                || census_out.is_some() || scored_source.is_some() || map_source.is_some()
                || capture_padding || capture_mixed || capture_c491
                || c496_clipped_header_zero_capture_out.is_some()
                || c498_source.is_some() || c498_capture_out.is_some()
                || (daa_source_out.is_some() && !coactive)
                || !matches!(fault, AssemblyFault::None)
                || work_endpoint_capture_out.as_ref().is_some_and(|out| out.is_some()) {
                return Err("C512i Work endpoint capture requires isolated genuine Carry writer".into());
            }
            #[cfg(test)]
            if legacy_header || bank53_witness.is_some() || self.legacy_adapter.is_some() {
                return Err("C512i Work endpoint capture rejects test or legacy writer".into());
            }
            let tree_mask = self.plan.physical_assignment_replacement_mask(owner as u64)?;
            let header = self.header_source_lease(owner)?;
            if tree_mask.len() != WIDTH { return Err("C512i Tree mask width".into()); }
            for index in 0..C512I_CAPTURE_BITS {
                let local = WorkEndpointCapture::expected_local(index)?;
                if !tree_mask[local] || NativeHeaderSourceLease::bit(&header.owned, local) {
                    return Err("C512i Work endpoint not reserved for Tree before HEADER".into());
                }
            }
        }
        if let Some(source) = scheduled_max_source {
            use crate::daa_history_roster::OwnerClass;
            if source.class.owner != owner || class != OwnerClass::Carry
                || self.plan.headers() != 1_827_840 || self.plan.slot_log() != 21
                || self.plan.slots() != 1 << 21 || self.input.header_count() != 1_827_840
                || self.max_adapter.is_some() || daa_source_out.is_none()
                || bank53_map.is_some() || cap0_source.is_some() || cap1_source.is_some()
                || overlay.is_some() || census_out.is_some() || scored_source.is_some()
                || map_source.is_some() || capture_padding || capture_mixed || capture_c491
                || c496_clipped_header_zero_capture_out.is_some()
                || c498_source.is_some() || c498_capture_out.is_some()
                || !matches!(fault, AssemblyFault::None)
                || scheduled_max_claims_out.as_ref().is_some_and(|out| out.is_some())
                || source.binding != HeaderSourceBinding::for_plan(self.plan, owner)?
                || source.binding.profile() != self.input.profile() {
                return Err("C512c MAX requires isolated same-parent CarryZero calendar owner".into());
            }
            #[cfg(test)]
            if legacy_header || bank53_witness.is_some() || self.legacy_adapter.is_some() {
                return Err("C512c MAX rejects test or legacy writer route".into());
            }
            source.stream.closed_native_snapshot(self.plan, self.input)?;
            if c576_max_route(owner,class)?!=source.class || c512c_checked_max_cells(owner, &source.cells)? != source.max {
                return Err("C512c MAX retained source projection changed".into());
            }
        }
        let c496_binding = if let Some(out) = c496_clipped_header_zero_capture_out.as_ref() {
            use crate::daa_history_roster::OwnerClass;
            let Some(MapPhysicalSource::Pair(lease)) = map_source.as_ref() else {
                return Err("C496 capture requires exact Map-only Pair route".into());
            };
            if out.is_some() || class != OwnerClass::Carry || self.max_adapter.is_some()
                || !matches!(fault, AssemblyFault::None)
                || self.plan.headers() != 1_827_840 || self.plan.slot_log() != 21
                || self.plan.slots() != 1 << 21 || self.input.header_count() != 1_827_840
                || capture_padding || capture_mixed || capture_c491 || bank53_map.is_some()
                || cap0_source.is_some() || cap1_source.is_some() || overlay.is_some()
                || census_out.is_some() || scored_source.is_some() || daa_source_out.is_some() {
                return Err("C496 capture requires isolated clipped H21 Carry route".into());
            }
            #[cfg(test)]
            if legacy_header || bank53_witness.is_some() || self.legacy_adapter.is_some() {
                return Err("C496 capture rejects test/legacy HEADER route".into());
            }
            let active_context = match owner {
                1_810_904 => 0, 1_810_841 => 1,
                _ => return Err("C496 clipped owner/context identity".into()),
            };
            let binding = HeaderSourceBinding::for_plan(self.plan, owner)?;
            c496_require_binding(&binding, active_context)?;
            if binding.profile() != self.input.profile() || lease.binding() != &binding {
                return Err("C496 exact source Map pair binding".into());
            }
            lease.checked_cells(&binding, owner, class)?;
            Some((binding, active_context))
        } else { None };
        let c491_binding = if capture_c491 {
            use crate::daa_history_roster::OwnerClass;
            let Some(MapPhysicalSource::PairSlack(bundle)) = map_source.as_ref() else {
                return Err("C491 HeaderZero capture requires the owner0 Map+Slack bundle".into());
            };
            if owner != 0 || class != OwnerClass::Genesis
                || self.plan.headers() != 1_827_840
                || self.plan.slot_log() != 21 || self.plan.slots() != 1 << 21
                || self.input.header_count() != crate::bank53_map::BANK53_N as usize
                || self.max_adapter.is_some() || capture_padding || capture_mixed
                || bank53_map.is_some() || cap0_source.is_some() || cap1_source.is_some()
                || overlay.is_some() || census_out.is_some() || scored_source.is_some()
                || daa_source_out.is_some()
            {
                return Err("C491 HeaderZero capture requires isolated owner0 Genesis Map+Slack route".into());
            }
            #[cfg(test)]
            if legacy_header || bank53_witness.is_some() || self.legacy_adapter.is_some() {
                return Err("C491 HeaderZero capture rejects test/legacy HEADER path".into());
            }
            let binding = HeaderSourceBinding::for_plan(self.plan, owner)?;
            if binding.profile() != self.input.profile()
                || bundle.map_lease().binding() != &binding
            {
                return Err("C491 HeaderZero capture exact Map+Slack binding mismatch".into());
            }
            Some(binding)
        } else { None };
        if capture_mixed {
            require_mixed_map_header_route(&MixedMapHeaderRoute {
                owner,class,plan_headers:self.plan.headers(),plan_slot_log:self.plan.slot_log(),
                plan_slots:self.plan.slots(),input_header_count:self.input.header_count(),
                has_max_adapter:self.max_adapter.is_some(),padding_capture:capture_padding,
                exact_map_pair:matches!(map_source.as_ref(),Some(MapPhysicalSource::Pair(_))),
                has_other_source:bank53_map.is_some() || cap0_source.is_some()
                    || cap1_source.is_some() || overlay.is_some() || census_out.is_some()
                    || scored_source.is_some() || daa_source_out.is_some(),
            })?;
        }
        #[cfg(test)]
        let test_header_route=legacy_header || bank53_witness.is_some()
            || self.legacy_adapter.is_some();
        #[cfg(not(test))]
        let test_header_route=false;
        require_padding_header_zero_route(&PaddingHeaderZeroRoute {
            capture_requested: capture_padding,
            owner,
            class,
            plan_headers: self.plan.headers(),
            plan_slot_log: self.plan.slot_log(),
            plan_slots: self.plan.slots(),
            input_header_count: self.input.header_count(),
            has_max_adapter: self.max_adapter.is_some(),
            test_header_route,
            has_bank53_map: bank53_map.is_some(),
            has_cap0: cap0_source.is_some(),
            has_cap1: cap1_source.is_some(),
            has_overlay: overlay.is_some(),
            has_census: census_out.is_some(),
            has_scored_source: scored_source.is_some(),
            has_map_source: map_source.is_some(),
            has_daa_source_out: daa_source_out.is_some(),
        })?;
        let padding_binding=if capture_padding {
            let binding=HeaderSourceBinding::for_plan(self.plan,owner)?;
            if binding.profile()!=self.input.profile() {
                return Err("C449 padding HEADER-zero profile binding".into());
            }
            Some(binding)
        } else {None};
        let mixed_binding=if capture_mixed {
            let binding=HeaderSourceBinding::for_plan(self.plan,owner)?;
            if binding.profile()!=self.input.profile() {
                return Err("C450 mixed capture profile binding".into());
            }
            let Some(MapPhysicalSource::Pair(lease))=map_source.as_ref() else {
                return Err("C450 mixed capture requires typed Map pair".into());
            };
            if lease.binding()!=&binding {
                return Err("C450 mixed capture Map pair binding".into());
            }
            Some(binding)
        } else {None};
        if scored_source.is_some() && (
            h21_eligible_context::Eligible08RegularScoreOwner::classify(owner).is_err()
                || class != crate::daa_history_roster::OwnerClass::Carry
                || cap0_source.is_some() || cap1_source.is_some() || overlay.is_some()
                || bank53_map.is_some() || census_out.is_some() || self.max_adapter.is_some()
                || daa_source_out.is_none()) {
            return Err("C396 source requires isolated regular CarryZero owner path".into());
        }
        if let Some(source) = map_source.as_ref() {
            if owner == FIRST_MODERN_CAP0_OWNER
                || h21_eligible_context::Eligible08RegularScoreOwner::classify(owner).is_ok()
                || bank53_map.is_some() || self.max_adapter.is_some()
                || cap0_source.is_some() || cap1_source.is_some()
                || overlay.is_some() || scored_source.is_some()
                || census_out.is_some() || daa_source_out.is_some()
            {
                return Err("C438 Map pair cannot mix with another Bank53/source path".into());
            }
            if matches!(source, MapPhysicalSource::PairSlack(_))
                && (owner != 0 || class != crate::daa_history_roster::OwnerClass::Genesis)
            {
                return Err("C441 Map+Slack physical path only authorizes Genesis owner0".into());
            }
            if matches!(source, MapPhysicalSource::PairSlackAnchor(_))
                && (owner != 417_790 || class != crate::daa_history_roster::OwnerClass::Carry)
            {
                return Err("C441 ScoreAnchor physical path requires Carry owner417790".into());
            }
            if matches!(source, MapPhysicalSource::PairSlackSecondAnchor(_, _))
                && (owner != 845_758 || class != crate::daa_history_roster::OwnerClass::Carry)
            {
                return Err("C443 second ScoreAnchor physical path requires Carry owner845758".into());
            }
            #[cfg(test)]
            if legacy_header || bank53_witness.is_some() || self.legacy_adapter.is_some() {
                return Err("C438 Map pair rejects legacy/test HEADER path".into());
            }
            let binding = HeaderSourceBinding::for_plan(self.plan, owner)?;
            if binding.profile() != self.input.profile() {
                return Err("C438 Map pair native profile drift".into());
            }
            source.map_lease().checked_cells(&binding, owner, class)?;
            if let MapPhysicalSource::PairSlack(bundle) = source {
                bundle.checked_slack_cells(&binding, owner, class)?;
                for context in 0..BANK53_CONTEXTS {
                    bundle.checked_slack_terms(&binding, owner, class, context)?;
                }
            }
            if let MapPhysicalSource::PairSlackAnchor(bundle) = source {
                checked_anchor_bank53_cells(*bundle, &binding, owner, class)?;
            }
            if let MapPhysicalSource::PairSlackSecondAnchor(bundle, _) = source {
                checked_anchor_bank53_cells(*bundle, &binding, owner, class)?;
            }
        }
        let mut overlay_cells = if let Some(source) = overlay {
            if owner != FIRST_MODERN_CAP0_OWNER
                || class != crate::daa_history_roster::OwnerClass::Carry
                || self.max_adapter.is_some() || bank53_map.is_some()
                || cap0_source.is_none() || cap1_source.is_none()
                || daa_source_out.is_none() {
                return Err("C373 overlay requires exact ordinary Carry/Cap01 source".into());
            }
            #[cfg(test)]
            if legacy_header || bank53_witness.is_some() || self.legacy_adapter.is_some() {
                return Err("C373 overlay rejects test/legacy HEADER source".into());
            }
            let binding = HeaderSourceBinding::for_plan(self.plan, owner)?;
            if binding.profile != self.input.profile()
                || cap0_source.as_ref().is_none_or(|cap| cap.binding() != &binding)
                || cap1_source.as_ref().is_none_or(|cap| cap.binding() != &binding) {
                return Err("C373 overlay exact native/Cap01 binding".into());
            }
            Some(source.checked_cells(&binding, owner)?)
        } else { None };
        let census_enabled = census_out.is_some();
        if census_enabled && (owner != POINT_MEMBERSHIP_OWNER
            || overlay_cells.is_none() || daa_source_out.is_none()
            || cap0_source.is_none() || cap1_source.is_none()
            || self.max_adapter.is_some() || bank53_map.is_some())
        {
            return Err("C374 census requires exact ordinary Eligible08 Carry/Cap01/Map owner".into());
        }
        #[cfg(test)]
        if census_enabled && (legacy_header || bank53_witness.is_some()
            || self.legacy_adapter.is_some())
        {
            return Err("C374 census rejects test or legacy source".into());
        }
        if regular_enabled && (c574_regular_owner(owner).is_err()
            || class != crate::daa_history_roster::OwnerClass::Carry
            || self.plan.headers() != 1_827_840 || self.plan.slot_log() != 21
            || self.plan.slots() != 1 << 21 || self.input.header_count() != 1_827_840
            || scored_source.is_none() || daa_source_out.is_none()
            || census_enabled || overlay_cells.is_some() || bank53_map.is_some()
            || cap0_source.is_some() || cap1_source.is_some() || map_source.is_some()
            || capture_padding || capture_mixed || capture_c491
            || c496_binding.is_some() || c498_source.is_some()
            || c498_capture_out.is_some() || self.max_adapter.is_some()
            || !matches!(fault, AssemblyFault::None)
            || regular_authors_out.as_ref().is_some_and(|out| out.is_some()))
        {
            return Err("C512e regular author capture requires isolated owner845887 scored CarryZero route".into());
        }
        #[cfg(test)]
        if regular_enabled && (legacy_header || bank53_witness.is_some()
            || self.legacy_adapter.is_some())
        {
            return Err("C512e regular author capture rejects test or legacy source".into());
        }
        let point_source = if census_enabled {
            Some(self.point_membership_source_lease(owner)?)
        } else { None };
        let tree_source = if census_enabled {
            Some(NativeTreeSourceLease::from_prefix(self.plan, self.input, owner)?)
        } else { None };
        let selection = OwnerSelection::Single { owner, class };
        #[cfg(test)]
        c578_record_native_assembly()?;
        let mut rows = native_timed!(timings, allocation_ns, OwnedRows::new(selection));
        if work_capture_enabled { rows.begin_work_endpoint_capture(owner)?; }
        if let Some((binding, active_context)) = c496_binding {
            let Some(MapPhysicalSource::Pair(lease)) = map_source.as_ref() else {
                return Err("C496 Map pair disappeared before capture".into());
            };
            rows.begin_c496_clipped_header_zero_capture(binding, active_context, lease)?;
        }
        if let Some(source) = c498_source {
            rows.begin_c498_clipped_score_capture(source)?;
        }
        if let Some(binding)=padding_binding {
            rows.begin_padding_header_zero_capture(binding)?;
        }
        if let Some(binding)=mixed_binding {
            rows.begin_mixed_map_header_capture(binding)?;
        }
        if let Some(binding)=c491_binding.as_ref() {
            rows.begin_c491_genesis_header_zero_capture(
                C491GenesisHeaderZeroRoute::GenesisMapSlackBundle,
                binding.clone(),
            )?;
        }
        if census_enabled {
            rows.begin_author_census()?;
            rows.set_author(NativePhysicalAuthor::Header)?;
        }
        if regular_enabled {
            rows.begin_regular_author_census()?;
            rows.set_regular_author(NativeRegularPhysicalAuthor::Header)?;
        }
        #[cfg(test)]
        let header_result = if let Some(assignment) = bank53_map {
            if assignment.h21_test_only {
                seed_header_from_template_bank53_map_h21_for_test(
                    &self.header_template,
                    self.plan,
                    self.input,
                    owner,
                    assignment.context,
                    &mut rows,
                )
            } else {
                seed_header_from_template_bank53_map(
                    &self.header_template,
                    self.plan,
                    self.input,
                    owner,
                    assignment.context,
                    &mut rows,
                )
            }
        } else if let Some(witness) = bank53_witness {
            seed_header_from_template_bank53_for_test(
                &self.header_template, self.plan, self.input, owner, witness.context, &mut rows,
            )
        } else if legacy_header {
            seed_header(self.plan, self.max_adapter, self.legacy_adapter, self.input, owner, &mut rows, timings.as_deref_mut())
        } else {
            seed_header_from_template(
                &self.header_template, self.plan, self.max_adapter, self.legacy_adapter, self.input, owner, &mut rows,
                timings.as_deref_mut(),
                cap0_source.as_ref(),
                cap1_source.as_ref(),
                overlay_cells.is_some(),
                scored_source,
                map_source.as_ref(),
                scheduled_max_source,
            )
        };
        #[cfg(not(test))]
        let header_result = if let Some(assignment) = bank53_map {
            seed_header_from_template_bank53_map(
                &self.header_template,
                self.plan,
                self.input,
                owner,
                assignment.context,
                &mut rows,
            )
        } else {
            seed_header_from_template(
                &self.header_template,
                self.plan,
                self.max_adapter,
                self.input,
                owner,
                &mut rows,
                cap0_source.as_ref(),
                cap1_source.as_ref(),
                overlay_cells.is_some(),
                scored_source,
                map_source.as_ref(),
                scheduled_max_source,
            )
        };
        header_result?;
        if let Some(source) = c498_source {
            for &(wire, _, value) in source.relation.cells() {
                rows.claim_c498_clipped_score(owner, wire % WIDTH, value)?;
            }
        }
        if let Some(source) = point_source.as_ref() {
            rows.set_author(NativePhysicalAuthor::PointMembership)?;
            for (bit, &value) in source.bits.iter().enumerate() {
                rows.claim_exclusive(owner, crate::segment_points::POINT_OFFSET + bit,
                    Fr::from(value as u64))?;
            }
        }
        if let Some(assignment) = bank53_map {
            if assignment.owner != owner {
                return Err("bank53 Map assignment owner mismatch".into());
            }
            write_bank53_map_assignment(&mut rows, assignment)?;
        }
        #[cfg(test)]
        if let Some(witness) = bank53_witness {
            write_bank53_witness_for_test(&mut rows, owner, witness.context, witness)?;
        }
        if census_enabled { rows.set_author(NativePhysicalAuthor::Tree)?; }
        if regular_enabled { rows.set_regular_author(NativeRegularPhysicalAuthor::Tree)?; }
        if work_capture_enabled { rows.begin_work_endpoint_tree_phase()?; }
        native_timed!(
            timings,
            tree_ns,
            seed_tree(self.plan, self.input, owner, &mut rows, fault)
        )?;
        if work_capture_enabled { rows.finish_work_endpoint_tree_phase()?; }
        if let Some(adapter) = self.max_adapter {
            for (offset, value) in adapter.helpers(self.input, owner)?.into_iter().enumerate() {
                rows.claim(owner, crate::max_header_adapter::BASE + offset, value)?;
            }
        }
        #[cfg(test)]
        if let Some(adapter) = self.legacy_adapter {
            for (offset, value) in adapter.helpers(owner)?.into_iter().enumerate() {
                rows.claim(owner, crate::legacy_envelope_map::BASE + offset, Fr::from(value as u64))?;
            }
        }
        if census_enabled { rows.set_author(NativePhysicalAuthor::Daa)?; }
        if regular_enabled { rows.set_regular_author(NativeRegularPhysicalAuthor::Daa)?; }
        let mut daa_zero_claims = if daa_source_out.is_some() {
            match class {
                OwnerClass::Carry => Some(DaaSourcePayload::CarryZero(
                    self.claim_carry_zero_banks(owner, class, &mut rows)?,
                )),
                OwnerClass::Genesis | OwnerClass::Initial | OwnerClass::FixedV2
                    | OwnerClass::Singleton | OwnerClass::Padding => {
                    Some(DaaSourcePayload::FullZero(
                        self.claim_full_zero_banks(owner, class, &mut rows)?,
                    ))
                }
                OwnerClass::M1 | OwnerClass::Short(_) | OwnerClass::Mature(_) => None,
                _ => return Err("native DAA source lease owner class".into()),
            }
        } else {
            None
        };
        if census_enabled { rows.set_author(NativePhysicalAuthor::Cap)?; }
        if let Some(source) = cap0_source.as_ref() {
            source.claim_exclusive(owner, &mut rows)?;
        }
        if let Some(source) = cap1_source.as_ref() {
            source.claim_exclusive(owner, &mut rows)?;
        }
        if let Some(source) = scored_source {
            if regular_enabled { rows.set_regular_author(NativeRegularPhysicalAuthor::Scored)?; }
            let binding = HeaderSourceBinding::for_plan(self.plan, owner)?;
            claim_scored_owner_source(&mut rows, source, &binding)?;
        }
        if census_enabled { rows.set_author(NativePhysicalAuthor::Bank53)?; }
        if let Some(cells) = overlay_cells.as_ref() {
            let binding = HeaderSourceBinding::for_plan(self.plan, owner)?;
            claim_eligible08_overlay_map(&mut rows, owner, &cells.map_score_slack, &binding)?;
        }
        if let Some(source) = map_source.as_ref() {
            let binding = HeaderSourceBinding::for_plan(self.plan, owner)?;
            match source {
                MapPhysicalSource::Pair(lease) =>
                    claim_map_pair_live(&mut rows, lease, &binding, owner, class)?,
                MapPhysicalSource::PairSlack(bundle) => {
                    claim_map_slack_live(&mut rows, bundle, &binding, owner, class)?;
                    require_map_slack_claim_census(&rows, bundle, &binding, owner, class)?;
                }
                MapPhysicalSource::PairSlackAnchor(bundle) => {
                    claim_map_slack_anchor_live(&mut rows, *bundle, &binding, owner, class)?;
                    require_map_slack_anchor_claim_census(
                        &rows, *bundle, &binding, owner, class,
                    )?;
                }
                MapPhysicalSource::PairSlackSecondAnchor(bundle, _) => {
                    claim_map_slack_anchor_live(&mut rows, *bundle, &binding, owner, class)?;
                    require_map_slack_anchor_claim_census(
                        &rows, *bundle, &binding, owner, class,
                    )?;
                }
            }
        }
        if let Some(source) = scheduled_max_source {
            use crate::h21_scheduled_max_cap::{MaxReplayAuthor, Writer};
            let expected_claims=source.class.count()*C512C_MAX_BITS;
            let mut claims = Vec::new();
            claims.try_reserve_exact(expected_claims).map_err(|_|"C576 physical MAX claim allocation")?;
            for context in 0..2 {
                for &(local, value) in &source.max[context] {
                    rows.claim_exclusive(owner, local, value)?;
                    claims.push((local, MaxReplayAuthor::Scheduled(Writer::Max {
                        context, end: owner + 2,
                    }), value.is_one()));
                }
            }
            if claims.len() != expected_claims {
                return Err("C512c complete zero-inclusive physical MAX claims".into());
            }
            let out = scheduled_max_claims_out.as_deref_mut()
                .ok_or("C512c MAX claim output disappeared")?;
            if out.is_some() {
                return Err("C512c duplicate MAX claim publication".into());
            }
            *out = Some(claims);
        }
        let mut packed = native_timed!(timings, pack_initial_ns, rows.bytes(0))?;
        use crate::daa_history_roster::OwnerClass;
        if matches!(class, OwnerClass::M1 | OwnerClass::Short(_) | OwnerClass::Mature(_)) {
            native_timed!(timings, retarget_ns, {
                let height = (owner + 1) as u32;
                let schedule = crate::daa_header_window::for_child_height(height)?;
                let samples = schedule
                    .sample_heights()
                    .iter()
                    .map(|&h| self.input.raw(h as usize))
                    .collect::<Result<Vec<_>, _>>()?;
                let window = crate::daa_history_producer::RawWindow {
                    parent: self.input.raw(owner)?,
                    child: self.input.raw(owner + 1)?,
                    samples: &samples,
                };
                if let Some(out) = daa_source_out.as_deref_mut() {
                    if self.max_adapter.is_some() {
                        return Err("DAA source lease rejects MAX adapter".into());
                    }
                    #[cfg(test)]
                    if self.legacy_adapter.is_some() {
                        return Err("DAA source lease rejects legacy adapter".into());
                    }
                    let (_, patch) = crate::daa_history_producer::write_retarget_with_patch(
                        &self.roster, owner as u64, window, &mut packed,
                        |index| self.exports.bit(index),
                    )?;
                    *out = Some(DaaSourcePayload::NativeRetarget(patch));
                } else {
                    crate::daa_history_producer::write_retarget(
                        &self.roster, owner as u64, window, &mut packed,
                        |index| self.exports.bit(index),
                    )?;
                }
            });
        } else if !matches!(
            class,
            OwnerClass::Genesis
                | OwnerClass::Initial
                | OwnerClass::Carry
                | OwnerClass::Singleton
                | OwnerClass::FixedV2
                | OwnerClass::Padding
        ) {
            return Err("native owner class outside admitted prefix".into());
        }
        #[cfg(test)]
        let mut late_daa_generic_claims = 0usize;
        native_timed!(timings, bank_claims_ns, {
            if daa_zero_claims.is_none() {
                for (lo, hi) in BANKS {
                    for wire in lo..hi {
                        rows.claim(
                            owner,
                            wire,
                            Fr::from(((packed[wire / 8] >> (wire % 8)) & 1) as u64),
                        )?;
                        #[cfg(test)]
                        { late_daa_generic_claims += 1; }
                    }
                }
            }
        });
        #[cfg(test)]
        if daa_zero_claims.is_some() && late_daa_generic_claims != 0 {
            return Err("FullZero source followed by late generic DAA claim".into());
        }
        #[cfg(test)]
        match fault {
            AssemblyFault::ConflictingClaim {
                owner: target,
                wire,
            } => {
                let (r, w) = rows.local(target as usize, wire)?;
                rows.claim(target as usize, wire, Fr::one() - rows.values[r][w])?;
            }
            AssemblyFault::NonBooleanClaim {
                owner: target,
                wire,
            } => rows.claim(target as usize, wire, Fr::from(2u64))?,
            AssemblyFault::MissingClaim {
                owner: target,
                wire,
            } => {
                let (r, w) = rows.local(target as usize, wire)?;
                rows.claimed[r][w] = false;
            }
            AssemblyFault::FlipBit { .. } => {
                return Err("production does not export an unvalidated bit fault".into())
            }
            _ => (),
        }
        if let Some(wire) = native_timed!(
            timings,
            completeness_ns,
            rows.claimed[0].iter().position(|claimed| !*claimed)
        ) {
            return Err(format!("missing claim owner{owner} wire{wire}"));
        }
        let unadapted = bank53_map.is_none() && self.max_adapter.is_none()
            && matches!(fault, AssemblyFault::None);
        #[cfg(test)]
        let unadapted = unadapted && self.legacy_adapter.is_none()
            && !legacy_header && bank53_witness.is_none();
        let bytes = native_timed!(timings, pack_final_ns, rows.bytes(0))?;
        if let Some(cells) = overlay_cells.as_ref() {
            require_eligible08_overlay_packed(owner, &bytes, cells,
                &HeaderSourceBinding::for_plan(self.plan, owner)?)?;
        }
        if let Some(source) = map_source.as_ref() {
            let binding = HeaderSourceBinding::for_plan(self.plan, owner)?;
            match source {
                MapPhysicalSource::Pair(lease) =>
                    require_map_pair_packed(&bytes, lease, &binding, owner, class)?,
                MapPhysicalSource::PairSlack(bundle) =>
                    require_map_slack_packed(&bytes, bundle, &binding, owner, class)?,
                MapPhysicalSource::PairSlackAnchor(bundle) =>
                    require_map_slack_anchor_packed(&bytes, *bundle, &binding, owner, class)?,
                MapPhysicalSource::PairSlackSecondAnchor(bundle, _) =>
                    require_map_slack_anchor_packed(&bytes, *bundle, &binding, owner, class)?,
            }
        }
        if let Some(source) = scored_source {
            require_scored_owner_source_packed(
                &bytes, source, &HeaderSourceBinding::for_plan(self.plan, owner)?,
            )?;
        }
        if let Some(claims) = daa_zero_claims.as_ref() {
            match claims {
                DaaSourcePayload::CarryZero(claims) => {
                    claims.check_identity(owner as u64, class)?;
                    if BANKS.iter().any(|&(start, end)|
                        bytes[start / 8..end / 8].iter().any(|byte| *byte != 0)) {
                        return Err("CarryZero explicit claims differ from final packed banks".into());
                    }
                }
                DaaSourcePayload::FullZero(claims) => {
                    check_full_zero_packed_banks(&bytes, claims, owner as u64, class)?;
                }
                DaaSourcePayload::NativeRetarget(_) => {
                    return Err("retarget patch cannot replace prepack zero claims".into());
                }
            }
        }
        if let Some(out) = daa_source_out.as_deref_mut() {
            if let Some(claims) = daa_zero_claims.take() {
                if out.is_some() {
                    return Err("DAA zero source output already occupied".into());
                }
                *out = Some(claims);
            } else if !matches!(out.as_ref(), Some(DaaSourcePayload::NativeRetarget(_))) {
                return Err("native retarget DAA source author missing".into());
            }
        }
        let header_source_binding = if unadapted && self.plan.headers() == 1_827_840
            && self.plan.slot_log() == 21 {
            let binding = HeaderSourceBinding::for_plan(self.plan, owner)?;
            if binding.profile != self.input.profile() {
                return Err("native packed ROW source profile drift".into());
            }
            Some(binding)
        } else { None };
        let row = NativePackedRow {
            owner,
            class,
            root: self.input.root,
            total: self.input.total,
            bytes,
            header_source_binding,
            cap0_source,
            cap1_source,
            max_binding: self.max_adapter.map(|adapter| adapter.binding()),
            map_binding: bank53_map.map(|assignment| assignment.binding.clone()),
            map_context: bank53_map.map(|assignment| assignment.context),
            #[cfg(test)]
            legacy_binding: self.legacy_adapter.map(|adapter| adapter.binding()),
        };
        // Check Score before consuming either capture; an error publishes neither.
        let c498_cells = c498_source.map(|source|
            rows.check_c498_clipped_score_capture(&row, source)).transpose()?;
        if let Some(out) = c496_clipped_header_zero_capture_out {
            let Some(MapPhysicalSource::Pair(lease)) = map_source.as_ref() else {
                return Err("C496 Map pair disappeared at final packing".into());
            };
            *out = Some(rows.finish_c496_clipped_header_zero_capture(&row, lease)?);
        }
        if let Some(out) = c498_capture_out { *out = c498_cells; }
        if let Some(out)=padding_header_zero_capture_out {
            if out.is_some() {
                return Err("C449 padding HEADER-zero capture output already occupied".into());
            }
            *out=Some(rows.finish_padding_header_zero_capture(&row)?);
        }
        if let Some(out)=mixed_map_header_capture_out {
            if out.is_some() {
                return Err("C450 mixed capture output already occupied".into());
            }
            *out=Some(rows.finish_mixed_map_header_capture(&row)?);
        }
        if let Some(out)=c491_genesis_header_zero_capture_out {
            if out.is_some() {
                return Err("C491 HeaderZero capture output already occupied".into());
            }
            let Some(MapPhysicalSource::PairSlack(bundle))=map_source.as_ref() else {
                return Err("C491 HeaderZero source bundle disappeared".into());
            };
            *out=Some(rows.finish_c491_genesis_header_zero_capture(&row,bundle)?);
        }
        if let Some(out) = census_out {
            if out.is_some() {
                return Err("C374 census output already occupied".into());
            }
            let binding = HeaderSourceBinding::for_plan(self.plan, owner)?;
            let census = NativeOwnerAuthorCensus {
                complete_checked: Cell::new(false),
                binding: binding.clone(),
                authors: rows.author_census.take()
                    .ok_or("C374 physical author tracking absent")?,
                source_bits: rows.bytes(0)?,
                bank53_source: overlay_cells.take()
                    .ok_or("C375 census Bank53 lease absent")?.map_score_slack,
                header_source: self.header_source_lease(owner)?,
                point_source: point_source.ok_or("C374 Point source absent")?,
                tree_source: tree_source.ok_or("C376 Tree source absent")?,
            };
            census.check_complete(&binding, &row)?;
            *out = Some(census);
        }
        if let Some(out) = work_endpoint_capture_out {
            if out.is_some() { return Err("C512i duplicate Work endpoint capture output".into()); }
            let mut capture = rows.work_endpoint_capture.take()
                .ok_or("C512i Work endpoint events absent after packed row")?;
            if capture.phase != WorkEndpointPhase::AfterTree
                || capture.events.len() != C512I_CAPTURE_BITS {
                return Err("C512i incomplete Work endpoint events after packed row".into());
            }
            capture.seal_row(&row)?;
            *out = Some(capture);
        }
        if let Some(out) = regular_authors_out {
            if out.is_some() || rows.current_regular_author != Some(NativeRegularPhysicalAuthor::Scored) {
                return Err("C512e regular author output or final phase".into());
            }
            let authors = rows.regular_author_census.take()
                .ok_or("C512e actual regular physical claim image absent")?;
            if authors.len() != WIDTH || authors.iter().any(Option::is_none) {
                return Err("C512e incomplete regular physical claim image including zeroes".into());
            }
            *out = Some(authors);
        }
        Ok(row)
    }
}

#[cfg(test)]
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) enum C433TreeAuthorFault {
    TreeAuthor,TreeBinding,UpperTreeOmission,ExponentTreeOmission,
    UpperHeaderMask,ExponentHeaderMask,UpperTreeValue,ExponentTreeValue,
}
#[cfg(test)]
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) enum C434TreeAuthorFault {
    TreeAuthor,TreeBinding,TreeOmissionLast,HeaderMaskLast,TreeValueLast,
}

// The point bank is a fixed subrange of each 2^20-bit native owner row. These
// geometry functions cannot choose a bank or an owner domain at call time.
const H21_ROLE3_HEADERS: u64 = 1_827_840;
const H21_ROLE3_SLOTS: usize = 1 << 21;
const H21_ROLE3_POINT_LOG: usize = 13;

fn h21_role3_wire_geometry(owner: usize, local: usize) -> Result<usize, String> {
    if owner >= H21_ROLE3_SLOTS || local >= crate::point_membership::POINT_WIDTH {
        return Err("H21 point owner/local coordinate outside source domain".into());
    }
    let wire = owner.checked_mul(WIDTH)
        .and_then(|base| base.checked_add(crate::segment_points::POINT_OFFSET))
        .and_then(|base| base.checked_add(local))
        .ok_or("H21 point global wire overflow")?;
    if wire >= (1usize << 41) {
        return Err("H21 point global wire outside common X".into());
    }
    Ok(wire)
}

fn h21_role3_point_geometry(point: &[Fr]) -> Result<Vec<Fr>, String> {
    if point.len() != H21_ROLE3_POINT_LOG + 21 {
        return Err("H21 point terminal must have 34 coordinates".into());
    }
    let projected = layout::embed_bank(
        crate::segment_points::POINT_OFFSET,
        crate::point_membership::POINT_WIDTH,
        21,
        point,
    )?;
    if projected.len() != 41 {
        return Err("H21 point projection is not common-X width".into());
    }
    Ok(projected)
}

fn require_h21_role3_plan(plan: &WorkTreeHistoryPlan) -> Result<(), String> {
    if plan.headers() != H21_ROLE3_HEADERS || plan.slot_log() != 21
        || plan.slots() != H21_ROLE3_SLOTS || WIDTH != 1 << 20
        || crate::segment_points::POINT_OFFSET != 96 * crate::point_membership::POINT_WIDTH
        || crate::point_membership::POINT_WIDTH != 1 << H21_ROLE3_POINT_LOG
    {
        return Err("H21 point source geometry differs".into());
    }
    let baseline = layout::shared_baseline()?;
    let bank = baseline.inventory.banks.iter().find(|bank| bank.role == "points")
        .ok_or("H21 point bank absent from source layout")?;
    if bank.start != crate::segment_points::POINT_OFFSET
        || bank.end != bank.start + crate::point_membership::POINT_WIDTH
        || bank.live_bits != crate::point_membership::POINT_WIDTH
        || bank.alignment != crate::point_membership::POINT_WIDTH
    {
        return Err("H21 point source bank differs".into());
    }
    Ok(())
}

/// A producer-owned coordinate projection. It binds the fixed point-bank
/// geometry to the same checked native plan/input that produces owner rows.
/// It does not authenticate a PCS opening or admit a complete H21 proof.
pub(crate) struct H21PointProjection<'p, 'a> {
    _source: &'p NativeOwnerProducer<'a>,
}

impl<'p, 'a> H21PointProjection<'p, 'a> {
    pub(crate) fn global_wire(&self, owner: usize, local: usize) -> Result<usize, String> {
        h21_role3_wire_geometry(owner, local)
    }

    pub(crate) fn project(&self, point: &[Fr]) -> Result<Vec<Fr>, String> {
        h21_role3_point_geometry(point)
    }
}

impl<'a> NativeOwnerProducer<'a> {
    pub(crate) fn h21_point_projection(&self) -> Result<H21PointProjection<'_, 'a>, String> {
        require_h21_role3_plan(self.plan)?;
        validate_native_plan_input(self.plan, self.input)?;
        if let Some(adapter) = self.max_adapter {
            adapter.check_parent(self.plan)?;
        }
        #[cfg(test)]
        if self.legacy_adapter.is_some() {
            return Err("H21 point projection has no legacy adapter binding".into());
        }
        Ok(H21PointProjection { _source: self })
    }
}

#[cfg(test)]
mod h21_role3_projection_unit_tests {
    use super::*;

    fn boolean_point(width: usize, index: usize) -> Vec<Fr> {
        (0..width).map(|bit| Fr::from(((index >> bit) & 1) as u64)).collect()
    }

    fn independent_eq(point: &[Fr], index: usize) -> Fr {
        point.iter().enumerate().fold(Fr::one(), |weight, (bit, coordinate)| {
            if ((index >> bit) & 1) != 0 {
                weight * coordinate
            } else {
                weight * (Fr::one() - coordinate)
            }
        })
    }

    #[test]
    fn h21_role3_no_frame_source_geometry_and_dense_oracle() {
        let plan = WorkTreeHistoryPlan::compile(
            H21_ROLE3_HEADERS, 21, [0x5a; 32], [0x42; 28],
        ).unwrap();
        require_h21_role3_plan(&plan).unwrap();
        let small = WorkTreeHistoryPlan::compile(3, 2, [0x5a; 32], [0x42; 28]).unwrap();
        assert!(require_h21_role3_plan(&small).is_err());
        for owner in [0, 1, 844_672, 1_827_839, H21_ROLE3_SLOTS - 1] {
            for local in [0, 1, 4095, crate::point_membership::POINT_WIDTH - 1] {
                let wire = h21_role3_wire_geometry(owner, local).unwrap();
                assert_eq!(wire, (owner << 20) + 786_432 + local);
                let local_point = boolean_point(13, local);
                let owner_point = boolean_point(21, owner);
                let point = [local_point, owner_point].concat();
                assert_eq!(h21_role3_point_geometry(&point).unwrap(), boolean_point(41, wire));
            }
        }
        assert!(h21_role3_wire_geometry(H21_ROLE3_SLOTS, 0).is_err());
        assert!(h21_role3_wire_geometry(0, 8192).is_err());
        assert!(h21_role3_point_geometry(&vec![Fr::zero(); 33]).is_err());
        assert!(h21_role3_point_geometry(&vec![Fr::zero(); 35]).is_err());

        // Independently sum one complete 8192-bit bank as a sparse column of
        // common X, without allocating the 2^41-bit history table.
        let owner = 844_672usize;
        let local_point: Vec<_> = (0..13).map(|bit| Fr::from((bit + 2) as u64)).collect();
        let point = [local_point.clone(), boolean_point(21, owner)].concat();
        let projected = h21_role3_point_geometry(&point).unwrap();
        assert_eq!(&projected[13..20], &[Fr::zero(), Fr::zero(), Fr::zero(),
            Fr::zero(), Fr::zero(), Fr::one(), Fr::one()]);
        let mut local_sum = Fr::zero();
        let mut global_sum = Fr::zero();
        for local in 0..8192usize {
            let bit = local == 0 || local % 17 == 0;
            if bit {
                local_sum += independent_eq(&local_point, local);
                global_sum += independent_eq(&projected,
                    h21_role3_wire_geometry(owner, local).unwrap());
            }
        }
        assert_ne!(local_sum, Fr::zero());
        assert_eq!(global_sum, local_sum);
        let mut wrong_bank = projected.clone();
        wrong_bank[13] = Fr::one();
        let mut wrong_sum = Fr::zero();
        for local in 0..8192usize {
            if local == 0 || local % 17 == 0 {
                wrong_sum += independent_eq(&wrong_bank,
                    h21_role3_wire_geometry(owner, local).unwrap());
            }
        }
        assert_eq!(wrong_sum, Fr::zero(), "one fixed bank-coordinate mutant");
        assert_ne!(wrong_sum, local_sum);
    }
}

#[cfg(test)]
mod c369_point_membership_source_tests {
    use super::*;

    const OWNER: usize = POINT_MEMBERSHIP_OWNER;

    fn generator(prefix: u8) -> [u8; 33] {
        let x = "79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798";
        let mut out = [0; 33];
        out[0] = prefix;
        for i in 0..32 {
            out[i + 1] = u8::from_str_radix(&x[2 * i..2 * i + 2], 16).unwrap();
        }
        out
    }

    fn fields(height: usize) -> crate::serializer::Fields {
        crate::serializer::Fields {
            version: 1,
            parent_id: [0; 32],
            ad_proofs_root: [0; 32],
            transactions_root: [0; 32],
            state_root: [0; 33],
            timestamp: 0,
            extension_root: [0; 32],
            n_bits: 0,
            height: height as u32,
            votes: [0; 3],
            pk: generator(2),
            w: generator(3),
            nonce: [0; 8],
            payload_len: 0,
            payload: [0; 255],
        }
    }

    #[test]
    fn c369_point_source_no_frame_bound_geometry_and_mutants() {
        let expected = HeaderSourceBinding::diagnostic_for_test(OWNER);
        let witness = crate::point_membership::witness(generator(2), generator(3)).unwrap();
        let source = NativePointMembershipSourceLease::from_fields(
            expected.clone(), OWNER, &fields(OWNER + 1),
        ).unwrap();
        source.check_binding(&expected).unwrap();
        source.check_author().unwrap();
        let base = OWNER * WIDTH + crate::segment_points::POINT_OFFSET;
        assert_eq!(base, OWNER * WIDTH + 786_432);
        for local in [1, 2, 264, 528] {
            assert_eq!(source.read_point_bit(&expected, base + local).unwrap(), witness[local]);
        }
        assert_eq!(source.read_count_for_test(), 4);
        assert!(source.read_point_bit(&expected, base - 1).unwrap_err()
            .contains("outside point input bytes"));
        assert!(source.read_point_bit(&expected, base).unwrap_err()
            .contains("outside point input bytes"));
        assert!(source.read_point_bit(&expected, base + 529).unwrap_err()
            .contains("outside point input bytes"));
        assert!(source.read_point_bit(&expected, base + 8192).unwrap_err()
            .contains("outside point input bytes"));
        assert_eq!(source.read_count_for_test(), 4);

        for field in 0..6 {
            let mut wrong = NativePointMembershipSourceLease::from_fields(
                expected.clone(), OWNER, &fields(OWNER + 1),
            ).unwrap();
            wrong.mutate_binding_field_for_test(field);
            assert!(wrong.check_binding(&expected).is_err(), "binding field {field}");
        }
        let mut wrong_author = NativePointMembershipSourceLease::from_fields(
            expected.clone(), OWNER, &fields(OWNER + 1),
        ).unwrap();
        wrong_author.wrong_author_mutant_for_test();
        assert!(wrong_author.check_author().is_err());
        assert!(wrong_author.read_point_bit(&expected, base + 1).unwrap_err()
            .contains("author mismatch"));
        assert_eq!(wrong_author.read_count_for_test(), 0);

        let mut wrong_value = NativePointMembershipSourceLease::from_fields(
            expected.clone(), OWNER, &fields(OWNER + 1),
        ).unwrap();
        wrong_value.flip_source_value_for_test(1);
        assert_eq!(wrong_value.read_point_bit(&expected, base + 1).unwrap(), !witness[1]);
    }

    #[test]
    fn c369_point_source_no_frame_producer_rejects_owner_and_noncanonical_plan() {
        let input = super::max_join_tests::bounded_input_n(3);
        let plan = WorkTreeHistoryPlan::compile(
            3, 2, input.root(), input.total_be28(),
        ).unwrap();
        let producer = NativeOwnerProducer::new_for_history(&plan, &input).unwrap();
        for owner in [OWNER - 1, OWNER + 1] {
            let error = producer.point_membership_source_lease(owner).err().unwrap();
            assert!(error.contains("fixed owner"));
        }
        let error = producer.point_membership_source_lease(OWNER).err().unwrap();
        assert!(error.contains("H21 point source geometry differs"));
    }
}

/// Check the source-owned Map assignment after packing. This is a local
/// producer/consumer join over the exact typed imports and physical Map terms;
/// it does not establish a common committed X or any global-U proof.
pub(crate) fn validate_native_bank53_map_consumer(
    plan: &WorkTreeHistoryPlan,
    input: &NativePrefix,
    map: &crate::legacy_envelope_map::Map,
    expected_owner: usize,
    context: usize,
    row: &NativePackedRow,
    foreign_rows: &BTreeMap<usize, NativePackedRow>,
) -> Result<(), String> {
    if context >= BANK53_CONTEXTS {
        return Err("bank53 Map consumer context outside two-context lane".into());
    }
    let binding = map.binding();
    let roster = DaaHistoryRoster::compile(plan)?;
    if row.owner != expected_owner {
        return Err("bank53 Map consumer expected owner mismatch".into());
    }
    let owner = expected_owner;
    if owner >= plan.slots() as usize || row.bytes.len() != OWNER_BYTES {
        return Err("bank53 Map consumer owner or packed row length mismatch".into());
    }
    if row.map_binding.as_ref() != Some(&binding) || row.map_context != Some(context) {
        return Err("bank53 Map consumer binding/context mismatch".into());
    }
    if row.max_binding.is_some()
        || row.root != input.root
        || row.total != input.total
        || row.class != roster.owner_class(owner as u64)?
        || plan.descriptor().root != input.root
        || plan.work_profile().total_be28 != input.total
        || binding.parent_root != Some(plan.descriptor().root)
        || map.n() != plan.headers()
        || map.h() != plan.slot_log()
        || map.slots() != plan.slots() as u64
    {
        return Err("bank53 Map consumer native parent binding mismatch".into());
    }
    #[cfg(test)]
    if row.legacy_binding.is_some() {
        return Err("bank53 Map consumer rejects legacy row".into());
    }

    let lane_start = BANK53_BASE + context * BANK53_CONTEXT_BITS;
    if (BANK53_MAP_LIVE_BITS..BANK53_CONTEXT_BITS).any(|offset| {
        ((row.bytes[(lane_start + offset) / 8] >> ((lane_start + offset) % 8)) & 1) != 0
    }) {
        return Err("bank53 Map consumer Map tail/Score slack is nonzero".into());
    }

    let imports = map.imports(owner as u64)?;
    let required_foreign: BTreeSet<usize> = imports
        .iter()
        .filter(|import| import.owner != owner as u64)
        .map(|import| import.owner as usize)
        .collect();
    if foreign_rows.keys().copied().collect::<BTreeSet<_>>() != required_foreign {
        return Err("bank53 Map consumer foreign owner census mismatch".into());
    }
    let exports = crate::native_owner_exports::NativeExports::new_for_history(plan, input)?;
    for (&source_owner, source_row) in foreign_rows {
        if source_row.owner != source_owner
            || source_row.bytes.len() != OWNER_BYTES
            || source_row.root != input.root
            || source_row.total != input.total
            || source_row.class != roster.owner_class(source_owner as u64)?
            || source_row.max_binding.is_some()
        {
            return Err("bank53 Map consumer foreign row binding mismatch".into());
        }
    }
    for import in &imports {
        let source_bytes = if import.owner == owner as u64 {
            &row.bytes
        } else {
            &foreign_rows
                .get(&(import.owner as usize))
                .ok_or("bank53 Map consumer missing foreign import row")?
                .bytes
        };
        for bit in 0..import.width {
            let index = map.input_index(*import, bit)?;
            let native = exports.bit(index)?;
            let wire = import.local + bit;
            let packed = ((source_bytes[wire / 8] >> (wire % 8)) & 1) != 0;
            if native != packed {
                return Err(format!(
                    "bank53 Map consumer typed import differs from native export owner{} bit{}",
                    import.owner, bit
                ));
            }
        }
    }

    let terms = crate::bank53_map::map_owner_terms(map, owner as u64, context)?;
    let mut value = |index: usize| -> Result<Fr, String> {
        if index >= plan.slots() as usize * WIDTH {
            return Err("bank53 Map consumer input outside native domain".into());
        }
        let source_owner = index / WIDTH;
        let wire = index % WIDTH;
        let typed = imports.iter().any(|import| {
            import.owner == source_owner as u64
                && import.local <= wire
                && wire < import.local + import.width
        });
        let source_bytes = if source_owner == owner {
            if !typed && !(lane_start..lane_start + BANK53_MAP_LIVE_BITS).contains(&wire) {
                return Err("bank53 Map consumer own coordinate outside helpers/imports".into());
            }
            &row.bytes
        } else {
            if !typed {
                return Err("bank53 Map consumer foreign coordinate outside typed imports".into());
            }
            &foreign_rows
                .get(&source_owner)
                .ok_or("bank53 Map consumer missing foreign term row")?
                .bytes
        };
        Ok(Fr::from(((source_bytes[wire / 8] >> (wire % 8)) & 1) as u64))
    };
    let mut sums = BTreeMap::<usize, Fr>::new();
    for term in &terms {
        let gate = &term.gate;
        let mut residual = gate.c0;
        if !gate.c1.is_zero() {
            residual += gate.c1 * value(gate.left)?;
        }
        if !gate.c2.is_zero() {
            residual += gate.c2 * value(gate.right)?;
        }
        if !gate.c3.is_zero() {
            residual += gate.c3 * value(gate.left)? * value(gate.right)?;
        }
        *sums.entry(term.row).or_insert(Fr::zero()) += residual;
    }
    if let Some((term_row, _)) = sums.into_iter().find(|(_, residual)| !residual.is_zero()) {
        return Err(format!("bank53 Map physical residual row{term_row}"));
    }
    Ok(())
}

#[cfg(test)]
fn evaluate_native_map_terms_residuals(
    terms: &[Term],
    mut value: impl FnMut(usize) -> Result<Fr, String>,
) -> Result<Vec<(usize, Fr)>, String> {
    let mut sums = BTreeMap::<usize, Fr>::new();
    for term in terms {
        let gate = &term.gate;
        let mut residual = gate.c0;
        if !gate.c1.is_zero() {
            residual += gate.c1 * value(gate.left)?;
        }
        if !gate.c2.is_zero() {
            residual += gate.c2 * value(gate.right)?;
        }
        if !gate.c3.is_zero() {
            residual += gate.c3 * value(gate.left)? * value(gate.right)?;
        }
        *sums.entry(term.row).or_insert(Fr::zero()) += residual;
    }
    Ok(sums.into_iter().filter(|(_, residual)| !residual.is_zero()).collect())
}

#[cfg(test)]
fn evaluate_native_map1_cut_residuals(
    map: &crate::legacy_envelope_map::Map,
    owner: usize,
    context: usize,
    row: &NativePackedRow,
    foreign_rows: &BTreeMap<usize, NativePackedRow>,
    terms: &[Term],
) -> Result<Vec<(usize, Fr)>, String> {
    if context >= BANK53_CONTEXTS || row.owner != owner || row.bytes.len() != OWNER_BYTES {
        return Err("c149 Map1 residual owner/context/row mismatch".into());
    }
    let imports = map.imports(owner as u64)?;
    let required_foreign: BTreeSet<usize> = imports
        .iter()
        .filter(|import| import.owner != owner as u64)
        .map(|import| import.owner as usize)
        .collect();
    if foreign_rows.keys().copied().collect::<BTreeSet<_>>() != required_foreign {
        return Err("c149 Map1 residual foreign owner census mismatch".into());
    }
    let lane_start = BANK53_BASE + context * BANK53_CONTEXT_BITS;
    evaluate_native_map_terms_residuals(terms, |index| {
        if index >= map.slots() as usize * WIDTH {
            return Err("c149 Map1 residual input outside native domain".into());
        }
        let source_owner = index / WIDTH;
        let wire = index % WIDTH;
        let typed = imports.iter().any(|import| {
            import.owner == source_owner as u64
                && import.local <= wire
                && wire < import.local + import.width
        });
        let source = if source_owner == owner {
            if !typed && !(lane_start..lane_start + BANK53_MAP_LIVE_BITS).contains(&wire) {
                return Err("c149 Map1 residual own coordinate outside helpers/imports".into());
            }
            &row.bytes
        } else {
            if !typed {
                return Err("c149 Map1 residual foreign coordinate outside typed imports".into());
            }
            &foreign_rows
                .get(&source_owner)
                .ok_or("c149 Map1 residual missing typed foreign row")?
                .bytes
        };
        Ok(Fr::from(((source[wire / 8] >> (wire % 8)) & 1) as u64))
    })
}

/// Separate c149 consumer for the rootless c146 Map1 cut. The row and typed
/// imports are rebound to the exact full parent prefix at every call; this
/// leaves the root-bound full-parent consumer above unchanged.
#[cfg(test)]
pub(crate) fn validate_native_map1_cut_consumer_for_test(
    plan: &WorkTreeHistoryPlan,
    input: &NativePrefix,
    map: &crate::legacy_envelope_map::Map,
    approved_binding: &crate::legacy_envelope_map::Binding,
    row: &NativePackedRow,
    foreign_rows: &BTreeMap<usize, NativePackedRow>,
) -> Result<(), String> {
    const OWNER: usize = 844_670;
    const CONTEXT: usize = 1;
    validate_native_plan_input(plan, input)?;
    if plan.descriptor().root != input.root || plan.work_profile().total_be28 != input.total {
        return Err("c149 Map1 cut consumer plan/prefix identity mismatch".into());
    }
    validate_h21_map1_cut_gate_for_test(plan, map, OWNER, CONTEXT, approved_binding)?;
    let roster = DaaHistoryRoster::compile(plan)?;
    if row.owner != OWNER
        || row.bytes.len() != OWNER_BYTES
        || row.class != roster.owner_class(OWNER as u64)?
        || row.root != input.root
        || row.total != input.total
        || row.map_binding.as_ref() != Some(approved_binding)
        || row.map_context != Some(CONTEXT)
        || row.max_binding.is_some()
    {
        return Err("c149 Map1 cut consumer row identity/class mismatch".into());
    }
    #[cfg(test)]
    if row.legacy_binding.is_some() {
        return Err("c149 Map1 cut consumer rejects legacy row".into());
    }

    let lane_start = BANK53_BASE + CONTEXT * BANK53_CONTEXT_BITS;
    if (BANK53_MAP_LIVE_BITS..BANK53_CONTEXT_BITS).any(|offset| {
        ((row.bytes[(lane_start + offset) / 8] >> ((lane_start + offset) % 8)) & 1) != 0
    }) {
        return Err("c149 Map1 cut consumer tail/slack is nonzero".into());
    }
    let imports = map.imports(OWNER as u64)?;
    let required_foreign: BTreeSet<usize> = imports
        .iter()
        .filter(|import| import.owner != OWNER as u64)
        .map(|import| import.owner as usize)
        .collect();
    if foreign_rows.keys().copied().collect::<BTreeSet<_>>() != required_foreign {
        return Err("c149 Map1 cut consumer foreign owner census mismatch".into());
    }
    let exports = crate::native_owner_exports::NativeExports::new_for_history(plan, input)?;
    for (&source_owner, source_row) in foreign_rows {
        if source_row.owner != source_owner
            || source_row.bytes.len() != OWNER_BYTES
            || source_row.class != roster.owner_class(source_owner as u64)?
            || source_row.root != input.root
            || source_row.total != input.total
            || source_row.max_binding.is_some()
        {
            return Err("c149 Map1 cut consumer foreign row identity/class mismatch".into());
        }
    }
    let mut inputs = crate::legacy_envelope_map::Inputs::default();
    for import in &imports {
        let mut value = num_bigint::BigInt::from(0u8);
        let source_bytes = if import.owner == OWNER as u64 {
            &row.bytes
        } else {
            &foreign_rows
                .get(&(import.owner as usize))
                .ok_or("c149 Map1 cut consumer missing import row")?
                .bytes
        };
        for bit in 0..import.width {
            let index = map.input_index(*import, bit)?;
            let native = exports.bit(index)?;
            let wire = import.local + bit;
            let packed = ((source_bytes[wire / 8] >> (wire % 8)) & 1) != 0;
            if native != packed {
                return Err(format!(
                    "c149 Map1 cut consumer import differs from native export owner{} bit{}",
                    import.owner, bit
                ));
            }
            if native {
                value += num_bigint::BigInt::from(1u8) << bit;
            }
        }
        inputs.put(map, *import, &value)?;
    }
    let generated = map.generate(OWNER as u64, &inputs)?;
    map.check_row(&generated)?;
    if generated.binding != *approved_binding || generated.bits.len() != crate::legacy_envelope_map::BANK {
        return Err("c149 Map1 cut consumer generated row binding/width mismatch".into());
    }
    for (offset, expected) in generated.bits.iter().enumerate() {
        let wire = lane_start + offset;
        let packed = ((row.bytes[wire / 8] >> (wire % 8)) & 1) != 0;
        if packed != *expected {
            return Err(format!("c149 Map1 cut consumer packed Map bit mismatch at {offset}"));
        }
    }
    let terms = crate::bank53_map::map_owner_terms(map, OWNER as u64, CONTEXT)?;
    let residuals = evaluate_native_map1_cut_residuals(
        map,
        OWNER,
        CONTEXT,
        row,
        foreign_rows,
        &terms,
    )?;
    if let Some((term_row, _)) = residuals.first() {
        return Err(format!("c149 Map1 cut physical residual row{term_row}"));
    }
    Ok(())
}

#[cfg(test)]
mod candidate149_map1_cut_gate_tests {
    use super::*;
    use crate::legacy_envelope_map::{LowerBranch, LowerSelector, LowerSource, Map};

    fn selector() -> LowerSelector {
        LowerSelector {
            source: LowerSource::HeaderDifficulty { height: 841_729 },
            branch: LowerBranch::Pivot(54),
        }
    }

    #[test]
    fn c149_map1_cut_gate_is_exact_and_distinct_from_full_parent_map() {
        let parent = WorkTreeHistoryPlan::compile(
            1_827_840, 21, [0x91; 32], [0x92; 28],
        ).unwrap();
        let cut = Map::new_modern_global_u_selected_lower(1_827_775, 21, 55, selector()).unwrap();
        let approved = cut.binding();
        assert!(approved.parent_root.is_none());
        validate_h21_map1_cut_gate_for_test(&parent, &cut, 844_670, 1, &approved).unwrap();

        let wrong_cut = Map::new_modern_global_u_selected_lower(1_827_774, 21, 55, selector()).unwrap();
        assert!(validate_h21_map1_cut_gate_for_test(&parent, &wrong_cut, 844_670, 1, &approved).is_err());
        assert!(validate_h21_map1_cut_gate_for_test(&parent, &cut, 844_670, 0, &approved).is_err());
        assert!(validate_h21_map1_cut_gate_for_test(&parent, &cut, 844_671, 1, &approved).is_err());

        let wrong_exponent = Map::new_modern_global_u_selected_lower(1_827_775, 21, 54, selector()).unwrap();
        assert!(validate_h21_map1_cut_gate_for_test(&parent, &wrong_exponent, 844_670, 1, &approved).is_err());
        let wrong_selector = Map::new_modern_global_u_selected_lower(
            1_827_775,
            21,
            55,
            LowerSelector { branch: LowerBranch::Pivot(52), ..selector() },
        ).unwrap();
        assert!(validate_h21_map1_cut_gate_for_test(&parent, &wrong_selector, 844_670, 1, &approved).is_err());
        let wrong_approval = wrong_selector.binding();
        assert!(validate_h21_map1_cut_gate_for_test(&parent, &cut, 844_670, 1, &wrong_approval).is_err());
        let wrong_lower_source = Map::new_modern_global_u_selected_lower(
            1_827_775,
            21,
            55,
            LowerSelector {
                source: LowerSource::HeaderDifficulty { height: 841_728 },
                branch: LowerBranch::Pivot(54),
            },
        ).unwrap();
        assert!(validate_h21_map1_cut_gate_for_test(
            &parent,
            &wrong_lower_source,
            844_670,
            1,
            &approved,
        ).is_err());

        let other_parent = WorkTreeHistoryPlan::compile(
            1_827_775, 21, [0x93; 32], [0x94; 28],
        ).unwrap();
        let rooted_cut = Map::from_parent_modern_global_u(&other_parent, 55, selector()).unwrap();
        assert!(rooted_cut.binding().parent_root.is_some());
        assert!(validate_h21_map1_cut_gate_for_test(&parent, &rooted_cut, 844_670, 1, &approved).is_err());

        let full_parent = Map::from_parent_modern_global_u(&parent, 55, selector()).unwrap();
        assert_eq!(full_parent.binding().parent_root, Some(parent.descriptor().root));
        assert_ne!(full_parent.binding(), cut.binding());
    }

    #[test]
    fn c149_map1_residual_evaluator_rejects_one_live_output_bit_mutant() {
        const OWNER: usize = 844_670;
        const CONTEXT: usize = 1;
        let plan = WorkTreeHistoryPlan::compile(
            1_827_840, 21, [0x95; 32], [0x96; 28],
        ).unwrap();
        let map = Map::new_modern_global_u_selected_lower(
            1_827_775, 21, 55, selector(),
        ).unwrap();
        let imports = map.imports(OWNER as u64).unwrap();
        assert_eq!(imports.len(), 1, "owner844670 has only its D import");
        assert_eq!(imports[0].owner, OWNER as u64);
        assert_eq!(imports[0].local, crate::legacy_envelope_map::D_LOCAL);
        assert_eq!(imports[0].width, 224);
        assert_eq!(imports[0].kind, crate::legacy_envelope_map::Kind::Difficulty);

        let mut inputs = crate::legacy_envelope_map::Inputs::default();
        inputs.put(&map, imports[0], &num_bigint::BigInt::from(1u8)).unwrap();
        let generated = map.generate(OWNER as u64, &inputs).unwrap();
        map.check_row(&generated).unwrap();
        assert!(generated.bits[BANK53_MAP_LIVE_BITS..].iter().all(|bit| !bit));

        let mut bytes = vec![0u8; OWNER_BYTES];
        let d_wire = crate::legacy_envelope_map::D_LOCAL;
        bytes[d_wire / 8] |= 1 << (d_wire % 8);
        let lane_start = BANK53_BASE + CONTEXT * BANK53_CONTEXT_BITS;
        for (offset, bit) in generated.bits[..BANK53_MAP_LIVE_BITS].iter().enumerate() {
            if *bit {
                let wire = lane_start + offset;
                bytes[wire / 8] |= 1 << (wire % 8);
            }
        }
        let row = NativePackedRow {
            owner: OWNER,
            class: DaaHistoryRoster::compile(&plan).unwrap().owner_class(OWNER as u64).unwrap(),
            root: plan.descriptor().root,
            total: plan.work_profile().total_be28,
            bytes,
            header_source_binding: None,
            cap0_source: None,
            cap1_source: None,
            max_binding: None,
            map_binding: Some(map.binding()),
            map_context: Some(CONTEXT),
            legacy_binding: None,
        };
        let foreign = BTreeMap::new();
        let terms = crate::bank53_map::map_owner_terms(&map, OWNER as u64, CONTEXT).unwrap();
        assert!(!terms.is_empty());
        assert!(evaluate_native_map1_cut_residuals(
            &map, OWNER, CONTEXT, &row, &foreign, &terms,
        ).unwrap().is_empty(), "generated Map bits must satisfy emitted ROW terms");

        let mut mutant = row.clone();
        let lane_wire = lane_start + 672;
        mutant.bytes[lane_wire / 8] ^= 1 << (lane_wire % 8);
        let mutant_index = OWNER * WIDTH + lane_wire;
        let touched_rows: BTreeSet<usize> = terms
            .iter()
            .filter(|term| {
                let gate = &term.gate;
                gate.c1 != Fr::zero() && gate.left == mutant_index
                    || gate.c2 != Fr::zero() && gate.right == mutant_index
                    || gate.c3 != Fr::zero()
                        && (gate.left == mutant_index || gate.right == mutant_index)
            })
            .map(|term| term.row)
            .collect();
        assert!(!touched_rows.is_empty(), "mutated live bit must feed emitted Map ROW terms");
        let residuals = evaluate_native_map1_cut_residuals(
            &map, OWNER, CONTEXT, &mutant, &foreign, &terms,
        ).unwrap();
        assert!(
            residuals.iter().any(|(row, residual)| touched_rows.contains(row) && !residual.is_zero()),
            "live output mutation must produce a nonzero residual on a touched ROW"
        );
    }
}

#[cfg(test)]
pub(crate) use bank53_writer_tests::{same_x_stage1b_n1984_fixture, SameXStage1bFixture};

#[cfg(test)]
mod bank53_writer_tests {
    use super::*;
    use crate::bank53_map::map_owner_terms;
    use crate::legacy_envelope_map::{Inputs as MapInputs, Map, D_LOCAL, T_LOCAL};
    use num_bigint::BigInt;

    fn small_input_and_plan(n: usize) -> (NativePrefix, WorkTreeHistoryPlan) {
        assert!(matches!(n, 3 | 4));
        let input = super::max_join_tests::bounded_input_n(n);
        let plan = WorkTreeHistoryPlan::compile(
            n as u64,
            2,
            input.root(),
            input.total_be28(),
        )
        .unwrap();
        (input, plan)
    }

    #[test]
    fn c440_owner0_map_slack_physical_join_no_frame() {
        use crate::daa_history_roster::OwnerClass;
        let owner = 0usize;
        let class = OwnerClass::Genesis;
        let (binding, bundle) = Eligible08MapSlackBundle::synthetic_for_test(owner, class)
            .expect("structural Map+Slack source fixture");
        let mask = vec![false; WIDTH];
        let mut native = vec![Fr::zero(); WIDTH];
        let reserved = preflight_map_slack_reservation(
            &bundle, &binding, owner, class, &mask, &native,
        ).expect("exact Map+Slack HEADER retirement");
        assert_eq!(reserved.iter().filter(|bit| **bit).count(),
            BANK53_CONTEXTS * (BANK53_MAP_LIVE_BITS + BANK53_SLACK_BITS));
        let map_only = preflight_map_pair_reservation(
            bundle.map_lease(), &binding, owner, class, &mask,
        ).unwrap();
        assert_eq!(map_only.iter().filter(|bit| **bit).count(),
            BANK53_CONTEXTS * BANK53_MAP_LIVE_BITS);
        for context in 0..BANK53_CONTEXTS {
            let start = BANK53_BASE + context * BANK53_CONTEXT_BITS;
            let score = start + BANK53_MAP_LIVE_BITS;
            let slack = score + crate::origin_score::INPUT;
            assert!(reserved[start] && reserved[score - 1]);
            assert!(!reserved[score] && !reserved[slack - 1]);
            assert!(reserved[slack] && reserved[slack + BANK53_SLACK_BITS - 1]);
            assert!(!map_only[slack], "Map-only path leaves required Slack source absent");
            assert_eq!(bundle.checked_slack_terms(&binding, owner, class, context).unwrap(),
                crate::bank53_slack::slack_zero_terms(owner, context).unwrap());
        }

        let mut rows = OwnedRows::new(OwnerSelection::Single { owner, class });
        for context in 0..BANK53_CONTEXTS {
            let score = BANK53_BASE + context * BANK53_CONTEXT_BITS + BANK53_MAP_LIVE_BITS;
            for local in score..score + crate::origin_score::INPUT {
                rows.claim(owner, local, Fr::zero()).unwrap();
            }
        }
        claim_map_slack_live(&mut rows, &bundle, &binding, owner, class).unwrap();
        require_map_slack_claim_census(&rows, &bundle, &binding, owner, class).unwrap();
        let mut packed = rows.bytes(0).unwrap();
        require_map_slack_packed(&packed, &bundle, &binding, owner, class).unwrap();
        for (local, name) in [
            (BANK53_BASE, "Map"),
            (BANK53_BASE + BANK53_MAP_LIVE_BITS + crate::origin_score::INPUT, "Slack"),
        ] {
            packed[local / 8] ^= 1 << (local % 8);
            assert!(require_map_slack_packed(&packed, &bundle, &binding, owner, class)
                .unwrap_err().contains(name));
            packed[local / 8] ^= 1 << (local % 8);
        }
        let first_slack = BANK53_BASE + BANK53_MAP_LIVE_BITS + crate::origin_score::INPUT;
        let mut omitted = rows;
        omitted.claimed[0][first_slack] = false;
        assert!(require_map_slack_claim_census(&omitted, &bundle, &binding, owner, class)
            .unwrap_err().contains("missing or changed"));

        for prior in [BANK53_BASE, first_slack] {
            let mut overlap = OwnedRows::new(OwnerSelection::Single { owner, class });
            overlap.claim_exclusive(owner, prior, Fr::zero()).unwrap();
            let before_claimed = overlap.claimed[0].clone();
            let before_values = overlap.values[0].clone();
            let error = claim_map_slack_live(&mut overlap, &bundle, &binding, owner, class)
                .unwrap_err();
            assert!(error.contains("overlaps"), "{error}");
            assert_eq!(overlap.claimed[0], before_claimed);
            assert_eq!(overlap.values[0], before_values);
        }
        for local in [BANK53_BASE, first_slack, BANK53_BASE + BANK53_MAP_LIVE_BITS] {
            let mut wrong = mask.clone();
            wrong[local] = true;
            assert!(preflight_map_slack_reservation(
                &bundle, &binding, owner, class, &wrong, &native,
            ).is_err(), "masked source local{local}");
        }
        let score = BANK53_BASE + BANK53_MAP_LIVE_BITS;
        native[score] = Fr::one();
        assert!(preflight_map_slack_reservation(
            &bundle, &binding, owner, class, &mask, &native,
        ).unwrap_err().contains("HEADER zero"));
        for field in 0..4 {
            let wrong_binding = binding.mutated_field_for_test(field);
            assert!(bundle.checked_slack_cells(&wrong_binding, owner, class).is_err(),
                "wrong parent/profile/cut binding field {field}");
        }
        assert!(bundle.checked_slack_terms(&binding, owner, class, 2).is_err());
        let (_, mut missing) = Eligible08MapSlackBundle::synthetic_for_test(owner, class).unwrap();
        missing.remove_slack_bit_for_test(0, 0).unwrap();
        assert!(preflight_map_slack_reservation(
            &missing, &binding, owner, class, &mask, &vec![Fr::zero(); WIDTH],
        ).is_err(), "one absent Slack zero cell");
        let (_, mut nonzero) = Eligible08MapSlackBundle::synthetic_for_test(owner, class).unwrap();
        nonzero.set_slack_bit_for_test(1, 386, true).unwrap();
        assert!(nonzero.checked_slack_cells(&binding, owner, class).is_err(),
            "nonzero Slack source");
        let (_, mut wrong_term) = Eligible08MapSlackBundle::synthetic_for_test(owner, class).unwrap();
        wrong_term.alter_slack_row_term_for_test(0, 0).unwrap();
        assert!(wrong_term.checked_slack_terms(&binding, owner, class, 0).is_err(),
            "noncanonical zero ROW term");
        let (_, mut swapped) = Eligible08MapSlackBundle::synthetic_for_test(owner, class).unwrap();
        swapped.swap_slack_contexts_for_test();
        assert!(swapped.checked_slack_cells(&binding, owner, class).is_err(),
            "wrong Slack context");
        let (_, mut changed_map) = Eligible08MapSlackBundle::synthetic_for_test(owner, class).unwrap();
        changed_map.mutate_map_cell_value_for_test(0).unwrap();
        assert!(changed_map.checked_slack_cells(&binding, owner, class).is_err(),
            "changed Map value must invalidate the combined source");
        for special in [FIRST_MODERN_CAP0_OWNER, 845_887] {
            assert!(preflight_map_slack_reservation(
                &bundle, &binding, special, class, &mask, &vec![Fr::zero(); WIDTH],
            ).unwrap_err().contains("special owner"));
        }
        assert!(preflight_map_slack_reservation(
            &bundle, &binding, 417_790, class, &mask, &vec![Fr::zero(); WIDTH],
        ).unwrap_err().contains("only authorizes proven Genesis owner0"));
        println!("C440_OWNER0_MAP_SLACK_NO_FRAME_PASS owner=0 contexts=2 exact_cells=12288 score_header_zero=true equal_zero_overlap_rejected=true frame=false proof=false client=false");
    }

    #[test]
    fn c441_owner417790_first_score_anchor_physical_join_no_frame() {
        use crate::daa_history_roster::OwnerClass;

        let owner = 417_790usize;
        let class = OwnerClass::Carry;
        let (binding, bundle) = Eligible08MapSlackAnchorBundle::synthetic_for_test()
            .expect("synthetic [55,55] first-anchor source fixture");
        let mask = vec![false; WIDTH];
        let reserved = preflight_map_slack_anchor_reservation(
            &bundle, &binding, owner, class, &mask,
        ).expect("complete Map+Score0/1+Slack HEADER reservation");
        assert_eq!(reserved.iter().filter(|bit| **bit).count(),
            BANK53_CONTEXTS * BANK53_CONTEXT_BITS);
        let mut masked_score = mask.clone();
        masked_score[BANK53_BASE + BANK53_MAP_LIVE_BITS] = true;
        assert!(preflight_map_slack_anchor_reservation(
            &bundle, &binding, owner, class, &masked_score,
        ).unwrap_err().contains("reservation overlap"),
            "a Score-local HEADER replacement bit rejects the complete reservation");
        for context in 0..BANK53_CONTEXTS {
            let start = BANK53_BASE + context * BANK53_CONTEXT_BITS;
            let score = start + BANK53_MAP_LIVE_BITS;
            let slack = score + crate::origin_score::INPUT;
            assert!(reserved[start] && reserved[start + BANK53_MAP_LIVE_BITS - 1]);
            assert!(reserved[score] && reserved[score + crate::origin_score::INPUT - 1]);
            assert!(reserved[slack] && reserved[slack + BANK53_SLACK_BITS - 1]);
            assert!(!bundle.checked_score_terms(&binding, owner, class, context)
                .unwrap().is_empty());
        }

        let mut rows = OwnedRows::new(OwnerSelection::Single { owner, class });
        claim_map_slack_anchor_live(&mut rows, &bundle, &binding, owner, class).unwrap();
        require_map_slack_anchor_claim_census(&rows, &bundle, &binding, owner, class).unwrap();
        assert_eq!(rows.claimed[0].iter().filter(|claimed| **claimed).count(),
            BANK53_CONTEXTS * BANK53_CONTEXT_BITS,
            "the source claims exactly the complete two-context Bank53 partition");
        let first_score = BANK53_BASE + BANK53_MAP_LIVE_BITS;
        let mut omitted = OwnedRows::new(OwnerSelection::Single { owner, class });
        claim_map_slack_anchor_live(&mut omitted, &bundle, &binding, owner, class).unwrap();
        omitted.claimed[0][first_score] = false;
        assert!(require_map_slack_anchor_claim_census(&omitted, &bundle, &binding, owner, class)
            .unwrap_err().contains("missing or changed"),
            "an omitted zero-valued Score claim is detected");
        let packed = rows.bytes(0).unwrap();
        require_map_slack_anchor_packed(&packed, &bundle, &binding, owner, class).unwrap();

        // All source-local negative cases use the same synthetic fixture API;
        // no authentic Upper publication or proof is asserted by this test.
        for context in 0..BANK53_CONTEXTS {
            let mut missing_score = bundle.clone();
            missing_score.remove_score_bit_for_test(context, 0).unwrap();
            assert!(missing_score.checked_score_cells(&binding, owner, class).is_err(),
                "missing Score bit in context{context}");

            let mut flipped_score = bundle.clone();
            flipped_score.flip_score_bit_for_test(context, 0).unwrap();
            assert!(flipped_score.checked_score_cells(&binding, owner, class).is_err(),
                "changed Score bit in context{context}");

            let mut wrong_term = bundle.clone();
            wrong_term.alter_score_term_for_test(context, 0).unwrap();
            assert!(wrong_term.checked_score_terms(&binding, owner, class, context).is_err(),
                "noncanonical Score term in context{context}");
        }

        let mut swapped = bundle.clone();
        swapped.swap_score_contexts_for_test();
        assert!(swapped.checked_score_cells(&binding, owner, class).is_err(),
            "swapped Score contexts");

        let mut changed_map = bundle.clone();
        changed_map.map_slack_mut_for_test().mutate_map_cell_value_for_test(0).unwrap();
        assert!(changed_map.checked_score_cells(&binding, owner, class).is_err(),
            "changed Map cell invalidates Score source");

        let mut swapped_maps = bundle.clone();
        swapped_maps.swap_score_maps_for_test();
        assert!(swapped_maps.checked_score_cells(&binding, owner, class).is_err(),
            "swapped retained Map contexts invalidate Score replay");

        for upper_mutation in 0..5 {
            let mut wrong_upper = bundle.clone();
            wrong_upper.mutate_upper_for_test(upper_mutation).unwrap();
            assert!(wrong_upper.checked_score_cells(&binding, owner, class).is_err(),
                "Upper mutation kind {upper_mutation}");
        }

        let mut overlap = OwnedRows::new(OwnerSelection::Single { owner, class });
        overlap.claim_exclusive(owner, first_score, Fr::zero()).unwrap();
        let before_claimed = overlap.claimed[0].clone();
        let before_values = overlap.values[0].clone();
        let error = claim_map_slack_anchor_live(&mut overlap, &bundle, &binding, owner, class)
            .unwrap_err();
        assert!(error.contains("overlap"), "{error}");
        assert_eq!(overlap.claimed[0], before_claimed);
        assert_eq!(overlap.values[0], before_values);

        assert!(preflight_map_slack_anchor_reservation(
            &bundle, &binding, 417_789, OwnerClass::Carry, &mask,
        ).is_err(), "wrong owner");
        assert!(preflight_map_slack_anchor_reservation(
            &bundle, &binding, owner, OwnerClass::Genesis, &mask,
        ).is_err(), "wrong owner class");
        let (_, map_slack_only) = Eligible08MapSlackBundle::synthetic_for_test(owner, class).unwrap();
        assert!(preflight_map_slack_reservation(
            &map_slack_only, &binding, owner, class, &mask, &vec![Fr::zero(); WIDTH],
        ).unwrap_err().contains("only authorizes proven Genesis owner0"),
            "C440 PairSlack cannot stand in for the ScoreAnchor owner");

        let (owner0_binding, owner0_bundle) = Eligible08MapSlackBundle::synthetic_for_test(
            0, OwnerClass::Genesis,
        ).unwrap();
        for rejected_owner in [417_790usize, 845_758usize] {
            assert!(preflight_map_slack_reservation(
                &owner0_bundle, &owner0_binding, rejected_owner, OwnerClass::Carry,
                &mask, &vec![Fr::zero(); WIDTH],
            ).unwrap_err().contains("only authorizes proven Genesis owner0"),
                "C440 owner-0 Map+Slack path rejects owner{rejected_owner}");
        }
        println!("C441_OWNER417790_FIRST_SCORE_ANCHOR_NO_FRAME_PASS owner=417790 class=Carry contexts=2 reserved_claimed_packed_cells=16384 upper_mutants=5 frame=false authentic_source=false proof=false client=false");
    }

    #[test]
    fn c140_bank53_map_metadata_gate_isolates_identity_fields() {
        let (input, plan) = small_input_and_plan(3);
        let map = Map::from_parent(&plan, 64).unwrap();
        // Metadata fixture only; zero packed bytes do not assert row validity.
        let row = NativePackedRow {
            owner: 0, class: crate::daa_history_roster::OwnerClass::Genesis,
            root: input.root(), total: input.total_be28(), bytes: vec![0; OWNER_BYTES],
            header_source_binding: None,
            cap0_source: None,
            cap1_source: None,
            max_binding: None, map_binding: Some(map.binding()), map_context: Some(0),
            legacy_binding: None,
        };
        row.validate_bank53_map_identity_for_history_test(&plan, &map, 0, 0).unwrap();
        let check = |candidate: &NativePackedRow| {
            assert!(candidate.validate_bank53_map_identity_for_history_test(&plan, &map, 0, 0)
                .unwrap_err().contains("identity/binding/context"));
        };
        let mut wrong = row.clone(); wrong.owner = 1; check(&wrong);
        let mut wrong = row.clone(); wrong.root[0] ^= 1; check(&wrong);
        let mut wrong = row.clone(); wrong.total[0] ^= 1; check(&wrong);
        let mut wrong = row.clone(); wrong.map_context = Some(1); check(&wrong);
        let mut wrong = row.clone(); wrong.map_binding = None; check(&wrong);
        let mut wrong = row.clone(); wrong.bytes.pop(); check(&wrong);
        let mut wrong = row.clone(); wrong.max_binding = Some([0; 32]); check(&wrong);
        let mut wrong = row.clone(); wrong.legacy_binding = Some([0; 32]); check(&wrong);
        let other_map = Map::from_parent(&plan, 63).unwrap();
        assert!(row.validate_bank53_map_identity_for_history_test(&plan, &other_map, 0, 0).is_err());
        assert!(row.validate_bank53_map_identity_for_history_test(&plan, &map, 0, 1).is_err());
        assert!(row.validate_bank53_map_identity_for_history_test(&plan, &map, 1, 0).is_err());
    }

    fn witness(owner: usize, context: usize) -> Bank53TestWitness {
        let mut values = vec![Fr::zero(); BANK53_TEST_CONTEXT_BITS];
        values[0] = Fr::one();
        values[127] = Fr::one();
        Bank53TestWitness::new(owner, context, values)
    }

    fn bit(bytes: &[u8], wire: usize) -> bool {
        ((bytes[wire / 8] >> (wire % 8)) & 1) != 0
    }

    fn rejected(result: Result<NativePackedRow, String>) -> String {
        result.err().expect("bank53 test writer should reject this fixture")
    }

    fn map_inputs_from_native(
        map: &Map,
        exports: &crate::native_owner_exports::NativeExports<'_>,
        owner: usize,
    ) -> Result<MapInputs, String> {
        let mut inputs = MapInputs::default();
        for imp in map.imports(owner as u64)? {
            let mut value = BigInt::from(0);
            for bit in 0..imp.width {
                if exports.bit(map.input_index(imp, bit)?)? {
                    value += BigInt::from(1) << bit;
                }
            }
            inputs.put(map, imp, &value)?;
        }
        Ok(inputs)
    }

    // The Stage1b test may consume only these three source-owned rows and the
    // original physical Map terms. This is a fixture bridge, not a verifier API.
    pub(crate) struct SameXStage1bFixture {
        pub root: [u8; 32],
        pub total: [u8; 28],
        pub q1: u64,
        pub owner_slices: [Vec<u8>; 3],
        pub original_map_terms: Vec<Term>,
    }

    pub(crate) fn same_x_stage1b_n1984_fixture() -> Result<SameXStage1bFixture, String> {
        use crate::legacy_envelope_map::{LowerBranch, LowerSelector, LowerSource, SMAX};

        const OWNER: usize = 1983;
        let input = super::max_join_tests::bounded_input_n(1984);
        let plan = WorkTreeHistoryPlan::compile(
            1984, 11, input.root(), input.total_be28(),
        )?;
        let producer = NativeOwnerProducer::new_for_history(&plan, &input)?;

        let legacy_map = Map::from_parent(&plan, 64)?;
        let legacy_inputs = map_inputs_from_native(&legacy_map, &producer.exports, OWNER)?;
        let legacy_row = legacy_map.generate(OWNER as u64, &legacy_inputs)?;
        let q1 = (0..92).fold(BigUint::from(0u8), |mut value, bit_index| {
            if legacy_row.bits[SMAX - crate::legacy_envelope_map::BASE + bit_index] {
                value += BigUint::from(1u8) << bit_index;
            }
            value
        });
        if q1 != BigUint::from(STAGE0_Q1) {
            return Err("Stage1b N1984 q1 differs from frozen native prefix".into());
        }

        let map = Map::from_parent_modern_global_u(
            &plan,
            47,
            LowerSelector {
                source: LowerSource::Reset417792,
                branch: LowerBranch::Literal,
            },
        )?;
        let context = 0usize;
        let own_row = producer.produce_bank53_map(OWNER, &map, context)?;
        let mut foreign = BTreeMap::new();
        foreign.insert(1023usize, producer.produce(1023)?);
        foreign.insert(1982usize, producer.produce(1982)?);
        validate_native_bank53_map_consumer(
            &plan, &input, &map, OWNER, context, &own_row, &foreign,
        )?;
        let owner_slices = [
            foreign[&1023].packed_bytes().to_vec(),
            foreign[&1982].packed_bytes().to_vec(),
            own_row.packed_bytes().to_vec(),
        ];
        if owner_slices.iter().any(|slice| slice.len() != OWNER_BYTES) {
            return Err("Stage1b N1984 source owner slice length".into());
        }
        Ok(SameXStage1bFixture {
            root: input.root(),
            total: input.total_be28(),
            q1: STAGE0_Q1,
            owner_slices,
            original_map_terms: map_owner_terms(&map, OWNER as u64, context)?,
        })
    }

    #[test]
    #[ignore = "explicit N1984 Stage1b source-profile discovery only"]
    fn bank53_same_x_stage1b_n1984_public_profile_discovery() {
        let fixture = same_x_stage1b_n1984_fixture().unwrap();
        let hex = |bytes: &[u8]| bytes.iter().map(|byte| format!("{byte:02X}")).collect::<String>();
        println!("STAGE1B_PUBLIC root={}", hex(&fixture.root));
        println!("STAGE1B_PUBLIC total={}", hex(&fixture.total));
        println!("STAGE1B_PUBLIC q1={}", fixture.q1);
        println!("STAGE1B_PUBLIC bundle_blake2b256=8CDB90DA475E646280113D97C9469BE7EB86A1D04F20404C64239187284FC009");
        println!("STAGE1B_PUBLIC owner_order=1023,1982,1983 map_terms={}", fixture.original_map_terms.len());
    }

    fn physical_map_failures(
        map: &Map,
        plan: &WorkTreeHistoryPlan,
        input: &NativePrefix,
        owner: usize,
        context: usize,
        row: &NativePackedRow,
        terms: &[Term],
        foreign_rows: &BTreeMap<usize, NativePackedRow>,
    ) -> Result<Vec<(usize, Fr)>, String> {
        if row.owner != owner || row.bytes.len() != OWNER_BYTES {
            return Err("bank53 Map physical owner or row length mismatch".into());
        }
        let roster = DaaHistoryRoster::compile(plan)?;
        if row.root != input.root || row.total != input.total
            || map.binding().parent_root != Some(plan.descriptor().root)
            || plan.descriptor().root != input.root
            || plan.work_profile().total_be28 != input.total
            || map.n() != plan.headers() || map.h() != plan.slot_log()
            || row.class != roster.owner_class(owner as u64)?
        {
            return Err("bank53 Map native parent binding mismatch".into());
        }
        if context >= BANK53_TEST_CONTEXTS {
            return Err("bank53 Map physical context outside test lanes".into());
        }
        let imports = map.imports(owner as u64)?;
        let required_foreign: BTreeSet<usize> = imports.iter()
            .filter(|imp| imp.owner != owner as u64)
            .map(|imp| imp.owner as usize).collect();
        if foreign_rows.keys().copied().collect::<BTreeSet<_>>() != required_foreign {
            return Err("bank53 Map physical foreign owner census mismatch".into());
        }
        for (&source_owner, source_row) in foreign_rows {
            if source_row.owner != source_owner || source_row.bytes.len() != OWNER_BYTES
                || source_row.root != input.root || source_row.total != input.total
                || source_row.class != roster.owner_class(source_owner as u64)?
            {
                return Err("bank53 Map physical foreign row binding mismatch".into());
            }
        }
        let selected = BANK53_TEST_BASE + context * BANK53_TEST_CONTEXT_BITS;
        let mut value = |index: usize| -> Result<Fr, String> {
            if index >= plan.slots() * WIDTH {
                return Err("bank53 Map input outside native domain".into());
            }
            let source_owner = index / WIDTH;
            let wire = index % WIDTH;
            let typed = imports.iter().any(|imp| imp.owner == source_owner as u64
                && imp.local <= wire && wire < imp.local + imp.width);
            let source_bit = if source_owner == owner {
                if !typed && !(selected..selected + 5_757).contains(&wire) {
                    return Err("bank53 Map own coordinate outside helpers/imports".into());
                }
                bit(row.packed_bytes(), wire)
            } else {
                if !typed {
                    return Err("bank53 Map foreign coordinate outside typed imports".into());
                }
                let source = foreign_rows.get(&source_owner)
                    .ok_or("bank53 Map missing physical foreign row")?;
                bit(source.packed_bytes(), wire)
            };
            Ok(Fr::from(source_bit as u64))
        };
        let mut sums = BTreeMap::<usize, Fr>::new();
        for term in terms {
            let gate = &term.gate;
            let mut residual = gate.c0;
            if !gate.c1.is_zero() { residual += gate.c1 * value(gate.left)?; }
            if !gate.c2.is_zero() { residual += gate.c2 * value(gate.right)?; }
            if !gate.c3.is_zero() {
                residual += gate.c3 * value(gate.left)? * value(gate.right)?;
            }
            *sums.entry(term.row).or_insert(Fr::zero()) += residual;
        }
        Ok(sums.into_iter().filter(|(_, residual)| !residual.is_zero()).collect())
    }

    #[test]
    fn bank53_native_map_values_and_physical_residuals_at_n3() {
        let owner = 1usize;
        let context = 0usize;
        let (input, plan) = small_input_and_plan(3);
        let producer = NativeOwnerProducer::new_for_history(&plan, &input).unwrap();
        let map = Map::from_parent(&plan, 64).unwrap();
        let imports = map.imports(owner as u64).unwrap();
        assert_eq!(imports.len(), 1);
        assert_eq!((imports[0].owner, imports[0].local, imports[0].width),
            (owner as u64, D_LOCAL, 224));
        let inputs = map_inputs_from_native(&map, &producer.exports, owner).unwrap();
        let generated = map.generate(owner as u64, &inputs).unwrap();
        assert!(generated.bits[5_757..].iter().all(|&value| !value));
        let mut values = vec![Fr::zero(); BANK53_TEST_CONTEXT_BITS];
        for (offset, &value) in generated.bits[..5_757].iter().enumerate() {
            values[offset] = Fr::from(value as u64);
        }
        let witness = Bank53TestWitness::new(owner, context, values);
        let row = producer.produce_bank53_for_test(owner, &witness).unwrap();
        for offset in 0..5_757 {
            assert_eq!(bit(row.packed_bytes(), BANK53_TEST_BASE + offset), generated.bits[offset]);
        }
        for bit_index in 0..224 {
            let index = map.input_index(imports[0], bit_index).unwrap();
            assert_eq!(producer.exports.bit(index).unwrap(),
                bit(row.packed_bytes(), D_LOCAL + bit_index));
        }
        let terms = map_owner_terms(&map, owner as u64, context).unwrap();
        assert!(terms.len() > 5_757);
        let foreign_rows = BTreeMap::new();
        assert!(physical_map_failures(&map, &plan, &input, owner, context,
            &row, &terms, &foreign_rows).unwrap().is_empty());

        let mut helper_fault = row.clone();
        flip_native_row_bit_for_test(&mut helper_fault, BANK53_TEST_BASE + 672).unwrap();
        let helper_failures = physical_map_failures(&map, &plan, &input, owner, context,
            &helper_fault, &terms, &foreign_rows).unwrap();
        assert!(!helper_failures.is_empty(), "a changed physical helper must violate Map");

        let mut difficulty_fault = row.clone();
        flip_native_row_bit_for_test(&mut difficulty_fault, D_LOCAL + 223).unwrap();
        let difficulty_failures = physical_map_failures(&map, &plan, &input, owner, context,
            &difficulty_fault, &terms, &foreign_rows).unwrap();
        assert!(!difficulty_failures.is_empty(), "a changed native D bit must violate Map");

        let mut wrong_owner = row.clone();
        wrong_owner.owner = 0;
        assert!(physical_map_failures(&map, &plan, &input, owner, context,
            &wrong_owner, &terms, &foreign_rows).unwrap_err().contains("owner"));

        let mut wrong_root = row.clone();
        wrong_root.root[0] ^= 1;
        assert!(physical_map_failures(&map, &plan, &input, owner, context,
            &wrong_root, &terms, &foreign_rows).unwrap_err().contains("binding"));
        let mut wrong_total = row.clone();
        wrong_total.total[0] ^= 1;
        assert!(physical_map_failures(&map, &plan, &input, owner, context,
            &wrong_total, &terms, &foreign_rows).unwrap_err().contains("binding"));

        let mut unlisted_foreign = terms.clone();
        let term = unlisted_foreign.iter_mut().find(|term| !term.gate.c1.is_zero()).unwrap();
        term.gate.left = 2 * WIDTH + D_LOCAL;
        assert!(physical_map_failures(&map, &plan, &input, owner, context,
            &row, &unlisted_foreign, &foreign_rows).unwrap_err().contains("foreign coordinate"));
    }

    #[test]
    fn bank53_first_anchor_reads_real_foreign_rows_at_n1984() {
        let owner = 1983usize;
        let context = 0usize;
        let input = super::max_join_tests::bounded_input_n(1984);
        let plan = WorkTreeHistoryPlan::compile(
            1984, 11, input.root(), input.total_be28()).unwrap();
        let producer = NativeOwnerProducer::new_for_history(&plan, &input).unwrap();
        let map = Map::from_parent(&plan, 64).unwrap();
        assert_eq!(map.tier(owner as u64).unwrap(), Some(1));
        let imports = map.imports(owner as u64).unwrap();
        assert_eq!(imports.iter().map(|imp| (imp.owner, imp.local, imp.width)).collect::<Vec<_>>(),
            vec![(1023, T_LOCAL, 64), (1982, D_LOCAL, 224), (1983, T_LOCAL, 64)]);
        let inputs = map_inputs_from_native(&map, &producer.exports, owner).unwrap();
        let generated = map.generate(owner as u64, &inputs).unwrap();
        assert!(generated.bits[5_757..].iter().all(|&value| !value));
        let mut values = vec![Fr::zero(); BANK53_TEST_CONTEXT_BITS];
        for (offset, &value) in generated.bits[..5_757].iter().enumerate() {
            values[offset] = Fr::from(value as u64);
        }
        let witness = Bank53TestWitness::new(owner, context, values);
        let row = producer.produce_bank53_for_test(owner, &witness).unwrap();
        let mut foreign_rows = BTreeMap::new();
        for source_owner in [1023usize, 1982] {
            foreign_rows.insert(source_owner, producer.produce(source_owner).unwrap());
        }
        for offset in 0..5_757 {
            assert_eq!(bit(row.packed_bytes(), BANK53_TEST_BASE + offset), generated.bits[offset]);
        }
        for imp in &imports {
            let source = if imp.owner == owner as u64 {
                &row
            } else {
                foreign_rows.get(&(imp.owner as usize)).unwrap()
            };
            for bit_index in 0..imp.width {
                let index = map.input_index(*imp, bit_index).unwrap();
                assert_eq!(producer.exports.bit(index).unwrap(),
                    bit(source.packed_bytes(), imp.local + bit_index),
                    "typed physical port owner{} local{}", imp.owner, imp.local + bit_index);
            }
        }
        let terms = map_owner_terms(&map, owner as u64, context).unwrap();
        assert!(physical_map_failures(&map, &plan, &input, owner, context,
            &row, &terms, &foreign_rows).unwrap().is_empty());

        let mut foreign_time_fault = foreign_rows.clone();
        flip_native_row_bit_for_test(foreign_time_fault.get_mut(&1023).unwrap(),
            T_LOCAL + 63).unwrap();
        let failures = physical_map_failures(&map, &plan, &input, owner, context,
            &row, &terms, &foreign_time_fault).unwrap();
        let physical_row_base = owner * (1 << 19) + 409_600 + context * 32_768;
        assert!(failures.iter().any(|(row, _)| *row == physical_row_base + 10_008),
            "foreign timestamp sign must fail its tier row");

        let mut missing_source = foreign_rows.clone();
        missing_source.remove(&1023);
        assert!(physical_map_failures(&map, &plan, &input, owner, context,
            &row, &terms, &missing_source).unwrap_err().contains("census"));
        let mut wrong_source_owner = foreign_rows.clone();
        wrong_source_owner.get_mut(&1023).unwrap().owner = 1982;
        assert!(physical_map_failures(&map, &plan, &input, owner, context,
            &row, &terms, &wrong_source_owner).unwrap_err().contains("foreign row binding"));

        let mut wrong_source_root = foreign_rows.clone();
        wrong_source_root.get_mut(&1023).unwrap().root[0] ^= 1;
        assert!(physical_map_failures(&map, &plan, &input, owner, context,
            &row, &terms, &wrong_source_root).unwrap_err().contains("foreign row binding"));

        let mut wrong_source_total = foreign_rows.clone();
        wrong_source_total.get_mut(&1023).unwrap().total[0] ^= 1;
        assert!(physical_map_failures(&map, &plan, &input, owner, context,
            &row, &terms, &wrong_source_total).unwrap_err().contains("foreign row binding"));

        let mut wrong_source_class = foreign_rows.clone();
        wrong_source_class.get_mut(&1023).unwrap().class =
            crate::daa_history_roster::OwnerClass::Padding;
        assert!(physical_map_failures(&map, &plan, &input, owner, context,
            &row, &terms, &wrong_source_class).unwrap_err().contains("foreign row binding"));

        let mut extra_source = foreign_rows.clone();
        extra_source.insert(1981, foreign_rows.get(&1982).unwrap().clone());
        assert!(physical_map_failures(&map, &plan, &input, owner, context,
            &row, &terms, &extra_source).unwrap_err().contains("census"));
    }

    #[test]
    fn bank53_test_writer_claims_one_context_on_real_n3_n4_native_rows() {
        for (n, owner, context) in [(4usize, 1usize, 0usize), (4, 1, 1), (3, 3, 0)] {
            let (input, plan) = small_input_and_plan(n);
            let producer = NativeOwnerProducer::new_for_history(&plan, &input).unwrap();
            let baseline = producer.produce(owner).unwrap();
            let witness = witness(owner, context);
            assert!(witness.values[BANK53_TEST_LIVE_BITS..].iter().all(|value| value.is_zero()));
            let assigned = producer.produce_bank53_for_test(owner, &witness).unwrap();
            assert_eq!(assigned.owner(), owner);
            assert_eq!(assigned.class(), producer.roster.owner_class(owner as u64).unwrap());
            assert_eq!(assigned.packed_bytes().len(), OWNER_BYTES);
            let selected = BANK53_TEST_BASE + context * BANK53_TEST_CONTEXT_BITS;
            let other_context = BANK53_TEST_BASE
                + (1 - context) * BANK53_TEST_CONTEXT_BITS;
            for offset in 0..BANK53_TEST_CONTEXT_BITS {
                assert_eq!(
                    bit(assigned.packed_bytes(), selected + offset),
                    witness.values[offset] == Fr::one(),
                    "owner{owner} context{context} bit{offset}",
                );
                assert_eq!(
                    bit(assigned.packed_bytes(), other_context + offset),
                    bit(baseline.packed_bytes(), other_context + offset),
                    "untouched context owner{owner} bit{offset}",
                );
            }
            for wire in (0..BANK53_TEST_BASE).chain(
                BANK53_TEST_BASE + BANK53_TEST_CONTEXTS * BANK53_TEST_CONTEXT_BITS..WIDTH,
            ) {
                assert_eq!(
                    bit(assigned.packed_bytes(), wire),
                    bit(baseline.packed_bytes(), wire),
                    "native row owner{owner} wire{wire}",
                );
            }
        }
    }

    #[test]
    fn bank53_test_writer_rejects_same_value_collision_for_zero_and_one() {
        let (input, plan) = small_input_and_plan(4);
        let producer = NativeOwnerProducer::new_for_history(&plan, &input).unwrap();
        for (offset, value) in [(3usize, Fr::zero()), (127, Fr::one())] {
            let mut witness = witness(1, 0);
            witness.values[offset] = value;
            let error = producer
                .bank53_same_value_collision_for_test(1, &witness, offset)
                .unwrap_err();
            assert!(error.contains("already claimed"), "{error}");
        }
    }

    #[test]
    fn bank53_test_writer_rejects_wrong_owner_context_length_and_lane() {
        let (input, plan) = small_input_and_plan(4);
        let producer = NativeOwnerProducer::new_for_history(&plan, &input).unwrap();

        let wrong_owner = witness(2, 0);
        assert!(rejected(producer.produce_bank53_for_test(1, &wrong_owner)).contains("owner mismatch"));

        let mut wrong_context = witness(1, 0);
        wrong_context.context = 1;
        let class = producer.roster.owner_class(1).unwrap();
        let selection = OwnerSelection::Single { owner: 1, class };
        let mut rows = OwnedRows::new(selection);
        seed_header_from_template_bank53_for_test(
            &producer.header_template, &plan, &input, 1, 0, &mut rows,
        )
        .unwrap();
        let before = rows.claimed[0].clone();
        assert!(write_bank53_witness_for_test(&mut rows, 1, 0, &wrong_context)
            .unwrap_err().contains("context mismatch"));
        assert_eq!(rows.claimed[0], before, "wrong-context attempt changed claims");

        let mut short = witness(1, 0);
        short.values.pop();
        assert!(rejected(producer.produce_bank53_for_test(1, &short)).contains("length mismatch"));

        let mut outside_lane = witness(1, 2);
        outside_lane.context = 2;
        assert!(rejected(producer.produce_bank53_for_test(1, &outside_lane)).contains("context"));

        for offset in [BANK53_TEST_LIVE_BITS, BANK53_TEST_CONTEXT_BITS - 1] {
            let mut nonzero_padding = witness(1, 0);
            nonzero_padding.values[offset] = Fr::one();
            assert!(rejected(producer.produce_bank53_for_test(1, &nonzero_padding))
                .contains("padding/slack"));
        }
    }

    #[test]
    fn bank53_test_writer_faults_zero_omission_and_non_boolean_at_selected_wire() {
        let (input, plan) = small_input_and_plan(4);
        let producer = NativeOwnerProducer::new_for_history(&plan, &input).unwrap();
        let context = 1usize;
        let wire = BANK53_TEST_BASE + context * BANK53_TEST_CONTEXT_BITS + 211;
        let witness = Bank53TestWitness::new(
            1,
            context,
            vec![Fr::zero(); BANK53_TEST_CONTEXT_BITS],
        );
        let omitted = rejected(producer
            .produce_bank53_fault_for_test(
                1,
                &witness,
                AssemblyFault::MissingClaim { owner: 1, wire },
            ));
        assert!(omitted.contains(&format!("wire{wire}")), "{omitted}");

        let non_boolean = rejected(producer
            .produce_bank53_fault_for_test(
                1,
                &witness,
                AssemblyFault::NonBooleanClaim { owner: 1, wire },
            ));
        assert!(non_boolean.contains("non-Boolean claim"), "{non_boolean}");
    }

    #[test]
    fn bank53_source_owned_map_n3_n4_and_exclusive_context_claims() {
        for (n, context) in [(3usize, 0usize), (4, 1)] {
            let (input, plan) = small_input_and_plan(n);
            let producer = NativeOwnerProducer::new_for_history(&plan, &input).unwrap();
            let map = Map::from_parent(&plan, 64).unwrap();
            let owner = 1usize;
            let assignment = generate_bank53_map_assignment(
                &plan, &input, &producer.exports, &map, owner, context,
            ).unwrap();
            let row = producer.produce_bank53_map(owner, &map, context).unwrap();
            assert_eq!(row.map_binding, Some(map.binding()));
            assert_eq!(row.map_context, Some(context));
            let start = BANK53_BASE + context * BANK53_CONTEXT_BITS;
            for (offset, &value) in assignment.values.iter().enumerate() {
                assert_eq!(bit(row.packed_bytes(), start + offset), value, "n{n} bit{offset}");
            }
            assert!(assignment.values[BANK53_MAP_LIVE_BITS..].iter().all(|bit| !bit));
            assert!(validate_native_bank53_map_consumer(
                &plan, &input, &map, owner, context, &row, &BTreeMap::new(),
            ).is_ok());

            let class = producer.roster.owner_class(owner as u64).unwrap();
            let selection = OwnerSelection::Single { owner, class };
            let mut claimed_rows = OwnedRows::new(selection);
            seed_header_from_template_bank53_map(
                &producer.header_template, &plan, &input, owner, context, &mut claimed_rows,
            ).unwrap();
            let offset = 4usize;
            let same_value = Fr::from(assignment.values[offset] as u64);
            claimed_rows.claim(owner, start + offset, same_value).unwrap();
            assert!(write_bank53_map_assignment(&mut claimed_rows, &assignment)
                .unwrap_err().contains("already claimed"));

            let mut bad_tail = assignment;
            bad_tail.values[BANK53_MAP_LIVE_BITS] = true;
            let mut empty_rows = OwnedRows::new(OwnerSelection::Single { owner, class });
            assert!(write_bank53_map_assignment(&mut empty_rows, &bad_tail)
                .unwrap_err().contains("tail/slack"));
        }
    }

    #[test]
    fn bank53_source_owned_modern_map_n1984_native_foreign_join_and_negatives() {
        use crate::global_u_roster::{self, CandidateSource};
        use crate::legacy_envelope_map::{LowerBranch, LowerSelector, LowerSource, SMAX};
        use num_bigint::BigUint;

        const N: usize = 1984;
        const OWNER: usize = 1983;
        let started = std::time::Instant::now();
        let mut phase_started = started;
        macro_rules! phase {
            ($label:expr) => {{
                println!("STAGEB_PHASE {} elapsed_ms={}", $label, phase_started.elapsed().as_millis());
                phase_started = std::time::Instant::now();
            }};
        }
        let input = super::max_join_tests::bounded_input_n(N);
        phase!("prefix_parse_and_native_derivation");
        let plan = WorkTreeHistoryPlan::compile(
            N as u64, 11, input.root(), input.total_be28(),
        ).unwrap();
        let producer = NativeOwnerProducer::new_for_history(&plan, &input).unwrap();
        phase!("plan_and_exports_setup");

        // Derive q1's lower bound from this exact native prefix via its
        // legacy Map row, then select e from the actual bounded envelope.
        let legacy_map = Map::from_parent(&plan, 64).unwrap();
        let legacy_inputs = map_inputs_from_native(&legacy_map, &producer.exports, OWNER).unwrap();
        let legacy_row = legacy_map.generate(OWNER as u64, &legacy_inputs).unwrap();
        phase!("native_legacy_q1_map_and_b_extraction");
        let q1_b = (0..92).fold(BigUint::from(0u8), |mut value, bit| {
            if legacy_row.bits[SMAX - crate::legacy_envelope_map::BASE + bit] {
                value += BigUint::from(1u8) << bit;
            }
            value
        });
        assert_eq!(q1_b, BigUint::from(22_538_929_735_599u64));
        let schedule = global_u_roster::Schedule::new(N as u64).unwrap();
        let mut supplied = Vec::new();
        let mut maximum_candidate = BigUint::from(global_u_roster::INITIAL_I);
        for value in [global_u_roster::RESET_CHILD_417792, global_u_roster::RESET_CHILD_417793] {
            maximum_candidate = maximum_candidate.max(BigUint::from(value));
        }
        let mut max_difficulty = BigUint::from(global_u_roster::INITIAL_I);
        for source in schedule.iter() {
            let value = match source {
                CandidateSource::HeaderDifficulty { height, .. } => {
                    crate::work_tree_work::native_decode(
                        input.compact_n_bits(height as usize).unwrap(),
                    ).unwrap()
                }
                CandidateSource::LegacyBound { q: 1, .. } => q1_b.clone(),
                CandidateSource::LegacyBound { q, .. } => panic!("unexpected q={q}"),
            };
            if matches!(source, CandidateSource::HeaderDifficulty { .. }) {
                max_difficulty = max_difficulty.max(value.clone());
            }
            maximum_candidate = maximum_candidate.max(value.clone());
            supplied.push(global_u_roster::SuppliedCandidate { source, value });
        }
        let modern_floor = (&max_difficulty * BigUint::from(3u8)) / BigUint::from(2u8);
        maximum_candidate = maximum_candidate.max(modern_floor);
        let envelope = global_u_roster::fold(N as u64, supplied).unwrap();
        assert_eq!(envelope.maximum_candidate, maximum_candidate);
        assert_eq!(envelope.exponent, 47);
        phase!("native_candidate_roster_and_exponent");

        let map = Map::from_parent_modern_global_u(
            &plan,
            envelope.exponent,
            LowerSelector { source: LowerSource::Reset417792, branch: LowerBranch::Literal },
        ).unwrap();
        let context = 0usize;
        let expected_assignment = generate_bank53_map_assignment(
            &plan, &input, &producer.exports, &map, OWNER, context,
        ).unwrap();
        let row = producer.produce_bank53_map(OWNER, &map, context).unwrap();
        let lane_start = BANK53_BASE + context * BANK53_CONTEXT_BITS;
        for offset in 0..BANK53_MAP_LIVE_BITS {
            assert_eq!(
                bit(row.packed_bytes(), lane_start + offset),
                expected_assignment.values[offset],
                "N1984 generated Map bit {offset}",
            );
        }
        assert!((BANK53_MAP_LIVE_BITS..BANK53_CONTEXT_BITS)
            .all(|offset| !bit(row.packed_bytes(), lane_start + offset)));
        phase!("source_owned_modern_map_and_packed_owner");
        let mut foreign = BTreeMap::new();
        for source_owner in [1023usize, 1982] {
            foreign.insert(source_owner, producer.produce(source_owner).unwrap());
        }
        phase!("foreign_native_packed_rows");
        validate_native_bank53_map_consumer(&plan, &input, &map, OWNER, context, &row, &foreign).unwrap();
        phase!("packed_import_equality_and_map_residual_consumer");

        let alternate_e = Map::from_parent_modern_global_u(
            &plan,
            46,
            LowerSelector { source: LowerSource::Reset417792, branch: LowerBranch::Literal },
        ).unwrap();
        assert_ne!(alternate_e.binding(), map.binding());
        assert!(validate_native_bank53_map_consumer(
            &plan, &input, &alternate_e, OWNER, context, &row, &foreign,
        ).unwrap_err().contains("binding/context"));
        let alternate_selector = Map::from_parent_modern_global_u(
            &plan,
            envelope.exponent,
            LowerSelector { source: LowerSource::Reset417793, branch: LowerBranch::Literal },
        ).unwrap();
        assert_ne!(alternate_selector.binding(), map.binding());
        assert!(validate_native_bank53_map_consumer(
            &plan, &input, &alternate_selector, OWNER, context, &row, &foreign,
        ).unwrap_err().contains("binding/context"));

        let mut bad_slack = row.clone();
        flip_native_row_bit_for_test(
            &mut bad_slack,
            BANK53_BASE + context * BANK53_CONTEXT_BITS + BANK53_MAP_LIVE_BITS,
        ).unwrap();
        assert!(validate_native_bank53_map_consumer(
            &plan, &input, &map, OWNER, context, &bad_slack, &foreign,
        ).unwrap_err().contains("tail/Score slack"));

        let mut bad_binding = row.clone();
        bad_binding.map_binding = Some(legacy_map.binding());
        assert!(validate_native_bank53_map_consumer(
            &plan, &input, &map, OWNER, context, &bad_binding, &foreign,
        ).unwrap_err().contains("binding/context"));
        let mut bad_context = row.clone();
        bad_context.map_context = Some(1);
        assert!(validate_native_bank53_map_consumer(
            &plan, &input, &map, OWNER, context, &bad_context, &foreign,
        ).unwrap_err().contains("binding/context"));
        let mut bad_root = row.clone();
        bad_root.root[0] ^= 1;
        assert!(validate_native_bank53_map_consumer(
            &plan, &input, &map, OWNER, context, &bad_root, &foreign,
        ).unwrap_err().contains("parent binding"));
        let mut bad_total = row.clone();
        bad_total.total[0] ^= 1;
        assert!(validate_native_bank53_map_consumer(
            &plan, &input, &map, OWNER, context, &bad_total, &foreign,
        ).unwrap_err().contains("parent binding"));
        let mut bad_owner = row.clone();
        bad_owner.owner = 1;
        assert!(validate_native_bank53_map_consumer(
            &plan, &input, &map, OWNER, context, &bad_owner, &foreign,
        ).unwrap_err().contains("expected owner mismatch"));
        let mut bad_class = row.clone();
        bad_class.class = crate::daa_history_roster::OwnerClass::Genesis;
        assert!(validate_native_bank53_map_consumer(
            &plan, &input, &map, OWNER, context, &bad_class, &foreign,
        ).unwrap_err().contains("parent binding"));

        let mut missing = foreign.clone();
        missing.remove(&1023);
        assert!(validate_native_bank53_map_consumer(
            &plan, &input, &map, OWNER, context, &row, &missing,
        ).unwrap_err().contains("census"));
        let mut extra = foreign.clone();
        extra.insert(1981, foreign[&1982].clone());
        assert!(validate_native_bank53_map_consumer(
            &plan, &input, &map, OWNER, context, &row, &extra,
        ).unwrap_err().contains("census"));
        let mut wrong_foreign = foreign.clone();
        wrong_foreign.get_mut(&1982).unwrap().owner = 1981;
        assert!(validate_native_bank53_map_consumer(
            &plan, &input, &map, OWNER, context, &row, &wrong_foreign,
        ).unwrap_err().contains("foreign row binding"));

        for (source_owner, wire) in [(1023usize, T_LOCAL + 7), (1982, D_LOCAL + 11)] {
            let mut mutated = foreign.clone();
            flip_native_row_bit_for_test(mutated.get_mut(&source_owner).unwrap(), wire).unwrap();
            assert!(validate_native_bank53_map_consumer(
                &plan, &input, &map, OWNER, context, &row, &mutated,
            ).unwrap_err().contains("typed import differs"));
        }
        let mut own_timestamp = row.clone();
        flip_native_row_bit_for_test(&mut own_timestamp, T_LOCAL + 5).unwrap();
        assert!(validate_native_bank53_map_consumer(
            &plan, &input, &map, OWNER, context, &own_timestamp, &foreign,
        ).unwrap_err().contains("typed import differs"));

        for helper in [
            crate::legacy_envelope_map::BASE + 672,
            SMAX,
        ] {
            let mut mutated = row.clone();
            flip_native_row_bit_for_test(
                &mut mutated,
                BANK53_BASE + context * BANK53_CONTEXT_BITS + helper - crate::legacy_envelope_map::BASE,
            ).unwrap();
            assert!(validate_native_bank53_map_consumer(
                &plan, &input, &map, OWNER, context, &mutated, &foreign,
            ).unwrap_err().contains("physical residual"), "helper {helper}");
        }
        phase!("isolated_negative_fixtures");
        println!("STAGEB_TOTAL elapsed_ms={}", started.elapsed().as_millis());
    }

    const STAGE0_GLOBAL_WIRES: usize = 1 << 20;
    const STAGE0_LOCAL_ROWS: usize = 1 << 19;
    const STAGE0_OWNER_ROW_BASE: usize = 1983 * STAGE0_LOCAL_ROWS;
    const STAGE0_Q1: u64 = 22_538_929_735_599;
    const STAGE0_Q1_START: usize = 677_223;

    fn stage0_rebase_terms(
        source: &[Term],
        row_shift: usize,
        reverse_wire: bool,
    ) -> Result<Vec<Term>, String> {
        let mut destinations = BTreeMap::<usize, usize>::new();
        let mut output = Vec::with_capacity(source.len());
        for term in source {
            let mut rebased = term.clone();
            for wire in [&mut rebased.gate.left, &mut rebased.gate.right] {
                let owner = *wire / STAGE0_GLOBAL_WIRES;
                let local = *wire % STAGE0_GLOBAL_WIRES;
                let slot = match owner {
                    1023 => 0,
                    1982 => 1,
                    1983 => 2,
                    _ => return Err(format!("Stage0 unexpected source owner {owner}")),
                };
                let local = if reverse_wire {
                    STAGE0_GLOBAL_WIRES - 1 - local
                } else {
                    local
                };
                let destination = slot * STAGE0_GLOBAL_WIRES + local;
                if let Some(previous) = destinations.insert(destination, *wire) {
                    if previous != *wire {
                        return Err("Stage0 input rebase collision".into());
                    }
                }
                *wire = destination;
            }
            rebased.row = rebased
                .row
                .checked_sub(STAGE0_OWNER_ROW_BASE)
                .ok_or("Stage0 output row below owner base")?
                .checked_add(row_shift)
                .ok_or("Stage0 output row shift overflow")?;
            if rebased.row >= STAGE0_LOCAL_ROWS {
                return Err("Stage0 output row outside log19 circuit".into());
            }
            output.push(rebased);
        }
        Ok(output)
    }

    fn stage0_residuals(
        terms: &[Term],
        read: impl Fn(usize) -> Result<bool, String>,
    ) -> Result<BTreeMap<usize, Fr>, String> {
        let mut sums = BTreeMap::<usize, Fr>::new();
        for term in terms {
            let gate = &term.gate;
            let mut residual = gate.c0;
            if !gate.c1.is_zero() {
                residual += gate.c1 * Fr::from(read(gate.left)? as u64);
            }
            if !gate.c2.is_zero() {
                residual += gate.c2 * Fr::from(read(gate.right)? as u64);
            }
            if !gate.c3.is_zero() {
                residual += gate.c3
                    * Fr::from(read(gate.left)? as u64)
                    * Fr::from(read(gate.right)? as u64);
            }
            *sums.entry(term.row).or_insert(Fr::zero()) += residual;
        }
        Ok(sums)
    }

    fn stage0_local_read(local_y: &[u8], index: usize) -> Result<bool, String> {
        if index >= 4 * STAGE0_GLOBAL_WIRES {
            return Err("Stage0 local input outside log22".into());
        }
        Ok(bit(local_y, index))
    }

    fn stage0_pin_residuals(local_y: &[u8], q1: &BigUint) -> BTreeMap<usize, Fr> {
        (0..92)
            .map(|bit_index| {
                let actual = bit(local_y, 2 * STAGE0_GLOBAL_WIRES + STAGE0_Q1_START + bit_index);
                let expected = q1.bit(bit_index as u64);
                (
                    bit_index,
                    Fr::from(actual as u64) - Fr::from(expected as u64),
                )
            })
            .collect()
    }

    #[test]
    fn bank53_same_x_stage0_q1_index_and_92_bit_pin_pure() {
        use crate::legacy_envelope_map::SMAX;
        use num_bigint::BigUint;

        assert_eq!(
            STAGE0_Q1_START,
            BANK53_BASE + SMAX - crate::legacy_envelope_map::BASE,
        );
        let expected_q1 = BigUint::from(STAGE0_Q1);
        let mut local_y = vec![0u8; 4 * OWNER_BYTES];
        for bit_index in 0..92 {
            if expected_q1.bit(bit_index as u64) {
                let index = 2 * STAGE0_GLOBAL_WIRES + STAGE0_Q1_START + bit_index;
                local_y[index / 8] |= 1 << (index % 8);
            }
        }
        assert!(stage0_pin_residuals(&local_y, &expected_q1)
            .values()
            .all(|residual| residual.is_zero()));
        let substituted = &expected_q1 ^ BigUint::from(1u8);
        assert_eq!(
            stage0_pin_residuals(&local_y, &substituted)
                .values()
                .filter(|residual| !residual.is_zero())
                .count(),
            1,
        );
    }

    fn stage0_check_pin_rows_disjoint(terms: &[Term]) -> Result<(), String> {
        if terms.iter().any(|term| term.row < 92) {
            return Err("Stage0 q1 pin row collision".into());
        }
        Ok(())
    }

    fn stage0_eval_lsb20(packed: &[u8], coordinates: &[Fr]) -> Fr {
        use ark_ff::Field;
        assert_eq!(packed.len(), OWNER_BYTES);
        assert_eq!(coordinates.len(), 20);
        let mut values = Vec::with_capacity(STAGE0_GLOBAL_WIRES);
        for wire in 0..STAGE0_GLOBAL_WIRES {
            values.push(Fr::from(bit(packed, wire) as u64));
        }
        for coordinate in coordinates {
            let one_minus = Fr::one() - coordinate;
            let half = values.len() / 2;
            for index in 0..half {
                values[index] = values[2 * index] * one_minus
                    + values[2 * index + 1] * coordinate;
            }
            values.truncate(half);
        }
        values[0]
    }

    fn stage0_eq_at_point(point: &[Fr], index: usize) -> Fr {
        point.iter().enumerate().fold(Fr::one(), |weight, (bit_index, r)| {
            weight
                * if (index >> bit_index) & 1 == 1 {
                    *r
                } else {
                    Fr::one() - r
                }
        })
    }

    fn stage0_global_x_mle(slice_mles: &[(usize, Fr)], point: &[Fr]) -> Result<Fr, String> {
        if point.len() != 31 {
            return Err("Stage0 global X point must have 31 coordinates".into());
        }
        if slice_mles.iter().map(|(owner, _)| *owner).collect::<Vec<_>>()
            != [1023, 1982, 1983]
        {
            return Err("Stage0 global X slices must be owners 1023/1982/1983 in order".into());
        }
        let mut owner_table = vec![Fr::zero(); 1 << 11];
        for (owner, value) in slice_mles {
            owner_table[*owner] = *value;
        }
        for coordinate in &point[20..] {
            let one_minus = Fr::one() - coordinate;
            for index in 0..owner_table.len() / 2 {
                owner_table[index] = owner_table[2 * index] * one_minus
                    + owner_table[2 * index + 1] * coordinate;
            }
            owner_table.truncate(owner_table.len() / 2);
        }
        Ok(owner_table[0])
    }

    fn stage0_point_for_owner(wire_point: &[Fr], owner: usize) -> Vec<Fr> {
        let mut point = wire_point.to_vec();
        point.extend((0..11).map(|index| Fr::from(((owner >> index) & 1) as u64)));
        point
    }

    #[test]
    fn bank53_same_x_stage0_global_mle_order_and_owner0_negative_pure() {
        use ark_ff::Field;

        let denominator = Fr::from(97u64).inverse().unwrap();
        let wire_point = (0..20)
            .map(|index| Fr::from((index + 2) as u64) * denominator)
            .collect::<Vec<_>>();
        let slice_mles = [(1023, Fr::from(2u64)), (1982, Fr::from(5u64)), (1983, Fr::from(9u64))];
        for (owner, expected) in slice_mles {
            assert_eq!(
                stage0_global_x_mle(&slice_mles, &stage0_point_for_owner(&wire_point, owner)).unwrap(),
                expected,
                "Boolean high block must select owner {owner} after low wire folding",
            );
        }
        let mut reversed_blocks = (0..11)
            .map(|index| Fr::from(((1023usize >> index) & 1) as u64))
            .collect::<Vec<_>>();
        reversed_blocks.extend_from_slice(&wire_point);
        assert_ne!(
            stage0_global_x_mle(&slice_mles, &reversed_blocks).unwrap(),
            stage0_global_x_mle(&slice_mles, &stage0_point_for_owner(&wire_point, 1023)).unwrap(),
            "[owner11,wire20] block reversal escaped sparse virtual X MLE",
        );

        let zero_owner_term = crate::sparse::Term {
            row: STAGE0_OWNER_ROW_BASE + 409_600,
            gate: crate::gkr::Gate {
                left: 0,
                right: 1023 * STAGE0_GLOBAL_WIRES,
                c0: Fr::zero(),
                c1: Fr::one(),
                c2: Fr::zero(),
                c3: Fr::zero(),
            },
        };
        assert!(stage0_rebase_terms(&[zero_owner_term.clone()], 0, false)
            .unwrap_err()
            .contains("unexpected source owner 0"));
        assert!(stage0_residuals(&[zero_owner_term], |index| {
            let owner = index / STAGE0_GLOBAL_WIRES;
            match owner {
                1023 | 1982 | 1983 => Ok(false),
                _ => Err(format!("Stage0 original source owner outside census: {owner}")),
            }
        })
        .unwrap_err()
        .contains("outside census: 0"));
    }

    fn stage0_projected_value(
        slice_mles: &[Fr; 4],
        t0: Fr,
        t1: Fr,
    ) -> Fr {
        (Fr::one() - t0) * (Fr::one() - t1) * slice_mles[0]
            + t0 * (Fr::one() - t1) * slice_mles[1]
            + (Fr::one() - t0) * t1 * slice_mles[2]
    }

    #[test]
    fn bank53_same_x_projection_stage0_n1984_host_preflight() {
        use crate::legacy_envelope_map::{LowerBranch, LowerSelector, LowerSource, SMAX};
        use ark_ff::Field;
        use num_bigint::BigUint;

        const OWNER: usize = 1983;
        let started = std::time::Instant::now();
        let input = super::max_join_tests::bounded_input_n(1984);
        let plan = WorkTreeHistoryPlan::compile(
            1984,
            11,
            input.root(),
            input.total_be28(),
        )
        .unwrap();
        let producer = NativeOwnerProducer::new_for_history(&plan, &input).unwrap();
        println!("STAGE0_PHASE native_input_and_exports_ms={}", started.elapsed().as_millis());

        // Derive q1 from the exact bounded native exports, then pin the modern
        // Map fixture to the reviewed exponent and selected reset branch.
        let legacy_map = Map::from_parent(&plan, 64).unwrap();
        let legacy_inputs = map_inputs_from_native(&legacy_map, &producer.exports, OWNER).unwrap();
        let legacy_row = legacy_map.generate(OWNER as u64, &legacy_inputs).unwrap();
        let q1 = (0..92).fold(BigUint::from(0u8), |mut value, bit_index| {
            if legacy_row.bits[SMAX - crate::legacy_envelope_map::BASE + bit_index] {
                value += BigUint::from(1u8) << bit_index;
            }
            value
        });
        assert_eq!(q1, BigUint::from(STAGE0_Q1));
        let map = Map::from_parent_modern_global_u(
            &plan,
            47,
            LowerSelector {
                source: LowerSource::Reset417792,
                branch: LowerBranch::Literal,
            },
        )
        .unwrap();
        let context = 0usize;
        let assignment = generate_bank53_map_assignment(
            &plan,
            &input,
            &producer.exports,
            &map,
            OWNER,
            context,
        )
        .unwrap();
        assert_eq!(
            STAGE0_Q1_START,
            BANK53_BASE + SMAX - crate::legacy_envelope_map::BASE,
            "q1 physical helper offset is rebased exactly once",
        );
        let owner_row = producer.produce_bank53_map(OWNER, &map, context).unwrap();
        let foreign_rows = [1023usize, 1982]
            .into_iter()
            .map(|owner| (owner, producer.produce(owner).unwrap()))
            .collect::<BTreeMap<_, _>>();
        let mut source_rows = foreign_rows.clone();
        source_rows.insert(OWNER, owner_row.clone());
        println!("STAGE0_PHASE map_and_native_owner_slices_ms={}", started.elapsed().as_millis());

        // The three immutable full packed slices are the same native X rows
        // used by the existing producer; slot 3 is a synthetic zero slice.
        let mut local_y = vec![0u8; 4 * OWNER_BYTES];
        for (slot, owner) in [(0usize, 1023usize), (1, 1982), (2, OWNER)] {
            let source = &source_rows[&owner];
            assert_eq!(source.owner, owner);
            assert_eq!(source.bytes.len(), OWNER_BYTES);
            local_y[slot * OWNER_BYTES..(slot + 1) * OWNER_BYTES]
                .copy_from_slice(&source.bytes);
        }
        assert!(local_y[3 * OWNER_BYTES..].iter().all(|byte| *byte == 0));
        assert_eq!(source_rows.keys().copied().collect::<Vec<_>>(), vec![1023, 1982, OWNER]);
        for import in map.imports(OWNER as u64).unwrap() {
            let source = &source_rows[&(import.owner as usize)];
            for bit_index in 0..import.width {
                assert_eq!(
                    producer.exports.bit(map.input_index(import, bit_index).unwrap()).unwrap(),
                    bit(source.packed_bytes(), import.local + bit_index),
                    "owner{} typed import bit{}",
                    import.owner,
                    import.local + bit_index,
                );
            }
        }
        for offset in 0..BANK53_MAP_LIVE_BITS {
            assert_eq!(
                bit(owner_row.packed_bytes(), BANK53_BASE + offset),
                assignment.values[offset],
                "source-owned owner1983 Map bit {offset}",
            );
        }
        assert!((BANK53_MAP_LIVE_BITS..BANK53_CONTEXT_BITS)
            .all(|offset| !bit(owner_row.packed_bytes(), BANK53_BASE + offset)));
        let q1_start = STAGE0_Q1_START;
        let expected_q1 = BigUint::from(STAGE0_Q1);
        for bit_index in 0..92 {
            assert_eq!(
                bit(owner_row.packed_bytes(), q1_start + bit_index),
                expected_q1.bit(bit_index as u64),
                "native Map q1 bit {bit_index}",
            );
        }
        assert_eq!(
            stage0_pin_residuals(&local_y, &expected_q1)
                .values()
                .filter(|residual| !residual.is_zero())
                .count(),
            0,
        );

        let terms = map_owner_terms(&map, OWNER as u64, context).unwrap();
        let left_zero = terms.iter().filter(|term| term.gate.left == 0).count();
        let right_zero = terms.iter().filter(|term| term.gate.right == 0).count();
        let active_left_zero = terms
            .iter()
            .filter(|term| term.gate.left == 0 && (!term.gate.c1.is_zero() || !term.gate.c3.is_zero()))
            .count();
        let active_right_zero = terms
            .iter()
            .filter(|term| term.gate.right == 0 && (!term.gate.c2.is_zero() || !term.gate.c3.is_zero()))
            .count();
        println!(
            "STAGE0_MAP_ZERO left={left_zero} right={right_zero} active_left={active_left_zero} active_right={active_right_zero}"
        );
        assert_eq!((left_zero, right_zero), (0, 0), "Map terms must not name global wire zero");
        let original_residuals = stage0_residuals(&terms, |index| {
            let source_owner = index / STAGE0_GLOBAL_WIRES;
            if !matches!(source_owner, 1023 | 1982 | 1983) {
                return Err(format!("Stage0 original source owner outside census: {source_owner}"));
            }
            let wire = index % STAGE0_GLOBAL_WIRES;
            let row = source_rows
                .get(&source_owner)
                .ok_or_else(|| format!("Stage0 original source owner outside census: {source_owner}"))?;
            Ok(bit(row.packed_bytes(), wire))
        })
        .unwrap();
        assert!(original_residuals.values().all(|residual| residual.is_zero()));
        let local_terms = stage0_rebase_terms(&terms, 0, false).unwrap();
        assert_eq!(local_terms.len(), terms.len());
        assert!(local_terms.iter().all(|term| (409_600..442_368).contains(&term.row)));
        stage0_check_pin_rows_disjoint(&local_terms).unwrap();
        let rebased_residuals = stage0_residuals(&local_terms, |index| stage0_local_read(&local_y, index))
            .unwrap();
        let normalized_original = original_residuals
            .iter()
            .map(|(row, residual)| (row - STAGE0_OWNER_ROW_BASE, *residual))
            .collect::<BTreeMap<_, _>>();
        assert_eq!(normalized_original, rebased_residuals, "original and rebased row residuals differ");
        assert!(rebased_residuals.values().all(|residual| residual.is_zero()));
        for (original, rebased) in terms.iter().zip(&local_terms) {
            assert_eq!(rebased.row, original.row - STAGE0_OWNER_ROW_BASE);
            assert_eq!(rebased.gate.c0, original.gate.c0);
            assert_eq!(rebased.gate.c1, original.gate.c1);
            assert_eq!(rebased.gate.c2, original.gate.c2);
            assert_eq!(rebased.gate.c3, original.gate.c3);
        }
        println!("STAGE0_PHASE checked_rebase_and_residual_parity_ms={}", started.elapsed().as_millis());

        // MLE projection at deterministic non-Boolean coordinates. The only
        // field scratch is one 2^20-element vector (32 MiB), reused by slot.
        let denominator = Fr::from(97u64).inverse().unwrap();
        let wire_point = (0..20)
            .map(|index| Fr::from((index + 2) as u64) * denominator)
            .collect::<Vec<_>>();
        let t0 = Fr::from(31u64) * denominator;
        let t1 = Fr::from(43u64) * denominator;
        let mut slice_mles = [Fr::zero(); 4];
        for slot in 0..4 {
            let packed = &local_y[slot * OWNER_BYTES..(slot + 1) * OWNER_BYTES];
            slice_mles[slot] = stage0_eval_lsb20(packed, &wire_point);
        }
        let local_mle = (0..4).fold(Fr::zero(), |sum, slot| {
            let owner_weight = stage0_eq_at_point(&[t0, t1], slot);
            sum + owner_weight * slice_mles[slot]
        });
        let projected = stage0_projected_value(&slice_mles, t0, t1);
        assert_eq!(local_mle, projected, "local Y MLE differs from three-point selector projection");
        let boolean_owner_point = |owner: usize| {
            (0..11)
                .map(|index| Fr::from(((owner >> index) & 1) as u64))
                .collect::<Vec<_>>()
        };
        let global_slices = [(1023, slice_mles[0]), (1982, slice_mles[1]), (1983, slice_mles[2])];
        let x_1023 = stage0_global_x_mle(&global_slices, &stage0_point_for_owner(&wire_point, 1023)).unwrap();
        let x_1982 = stage0_global_x_mle(&global_slices, &stage0_point_for_owner(&wire_point, 1982)).unwrap();
        let x_1983 = stage0_global_x_mle(&global_slices, &stage0_point_for_owner(&wire_point, 1983)).unwrap();
        assert_eq!(x_1023, slice_mles[0]);
        assert_eq!(x_1982, slice_mles[1]);
        assert_eq!(x_1983, slice_mles[2]);
        assert_eq!(
            projected,
            (Fr::one() - t0) * (Fr::one() - t1) * x_1023
                + t0 * (Fr::one() - t1) * x_1982
                + (Fr::one() - t0) * t1 * x_1983,
        );
        assert!(x_1023 != x_1982 && x_1982 != x_1983);
        println!("STAGE0_PHASE nonboolean_mle_projection_ms={}", started.elapsed().as_millis());

        // Isolated single-fault preflight negatives.
        let mut swapped_slots = local_y.clone();
        for index in 0..OWNER_BYTES {
            swapped_slots.swap(index, OWNER_BYTES + index);
        }
        let swapped_residuals = stage0_residuals(&local_terms, |index| stage0_local_read(&swapped_slots, index)).unwrap();
        assert_ne!(rebased_residuals, swapped_residuals, "slot swap escaped Map residual check");

        let reversed_terms = stage0_rebase_terms(&terms, 0, true).unwrap();
        let reversed_residuals = stage0_residuals(&reversed_terms, |index| stage0_local_read(&local_y, index)).unwrap();
        assert_ne!(rebased_residuals, reversed_residuals, "wire-coordinate reversal escaped Map residual check");
        let reversed_point = wire_point.iter().copied().rev().collect::<Vec<_>>();
        assert_ne!(
            stage0_eval_lsb20(&local_y[0..OWNER_BYTES], &wire_point),
            stage0_eval_lsb20(&local_y[0..OWNER_BYTES], &reversed_point),
            "LSB-first MLE coordinate reversal went undetected",
        );
        let reversed_blocks = [boolean_owner_point(1023), wire_point.clone()].concat();
        let reversed_low_mles = [0usize, 1, 2]
            .map(|slot| {
                stage0_eval_lsb20(
                    &local_y[slot * OWNER_BYTES..(slot + 1) * OWNER_BYTES],
                    &reversed_blocks[..20],
                )
            });
        let reversed_slices = [
            (1023, reversed_low_mles[0]),
            (1982, reversed_low_mles[1]),
            (1983, reversed_low_mles[2]),
        ];
        assert_ne!(
            stage0_global_x_mle(&reversed_slices, &reversed_blocks).unwrap(),
            x_1023,
            "[owner11,wire20] block reversal escaped virtual global X MLE",
        );

        for (slot, wire, label) in [
            (0usize, crate::legacy_envelope_map::T_LOCAL + 7, "owner1023 T"),
            (1, crate::legacy_envelope_map::D_LOCAL + 11, "owner1982 D"),
            (2, crate::legacy_envelope_map::T_LOCAL + 5, "owner1983 T"),
        ] {
            let mut mutated = local_y.clone();
            let global_local_wire = slot * STAGE0_GLOBAL_WIRES + wire;
            mutated[global_local_wire / 8] ^= 1 << (global_local_wire % 8);
            let residuals = stage0_residuals(&local_terms, |index| stage0_local_read(&mutated, index)).unwrap();
            assert_ne!(rebased_residuals, residuals, "{label} bit mutation escaped Map residual check");
        }

        let mut nonzero_slot3 = local_y.clone();
        nonzero_slot3[3 * OWNER_BYTES] |= 1;
        let nonzero_mle = (0..4).fold(Fr::zero(), |sum, slot| {
            sum + stage0_eq_at_point(&[t0, t1], slot) * stage0_eval_lsb20(
                &nonzero_slot3[slot * OWNER_BYTES..(slot + 1) * OWNER_BYTES],
                &wire_point,
            )
        });
        assert_ne!(projected, nonzero_mle, "nonzero fourth slot escaped projection check");

        let shifted_terms = stage0_rebase_terms(&terms, 1, false).unwrap();
        let shifted_residuals = stage0_residuals(&shifted_terms, |index| stage0_local_read(&local_y, index)).unwrap();
        assert_ne!(rebased_residuals, shifted_residuals, "output-row shift escaped residual map comparison");
        let mut colliding_rows = local_terms.clone();
        colliding_rows[0].row = 17;
        assert!(stage0_check_pin_rows_disjoint(&colliding_rows)
            .unwrap_err().contains("q1 pin row collision"));
        assert!(stage0_rebase_terms(&terms, STAGE0_LOCAL_ROWS, false)
            .unwrap_err().contains("outside log19"));

        let substituted_q1 = &expected_q1 ^ BigUint::from(1u8);
        let q1_fault = stage0_pin_residuals(&local_y, &substituted_q1);
        assert_eq!(q1_fault.values().filter(|residual| !residual.is_zero()).count(), 1);
        assert_ne!(expected_q1, substituted_q1, "q1 public-only substitution was not distinct");

        println!("STAGE0_PHASE isolated_negatives_ms={}", started.elapsed().as_millis());
        println!("STAGE0_TOTAL elapsed_ms={}", started.elapsed().as_millis());
    }

    fn c520_synthetic_h21_binding(owner: usize) -> HeaderSourceBinding {
        let mut profile_bytes = fixed::PROFILE_PREFIX.to_vec();
        profile_bytes.extend_from_slice(&crate::header_order::MAINNET_GENESIS);
        HeaderSourceBinding::from_sink_for_test(
            [0x52; 32],
            [0x53; 28],
            Blake2b::<U32>::digest(profile_bytes).into(),
            crate::bank53_map::CutDescriptor::eligible08().canonical_identity(),
            owner,
        )
    }

    #[test]
    fn c520_full_zero_n3_actual_producer_pipeline_capture() {
        use crate::daa_history_roster::OwnerClass;
        let (input, plan) = small_input_and_plan(3);
        let producer = NativeOwnerProducer::new_for_history(&plan, &input).unwrap();
        for (owner, class) in [
            (0usize, OwnerClass::Genesis),
            (1, OwnerClass::Initial),
            (3, OwnerClass::Padding),
        ] {
            assert_eq!(producer.roster.owner_class(owner as u64).unwrap(), class);
            let mut source = None;
            let row = producer.produce_inner(
                owner, AssemblyFault::None, None, None, false, None,
                Some(&mut source),
            ).expect("N=3 real owner assembly with prepack FullZero capture");
            assert_eq!((row.owner(), row.class()), (owner, class));
            let DaaSourcePayload::FullZero(claims) = source
                .expect("N=3 actual producer returned FullZero claims") else {
                panic!("N=3 producer returned a different DAA source");
            };
            claims.check_identity(owner as u64, class).unwrap();
            check_full_zero_packed_banks(row.packed_bytes(), &claims,
                owner as u64, class).unwrap();
        }
        println!("C520_N3_WRITER_PIPELINE_PASS owners=[0,1,3] exclusive_prepack=true full_zero_capture=true h21_lease=false");
    }

    #[test]
    fn c520_full_zero_n3_exclusive_writer_capture_before_h21_binding() {
        use crate::daa_history_roster::OwnerClass;
        let (input, plan) = small_input_and_plan(3);
        let producer = NativeOwnerProducer::new_for_history(&plan, &input).unwrap();

        let binding_error = producer
            .produce_with_full_zero_daa_source_lease(0)
            .err()
            .expect("N=3 must not mint an H21 DAA source lease");
        assert!(binding_error.contains("fixed H21 owner/plan"), "{binding_error}");

        for (owner, expected_class) in [
            (0usize, OwnerClass::Genesis),
            (1, OwnerClass::Initial),
            (3, OwnerClass::Padding),
        ] {
            let class = producer.roster.owner_class(owner as u64).unwrap();
            assert_eq!(class, expected_class);
            let mut rows = OwnedRows::new(OwnerSelection::Single { owner, class });
            let claims = producer.claim_full_zero_banks(owner, class, &mut rows).unwrap();
            claims.check_identity(owner as u64, class).unwrap();
            assert_eq!(claims.banks.len(), 4);
            assert_eq!(claims.banks.iter().map(|bank| bank.claimed_bits).sum::<usize>(), 81_920);
            assert_eq!(rows.claimed[0].iter().filter(|claimed| **claimed).count(), 81_920);

            let packed = rows.bytes(0).unwrap();
            check_full_zero_packed_banks(&packed, &claims, owner as u64, class).unwrap();
            for &(start, end) in &BANKS {
                for wire in start..end {
                    assert!(rows.claimed[0][wire], "owner{owner} bank wire{wire} was not claimed");
                    assert!(rows.values[0][wire].is_zero(), "owner{owner} bank wire{wire} not zero");
                    assert!(!bit(&packed, wire), "owner{owner} packed bank wire{wire} not zero");
                }
            }

            let missing_wire = BANKS[0].0;
            rows.claimed[0][missing_wire] = false;
            let missing = claims.check_claimed_rows(&rows, owner)
                .err().expect("missing exclusive zero write must be detected");
            assert!(missing.contains("missing or changed exclusive zero claim"), "{missing}");
            rows.claimed[0][missing_wire] = true;

            let before_values = rows.values[0].clone();
            let before_claimed = rows.claimed[0].clone();
            let duplicate = producer.claim_full_zero_banks(owner, class, &mut rows)
                .err().expect("a second equal-zero writer must conflict");
            assert!(duplicate.contains("exclusive claim overlaps"), "{duplicate}");
            assert_eq!(rows.values[0], before_values);
            assert_eq!(rows.claimed[0], before_claimed);
        }

        assert_eq!(producer.roster.owner_class(2).unwrap(), OwnerClass::Carry);
        let carry_error = producer.produce_with_full_zero_daa_source_lease(2)
            .err().expect("Carry remains on the CarryZero path");
        assert!(carry_error.contains("full-template owner"), "{carry_error}");
    }

    #[test]
    fn c520_full_zero_synthetic_h21_lease_checks_binding_class_author_and_reads() {
        use crate::daa_history_roster::OwnerClass;
        let (input, plan) = small_input_and_plan(3);
        let source = NativeOwnerProducer::new_for_history(&plan, &input).unwrap();
        let cases = [
            (0usize, OwnerClass::Genesis),
            (1, OwnerClass::Initial),
            (417_791, OwnerClass::FixedV2),
            (1_024, OwnerClass::Singleton),
            (1_827_840, OwnerClass::Padding),
        ];

        for (owner, class) in cases {
            // Synthetic lease checks exercise H21-shaped bindings only; this N=3
            // producer is a borrow anchor, not an H21 source producer.
            let binding = c520_synthetic_h21_binding(owner);
            let lease = NativeDaaSourceLease::synthetic_full_zero_for_test(
                &source, binding.clone(), class,
            );
            lease.check_full_zero_source(&binding).unwrap();
            let base = owner * WIDTH;
            for &(start, end) in &BANKS {
                assert_eq!(lease.read_daa_bit(&binding, base + start).unwrap(), Some(false));
                assert_eq!(lease.read_daa_bit(&binding, base + end - 1).unwrap(), Some(false));
            }
            assert_eq!(lease.read_daa_bit(&binding, base).unwrap(), None);
            assert_eq!(lease.read_daa_bit(&binding, base + BANKS[0].1).unwrap(), None);
            assert!(lease.read_daa_bit(&binding, base + WIDTH + BANKS[0].0).is_err());
            assert_eq!(lease.read_count_for_test(), 8);

            for field in 0..6 {
                assert!(lease.check_full_zero_source(&binding.mutated_field_for_test(field)).is_err(),
                    "source binding field {field}");
            }

            let claims = match &lease.source {
                DaaSourcePayload::FullZero(claims) => claims,
                _ => panic!("synthetic FullZero payload changed"),
            };
            let zero_bytes = vec![0u8; OWNER_BYTES];
            check_full_zero_packed_banks(&zero_bytes, claims, owner as u64, class).unwrap();
            let mut nonzero_bytes = zero_bytes;
            nonzero_bytes[BANKS[0].0 / 8] |= 1 << (BANKS[0].0 % 8);
            assert!(check_full_zero_packed_banks(&nonzero_bytes, claims, owner as u64, class)
                .unwrap_err().contains("final packed banks"));

            let mut wrong_author = NativeDaaSourceLease::synthetic_full_zero_for_test(
                &source, binding.clone(), class,
            );
            wrong_author.wrong_author_mutant_for_test();
            assert!(wrong_author.check_full_zero_source(&binding).is_err());

            let mut wrong_owner = NativeDaaSourceLease::synthetic_full_zero_for_test(
                &source, binding.clone(), class,
            );
            if let DaaSourcePayload::FullZero(claims) = &mut wrong_owner.source {
                claims.owner += 1;
            }
            assert!(wrong_owner.check_full_zero_source(&binding).is_err());

            let mut wrong_domain = NativeDaaSourceLease::synthetic_full_zero_for_test(
                &source, binding.clone(), class,
            );
            if let DaaSourcePayload::FullZero(claims) = &mut wrong_domain.source {
                claims.banks[0].start += 1;
            }
            assert!(wrong_domain.check_full_zero_source(&binding).is_err());

            let mut shortened_domain = NativeDaaSourceLease::synthetic_full_zero_for_test(
                &source, binding.clone(), class,
            );
            if let DaaSourcePayload::FullZero(claims) = &mut shortened_domain.source {
                claims.banks[0].end -= 8;
                claims.banks[0].claimed_bits -= 8;
            }
            assert!(shortened_domain.check_full_zero_source(&binding).is_err());

            let mut missing_domain = NativeDaaSourceLease::synthetic_full_zero_for_test(
                &source, binding.clone(), class,
            );
            if let DaaSourcePayload::FullZero(claims) = &mut missing_domain.source {
                claims.banks[0].claimed_bits -= 1;
            }
            assert!(missing_domain.check_full_zero_source(&binding).is_err());

            let mut duplicate_domain = NativeDaaSourceLease::synthetic_full_zero_for_test(
                &source, binding.clone(), class,
            );
            if let DaaSourcePayload::FullZero(claims) = &mut duplicate_domain.source {
                let first = claims.banks[0];
                claims.banks.push(first);
            }
            assert!(duplicate_domain.check_full_zero_source(&binding).is_err());

            let mut wrong_payload = NativeDaaSourceLease::synthetic_full_zero_for_test(
                &source, binding.clone(), class,
            );
            let wrong_claims = match &wrong_payload.source {
                DaaSourcePayload::FullZero(claims) => claims.clone(),
                _ => panic!("synthetic FullZero payload changed"),
            };
            wrong_payload.source = DaaSourcePayload::CarryZero(CarryZeroBankClaims {
                owner: wrong_claims.owner,
                class: OwnerClass::Carry,
                banks: wrong_claims.banks.iter().map(|bank| CarryZeroBankClaim {
                    start: bank.start,
                    end: bank.end,
                    claimed_bits: bank.claimed_bits,
                }).collect(),
            });
            assert!(wrong_payload.check_full_zero_source(&binding).is_err());
        }

        for class in [
            OwnerClass::Carry,
            OwnerClass::M1,
            OwnerClass::Short(crate::short_daa_layout::Profile::M2),
            OwnerClass::Mature(crate::daa_integer::Epoch::Legacy),
        ] {
            let binding = c520_synthetic_h21_binding(2);
            let lease = NativeDaaSourceLease::synthetic_full_zero_for_test(
                &source, binding.clone(), class,
            );
            assert!(lease.check_full_zero_source(&binding).is_err(), "class {class:?}");
        }
    }
}

/// Timing and immutable source for the sixteen-row diagnostic window.
#[cfg(test)]
pub(crate) struct NativeWindowFile {
    pub(crate) source: crate::packed::PackedFile,
    pub(crate) production_ns: u128,
    pub(crate) write_ns: u128,
    pub(crate) finish_ns: u128,
}

/// A cost/byte-join diagnostic for original owners 0..16, not the N3073 domain.
/// No collector or packed-source admission for the full domain is implied.
#[cfg(test)]
pub(crate) fn write_native_window_for_test(
    producer: &NativeOwnerProducer<'_>,
    path: &std::path::Path,
    owner_count: usize,
    mut produce: impl FnMut(usize) -> Result<NativePackedRow, String>,
) -> Result<NativeWindowFile, String> {
    producer.reject_legacy_for_test()?;
    if producer.max_adapter.is_some() {
        return Err("legacy native window collector has no MAX binding transport".into());
    }
    if owner_count != 16 {
        return Err("native window collector requires original owners 0..16".into());
    }
    // Admit the entire finite callback window before creating a destination.
    // Retain packed bytes (~2 MiB), never expanded field rows.
    let mut admitted = Vec::with_capacity(owner_count);
    let mut production_ns = 0u128;
    let mut write_ns = 0u128;
    for owner in 0..owner_count {
        let started = std::time::Instant::now();
        let row = produce(owner)?;
        row.reject_legacy_for_test()?;
        if row.max_binding.is_some() {
            return Err("legacy native window collector rejects MAX rows".into());
        }
        production_ns += started.elapsed().as_nanos();
        if row.owner != owner {
            return Err(format!("native window original owner mismatch at {owner}"));
        }
        if row.root != producer.input.root || row.total != producer.input.total {
            return Err(format!("native window root/total mismatch at {owner}"));
        }
        if row.class != producer.roster.owner_class(owner as u64)? {
            return Err(format!("native window class mismatch at {owner}"));
        }
        if row.bytes.len() != OWNER_BYTES {
            return Err(format!("native window row length mismatch at {owner}"));
        }
        admitted.push(row);
    }
    let mut writer = crate::packed::PackedFileWriter::create_new(path, 24)?;
    for row in admitted {
        let started = std::time::Instant::now();
        writer.write_bytes(&row.bytes)?;
        write_ns += started.elapsed().as_nanos();
    }
    let started = std::time::Instant::now();
    let source = writer.finish()?;
    let finish_ns = started.elapsed().as_nanos();
    Ok(NativeWindowFile {
        source,
        production_ns,
        write_ns,
        finish_ns,
    })
}

/// Metadata-only collector fixtures; these bytes do not claim row algebra.
#[cfg(test)]
pub(crate) fn metadata_native_row_for_test(
    producer: &NativeOwnerProducer<'_>, owner: usize,
) -> Result<NativePackedRow, String> {
    producer.require_unadapted_cache_for_test()?;
    if owner >= producer.plan.slots() { return Err("metadata owner outside domain".into()); }
    Ok(NativePackedRow { owner, class: producer.roster.owner_class(owner as u64)?,
        root: producer.input.root, total: producer.input.total, bytes: vec![0;OWNER_BYTES],
        header_source_binding: None,
        cap0_source: None,
        cap1_source: None,
        max_binding: None, map_binding: None, map_context: None, legacy_binding: None })
}

#[cfg(test)]
pub(crate) fn legacy_old_seeder_conflict_for_test(
    producer: &NativeOwnerProducer<'_>,
    adapter: &crate::legacy_native_adapter::LegacyNativeAdapter<'_>, owner: usize,
) -> Result<(), String> {
    producer.require_unadapted_cache_for_test()?;
    adapter.check(producer.plan, producer.input)?;
    let selection = OwnerSelection::Single { owner, class: producer.roster.owner_class(owner as u64)? };
    let mut rows = OwnedRows::new(selection);
        seed_header_from_template(&producer.header_template, producer.plan, None, None,
            producer.input, owner, &mut rows, None, None, None, false, None, None, None)?;
    for (offset, bit) in adapter.helpers(owner)?.into_iter().enumerate() {
        rows.claim(owner, crate::legacy_envelope_map::BASE+offset, Fr::from(bit as u64))?;
    }
    Ok(())
}

#[cfg(test)]
#[derive(Clone, Copy)]
pub(crate) enum NativeRowFileFault {
    Root,
    Total,
    Class,
    Length,
}

/// Isolated metadata/size negatives at the collector boundary only.
#[cfg(test)]
pub(crate) fn native_row_file_fault_for_test(
    mut row: NativePackedRow,
    fault: NativeRowFileFault,
) -> NativePackedRow {
    match fault {
        NativeRowFileFault::Root => row.root[0] ^= 1,
        NativeRowFileFault::Total => row.total[0] ^= 1,
        NativeRowFileFault::Class => {
            row.class = if row.class == crate::daa_history_roster::OwnerClass::Genesis {
                crate::daa_history_roster::OwnerClass::Carry
            } else {
                crate::daa_history_roster::OwnerClass::Genesis
            };
        }
        NativeRowFileFault::Length => {
            row.bytes.pop();
        }
    }
    row
}

/// Checkpoint validation of all owner-local families and all eleven cores.
/// Global incident topology, reverse imports, commitment and PCS are separate.
#[cfg(test)]
pub(crate) fn validate_native_row_for_test(
    plan: &WorkTreeHistoryPlan,
    input: &NativePrefix,
    row: &NativePackedRow,
    read_bit: impl FnMut(usize) -> Result<bool, String>,
) -> Result<AssemblyReceipt, String> {
    if plan.headers() != PREFIX_HEADERS as u64 || plan.slot_log() != 12 || plan.slots() != 4096 {
        return Err("native row validation requires N3073/S12".into());
    }
    validate_native_row_for_history_test(plan, input, row, read_bit)
}

#[cfg(test)]
pub(crate) fn validate_native_row_for_history_test(
    plan: &WorkTreeHistoryPlan,
    input: &NativePrefix,
    row: &NativePackedRow,
    read_bit: impl FnMut(usize) -> Result<bool, String>,
) -> Result<AssemblyReceipt, String> {
    validate_native_row_inner(plan, input, row, read_bit, None, None)
}

/// MAX foreign D and helper exports are derived from the same immutable X.
#[cfg(test)]
pub(crate) fn validate_native_max_row_for_history_test(
    adapter: &crate::max_header_adapter::MaxHeaderAdapter<'_>,
    input: &NativePrefix,
    row: &NativePackedRow,
) -> Result<AssemblyReceipt, String> {
    row.reject_legacy_for_test()?;
    let exports = crate::native_owner_exports::NativeExports::new_for_history(adapter.parent(), input)?;
    let mut helpers = BTreeMap::<usize, Vec<Fr>>::new();
    validate_native_row_inner(adapter.parent(), input, row, |index| {
        let owner = index / WIDTH;
        let local = index % WIDTH;
        if (crate::max_header_adapter::BASE..crate::max_header_adapter::BASE+crate::suffix_max::HELPERS).contains(&local) {
            if !helpers.contains_key(&owner) { helpers.insert(owner, adapter.helpers(input, owner)?); }
            Ok(helpers[&owner][local-crate::max_header_adapter::BASE] == Fr::one())
        } else { exports.bit(index) }
    }, Some(adapter), None)
}

#[cfg(test)]
pub(crate) fn validate_native_legacy_row_for_history_test(
    adapter: &crate::legacy_native_adapter::LegacyNativeAdapter<'_>,
    input: &NativePrefix, owner: usize, row: &NativePackedRow,
    read_bit: impl FnMut(usize) -> Result<bool, String>,
) -> Result<AssemblyReceipt, String> {
    adapter.check(adapter.parent(), input)?;
    row.admit_legacy_for_test(adapter, owner)?;
    validate_native_row_inner(adapter.parent(), input, row, read_bit, None, Some(adapter))
}

#[cfg(test)]
fn validate_native_row_inner(
    plan: &WorkTreeHistoryPlan,
    input: &NativePrefix,
    row: &NativePackedRow,
    read_bit: impl FnMut(usize) -> Result<bool, String>,
    max_adapter: Option<&crate::max_header_adapter::MaxHeaderAdapter<'_>>,
    legacy_adapter: Option<&crate::legacy_native_adapter::LegacyNativeAdapter<'_>>,
) -> Result<AssemblyReceipt, String> {
    if let Some(adapter) = legacy_adapter {
        adapter.check(plan, input)?;
        row.admit_legacy_for_test(adapter, row.owner)?;
        if max_adapter.is_some() { return Err("legacy native MAX mixing".into()); }
    } else { row.reject_legacy_for_test()?; }
    validate_native_plan_input(plan, input)?;
    if let Some(adapter) = max_adapter {adapter.check_parent(plan)?;}
    if row.max_binding != max_adapter.map(|adapter| adapter.binding()) {
        return Err("native row MAX consumer binding mismatch".into());
    }
    let roster = DaaHistoryRoster::compile(plan)?;
    if row.owner >= plan.slots()
        || row.root != input.root
        || row.total != input.total
        || plan.descriptor().root != input.root
        || plan.work_profile().total_be28 != input.total
        || row.bytes.len() != OWNER_BYTES
        || roster.owner_class(row.owner as u64)? != row.class
    {
        return Err("native row validation binding mismatch".into());
    }
    let selection = OwnerSelection::Single {
        owner: row.owner,
        class: row.class,
    };
    let mut rows = OwnedRows::new(selection);
    for wire in 0..WIDTH {
        rows.claim(
            row.owner,
            wire,
            Fr::from(((row.bytes[wire / 8] >> (wire % 8)) & 1) as u64),
        )?;
    }
    let mut groups = local_groups(plan, &roster, selection, max_adapter)?;
    if let Some(adapter) = legacy_adapter {
        groups.push(Group { name: format!("LegacyMap/{}", row.owner),
            terms: adapter.terms(row.owner)? });
    }
    let mut support = BTreeSet::new();
    for group in &groups {
        for term in &group.terms {
            reads(term, &mut |index| {
                add_foreign(selection, plan.slots() * WIDTH, &mut support, index)
            })?;
        }
    }
    let mut reader = ForeignReader {
        read: read_bit,
        support,
        cache: BTreeMap::new(),
    };
    check_cores(&rows)?;
    for group in &mut groups {
        check_group(group, &rows, &mut reader)?;
    }
    Ok(AssemblyReceipt {
        external_cells: reader.cache.len(),
        foreign_census: reader.support.len(),
        groups: groups
            .iter()
            .map(|g| (g.name.clone(), g.terms.len()))
            .collect(),
    })
}

#[cfg(test)]
pub(crate) fn flip_native_row_bit_for_test(
    row: &mut NativePackedRow,
    wire: usize,
) -> Result<(), String> {
    if wire >= WIDTH {
        return Err("native row mutant outside owner".into());
    }
    row.bytes[wire / 8] ^= 1 << (wire % 8);
    Ok(())
}

#[cfg(test)]
pub(crate) fn mutate_native_row_parent_for_test(row: &mut NativePackedRow) {
    row.root[0] ^= 1;
}

#[cfg(test)]
pub(crate) fn truncate_native_row_for_test(row: &mut NativePackedRow) {
    row.bytes.pop();
}

pub(crate) fn assemble_window(
    plan: &WorkTreeHistoryPlan,
    input: &NativePrefix,
    read_bit: impl FnMut(usize) -> Result<bool, String>,
) -> Result<PreparedOwnerWindow, String> {
    assemble_inner(
        plan,
        input,
        read_bit,
        OwnerSelection::M2,
        AssemblyFault::None,
    )
}
pub(crate) fn assemble_m1_window(
    plan: &WorkTreeHistoryPlan,
    input: &NativePrefix,
    read_bit: impl FnMut(usize) -> Result<bool, String>,
) -> Result<PreparedOwnerWindow, String> {
    assemble_inner(
        plan,
        input,
        read_bit,
        OwnerSelection::M1,
        AssemblyFault::None,
    )
}
#[cfg(test)]
pub(crate) fn assemble_window_fault_for_test(
    plan: &WorkTreeHistoryPlan,
    input: &NativePrefix,
    read_bit: impl FnMut(usize) -> Result<bool, String>,
    fault: AssemblyFault,
) -> Result<PreparedOwnerWindow, String> {
    assemble_inner(plan, input, read_bit, OwnerSelection::M2, fault)
}
#[cfg(test)]
pub(crate) fn assemble_m1_window_fault_for_test(
    plan: &WorkTreeHistoryPlan,
    input: &NativePrefix,
    read_bit: impl FnMut(usize) -> Result<bool, String>,
    fault: AssemblyFault,
) -> Result<PreparedOwnerWindow, String> {
    assemble_inner(plan, input, read_bit, OwnerSelection::M1, fault)
}

fn assemble_inner<F: FnMut(usize) -> Result<bool, String>>(
    plan: &WorkTreeHistoryPlan,
    input: &NativePrefix,
    read_bit: F,
    selection: OwnerSelection,
    fault: AssemblyFault,
) -> Result<PreparedOwnerWindow, String> {
    if plan.headers() != 3073 || plan.slot_log() != 12 || plan.slots() != 4096 {
        return Err("assembly requires N3073/S12".into());
    }
    if plan.descriptor().root != input.root || plan.work_profile().total_be28 != input.total {
        return Err("assembly native prefix root/total mismatch".into());
    }
    let roster = DaaHistoryRoster::compile(plan)?;
    let first_owner = selection.first_owner();
    let child_height = selection.child_height();
    if roster.owner_class(first_owner as u64)? != crate::daa_history_roster::OwnerClass::Carry
        || roster.owner_class((first_owner + 1) as u64)? != selection.terminal_class()
    {
        return Err("assembly owner class mismatch".into());
    }
    let schedule = crate::daa_header_window::for_child_height(child_height)?;
    if schedule.action()
        != crate::daa_header_window::Action::Retarget(crate::daa_integer::Epoch::Legacy)
        || schedule.sample_heights().last() != Some(&(child_height - 1))
    {
        return Err("assembly selected schedule mismatch".into());
    }
    let mut groups = groups(plan, &roster, selection)?;
    let support = census(&groups, plan, input, selection)?;
    let mut reader = ForeignReader {
        read: read_bit,
        support,
        cache: BTreeMap::new(),
    };
    let mut rows = OwnedRows::new(selection);
    for owner in selection.owners() {
        seed_header(
            plan,
            None,
            #[cfg(test)]
            None,
            input,
            owner,
            &mut rows,
            #[cfg(test)]
            None,
        )?;
        seed_tree(plan, input, owner, &mut rows, fault)?;
    }
    let samples = schedule
        .sample_heights()
        .iter()
        .map(|&h| input.raw(h as usize))
        .collect::<Result<Vec<_>, _>>()?;
    let window = crate::daa_history_producer::RawWindow {
        parent: input.raw(child_height as usize - 1)?,
        child: input.raw(child_height as usize)?,
        samples: &samples,
    };
    let mut patched = rows.bytes(1)?;
    crate::daa_history_producer::write_retarget(
        &roster,
        (first_owner + 1) as u64,
        window,
        &mut patched,
        |index| reader.get(&rows, index).map(|v| v == Fr::one()),
    )?;
    for (lo, hi) in BANKS {
        for wire in lo..hi {
            rows.claim(first_owner, wire, Fr::zero())?;
            rows.claim(
                first_owner + 1,
                wire,
                Fr::from(((patched[wire / 8] >> (wire % 8)) & 1) as u64),
            )?;
        }
    }
    #[cfg(test)]
    match fault {
        AssemblyFault::ConflictingClaim { owner, wire } => {
            let (r, w) = rows.local(owner as usize, wire)?;
            rows.claim(owner as usize, wire, Fr::one() - rows.values[r][w])?;
        }
        AssemblyFault::NonBooleanClaim { owner, wire } => {
            rows.claim(owner as usize, wire, Fr::from(2u64))?
        }
        AssemblyFault::MissingClaim { owner, wire } => {
            let (r, w) = rows.local(owner as usize, wire)?;
            rows.claimed[r][w] = false;
        }
        AssemblyFault::FlipBit { owner, wire } => {
            let (r, w) = rows.local(owner as usize, wire)?;
            rows.values[r][w] = Fr::one() - rows.values[r][w];
        }
        _ => {}
    }
    for row in 0..2 {
        if let Some(wire) = rows.claimed[row].iter().position(|x| !*x) {
            return Err(format!(
                "missing claim owner{} wire{wire}",
                first_owner + row
            ));
        }
    }
    // Packed Booleanity, all native cores, then every selected consumer family.
    let mut bytes = rows.bytes(0)?;
    bytes.extend(rows.bytes(1)?);
    check_cores(&rows)?;
    for group in &mut groups {
        check_group(group, &rows, &mut reader)?;
    }
    let receipt = AssemblyReceipt {
        external_cells: reader.cache.len(),
        foreign_census: reader.support.len(),
        groups: groups
            .iter()
            .map(|g| (g.name.clone(), g.terms.len()))
            .collect(),
    };
    Ok(PreparedOwnerWindow {
        selection,
        bytes,
        receipt,
    })
}

impl PreparedOwnerWindow {
    /// Creates an immutable local two-owner file only after the complete join.
    pub(crate) fn write_new(
        &self,
        path: impl AsRef<std::path::Path>,
    ) -> Result<crate::packed::PackedFile, String> {
        let mut writer = crate::packed::PackedFileWriter::create_new(path, 21)?;
        writer.write_bytes(&self.bytes)?;
        let source = writer.finish()?;
        for row in 0..2 {
            let expanded = crate::packed_rows::read_row(&source, WIDTH, row)?;
            for (wire, value) in expanded.iter().enumerate() {
                let expected =
                    Fr::from(((self.bytes[row * OWNER_BYTES + wire / 8] >> (wire % 8)) & 1) as u64);
                if *value != expected {
                    return Err("packed owner readback mismatch".into());
                }
            }
        }
        Ok(source)
    }
}

#[cfg(test)]
pub(crate) fn c498_physical_fixture(
    relation: &h21_eligible_context::H21ClosedScoreOwnerRelation<'_>,
    binding: &HeaderSourceBinding, lease: &Eligible08MapPairLease, context: usize,
) -> Result<(), String> {
    use crate::daa_history_roster::OwnerClass;
    let source = C498ClippedScoreSource::new(relation, binding, lease, context)?;
    let owner = binding.owner();
    let start = [677_501, 685_693][context];
    let plan = WorkTreeHistoryPlan::compile(1_827_840, 21, binding.root, binding.total)?;
    let mask = plan.physical_assignment_replacement_mask(owner as u64)?;
    let reserved = preflight_map_pair_reservation(lease, binding, owner, OwnerClass::Carry, &mask)?;
    let native = vec![Fr::zero(); WIDTH];
    let fresh = || -> Result<OwnedRows, String> {
        let mut rows = OwnedRows::new(OwnerSelection::Single { owner, class: OwnerClass::Carry });
        rows.begin_c496_clipped_header_zero_capture(binding.clone(), context, lease)?;
        rows.begin_c498_clipped_score_capture(&source)?;
        Ok(rows)
    };
    let prepared = || -> Result<OwnedRows, String> {
        let mut rows = fresh()?;
        rows.prepare_c498_and_c496_seed(owner, &mask, &reserved, &native, &BANKS)?;
        Ok(rows)
    };
    let seed = |rows: &mut OwnedRows, skip: Option<usize>| -> Result<(), String> {
        for &(wire, _, value) in relation.cells() {
            if Some(wire % WIDTH) != skip { rows.claim_c498_clipped_score(owner, wire % WIDTH, value)?; }
        }
        for local in c496_clipped_header_zero_locals(owner, context)? {
            rows.claim_header_seed(owner, local, Fr::zero())?;
        }
        claim_map_pair_live(rows, lease, binding, owner, OwnerClass::Carry)
    };
    let packed = |rows: &OwnedRows| -> Result<NativePackedRow, String> {
        Ok(NativePackedRow { owner, class: OwnerClass::Carry, root: binding.root,
            total: binding.total, bytes: rows.bytes(0)?, header_source_binding: Some(binding.clone()),
            cap0_source: None, cap1_source: None, max_binding: None, map_binding: None,
            map_context: None, legacy_binding: None })
    };
    // The last case passes Score preflight before failing the C496 preflight.
    // Every overlap is isolated at the last target, before any claim mutation.
    for fault in 0..7 {
        let mut rows = fresh()?;
        let mut wrong_mask = mask.clone();
        let mut wrong_reserved = reserved.clone();
        let mut wrong_native = native.clone();
        let mut banks = BANKS.to_vec();
        let last = start + 2_047;
        match fault {
            0 => wrong_mask[last] = true,
            1 => wrong_reserved[last] = true,
            2 => wrong_native[last] = Fr::one(),
            3 => banks.push((last, last + 1)),
            4 => rows.claimed[0][last] = true,
            5 => rows.c496_clipped_header_zero_capture.as_mut().unwrap().locals.push(last),
            6 => wrong_native[*rows.c496_clipped_header_zero_capture.as_ref()
                .unwrap().locals.last().unwrap()] = Fr::one(),
            _ => unreachable!(),
        }
        if fault == 5 { rows.c496_clipped_header_zero_capture.as_mut().unwrap().locals.sort_unstable(); }
        let values = rows.values[0].clone();
        let claims = rows.claimed[0].clone();
        assert!(rows.prepare_c498_and_c496_seed(owner, &wrong_mask,
            &wrong_reserved, &wrong_native, &banks).is_err(), "overlap fault {fault}");
        assert_eq!(rows.values[0], values);
        assert_eq!(rows.claimed[0], claims);
        assert!(!rows.c498_clipped_score_capture.as_ref().unwrap().prepared);
        assert!(!rows.c496_clipped_header_zero_capture.as_ref().unwrap().prepared);
        assert!(rows.c498_clipped_score_capture.as_ref().unwrap().cells.iter().all(Option::is_none));
        prepared()?;
    }
    // Prior equal-zero claims must reject at source admission, including padding.
    for local in [start, start + 1_994, start + 2_047] {
        let mut rows = OwnedRows::new(OwnerSelection::Single { owner, class: OwnerClass::Carry });
        rows.claim(owner, local, Fr::zero())?;
        rows.begin_c496_clipped_header_zero_capture(binding.clone(), context, lease)?;
        assert!(rows.begin_c498_clipped_score_capture(&source).is_err());
        assert!(rows.c498_clipped_score_capture.is_none());
    }
    for skip in [start, start + 1_994, start + 2_047] {
        let mut rows = prepared()?;
        seed(&mut rows, Some(skip))?;
        let row = packed(&rows)?;
        assert!(rows.check_c498_clipped_score_capture(&row, &source).is_err());
        assert!(rows.c496_clipped_header_zero_capture.is_some());
        assert!(rows.c498_clipped_score_capture.is_some());
    }
    for fault in 0..7 {
        let mut rows = if fault == 0 { fresh()? } else { prepared()? };
        let last = start + 2_047;
        if fault >= 2 { rows.claim_c498_clipped_score(owner, last, Fr::zero())?; }
        let values = rows.values[0].clone();
        let claims = rows.claimed[0].clone();
        let captured = rows.c498_clipped_score_capture.as_ref().unwrap().cells.clone();
        let result = match fault {
            0 => rows.claim_c498_clipped_score(owner, last, Fr::zero()),
            1 => rows.claim_c498_clipped_score(owner, last, Fr::one()),
            2 => rows.claim_c498_clipped_score(owner, last, Fr::zero()),
            3 => rows.claim(owner, last, Fr::zero()),
            4 => rows.claim_exclusive(owner, last, Fr::zero()),
            5 => rows.claim_header_seed(owner, last, Fr::zero()),
            6 => rows.claim_c498_clipped_score(owner - 1, last, Fr::zero()),
            _ => unreachable!(),
        };
        assert!(result.is_err(), "claim fault {fault}");
        assert_eq!(rows.values[0], values);
        assert_eq!(rows.claimed[0], claims);
        assert_eq!(rows.c498_clipped_score_capture.as_ref().unwrap().cells, captured);
    }
    let other_lease = Eligible08MapPairLease::synthetic_valid_for_test(binding.clone(),
        owner, OwnerClass::Carry, H21EligibleMapStage::source_maps()?)?;
    let other_source = C498ClippedScoreSource::new(relation, binding, &other_lease, context)?;
    for fault in 0..6 {
        let mut rows = prepared()?;
        seed(&mut rows, None)?;
        let mut row = packed(&rows)?;
        match fault {
            0 => row.bytes[(start + 2_047) / 8] ^= 1 << ((start + 2_047) % 8),
            1 => rows.claimed[0][start] = false,
            2 => rows.values[0][start] += Fr::one(),
            3 => rows.c498_clipped_score_capture.as_mut().unwrap().cells[0] = None,
            4 => rows.c498_clipped_score_capture.as_mut().unwrap().expected[0] += Fr::one(),
            5 => {},
            _ => unreachable!(),
        }
        assert!(rows.check_c498_clipped_score_capture(&row,
            if fault == 5 { &other_source } else { &source }).is_err(), "final fault {fault}");
        assert!(rows.c496_clipped_header_zero_capture.is_some());
    }
    let mut rows = prepared()?;
    seed(&mut rows, None)?;
    let row = packed(&rows)?;
    let cells = rows.check_c498_clipped_score_capture(&row, &source)?;
    assert!(rows.finish_c496_clipped_header_zero_capture(&row, &other_lease).is_err());
    let capture = rows.finish_c496_clipped_header_zero_capture(&row, lease)?;
    let mut result = C498ClippedScoreRow {
        header_zero: NativeClippedHeaderZeroRow { row, capture }, source, cells,
    };
    result.validate_for(binding, lease)?;
    assert_eq!(result.census(), (2_048, 8_545, 514, 2_822));
    assert!(result.validate_for(binding, &other_lease).is_err());
    for field in 0..6 {
        assert!(result.validate_for(&binding.mutated_field_for_test(field), lease).is_err());
        result.validate_for(binding, lease)?;
    }
    for local in [start, start + 1_994, start + 2_047,
        c496_clipped_header_zero_locals(owner, context)?[0]] {
        result.header_zero.row.bytes[local / 8] ^= 1 << (local % 8);
        assert!(result.validate_for(binding, lease).is_err());
        result.header_zero.row.bytes[local / 8] ^= 1 << (local % 8);
        result.validate_for(binding, lease)?;
    }
    Ok(())
}

#[cfg(test)]
mod c496_clipped_headerzero_tests {
    use super::*;
    use crate::daa_history_roster::OwnerClass;

    const OWNERS: [(usize, usize); 2] = [(1_810_904, 0), (1_810_841, 1)];

    fn sources(owner: usize) -> (HeaderSourceBinding, Eligible08MapPairLease) {
        let mut profile_bytes = fixed::PROFILE_PREFIX.to_vec();
        profile_bytes.extend_from_slice(&crate::header_order::MAINNET_GENESIS);
        let binding = HeaderSourceBinding::from_sink_for_test([7; 32], [8; 28],
            Blake2b::<U32>::digest(profile_bytes).into(),
            crate::bank53_map::CutDescriptor::eligible08().canonical_identity(), owner);
        let lease = Eligible08MapPairLease::synthetic_valid_for_test(binding.clone(),
            owner, OwnerClass::Carry, H21EligibleMapStage::source_maps().unwrap()).unwrap();
        (binding, lease)
    }

    fn fresh(binding: &HeaderSourceBinding, context: usize,
        lease: &Eligible08MapPairLease) -> OwnedRows {
        let mut rows = OwnedRows::new(OwnerSelection::Single {
            owner: binding.owner(), class: OwnerClass::Carry,
        });
        rows.begin_c496_clipped_header_zero_capture(binding.clone(), context, lease).unwrap();
        rows
    }

    fn reserved(binding: &HeaderSourceBinding, lease: &Eligible08MapPairLease,
        mask: &[bool]) -> Vec<bool> {
        preflight_map_pair_reservation(lease, binding, binding.owner(),
            OwnerClass::Carry, mask).unwrap()
    }

    fn prepared(binding: &HeaderSourceBinding, context: usize,
        lease: &Eligible08MapPairLease) -> OwnedRows {
        let mut rows = fresh(binding, context, lease);
        let mask = vec![false; WIDTH];
        rows.prepare_c496_clipped_header_zero_seed(binding.owner(), &mask,
            &reserved(binding, lease, &mask), &vec![Fr::zero(); WIDTH], &BANKS).unwrap();
        rows
    }

    fn seed(rows: &mut OwnedRows, skip: Option<usize>) {
        let capture = rows.c496_clipped_header_zero_capture.as_ref().unwrap();
        let owner = capture.binding.owner();
        let locals = capture.locals.clone();
        for local in locals {
            if skip != Some(local) { rows.claim_header_seed(owner, local, Fr::zero()).unwrap(); }
        }
    }

    fn packed(binding: &HeaderSourceBinding, rows: &OwnedRows) -> NativePackedRow {
        NativePackedRow { owner: binding.owner(), class: OwnerClass::Carry,
            root: binding.root, total: binding.total, bytes: rows.bytes(0).unwrap(),
            header_source_binding: Some(binding.clone()), cap0_source: None, cap1_source: None,
            max_binding: None, map_binding: None, map_context: None, legacy_binding: None }
    }

    fn complete<'m>(binding: &HeaderSourceBinding, context: usize,
        lease: &'m Eligible08MapPairLease) -> NativeClippedHeaderZeroRow<'m> {
        let mut rows = prepared(binding, context, lease);
        seed(&mut rows, None);
        claim_map_pair_live(&mut rows, lease, binding, binding.owner(), OwnerClass::Carry).unwrap();
        let row = packed(binding, &rows);
        let capture = rows.finish_c496_clipped_header_zero_capture(&row, lease).unwrap();
        NativeClippedHeaderZeroRow { row, capture }
    }

    #[test]
    fn c496_cheapest_policy_census_and_real_parent_masks_are_disjoint() {
        let plan = WorkTreeHistoryPlan::compile(1_827_840, 21, [7; 32], [8; 28]).unwrap();
        for (owner, context) in OWNERS {
            let (binding, lease) = sources(owner);
            assert_eq!(HeaderSourceBinding::for_plan(&plan, owner).unwrap(), binding);
            let locals = c496_clipped_header_zero_locals(owner, context).unwrap();
            assert_eq!(locals.len(), 2_822);
            let expected: Vec<_> = match context {
                0 => [679_549..679_936, 685_693..688_128],
                _ => [677_501..679_936, 687_741..688_128],
            }.into_iter().flatten().collect();
            assert_eq!(locals, expected);
            let mask = plan.physical_assignment_replacement_mask(owner as u64).unwrap();
            let map_reserved = reserved(&binding, &lease, &mask);
            let mut rows = fresh(&binding, context, &lease);
            rows.prepare_c496_clipped_header_zero_seed(owner, &mask, &map_reserved,
                &vec![Fr::zero(); WIDTH], &BANKS).unwrap();
            assert!(rows.claimed[0].iter().all(|claimed| !claimed));
            assert!(!locals.contains(&(BANK53_BASE + context * BANK53_CONTEXT_BITS + 5_757)));
            assert!(!locals.contains(&(BANK53_BASE + context * BANK53_CONTEXT_BITS + 7_804)));
        }
    }

    #[test]
    fn c496_complete_synthetic_claim_to_packed_controls() {
        for (owner, context) in OWNERS {
            let (binding, lease) = sources(owner);
            let result = complete(&binding, context, &lease);
            assert_eq!(result.capture.cells.len(), 2_822);
            result.validate_for(&binding, &lease).unwrap();
        }
    }

    fn preseed_fault(fault: usize) {
        for (owner, context) in OWNERS {
            let (binding, lease) = sources(owner);
            let mut rows = fresh(&binding, context, &lease);
            let target = *rows.c496_clipped_header_zero_capture.as_ref().unwrap().locals.last().unwrap();
            let mut mask = vec![false; WIDTH];
            let mut map_reserved = reserved(&binding, &lease, &mask);
            let mut native = vec![Fr::zero(); WIDTH];
            let mut daa = BANKS.to_vec();
            match fault {
                0 => mask[target] = true,
                1 => map_reserved[target] = true,
                2 => native[target] = Fr::one(),
                3 => daa.push((target, target + 1)),
                _ => panic!("unknown isolated C496 preseed fault"),
            }
            assert!(rows.prepare_c496_clipped_header_zero_seed(owner, &mask,
                &map_reserved, &native, &daa).is_err());
            assert!(!rows.c496_clipped_header_zero_capture.as_ref().unwrap().prepared);
            assert!(rows.c496_clipped_header_zero_capture.as_ref().unwrap().cells
                .iter().all(|cell| cell.is_none()));
            assert!(rows.claimed[0].iter().all(|claimed| !claimed));
            assert!(rows.values[0].iter().all(|value| value.is_zero()));
        }
    }

    #[test] fn c496_rejects_replacement_mask_before_first_target() { preseed_fault(0); }
    #[test] fn c496_rejects_map_reservation_before_first_target() { preseed_fault(1); }
    #[test] fn c496_rejects_native_nonzero_before_first_target() { preseed_fault(2); }
    #[test] fn c496_rejects_daa_bank_before_first_target() { preseed_fault(3); }

    #[test]
    fn c496_rejects_preexisting_equal_zero_target_claim() {
        let (binding, lease) = sources(1_810_904);
        let mut rows = fresh(&binding, 0, &lease);
        let target = rows.c496_clipped_header_zero_capture.as_ref().unwrap().locals[0];
        rows.claim(binding.owner(), target, Fr::zero()).unwrap();
        let mask = vec![false; WIDTH];
        assert!(rows.prepare_c496_clipped_header_zero_seed(binding.owner(), &mask,
            &reserved(&binding, &lease, &mask), &vec![Fr::zero(); WIDTH], &BANKS).is_err());
        assert!(rows.c496_clipped_header_zero_capture.as_ref().unwrap().cells
            .iter().all(|cell| cell.is_none()));
    }

    #[test]
    fn c496_rejects_unprepared_nonzero_duplicate_and_later_equal_zero_separately() {
        for (owner, context) in OWNERS {
            let (binding, lease) = sources(owner);
            let target = c496_clipped_header_zero_locals(owner, context).unwrap()[0];
            let mut unprepared = fresh(&binding, context, &lease);
            assert!(unprepared.claim_header_seed(owner, target, Fr::zero()).is_err());
            for fault in 0..4 {
                let mut rows = prepared(&binding, context, &lease);
                if fault != 0 { rows.claim_header_seed(owner, target, Fr::zero()).unwrap(); }
                let before = rows.c496_clipped_header_zero_capture.as_ref().unwrap().cells.clone();
                let claimed_before = rows.claimed[0][target];
                let result = match fault {
                    0 => rows.claim_header_seed(owner, target, Fr::one()),
                    1 => rows.claim_header_seed(owner, target, Fr::zero()),
                    2 => rows.claim(owner, target, Fr::zero()),
                    _ => rows.claim_exclusive(owner, target, Fr::zero()),
                };
                assert!(result.is_err(), "isolated claim fault {fault}");
                assert_eq!(before, rows.c496_clipped_header_zero_capture.as_ref().unwrap().cells);
                assert_eq!(rows.claimed[0][target], claimed_before);
                assert!(rows.values[0][target].is_zero());
            }
        }
    }

    #[test]
    fn c496_rejects_missing_first_and_last_of_each_interval() {
        for (owner, context) in OWNERS {
            let (binding, lease) = sources(owner);
            let boundaries = if context == 0 { [679_549, 679_935, 685_693, 688_127] }
                else { [677_501, 679_935, 687_741, 688_127] };
            for missing in boundaries {
                let mut rows = prepared(&binding, context, &lease);
                seed(&mut rows, Some(missing));
                let row = packed(&binding, &rows);
                assert!(rows.finish_c496_clipped_header_zero_capture(&row, &lease).is_err());
                assert!(rows.c496_clipped_header_zero_capture.is_some());
            }
        }
    }

    #[test]
    fn c496_rejects_foreign_owner_and_swapped_or_invalid_context() {
        for (owner, context) in OWNERS {
            let (binding, lease) = sources(owner);
            let mut rows = OwnedRows::new(OwnerSelection::Single {
                owner: owner + 1, class: OwnerClass::Carry });
            assert!(rows.begin_c496_clipped_header_zero_capture(binding.clone(), context, &lease).is_err());
            for wrong_context in [context ^ 1, 2] {
                let mut rows = OwnedRows::new(OwnerSelection::Single { owner, class: OwnerClass::Carry });
                assert!(rows.begin_c496_clipped_header_zero_capture(binding.clone(), wrong_context, &lease).is_err());
            }
            let mut rows = prepared(&binding, context, &lease);
            let target = c496_clipped_header_zero_locals(owner, context).unwrap()[0];
            assert!(rows.claim_header_seed(owner + 1, target, Fr::zero()).is_err());
            assert!(rows.c496_clipped_header_zero_capture.as_ref().unwrap().cells.iter().all(|cell| cell.is_none()));
        }
    }

    #[test]
    fn c496_rejects_each_binding_field_and_foreign_lease_at_consumer() {
        for (owner, context) in OWNERS {
            let (binding, lease) = sources(owner);
            let result = complete(&binding, context, &lease);
            for field in 0..6 {
                assert!(result.validate_for(&binding.mutated_field_for_test(field), &lease).is_err());
            }
            let cloned_lease = lease.clone();
            assert!(result.validate_for(&binding, &cloned_lease).is_err());
            result.validate_for(&binding, &lease).unwrap();
        }
    }

    #[test]
    fn c496_rejects_cut_profile_layout_and_lease_before_capture() {
        let (binding, lease) = sources(1_810_904);
        for field in [2, 3, 4] {
            let mut rows = OwnedRows::new(OwnerSelection::Single { owner: binding.owner(), class: OwnerClass::Carry });
            assert!(rows.begin_c496_clipped_header_zero_capture(binding.mutated_field_for_test(field), 0, &lease).is_err());
            assert!(rows.c496_clipped_header_zero_capture.is_none());
        }
        let (_, foreign_lease) = sources(1_810_841);
        let mut rows = OwnedRows::new(OwnerSelection::Single { owner: binding.owner(), class: OwnerClass::Carry });
        assert!(rows.begin_c496_clipped_header_zero_capture(binding, 0, &foreign_lease).is_err());
    }

    #[test]
    fn c496_rejects_equal_binding_lease_substitution_at_finish() {
        let (binding, lease) = sources(1_810_904);
        let other_lease = lease.clone();
        let mut rows = prepared(&binding, 0, &lease);
        seed(&mut rows, None);
        let row = packed(&binding, &rows);
        assert!(rows.finish_c496_clipped_header_zero_capture(&row, &other_lease).is_err());
        assert!(rows.c496_clipped_header_zero_capture.is_some());
        assert!(rows.finish_c496_clipped_header_zero_capture(&row, &lease).is_ok());
    }

    #[test]
    fn c496_rejects_final_packed_bit_mutation() {
        for (owner, context) in OWNERS {
            let (binding, lease) = sources(owner);
            let mut rows = prepared(&binding, context, &lease);
            seed(&mut rows, None);
            let mut row = packed(&binding, &rows);
            let target = *c496_clipped_header_zero_locals(owner, context).unwrap().last().unwrap();
            row.bytes[target / 8] |= 1 << (target % 8);
            assert!(rows.finish_c496_clipped_header_zero_capture(&row, &lease).is_err());
            assert!(rows.c496_clipped_header_zero_capture.is_some());
            row.bytes[target / 8] &= !(1 << (target % 8));
            let capture = rows.finish_c496_clipped_header_zero_capture(&row, &lease).unwrap();
            let mut result = NativeClippedHeaderZeroRow { row, capture };
            result.row.bytes[target / 8] |= 1 << (target % 8);
            assert!(result.validate_for(&binding, &lease).is_err());
        }
    }

    #[test]
    fn c496_rejects_lost_or_nonzero_claim_after_final_packing() {
        for (owner, context) in OWNERS {
            let (binding, lease) = sources(owner);
            for fault in 0..2 {
                let mut rows = prepared(&binding, context, &lease);
                seed(&mut rows, None);
                let row = packed(&binding, &rows);
                let target = c496_clipped_header_zero_locals(owner, context).unwrap()[0];
                if fault == 0 { rows.claimed[0][target] = false; }
                else { rows.values[0][target] = Fr::one(); }
                assert!(rows.finish_c496_clipped_header_zero_capture(&row, &lease).is_err());
                assert!(rows.c496_clipped_header_zero_capture.is_some());
            }
        }
    }
}

#[cfg(test)]
mod c491_headerzero_tests {
    use super::*;
    use crate::daa_history_roster::OwnerClass;

    fn sources() -> (HeaderSourceBinding, Eligible08MapSlackBundle) {
        Eligible08MapSlackBundle::synthetic_for_test(0, OwnerClass::Genesis).unwrap()
    }

    fn fresh_rows(binding: HeaderSourceBinding) -> Result<OwnedRows, String> {
        let mut rows = OwnedRows::new(OwnerSelection::Single {
            owner: 0, class: OwnerClass::Genesis,
        });
        rows.begin_c491_genesis_header_zero_capture(
            C491GenesisHeaderZeroRoute::GenesisMapSlackBundle, binding,
        )?;
        Ok(rows)
    }

    fn seed_all(rows: &mut OwnedRows, skipped: Option<(usize, usize)>) -> Result<(), String> {
        for context in 0..BANK53_CONTEXTS {
            for offset in C491_HEADER_ZERO_FIRST_OFFSET..=C491_HEADER_ZERO_LAST_OFFSET {
                if skipped == Some((context, offset)) { continue; }
                let wire = BANK53_BASE + context * BANK53_CONTEXT_BITS + offset;
                rows.claim_header_seed(0, wire, Fr::zero())?;
            }
        }
        Ok(())
    }

    fn synthetic_row(binding: &HeaderSourceBinding, rows: &OwnedRows) -> NativePackedRow {
        NativePackedRow {
            owner: 0, class: OwnerClass::Genesis,
            root: binding.root, total: binding.total, bytes: rows.bytes(0).unwrap(),
            header_source_binding: Some(binding.clone()),
            cap0_source: None, cap1_source: None, max_binding: None,
            map_binding: None, map_context: None, legacy_binding: None,
        }
    }

    fn finish<'b>(
        binding: &HeaderSourceBinding,
        bundle: &'b Eligible08MapSlackBundle,
        mut rows: OwnedRows,
    ) -> Result<NativeGenesisHeaderZeroRow<'b>, String> {
        let row = synthetic_row(binding, &rows);
        let capture = rows.finish_c491_genesis_header_zero_capture(&row, bundle)?;
        let result = NativeGenesisHeaderZeroRow { row, capture };
        result.validate_for(binding, bundle)?;
        Ok(result)
    }

    #[test]
    fn c491_header_zero_complete_synthetic_helper_control() {
        let (binding, bundle) = sources();
        let mut rows = fresh_rows(binding.clone()).unwrap();
        seed_all(&mut rows, None).unwrap();
        assert_eq!(finish(&binding, &bundle, rows).unwrap().capture.cells.len(), 4_096);
    }

    #[test]
    fn c491_header_zero_rejects_wrong_author_owner_and_binding_owner() {
        let (binding, _) = sources();
        let mut rows = OwnedRows::new(OwnerSelection::Single {
            owner: 1, class: OwnerClass::Genesis,
        });
        assert!(rows.begin_c491_genesis_header_zero_capture(
            C491GenesisHeaderZeroRoute::GenesisMapSlackBundle, binding,
        ).is_err());
        let (binding, _) = sources();
        assert!(fresh_rows(binding.mutated_field_for_test(5)).is_err());
    }

    #[test]
    fn c491_header_zero_rejects_wrong_cut_and_route() {
        let (binding, _) = sources();
        assert!(fresh_rows(binding.mutated_field_for_test(3)).is_err());
        let mut rows = OwnedRows::new(OwnerSelection::Single {
            owner: 0, class: OwnerClass::Genesis,
        });
        let (binding, _) = sources();
        assert!(rows.begin_c491_genesis_header_zero_capture(
            C491GenesisHeaderZeroRoute::Other, binding,
        ).is_err());
    }

    #[test]
    fn c491_header_zero_rejects_missing_context_zero_first_cell() {
        let (binding, bundle) = sources();
        let mut rows = fresh_rows(binding.clone()).unwrap();
        seed_all(&mut rows, Some((0, C491_HEADER_ZERO_FIRST_OFFSET))).unwrap();
        assert!(finish(&binding, &bundle, rows).is_err());
    }

    #[test]
    fn c491_header_zero_rejects_missing_context_one_last_cell() {
        let (binding, bundle) = sources();
        let mut rows = fresh_rows(binding.clone()).unwrap();
        seed_all(&mut rows, Some((1, C491_HEADER_ZERO_LAST_OFFSET))).unwrap();
        assert!(finish(&binding, &bundle, rows).is_err());
    }

    #[test]
    fn c491_header_zero_rejects_duplicate_cell() {
        let (binding, _) = sources();
        let mut rows = fresh_rows(binding).unwrap();
        let mut claims = rows.c491_genesis_header_zero_capture.take().unwrap();
        claims.record(0, C491_HEADER_ZERO_FIRST_OFFSET, Fr::zero()).unwrap();
        assert!(claims.record(0, C491_HEADER_ZERO_FIRST_OFFSET, Fr::zero()).is_err());
    }

    #[test]
    fn c491_header_zero_rejects_each_out_of_domain_boundary() {
        let (binding, _) = sources();
        let mut rows = fresh_rows(binding).unwrap();
        let claims = rows.c491_genesis_header_zero_capture.as_mut().unwrap();
        assert!(claims.record(0, C491_HEADER_ZERO_FIRST_OFFSET - 1, Fr::zero()).is_err());
        assert!(claims.record(1, C491_HEADER_ZERO_LAST_OFFSET + 1, Fr::zero()).is_err());
    }

    #[test]
    fn c491_header_zero_rejects_invalid_context() {
        let (binding, _) = sources();
        let mut rows = fresh_rows(binding).unwrap();
        assert!(rows.c491_genesis_header_zero_capture.as_mut().unwrap()
            .record(2, C491_HEADER_ZERO_FIRST_OFFSET, Fr::zero()).is_err());
    }

    #[test]
    fn c491_header_zero_rejects_nonzero_seed_and_competing_author() {
        let (binding, _) = sources();
        let mut nonzero = fresh_rows(binding.clone()).unwrap();
        let wire = BANK53_BASE + C491_HEADER_ZERO_FIRST_OFFSET;
        assert!(nonzero.claim_header_seed(0, wire, Fr::one()).is_err());

        let mut competing = fresh_rows(binding).unwrap();
        competing.claim(0, wire, Fr::zero()).unwrap();
        assert!(competing.claim_header_seed(0, wire, Fr::zero()).is_err());
    }

    #[test]
    fn c491_header_zero_rejects_later_same_zero_competing_author() {
        let (binding, _) = sources();
        let mut rows = fresh_rows(binding).unwrap();
        let wire = BANK53_BASE + C491_HEADER_ZERO_FIRST_OFFSET;
        rows.claim_header_seed(0, wire, Fr::zero()).unwrap();
        let before_claimed = rows.claimed[0][wire];
        let before_value = rows.values[0][wire];
        let before_cells = rows.c491_genesis_header_zero_capture.as_ref()
            .unwrap().cells.clone();
        assert_eq!(rows.claim(0, wire, Fr::zero()).unwrap_err(),
            format!("C491 later claim overlaps HeaderZero source wire{wire}"));
        assert_eq!(rows.claimed[0][wire], before_claimed);
        assert_eq!(rows.values[0][wire], before_value);
        assert_eq!(rows.c491_genesis_header_zero_capture.as_ref().unwrap().cells,
            before_cells);
    }

    #[test]
    fn c491_header_zero_rejects_final_nonzero_packed_bit() {
        let (binding, bundle) = sources();
        let mut rows = fresh_rows(binding.clone()).unwrap();
        seed_all(&mut rows, None).unwrap();
        let mut row = synthetic_row(&binding, &rows);
        let wire = BANK53_BASE + C491_HEADER_ZERO_FIRST_OFFSET;
        row.bytes[wire / 8] |= 1 << (wire % 8);
        assert!(rows.finish_c491_genesis_header_zero_capture(&row, &bundle).is_err());
    }

    #[test]
    fn c491_header_zero_rejects_different_bundle_object() {
        let (binding, bundle) = sources();
        let (_, other_bundle) = sources();
        let mut rows = fresh_rows(binding.clone()).unwrap();
        seed_all(&mut rows, None).unwrap();
        let result = finish(&binding, &bundle, rows).unwrap();
        assert!(result.validate_for(&binding, &other_bundle).is_err());
    }

    #[test]
    fn c491_header_zero_rejects_each_read_binding_field() {
        let (binding, bundle) = sources();
        let mut rows = fresh_rows(binding.clone()).unwrap();
        seed_all(&mut rows, None).unwrap();
        let result = finish(&binding, &bundle, rows).unwrap();
        for field in 0..6 {
            let wrong = binding.mutated_field_for_test(field);
            assert_eq!(result.validate_for(&wrong, &bundle).unwrap_err(),
                "C491 HeaderZero row/capture source binding mismatch");
        }
        result.validate_for(&binding, &bundle).unwrap();
    }

    #[test]
    fn c491_header_zero_failure_exposes_no_result_and_fresh_retry_succeeds() {
        let (binding, bundle) = sources();
        let mut failed = fresh_rows(binding.clone()).unwrap();
        seed_all(&mut failed, Some((0, C491_HEADER_ZERO_FIRST_OFFSET))).unwrap();
        assert!(finish(&binding, &bundle, failed).is_err());

        let mut fresh = fresh_rows(binding.clone()).unwrap();
        seed_all(&mut fresh, None).unwrap();
        assert!(finish(&binding, &bundle, fresh).is_ok());
    }
}

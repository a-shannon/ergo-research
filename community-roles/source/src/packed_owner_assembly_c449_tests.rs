use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SyntheticHeaderZeroAuthor {
    HeaderSeed,
    Map,
    Slack,
}

/// Test-only custody cannot be converted into NativePaddingHeaderZeroRow.
struct SyntheticPaddingHeaderZeroCustody {
    binding: HeaderSourceBinding,
    owner: usize,
    class: crate::daa_history_roster::OwnerClass,
    claims: Vec<Option<(SyntheticHeaderZeroAuthor, bool)>>,
    packed: Vec<u8>,
}

impl SyntheticPaddingHeaderZeroCustody {
    fn complete_zero() -> Self {
        Self {
            binding: HeaderSourceBinding::diagnostic_for_test(C449_PADDING_OWNER),
            owner: C449_PADDING_OWNER,
            class: crate::daa_history_roster::OwnerClass::Padding,
            claims: vec![Some((SyntheticHeaderZeroAuthor::HeaderSeed, false));
                C449_PADDING_BANK53_CELLS],
            packed: vec![0; OWNER_BYTES],
        }
    }

    fn read(
        &self,
        expected: &HeaderSourceBinding,
        context: usize,
        offset: usize,
    ) -> Result<bool, String> {
        if self.binding != *expected || self.owner != C449_PADDING_OWNER
            || self.class != crate::daa_history_roster::OwnerClass::Padding
            || self.claims.len() != C449_PADDING_BANK53_CELLS
            || self.packed.len() != OWNER_BYTES {
            return Err("C449 synthetic custody row binding/geometry".into());
        }
        let required = crate::bank53_required_writer::required_bank53_writer(
            C449_PADDING_OWNER, context, offset,
        ).map_err(|error| error.to_owned())?;
        let index = context.checked_mul(BANK53_CONTEXT_BITS)
            .and_then(|base| base.checked_add(offset))
            .filter(|index| *index < C449_PADDING_BANK53_CELLS)
            .ok_or("C449 synthetic custody context/offset")?;
        let claim = self.claims[index];
        let (observed, source_bit) = match claim {
            Some((SyntheticHeaderZeroAuthor::HeaderSeed, value)) =>
                (Some(ObservedPaddingHeaderZeroAuthor::HeaderSeed), Some(value)),
            Some((SyntheticHeaderZeroAuthor::Map | SyntheticHeaderZeroAuthor::Slack, value)) =>
                (Some(ObservedPaddingHeaderZeroAuthor::Other), Some(value)),
            None => (None, None),
        };
        let local = BANK53_BASE + index;
        check_padding_header_zero_observation(
            required, observed, source_bit,
            NativeHeaderSourceLease::bit(&self.packed, local),
        )
    }
}

fn synthetic_native_padding_row(binding: &HeaderSourceBinding, flipped: Option<usize>)
    -> NativePackedRow {
    let mut bytes=vec![0;OWNER_BYTES];
    if let Some(wire)=flipped {
        bytes[wire/8]|=1<<(wire%8);
    }
    NativePackedRow {
        owner:C449_PADDING_OWNER,
        class:crate::daa_history_roster::OwnerClass::Padding,
        root:binding.root,
        total:binding.total,
        bytes,
        header_source_binding:Some(binding.clone()),
        cap0_source:None,
        cap1_source:None,
        max_binding:None,
        map_binding:None,
        map_context:None,
        legacy_binding:None,
    }
}

fn fully_seed_header_zero_capture(skip: Option<usize>) -> (OwnedRows, HeaderSourceBinding) {
    let binding=HeaderSourceBinding::diagnostic_for_test(C449_PADDING_OWNER);
    let mut rows=OwnedRows::new(OwnerSelection::Single {
        owner:C449_PADDING_OWNER,
        class:crate::daa_history_roster::OwnerClass::Padding,
    });
    rows.begin_padding_header_zero_capture(binding.clone()).unwrap();
    for index in 0..C449_PADDING_BANK53_CELLS {
        if Some(index)!=skip {
            rows.claim_header_seed(C449_PADDING_OWNER,BANK53_BASE+index,Fr::zero()).unwrap();
        }
    }
    (rows,binding)
}

fn valid_padding_header_zero_route() -> PaddingHeaderZeroRoute {
    PaddingHeaderZeroRoute {
        capture_requested:true,
        owner:C449_PADDING_OWNER,
        class:crate::daa_history_roster::OwnerClass::Padding,
        plan_headers:C449_PADDING_OWNER as u64,
        plan_slot_log:21,
        plan_slots:1<<21,
        input_header_count:C449_PADDING_OWNER,
        has_max_adapter:false,
        test_header_route:false,
        has_bank53_map:false,
        has_cap0:false,
        has_cap1:false,
        has_overlay:false,
        has_census:false,
        has_scored_source:false,
        has_map_source:false,
        has_daa_source_out:false,
    }
}

#[test]
fn c449_padding_capture_route_is_exact_and_capture_disabled_is_inert() {
    assert!(require_padding_header_zero_route(&valid_padding_header_zero_route()).is_ok());

    let mut disabled=valid_padding_header_zero_route();
    disabled.capture_requested=false;
    disabled.owner=0;
    disabled.class=crate::daa_history_roster::OwnerClass::Carry;
    disabled.has_max_adapter=true;
    disabled.test_header_route=true;
    disabled.has_bank53_map=true;
    disabled.has_cap0=true;
    disabled.has_cap1=true;
    disabled.has_overlay=true;
    disabled.has_census=true;
    disabled.has_scored_source=true;
    disabled.has_map_source=true;
    disabled.has_daa_source_out=true;
    assert!(require_padding_header_zero_route(&disabled).is_ok());

    macro_rules! reject_one {
        ($field:ident, $bad:expr) => {{
            let mut route=valid_padding_header_zero_route();
            route.$field=$bad;
            assert!(require_padding_header_zero_route(&route).is_err(), stringify!($field));
        }};
    }
    reject_one!(owner,C449_PADDING_OWNER-1);
    reject_one!(class,crate::daa_history_roster::OwnerClass::Carry);
    reject_one!(plan_headers,C449_PADDING_OWNER as u64-1);
    reject_one!(plan_slot_log,20);
    reject_one!(plan_slots,(1<<21)-1);
    reject_one!(input_header_count,C449_PADDING_OWNER-1);
    reject_one!(has_max_adapter,true);
    reject_one!(test_header_route,true);
    reject_one!(has_bank53_map,true);
    reject_one!(has_cap0,true);
    reject_one!(has_cap1,true);
    reject_one!(has_overlay,true);
    reject_one!(has_census,true);
    reject_one!(has_scored_source,true);
    reject_one!(has_map_source,true);
    reject_one!(has_daa_source_out,true);
}

#[test]
fn c449_owned_rows_capture_accepts_complete_same_writer_zero_claims() {
    let (mut rows,binding)=fully_seed_header_zero_capture(None);
    let row=synthetic_native_padding_row(&binding,None);
    let capture=rows.finish_padding_header_zero_capture(&row).unwrap();
    assert_eq!(capture.cells.len(),C449_PADDING_BANK53_CELLS);
    assert!(capture.cells.iter().all(|claim|*claim==Some(false)));
}

#[test]
fn c449_owned_rows_capture_rejects_one_missing_header_claim() {
    let missing=C449_PADDING_BANK53_CELLS-1;
    let (mut rows,binding)=fully_seed_header_zero_capture(Some(missing));
    let row=synthetic_native_padding_row(&binding,None);
    let error=rows.finish_padding_header_zero_capture(&row).err().unwrap();
    assert!(error.contains("seed/final claim mismatch"));
}

#[test]
fn c449_owned_rows_capture_rejects_final_packed_bit_flip() {
    let (mut rows,binding)=fully_seed_header_zero_capture(None);
    let wire=BANK53_BASE+C449_PADDING_BANK53_CELLS-1;
    let row=synthetic_native_padding_row(&binding,Some(wire));
    let error=rows.finish_padding_header_zero_capture(&row).err().unwrap();
    assert!(error.contains("seed/final claim mismatch"));
}

#[test]
fn c449_owned_rows_capture_rejects_row_binding_substitution() {
    for field in 0..6 {
        let (mut rows,binding)=fully_seed_header_zero_capture(None);
        let wrong=binding.mutated_field_for_test(field);
        let row=synthetic_native_padding_row(&wrong,None);
        let error=rows.finish_padding_header_zero_capture(&row).err().unwrap();
        assert!(error.contains("final row binding/geometry"),"binding field {field}");
    }
    let (mut rows,binding)=fully_seed_header_zero_capture(None);
    let mut wrong_owner=synthetic_native_padding_row(&binding,None);
    wrong_owner.owner+=1;
    let error=rows.finish_padding_header_zero_capture(&wrong_owner).err().unwrap();
    assert!(error.contains("final row binding/geometry"),"row owner");

    let (mut rows,binding)=fully_seed_header_zero_capture(None);
    let mut wrong_class=synthetic_native_padding_row(&binding,None);
    wrong_class.class=crate::daa_history_roster::OwnerClass::Carry;
    let error=rows.finish_padding_header_zero_capture(&wrong_class).err().unwrap();
    assert!(error.contains("final row binding/geometry"),"row class");
}

#[test]
fn c449_padding_synthetic_custody_requires_header_claim_and_final_zero() {
    let mut custody = SyntheticPaddingHeaderZeroCustody::complete_zero();
    let binding = custody.binding.clone();
    assert_eq!(custody.read(&binding, 0, 0).unwrap(), false);

    custody.claims[0] = None;
    assert!(custody.read(&binding, 0, 0).unwrap_err().contains("claim"));

    custody = SyntheticPaddingHeaderZeroCustody::complete_zero();
    custody.claims[0] = Some((SyntheticHeaderZeroAuthor::Map, false));
    assert!(custody.read(&binding, 0, 0).unwrap_err().contains("wrong author"));

    custody = SyntheticPaddingHeaderZeroCustody::complete_zero();
    custody.claims[0] = Some((SyntheticHeaderZeroAuthor::HeaderSeed, true));
    assert!(custody.read(&binding, 0, 0).unwrap_err().contains("mismatch"));

    custody = SyntheticPaddingHeaderZeroCustody::complete_zero();
    custody.packed[BANK53_BASE / 8] |= 1 << (BANK53_BASE % 8);
    assert!(custody.read(&binding, 0, 0).unwrap_err().contains("mismatch"));

    custody = SyntheticPaddingHeaderZeroCustody::complete_zero();
    let wrong_binding = binding.mutated_field_for_test(2);
    assert!(custody.read(&wrong_binding, 0, 0).unwrap_err().contains("binding"));
}

#[test]
fn c449_padding_seed_capture_rejects_later_equal_zero_claims() {
    let mut rows = OwnedRows::new(OwnerSelection::Single {
        owner: C449_PADDING_OWNER,
        class: crate::daa_history_roster::OwnerClass::Padding,
    });
    let binding = HeaderSourceBinding::diagnostic_for_test(C449_PADDING_OWNER);
    rows.begin_padding_header_zero_capture(binding).unwrap();
    rows.claim_header_seed(C449_PADDING_OWNER, BANK53_BASE, Fr::zero()).unwrap();

    assert!(rows.claim_header_seed(C449_PADDING_OWNER, BANK53_BASE, Fr::zero())
        .unwrap_err().contains("duplicate"));
    assert!(rows.claim(C449_PADDING_OWNER, BANK53_BASE, Fr::zero())
        .unwrap_err().contains("HEADER-zero"));
    assert!(rows.claim_exclusive(C449_PADDING_OWNER, BANK53_BASE, Fr::zero())
        .unwrap_err().contains("HEADER-zero"));
    assert!(rows.claim_header_seed(C449_PADDING_OWNER, BANK53_BASE + 1, Fr::one())
        .unwrap_err().contains("nonzero"));
}

#[test]
fn c449_required_writer_n_boundary_and_active_score_7804_are_distinct() {
    use crate::bank53_required_writer::{required_bank53_writer as required,
        RequiredWriter, ScoreEndpointKind};

    assert_eq!(required(C449_PADDING_OWNER - 1, 0, 0).unwrap(),
        RequiredWriter::Map { context: 0 });
    assert_eq!(required(C449_PADDING_OWNER - 1, 0, 5_756).unwrap(),
        RequiredWriter::Map { context: 0 });
    assert_eq!(required(C449_PADDING_OWNER - 1, 0, 5_757).unwrap(),
        RequiredWriter::HeaderZero);
    assert_eq!(required(C449_PADDING_OWNER - 1, 0, 7_804).unwrap(),
        RequiredWriter::HeaderZero);
    assert_eq!(required(C449_PADDING_OWNER, 0, 0).unwrap(),
        RequiredWriter::HeaderZero);
    assert_eq!(required(C449_PADDING_OWNER, 1, 7_804).unwrap(),
        RequiredWriter::HeaderZero);

    assert_eq!(required(1_810_879, 0, 7_804).unwrap(),
        RequiredWriter::ScoreReplay {
            context: 0, endpoint: ScoreEndpointKind::Regular,
        });
    assert_eq!(required(1_810_879, 1, 7_804).unwrap(),
        RequiredWriter::HeaderZero);
    for context in 0..2 {
        assert_eq!(required(1_810_879, context, 7_805).unwrap(),
            RequiredWriter::Slack { context });
    }
}

mod c460_padding_owner_tests {
    use super::*;
    use crate::daa_history_roster::OwnerClass;

    const SLOT_END: usize = 1 << 21;

    fn route(owner: usize) -> PaddingHeaderZeroRoute {
        PaddingHeaderZeroRoute {
            capture_requested: true,
            owner,
            class: OwnerClass::Padding,
            plan_headers: crate::bank53_map::BANK53_N,
            plan_slot_log: 21,
            plan_slots: SLOT_END,
            input_header_count: C449_PADDING_OWNER,
            has_max_adapter: false,
            test_header_route: false,
            has_bank53_map: false,
            has_cap0: false,
            has_cap1: false,
            has_overlay: false,
            has_census: false,
            has_scored_source: false,
            has_map_source: false,
            has_daa_source_out: false,
        }
    }

    fn rows_with_header_zero_claims(
        owner: usize,
        skip: Option<usize>,
    ) -> (OwnedRows, HeaderSourceBinding) {
        let binding = HeaderSourceBinding::diagnostic_for_test(owner);
        let mut rows = OwnedRows::new(OwnerSelection::Single {
            owner,
            class: OwnerClass::Padding,
        });
        rows.begin_padding_header_zero_capture(binding.clone()).unwrap();
        for index in 0..C449_PADDING_BANK53_CELLS {
            if Some(index) != skip {
                rows.claim_header_seed(owner, BANK53_BASE + index, Fr::zero()).unwrap();
            }
        }
        (rows, binding)
    }

    fn row(owner: usize, binding: &HeaderSourceBinding, flipped: Option<usize>)
        -> NativePackedRow {
        let mut bytes = vec![0; OWNER_BYTES];
        if let Some(wire) = flipped {
            bytes[wire / 8] |= 1 << (wire % 8);
        }
        NativePackedRow {
            owner,
            class: OwnerClass::Padding,
            root: binding.root,
            total: binding.total,
            bytes,
            header_source_binding: Some(binding.clone()),
            cap0_source: None,
            cap1_source: None,
            max_binding: None,
            map_binding: None,
            map_context: None,
            legacy_binding: None,
        }
    }

    #[test]
    fn c460_route_accepts_padding_interval_and_rejects_both_edges_and_forbidden_source() {
        for owner in [C449_PADDING_OWNER, C449_PADDING_OWNER + 17, SLOT_END - 1] {
            assert!(require_padding_header_zero_route(&route(owner)).is_ok(), "owner {owner}");
        }
        for owner in [C449_PADDING_OWNER - 1, SLOT_END] {
            assert!(require_padding_header_zero_route(&route(owner)).is_err(), "owner {owner}");
        }
        let mut forbidden = route(C449_PADDING_OWNER + 17);
        forbidden.has_overlay = true;
        assert!(require_padding_header_zero_route(&forbidden).is_err(), "overlay route");
    }

    #[test]
    fn c460_capture_binds_interior_and_last_padding_owners_to_their_exact_rows() {
        for owner in [C449_PADDING_OWNER + 17, SLOT_END - 1] {
            let (mut rows, binding) = rows_with_header_zero_claims(owner, None);
            let native = row(owner, &binding, None);
            let capture = rows.finish_padding_header_zero_capture(&native).unwrap();
            let custody = NativePaddingHeaderZeroRow::from_producer(native, capture).unwrap();
            assert_eq!(custody.row().owner, owner);
            assert!(!custody.read_header_zero(&binding, 0, 0).unwrap());
            assert!(!custody.read_header_zero(&binding, 1, BANK53_CONTEXT_BITS - 1).unwrap());
        }
    }

    #[test]
    fn c460_capture_rejects_one_missing_cell() {
        let missing = C449_PADDING_BANK53_CELLS - 1;
        let owner = C449_PADDING_OWNER + 17;
        let (mut rows, binding) = rows_with_header_zero_claims(owner, Some(missing));
        let native = row(owner, &binding, None);
        assert!(rows.finish_padding_header_zero_capture(&native).err().unwrap()
            .contains("seed/final claim mismatch"));
    }

    #[test]
    fn c460_capture_rejects_duplicate_equal_zero_claim() {
        let owner = C449_PADDING_OWNER + 17;
        let binding = HeaderSourceBinding::diagnostic_for_test(owner);
        let mut rows = OwnedRows::new(OwnerSelection::Single { owner, class: OwnerClass::Padding });
        rows.begin_padding_header_zero_capture(binding).unwrap();
        rows.claim_header_seed(owner, BANK53_BASE, Fr::zero()).unwrap();
        assert!(rows.claim_header_seed(owner, BANK53_BASE, Fr::zero()).unwrap_err()
            .contains("duplicate"));
    }

    #[test]
    fn c460_capture_rejects_nonzero_header_seed() {
        let owner = C449_PADDING_OWNER + 17;
        let binding = HeaderSourceBinding::diagnostic_for_test(owner);
        let mut rows = OwnedRows::new(OwnerSelection::Single { owner, class: OwnerClass::Padding });
        rows.begin_padding_header_zero_capture(binding).unwrap();
        assert!(rows.claim_header_seed(owner, BANK53_BASE, Fr::one()).unwrap_err()
            .contains("nonzero"));
    }

    #[test]
    fn c460_claim_checks_required_writer_at_the_actual_header_seed() {
        // Corrupt only the synthetic test capture owner to the adjacent live
        // owner; its first Bank53 cell requires Map, so a HEADER claim must fail.
        let owner = C449_PADDING_OWNER;
        let mut rows = OwnedRows::new(OwnerSelection::Single { owner, class: OwnerClass::Padding });
        rows.begin_padding_header_zero_capture(
            HeaderSourceBinding::diagnostic_for_test(owner),
        ).unwrap();
        let wrong_owner = C449_PADDING_OWNER - 1;
        rows.selection = OwnerSelection::Single { owner: wrong_owner, class: OwnerClass::Padding };
        let capture = rows.padding_header_zero_capture.as_mut().unwrap();
        capture.owner = wrong_owner;
        capture.binding = HeaderSourceBinding::diagnostic_for_test(wrong_owner);
        let error = rows.claim_header_seed(wrong_owner, BANK53_BASE, Fr::zero()).unwrap_err();
        assert!(error.contains("non-HEADER cell"));
        assert!(rows.padding_header_zero_capture.as_ref().unwrap().cells[0].is_none());
    }

    #[test]
    fn c460_finalization_rejects_packed_bit_flip() {
        let owner = C449_PADDING_OWNER + 17;
        let (mut rows, binding) = rows_with_header_zero_claims(owner, None);
        let native = row(owner, &binding, Some(BANK53_BASE + C449_PADDING_BANK53_CELLS - 1));
        assert!(rows.finish_padding_header_zero_capture(&native).err().unwrap()
            .contains("seed/final claim mismatch"));
    }

    #[test]
    fn c460_finalization_rejects_wrong_row_owner_and_binding() {
        let owner = C449_PADDING_OWNER + 17;
        let (mut rows, binding) = rows_with_header_zero_claims(owner, None);
        let mut wrong_owner = row(owner, &binding, None);
        wrong_owner.owner += 1;
        assert!(rows.finish_padding_header_zero_capture(&wrong_owner).err().unwrap()
            .contains("final row binding/geometry"));

        let (mut rows, binding) = rows_with_header_zero_claims(owner, None);
        let wrong_binding = binding.mutated_field_for_test(2);
        let native = row(owner, &wrong_binding, None);
        assert!(rows.finish_padding_header_zero_capture(&native).err().unwrap()
            .contains("final row binding/geometry"));
    }

    #[test]
    fn c460_read_rejects_owner_binding_substitution() {
        let owner = C449_PADDING_OWNER + 17;
        let (mut rows, binding) = rows_with_header_zero_claims(owner, None);
        let native = row(owner, &binding, None);
        let capture = rows.finish_padding_header_zero_capture(&native).unwrap();
        let custody = NativePaddingHeaderZeroRow::from_producer(native, capture).unwrap();
        let wrong_binding = binding.mutated_field_for_test(5);
        assert!(custody.read_header_zero(&wrong_binding, 0, 0).is_err());
    }
}

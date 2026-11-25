//! Opaque author custody for the three foreign-read families of one clipped
//! H21 Score relation. This module does not publish cells, rows, or bytes.

use super::h21_eligible_context::{
    Eligible08RegularScoreOwner, H21ClosedScoreOwnerRelation, ScoreRelationReadAuthor,
    ScoreReplayAuthor, ScoredOwnerPackedAuthor, ScoredOwnerPackedCell,
};
use super::{HeaderSourceBinding, NativeOwnerProducer,
    NativePartialScoredOwnerPackedCandidate, WorkUpperPublication};
use crate::h21_scheduled_family_ledger::{ScoredOwnerCapMaterial, ScoredOwnerCapPublication};
use crate::h21_scheduled_max_cap::Writer;
use ark_bn254::Fr;
use ark_ff::{One, Zero};

const WIDTH: usize = 1 << 20;
const PREVIOUS_READS: usize = 225;
const CAP_READS: usize = 65;
const WORK_UPPER_READS: usize = 224;
const TOTAL_READS: usize = PREVIOUS_READS + CAP_READS + WORK_UPPER_READS;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ClippedRoute {
    context: usize,
    destination: usize,
    previous_owner: usize,
    max_owner: usize,
    work_owner: usize,
    height: usize,
}

impl ClippedRoute {
    fn for_context(context: usize) -> Result<Self, String> {
        let descriptor = crate::bank53_map::CutDescriptor::eligible08();
        let height = *descriptor.guards().get(context).ok_or("C500 clipped read context")?;
        let destination = height - 1;
        let plan = Eligible08RegularScoreOwner::equation_plan(destination)?;
        let author = plan.authors()[context].ok_or("C500 clipped plan inactive context")?;
        Ok(Self { context, destination, previous_owner: author.previous_owner,
            max_owner: author.max_owner, work_owner: destination - 1, height })
    }

    fn relation_author(self) -> ScoreReplayAuthor {
        ScoreReplayAuthor {
            context: self.context,
            origin: self.destination + 1,
            previous_owner: self.previous_owner,
            max_owner: self.max_owner,
            cap_owner: self.destination,
        }
    }

    fn predecessor_author(self) -> Result<ScoredOwnerPackedAuthor, String> {
        let schedule = Eligible08RegularScoreOwner::classify(self.previous_owner)?;
        if !schedule.active()[self.context] {
            return Err("C500 inactive predecessor Score context".into());
        }
        Ok(ScoredOwnerPackedAuthor::Score(ScoreReplayAuthor {
            context: self.context,
            origin: self.previous_owner + 1,
            previous_owner: schedule.previous_r_owner(),
            max_owner: schedule.max_owner(),
            cap_owner: self.previous_owner,
        }))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PhysicalReadAuthor {
    PreviousR(ScoredOwnerPackedAuthor),
    Cap {
        context: usize,
        origin: usize,
        max_owner: usize,
        cap_owner: usize,
    },
    WorkUpper { owner: usize, height: usize },
}

fn boolean(value: Fr) -> Result<bool, String> {
    if value.is_zero() {
        Ok(false)
    } else if value.is_one() {
        Ok(true)
    } else {
        Err("C500 non-Boolean foreign read".into())
    }
}

fn require_binding(
    binding: &HeaderSourceBinding,
    relation: &H21ClosedScoreOwnerRelation<'_>,
    owner: usize,
    label: &str,
) -> Result<(), String> {
    require_binding_parts(
        binding,
        relation.parent_root(),
        relation.parent_total(),
        relation.parent_profile(),
        relation.cut_identity(),
        owner,
        label,
    )
}

fn require_binding_parts(
    binding: &HeaderSourceBinding,
    root: [u8; 32],
    total: [u8; 28],
    profile: [u8; 32],
    cut: &[u8],
    owner: usize,
    label: &str,
) -> Result<(), String> {
    if !binding.matches_sink(root, total, profile, cut, owner) {
        return Err(format!("C500 {label} parent/cut/owner"));
    }
    Ok(())
}

fn require_unique_occurrence<I>(
    claims: I,
    wire: usize,
    author: PhysicalReadAuthor,
    value: bool,
    ordinal: usize,
) -> Result<(), String>
where
    I: IntoIterator<Item = (usize, PhysicalReadAuthor, bool)>,
{
    let mut found = None;
    for claim in claims.into_iter().filter(|claim| claim.0 == wire) {
        if found.replace(claim).is_some() {
            return Err(format!("C500 duplicate source occurrence ordinal {ordinal}"));
        }
    }
    let found = found.ok_or_else(|| format!("C500 missing source occurrence ordinal {ordinal}"))?;
    if found.1 != author || found.2 != value {
        return Err(format!("C500 source author/value ordinal {ordinal}"));
    }
    Ok(())
}

fn require_source_cells_packed(
    owner: usize,
    cells: &[ScoredOwnerPackedCell],
    packed: &[u8],
) -> Result<(), String> {
    if packed.len() != WIDTH / 8 {
        return Err("C500 predecessor partial packed width".into());
    }
    let base = owner.checked_mul(WIDTH)
        .ok_or("C500 predecessor packed base overflow")?;
    for (ordinal, cell) in cells.iter().enumerate() {
        let local = cell.wire().checked_sub(base).filter(|local| *local < WIDTH)
            .ok_or_else(|| format!("C500 predecessor source wire ordinal {ordinal}"))?;
        let packed_value = (packed[local / 8] >> (local % 8)) & 1 != 0;
        if packed_value != cell.value() {
            return Err(format!("C500 predecessor packed value ordinal {ordinal}"));
        }
    }
    Ok(())
}

fn check_cap_max_source(
    material: &ScoredOwnerCapMaterial,
    route: ClippedRoute,
) -> Result<(), String> {
    let mut bit = 0usize;
    for &(wire, writer, _) in &material.imports {
        let Writer::Max { context, end } = writer else {
            return Err("C500 Cap non-MAX source".into());
        };
        if context != route.context {
            continue;
        }
        let expected_wire = route.max_owner.checked_mul(WIDTH)
            .and_then(|base| base.checked_add([999_424, 1_000_097][route.context]))
            .and_then(|base| base.checked_add(bit))
            .ok_or("C500 Cap MAX wire overflow")?;
        if bit >= WORK_UPPER_READS || end != route.max_owner + 2
            || wire != expected_wire {
            return Err("C500 Cap MAX source/context/order".into());
        }
        bit += 1;
    }
    if bit != WORK_UPPER_READS {
        return Err("C500 Cap MAX source census".into());
    }
    Ok(())
}

fn check_ordered_reads<F>(
    route: ClippedRoute,
    reads: &[(usize, ScoreRelationReadAuthor, Fr)],
    mut require_source: F,
) -> Result<(), String>
where
    F: FnMut(usize, PhysicalReadAuthor, bool, usize) -> Result<(), String>,
{
    if reads.len() != TOTAL_READS {
        return Err("C500 exact foreign-read census".into());
    }
    let score_base = [677_501, 685_693][route.context];
    let r_start = crate::origin_score::Layout::new().r.start;
    for bit in 0..PREVIOUS_READS {
        let ordinal = bit;
        let expected_wire = route.previous_owner * WIDTH + score_base + r_start + bit;
        let &(wire, author, value) = &reads[ordinal];
        let expected_read = ScoreRelationReadAuthor::PreviousR {
            context: route.context,
            owner: route.previous_owner,
        };
        if wire != expected_wire || author != expected_read {
            return Err(format!("C500 PreviousR read ordinal {ordinal}"));
        }
        require_source(
            wire,
            PhysicalReadAuthor::PreviousR(route.predecessor_author()?),
            boolean(value)?,
            ordinal,
        )?;
    }
    for bit in 0..CAP_READS {
        let ordinal = PREVIOUS_READS + bit;
        let expected_wire = route.destination * WIDTH
            + [1_000_770, 1_002_818][route.context] + 740 + bit;
        let &(wire, author, value) = &reads[ordinal];
        let expected_read = ScoreRelationReadAuthor::Cap {
            context: route.context,
            origin: route.destination + 1,
            max_owner: route.max_owner,
            cap_owner: route.destination,
        };
        if wire != expected_wire || author != expected_read {
            return Err(format!("C500 Cap read ordinal {ordinal}"));
        }
        require_source(
            wire,
            PhysicalReadAuthor::Cap {
                context: route.context,
                origin: route.destination + 1,
                max_owner: route.max_owner,
                cap_owner: route.destination,
            },
            boolean(value)?,
            ordinal,
        )?;
    }
    for bit in 0..WORK_UPPER_READS {
        let ordinal = PREVIOUS_READS + CAP_READS + bit;
        let expected_wire = route.work_owner * WIDTH + 987_450 + bit;
        let &(wire, author, value) = &reads[ordinal];
        let expected_read = ScoreRelationReadAuthor::WorkUpper {
            owner: route.work_owner,
            height: route.height,
        };
        if wire != expected_wire || author != expected_read {
            return Err(format!("C500 WorkUpper read ordinal {ordinal}"));
        }
        require_source(
            wire,
            PhysicalReadAuthor::WorkUpper {
                owner: route.work_owner,
                height: route.height,
            },
            boolean(value)?,
            ordinal,
        )?;
    }
    Ok(())
}

/// Source-bound custody for one clipped relation's three foreign-read
/// families. Construction validates all 514 ordered occurrences before the
/// bundle exists. Its sources remain opaque and there is no cell or byte view.
pub(crate) struct ClippedScoreReadAuthorBundle<'r, 'source, 'packed, 'producer, 'input> {
    relation: &'r H21ClosedScoreOwnerRelation<'source>,
    predecessor: &'packed NativePartialScoredOwnerPackedCandidate<'producer, 'input>,
    cap: ScoredOwnerCapPublication,
    work_upper: WorkUpperPublication,
    context: usize,
}

impl<'r, 'source, 'packed, 'producer, 'input>
    ClippedScoreReadAuthorBundle<'r, 'source, 'packed, 'producer, 'input> {
    pub(crate) fn new(
        relation: &'r H21ClosedScoreOwnerRelation<'source>,
        predecessor: &'packed NativePartialScoredOwnerPackedCandidate<'producer, 'input>,
        cap: ScoredOwnerCapPublication,
        producer: &NativeOwnerProducer<'_>,
        context: usize,
    ) -> Result<Self, String> {
        let route = ClippedRoute::for_context(context)?;
        let native_lease = producer.native_work_local_lease_for_owner(route.work_owner)?;
        producer.require_native_work_local_lease_for_owner(
            &native_lease.parent, route.work_owner, &native_lease)?;
        let work_upper = producer.work_upper_publication(
            route.work_owner, native_lease.local())?;
        let bundle = Self { relation, predecessor, cap, work_upper, context };
        bundle.validate()?;
        Ok(bundle)
    }

    pub(crate) fn validate(&self) -> Result<(), String> {
        let route = ClippedRoute::for_context(self.context)?;
        let relation = self.relation;
        relation.source_equation_plan(route.destination)?;
        if relation.owner() != route.destination
            || relation.authors()[route.context] != Some(route.relation_author())
            || relation.authors()[1 - route.context].is_some()
            || relation.cells().len() != 2_048
            || relation.terms(route.context)?.len() != 8_545
            || !relation.terms(1 - route.context)?.is_empty()
        {
            return Err("C500 clipped relation owner/context/census".into());
        }

        if self.predecessor.owner() != route.previous_owner {
            return Err("C500 predecessor packed owner".into());
        }
        let predecessor_binding = self.predecessor.binding()?;
        self.predecessor.check_daa_author()?;
        self.predecessor.source.validate_for_packing(
            predecessor_binding, route.previous_owner)?;
        require_binding(predecessor_binding, relation, route.previous_owner, "predecessor")?;
        require_source_cells_packed(
            route.previous_owner,
            self.predecessor.source_cells(),
            self.predecessor.partial_packed_bytes(),
        )?;

        require_binding(self.cap.binding(), relation, route.destination, "Cap")?;
        let cap = self.cap.checked_material()?;
        if !cap.active[route.context] || cap.q[route.context].len() != CAP_READS {
            return Err("C500 Cap active q census".into());
        }
        check_cap_max_source(&cap, route)?;

        let upper = self.work_upper.checked_upper(
            relation.parent_root(), relation.parent_total(), relation.parent_profile(),
            relation.cut_identity(), route.work_owner)?;

        check_ordered_reads(route, relation.reads(), |wire, author, value, ordinal| {
            match author {
                PhysicalReadAuthor::PreviousR(_) => require_unique_occurrence(
                    self.predecessor.source_cells().iter().map(|cell| (
                        cell.wire(), PhysicalReadAuthor::PreviousR(cell.author()), cell.value())),
                    wire, author, value, ordinal),
                PhysicalReadAuthor::Cap { context, origin, max_owner, cap_owner } =>
                    require_unique_occurrence(
                        cap.q[context].iter().copied().map(|(wire, value)| (
                            wire,
                            PhysicalReadAuthor::Cap {
                                context, origin, max_owner, cap_owner,
                            },
                            value,
                        )),
                        wire, author, value, ordinal),
                PhysicalReadAuthor::WorkUpper { owner, height } =>
                    require_unique_occurrence(
                        upper.iter().copied().map(|(wire, value)| (
                            wire,
                            PhysicalReadAuthor::WorkUpper { owner, height },
                            value.is_one(),
                        )),
                        wire, author, value, ordinal),
            }
        })
    }

    pub(crate) fn census(&self) -> Result<(usize, usize, usize, usize), String> {
        self.validate()?;
        Ok((PREVIOUS_READS, CAP_READS, WORK_UPPER_READS, TOTAL_READS))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone)]
    struct Fixture {
        route: ClippedRoute,
        reads: Vec<(usize, ScoreRelationReadAuthor, Fr)>,
        claims: Vec<(usize, PhysicalReadAuthor, bool)>,
    }

    impl Fixture {
        fn new(context: usize) -> Self {
            let route = ClippedRoute::for_context(context).unwrap();
            let mut reads = Vec::with_capacity(TOTAL_READS);
            let mut claims = Vec::with_capacity(TOTAL_READS);
            let previous_author = route.predecessor_author().unwrap();
            let r_start = crate::origin_score::Layout::new().r.start;
            for bit in 0..PREVIOUS_READS {
                let wire = route.previous_owner * WIDTH
                    + [677_501, 685_693][context] + r_start + bit;
                reads.push((wire, ScoreRelationReadAuthor::PreviousR {
                    context, owner: route.previous_owner }, Fr::zero()));
                claims.push((wire, PhysicalReadAuthor::PreviousR(previous_author), false));
            }
            for bit in 0..CAP_READS {
                let wire = route.destination * WIDTH
                    + [1_000_770, 1_002_818][context] + 740 + bit;
                let author = PhysicalReadAuthor::Cap { context,
                    origin: route.destination + 1, max_owner: route.max_owner,
                    cap_owner: route.destination };
                reads.push((wire, ScoreRelationReadAuthor::Cap { context,
                    origin: route.destination + 1, max_owner: route.max_owner,
                    cap_owner: route.destination }, Fr::zero()));
                claims.push((wire, author, false));
            }
            for bit in 0..WORK_UPPER_READS {
                let wire = route.work_owner * WIDTH + 987_450 + bit;
                let author = PhysicalReadAuthor::WorkUpper {
                    owner: route.work_owner, height: route.height };
                reads.push((wire, ScoreRelationReadAuthor::WorkUpper {
                    owner: route.work_owner, height: route.height }, Fr::zero()));
                claims.push((wire, author, false));
            }
            Self { route, reads, claims }
        }

        fn check(&self) -> Result<(), String> {
            check_ordered_reads(self.route, &self.reads,
                |wire, author, value, ordinal| require_unique_occurrence(
                    self.claims.iter().copied(), wire, author, value, ordinal))
        }
    }

    #[test]
    fn c500_same_value_wrong_previous_author_rejects_then_pristine_retry_passes() {
        let pristine = Fixture::new(0);
        assert_eq!(pristine.reads[0].0, 1_898_844_937_123);
        let mut wrong = pristine.clone();
        wrong.claims[0].1 = PhysicalReadAuthor::PreviousR(
            ScoredOwnerPackedAuthor::Slack(0));
        assert_eq!(wrong.claims[0].0, pristine.claims[0].0);
        assert_eq!(wrong.claims[0].2, pristine.claims[0].2);
        assert_eq!(wrong.check().unwrap_err(), "C500 source author/value ordinal 0");
        pristine.check().unwrap();
    }

    #[test]
    fn c500_missing_duplicate_reordered_and_trailing_reads_reject() {
        let pristine = Fixture::new(0);
        let mut missing = pristine.clone();
        missing.claims.remove(0);
        assert_eq!(missing.check().unwrap_err(), "C500 missing source occurrence ordinal 0");
        let mut duplicate = pristine.clone();
        duplicate.claims.push(duplicate.claims[0]);
        assert_eq!(duplicate.check().unwrap_err(), "C500 duplicate source occurrence ordinal 0");
        let mut reordered = pristine.clone();
        reordered.reads.swap(0, 1);
        assert_eq!(reordered.check().unwrap_err(), "C500 PreviousR read ordinal 0");
        let mut trailing = pristine.clone();
        trailing.reads.push(trailing.reads[0]);
        assert_eq!(trailing.check().unwrap_err(), "C500 exact foreign-read census");
        pristine.check().unwrap();
    }

    #[test]
    fn c500_cap_and_work_typed_author_faults_reject_both_contexts() {
        for context in 0..2 {
            let pristine = Fixture::new(context);
            for fault in 0..6 {
                let mut wrong = pristine.clone();
                match fault {
                    0 => wrong.reads[PREVIOUS_READS].1 = ScoreRelationReadAuthor::Cap {
                        context: 1 - context, origin: wrong.route.destination + 1,
                        max_owner: wrong.route.max_owner, cap_owner: wrong.route.destination },
                    1 => wrong.reads[PREVIOUS_READS].1 = ScoreRelationReadAuthor::Cap {
                        context, origin: wrong.route.destination,
                        max_owner: wrong.route.max_owner, cap_owner: wrong.route.destination },
                    2 => wrong.reads[PREVIOUS_READS].1 = ScoreRelationReadAuthor::Cap {
                        context, origin: wrong.route.destination + 1,
                        max_owner: wrong.route.max_owner - 1, cap_owner: wrong.route.destination },
                    3 => wrong.reads[PREVIOUS_READS].1 = ScoreRelationReadAuthor::Cap {
                        context, origin: wrong.route.destination + 1,
                        max_owner: wrong.route.max_owner, cap_owner: wrong.route.destination - 1 },
                    4 => wrong.reads[PREVIOUS_READS + CAP_READS].1 =
                        ScoreRelationReadAuthor::WorkUpper {
                            owner: wrong.route.work_owner - 1, height: wrong.route.height },
                    5 => wrong.reads[PREVIOUS_READS + CAP_READS].1 =
                        ScoreRelationReadAuthor::WorkUpper {
                            owner: wrong.route.work_owner, height: wrong.route.height - 1 },
                    _ => unreachable!(),
                }
                assert!(wrong.check().is_err(), "context {context} fault {fault}");
                pristine.check().unwrap();
            }
        }
    }

    #[test]
    fn c500_context_route_and_bundle_signature_are_closed() {
        assert!(ClippedRoute::for_context(2).is_err());
        let _new = ClippedScoreReadAuthorBundle::new;
        let _validate = ClippedScoreReadAuthorBundle::validate;
        let _census = ClippedScoreReadAuthorBundle::census;

        let route = ClippedRoute::for_context(0).unwrap();
        let local = 677_501 + crate::origin_score::Layout::new().r.start;
        let cell = ScoredOwnerPackedCell::synthetic_for_test(
            route.previous_owner * WIDTH + local,
            route.predecessor_author().unwrap(),
            true,
        );
        let mut packed = vec![0u8; WIDTH / 8];
        packed[local / 8] |= 1 << (local % 8);
        require_source_cells_packed(route.previous_owner, &[cell], &packed).unwrap();
        packed[local / 8] ^= 1 << (local % 8);
        assert_eq!(require_source_cells_packed(
            route.previous_owner, &[cell], &packed).unwrap_err(),
            "C500 predecessor packed value ordinal 0");
    }

    #[test]
    fn c500_parent_value_and_cap_max_faults_reject() {
        let route = ClippedRoute::for_context(0).unwrap();
        let root = [0x51; 32];
        let total = [0x62; 28];
        let profile = [0x73; 32];
        let cut = crate::bank53_map::CutDescriptor::eligible08().canonical_identity();
        let binding = HeaderSourceBinding::from_sink_for_test(
            root, total, profile, cut.clone(), route.destination);
        require_binding_parts(&binding, root, total, profile, &cut,
            route.destination, "fixture").unwrap();
        for field in 0..6 {
            assert!(require_binding_parts(&binding.mutated_field_for_test(field),
                root, total, profile, &cut, route.destination, "fixture").is_err(),
                "binding field {field}");
        }

        let pristine = Fixture::new(0);
        let mut wrong_value = pristine.clone();
        wrong_value.claims[0].2 = true;
        assert_eq!(wrong_value.check().unwrap_err(), "C500 source author/value ordinal 0");
        let mut non_boolean = pristine.clone();
        non_boolean.reads[0].2 = Fr::from(2u64);
        assert_eq!(non_boolean.check().unwrap_err(), "C500 non-Boolean foreign read");
        pristine.check().unwrap();

        let imports = (0..WORK_UPPER_READS).map(|bit| (
            route.max_owner * WIDTH + 999_424 + bit,
            Writer::Max { context: 0, end: route.max_owner + 2 },
            false,
        )).collect();
        let material = ScoredOwnerCapMaterial {
            rows: Vec::new(),
            cells: Vec::new(),
            q: std::array::from_fn(|_| Vec::new()),
            imports,
            active: [true, false],
        };
        check_cap_max_source(&material, route).unwrap();
        let mut wrong_end = ScoredOwnerCapMaterial { imports: material.imports.clone(),
            rows: Vec::new(), cells: Vec::new(), q: std::array::from_fn(|_| Vec::new()),
            active: [true, false] };
        wrong_end.imports[0].1 = Writer::Max { context: 0, end: route.max_owner + 3 };
        assert!(check_cap_max_source(&wrong_end, route).is_err());
        let mut wrong_context = ScoredOwnerCapMaterial { imports: material.imports.clone(),
            rows: Vec::new(), cells: Vec::new(), q: std::array::from_fn(|_| Vec::new()),
            active: [true, false] };
        wrong_context.imports[0].1 = Writer::Max { context: 1, end: route.max_owner + 2 };
        assert!(check_cap_max_source(&wrong_context, route).is_err());
        let mut wrong_order = material;
        wrong_order.imports.swap(0, 1);
        assert!(check_cap_max_source(&wrong_order, route).is_err());
    }
}

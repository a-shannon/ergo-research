//! Private exact-tail coactive producer. Ordinary entry points remain separate.
use super::*;
use crate::h21_scheduled_max_cap::{MaxReplayAuthor, MaxStream};

const OWNER: usize = 1_810_840;
const HEIGHT: usize = 1_810_842;

fn require_exact_shape(owner: usize, height: usize,
    class: crate::daa_history_roster::OwnerClass, role: leaf::Role,
    activity: ([bool; 2], [bool; 2]), work: bool, max_source: bool,
    max_claims: bool, daa: bool, other: bool) -> Result<(), String> {
    if owner != OWNER || height != HEIGHT
        || class != crate::daa_history_roster::OwnerClass::Carry
        || role != leaf::Role::Genuine
        || activity != ([false, true], [false, false])
        || !work || !max_source || !max_claims || !daa || other {
        return Err("C581 exact-tail coactive admission".into());
    }
    Ok(())
}

// Fields and constructor are private. The inner builder can inspect only this
// token's checked admission method; no caller supplies a mode Boolean.
pub(super) struct CoactiveAdmission<'p, 'a, 'm> {
    producer: &'p NativeOwnerProducer<'a>,
    stream: &'p MaxStream<'m>,
    binding: HeaderSourceBinding,
}

impl<'p, 'a, 'm> CoactiveAdmission<'p, 'a, 'm> {
    fn new(producer: &'p NativeOwnerProducer<'a>, stream: &'p MaxStream<'m>)
        -> Result<Self, String> {
        validate_native_plan_input(producer.plan, producer.input)?;
        producer.work_local_parent(OWNER)?;
        let height = OWNER.checked_add(2).ok_or("C581 owner height overflow")?;
        let class = producer.roster.owner_class(OWNER as u64)?;
        let role = producer.plan.leaf_profile().role(OWNER)?;
        let activity = mixed_map_header_schedule().owner_activity(OWNER)?;
        require_exact_shape(OWNER, height, class, role, activity,
            true, true, true, true, false)?;
        if producer.plan.headers() != 1_827_840 || producer.plan.slot_log() != 21
            || producer.plan.slots() != 1 << 21
            || producer.input.header_count() != 1_827_840
            || producer.max_adapter.is_some() {
            return Err("C581 coactive H21 source geometry".into());
        }
        #[cfg(test)]
        if producer.legacy_adapter.is_some() {
            return Err("C581 coactive rejects legacy adapter".into());
        }
        let member = scheduled_max_class(OWNER)?;
        if member.active != [false, true] {
            return Err("C581 coactive MAX class activity".into());
        }
        stream.closed_native_snapshot(producer.plan, producer.input)?;
        let binding = HeaderSourceBinding::for_plan(producer.plan, OWNER)?;
        if binding.profile() != producer.input.profile() {
            return Err("C581 coactive source profile".into());
        }
        Ok(Self { producer, stream, binding })
    }

    pub(super) fn check(&self, producer: &NativeOwnerProducer<'_>, owner: usize,
        class: crate::daa_history_roster::OwnerClass,
        source: Option<&NativeScheduledMaxSource<'_, '_>>,
        work: bool, max_claims: bool, daa: bool, other: bool) -> Result<(), String> {
        let source = source.ok_or("C581 coactive MAX source missing")?;
        let height = owner.checked_add(2).ok_or("C581 owner height overflow")?;
        require_exact_shape(owner, height, class,
            producer.plan.leaf_profile().role(owner)?,
            mixed_map_header_schedule().owner_activity(owner)?,
            work, true, max_claims, daa, other)?;
        if !std::ptr::eq(self.producer, producer)
            || !std::ptr::eq(self.stream, source.stream)
            || owner != self.binding.owner()
            || source.binding != self.binding
            || source.binding.profile() != producer.input.profile()
            || source.class != scheduled_max_class(owner)?
            || source.cells != self.stream.closed_owner_cells(owner)?
            || source.max != c512c_checked_max_cells(owner, &source.cells)? {
            return Err("C581 coactive token/source identity".into());
        }
        self.stream.closed_native_snapshot(producer.plan, producer.input)?;
        Ok(())
    }
}

// Real evidence fields, with neither an owned row nor a borrow into Composite.
struct MaxEvidence<'p, 'a, 'm> {
    daa: NativeDaaSourceLease<'p, 'a>,
    source: NativeScheduledMaxSource<'p, 'm>,
    claims: Vec<(usize, MaxReplayAuthor, bool)>,
}

impl MaxEvidence<'_, '_, '_> {
    fn require_live_source(&self, producer: &NativeOwnerProducer<'_>,
        stream: &MaxStream<'_>) -> Result<(), String> {
        if !std::ptr::eq(self.source.stream, stream) {
            return Err("C580 type slice MAX stream identity".into());
        }
        if !std::ptr::eq(self.daa._source, producer) {
            return Err("C580 type slice MAX producer identity".into());
        }
        let expected = HeaderSourceBinding::for_plan(producer.plan, OWNER)?;
        if self.source.binding != expected || expected.profile() != producer.input.profile() {
            return Err("C580 type slice MAX live binding".into());
        }
        Ok(())
    }

    fn check_on(&self, row: &NativePackedRow) -> Result<(), String> {
        if self.source.class.owner != OWNER || self.source.class.active != [false, true] {
            return Err("C581 exact coactive MAX owner/activity".into());
        }
        c581_check_max_on_row(row, &self.daa, &self.source, &self.claims)
    }

    fn read_on(&self, row: &NativePackedRow, wire: usize)
        -> Result<(MaxReplayAuthor, Fr), String> {
        c576_physical_max_read(self.source.class, &self.source.cells,
            &self.claims, &row.bytes, wire)
    }
}

struct Composite<'p, 'a, 'm> {
    work: NativeWorkEndpointAuthorLease<'p>,
    max: MaxEvidence<'p, 'a, 'm>,
    complete: Cell<bool>,
}

struct UpperView<'v, 'p, 'a, 'm>(&'v Composite<'p, 'a, 'm>);
struct MaxView<'v, 'p, 'a, 'm>(&'v Composite<'p, 'a, 'm>);

fn checked_gate<R>(complete: &Cell<bool>, read: impl FnOnce() -> Result<R, String>)
    -> Result<R, String> {
    if !complete.get() {
        return Err("C581 coactive requires dual qualification".into());
    }
    let result = read();
    if result.is_err() { complete.set(false); }
    result
}

fn qualify_gate(complete: &Cell<bool>, work: impl FnOnce() -> Result<(), String>,
    max: impl FnOnce() -> Result<(), String>) -> Result<(), String> {
    complete.set(false);
    work()?;
    max()?;
    complete.set(true);
    Ok(())
}

impl<'p, 'a, 'm> Composite<'p, 'a, 'm> {
    fn row(&self) -> &NativePackedRow { &self.work.local.row }

    fn qualify(&self, producer: &NativeOwnerProducer<'_>, stream: &MaxStream<'_>)
        -> Result<(), String> {
        qualify_gate(&self.complete,
            || {
                self.work.require_live_source(producer)?;
                self.max.require_live_source(producer, stream)?;
                self.work.check_complete()?;
                Ok(())
            },
            || self.max.check_on(self.row()))
    }

    fn checked<R>(&self, read: impl FnOnce() -> Result<R, String>) -> Result<R, String> {
        checked_gate(&self.complete, read)
    }

    fn views<'v>(&'v self)
        -> Result<(UpperView<'v, 'p, 'a, 'm>, MaxView<'v, 'p, 'a, 'm>), String> {
        self.checked(|| Ok((UpperView(self), MaxView(self))))
    }
}

impl UpperView<'_, '_, '_, '_> {
    fn read(&self, wire: usize) -> Result<(NativeWorkEndpointAuthor, Fr), String> {
        self.0.checked(|| self.0.work.checked_upper_fr(wire))
    }
}
impl MaxView<'_, '_, '_, '_> {
    fn read(&self, wire: usize) -> Result<(MaxReplayAuthor, Fr), String> {
        self.0.checked(|| self.0.max.read_on(self.0.row(), wire))
    }
}

fn produce_exact_tail_coactive<'p, 'a, 'm>(
    producer: &'p NativeOwnerProducer<'a>, stream: &'p MaxStream<'m>,
) -> Result<Composite<'p, 'a, 'm>, String> {
    let admission = CoactiveAdmission::new(producer, stream)?;
    let parent = producer.work_local_parent(OWNER)?;
    let class = c576_max_route(OWNER, producer.roster.owner_class(OWNER as u64)?)?;
    stream.closed_native_snapshot(producer.plan, producer.input)?;
    let cells = stream.closed_owner_cells(OWNER)?;
    let max = c512c_checked_max_cells(OWNER, &cells)?;
    let binding = HeaderSourceBinding::for_plan(producer.plan, OWNER)?;
    let source = NativeScheduledMaxSource { stream, binding: binding.clone(), cells, max, class };
    let tree = NativeTreeSourceLease::from_prefix(producer.plan, producer.input, OWNER)?;
    tree.check_binding(&binding)?;
    tree.check_author()?;
    let mut capture_out = None;
    let mut daa_out = None;
    let mut claims_out = None;
    let row = producer.produce_inner_with_cap0_and_c496(
        OWNER, AssemblyFault::None, None,
        #[cfg(test)] None,
        #[cfg(test)] false,
        #[cfg(test)] None,
        Some(&mut daa_out), // DAA, not a row borrow.
        None, // Cap0
        None, // Cap1
        None, // overlay
        None, // C374
        None, // Score
        None, // Map
        None, // padding capture
        None, // mixed capture
        None, // genesis capture
        None, // C496
        None, // C498 source
        None, // C498 output
        None, // regular census
        Some(&source),
        Some(&mut claims_out),
        Some(&mut capture_out),
        Some(&admission),
    )?;
    // The three temporary output borrows and &source call borrow end here.
    let operands = crate::h21_work_local_source::operand_domain(OWNER)?.into_iter()
        .map(|wire| (wire, Fr::from(((row.bytes[(wire % WIDTH) / 8]
            >> ((wire % WIDTH) % 8)) & 1) as u64))).collect();
    let local = WorkLocalLease { source: producer, parent, owner: OWNER,
        height: OWNER + 2, row,
        terms: crate::h21_work_local_source::canonical_terms(producer.plan, OWNER)?,
        operands, d: producer.native_work_d_projection(OWNER)? };
    let work = NativeWorkEndpointAuthorLease { local, tree,
        capture: capture_out.ok_or("C580 type slice missing Tree capture")?,
        binding: binding.clone(), complete_checked: Cell::new(false) };
    let payload = daa_out.ok_or("C580 type slice missing DAA output")?;
    let DaaSourcePayload::CarryZero(banks) = payload else {
        return Err("C580 type slice requires CarryZero".into());
    };
    let daa = NativeDaaSourceLease { _source: producer, binding,
        author: DaaSourceAuthor::CarryZero, source: DaaSourcePayload::CarryZero(banks),
        #[cfg(test)] read_count: Cell::new(0),
        #[cfg(test)] synthetic_class: None };
    let evidence = MaxEvidence { daa, source,
        claims: claims_out.ok_or("C580 type slice missing MAX claims")? };
    let composite = Composite { work, max: evidence, complete: Cell::new(false) };
    composite.qualify(producer, stream)?;
    Ok(composite)
}

// Both views coexist, both are used, and both reach the Work-owned row.
fn observe_both(composite: &Composite<'_, '_, '_>) -> Result<(), String> {
    let (upper, max) = composite.views()?;
    let _upper_value = upper.read(OWNER * WIDTH + C512I_UPPER_BASE)?;
    let _max_value = max.read(OWNER * WIDTH + C512C_MAX_BASE[1])?;
    if !std::ptr::eq(upper.0.row(), max.0.row()) {
        return Err("C580 type slice requires one retained row".into());
    }
    Ok(())
}

#[cfg(test)]
#[derive(Clone, Copy)]
enum C582AdmissionFault {
    WrongOwner, OccupiedWork, TamperedToken, OtherProducer, OtherStream,
}

// Every case enters the real private builder with one changed input. The
// counter starts immediately before admission and must stay at zero.
#[cfg(test)]
fn c582_rejected_before_assembly(producer: &NativeOwnerProducer<'_>,
    stream: &MaxStream<'_>, other_stream: &MaxStream<'_>, fault: C582AdmissionFault)
    -> Result<(), String> {
    let mut admission = CoactiveAdmission::new(producer, stream)?;
    if matches!(fault, C582AdmissionFault::TamperedToken) {
        admission.binding.owner += 1;
    }
    let class = scheduled_max_class(OWNER)?;
    let cells = stream.closed_owner_cells(OWNER)?;
    let max = c512c_checked_max_cells(OWNER, &cells)?;
    let binding = HeaderSourceBinding::for_plan(producer.plan, OWNER)?;
    let source_stream = if matches!(fault, C582AdmissionFault::OtherStream) {
        other_stream
    } else { stream };
    let source = NativeScheduledMaxSource {
        stream: source_stream, binding, cells, max, class,
    };
    let alternate = if matches!(fault, C582AdmissionFault::OtherProducer) {
        Some(NativeOwnerProducer::new_for_history(producer.plan, producer.input)?)
    } else { None };
    let writer = alternate.as_ref().unwrap_or(producer);
    let owner = if matches!(fault, C582AdmissionFault::WrongOwner) {
        OWNER + 1
    } else { OWNER };
    let mut capture_out = if matches!(fault, C582AdmissionFault::OccupiedWork) {
        Some(WorkEndpointCapture::new(OWNER)?)
    } else { None };
    let capture_state = |capture: &WorkEndpointCapture| {
        (capture.owner, capture.phase, capture.events.len(), capture.packed_identity)
    };
    let before_capture = capture_out.as_ref().map(&capture_state);
    let mut daa_out = None;
    let mut claims_out = None;
    C578_NATIVE_ASSEMBLIES.with(|count| -> Result<(), String> {
        if count.get().is_some() {
            return Err("C582 nested assembly counter".into());
        }
        count.set(Some(0));
        Ok(())
    })?;
    let result = writer.produce_inner_with_cap0_and_c496(
        owner, AssemblyFault::None, None,
        None, false, None,
        Some(&mut daa_out),
        None, None, None, None, None, None,
        None, None, None, None, None, None,
        None, Some(&source), Some(&mut claims_out),
        Some(&mut capture_out), Some(&admission),
    );
    let assemblies = C578_NATIVE_ASSEMBLIES.with(|count| count.replace(None));
    let expected = match fault {
        C582AdmissionFault::WrongOwner | C582AdmissionFault::OccupiedWork =>
            "C581 exact-tail coactive admission",
        C582AdmissionFault::TamperedToken | C582AdmissionFault::OtherProducer
            | C582AdmissionFault::OtherStream =>
            "C581 coactive token/source identity",
    };
    if result.err().as_deref() != Some(expected) || assemblies != Some(0)
        || capture_out.as_ref().map(&capture_state) != before_capture
        || daa_out.is_some() || claims_out.is_some() {
        return Err("C582 admission fault reached assembly or published output".into());
    }
    Ok(())
}

#[cfg(test)]
fn c582_original_fr_revocation(composite: &mut Composite<'_, '_, '_>,
    producer: &NativeOwnerProducer<'_>, stream: &MaxStream<'_>)
    -> Result<(), String> {
    let upper_wire = OWNER * WIDTH + C512I_UPPER_BASE;
    let max_wire = OWNER * WIDTH + C512C_MAX_BASE[1];
    let (max_index, max_cell) = composite.max.source.cells.iter().enumerate().skip(224)
        .find(|(_, cell)| cell.2.is_zero()).map(|(index, cell)| (index, *cell))
        .ok_or("C582 no zero original MAX Fr")?;
    let max_local = max_cell.0 % WIDTH;
    if composite.row().bytes[max_local / 8] & (1 << (max_local % 8)) != 0 {
        return Err("C582 MAX packed zero premise".into());
    }
    composite.max.source.cells[max_index].2 = Fr::from(2u64);
    {
        let (upper, max) = composite.views()?;
        if max.read(max_cell.0).err().as_deref()
            != Some("C576 original MAX Fr is not Boolean")
            || upper.read(upper_wire).is_ok() || max.read(max_wire).is_ok()
            || composite.row().bytes[max_local / 8] & (1 << (max_local % 8)) != 0 {
            return Err("C582 MAX Fr2 failed shared revocation".into());
        }
    }
    composite.max.source.cells[max_index] = max_cell;
    if composite.views().is_ok() {
        return Err("C582 MAX Fr restoration reopened views".into());
    }
    composite.qualify(producer, stream)?;
    observe_both(composite)?;

    let (upper_index, upper_event) = composite.work.capture.events[..224]
        .iter().enumerate().find(|(_, event)| event.2.is_zero())
        .map(|(index, event)| (index, *event))
        .ok_or("C582 no zero original Upper Fr")?;
    if composite.row().bytes[upper_event.0 / 8]
        & (1 << (upper_event.0 % 8)) != 0 {
        return Err("C582 Upper packed zero premise".into());
    }
    composite.work.capture.events[upper_index].2 = Fr::from(2u64);
    {
        let (upper, max) = composite.views()?;
        if upper.read(OWNER * WIDTH + upper_event.0).err().as_deref()
            != Some("C577 original Work endpoint Fr is not Boolean")
            || upper.read(upper_wire).is_ok() || max.read(max_wire).is_ok()
            || composite.row().bytes[upper_event.0 / 8]
                & (1 << (upper_event.0 % 8)) != 0 {
            return Err("C582 Upper Fr2 failed shared revocation".into());
        }
    }
    composite.work.capture.events[upper_index] = upper_event;
    if composite.views().is_ok() {
        return Err("C582 Upper Fr restoration reopened views".into());
    }
    composite.qualify(producer, stream)?;
    observe_both(composite)
}

// Called inside the existing pinned-frame native test after its one full MAX
// stream has already closed. This creates one additional coactive assembly.
#[cfg(test)]
pub(super) fn native_coactive_probe(producer: &NativeOwnerProducer<'_>,
    stream: &MaxStream<'_>, other_stream: &MaxStream<'_>) -> Result<(), String> {
    if other_stream.remaining_owners() != 7_683 {
        return Err("C582 alternate MAX stream must be empty".into());
    }
    for fault in [C582AdmissionFault::WrongOwner, C582AdmissionFault::OccupiedWork,
        C582AdmissionFault::TamperedToken, C582AdmissionFault::OtherProducer,
        C582AdmissionFault::OtherStream] {
        c582_rejected_before_assembly(producer, stream, other_stream, fault)?;
    }
    let mut composite = produce_exact_tail_coactive(producer, stream)?;
    let (upper, max) = composite.views()?;
    let upper_wire = OWNER * WIDTH + C512I_UPPER_BASE;
    let max_wire = OWNER * WIDTH + C512C_MAX_BASE[1];
    upper.read(upper_wire)?;
    max.read(max_wire)?;
    if !std::ptr::eq(upper.0.row(), max.0.row()) {
        return Err("C581 coactive views did not share one row".into());
    }
    if max.read(OWNER * WIDTH + C512C_MAX_BASE[0]).is_ok()
        || upper.read(upper_wire).is_ok() || max.read(max_wire).is_ok() {
        return Err("C581 MAX read failure did not revoke both views".into());
    }
    composite.qualify(producer, stream)?;
    if upper.read(OWNER * WIDTH + C512I_WORK_D_BASE).is_ok()
        || upper.read(upper_wire).is_ok() || max.read(max_wire).is_ok() {
        return Err("C581 Upper read failure did not revoke both views".into());
    }
    composite.qualify(producer, stream)?;
    upper.read(upper_wire)?;
    max.read(max_wire)?;
    drop(upper);
    drop(max);
    c582_original_fr_revocation(&mut composite, producer, stream)
}

fn exclusive_marker(composite: &mut Composite<'_, '_, '_>) {
    composite.complete.set(false);
}

// Positive controls use the same real declarations as the isolated failures.
fn positive_return_owned<'p, 'a, 'm>(producer: &'p NativeOwnerProducer<'a>,
    stream: &'p MaxStream<'m>) -> Result<Composite<'p, 'a, 'm>, String> {
    let composite = produce_exact_tail_coactive(producer, stream)?;
    composite.qualify(producer, stream)?;
    observe_both(&composite)?;
    Ok(composite)
}

fn positive_producer_drop<'a, 'm>(producer: NativeOwnerProducer<'a>,
    stream: &MaxStream<'m>) -> Result<(), String> {
    let composite = produce_exact_tail_coactive(&producer, stream)?;
    composite.qualify(&producer, stream)?;
    observe_both(&composite)?;
    drop(composite);
    drop(producer);
    Ok(())
}

fn positive_stream_drop<'a, 'm>(producer: &NativeOwnerProducer<'a>,
    stream: MaxStream<'m>) -> Result<(), String> {
    let composite = produce_exact_tail_coactive(producer, &stream)?;
    composite.qualify(producer, &stream)?;
    observe_both(&composite)?;
    drop(composite);
    drop(stream);
    Ok(())
}

fn positive_exclusive<'a, 'm>(producer: &NativeOwnerProducer<'a>,
    stream: &MaxStream<'m>) -> Result<(), String> {
    let mut composite = produce_exact_tail_coactive(producer, stream)?;
    composite.qualify(producer, stream)?;
    {
        let (upper, max) = composite.views()?;
        let _ = upper.read(OWNER * WIDTH + C512I_UPPER_BASE)?;
        let _ = max.read(OWNER * WIDTH + C512C_MAX_BASE[1])?;
    }
    exclusive_marker(&mut composite);
    composite.qualify(producer, stream)?;
    observe_both(&composite)
}

// Select exactly one expected-failure configuration after a green positive
// configuration. Require its indicated diagnostic, not merely a nonzero exit.
#[cfg(c580_type_fail = "escape")]
fn negative_escape<'p, 'a, 'm>(producer: &'p NativeOwnerProducer<'a>,
    stream: &'p MaxStream<'m>) -> Result<UpperView<'p, 'p, 'a, 'm>, String> {
    let composite = produce_exact_tail_coactive(producer, stream)?;
    composite.qualify(producer, stream)?;
    let (upper, max) = composite.views()?;
    let _ = max.read(OWNER * WIDTH + C512C_MAX_BASE[1])?;
    Ok(upper) // C580-FAIL-ESCAPE: returned view borrows local composite.
}

#[cfg(c580_type_fail = "producer_drop")]
fn negative_producer_drop<'a, 'm>(producer: NativeOwnerProducer<'a>,
    stream: &MaxStream<'m>) -> Result<(), String> {
    let composite = produce_exact_tail_coactive(&producer, stream)?;
    composite.qualify(&producer, stream)?;
    drop(producer); // C580-FAIL-PRODUCER: move while composite still borrows.
    observe_both(&composite)
}

#[cfg(c580_type_fail = "stream_drop")]
fn negative_stream_drop<'a, 'm>(producer: &NativeOwnerProducer<'a>,
    stream: MaxStream<'m>) -> Result<(), String> {
    let composite = produce_exact_tail_coactive(producer, &stream)?;
    composite.qualify(producer, &stream)?;
    drop(stream); // C580-FAIL-STREAM: move while composite still borrows.
    observe_both(&composite)
}

#[cfg(c580_type_fail = "exclusive")]
fn negative_exclusive<'a, 'm>(producer: &NativeOwnerProducer<'a>,
    stream: &MaxStream<'m>) -> Result<(), String> {
    let mut composite = produce_exact_tail_coactive(producer, stream)?;
    composite.qualify(producer, stream)?;
    let (upper, max) = composite.views()?;
    exclusive_marker(&mut composite); // C580-FAIL-EXCLUSIVE: live shared views.
    let _ = upper.read(OWNER * WIDTH + C512I_UPPER_BASE)?;
    let _ = max.read(OWNER * WIDTH + C512C_MAX_BASE[1])?;
    Ok(())
}

#[cfg(test)]
mod c581_no_frame_tests {
    use super::*;
    use crate::daa_history_roster::OwnerClass;

    #[test]
    fn exact_tail_admission_shape_positive_and_single_faults() {
        let good = |owner, height, class, role, activity, work, source, claims, daa, other| {
            require_exact_shape(owner, height, class, role, activity,
                work, source, claims, daa, other)
        };
        let exact = ([false, true], [false, false]);
        good(OWNER, HEIGHT, OwnerClass::Carry, leaf::Role::Genuine,
            exact, true, true, true, true, false).unwrap();
        assert!(good(OWNER + 1, HEIGHT, OwnerClass::Carry, leaf::Role::Genuine,
            exact, true, true, true, true, false).is_err(),
            "wrong owner must fail before assembly");
        assert!(good(OWNER, HEIGHT + 1, OwnerClass::Carry, leaf::Role::Genuine,
            exact, true, true, true, true, false).is_err());
        assert!(good(OWNER, HEIGHT, OwnerClass::Initial, leaf::Role::Genuine,
            exact, true, true, true, true, false).is_err());
        for activity in [([true, false], [false, false]),
            ([true, true], [false, false]), ([false, false], [false, false]),
            ([false, true], [true, false])] {
            assert!(good(OWNER, HEIGHT, OwnerClass::Carry, leaf::Role::Genuine,
                activity, true, true, true, true, false).is_err());
        }
        for (work, source, claims, daa, other) in [
            (false, true, true, true, false), (true, false, true, true, false),
            (true, true, false, true, false), (true, true, true, false, false),
            (true, true, true, true, true)] {
            assert!(good(OWNER, HEIGHT, OwnerClass::Carry, leaf::Role::Genuine,
                exact, work, source, claims, daa, other).is_err());
        }
    }

    #[test]
    fn two_borrowed_reader_paths_share_fail_closed_gate() {
        let complete = Cell::new(false);
        assert!(checked_gate(&complete, || Ok(1)).is_err());
        complete.set(true); // Models successful dual qualification, not admission.
        let upper = || checked_gate(&complete, || Ok(7));
        let max = || checked_gate(&complete, || Ok(11));
        assert_eq!(upper().unwrap(), 7);
        assert_eq!(max().unwrap(), 11);
        assert!(checked_gate::<()>(&complete, || Err("MAX read fault".into())).is_err());
        assert!(!complete.get());
        assert!(upper().is_err() && max().is_err());
        complete.set(true);
        assert!(checked_gate::<()>(&complete, || Err("Upper read fault".into())).is_err());
        assert!(upper().is_err() && max().is_err());
        qualify_gate(&complete, || Ok(()), || Err("MAX qualification fault".into()))
            .unwrap_err();
        assert!(!complete.get());
        assert!(upper().is_err() && max().is_err());
        qualify_gate(&complete, || Ok(()), || Ok(())).unwrap();
        assert_eq!(upper().unwrap(), 7);
        assert_eq!(max().unwrap(), 11);
    }
}

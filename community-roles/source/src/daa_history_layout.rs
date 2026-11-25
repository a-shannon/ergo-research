//! Bounded physical-slot coefficients for the complete mature DAA relation.
//!
//! This is a coefficient/owner adapter. It neither constructs a historical
//! witness nor authenticates a chain, PoW, or consensus history.
use ark_bn254::Fr;
use ark_ff::{One, Zero};

use crate::{
    daa_count, daa_finish,
    daa_header_window::{self, Action, SelectedWindow},
    daa_integer::Epoch,
    daa_schedule_wiring::{self, DaaScheduleWiring, FieldPort, PortFamily, ScheduleDomain},
    header_compact_links, header_hash, header_order,
    mapped_daa_plan::{MappedDaaPlan, MAPPED_INPUT_LEN, MAPPED_INPUT_LOG, ORIGINAL_INPUT_LEN},
    segment_relation,
    serializer::{self, Compiled as CompiledSerializer},
    sparse::{self, Circuit},
    wiring::{self, RightIndex},
    work_tree_layout,
};

const SLOT_LOG: usize = 20;
const SLOT_LEN: usize = 1 << SLOT_LOG;
const ARITHMETIC_ROW_LOG: usize = 17;
const ALIAS_ROW_LOG: usize = 10;
const HEADER_BOUNDARY_ROW_LOG: usize = 19;
const IMPORT_COUNT: usize = 896;
const A4_RELEASE_ROWS: std::ops::Range<usize> = 348_440..356_632;

/// Compose the full serializer with the compact point/order/hash boundary.
/// Only the final attached relation leaves this factory.
pub(crate) fn full_header_boundary(
    fields: Option<&serializer::Fields>,
) -> Result<header_compact_links::Joined, String> {
    let mut compact = header_compact_links::build(fields)?;
    let spans = [
        compact.base.base.released_rows.clone(),
        compact.base.released_rows.clone(),
        compact.released_rows.clone(),
    ];
    let base = &mut compact.base.base.base;
    let baseline = work_tree_layout::shared_baseline()?;
    if base.boundary.input_len != SLOT_LEN
        || base.boundary.row_count != 1 << HEADER_BOUNDARY_ROW_LOG
        || base.boundary.terms.len() != 421_353
        || base
            .boundary
            .terms
            .windows(2)
            .any(|pair| pair[0].row > pair[1].row)
        || work_tree_layout::hash_terms(&base.boundary.terms)
            != baseline.inventory.old_boundary_blake2b256
    {
        return Err(
            "compact source fingerprint or shape changed before serializer attachment".into(),
        );
    }
    let used_rows = 12_836..274_980;
    restore_compact_anchors(
        &mut base.boundary,
        base.digest_boolean_rows.end,
        segment_relation::DIGEST_OFFSET + 256,
        &spans,
        &used_rows,
    )?;
    let attached = segment_relation::attach_serializer_relation(base)?;
    if attached != used_rows
        || base.remaining_padding_rows != (274_980..405_784)
        || base.boundary.input_len != SLOT_LEN
        || base.boundary.row_count != 1 << HEADER_BOUNDARY_ROW_LOG
        || base.boundary.terms.len() != 474_755
    {
        return Err("complete compact serializer boundary geometry changed".into());
    }
    Ok(compact)
}

const FINAL_HEADER_BOUNDARY_BLAKE2B256: &str =
    "580f92b15945029ea82a9f1e0b97cfc9917df940380211a8fd6701e39336ab76";

fn validate_final_header_boundary(boundary: &Circuit) -> Result<(), String> {
    if boundary.input_len != SLOT_LEN {
        return Err("canonical final header boundary input width changed".into());
    }
    if boundary.row_count != 1 << HEADER_BOUNDARY_ROW_LOG {
        return Err("canonical final header boundary row count changed".into());
    }
    if boundary.terms.len() != 474_755 {
        return Err("canonical final header boundary term count changed".into());
    }
    if work_tree_layout::hash_terms(&boundary.terms) != FINAL_HEADER_BOUNDARY_BLAKE2B256 {
        return Err("canonical final header boundary fingerprint changed".into());
    }
    Ok(())
}

/// Immutable assignment support for the canonical complete header boundary.
/// The circuit is constructed and pinned once; each call returns a fresh input.
pub(crate) struct HeaderAssignmentTemplate {
    canonical: header_compact_links::Joined,
    compression: &'static crate::circuit::CompressionLayout,
}

impl HeaderAssignmentTemplate {
    pub(crate) fn new() -> Result<Self, String> {
        let canonical = full_header_boundary(None)?;
        let boundary = &canonical.base.base.base.boundary;
        validate_final_header_boundary(boundary)?;
        let compression = &work_tree_layout::shared_baseline()?.compression;
        if canonical.base.base.base.serializer.circuit.input_len != header_hash::SERIALIZER_WIDTH {
            return Err("canonical template serializer input width changed".into());
        }
        Ok(Self { canonical, compression })
    }

    pub(crate) fn assign(&self, fields: &serializer::Fields) -> Result<Vec<Fr>, String> {
        let segment = &self.canonical.base.base.base;
        let mut input = header_hash::assign_from_template(
            self.compression,
            &segment.serializer,
            fields,
        )?;
        if input.len() != SLOT_LEN {
            return Err("header template assignment input width mismatch".into());
        }

        let selectors = std::array::from_fn::<_, 5, _>(|index| header_hash::AUX_OFFSET + index);
        let selected = selectors
            .iter()
            .enumerate()
            .filter_map(|(index, &wire)| input[wire].is_one().then_some(index))
            .collect::<Vec<_>>();
        if selected.len() != 1
            || selectors
                .iter()
                .any(|&wire| !input[wire].is_zero() && !input[wire].is_one())
        {
            return Err("header assignment has malformed digest selectors".into());
        }
        for bit in 0..256 {
            let output = self.compression.output[bit / 64][bit % 64];
            let value = input[selected[0] * header_hash::CORE_WIDTH + output];
            if !value.is_zero() && !value.is_one() {
                return Err("header output assignment is non-Boolean".into());
            }
            input[segment.digest_wires[bit]] = value;
        }

        let point_bits = crate::point_membership::witness(fields.pk, fields.w)?;
        if point_bits.len() != crate::segment_points::POINT_WIDTH {
            return Err("point membership witness width changed".into());
        }
        for (wire, bit) in input[crate::segment_points::POINT_OFFSET
            ..crate::segment_points::POINT_OFFSET + crate::segment_points::POINT_WIDTH]
            .iter_mut()
            .zip(point_bits)
        {
            *wire = Fr::from(bit as u64);
        }

        for bit in 0..header_compact_links::HASH_WIDTH {
            let source = if bit < 256 {
                segment.parent_wires[bit]
            } else {
                segment.digest_wires[bit - 256]
            };
            input[header_compact_links::HASH_OFFSET + bit] = input[source];
        }
        Ok(input)
    }

    /// Fill only the existing order bank, using the canonical arithmetic.
    pub(crate) fn assign_order(
        &self,
        input: &mut [Fr],
        fields: &serializer::Fields,
        previous_height: u32,
        previous_time: i64,
        first: bool,
    ) -> Result<(), String> {
        if input.len() != SLOT_LEN {
            return Err("order input width mismatch".into());
        }
        let bits = header_order::witness(
            fields.height,
            fields.timestamp,
            previous_height,
            previous_time,
            first,
        )?;
        if bits.len() != header_order::ORDER_WIDTH {
            return Err("canonical order witness width changed".into());
        }
        for (wire, bit) in input[header_order::ORDER_OFFSET
            ..header_order::ORDER_OFFSET + header_order::ORDER_WIDTH]
            .iter_mut()
            .zip(bits)
        {
            *wire = Fr::from(bit as u64);
        }
        Ok(())
    }
}

fn restore_compact_anchors(
    boundary: &mut Circuit,
    row_base: usize,
    wire_base: usize,
    spans: &[std::ops::Range<usize>],
    used_rows: &std::ops::Range<usize>,
) -> Result<(), String> {
    if spans != [143_640..151_832, 151_832..152_856, 152_856..153_368]
        || used_rows != &(12_836..274_980)
        || row_base != used_rows.start
        || wire_base != segment_relation::DIGEST_OFFSET + 256
    {
        return Err("compact anchor restoration spans or coordinate bases changed".into());
    }
    let zero_gate = crate::gkr::Gate {
        left: 0,
        right: 0,
        c0: Fr::zero(),
        c1: Fr::zero(),
        c2: Fr::zero(),
        c3: Fr::zero(),
    };
    let mut groups = Vec::with_capacity(3);
    for span in spans {
        if span.start < used_rows.start || span.end > used_rows.end {
            return Err("compact restoration lies outside the serializer overlay".into());
        }
        let first = boundary.terms.partition_point(|term| term.row < span.start);
        let after = boundary.terms.partition_point(|term| term.row < span.end);
        if after - first != span.len() {
            return Err("compact restoration term count changed".into());
        }
        for (offset, term) in boundary.terms[first..after].iter().enumerate() {
            if term.row != span.start + offset || term.gate != zero_gate {
                return Err("compact restoration expected one exact zero gate per row".into());
            }
            let wire = wire_base
                .checked_add(
                    term.row
                        .checked_sub(row_base)
                        .ok_or("compact anchor row precedes its coordinate base")?,
                )
                .ok_or("compact anchor wire overflow")?;
            if wire >= boundary.input_len {
                return Err("restored anchor escapes its input domain".into());
            }
        }
        groups.push((first, after));
    }
    // Check every group before changing any gate. These transient anchors are
    // immediately consumed by the complete serializer attachment.
    for (first, after) in groups {
        for term in &mut boundary.terms[first..after] {
            term.gate = crate::gkr::Gate {
                left: wire_base + term.row - row_base,
                right: 0,
                c0: Fr::zero(),
                c1: Fr::one(),
                c2: Fr::zero(),
                c3: Fr::zero(),
            };
        }
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PhysicalPort {
    serializer_wire: usize,
    daa_wire: usize,
    offset: u64,
}

/// Fixed maps and coefficient methods for one native mature DAA epoch.
/// Construction derives every DAA endpoint from compiler-owned templates.
pub(crate) struct DaaHistoryLayout {
    epoch: Epoch,
    schedule: ScheduleDomain,
    native_template: daa_finish::CompiledFinish,
    circuit: Circuit,
    arithmetic_shape: sparse::Shape,
    original_to_mapped: Vec<usize>,
    phase_banks: [(usize, usize); 4],
    ports: Vec<PhysicalPort>,
    a4_wires: std::ops::Range<usize>,
    a4_rows: std::ops::Range<usize>,
    anchor_delta: usize,
}

impl DaaHistoryLayout {
    pub(crate) fn compile(
        epoch: Epoch,
        history_slots: u64,
        slot_log: usize,
    ) -> Result<Self, String> {
        if slot_log > 21 || history_slots == 0 {
            return Err("physical history dimensions exceed the fixed profile".into());
        }
        let domain_len = 1u64
            .checked_shl(slot_log as u32)
            .ok_or("physical history domain overflow")?;
        if history_slots > domain_len || history_slots > daa_header_window::MAX_CHILD_HEIGHT as u64
        {
            return Err("physical history count exceeds its declared slot domain".into());
        }
        let schedule = ScheduleDomain::new(history_slots, slot_log)?;
        let serializer = serializer::build(None)?;
        if serializer.circuit.input_len != 1 << 17 {
            return Err("full serializer source template geometry changed".into());
        }
        let mut template = daa_schedule_wiring::compile_epoch_template(epoch, true)?;
        let mapped = MappedDaaPlan::compile(&template)?;
        if mapped.circuit().input_len != MAPPED_INPUT_LEN
            || mapped.circuit().row_count != 1 << ARITHMETIC_ROW_LOG
        {
            return Err("complete mapped DAA relation geometry changed".into());
        }
        let arithmetic_shape = sparse::validate(mapped.circuit(), 0)
            .map_err(|error| format!("mapped arithmetic shape rejected: {error:?}"))?;
        if arithmetic_shape.input_bits != MAPPED_INPUT_LOG
            || arithmetic_shape.row_bits != ARITHMETIC_ROW_LOG
        {
            return Err("mapped DAA arithmetic must use its exact 17-bit row point".into());
        }

        let wiring = DaaScheduleWiring::compile()?;
        let ports = wiring.ports(epoch);
        if ports.len() != IMPORT_COUNT {
            return Err("code-owned physical import roster changed".into());
        }
        for port in ports {
            offset_cache_index(epoch, port.offset(epoch))?;
        }
        let physical_ports = ports
            .iter()
            .map(|port| {
                Ok(PhysicalPort {
                    serializer_wire: header_hash::SERIALIZER_OFFSET
                        .checked_add(port.serializer_wire())
                        .ok_or("serializer physical wire overflow")?,
                    daa_wire: mapped.mapped_wire(port.daa_wire())?,
                    offset: port.offset(epoch),
                })
            })
            .collect::<Result<Vec<_>, String>>()?;

        let (circuit, original_to_mapped, banks) = mapped.into_history_parts();
        // The seed selects a fixed program, never source assignment authority.
        // Keep its circuit/consumed ledger and drop diagnostic witness storage.
        template.joined.joined.joined.witness = Vec::new();
        let canonical = full_header_boundary(None)?;
        let boundary = &canonical.base.base.base;
        if boundary.boundary.input_len != SLOT_LEN
            || boundary.boundary.row_count != 1 << HEADER_BOUNDARY_ROW_LOG
            || boundary.boundary.terms.len() != 474_755
        {
            return Err("canonical full header boundary fingerprint or shape changed".into());
        }
        for (index, bank) in banks.iter().take(3).enumerate() {
            let active = boundary.boundary.terms.iter().any(|term| {
                (bank.0..bank.1).contains(&term.gate.left)
                    || (bank.0..bank.1).contains(&term.gate.right)
            });
            if active {
                return Err(format!(
                    "A{} bank still has active boundary references",
                    index + 1
                ));
            }
        }
        let a4_wires = banks[3].0..banks[3].1;
        let mut anchor_rows = segment_relation::padding_anchor_row_ranges_for_wires(
            boundary,
            std::slice::from_ref(&a4_wires),
        )?;
        let a4_rows = anchor_rows.pop().ok_or("A4 anchor row map missing")?;
        if a4_rows != A4_RELEASE_ROWS || a4_rows.end - a4_rows.start != 8192 {
            return Err("canonical A4 anchor release geometry changed".into());
        }
        let anchor_delta = a4_wires
            .start
            .checked_sub(a4_rows.start)
            .ok_or("A4 anchor row/wire map is reversed")?;
        if a4_wires.end.checked_sub(a4_rows.end) != Some(anchor_delta) {
            return Err("A4 anchor row/wire map is not contiguous".into());
        }

        Ok(Self {
            epoch,
            schedule,
            native_template: template,
            circuit,
            arithmetic_shape,
            original_to_mapped,
            phase_banks: banks,
            ports: physical_ports,
            a4_wires,
            a4_rows,
            anchor_delta,
        })
    }

    pub(crate) fn epoch(&self) -> Epoch {
        self.epoch
    }

    pub(crate) fn import_count(&self) -> usize {
        self.ports.len()
    }

    /// Resolve an original DAA input through the immutable physical map used
    /// when this layout constructed its alias ports.
    pub(crate) fn mapped_port_wire(&self, original_wire: usize) -> Result<usize, String> {
        self.original_to_mapped
            .get(original_wire)
            .copied()
            .filter(|wire| *wire != usize::MAX)
            .ok_or_else(|| "physical DAA source wire is outside the mapped program".into())
    }

    /// Admit the native program and its consumed import ledger, then bind the
    /// producer's imported bits to a validated source window. Residual validity
    /// and historical authentication remain separate proof obligations.
    pub(crate) fn admit_selected(
        &self,
        selected: &SelectedWindow,
        compiled: &daa_finish::CompiledFinish,
    ) -> Result<MappedDaaPlan, String> {
        if selected.action() != Action::Retarget(self.epoch) {
            return Err("mature selected epoch mismatch".into());
        }
        let child_slot = u64::from(selected.child_height())
            .checked_sub(1)
            .ok_or("mature selected child outside consumer schedule")?;
        if self.schedule.contains_mature_retarget(child_slot) != Some(self.epoch) {
            return Err("mature selected child outside consumer schedule".into());
        }
        let expected = &self.native_template.joined.joined.joined;
        let actual = &compiled.joined.joined.joined;
        let circuit = actual
            .circuit
            .as_ref()
            .ok_or("mature producer circuit was not materialized")?;
        let expected_circuit = expected
            .circuit
            .as_ref()
            .ok_or("mature consumer template circuit missing")?;
        if circuit != expected_circuit {
            return Err("mature native circuit differs from consumer template".into());
        }
        if !same_native_semantic_count(&actual.count, &expected.count)
            || actual.witness.len() != ORIGINAL_INPUT_LEN
        {
            return Err("mature native semantic count or witness shape mismatch".into());
        }
        if !same_consumed_native_ledger(compiled, &self.native_template) {
            return Err("mature native consumed handles or checkpoint mismatch".into());
        }
        if actual.witness[actual.count.live_bits..]
            .iter()
            .any(|value| !value.is_zero())
        {
            return Err("mature producer native padding is nonzero".into());
        }
        // Only consumer-owned handles are used to read producer assignments.
        // SelectedWindow values are canonical source metadata, not seed values.
        let prediction = selected.prediction();
        for index in 0..8 {
            let external = &expected.external[index];
            if !matches_native_bits(
                &actual.witness,
                &external.nbits,
                u64::from(prediction.window.nbits[index]),
                32,
            ) || !matches_native_bits(
                &actual.witness,
                &external.start_timestamp,
                prediction.window.timestamps[index] as u64,
                64,
            ) || !matches_native_bits(
                &actual.witness,
                &external.end_timestamp,
                prediction.window.timestamps[index + 1] as u64,
                64,
            ) {
                return Err("mature selected source bit assignment mismatch".into());
            }
        }
        let child_nbits = self.native_template.child_nbits.as_ref()
            .ok_or("mature consumer template child nBits missing")?;
        if !matches_native_bits(
            &actual.witness,
            &self.native_template.joined.output.x0_bits,
            u64::from(prediction.x0),
            32,
        ) || !matches_native_bits(
            &actual.witness,
            child_nbits,
            u64::from(selected.child_nbits()),
            32,
        ) {
            return Err("mature selected source bit assignment mismatch".into());
        }
        let mapped = MappedDaaPlan::compile(compiled)?;
        if mapped.circuit() != &self.circuit
            || mapped.phase_bank_ranges() != self.phase_banks
            || self.original_to_mapped.iter().enumerate().any(|(index, &wire)| {
                mapped.mapped_wire(index).ok() != Some(wire)
            })
        {
            return Err("mature mapped program or coordinate ledger mismatch".into());
        }
        // Admission above checks all dynamic shapes before the existing port
        // validator can index external[7] or any typed import handle.
        let serializer = serializer::build(None)?;
        let wiring = DaaScheduleWiring::compile()?;
        validate_actual_ports(&serializer, compiled, &mapped, wiring.ports(self.epoch))?;
        Ok(mapped)
    }

    /// Emit one mature child's complete physical serializer-to-DAA relation.
    /// All geometry is checked before the first sink; this does not authenticate
    /// the source headers or establish historical inclusion.
    pub(crate) fn visit_alias_terms(
        &self,
        child_slot: u64,
        mut sink: impl FnMut(sparse::Term) -> Result<(), String>,
    ) -> Result<usize, String> {
        if child_slot >= self.schedule.upper_bound()
            || self.schedule.contains_mature_retarget(child_slot) != Some(self.epoch)
        {
            return Err("physical alias target is not a mature child of this epoch".into());
        }
        if self.ports.len() != IMPORT_COUNT {
            return Err("physical alias port roster changed".into());
        }
        let slot = usize::try_from(child_slot).map_err(|_| "physical alias slot overflow")?;
        let input_len = 1usize.checked_shl((SLOT_LOG + self.schedule.slot_log()) as u32)
            .ok_or("physical alias input dimension overflow")?;
        let row_count = 1usize.checked_shl((ALIAS_ROW_LOG + self.schedule.slot_log()) as u32)
            .ok_or("physical alias row dimension overflow")?;
        let target_base = slot.checked_mul(SLOT_LEN).ok_or("physical alias target overflow")?;
        let row_base = slot.checked_mul(1 << ALIAS_ROW_LOG).ok_or("physical alias row overflow")?;
        let mut terms = Vec::new();
        terms.try_reserve_exact(IMPORT_COUNT).map_err(|error| format!("physical alias allocation: {error}"))?;
        for (index, port) in self.ports.iter().enumerate() {
            let source = child_slot.checked_sub(port.offset).ok_or("physical alias source underflow")?;
            if source >= self.schedule.upper_bound()
                || port.serializer_wire >= SLOT_LEN || port.daa_wire >= SLOT_LEN
            {
                return Err("physical alias source or local endpoint outside profile".into());
            }
            let source_base = usize::try_from(source).map_err(|_| "physical alias source overflow")?
                .checked_mul(SLOT_LEN).ok_or("physical alias source base overflow")?;
            let row = row_base.checked_add(index).ok_or("physical alias row index overflow")?;
            let left = source_base.checked_add(port.serializer_wire).ok_or("physical alias left overflow")?;
            let right = target_base.checked_add(port.daa_wire).ok_or("physical alias right overflow")?;
            if row >= row_count || left >= input_len || right >= input_len {
                return Err("physical alias global endpoint outside profile".into());
            }
            terms.push(sparse::Term { row, gate: crate::gkr::Gate {
                left, right, c0: Fr::zero(), c1: Fr::one(), c2: -Fr::one(), c3: Fr::zero(),
            }});
        }
        for term in terms { sink(term)?; }
        Ok(IMPORT_COUNT)
    }

    pub(crate) fn mapped_relation(&self) -> &Circuit {
        &self.circuit
    }

    pub(crate) fn a4_anchor_rows(&self) -> std::ops::Range<usize> {
        self.a4_rows.clone()
    }

    /// Evaluate the complete mapped A1–A4 row relation in one physical slot.
    pub(crate) fn arithmetic_coefficients(
        &self,
        r: &[Fr],
        u: &[Fr],
        v: &[Fr],
    ) -> Result<[Fr; 4], String> {
        let input_bits = SLOT_LOG + self.schedule.slot_log();
        let row_bits = ARITHMETIC_ROW_LOG + self.schedule.slot_log();
        if r.len() != row_bits || u.len() != input_bits || v.len() != input_bits {
            return Err("physical arithmetic point dimensions rejected".into());
        }
        let mut coefficients = sparse::wiring(
            &self.circuit,
            &self.arithmetic_shape,
            &r[..ARITHMETIC_ROW_LOG],
            &u[..SLOT_LOG],
            &v[..SLOT_LOG],
        )
        .map_err(|error| format!("mapped arithmetic wiring rejected: {error:?}"))?;
        let active =
            self.same_slot_mask(&r[ARITHMETIC_ROW_LOG..], &u[SLOT_LOG..], &v[SLOT_LOG..], 0)?;
        for coefficient in &mut coefficients {
            *coefficient *= active;
        }
        Ok(coefficients)
    }

    /// Evaluate all 896 serializer-to-mapped-DAA aliases at physical slots.
    /// Source slots use each port's native epoch distance without wraparound.
    pub(crate) fn alias_coefficients(
        &self,
        r: &[Fr],
        u: &[Fr],
        v: &[Fr],
    ) -> Result<[Fr; 4], String> {
        let input_bits = SLOT_LOG + self.schedule.slot_log();
        let row_bits = ALIAS_ROW_LOG + self.schedule.slot_log();
        if r.len() != row_bits || u.len() != input_bits || v.len() != input_bits {
            return Err("physical alias point dimensions rejected".into());
        }
        let row_local = &r[..ALIAS_ROW_LOG];
        let serializer_local = &u[..SLOT_LOG];
        let daa_local = &v[..SLOT_LOG];
        let row_slots = &r[ALIAS_ROW_LOG..];
        let serializer_slots = &u[SLOT_LOG..];
        let daa_slots = &v[SLOT_LOG..];
        let mut cache: [Option<Fr>; 10] = [None; 10];
        let mut result = [Fr::zero(); 4];
        for (index, port) in self.ports.iter().enumerate() {
            let local = eq_index(row_local, index)
                * eq_index(serializer_local, port.serializer_wire)
                * eq_index(daa_local, port.daa_wire);
            if local.is_zero() {
                continue;
            }
            let cache_index = offset_cache_index(self.epoch, port.offset)?;
            let slot_weight = if let Some(weight) = cache[cache_index] {
                weight
            } else {
                let weight = daa_schedule_wiring::evaluate_mature_shift(
                    self.epoch,
                    &self.schedule,
                    row_slots,
                    serializer_slots,
                    daa_slots,
                    port.offset,
                    RightIndex::SameRow,
                )?;
                cache[cache_index] = Some(weight);
                weight
            };
            let weight = local * slot_weight;
            result[1] += weight;
            result[2] -= weight;
        }
        Ok(result)
    }

    /// Coefficient for the only releasable header-boundary zero family: A4.
    pub(crate) fn a4_release_coefficient(
        &self,
        r: &[Fr],
        u: &[Fr],
        v: &[Fr],
    ) -> Result<Fr, String> {
        let input_bits = SLOT_LOG + self.schedule.slot_log();
        let row_bits = HEADER_BOUNDARY_ROW_LOG + self.schedule.slot_log();
        if r.len() != row_bits || u.len() != input_bits || v.len() != input_bits {
            return Err("A4 release point dimensions rejected".into());
        }
        let mut padded_r = r[..HEADER_BOUNDARY_ROW_LOG].to_vec();
        padded_r.push(Fr::zero());
        let zero = vec![Fr::zero(); SLOT_LOG];
        let local = wiring::evaluate_shift(
            &u[..SLOT_LOG],
            &padded_r,
            &zero,
            self.anchor_delta as u64,
            self.a4_wires.start as u64,
            self.a4_wires.end as u64,
            0,
            RightIndex::GlobalZero,
        )? * eq_index(&v[..SLOT_LOG], 0);
        let active = self.same_slot_mask(
            &r[HEADER_BOUNDARY_ROW_LOG..],
            &u[SLOT_LOG..],
            &v[SLOT_LOG..],
            0,
        )?;
        Ok(local * active)
    }

    pub(crate) fn releases_anchor(&self, child_slot: u64, row: usize) -> bool {
        self.a4_rows.contains(&row)
            && self.schedule.contains_mature_retarget(child_slot) == Some(self.epoch)
    }

    fn same_slot_mask(
        &self,
        row_slots: &[Fr],
        left_slots: &[Fr],
        right_slots: &[Fr],
        offset: u64,
    ) -> Result<Fr, String> {
        daa_schedule_wiring::evaluate_mature_shift(
            self.epoch,
            &self.schedule,
            row_slots,
            left_slots,
            right_slots,
            offset,
            RightIndex::SameRow,
        )
    }
}

fn offset_cache_index(epoch: Epoch, offset: u64) -> Result<usize, String> {
    if offset == 0 {
        return Ok(9);
    }
    let step = epoch.length();
    if offset < 1 || (offset - 1) % step != 0 {
        return Err("physical port has an unexpected native sample offset".into());
    }
    let back = ((offset - 1) / step) as usize;
    if back > 8 {
        return Err("physical port exceeds the fixed nine-sample window".into());
    }
    Ok(back)
}

fn same_native_semantic_count(a: &crate::daa_integer::Count, b: &crate::daa_integer::Count) -> bool {
    let fields = |count: &crate::daa_integer::Count| {
        [
            count.live_bits, count.input_bits, count.padded_input_bits,
            count.residual_rows, count.padded_rows, count.terms,
            count.boolean_rows, count.linear_rows, count.bilinear_rows,
            count.maximum_column_signed_abs_bits, count.maximum_degree,
            count.source_nbits_bits, count.source_timestamp_bits, count.decoded_bits,
            count.wrapped_delta_bits, count.denominator_bits, count.numerator_bits,
            count.quotient_bits, count.remainder_bits, count.quotient_sign_bits,
            count.remainder_sign_bits, count.auxiliary_bits, count.padding_bits,
            count.peak_row_terms,
        ]
    };
    fields(a) == fields(b) && a.topology_blake2b256 == b.topology_blake2b256
}

fn same_consumed_native_ledger(
    actual: &daa_finish::CompiledFinish,
    expected: &daa_finish::CompiledFinish,
) -> bool {
    let actual_window = &actual.joined.joined.joined;
    let expected_window = &expected.joined.joined.joined;
    actual_window.external.len() == 8
        && actual_window.external.len() == expected_window.external.len()
        && actual_window.external.iter().zip(&expected_window.external).all(|(a, b)| {
            a.nbits == b.nbits
                && a.start_timestamp == b.start_timestamp
                && a.end_timestamp == b.end_timestamp
        })
        && actual.joined.joined.increment == expected.joined.joined.increment
        && actual.joined.increment == expected.joined.increment
        && actual.increment == expected.increment
        && actual.joined.output.x0_bits == expected.joined.output.x0_bits
        && actual.output.numeric_result == expected.output.numeric_result
        && actual.child_nbits.is_some()
        && actual.child_nbits == expected.child_nbits
}

fn matches_native_bits(witness: &[Fr], wires: &[usize], value: u64, width: usize) -> bool {
    width <= 64 && wires.len() == width && wires.iter().enumerate().all(|(bit, &wire)| {
        witness.get(wire) == Some(&Fr::from((value >> bit) & 1))
    })
}

fn validate_actual_ports(
    serializer: &CompiledSerializer,
    compiled: &daa_finish::CompiledFinish,
    mapped: &MappedDaaPlan,
    ports: &[FieldPort],
) -> Result<(), String> {
    let window = &compiled.joined.joined.joined;
    let timestamps = (0..9)
        .map(|index| {
            if index == 8 {
                &window.external[7].end_timestamp
            } else {
                &window.external[index].start_timestamp
            }
        })
        .collect::<Vec<_>>();
    let child_nbits = compiled
        .child_nbits
        .as_ref()
        .ok_or("child nBits map missing")?;
    if timestamps.iter().any(|bits| bits.len() != 64)
        || window.external.len() != 8
        || child_nbits.len() != 32
        || compiled.joined.output.x0_bits.len() != 32
    {
        return Err("actual DAA source import geometry changed".into());
    }
    if (0..7).any(|index| {
        window.external[index].end_timestamp != window.external[index + 1].start_timestamp
    }) {
        return Err("actual DAA adjacent timestamps are not shared".into());
    }
    for port in ports {
        let (serializer_wire, daa_wire) = match port.family() {
            PortFamily::Timestamp => (
                serializer.layout.fields.timestamp[port.field_index() % 64],
                timestamps[port.source_ordinal()][port.field_index() % 64],
            ),
            PortFamily::SampleNBits => (
                serializer.layout.fields.n_bits[port.field_index() % 32],
                window.external[port.source_ordinal() - 1].nbits[port.field_index() % 32],
            ),
            PortFamily::X0Height => (
                serializer.layout.fields.height[port.field_index()],
                compiled.joined.output.x0_bits[port.field_index()],
            ),
            PortFamily::ChildNBits => (
                serializer.layout.fields.n_bits[port.field_index()],
                child_nbits[port.field_index()],
            ),
        };
        if port.serializer_wire() != serializer_wire
            || mapped.mapped_wire(port.daa_wire())? != mapped.mapped_wire(daa_wire)?
        {
            return Err("seed and selected DAA physical endpoint maps diverge".into());
        }
    }
    Ok(())
}

fn eq_index(point: &[Fr], index: usize) -> Fr {
    point
        .iter()
        .enumerate()
        .fold(Fr::one(), |weight, (bit, coordinate)| {
            weight
                * if (index >> bit) & 1 == 1 {
                    *coordinate
                } else {
                    Fr::one() - coordinate
                }
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use ergo_header_core::Header;
    use serde::Deserialize;
    use std::collections::{HashMap, HashSet};

    const FIXTURE: &str = include_str!("../fixtures/mainnet-daa-windows-v1.json");

    #[derive(Deserialize)]
    struct Fixture {
        cases: Vec<FixtureCase>,
        headers: Vec<FixtureHeader>,
    }
    #[derive(Deserialize)]
    struct FixtureCase {
        child: u32,
        parent: u32,
        samples: Vec<u32>,
    }
    #[derive(Deserialize)]
    struct FixtureHeader {
        height: u32,
        raw_hex: String,
    }

    fn fixtures() -> (Fixture, HashMap<u32, Vec<u8>>) {
        let fixture: Fixture = serde_json::from_str(FIXTURE).unwrap();
        let headers = fixture
            .headers
            .iter()
            .map(|header| {
                let bytes = header
                    .raw_hex
                    .as_bytes()
                    .chunks_exact(2)
                    .map(|pair| u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).unwrap())
                    .collect::<Vec<_>>();
                assert_eq!(Header::decode(&bytes, None).unwrap().height, header.height);
                (header.height, bytes)
            })
            .collect::<HashMap<_, _>>();
        (fixture, headers)
    }

    fn selected(child: u32, fixture: &Fixture, headers: &HashMap<u32, Vec<u8>>) -> SelectedWindow {
        let case = fixture
            .cases
            .iter()
            .find(|case| case.child == child)
            .unwrap();
        let samples = case
            .samples
            .iter()
            .map(|height| headers.get(height).unwrap().as_slice())
            .collect::<Vec<_>>();
        let samples: [&[u8]; 9] = samples.try_into().unwrap();
        daa_header_window::select_window(
            headers.get(&case.parent).unwrap(),
            headers.get(&child).unwrap(),
            &samples,
        )
        .unwrap()
    }

    fn point(bits: usize, seed: u64) -> Vec<Fr> {
        (0..bits)
            .map(|index| Fr::from(seed.wrapping_add((index as u64 + 1) * 37)))
            .collect()
    }

    fn boolean_point(bits: usize, value: u64) -> Vec<Fr> {
        (0..bits)
            .map(|index| Fr::from((value >> index) & 1))
            .collect()
    }

    fn direct_arithmetic(
        layout: &DaaHistoryLayout,
        r: &[Fr],
        u: &[Fr],
        v: &[Fr],
        slot: u64,
    ) -> [Fr; 4] {
        let mut result = [Fr::zero(); 4];
        for term in &layout.circuit.terms {
            let weight = eq_index(&r[..ARITHMETIC_ROW_LOG], term.row)
                * eq_index(&u[..SLOT_LOG], term.gate.left)
                * eq_index(&v[..SLOT_LOG], term.gate.right);
            result[0] += weight * term.gate.c0;
            result[1] += weight * term.gate.c1;
            result[2] += weight * term.gate.c2;
            result[3] += weight * term.gate.c3;
        }
        let slot_weight = eq_index(&r[ARITHMETIC_ROW_LOG..], slot as usize)
            * eq_index(&u[SLOT_LOG..], slot as usize)
            * eq_index(&v[SLOT_LOG..], slot as usize);
        result.iter_mut().for_each(|value| *value *= slot_weight);
        result
    }

    fn direct_aliases(
        layout: &DaaHistoryLayout,
        r: &[Fr],
        u: &[Fr],
        v: &[Fr],
        slot: u64,
    ) -> [Fr; 4] {
        let mut result = [Fr::zero(); 4];
        for (index, port) in layout.ports.iter().enumerate() {
            let source = slot
                .checked_sub(port.offset)
                .expect("mature slot covers every sample");
            let weight = eq_index(&r[..ALIAS_ROW_LOG], index)
                * eq_index(&u[..SLOT_LOG], port.serializer_wire)
                * eq_index(&v[..SLOT_LOG], port.daa_wire)
                * eq_index(&r[ALIAS_ROW_LOG..], slot as usize)
                * eq_index(&u[SLOT_LOG..], source as usize)
                * eq_index(&v[SLOT_LOG..], slot as usize);
            result[1] += weight;
            result[2] -= weight;
        }
        result
    }

    fn direct_release(layout: &DaaHistoryLayout, r: &[Fr], u: &[Fr], v: &[Fr], slot: u64) -> Fr {
        let slot_weight = eq_index(&r[HEADER_BOUNDARY_ROW_LOG..], slot as usize)
            * eq_index(&u[SLOT_LOG..], slot as usize)
            * eq_index(&v[SLOT_LOG..], slot as usize);
        let local = (layout.a4_wires.clone()).fold(Fr::zero(), |sum, wire| {
            sum + eq_index(&u[..SLOT_LOG], wire)
                * eq_index(&r[..HEADER_BOUNDARY_ROW_LOG], wire - layout.anchor_delta)
                * eq_index(&v[..SLOT_LOG], 0)
        });
        slot_weight * local
    }

    fn residuals(circuit: &Circuit, input: &[Fr]) -> Vec<Fr> {
        let mut rows = vec![Fr::zero(); circuit.row_count];
        for term in &circuit.terms {
            let gate = &term.gate;
            rows[term.row] += gate.c0
                + gate.c1 * input[gate.left]
                + gate.c2 * input[gate.right]
                + gate.c3 * input[gate.left] * input[gate.right];
        }
        rows
    }

    #[test]
    fn header_assignment_template_matches_legacy_full_boundary_and_order_assignment() {
        let (_, headers) = fixtures();
        let template = HeaderAssignmentTemplate::new().unwrap();
        let canonical_before = full_header_boundary(None).unwrap();
        let canonical_boundary = canonical_before.base.base.base.boundary.clone();
        let compare_with_legacy = |fields: &serializer::Fields,
                                   previous_height: u32,
                                   previous_time: i64,
                                   first: bool| {
            let mut expected = full_header_boundary(Some(fields)).unwrap();
            header_compact_links::assign_order(
                &mut expected,
                fields,
                previous_height,
                previous_time,
                first,
            )
            .unwrap();
            let mut actual = template.assign(fields).unwrap();
            template
                .assign_order(
                    &mut actual,
                    fields,
                    previous_height,
                    previous_time,
                    first,
                )
                .unwrap();
            assert_eq!(
                actual.as_slice(),
                expected.base.base.base.input.as_ref().unwrap().as_slice(),
                "template must reproduce every canonical wire"
            );
        };

        for height in [1, 2, 1025, 844_801] {
            let header = Header::decode(headers.get(&height).unwrap(), None).unwrap();
            let fields = serializer::Fields::from_header(&header).unwrap();
            let (previous_height, previous_time, first) = if height == 1 {
                (0, fields.timestamp, true)
            } else {
                let previous = Header::decode(headers.get(&(height - 1)).unwrap(), None).unwrap();
                (previous.height, previous.timestamp, false)
            };
            compare_with_legacy(&fields, previous_height, previous_time, first);
        }

        let first_fields = serializer::Fields::from_header(
            &Header::decode(headers.get(&1).unwrap(), None).unwrap(),
        )
        .unwrap();
        let second_fields = serializer::Fields::from_header(
            &Header::decode(headers.get(&2).unwrap(), None).unwrap(),
        )
        .unwrap();
        let first = template.assign(&first_fields).unwrap();
        let mut second = template.assign(&second_fields).unwrap();
        assert_ne!(first.as_ptr(), second.as_ptr(), "assignments own separate vectors");
        second[0] = Fr::one() - second[0];
        assert_eq!(first, template.assign(&first_fields).unwrap());

        for version in [-1, 1, 4, 5] {
            let mut fields = first_fields.clone();
            fields.version = version;
            fields.payload_len = 0;
            fields.payload = [0; 255];
            compare_with_legacy(&fields, 0, 0, true);
        }

        let serialized = &template.canonical.base.base.base.serializer;
        let encoded_length = |fields: &serializer::Fields| {
            let assignment = serialized.assign(fields);
            serialized
                .layout
                .length
                .iter()
                .enumerate()
                .fold(0usize, |length, (bit, &wire)| {
                    if assignment[wire].is_one() {
                        length | (1usize << bit)
                    } else {
                        length
                    }
                })
        };
        for target in [255usize, 256, 257, 383, 384, 385, 511, 512, 513, 514] {
            let mut fields = first_fields.clone();
            fields.version = 1;
            fields.payload_len = 0;
            fields.payload = [0; 255];
            if target >= 511 {
                fields.timestamp = -1;
                fields.height = i32::MAX as u32;
            }
            let base_length = encoded_length(&fields);
            assert!(target >= base_length && target - base_length <= 255);
            fields.payload_len = (target - base_length) as u8;
            fields.payload[..fields.payload_len as usize].fill(0xa5);
            assert_eq!(encoded_length(&fields), target);
            compare_with_legacy(&fields, 0, 0, true);
        }

        assert_eq!(
            template.canonical.base.base.base.boundary,
            canonical_boundary,
            "assignments must not mutate the immutable canonical circuit"
        );
    }

    #[test]
    fn header_assignment_template_rejects_invalid_inputs_without_mutation() {
        let (_, headers) = fixtures();
        let template = HeaderAssignmentTemplate::new().unwrap();
        let header = Header::decode(headers.get(&2).unwrap(), None).unwrap();
        let fields = serializer::Fields::from_header(&header).unwrap();

        let mut bad_point = fields.clone();
        bad_point.pk = [0; 33];
        bad_point.pk[0] = 2;
        assert!(template.assign(&bad_point).is_err(), "invalid point membership must reject");

        let mut short = vec![Fr::from(7u64); SLOT_LEN - 1];
        let short_before = short.clone();
        assert!(template
            .assign_order(&mut short, &fields, 1, 0, false)
            .is_err());
        assert_eq!(short, short_before, "wrong-width order assignment is atomic");

        let mut input = template.assign(&fields).unwrap();
        let before = input.clone();
        assert!(template
            .assign_order(&mut input, &fields, 1, fields.timestamp, false)
            .is_err(), "invalid previous timestamp must reject");
        assert_eq!(input, before, "invalid order witness must leave the input unchanged");
    }

    #[test]
    fn header_assignment_template_guards_canonical_final_pin() {
        let template = HeaderAssignmentTemplate::new().unwrap();
        let original = &template.canonical.base.base.base.boundary;
        validate_final_header_boundary(original).unwrap();

        let mut changed_term = original.clone();
        let prior_term = changed_term.terms[0].clone();
        changed_term.terms[0].gate.c0 += Fr::one();
        assert!(validate_final_header_boundary(&changed_term)
            .unwrap_err()
            .contains("fingerprint"));
        assert_eq!(changed_term.terms[0].row, prior_term.row);
        assert_eq!(changed_term.terms[0].gate.left, prior_term.gate.left);
        assert_eq!(changed_term.terms[0].gate.right, prior_term.gate.right);
        assert_eq!(changed_term.terms[0].gate.c1, prior_term.gate.c1);
        assert_eq!(changed_term.terms[0].gate.c2, prior_term.gate.c2);
        assert_eq!(changed_term.terms[0].gate.c3, prior_term.gate.c3);
        assert_eq!(original.terms[0], prior_term, "the rejected mutant cannot alter the template");

        let mut wrong_width = original.clone();
        wrong_width.input_len -= 1;
        assert!(validate_final_header_boundary(&wrong_width)
            .unwrap_err()
            .contains("input width"));
        assert_eq!(wrong_width.terms, original.terms);

        let mut wrong_rows = original.clone();
        wrong_rows.row_count >>= 1;
        assert!(validate_final_header_boundary(&wrong_rows)
            .unwrap_err()
            .contains("row count"));
        assert_eq!(wrong_rows.terms, original.terms);

        let mut wrong_terms = original.clone();
        wrong_terms.terms.pop();
        assert!(validate_final_header_boundary(&wrong_terms)
            .unwrap_err()
            .contains("term count"));
        assert_eq!(wrong_terms.input_len, original.input_len);
        assert_eq!(wrong_terms.row_count, original.row_count);
    }

    fn assert_physical_boundary(child: u32, fixture: &Fixture, headers: &HashMap<u32, Vec<u8>>) {
        let selected = selected(child, fixture, headers);
        let slot_log = u64::from(child).next_power_of_two().trailing_zeros() as usize;
        let Action::Retarget(epoch) = selected.action() else {
            panic!("fixture must be a retarget")
        };
        let layout = DaaHistoryLayout::compile(epoch, u64::from(child), slot_log).unwrap();
        let actual_daa = daa_finish::compile_finish_with_child(
            epoch,
            &daa_count::q(),
            selected.prediction(),
            selected.child_nbits(),
            true,
        )
        .unwrap();
        assert!(layout.native_template.joined.joined.joined.witness.is_empty());
        let actual_mapped = layout.admit_selected(&selected, &actual_daa).unwrap();
        assert_eq!(actual_mapped.circuit(), layout.mapped_relation());
        assert_eq!(actual_mapped.phase_bank_ranges(), layout.phase_banks);
        for original_wire in 0..ORIGINAL_INPUT_LEN {
            assert_eq!(
                actual_mapped.mapped_wire(original_wire).unwrap(),
                layout.original_to_mapped[original_wire],
                "fixture source map at wire {original_wire}"
            );
        }
        let serializer = serializer::build(None).unwrap();
        let schedule_wiring = DaaScheduleWiring::compile().unwrap();
        validate_actual_ports(
            &serializer,
            &actual_daa,
            &actual_mapped,
            schedule_wiring.ports(epoch),
        )
        .unwrap();
        let child_header = Header::decode(headers.get(&child).unwrap(), None).unwrap();
        let parent = Header::decode(headers.get(&(child - 1)).unwrap(), None).unwrap();
        let fields = serializer::Fields::from_header(&child_header).unwrap();
        let mut boundary = full_header_boundary(Some(&fields)).unwrap();
        assert_eq!(
            boundary.base.base.base.boundary,
            full_header_boundary(None).unwrap().base.base.base.boundary,
            "fixture-boundary full canonical terms"
        );
        header_compact_links::assign_order(
            &mut boundary,
            &fields,
            child - 1,
            parent.timestamp,
            false,
        )
        .unwrap();
        let relation = &boundary.base.base.base.boundary;
        let input = boundary.base.base.base.input.as_mut().unwrap();
        for (start, end) in actual_mapped.phase_bank_ranges() {
            input[start..end].copy_from_slice(&actual_mapped.witness()[start..end]);
        }
        assert!(
            residuals(layout.mapped_relation(), input)
                .iter()
                .all(Zero::is_zero),
            "the physical header assignment satisfies the complete mapped owner"
        );
        let case = fixture
            .cases
            .iter()
            .find(|case| case.child == child)
            .unwrap();
        let native_headers = case
            .samples
            .iter()
            .copied()
            .chain(std::iter::once(child))
            .map(|height| Header::decode(headers.get(&height).unwrap(), None).unwrap())
            .collect::<Vec<_>>();
        let assignments = native_headers
            .iter()
            .map(|header| serializer.assign(&serializer::Fields::from_header(header).unwrap()))
            .collect::<Vec<_>>();
        let logical_ports = schedule_wiring.ports(epoch);
        let child_slot = u64::from(child - 1);
        for (index, (logical, physical)) in logical_ports.iter().zip(&layout.ports).enumerate() {
            let source = &native_headers[logical.source_ordinal()];
            let bit = match logical.family() {
                PortFamily::Timestamp => {
                    (source.timestamp as u64 >> (logical.field_index() % 64)) & 1
                }
                PortFamily::SampleNBits | PortFamily::ChildNBits => {
                    (u64::from(source.n_bits) >> (logical.field_index() % 32)) & 1
                }
                PortFamily::X0Height => (u64::from(source.height) >> logical.field_index()) & 1,
            };
            let source_value = assignments[logical.source_ordinal()]
                [physical.serializer_wire - header_hash::SERIALIZER_OFFSET];
            assert_eq!(
                source_value,
                Fr::from(bit),
                "native physical serializer port {index}"
            );
            assert_eq!(
                input[physical.daa_wire], source_value,
                "physical DAA port {index}"
            );
            assert_eq!(physical.offset, child_slot - u64::from(source.height - 1));
        }
        for family in [
            PortFamily::Timestamp,
            PortFamily::SampleNBits,
            PortFamily::X0Height,
            PortFamily::ChildNBits,
        ] {
            let index = logical_ports
                .iter()
                .enumerate()
                .position(|(index, logical)| {
                    logical.family() == family
                        && assignments[logical.source_ordinal()]
                            [layout.ports[index].serializer_wire - header_hash::SERIALIZER_OFFSET]
                            .is_one()
                })
                .expect("each native field family has a set bit");
            let logical = &logical_ports[index];
            let physical = layout.ports[index];
            let source_value = assignments[logical.source_ordinal()]
                [physical.serializer_wire - header_hash::SERIALIZER_OFFSET];
            let coefficients = layout
                .alias_coefficients(
                    &boolean_point(
                        ALIAS_ROW_LOG + slot_log,
                        (child_slot << ALIAS_ROW_LOG) | index as u64,
                    ),
                    &boolean_point(
                        SLOT_LOG + slot_log,
                        ((child_slot - physical.offset) << SLOT_LOG)
                            | physical.serializer_wire as u64,
                    ),
                    &boolean_point(
                        SLOT_LOG + slot_log,
                        (child_slot << SLOT_LOG) | physical.daa_wire as u64,
                    ),
                )
                .unwrap();
            let evaluate = |coefficients: [Fr; 4], target: Fr| {
                coefficients[0]
                    + coefficients[1] * source_value
                    + coefficients[2] * target
                    + coefficients[3] * source_value * target
            };
            let original = input[physical.daa_wire];
            assert!(evaluate(coefficients, original).is_zero());
            input[physical.daa_wire] = Fr::one() - original;
            assert!(
                !evaluate(coefficients, input[physical.daa_wire]).is_zero(),
                "the isolated physical alias rejects a flipped {family:?} value"
            );
            assert!(
                evaluate([Fr::zero(); 4], input[physical.daa_wire]).is_zero(),
                "omitting that alias would accept its flipped value"
            );
            let mut wrong_orientation = coefficients;
            wrong_orientation[2] = -wrong_orientation[2];
            assert!(
                !evaluate(wrong_orientation, original).is_zero(),
                "a reversed alias orientation rejects the honest set bit"
            );
            input[physical.daa_wire] = original;
        }
        let before = residuals(relation, input);
        let failures = before
            .iter()
            .enumerate()
            .filter_map(|(row, residual)| (!residual.is_zero()).then_some(row))
            .collect::<Vec<_>>();
        assert!(
            !failures.is_empty(),
            "A4 populated zero anchors must be active"
        );
        assert!(
            failures.iter().all(|row| layout.a4_rows.contains(row)),
            "unexpected retained boundary failure"
        );
        assert_eq!(
            failures,
            layout
                .a4_wires
                .clone()
                .filter(|wire| !input[*wire].is_zero())
                .map(|wire| wire - layout.anchor_delta)
                .collect::<Vec<_>>(),
            "exactly the nonzero canonical A4 anchors fail before replacement"
        );

        let mut released = relation.clone();
        for term in released
            .terms
            .iter_mut()
            .filter(|term| layout.releases_anchor(child_slot, term.row))
        {
            term.gate = crate::gkr::Gate {
                left: 0,
                right: 0,
                c0: Fr::zero(),
                c1: Fr::zero(),
                c2: Fr::zero(),
                c3: Fr::zero(),
            };
        }
        for (old, new) in relation.terms.iter().zip(&released.terms) {
            if !layout.a4_rows.contains(&old.row) {
                assert_eq!(old, new, "nonreleased boundary term changed");
            }
        }
        assert!(residuals(&released, input).iter().all(Zero::is_zero));
        let mut r = point(HEADER_BOUNDARY_ROW_LOG, 907);
        let mut u = point(SLOT_LOG, 1009);
        let mut v = point(SLOT_LOG, 1103);
        r.extend(boolean_point(slot_log, child_slot));
        u.extend(boolean_point(slot_log, child_slot));
        v.extend(boolean_point(slot_log, child_slot));
        let mut difference = [Fr::zero(); 4];
        let mut released_count = 0;
        for (old, retained) in relation.terms.iter().zip(&released.terms) {
            if old == retained {
                continue;
            }
            released_count += 1;
            let weight = eq_index(&r[..HEADER_BOUNDARY_ROW_LOG], old.row)
                * eq_index(&u[..SLOT_LOG], old.gate.left)
                * eq_index(&v[..SLOT_LOG], old.gate.right);
            for (index, coefficient) in [old.gate.c0, old.gate.c1, old.gate.c2, old.gate.c3]
                .iter()
                .enumerate()
            {
                difference[index] += weight * coefficient;
            }
            assert!([
                retained.gate.c0,
                retained.gate.c1,
                retained.gate.c2,
                retained.gate.c3
            ]
            .iter()
            .all(Zero::is_zero));
        }
        assert_eq!(released_count, 8192);
        assert_eq!(
            difference,
            [
                Fr::zero(),
                layout.a4_release_coefficient(&r, &u, &v).unwrap(),
                Fr::zero(),
                Fr::zero()
            ],
            "the consumer subtracts exactly the producer's canonical terms"
        );
        {
            let omitted_row = failures[0];
            let index = relation
                .terms
                .iter()
                .position(|term| term.row == omitted_row)
                .unwrap();
            let mut missing_release = released.clone();
            missing_release.terms[index] = relation.terms[index].clone();
            assert_eq!(
                residuals(&missing_release, input)
                    .iter()
                    .enumerate()
                    .filter_map(|(row, value)| (!value.is_zero()).then_some(row))
                    .collect::<Vec<_>>(),
                vec![omitted_row],
                "omitting one required nonzero release fails at its anchor"
            );
        }
        {
            let extra_row = layout.a4_rows.start - 1;
            let index = relation
                .terms
                .iter()
                .position(|term| term.row == extra_row)
                .unwrap();
            let extra = &relation.terms[index].gate;
            assert!(!layout.releases_anchor(child_slot, extra_row));
            assert_eq!(
                [extra.c0, extra.c1, extra.c2, extra.c3],
                [Fr::zero(), Fr::one(), Fr::zero(), Fr::zero()]
            );
            assert_eq!(extra.right, 0);
            let original = input[extra.left];
            assert!(original.is_zero());
            input[extra.left] = Fr::one();
            assert_eq!(
                residuals(&released, input)
                    .iter()
                    .enumerate()
                    .filter_map(|(row, value)| (!value.is_zero()).then_some(row))
                    .collect::<Vec<_>>(),
                vec![extra_row],
                "the canonical selector retains the adjacent nonzero anchor"
            );
            let mut extra_release = released.clone();
            extra_release.terms[index].gate.c1 = Fr::zero();
            assert!(
                residuals(&extra_release, input).iter().all(Zero::is_zero),
                "releasing an extra anchor would admit its isolated nonzero cell"
            );
            input[extra.left] = original;
        }
    }

    #[test]
    fn full_serializer_composition_preserves_compact_aliases_and_rejects_bad_restoration() {
        let compact = header_compact_links::build(None).unwrap();
        let old = &compact.base.base.base;
        let raw = segment_relation::build(None).unwrap();
        let spans = [
            compact.base.base.released_rows.clone(),
            compact.base.released_rows.clone(),
            compact.released_rows.clone(),
        ];
        assert!(
            old.boundary.terms.iter().any(|term| term.row == 176_408
                && term.gate.left == 819_200
                && term.gate.c1.is_one()),
            "the unattached compact builder really retains the conflicting A1 anchor"
        );
        let full = full_header_boundary(None).unwrap();
        let complete = &full.base.base.base;
        let used = 12_836..274_980;
        let mut restored = old.boundary.clone();
        restore_compact_anchors(
            &mut restored,
            old.digest_boolean_rows.end,
            segment_relation::DIGEST_OFFSET + 256,
            &spans,
            &used,
        )
        .unwrap();
        for span in &spans {
            let raw_first = raw
                .boundary
                .terms
                .partition_point(|term| term.row < span.start);
            let restored_first = restored.terms.partition_point(|term| term.row < span.start);
            assert_eq!(
                &restored.terms[restored_first..restored_first + span.len()],
                &raw.boundary.terms[raw_first..raw_first + span.len()],
                "all restored anchors match the independently built original relation"
            );
        }
        let outside_old = old
            .boundary
            .terms
            .iter()
            .filter(|term| !used.contains(&term.row));
        let outside_full = complete
            .boundary
            .terms
            .iter()
            .filter(|term| !used.contains(&term.row));
        assert!(
            outside_old.eq(outside_full),
            "all compact aliases and genesis remain byte-identical"
        );
        let inserted = complete
            .boundary
            .terms
            .iter()
            .filter(|term| used.contains(&term.row))
            .collect::<Vec<_>>();
        assert_eq!(inserted.len(), 315_546);
        for (actual, source) in inserted.iter().zip(&old.serializer.circuit.terms) {
            let mut expected = source.clone();
            expected.row += used.start;
            expected.gate.left += header_hash::SERIALIZER_OFFSET;
            expected.gate.right += header_hash::SERIALIZER_OFFSET;
            assert_eq!(
                **actual, expected,
                "exact full serializer term in the composed boundary"
            );
        }
        eprintln!(
            "complete_header_boundary_terms=474755 fingerprint_blake2b256={}",
            work_tree_layout::hash_terms(&complete.boundary.terms)
        );
        for bad_spans in [
            spans[1..].to_vec(),
            vec![143_641..151_832, spans[1].clone(), spans[2].clone()],
        ] {
            let mut candidate = old.boundary.clone();
            assert!(restore_compact_anchors(
                &mut candidate,
                old.digest_boolean_rows.end,
                segment_relation::DIGEST_OFFSET + 256,
                &bad_spans,
                &used
            )
            .is_err());
            assert_eq!(candidate, old.boundary, "bad span fails before mutation");
        }
        let mut bad_gate = old.boundary.clone();
        let index = bad_gate
            .terms
            .partition_point(|term| term.row < spans[2].start);
        bad_gate.terms[index].gate.c1 = Fr::one();
        let original_bad = bad_gate.clone();
        assert!(restore_compact_anchors(
            &mut bad_gate,
            old.digest_boolean_rows.end,
            segment_relation::DIGEST_OFFSET + 256,
            &spans,
            &used
        )
        .is_err());
        assert_eq!(
            bad_gate, original_bad,
            "a changed last-group gate cannot leave earlier groups restored"
        );
    }

    #[test]
    fn actual_mature_fixture_maps_preserve_banks_ports_and_a4_rows() {
        let (fixture, headers) = fixtures();
        for child in [9_217, 844_673, 844_801] {
            let selected = selected(child, &fixture, &headers);
            let slot_log = (u64::from(child).next_power_of_two().trailing_zeros()) as usize;
            let Action::Retarget(epoch) = selected.action() else {
                panic!("fixture must retarget")
            };
            let layout = DaaHistoryLayout::compile(epoch, u64::from(child), slot_log).unwrap();
            assert_eq!(layout.import_count(), IMPORT_COUNT);
            assert_eq!(layout.mapped_relation().input_len, MAPPED_INPUT_LEN);
            assert_eq!(layout.mapped_relation().row_count, 1 << ARITHMETIC_ROW_LOG);
            assert_eq!(layout.a4_anchor_rows(), A4_RELEASE_ROWS);
            assert!(layout.releases_anchor(u64::from(child - 1), A4_RELEASE_ROWS.start));
            assert!(!layout.releases_anchor(u64::from(child - 1), A4_RELEASE_ROWS.end));
            let expected = match child {
                9_217 => Epoch::Legacy,
                _ => Epoch::Eip,
            };
            assert_eq!(layout.epoch(), expected);
            let logical_ports = DaaScheduleWiring::compile().unwrap();
            let counts = logical_ports
                .ports(epoch)
                .iter()
                .fold([0usize; 4], |mut counts, port| {
                    counts[match port.family() {
                        PortFamily::Timestamp => 0,
                        PortFamily::SampleNBits => 1,
                        PortFamily::X0Height => 2,
                        PortFamily::ChildNBits => 3,
                    }] += 1;
                    counts
                });
            assert_eq!(counts, [576, 256, 32, 32]);

            let term = &layout.mapped_relation().terms[0];
            let (mut c0, mut c1, mut c2, mut c3) = (Fr::zero(), Fr::zero(), Fr::zero(), Fr::zero());
            for candidate in &layout.mapped_relation().terms {
                if candidate.row == term.row
                    && candidate.gate.left == term.gate.left
                    && candidate.gate.right == term.gate.right
                {
                    c0 += candidate.gate.c0;
                    c1 += candidate.gate.c1;
                    c2 += candidate.gate.c2;
                    c3 += candidate.gate.c3;
                }
            }
            let target_slot = u64::from(child - 1);
            let arithmetic = layout
                .arithmetic_coefficients(
                    &boolean_point(
                        ARITHMETIC_ROW_LOG + slot_log,
                        (target_slot << ARITHMETIC_ROW_LOG | term.row as u64),
                    ),
                    &boolean_point(
                        SLOT_LOG + slot_log,
                        (target_slot << SLOT_LOG | term.gate.left as u64),
                    ),
                    &boolean_point(
                        SLOT_LOG + slot_log,
                        (target_slot << SLOT_LOG | term.gate.right as u64),
                    ),
                )
                .unwrap();
            assert_eq!(arithmetic, [c0, c1, c2, c3]);

            let port = layout.ports[0];
            let source_slot = target_slot - port.offset;
            let row = ((target_slot as usize) << ALIAS_ROW_LOG) | 0;
            let left = ((source_slot as usize) << SLOT_LOG) | port.serializer_wire;
            let right = ((target_slot as usize) << SLOT_LOG) | port.daa_wire;
            let actual = layout
                .alias_coefficients(
                    &boolean_point(ALIAS_ROW_LOG + slot_log, row as u64),
                    &boolean_point(SLOT_LOG + slot_log, left as u64),
                    &boolean_point(SLOT_LOG + slot_log, right as u64),
                )
                .unwrap();
            assert_eq!(actual, [Fr::zero(), Fr::one(), -Fr::one(), Fr::zero()]);
            assert_eq!(actual[1], -actual[2], "serializer minus DAA orientation");

            for family in [
                PortFamily::Timestamp,
                PortFamily::SampleNBits,
                PortFamily::X0Height,
                PortFamily::ChildNBits,
            ] {
                let family_range = match family {
                    PortFamily::Timestamp => 0..576,
                    PortFamily::SampleNBits => 576..832,
                    PortFamily::X0Height => 832..864,
                    PortFamily::ChildNBits => 864..896,
                };
                let (port_index, port) = layout
                    .ports
                    .iter()
                    .enumerate()
                    .find(|(index, _)| family_range.contains(index))
                    .unwrap();
                let source = target_slot - port.offset;
                let row = (target_slot as usize) << ALIAS_ROW_LOG | port_index;
                let left = (source as usize) << SLOT_LOG | port.serializer_wire;
                let right = (target_slot as usize) << SLOT_LOG | port.daa_wire;
                let exact = layout
                    .alias_coefficients(
                        &boolean_point(ALIAS_ROW_LOG + slot_log, row as u64),
                        &boolean_point(SLOT_LOG + slot_log, left as u64),
                        &boolean_point(SLOT_LOG + slot_log, right as u64),
                    )
                    .unwrap();
                assert_eq!(exact[1], Fr::one(), "family endpoint {family:?}");
                let wrong = layout
                    .alias_coefficients(
                        &boolean_point(ALIAS_ROW_LOG + slot_log, row as u64),
                        &boolean_point(SLOT_LOG + slot_log, (left ^ 1) as u64),
                        &boolean_point(SLOT_LOG + slot_log, right as u64),
                    )
                    .unwrap();
                assert_eq!(
                    wrong,
                    [Fr::zero(); 4],
                    "isolated source endpoint {family:?}"
                );
                let wrong_daa = layout
                    .alias_coefficients(
                        &boolean_point(ALIAS_ROW_LOG + slot_log, row as u64),
                        &boolean_point(SLOT_LOG + slot_log, left as u64),
                        &boolean_point(SLOT_LOG + slot_log, (right ^ 1) as u64),
                    )
                    .unwrap();
                assert_eq!(
                    wrong_daa,
                    [Fr::zero(); 4],
                    "isolated DAA endpoint {family:?}"
                );
                let shifted = layout
                    .alias_coefficients(
                        &boolean_point(ALIAS_ROW_LOG + slot_log, row as u64),
                        &boolean_point(
                            SLOT_LOG + slot_log,
                            (((source - 1) as usize) << SLOT_LOG | port.serializer_wire) as u64,
                        ),
                        &boolean_point(SLOT_LOG + slot_log, right as u64),
                    )
                    .unwrap();
                assert_eq!(
                    shifted,
                    [Fr::zero(); 4],
                    "isolated wrong source slot {family:?}"
                );
            }

            let required_index = IMPORT_COUNT - 1;
            let required = layout.ports[required_index];
            let required_source = target_slot - required.offset;
            let required_row = (target_slot as usize) << ALIAS_ROW_LOG | required_index;
            let required_left = (required_source as usize) << SLOT_LOG | required.serializer_wire;
            let required_right = (target_slot as usize) << SLOT_LOG | required.daa_wire;
            let required_claim = layout
                .alias_coefficients(
                    &boolean_point(ALIAS_ROW_LOG + slot_log, required_row as u64),
                    &boolean_point(SLOT_LOG + slot_log, required_left as u64),
                    &boolean_point(SLOT_LOG + slot_log, required_right as u64),
                )
                .unwrap();
            let omitted_roster = &layout.ports[..required_index];
            assert_eq!(omitted_roster.len(), IMPORT_COUNT - 1);
            let required_row_point = boolean_point(ALIAS_ROW_LOG, required_index as u64);
            let omitted_local =
                omitted_roster
                    .iter()
                    .enumerate()
                    .fold([Fr::zero(); 4], |mut sum, (index, _)| {
                        let weight = eq_index(&required_row_point, index);
                        sum[1] += weight;
                        sum[2] -= weight;
                        sum
                    });
            assert_eq!(required_claim[1], Fr::one());
            assert_eq!(
                omitted_local,
                [Fr::zero(); 4],
                "omitted mandatory alias is unbound"
            );

            let wire = layout.a4_wires.start;
            let row =
                (target_slot as usize) << HEADER_BOUNDARY_ROW_LOG | (wire - layout.anchor_delta);
            let local_right = (target_slot as usize) << SLOT_LOG;
            assert_eq!(
                layout
                    .a4_release_coefficient(
                        &boolean_point(HEADER_BOUNDARY_ROW_LOG + slot_log, row as u64),
                        &boolean_point(
                            SLOT_LOG + slot_log,
                            ((target_slot as usize) << SLOT_LOG | wire) as u64
                        ),
                        &boolean_point(SLOT_LOG + slot_log, local_right as u64),
                    )
                    .unwrap(),
                Fr::one()
            );
        }
    }

    #[test]
    fn physical_mature_boundary_releases_only_canonical_a4_anchors() {
        let (fixture, headers) = fixtures();
        for child in [9_217, 844_673, 844_801] {
            assert_physical_boundary(child, &fixture, &headers);
        }
    }

    #[test]
    fn non_boolean_coefficients_match_singleton_native_slot_oracles() {
        let cases = [
            (Epoch::Legacy, 9_216u64, 14usize),
            (Epoch::Eip, 844_672, 20),
            (Epoch::Eip, (1 << 21) - 128, 21),
        ];
        for (epoch, slot, slot_log) in cases {
            let mut layout = DaaHistoryLayout::compile(epoch, slot + 1, slot_log).unwrap();
            let r_arith = point(ARITHMETIC_ROW_LOG + slot_log, 13);
            let u_arith = point(SLOT_LOG + slot_log, 107);
            let v_arith = point(SLOT_LOG + slot_log, 211);
            let upper = layout
                .arithmetic_coefficients(&r_arith, &u_arith, &v_arith)
                .unwrap();
            let saved_schedule = std::mem::replace(
                &mut layout.schedule,
                ScheduleDomain::new(slot, slot_log).unwrap(),
            );
            let lower = layout
                .arithmetic_coefficients(&r_arith, &u_arith, &v_arith)
                .unwrap();
            layout.schedule = saved_schedule;
            let actual: [Fr; 4] = std::array::from_fn(|index| upper[index] - lower[index]);
            assert_eq!(
                actual,
                direct_arithmetic(&layout, &r_arith, &u_arith, &v_arith, slot)
            );

            let r_alias = point(ALIAS_ROW_LOG + slot_log, 307);
            let u_alias = point(SLOT_LOG + slot_log, 401);
            let v_alias = point(SLOT_LOG + slot_log, 503);
            let upper = layout
                .alias_coefficients(&r_alias, &u_alias, &v_alias)
                .unwrap();
            let saved_schedule = std::mem::replace(
                &mut layout.schedule,
                ScheduleDomain::new(slot, slot_log).unwrap(),
            );
            let lower = layout
                .alias_coefficients(&r_alias, &u_alias, &v_alias)
                .unwrap();
            layout.schedule = saved_schedule;
            let actual: [Fr; 4] = std::array::from_fn(|index| upper[index] - lower[index]);
            assert_eq!(
                actual,
                direct_aliases(&layout, &r_alias, &u_alias, &v_alias, slot)
            );
            assert_eq!(actual[1], -actual[2], "physical alias orientation");

            let r_release = point(HEADER_BOUNDARY_ROW_LOG + slot_log, 601);
            let u_release = point(SLOT_LOG + slot_log, 701);
            let v_release = point(SLOT_LOG + slot_log, 809);
            let upper = layout
                .a4_release_coefficient(&r_release, &u_release, &v_release)
                .unwrap();
            let saved_schedule = std::mem::replace(
                &mut layout.schedule,
                ScheduleDomain::new(slot, slot_log).unwrap(),
            );
            let lower = layout
                .a4_release_coefficient(&r_release, &u_release, &v_release)
                .unwrap();
            layout.schedule = saved_schedule;
            assert_eq!(
                upper - lower,
                direct_release(&layout, &r_release, &u_release, &v_release, slot)
            );
        }
    }

    #[test]
    fn exact_arithmetic_point_and_native_branch_gates_reject_wrong_shapes() {
        let layout = DaaHistoryLayout::compile(Epoch::Legacy, 9_217, 14).unwrap();
        assert!(layout
            .arithmetic_coefficients(
                &vec![Fr::zero(); 17 + 14],
                &vec![Fr::zero(); 20 + 14],
                &vec![Fr::zero(); 20 + 14]
            )
            .is_ok());
        assert!(layout
            .arithmetic_coefficients(
                &vec![Fr::zero(); 16 + 14],
                &vec![Fr::zero(); 20 + 14],
                &vec![Fr::zero(); 20 + 14]
            )
            .is_err());
        assert!(
            layout
                .arithmetic_coefficients(
                    &vec![Fr::zero(); 19 + 14],
                    &vec![Fr::zero(); 20 + 14],
                    &vec![Fr::zero(); 20 + 14]
                )
                .is_err(),
            "a header row point cannot be silently sliced into the arithmetic row domain"
        );
        assert!(layout
            .alias_coefficients(
                &vec![Fr::zero(); 9 + 14],
                &vec![Fr::zero(); 20 + 14],
                &vec![Fr::zero(); 20 + 14]
            )
            .is_err());
        assert!(layout
            .a4_release_coefficient(
                &vec![Fr::zero(); 18 + 14],
                &vec![Fr::zero(); 20 + 14],
                &vec![Fr::zero(); 20 + 14]
            )
            .is_err());
        assert!(DaaHistoryLayout::compile(Epoch::Legacy, 9_217, 13).is_err());
        assert!(DaaHistoryLayout::compile(Epoch::Legacy, 9_217, 22).is_err());
        assert!(DaaHistoryLayout::compile(Epoch::Legacy, 16_385, 14).is_err());
        assert!(!layout.releases_anchor(0, A4_RELEASE_ROWS.start));
        assert!(!layout.releases_anchor(8 * 1024, A4_RELEASE_ROWS.start));
        assert!(!layout.releases_anchor(9 * 1024 - 1, A4_RELEASE_ROWS.start));
        assert!(!layout.releases_anchor(9_217, A4_RELEASE_ROWS.start));
        assert!(!layout.releases_anchor(
            daa_header_window::EIP37_FIRST_CHILD as u64 - 1,
            A4_RELEASE_ROWS.start
        ));
        assert!(!layout.releases_anchor(
            daa_header_window::V2_RESET_CHILDREN[0] as u64 - 1,
            A4_RELEASE_ROWS.start
        ));
        let mut high = DaaHistoryLayout::compile(Epoch::Eip, 1 << 21, 21).unwrap();
        assert_eq!(high.import_count(), IMPORT_COUNT);
        assert_eq!(high.schedule.upper_bound(), 1 << 21);
        let high_legacy = DaaHistoryLayout::compile(Epoch::Legacy, 1 << 21, 21).unwrap();
        let assert_release = |owner: &DaaHistoryLayout, slot: u64, expected: bool| {
            assert_eq!(
                owner.releases_anchor(slot, owner.a4_rows.start),
                expected,
                "native producer selector epoch {:?} slot {slot}",
                owner.epoch
            );
            let coefficient = owner
                .a4_release_coefficient(
                    &boolean_point(
                        HEADER_BOUNDARY_ROW_LOG + 21,
                        (slot << HEADER_BOUNDARY_ROW_LOG) | owner.a4_rows.start as u64,
                    ),
                    &boolean_point(
                        SLOT_LOG + 21,
                        (slot << SLOT_LOG) | owner.a4_wires.start as u64,
                    ),
                    &boolean_point(SLOT_LOG + 21, slot << SLOT_LOG),
                )
                .unwrap();
            assert_eq!(
                coefficient,
                Fr::from(u64::from(expected)),
                "native consumer coefficient epoch {:?} slot {slot}",
                owner.epoch
            );
        };
        for (slot, expected) in [
            (0, false),
            (8192, false),
            (9216, true),
            (9217, false),
            (416768, true),
            (417791, false),
            (417792, false),
            (418816, true),
            (843776, true),
            (844672, false),
            (845824, false),
        ] {
            assert_release(&high_legacy, slot, expected);
        }
        for (slot, expected) in [
            (9216, false),
            (844544, false),
            (844672, true),
            (844673, false),
            (844800, true),
            ((1 << 21) - 128, true),
        ] {
            assert_release(&high, slot, expected);
        }
        let padded_slot = (1 << 21) - 128;
        let old_schedule = std::mem::replace(
            &mut high.schedule,
            ScheduleDomain::new(padded_slot, 21).unwrap(),
        );
        assert_release(&high, padded_slot, false);
        high.schedule = old_schedule;
        for (row, wire) in [
            (high.a4_rows.start - 1, high.a4_wires.start - 1),
            (high.a4_rows.end, high.a4_wires.end),
        ] {
            assert!(!high.releases_anchor(844672, row));
            assert!(
                high.a4_release_coefficient(
                    &boolean_point(
                        HEADER_BOUNDARY_ROW_LOG + 21,
                        (844672 << HEADER_BOUNDARY_ROW_LOG) | row as u64
                    ),
                    &boolean_point(SLOT_LOG + 21, (844672 << SLOT_LOG) | wire as u64),
                    &boolean_point(SLOT_LOG + 21, 844672 << SLOT_LOG),
                )
                .unwrap()
                .is_zero(),
                "adjacent canonical anchors remain outside release"
            );
        }
        assert!(!high.releases_anchor(
            daa_header_window::EIP37_FIRST_CHILD as u64 - 2,
            A4_RELEASE_ROWS.start
        ));
        assert!(!high.releases_anchor(
            daa_header_window::V2_RESET_CHILDREN[0] as u64 - 1,
            A4_RELEASE_ROWS.start
        ));
        assert!(
            !high.releases_anchor(9 * 1024, A4_RELEASE_ROWS.start),
            "wrong epoch"
        );
        assert!(!high.releases_anchor(0, A4_RELEASE_ROWS.start - 1));
        let one_slot = DaaHistoryLayout::compile(Epoch::Eip, 1, 0).unwrap();
        assert_eq!(
            one_slot
                .alias_coefficients(
                    &vec![Fr::from(2u64); ALIAS_ROW_LOG],
                    &vec![Fr::from(3u64); SLOT_LOG],
                    &vec![Fr::from(5u64); SLOT_LOG]
                )
                .unwrap(),
            [Fr::zero(); 4],
            "empty mature intervals do not invoke shifted-index underflow"
        );
    }

    #[test]
    #[ignore = "C337 source-only census; run only inside a bounded diagnostic Job"]
    fn c337_a_support_census() {
        let joined = full_header_boundary(None).unwrap();
        let boundary = &joined.base.base.base.boundary;
        validate_final_header_boundary(boundary).unwrap();
        assert_eq!(boundary.terms.len(), 474_755);

        // Before owner-specific retirement, the canonical local template is a
        // safe support superset: owner traversal only translates or removes
        // terms. A is sourced by c1 and c3; c0/c2 contribute to B instead.
        let mut a_pairs: Vec<HashSet<usize>> = (0..10).map(|_| HashSet::new()).collect();
        let mut a_terms = 0usize;
        for term in &boundary.terms {
            assert!(term.gate.left < SLOT_LEN, "canonical left outside local input");
            if term.gate.c1.is_zero() && term.gate.c3.is_zero() {
                continue;
            }
            a_terms += 1;
            for (k, pairs) in a_pairs.iter_mut().enumerate() {
                pairs.insert(term.gate.left >> (k + 1));
            }
        }
        assert!(a_terms > 0 && a_terms <= boundary.terms.len());
        let rows: Vec<_> = a_pairs
            .iter()
            .enumerate()
            .map(|(k, pairs)| {
                let dense_pairs = SLOT_LEN >> (k + 1);
                assert!(!pairs.is_empty() && pairs.len() <= dense_pairs);
                serde_json::json!({
                    "k": k,
                    "a_active_pair_support": pairs.len(),
                    "dense_pairs": dense_pairs,
                })
            })
            .collect();
        println!(
            "C337_A_SUPPORT_CENSUS_PASS {}",
            serde_json::json!({
                "scope": "canonical_full_template_owner_superset",
                "template_terms": boundary.terms.len(),
                "template_blake2b256": work_tree_layout::hash_terms(&boundary.terms),
                "a_active_terms": a_terms,
                "rounds": rows,
                "owner_specific_exact_support": false,
                "producer_timing": false,
            })
        );
    }
}

// BEGIN ROLE2 TEMPLATE CAPACITY CFGTEST
#[cfg(test)]
pub(crate) use self::role2_template_capacity::{
    HeaderAssignmentCapacityInventory, HeaderAssignmentCapacityPlan,
};

#[cfg(test)]
mod role2_template_capacity {
    use super::HeaderAssignmentTemplate;
    use crate::{sparse::Term, work_tree_fixed_hash::Engine, work_tree_layout::Baseline};
    use ark_bn254::Fr;
    use std::mem::{size_of, size_of_val};

    const MIB: usize = 1 << 20;
    const LENGTHS: [usize; 5] = [689_920, 474_755, 315_546, 288_158, 2_081];
    const CAPS: [usize; 5] = [689_920, 524_288, 524_288, 288_158, 2_081];
    // serializer::Compiled keeps recipes/sums private. This is a source-derived
    // payload ceiling, never a claim that their capacities were observed here.
    const SERIALIZER_PRIVATE_BYTES: usize = 131_072 * 32 + 4 * 24 + 4 * 32 * 16;

    fn add(a: usize, b: usize) -> Result<usize, String> {
        a.checked_add(b).ok_or_else(|| "role2 inventory byte addition overflow".into())
    }
    fn mul(a: usize, b: usize) -> Result<usize, String> {
        a.checked_mul(b).ok_or_else(|| "role2 inventory byte multiplication overflow".into())
    }
    fn heap<T>(values: &Vec<T>) -> Result<usize, String> {
        mul(values.capacity(), size_of::<T>())
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub(crate) struct HeaderAssignmentCapacityPlan {
        pub construct_bound_bytes: usize,
        pub retained_bound_bytes: usize,
        pub template_bound_bytes: usize,
        pub shared_bound_bytes: usize,
        pub job_limit_bytes: usize,
        pub metadata_bound_bytes: usize,
        pub preparation_bound_bytes: usize,
    }
    impl HeaderAssignmentCapacityPlan {
        pub(crate) fn require_preparation_for_test(&self, metadata_bytes: usize) -> Result<(), String> {
            if *self != plan() {
                return Err("role2 inventory static plan changed".into());
            }
            if size_of::<Fr>() != 32 || size_of::<Term>() != 152 || size_of::<usize>() != 8 {
                return Err("role2 inventory typed ABI changed".into());
            }
            if metadata_bytes > self.metadata_bound_bytes {
                return Err("role2 inventory metadata capacity exceeds bound".into());
            }
            if add(self.construct_bound_bytes, metadata_bytes)? > self.job_limit_bytes
                || add(self.retained_bound_bytes, self.preparation_bound_bytes)? > self.job_limit_bytes
                || self.preparation_bound_bytes > 512 * MIB
            {
                return Err("role2 inventory preparation exceeds resource bound".into());
            }
            Ok(())
        }
    }
    fn plan() -> HeaderAssignmentCapacityPlan {
        HeaderAssignmentCapacityPlan {
            construct_bound_bytes: 512 * MIB,
            retained_bound_bytes: 384 * MIB,
            template_bound_bytes: 320 * MIB,
            shared_bound_bytes: 64 * MIB,
            job_limit_bytes: 2_147_483_648,
            metadata_bound_bytes: 17 * MIB,
            preparation_bound_bytes: 406_941_696,
        }
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub(crate) struct HeaderAssignmentCapacityInventory {
        // Fixed order: core4, final boundary, serializer, points, order.
        pub circuit_lengths: [usize; 5],
        pub circuit_capacities: [usize; 5],
        pub template_public_capacity_bytes: usize,
        pub template_private_source_bound_bytes: usize,
        pub shared_core_length: usize,
        pub shared_core_capacity: usize,
        pub shared_baseline_public_capacity_bytes: usize,
        pub shared_public_capacity_bytes: usize,
        pub shared_source_bound_bytes: usize,
        pub template_total_bound_bytes: usize,
        pub shared_total_bound_bytes: usize,
        pub retained_total_bound_bytes: usize,
    }
    impl HeaderAssignmentCapacityInventory {
        // The real census and isolated capacity mutants use this same validator.
        pub(crate) fn require_bounds_for_test(&self) -> Result<(), String> {
            plan().require_preparation_for_test(0)?;
            if self.circuit_lengths != LENGTHS {
                return Err("role2 inventory circuit length changed".into());
            }
            for i in 0..5 {
                if self.circuit_capacities[i] < self.circuit_lengths[i]
                    || self.circuit_capacities[i] > CAPS[i]
                {
                    return Err("role2 inventory circuit capacity exceeds bound".into());
                }
            }
            let mut term_bytes = 0usize;
            for capacity in self.circuit_capacities {
                term_bytes = add(term_bytes, mul(capacity, size_of::<Term>())?)?;
            }
            if self.template_public_capacity_bytes < term_bytes
                || self.template_private_source_bound_bytes != SERIALIZER_PRIVATE_BYTES
                || self.shared_source_bound_bytes != 0
            {
                return Err("role2 inventory payload accounting changed".into());
            }
            if self.shared_core_length != 172_480
                || self.shared_core_capacity < self.shared_core_length
                || self.shared_core_capacity > 262_144
            {
                return Err("role2 inventory shared core capacity exceeds bound".into());
            }
            if self.shared_baseline_public_capacity_bytes > 16 * MIB
                || self.shared_public_capacity_bytes
                    < add(self.shared_baseline_public_capacity_bytes,
                        mul(self.shared_core_capacity, size_of::<Term>())?)?
            {
                return Err("role2 inventory shared baseline accounting changed".into());
            }
            if self.template_total_bound_bytes != add(self.template_public_capacity_bytes,
                    self.template_private_source_bound_bytes)?
                || self.shared_total_bound_bytes != add(self.shared_public_capacity_bytes,
                    self.shared_source_bound_bytes)?
                || self.retained_total_bound_bytes != add(self.template_total_bound_bytes,
                    self.shared_total_bound_bytes)?
            {
                return Err("role2 inventory total accounting changed".into());
            }
            let limits = plan();
            if self.template_total_bound_bytes > limits.template_bound_bytes
                || self.shared_total_bound_bytes > limits.shared_bound_bytes
                || self.retained_total_bound_bytes > limits.retained_bound_bytes
            {
                return Err("role2 inventory retained capacity exceeds bound".into());
            }
            Ok(())
        }
    }

    // Inline headers are included by sizeof(Baseline); each public heap payload
    // is then counted once. No construction, serialization or Vec allocation.
    fn baseline_public_bytes(base: &Baseline) -> Result<usize, String> {
        let mut bytes = size_of_val(base);
        let ep = &base.endpoints;
        for wires in [
            &ep.raw, &ep.length, &ep.n_bits, &ep.height, &ep.lower, &ep.upper,
            &ep.work, &ep.exponent, &ep.work_minus_one, &ep.leaf, &ep.node_left,
            &ep.node_right, &ep.node, &ep.profile, &ep.count, &ep.position, &ep.level,
            &base.header_alias_wires,
        ] {
            bytes = add(bytes, heap(wires)?)?;
        }
        let inventory = &base.inventory;
        for value in [
            &inventory.schema, &inventory.baseline_id, &inventory.contract_sha256,
            &inventory.core.terms_blake2b256, &inventory.old_boundary_blake2b256,
            &inventory.descriptor_blake2b256,
        ] {
            bytes = add(bytes, value.capacity())?;
        }
        bytes = add(bytes, heap(&inventory.source_sha256_pins_for_archive)?)?;
        for (path, digest) in &inventory.source_sha256_pins_for_archive {
            bytes = add(add(bytes, path.capacity())?, digest.capacity())?;
        }
        for banks in [&inventory.banks, &inventory.endpoint_fields] {
            bytes = add(bytes, heap(banks)?)?;
            for bank in banks {
                bytes = add(add(bytes, bank.role.capacity())?, bank.opening.capacity())?;
            }
        }
        bytes = add(bytes, heap(&inventory.free_ranges)?)?;
        bytes = add(bytes, heap(&inventory.retired)?)?;
        for retired in &inventory.retired {
            bytes = add(add(bytes, retired.role.capacity())?,
                retired.replacement_obligation.capacity())?;
        }
        bytes = add(bytes, heap(&inventory.pending)?)?;
        for pending in &inventory.pending {
            bytes = add(bytes, pending.capacity())?;
        }
        Ok(bytes)
    }

    impl HeaderAssignmentTemplate {
        // Invoke before shared_baseline/engine/new; this does not call them.
        pub(crate) fn role2_capacity_preflight_for_test(
            metadata_bytes: usize,
        ) -> Result<HeaderAssignmentCapacityPlan, String> {
            let value = plan();
            value.require_preparation_for_test(metadata_bytes)?;
            Ok(value)
        }

        // The caller supplies an already initialized engine, so the census
        // cannot accidentally construct a second parental graph.
        pub(crate) fn role2_capacity_inventory_for_test(
            &self, engine: &Engine,
        ) -> Result<HeaderAssignmentCapacityInventory, String> {
            let limits = Self::role2_capacity_preflight_for_test(0)?;
            if !std::ptr::eq(self.compression, &engine.base.compression) {
                return Err("role2 inventory detached shared baseline".into());
            }
            let order = self.canonical.base.as_ref();
            let points = order.base.as_ref();
            let segment = points.base.as_ref();
            if segment.input.is_some() || segment.serializer.input.is_some() {
                return Err("role2 inventory template retains assignment".into());
            }
            let circuits = [
                &segment.core4, &segment.boundary, &segment.serializer.circuit,
                &points.points.circuit, &order.order.circuit,
            ];
            let mut lengths = [0usize; 5];
            let mut capacities = [0usize; 5];
            let mut public_bytes = size_of_val(self);
            // self includes compact inline fields; dereferenced Box payloads
            // include their own inline Vec/Box headers, but not heap children.
            for inline in [
                size_of_val(order), size_of_val(points), size_of_val(segment),
                size_of_val(points.points.as_ref()), size_of_val(order.order.as_ref()),
            ] {
                public_bytes = add(public_bytes, inline)?;
            }
            for (i, circuit) in circuits.iter().enumerate() {
                lengths[i] = circuit.terms.len();
                capacities[i] = circuit.terms.capacity();
                public_bytes = add(public_bytes, heap(&circuit.terms)?)?;
            }
            for point in &points.points.layout.points {
                for bits in [&point.x, &point.y, &point.u, &point.v] {
                    public_bytes = add(public_bytes, size_of_val(bits.as_ref()))?;
                }
                for bits in point.quotients.iter().chain(point.comparisons.iter()) {
                    public_bytes = add(public_bytes, size_of_val(bits.as_ref()))?;
                }
                for identity in &point.carries {
                    for bits in identity {
                        public_bytes = add(public_bytes, size_of_val(bits.as_ref()))?;
                    }
                }
            }
            let baseline_bytes = baseline_public_bytes(engine.base)?;
            let shared_bytes = add(add(size_of_val(engine),
                heap(&engine.core.terms)?)?, baseline_bytes)?;
            let template_total = add(public_bytes, SERIALIZER_PRIVATE_BYTES)?;
            let shared_total = shared_bytes;
            let value = HeaderAssignmentCapacityInventory {
                circuit_lengths: lengths, circuit_capacities: capacities,
                template_public_capacity_bytes: public_bytes,
                template_private_source_bound_bytes: SERIALIZER_PRIVATE_BYTES,
                shared_core_length: engine.core.terms.len(),
                shared_core_capacity: engine.core.terms.capacity(),
                shared_baseline_public_capacity_bytes: baseline_bytes,
                shared_public_capacity_bytes: shared_bytes,
                shared_source_bound_bytes: 0,
                template_total_bound_bytes: template_total,
                shared_total_bound_bytes: shared_total,
                retained_total_bound_bytes: add(template_total, shared_total)?,
            };
            value.require_bounds_for_test()?;
            // Keep the same checked preparation join used before construction.
            limits.require_preparation_for_test(0)?;
            Ok(value)
        }
    }
}
// END ROLE2 TEMPLATE CAPACITY CFGTEST


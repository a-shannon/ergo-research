//! Analytic, bounded logical-slot wiring for native Mainnet DAA retargets.
//!
//! This module exposes exact serializer-to-A1/A4 field ports and evaluates
//! their shifted slot coefficients without choosing a physical history bank,
//! materializing a historical circuit, or asserting history authentication.
use ark_bn254::Fr;
use ark_ff::{One, Zero};

use crate::{
    daa_count, daa_finish,
    daa_header_window::{self, Action},
    daa_integer::{Epoch, WindowInputs},
    daa_regression::PredictionInput,
    serializer::{self, Compiled as CompiledSerializer},
    wiring::{self, RightIndex},
};

const HEADER_SLOT_LOG: usize = 20;
const SERIALIZER_LOG: usize = 17;
const SERIALIZER_LEN: usize = 1 << SERIALIZER_LOG;
const DAA_LOG: usize = 16;
const DAA_LEN: usize = 1 << DAA_LOG;
const PORT_COUNT: usize = 896;
const PORT_LOG: usize = 10;
const LEGACY_EPOCH: u64 = daa_header_window::MAINNET_LEGACY_EPOCH_LENGTH;
const EIP_EPOCH: u64 = daa_header_window::MAINNET_EIP37_EPOCH_LENGTH;
const LEGACY_MATURE_FROM: u64 = 9 * LEGACY_EPOCH;
const LEGACY_RESET_SLOT: u64 = daa_header_window::V2_RESET_CHILDREN[1] as u64 - 1;
const EIP_FIRST_SLOT: u64 = daa_header_window::EIP37_FIRST_CHILD as u64 - 1;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PortFamily {
    Timestamp,
    SampleNBits,
    X0Height,
    ChildNBits,
}

/// A code-owned Boolean wire equality. Fields stay private; callers can inspect
/// a map for diagnostics but cannot inject or reorder ports into evaluation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct FieldPort {
    family: PortFamily,
    field_index: usize,
    source_ordinal: usize,
    source_back: Option<usize>,
    serializer_wire: usize,
    daa_wire: usize,
}

impl FieldPort {
    pub(crate) fn family(&self) -> PortFamily {
        self.family
    }
    pub(crate) fn field_index(&self) -> usize {
        self.field_index
    }
    pub(crate) fn source_ordinal(&self) -> usize {
        self.source_ordinal
    }
    pub(crate) fn serializer_wire(&self) -> usize {
        self.serializer_wire
    }
    pub(crate) fn daa_wire(&self) -> usize {
        self.daa_wire
    }

    /// Distance between the child-slot DAA input and its zero-based source
    /// serializer slot. Slot s contains the header at height s+1.
    pub(crate) fn offset(&self, epoch: Epoch) -> u64 {
        self.source_back
            .map_or(0, |back| 1 + back as u64 * epoch.length())
    }
}

struct EpochPorts {
    ports: Vec<FieldPort>,
}

/// Fixed port roster derived from the compiled serializer and both full DAA
/// templates. No callback, caller map, or bank assignment enters the object.
pub(crate) struct DaaScheduleWiring {
    legacy: EpochPorts,
    eip: EpochPorts,
}

impl DaaScheduleWiring {
    pub(crate) fn compile() -> Result<Self, String> {
        let serializer = serializer::build(None)?;
        if serializer.circuit.input_len != SERIALIZER_LEN
            || serializer.layout.fields.timestamp.len() != 64
            || serializer.layout.fields.n_bits.len() != 32
            || serializer.layout.fields.height.len() != 32
        {
            return Err("serializer port template geometry changed".into());
        }
        let legacy_daa = compile_epoch_template(Epoch::Legacy, false)?;
        let eip_daa = compile_epoch_template(Epoch::Eip, false)?;
        Ok(Self {
            legacy: compile_epoch_ports(&serializer, Epoch::Legacy, &legacy_daa)?,
            eip: compile_epoch_ports(&serializer, Epoch::Eip, &eip_daa)?,
        })
    }

    pub(crate) fn ports(&self, epoch: Epoch) -> &[FieldPort] {
        match epoch {
            Epoch::Legacy => &self.legacy.ports,
            Epoch::Eip => &self.eip.ports,
        }
    }

    pub(crate) fn evaluate(
        &self,
        epoch: Epoch,
        schedule: &ScheduleDomain,
        row: &[Fr],
        serializer_source: &[Fr],
        daa_target: &[Fr],
    ) -> Result<[Fr; 4], String> {
        let row_bits = PORT_LOG
            .checked_add(schedule.slot_log)
            .ok_or("DAA schedule row dimension overflow")?;
        let input_bits = HEADER_SLOT_LOG
            .checked_add(schedule.slot_log)
            .ok_or("DAA schedule input dimension overflow")?;
        if row.len() != row_bits
            || serializer_source.len() != input_bits
            || daa_target.len() != input_bits
        {
            return Err("DAA schedule point dimensions rejected".into());
        }

        if let (Some(row_index), Some(source_index), Some(target_index)) = (
            boolean_index(row),
            boolean_index(serializer_source),
            boolean_index(daa_target),
        ) {
            let port_index = (row_index & ((1u64 << PORT_LOG) - 1)) as usize;
            let row_slot = row_index >> PORT_LOG;
            let source_wire = (source_index & ((1u64 << HEADER_SLOT_LOG) - 1)) as usize;
            let source_slot = source_index >> HEADER_SLOT_LOG;
            let target_wire = (target_index & ((1u64 << HEADER_SLOT_LOG) - 1)) as usize;
            let target_slot = target_index >> HEADER_SLOT_LOG;
            if row_slot == target_slot
                && schedule.contains_mature_retarget(target_slot) == Some(epoch)
                && self.ports(epoch).get(port_index).is_some_and(|port| {
                    port.serializer_wire == source_wire
                        && port.daa_wire == target_wire
                        && source_slot.checked_add(port.offset(epoch)) == Some(target_slot)
                })
            {
                return Ok([Fr::zero(), Fr::one(), -Fr::one(), Fr::zero()]);
            }
            return Ok([Fr::zero(); 4]);
        }

        let mut result = [Fr::zero(); 4];
        let row_ports = &row[..PORT_LOG];
        let row_slots = &row[PORT_LOG..];
        let source_local = &serializer_source[..HEADER_SLOT_LOG];
        let source_slots = &serializer_source[HEADER_SLOT_LOG..];
        let target_local = &daa_target[..HEADER_SLOT_LOG];
        let target_slots = &daa_target[HEADER_SLOT_LOG..];
        let mut shifted_weights = [None; 10];
        for (port_index, port) in self.ports(epoch).iter().enumerate() {
            let local_weight = eq_index(row_ports, port_index)
                * eq_index(source_local, port.serializer_wire)
                * eq_index(target_local, port.daa_wire);
            if local_weight.is_zero() {
                continue;
            }
            let offset = port.offset(epoch);
            let cache_index = offset_cache_index(epoch, offset)?;
            let slot_weight = if let Some(weight) = shifted_weights[cache_index] {
                weight
            } else {
                let weight = evaluate_mature_shift(
                    epoch,
                    schedule,
                    row_slots,
                    source_slots,
                    target_slots,
                    offset,
                    RightIndex::SameRow,
                )?;
                shifted_weights[cache_index] = Some(weight);
                weight
            };
            let weight = local_weight * slot_weight;
            // Gate orientation is serializer − DAA; zero residuals are
            // identical to the mature packet's DAA − serializer rows.
            result[1] += weight;
            result[2] -= weight;
        }
        Ok(result)
    }
}

fn boolean_index(point: &[Fr]) -> Option<u64> {
    let mut index = 0u64;
    for (bit, coordinate) in point.iter().enumerate() {
        if coordinate.is_one() {
            index |= 1u64 << bit;
        } else if !coordinate.is_zero() {
            return None;
        }
    }
    Some(index)
}

fn offset_cache_index(epoch: Epoch, offset: u64) -> Result<usize, String> {
    if offset == 0 {
        return Ok(9);
    }
    let epoch_length = epoch.length();
    if offset < 1 || (offset - 1) % epoch_length != 0 {
        return Err("DAA schedule port has an unexpected source offset".into());
    }
    let back = ((offset - 1) / epoch_length) as usize;
    if back > 8 {
        return Err("DAA schedule port offset exceeds the fixed sample window".into());
    }
    Ok(back)
}

/// Compile the same fixed, code-owned DAA seed consumed by the schedule map.
/// A physical owner may retain its circuit but must discard this diagnostic
/// witness after deriving its immutable coordinates.
pub(crate) fn compile_epoch_template(
    epoch: Epoch,
    materialize: bool,
) -> Result<daa_finish::CompiledFinish, String> {
    let input = PredictionInput {
        window: WindowInputs {
            nbits: [0x0300_0001; 8],
            timestamps: std::array::from_fn(|index| index as i64 * 1000),
        },
        x0: 1024,
    };
    let daa = daa_finish::compile_finish_with_child(
        epoch,
        &daa_count::q(),
        input,
        0x0300_0001,
        materialize,
    )?;
    validate_template(&daa)?;
    Ok(daa)
}

fn compile_epoch_ports(
    serializer: &CompiledSerializer,
    epoch: Epoch,
    daa: &daa_finish::CompiledFinish,
) -> Result<EpochPorts, String> {
    validate_template(daa)?;
    let window = &daa.joined.joined.joined;

    let mut ports = Vec::with_capacity(PORT_COUNT);
    // DAA external timestamps 0..8 map to the nine source samples in order.
    for external in 0..9 {
        let daa_bits = if external == 8 {
            &window.external[7].end_timestamp
        } else {
            &window.external[external].start_timestamp
        };
        for bit in 0..64 {
            ports.push(FieldPort {
                family: PortFamily::Timestamp,
                field_index: external * 64 + bit,
                source_ordinal: external,
                source_back: Some(8 - external),
                serializer_wire: serializer.layout.fields.timestamp[bit],
                daa_wire: daa_bits[bit],
            });
        }
    }
    // External nBits 0..7 map to sample headers 1..8.
    for external in 0..8 {
        for bit in 0..32 {
            ports.push(FieldPort {
                family: PortFamily::SampleNBits,
                field_index: external * 32 + bit,
                source_ordinal: external + 1,
                source_back: Some(7 - external),
                serializer_wire: serializer.layout.fields.n_bits[bit],
                daa_wire: window.external[external].nbits[bit],
            });
        }
    }
    for bit in 0..32 {
        ports.push(FieldPort {
            family: PortFamily::X0Height,
            field_index: bit,
            source_ordinal: 1,
            source_back: Some(7),
            serializer_wire: serializer.layout.fields.height[bit],
            daa_wire: daa.joined.output.x0_bits[bit],
        });
    }
    let child_nbits = daa.child_nbits.as_ref().ok_or("child nBits map missing")?;
    for bit in 0..32 {
        ports.push(FieldPort {
            family: PortFamily::ChildNBits,
            field_index: bit,
            source_ordinal: 9,
            source_back: None,
            serializer_wire: serializer.layout.fields.n_bits[bit],
            daa_wire: child_nbits[bit],
        });
    }
    if ports.len() != PORT_COUNT
        || ports
            .iter()
            .any(|port| port.serializer_wire >= SERIALIZER_LEN || port.daa_wire >= DAA_LEN)
    {
        return Err("DAA serializer port roster or local wire bounds changed".into());
    }
    Ok(EpochPorts { ports })
}

fn validate_template(daa: &daa_finish::CompiledFinish) -> Result<(), String> {
    let window = &daa.joined.joined.joined;
    if window.external.len() != 8
        || window.count.padded_input_bits != DAA_LEN
        || daa.joined.output.x0_bits.len() != 32
        || daa
            .child_nbits
            .as_ref()
            .map_or(true, |bits| bits.len() != 32)
    {
        return Err("full DAA port template geometry changed".into());
    }
    if (0..7).any(|index| {
        window.external[index].end_timestamp != window.external[index + 1].start_timestamp
    }) {
        return Err("DAA adjacent timestamp imports are not shared".into());
    }
    Ok(())
}

/// Logical slot domain for the child-slot schedule. Slot s stores header
/// height s+1; the upper bound is clipped to both this domain and Mainnet's
/// supported child-height range. This does not assign a physical bank.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ScheduleDomain {
    history_slots: u64,
    slot_log: usize,
}

impl ScheduleDomain {
    pub(crate) fn new(history_slots: u64, slot_log: usize) -> Result<Self, String> {
        if history_slots == 0
            || history_slots > daa_header_window::MAX_CHILD_HEIGHT as u64
            || slot_log > 43
        {
            return Err("invalid DAA schedule history or slot dimension".into());
        }
        let domain = 1u64
            .checked_shl(slot_log as u32)
            .ok_or("DAA slot domain overflow")?;
        if history_slots > domain {
            return Err("DAA history exceeds the declared power-of-two domain".into());
        }
        Ok(Self {
            history_slots,
            slot_log,
        })
    }

    pub(crate) fn slot_log(&self) -> usize {
        self.slot_log
    }
    pub(crate) fn upper_bound(&self) -> u64 {
        self.history_slots
            .min(daa_header_window::MAX_CHILD_HEIGHT as u64)
            .min(1u64 << self.slot_log)
    }

    pub(crate) fn ranges(&self, epoch: Epoch) -> Vec<(u64, u64)> {
        let upper = self.upper_bound();
        let clip = |lo: u64, hi: u64| {
            let lo = lo.min(upper);
            (lo, hi.min(upper).max(lo))
        };
        match epoch {
            Epoch::Legacy => vec![
                clip(LEGACY_MATURE_FROM, LEGACY_RESET_SLOT),
                clip(LEGACY_RESET_SLOT + 1, EIP_FIRST_SLOT),
            ],
            Epoch::Eip => vec![clip(EIP_FIRST_SLOT, upper)],
        }
    }

    pub(crate) fn contains_mature_retarget(&self, target_slot: u64) -> Option<Epoch> {
        if target_slot >= self.upper_bound() {
            return None;
        }
        let child = u32::try_from(target_slot.checked_add(1)?).ok()?;
        let plan = daa_header_window::for_child_height(child).ok()?;
        if plan.sample_heights().len() != 9 {
            return None;
        }
        match plan.action() {
            Action::Retarget(epoch) => Some(epoch),
            _ => None,
        }
    }

    pub(crate) fn mature_retarget_count(&self, epoch: Epoch) -> u64 {
        self.ranges(epoch)
            .into_iter()
            .map(|(lo, hi)| {
                if lo >= hi {
                    return 0;
                }
                let step = epoch.length();
                let first = lo.div_ceil(step) * step;
                if first >= hi {
                    0
                } else {
                    1 + (hi - 1 - first) / step
                }
            })
            .sum()
    }
}

/// Shared exact mature-interval shift kernel used by both logical and
/// physical DAA coefficient consumers. Empty clipped intervals are skipped
/// before invoking the non-wrapping borrow automaton.
pub(crate) fn evaluate_mature_shift(
    epoch: Epoch,
    schedule: &ScheduleDomain,
    row: &[Fr],
    source: &[Fr],
    target: &[Fr],
    offset: u64,
    right: RightIndex,
) -> Result<Fr, String> {
    if row.len() != schedule.slot_log
        || source.len() != schedule.slot_log
        || target.len() != schedule.slot_log
    {
        return Err("mature slot coefficient point dimensions rejected".into());
    }
    let mut result = Fr::zero();
    let align = epoch.length().trailing_zeros() as usize;
    for (lo, hi) in schedule.ranges(epoch) {
        if lo == hi {
            continue;
        }
        result += wiring::evaluate_shift(row, source, target, offset, lo, hi, align, right)?;
    }
    Ok(result)
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
    use ark_ff::Zero;
    use ergo_header_core::Header;
    use serde::Deserialize;
    use std::collections::HashMap;

    const FIXTURE: &str = include_str!("../fixtures/mainnet-daa-windows-v1.json");

    #[derive(Deserialize)]
    struct Fixture {
        cases: Vec<Case>,
        headers: Vec<HeaderEntry>,
    }
    #[derive(Deserialize)]
    struct Case {
        child: u32,
        parent: u32,
        samples: Vec<u32>,
    }
    #[derive(Deserialize)]
    struct HeaderEntry {
        height: u32,
        raw_hex: String,
    }

    fn fixture() -> (Fixture, HashMap<u32, Vec<u8>>) {
        let value: Fixture = serde_json::from_str(FIXTURE).unwrap();
        let headers = value
            .headers
            .iter()
            .map(|entry| (entry.height, decode_hex(&entry.raw_hex)))
            .collect();
        (value, headers)
    }

    fn decode_hex(text: &str) -> Vec<u8> {
        text.as_bytes()
            .chunks_exact(2)
            .map(|pair| u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).unwrap())
            .collect()
    }

    fn bits(value: u64, bit: usize) -> bool {
        (value >> bit) & 1 == 1
    }

    fn boolean_point(index: u64, dimension: usize) -> Vec<Fr> {
        (0..dimension)
            .map(|bit| {
                if (index >> bit) & 1 == 1 {
                    Fr::one()
                } else {
                    Fr::zero()
                }
            })
            .collect()
    }

    fn native_source_height(
        plan: &daa_header_window::ChildPlan,
        child_height: u32,
        family: PortFamily,
        field_index: usize,
    ) -> u32 {
        let samples = plan.sample_heights();
        match family {
            PortFamily::Timestamp => samples[field_index / 64],
            PortFamily::SampleNBits => samples[field_index / 32 + 1],
            PortFamily::X0Height => samples[1],
            PortFamily::ChildNBits => child_height,
        }
    }

    fn native_epoch(target_slot: u64) -> Option<Epoch> {
        let child = u32::try_from(target_slot.checked_add(1)?).ok()?;
        let plan = daa_header_window::for_child_height(child).ok()?;
        if plan.sample_heights().len() != 9 {
            return None;
        }
        match plan.action() {
            Action::Retarget(epoch) => Some(epoch),
            _ => None,
        }
    }

    fn native_reference_at_slot(
        wiring: &DaaScheduleWiring,
        epoch: Epoch,
        schedule: &ScheduleDomain,
        target_slot: u64,
        row: &[Fr],
        serializer_source: &[Fr],
        daa_target: &[Fr],
    ) -> [Fr; 4] {
        let mut result = [Fr::zero(); 4];
        if target_slot >= schedule.upper_bound() {
            return result;
        }
        let child_height = match target_slot
            .checked_add(1)
            .and_then(|height| u32::try_from(height).ok())
        {
            Some(height) => height,
            None => return result,
        };
        let plan = match daa_header_window::for_child_height(child_height) {
            Ok(plan) => plan,
            Err(_) => return result,
        };
        if plan.sample_heights().len() != 9
            || !matches!(plan.action(), Action::Retarget(selected) if selected == epoch)
        {
            return result;
        }

        let source_local = &serializer_source[..HEADER_SLOT_LOG];
        let source_slots = &serializer_source[HEADER_SLOT_LOG..];
        let target_local = &daa_target[..HEADER_SLOT_LOG];
        let target_slots = &daa_target[HEADER_SLOT_LOG..];
        let row_ports = &row[..PORT_LOG];
        let row_slots = &row[PORT_LOG..];
        for (port_index, port) in wiring.ports(epoch).iter().enumerate() {
            let source_height =
                native_source_height(&plan, child_height, port.family, port.field_index);
            let source_slot = source_height as u64 - 1;
            if source_slot > target_slot {
                continue;
            }
            let weight = eq_index(row_ports, port_index)
                * eq_index(row_slots, target_slot as usize)
                * eq_index(source_local, port.serializer_wire)
                * eq_index(source_slots, source_slot as usize)
                * eq_index(target_local, port.daa_wire)
                * eq_index(target_slots, target_slot as usize);
            result[1] += weight;
            result[2] -= weight;
        }
        result
    }

    #[test]
    fn fixed_masks_match_native_branch_and_nine_positive_sample_selection() {
        let domain = ScheduleDomain::new(1 << 21, 21).unwrap();
        let windows = [
            (1u64, 9_300u64),
            (417_780, 417_810),
            (844_660, 844_690),
            ((1 << 21) - 24, 1 << 21),
        ];
        for (lo, hi) in windows {
            for target in lo..hi {
                let expected = native_epoch(target);
                assert_eq!(
                    domain.contains_mature_retarget(target),
                    expected,
                    "slot {target}"
                );
                assert_eq!(
                    domain.contains_mature_retarget(target),
                    if target >= LEGACY_MATURE_FROM
                        && target < LEGACY_RESET_SLOT
                        && target % LEGACY_EPOCH == 0
                    {
                        Some(Epoch::Legacy)
                    } else if target > LEGACY_RESET_SLOT
                        && target < EIP_FIRST_SLOT
                        && target % LEGACY_EPOCH == 0
                    {
                        Some(Epoch::Legacy)
                    } else if target >= EIP_FIRST_SLOT && target % EIP_EPOCH == 0 {
                        Some(Epoch::Eip)
                    } else {
                        None
                    },
                    "fixed range mask at slot {target}",
                );
            }
        }
        assert_eq!(LEGACY_EPOCH, Epoch::Legacy.length());
        assert_eq!(EIP_EPOCH, Epoch::Eip.length());
        assert_eq!(domain.contains_mature_retarget(0), None); // height 1 / genesis boundary
        assert_eq!(domain.contains_mature_retarget(8 * LEGACY_EPOCH), None); // only eight positive samples
        assert_eq!(
            domain.contains_mature_retarget(9 * LEGACY_EPOCH),
            Some(Epoch::Legacy)
        );
        assert_eq!(domain.contains_mature_retarget(LEGACY_RESET_SLOT), None); // V2 reset child
        assert_eq!(
            domain.contains_mature_retarget(EIP_FIRST_SLOT),
            Some(Epoch::Eip)
        );
        assert_eq!(domain.mature_retarget_count(Epoch::Legacy), 815);
        let retained_history = ScheduleDomain::new(1_827_840, 21).unwrap();
        assert_eq!(retained_history.mature_retarget_count(Epoch::Legacy), 815);
        assert_eq!(retained_history.mature_retarget_count(Epoch::Eip), 7_681);
    }

    #[test]
    fn compiled_ports_match_actual_fixture_serializer_and_daa_witness_bits() {
        let (fixture, headers) = fixture();
        let serializer = serializer::build(None).unwrap();
        let wiring = DaaScheduleWiring::compile().unwrap();
        for child_height in [9_217, 844_673, 844_801] {
            let case = fixture
                .cases
                .iter()
                .find(|case| case.child == child_height)
                .unwrap();
            let parent_raw = headers.get(&case.parent).unwrap();
            let child_raw = headers.get(&case.child).unwrap();
            let samples = case
                .samples
                .iter()
                .map(|height| headers.get(height).unwrap().as_slice())
                .collect::<Vec<_>>();
            let selected =
                daa_header_window::select_window(parent_raw, child_raw, &samples).unwrap();
            let epoch = match selected.action() {
                Action::Retarget(epoch) => epoch,
                _ => panic!("fixture retarget"),
            };
            let actual_daa = daa_header_window::compile_selected_window(&selected).unwrap();
            let actual_witness = &actual_daa.joined.joined.joined.witness;
            let actual_window = &actual_daa.joined.joined.joined;
            let mapped_ports = wiring.ports(epoch);
            assert_eq!(mapped_ports.len(), PORT_COUNT);
            assert_eq!(
                mapped_ports
                    .iter()
                    .filter(|port| port.family == PortFamily::Timestamp)
                    .count(),
                9 * 64
            );
            assert_eq!(
                mapped_ports
                    .iter()
                    .filter(|port| port.family == PortFamily::SampleNBits)
                    .count(),
                8 * 32
            );
            assert_eq!(
                mapped_ports
                    .iter()
                    .filter(|port| port.family == PortFamily::X0Height)
                    .count(),
                32
            );
            assert_eq!(
                mapped_ports
                    .iter()
                    .filter(|port| port.family == PortFamily::ChildNBits)
                    .count(),
                32
            );

            let raw_order = case
                .samples
                .iter()
                .map(|height| headers.get(height).unwrap())
                .chain(std::iter::once(child_raw))
                .collect::<Vec<_>>();
            let decoded = raw_order
                .iter()
                .map(|raw| Header::decode(raw, None).unwrap())
                .collect::<Vec<_>>();
            let assignments = decoded
                .iter()
                .map(|header| serializer.assign(&serializer::Fields::from_header(header).unwrap()))
                .collect::<Vec<_>>();
            let prediction = selected.prediction();
            let target_slot = child_height as u64 - 1;
            let plan = daa_header_window::for_child_height(child_height).unwrap();
            let schedule = ScheduleDomain::new(child_height as u64, 21).unwrap();
            for (port_index, port) in mapped_ports.iter().enumerate() {
                let source_height =
                    native_source_height(&plan, child_height, port.family, port.field_index);
                let source_ordinal = decoded
                    .iter()
                    .position(|header| header.height == source_height)
                    .unwrap();
                let source = &decoded[source_ordinal];
                let expected = match port.family {
                    PortFamily::Timestamp => bits(source.timestamp as u64, port.field_index % 64),
                    PortFamily::SampleNBits | PortFamily::ChildNBits => {
                        bits(source.n_bits as u64, port.field_index % 32)
                    }
                    PortFamily::X0Height => bits(source.height as u64, port.field_index),
                };

                let expected_serializer_wire = match port.family {
                    PortFamily::Timestamp => {
                        serializer.layout.fields.timestamp[port.field_index % 64]
                    }
                    PortFamily::SampleNBits | PortFamily::ChildNBits => {
                        serializer.layout.fields.n_bits[port.field_index % 32]
                    }
                    PortFamily::X0Height => serializer.layout.fields.height[port.field_index],
                };
                let expected_daa_wire = match port.family {
                    PortFamily::Timestamp => {
                        let external = port.field_index / 64;
                        let bit = port.field_index % 64;
                        if external == 8 {
                            actual_window.external[7].end_timestamp[bit]
                        } else {
                            actual_window.external[external].start_timestamp[bit]
                        }
                    }
                    PortFamily::SampleNBits => {
                        actual_window.external[port.field_index / 32].nbits[port.field_index % 32]
                    }
                    PortFamily::X0Height => actual_daa.joined.output.x0_bits[port.field_index],
                    PortFamily::ChildNBits => {
                        actual_daa.child_nbits.as_ref().unwrap()[port.field_index]
                    }
                };
                assert_eq!(port.serializer_wire, expected_serializer_wire);
                assert_eq!(port.daa_wire, expected_daa_wire);
                assert_eq!(
                    assignments[source_ordinal][expected_serializer_wire].is_one(),
                    expected
                );
                assert_eq!(actual_witness[expected_daa_wire].is_one(), expected);

                let source_slot = source_height as u64 - 1;
                let row = boolean_point(
                    ((target_slot << PORT_LOG) | port_index as u64),
                    PORT_LOG + schedule.slot_log(),
                );
                let serializer_point = boolean_point(
                    (source_slot << HEADER_SLOT_LOG) | expected_serializer_wire as u64,
                    HEADER_SLOT_LOG + schedule.slot_log(),
                );
                let daa_point = boolean_point(
                    (target_slot << HEADER_SLOT_LOG) | expected_daa_wire as u64,
                    HEADER_SLOT_LOG + schedule.slot_log(),
                );
                assert_eq!(
                    wiring
                        .evaluate(epoch, &schedule, &row, &serializer_point, &daa_point)
                        .unwrap(),
                    [Fr::zero(), Fr::one(), -Fr::one(), Fr::zero()],
                    "Boolean port {port_index}, child {child_height}, {:?} bit {}",
                    port.family,
                    port.field_index
                );
                let expected_offset = target_slot - source_slot;
                assert_eq!(port.offset(epoch), expected_offset);
            }
            assert_eq!(prediction.x0, case.samples[1]);
            let latest_timestamp = mapped_ports
                .iter()
                .find(|port| port.family == PortFamily::Timestamp && port.field_index == 8 * 64)
                .unwrap();
            assert_eq!(latest_timestamp.offset(epoch), 1);
            let child_timestamp = (0..64)
                .map(|bit| assignments[9][serializer.layout.fields.timestamp[bit]].is_one())
                .collect::<Vec<_>>();
            let parent_timestamp = (0..64)
                .map(|bit| {
                    let port = mapped_ports
                        .iter()
                        .find(|port| {
                            port.family == PortFamily::Timestamp && port.field_index == 8 * 64 + bit
                        })
                        .unwrap();
                    actual_witness[port.daa_wire].is_one()
                })
                .collect::<Vec<_>>();
            assert_ne!(
                child_timestamp, parent_timestamp,
                "zero-shift latest-parent mutant"
            );
        }
    }

    #[test]
    fn analytic_coefficients_match_native_selection_across_epochs_and_bounds() {
        let wiring = DaaScheduleWiring::compile().unwrap();
        // The logical upper domain is represented symbolically; no historical
        // serializer rows or DAA witness arrays are materialized here.
        let history_slots = 1_827_840u64;
        let schedule = ScheduleDomain::new(history_slots, 21).unwrap();
        let point = |len: usize, seed: u64| {
            (0..len)
                .map(|index| Fr::from(seed + 19 * index as u64 + 3))
                .collect::<Vec<_>>()
        };
        let row_ports = point(PORT_LOG, 5);
        let source = point(HEADER_SLOT_LOG + schedule.slot_log(), 17);
        let target = point(HEADER_SLOT_LOG + schedule.slot_log(), 41);
        // Each prefix has exactly one active retarget of the selected epoch.
        // All coordinates, including row slots, exercise the analytic path.
        for (epoch, active_slot) in [
            (Epoch::Legacy, LEGACY_MATURE_FROM),
            (Epoch::Eip, EIP_FIRST_SLOT),
        ] {
            let dense_schedule = ScheduleDomain::new(active_slot + 1, 21).unwrap();
            let dense_row = point(PORT_LOG + dense_schedule.slot_log(), 5);
            let expected = native_reference_at_slot(
                &wiring,
                epoch,
                &dense_schedule,
                active_slot,
                &dense_row,
                &source,
                &target,
            );
            let actual = wiring
                .evaluate(epoch, &dense_schedule, &dense_row, &source, &target)
                .unwrap();
            assert_eq!(actual, expected, "dense off-Boolean row slots, {epoch:?}");
            assert!(!actual[1].is_zero(), "dense reference must be populated");
        }
        let targets = [
            (Epoch::Legacy, LEGACY_MATURE_FROM),
            (Epoch::Legacy, LEGACY_RESET_SLOT - LEGACY_EPOCH),
            (Epoch::Legacy, LEGACY_RESET_SLOT - 1),
            (Epoch::Legacy, LEGACY_RESET_SLOT),
            (Epoch::Legacy, 843_776),
            (Epoch::Eip, EIP_FIRST_SLOT),
            (Epoch::Eip, EIP_FIRST_SLOT + EIP_EPOCH),
            (Epoch::Eip, (history_slots - 1) / EIP_EPOCH * EIP_EPOCH),
        ];
        for (epoch, target_slot) in targets {
            let mut row = row_ports.clone();
            row.extend(boolean_point(target_slot, schedule.slot_log()));
            let expected = native_reference_at_slot(
                &wiring,
                epoch,
                &schedule,
                target_slot,
                &row,
                &source,
                &target,
            );
            let actual = wiring
                .evaluate(epoch, &schedule, &row, &source, &target)
                .unwrap();
            assert_eq!(actual, expected, "native slot {target_slot}, {epoch:?}");
            if native_epoch(target_slot) == Some(epoch) {
                assert!(!actual[1].is_zero(), "active slot {target_slot}");
                let wrong_orientation = wiring
                    .evaluate(epoch, &schedule, &row, &target, &source)
                    .unwrap();
                assert_ne!(wrong_orientation, actual, "orientation at {target_slot}");
            }
        }

        let before_eip = ScheduleDomain::new(EIP_FIRST_SLOT, 21).unwrap();
        let mut endpoint_row = row_ports.clone();
        endpoint_row.extend(boolean_point(EIP_FIRST_SLOT, 21));
        assert_eq!(
            wiring
                .evaluate(Epoch::Eip, &before_eip, &endpoint_row, &source, &target)
                .unwrap(),
            [Fr::zero(); 4],
            "active slot at exclusive history endpoint"
        );
        let includes_eip = ScheduleDomain::new(EIP_FIRST_SLOT + 1, 21).unwrap();
        let expected = native_reference_at_slot(
            &wiring,
            Epoch::Eip,
            &includes_eip,
            EIP_FIRST_SLOT,
            &endpoint_row,
            &source,
            &target,
        );
        assert_eq!(
            wiring
                .evaluate(Epoch::Eip, &includes_eip, &endpoint_row, &source, &target)
                .unwrap(),
            expected
        );
    }

    #[test]
    fn boolean_port_mutants_fail_at_the_intended_coordinate() {
        let wiring = DaaScheduleWiring::compile().unwrap();
        let epoch = Epoch::Eip;
        let target_slot = EIP_FIRST_SLOT + EIP_EPOCH;
        let schedule = ScheduleDomain::new(target_slot + 1, 21).unwrap();
        let child_height = target_slot as u32 + 1;
        let plan = daa_header_window::for_child_height(child_height).unwrap();

        let timestamp_index = 8 * 64;
        let timestamp_port_index = timestamp_index;
        let timestamp_port = wiring.ports(epoch)[timestamp_port_index];
        let source_height =
            native_source_height(&plan, child_height, PortFamily::Timestamp, timestamp_index);
        let row = boolean_point(
            (target_slot << PORT_LOG) | timestamp_port_index as u64,
            PORT_LOG + schedule.slot_log(),
        );
        let serializer_point = boolean_point(
            (((source_height as u64 - 1) << HEADER_SLOT_LOG)
                | timestamp_port.serializer_wire as u64),
            HEADER_SLOT_LOG + schedule.slot_log(),
        );
        let daa_point = boolean_point(
            ((target_slot << HEADER_SLOT_LOG) | timestamp_port.daa_wire as u64),
            HEADER_SLOT_LOG + schedule.slot_log(),
        );
        let valid = [Fr::zero(), Fr::one(), -Fr::one(), Fr::zero()];
        assert_eq!(
            wiring
                .evaluate(epoch, &schedule, &row, &serializer_point, &daa_point)
                .unwrap(),
            valid
        );

        let mut missing = DaaScheduleWiring::compile().unwrap();
        missing.eip.ports.pop();
        let last_index = PORT_COUNT - 1;
        let last = wiring.ports(epoch)[last_index];
        let last_row = boolean_point(
            (target_slot << PORT_LOG) | last_index as u64,
            PORT_LOG + schedule.slot_log(),
        );
        let last_source_height =
            native_source_height(&plan, child_height, last.family, last.field_index);
        let last_source = boolean_point(
            (((last_source_height as u64 - 1) << HEADER_SLOT_LOG) | last.serializer_wire as u64),
            HEADER_SLOT_LOG + schedule.slot_log(),
        );
        let last_target = boolean_point(
            ((target_slot << HEADER_SLOT_LOG) | last.daa_wire as u64),
            HEADER_SLOT_LOG + schedule.slot_log(),
        );
        assert_eq!(
            missing
                .evaluate(epoch, &schedule, &last_row, &last_source, &last_target)
                .unwrap(),
            [Fr::zero(); 4],
            "missing mandatory last port"
        );

        let shifted_source_slot = source_height as u64 - 2;
        let shifted_serializer_point = boolean_point(
            (shifted_source_slot << HEADER_SLOT_LOG) | timestamp_port.serializer_wire as u64,
            HEADER_SLOT_LOG + schedule.slot_log(),
        );
        assert_eq!(
            wiring
                .evaluate(
                    epoch,
                    &schedule,
                    &row,
                    &shifted_serializer_point,
                    &daa_point
                )
                .unwrap(),
            [Fr::zero(); 4],
            "serializer source selected one slot too early (offset + 1)"
        );

        let mut wrong_serializer_wire = DaaScheduleWiring::compile().unwrap();
        wrong_serializer_wire.eip.ports[timestamp_port_index].serializer_wire += 1;
        assert_eq!(
            wrong_serializer_wire
                .evaluate(epoch, &schedule, &row, &serializer_point, &daa_point)
                .unwrap(),
            [Fr::zero(); 4],
            "wrong serializer local coordinate"
        );

        let mut wrong_daa_wire = DaaScheduleWiring::compile().unwrap();
        wrong_daa_wire.eip.ports[timestamp_port_index].daa_wire += 1;
        assert_eq!(
            wrong_daa_wire
                .evaluate(epoch, &schedule, &row, &serializer_point, &daa_point)
                .unwrap(),
            [Fr::zero(); 4],
            "wrong DAA local coordinate"
        );
    }

    #[test]
    fn schedule_bounds_clip_padding_and_reject_invalid_dimensions() {
        let short = ScheduleDomain::new(1, 20).unwrap();
        assert_eq!(short.upper_bound(), 1);
        assert_eq!(short.mature_retarget_count(Epoch::Legacy), 0);
        assert_eq!(short.contains_mature_retarget(1024), None); // power-of-two padding
        let max_height =
            ScheduleDomain::new(daa_header_window::MAX_CHILD_HEIGHT as u64, 31).unwrap();
        assert_eq!(
            max_height.upper_bound(),
            daa_header_window::MAX_CHILD_HEIGHT as u64
        );
        assert_eq!(
            max_height.contains_mature_retarget(daa_header_window::MAX_CHILD_HEIGHT as u64 - 1),
            None
        );
        assert!(ScheduleDomain::new(0, 20).is_err());
        assert!(ScheduleDomain::new(u32::MAX as u64, 32).is_err());
        assert!(ScheduleDomain::new((1 << 20) + 1, 20).is_err());
        assert!(ScheduleDomain::new(1, 44).is_err());

        let wiring = DaaScheduleWiring::compile().unwrap();
        let valid_schedule = ScheduleDomain::new(1_000, 10).unwrap();
        let valid_row = vec![Fr::zero(); PORT_LOG + valid_schedule.slot_log()];
        let valid_source = vec![Fr::zero(); HEADER_SLOT_LOG + valid_schedule.slot_log()];
        let valid_target = valid_source.clone();
        assert!(wiring
            .evaluate(
                Epoch::Legacy,
                &valid_schedule,
                &valid_row[..valid_row.len() - 1],
                &valid_source,
                &valid_target,
            )
            .is_err());
        assert!(wiring
            .evaluate(
                Epoch::Legacy,
                &valid_schedule,
                &valid_row,
                &valid_source[..valid_source.len() - 1],
                &valid_target,
            )
            .is_err());
        assert!(wiring
            .evaluate(
                Epoch::Legacy,
                &valid_schedule,
                &valid_row,
                &valid_source,
                &valid_target[..valid_target.len() - 1],
            )
            .is_err());
    }
}

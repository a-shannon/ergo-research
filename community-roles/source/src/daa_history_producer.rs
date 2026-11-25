//! Native retarget assignments into one packed physical owner.
//! Full-history custody, GKR/PCS consumption and PoW remain separate.
use std::{collections::BTreeMap, sync::OnceLock};

use ark_bn254::Fr;
use ark_ff::{One, Zero};
use blake2::{digest::consts::U32, Blake2b, Digest};
use ergo_header_core::Header;

use crate::{
    daa_count, daa_finish,
    daa_header_window::{self, Action},
    daa_history_roster::{Counts, DaaHistoryRoster, OwnerClass, BANKS, WIDTH},
    daa_integer::{Epoch, Inputs, ShortLegacyInputs, ShortLegacyProfile, TwoRatioInputs},
    daa_one_ratio_finish, header_hash, serializer,
    short_daa_layout::Profile,
};

pub(crate) const PACKED_OWNER_BYTES: usize = WIDTH / 8;
pub(crate) const PATCH_BYTES: usize = 10_240;
pub(crate) const MAX_EXTERNAL_CELLS: usize = 4096;
const OWNER_ROWS: usize = 1 << 19;

#[derive(Clone, Copy)]
pub(crate) struct RawWindow<'a> {
    pub(crate) parent: &'a [u8],
    pub(crate) child: &'a [u8],
    pub(crate) samples: &'a [&'a [u8]],
}

#[derive(Debug)]
pub(crate) struct Receipt {
    pub(crate) owner: u64,
    pub(crate) class: OwnerClass,
    pub(crate) counts: Counts,
    pub(crate) patched_bytes: usize,
    pub(crate) external_cells: usize,
}

/// Opaque bytes authored by a successfully validated native retarget write.
/// Only `apply` can construct this after copying every bank into its destination.
pub(crate) struct DaaBankPatch {
    owner: u64,
    class: OwnerClass,
    banks: Vec<(usize, Vec<u8>)>,
}
impl DaaBankPatch {
    pub(crate) fn identity(&self) -> (u64, OwnerClass) {
        (self.owner, self.class)
    }

    pub(crate) fn read_bank_bit(&self, local_wire: usize) -> Result<Option<bool>, String> {
        let Some((index, &(start, end))) = BANKS.iter().enumerate()
            .find(|(_, (start, end))| (*start..*end).contains(&local_wire)) else {
            return Ok(None);
        };
        if self.banks.len() != BANKS.len() {
            return Err("retarget author patch bank count".into());
        }
        let (patch_start, bytes) = &self.banks[index];
        if *patch_start != start / 8 || bytes.len() != (end - start) / 8 {
            return Err("retarget author patch bank geometry".into());
        }
        let offset = local_wire - start;
        Ok(Some((bytes[offset / 8] >> (offset % 8)) & 1 != 0))
    }

    #[cfg(test)]
    pub(crate) fn zero_for_test(owner: u64, class: OwnerClass) -> Self {
        Self {
            owner,
            class,
            banks: BANKS.iter().map(|&(start, end)| {
                (start / 8, vec![0; (end - start) / 8])
            }).collect(),
        }
    }

    #[cfg(test)]
    pub(crate) fn wrong_owner_for_test(&mut self) { self.owner += 1; }

    #[cfg(test)]
    pub(crate) fn flip_first_bit_for_test(&mut self) { self.banks[0].1[0] ^= 1; }

    #[cfg(test)]
    pub(crate) fn shift_first_bank_for_test(&mut self) { self.banks[0].0 += 1; }
}

struct Prepared {
    class: OwnerClass,
    values: Vec<Fr>,
    headers: Vec<Header>,
    #[cfg(test)]
    observation: numeric_probe::Observation,
}

fn in_bank(wire: usize) -> bool {
    BANKS
        .iter()
        .any(|&(start, end)| (start..end).contains(&wire))
}

fn check_destination(destination: &[u8]) -> Result<(), String> {
    if destination.len() != PACKED_OWNER_BYTES {
        return Err("retarget producer destination width".into());
    }
    let mut count = 0;
    for (start, end) in BANKS {
        if start >= end || end > WIDTH || start % 8 != 0 || end % 8 != 0 {
            return Err("retarget producer bank geometry".into());
        }
        if destination[start / 8..end / 8]
            .iter()
            .any(|&byte| byte != 0)
        {
            return Err(format!("retarget producer nonempty bank at {start}"));
        }
        count += (end - start) / 8;
    }
    if count != PATCH_BYTES {
        return Err("retarget producer patch size".into());
    }
    Ok(())
}

fn decode(raw: &[u8]) -> Result<Header, String> {
    if raw.is_empty() || raw.len() > 514 {
        return Err("retarget producer RAW length".into());
    }
    let header =
        Header::decode(raw, None).map_err(|e| format!("retarget producer RAW decode: {e:?}"))?;
    if header.encode().map_err(|e| format!("RAW encode: {e:?}"))? != raw {
        return Err("retarget producer noncanonical RAW".into());
    }
    serializer::Fields::from_header(&header)?;
    Ok(header)
}

fn prepare(
    roster: &DaaHistoryRoster<'_>,
    owner: u64,
    raw: RawWindow<'_>,
) -> Result<Prepared, String> {
    let class = roster.owner_class(owner)?;
    let epoch = match class {
        OwnerClass::M1 | OwnerClass::Short(_) => Epoch::Legacy,
        OwnerClass::Mature(epoch) => epoch,
        _ => return Err("retarget producer unsupported owner class".into()),
    };
    let child = decode(raw.child)?;
    let expected = owner
        .checked_add(1)
        .ok_or("retarget producer owner overflow")?;
    if u64::from(child.height) != expected {
        return Err("retarget producer child owner mismatch".into());
    }
    let parent = decode(raw.parent)?;
    if parent.height.checked_add(1) != Some(child.height) {
        return Err("retarget producer parent height mismatch".into());
    }
    let parent_id: [u8; 32] = Blake2b::<U32>::digest(raw.parent).into();
    if child.parent_id != parent_id {
        return Err("retarget producer parent identity mismatch".into());
    }
    let schedule = daa_header_window::for_child_height(child.height)?;
    if schedule.action() != Action::Retarget(epoch) {
        return Err("retarget producer native schedule mismatch".into());
    }
    if raw.samples.len() != schedule.sample_heights().len() {
        return Err("retarget producer sample count mismatch".into());
    }
    let mut samples = Vec::with_capacity(raw.samples.len());
    for (bytes, &height) in raw.samples.iter().zip(schedule.sample_heights()) {
        let header = decode(bytes)?;
        if header.height != height {
            return Err("retarget producer sample height mismatch".into());
        }
        samples.push(header);
    }
    if raw.samples.last().copied() != Some(raw.parent) {
        return Err("retarget producer last sample is not exact parent".into());
    }
    let timestamps: Vec<i64> = samples.iter().map(|h| h.timestamp).collect();
    let nbits: Vec<u32> = samples.iter().skip(1).map(|h| h.n_bits).collect();
    #[cfg(test)]
    let mut observation = numeric_probe::Observation::default();
    let values = match class {
        OwnerClass::M1 => {
            if samples.len() != 2 {
                return Err("retarget producer M1 sample geometry".into());
            }
            let compiled = daa_one_ratio_finish::compile(
                &daa_count::q(),
                Inputs {
                    nbits: nbits[0],
                    start_timestamp: timestamps[0],
                    end_timestamp: timestamps[1],
                },
                child.n_bits,
                true,
            )?;
            let mapped = roster.admit_one(&compiled)?;
            #[cfg(test)]
            { observation = numeric_probe::one(&compiled, &mapped)?; }
            mapped.witness().to_vec()
        }
        OwnerClass::Short(profile) => {
            if samples.len() != profile.count() + 1 {
                return Err("retarget producer short sample geometry".into());
            }
            let compiled = if profile == Profile::M2 {
                daa_finish::compile_two_finish_with_child(
                    &daa_count::q(),
                    TwoRatioInputs {
                        nbits: nbits
                            .try_into()
                            .map_err(|_| "retarget producer M2 compact geometry")?,
                        timestamps: timestamps
                            .try_into()
                            .map_err(|_| "retarget producer M2 time geometry")?,
                    },
                    child.n_bits,
                    true,
                )?
            } else {
                let profile = match profile {
                    Profile::M3 => ShortLegacyProfile::M3,
                    Profile::M4 => ShortLegacyProfile::M4,
                    Profile::M5 => ShortLegacyProfile::M5,
                    Profile::M6 => ShortLegacyProfile::M6,
                    Profile::M7 => ShortLegacyProfile::M7,
                    Profile::M2 => unreachable!(),
                };
                daa_finish::compile_short_legacy_with_child(
                    &daa_count::q(),
                    ShortLegacyInputs {
                        profile,
                        nbits,
                        timestamps,
                    },
                    child.n_bits,
                    true,
                )?
            };
            let mapped = roster.admit_short(profile, &compiled)?;
            #[cfg(test)]
            { observation = numeric_probe::finish(&compiled, &mapped)?; }
            mapped.witness().to_vec()
        }
        OwnerClass::Mature(_) => {
            let selected = daa_header_window::select_window(raw.parent, raw.child, raw.samples)?;
            let compiled = daa_header_window::compile_selected_window(&selected)?;
            let mapped = roster.admit_mature(&selected, &compiled)?;
            #[cfg(test)]
            { observation = numeric_probe::finish(&compiled, &mapped)?; }
            mapped.witness().to_vec()
        }
        _ => return Err("retarget producer unsupported owner class".into()),
    };
    samples.push(child);
    Ok(Prepared {
        class,
        values,
        headers: samples,
        #[cfg(test)]
        observation,
    })
}

/// Test observations carry coordinates only, after the normal consumer map admission.
/// They contain neither witness values nor expected numeric results.
#[cfg(test)]
pub(crate) mod numeric_probe {
    use super::*;
    use crate::{daa_integer::{ExternalBits, OutputBits}, mapped_daa_plan::MappedDaaPlan,
        mapped_one_daa::MappedM1};

    #[derive(Clone, Default)]
    pub(crate) struct Observation {
        pub(crate) words: BTreeMap<String, Vec<usize>>,
    }
    impl Observation {
        fn put(&mut self, name: String, wires: &[usize],
            map: &impl Fn(usize) -> Result<usize, String>) -> Result<(), String> {
            let mapped = wires.iter().map(|&w| map(w)).collect::<Result<Vec<_>, _>>()?;
            if mapped.is_empty() || mapped.iter().any(|&w| !in_bank(w))
                || self.words.insert(name, mapped).is_some() {
                return Err("numeric probe coordinate census".into());
            }
            Ok(())
        }
        fn a1(&mut self, external: &[ExternalBits], output: &[OutputBits],
            map: &impl Fn(usize) -> Result<usize, String>) -> Result<(), String> {
            for (j, (external, out)) in external.iter().zip(output).enumerate() {
                for (name, wires) in [
                    ("nbits", external.nbits.as_slice()),
                    ("start_timestamp", external.start_timestamp.as_slice()),
                    ("end_timestamp", external.end_timestamp.as_slice()),
                    ("decoded_difficulty", out.decoded_difficulty.as_slice()),
                    ("wrapped_delta", out.wrapped_delta.as_slice()),
                    ("denominator_magnitude", out.denominator_magnitude.as_slice()),
                    ("numerator", out.numerator.as_slice()),
                    ("quotient_magnitude", out.quotient_magnitude.as_slice()),
                    ("quotient_negative", std::slice::from_ref(&out.quotient_negative)),
                    ("remainder_magnitude", out.remainder_magnitude.as_slice()),
                    ("remainder_negative", std::slice::from_ref(&out.remainder_negative)),
                ] { self.put(format!("a1.{j}.{name}"), wires, map)?; }
            }
            Ok(())
        }
    }
    pub(super) fn one(c: &daa_one_ratio_finish::CompiledOne, m: &MappedM1)
        -> Result<Observation, String> {
        let mut o = Observation::default();
        let map = |w| m.mapped_wire(w);
        o.a1(std::slice::from_ref(&c.arithmetic.external),
            std::slice::from_ref(&c.arithmetic.output), &map)?;
        for (name, wires) in [
            ("finish.delta_nonzero", std::slice::from_ref(&c.output.delta_nonzero)),
            ("finish.use_prediction", std::slice::from_ref(&c.output.use_quotient)),
            ("finish.selected", c.output.selected.as_slice()),
            ("finish.numeric_result", c.output.numeric_result.as_slice()),
            ("finish.child_nbits", c.output.child_nbits.as_slice()),
        ] { o.put(name.into(), wires, &map)?; }
        Ok(o)
    }
    pub(super) fn finish(c: &daa_finish::CompiledFinish, m: &MappedDaaPlan)
        -> Result<Observation, String> {
        let mut o = Observation::default();
        let map = |w| m.mapped_wire(w);
        let a1 = &c.joined.joined.joined;
        o.a1(&a1.external, &a1.output, &map)?;
        let r = &c.joined.joined.output;
        for (j, alias) in r.aliases.iter().enumerate() {
            o.put(format!("a2.alias.{j}.magnitude"), &alias.magnitude, &map)?;
            o.put(format!("a2.alias.{j}.negative"), &[alias.negative], &map)?;
        }
        for (name, wires) in [
            ("positive_sum", r.positive_sum.as_slice()), ("negative_sum", r.negative_sum.as_slice()),
            ("sum_magnitude", r.sum_magnitude.as_slice()), ("sum_negative", std::slice::from_ref(&r.sum_negative)),
            ("numerator", r.numerator.as_slice()), ("slope_magnitude", r.slope_magnitude.as_slice()),
            ("slope_negative", std::slice::from_ref(&r.slope_negative)),
            ("remainder", r.remainder.as_slice()), ("remainder_negative", std::slice::from_ref(&r.remainder_negative)),
        ] { o.put(format!("a2.{name}"), wires, &map)?; }
        let p = &c.joined.output;
        for (j, grid) in p.grid_x.iter().enumerate() { o.put(format!("a3.grid.{j}"), grid, &map)?; }
        for (name, wires) in [
            ("x0", p.x0_bits.as_slice()), ("sum_x", p.sum_x.as_slice()),
            ("b_magnitude", p.b_alias.magnitude.as_slice()), ("b_negative", std::slice::from_ref(&p.b_alias.negative)),
            ("y_magnitude", p.y_magnitude.as_slice()), ("y_negative", std::slice::from_ref(&p.y_negative)),
            ("py_magnitude", p.py_magnitude.as_slice()), ("b_sum_x_magnitude", p.b_sum_x_magnitude.as_slice()),
            ("x_magnitude", p.x_magnitude.as_slice()), ("x_negative", std::slice::from_ref(&p.x_negative)),
            ("a_magnitude", p.a_magnitude.as_slice()), ("a_negative", std::slice::from_ref(&p.a_negative)),
            ("a_remainder", p.a_remainder.as_slice()), ("a_remainder_negative", std::slice::from_ref(&p.a_remainder_negative)),
            ("point_twos", p.point_twos.as_slice()), ("point_magnitude", p.point_magnitude.as_slice()),
            ("point_negative", std::slice::from_ref(&p.point_negative)), ("b_point_magnitude", p.b_point_magnitude.as_slice()),
            ("term_magnitude", p.term_magnitude.as_slice()), ("term_negative", std::slice::from_ref(&p.term_negative)),
            ("term_remainder", p.term_remainder.as_slice()), ("term_remainder_negative", std::slice::from_ref(&p.term_remainder_negative)),
            ("prediction_magnitude", p.prediction_magnitude.as_slice()),
            ("prediction_negative", std::slice::from_ref(&p.prediction_negative)),
        ] { o.put(format!("a3.{name}"), wires, &map)?; }
        if let Some(trace) = &c.intercept_count_trace {
            for (name, wires) in [
                ("quotient_magnitude", trace.quotient_magnitude.as_slice()),
                ("quotient_negative", std::slice::from_ref(&trace.quotient_negative)),
                ("remainder_magnitude", trace.remainder_magnitude.as_slice()),
                ("remainder_negative", std::slice::from_ref(&trace.remainder_negative)),
            ] { o.put(format!("a3.count.{name}"), wires, &map)?; }
        }
        let f = &c.output;
        o.put("finish.use_prediction".into(), &[f.use_prediction], &map)?;
        o.put("finish.predictive".into(), &f.predictive, &map)?;
        o.put("finish.numeric_result".into(), &f.numeric_result, &map)?;
        o.put("finish.child_nbits".into(), c.child_nbits.as_ref().ok_or("numeric probe child port")?, &map)?;
        for (name, wires) in [ ("lower", &f.lower), ("upper", &f.upper),
            ("limited", &f.limited), ("average_magnitude", &f.average_magnitude),
            ("precompact", &f.precompact) ] {
            if let Some(wires) = wires { o.put(format!("finish.{name}"), wires, &map)?; }
        }
        if let Some(wire) = f.average_negative { o.put("finish.average_negative".into(), &[wire], &map)?; }
        Ok(o)
    }
}

#[cfg(test)]
pub(crate) fn write_observed_for_test<F: FnMut(usize) -> Result<bool, String>>(
    roster: &DaaHistoryRoster<'_>, owner: u64, raw: RawWindow<'_>,
    destination: &mut [u8], outside: F,
) -> Result<(Receipt, numeric_probe::Observation), String> {
    check_destination(destination)?;
    let mut prepared = prepare(roster, owner, raw)?;
    let observation = std::mem::take(&mut prepared.observation);
    let (receipt, _) = apply(roster, owner, prepared, destination, outside)?;
    Ok((receipt, observation))
}

fn field_layout() -> Result<&'static serializer::FieldLayout, String> {
    static LAYOUT: OnceLock<Result<serializer::FieldLayout, String>> = OnceLock::new();
    LAYOUT
        .get_or_init(|| Ok(serializer::build(None)?.layout.fields))
        .as_ref()
        .map_err(Clone::clone)
}

struct Overlay<'a, F> {
    owner_base: usize,
    input_len: usize,
    original: &'a [u8],
    prepared: &'a [Fr],
    outside: F,
    cache: BTreeMap<usize, bool>,
}
impl<F: FnMut(usize) -> Result<bool, String>> Overlay<'_, F> {
    fn bit(&mut self, index: usize) -> Result<bool, String> {
        if index >= self.input_len {
            return Err("retarget producer global input outside domain".into());
        }
        if (self.owner_base..self.owner_base + WIDTH).contains(&index) {
            let local = index - self.owner_base;
            return Ok(if in_bank(local) {
                self.prepared[local].is_one()
            } else {
                self.original[local / 8] & (1 << (local % 8)) != 0
            });
        }
        if let Some(value) = self.cache.get(&index) {
            return Ok(*value);
        }
        if self.cache.len() >= MAX_EXTERNAL_CELLS {
            return Err("retarget producer external cache limit".into());
        }
        let value = (self.outside)(index)?;
        self.cache.insert(index, value);
        Ok(value)
    }
}

fn apply<F: FnMut(usize) -> Result<bool, String>>(
    roster: &DaaHistoryRoster<'_>,
    owner: u64,
    prepared: Prepared,
    destination: &mut [u8],
    outside: F,
) -> Result<(Receipt, DaaBankPatch), String> {
    if prepared.values.len() != WIDTH {
        return Err("retarget producer mapped witness width".into());
    }
    for (wire, value) in prepared.values.iter().enumerate() {
        if !value.is_zero() && !value.is_one() {
            return Err(format!("retarget producer non-Boolean mapped cell {wire}"));
        }
        if !in_bank(wire) && !value.is_zero() {
            return Err(format!("retarget producer nonzero outside bank {wire}"));
        }
    }
    let owner = usize::try_from(owner).map_err(|_| "retarget producer owner width")?;
    let owner_base = owner
        .checked_mul(WIDTH)
        .ok_or("retarget producer owner base overflow")?;
    let input_len = 1usize
        .checked_shl(roster.input_log() as u32)
        .ok_or("retarget producer input width overflow")?;
    let mut overlay = Overlay {
        owner_base,
        input_len,
        original: destination,
        prepared: &prepared.values,
        outside,
        cache: BTreeMap::new(),
    };
    let layout = field_layout()?;
    for header in &prepared.headers {
        let slot = usize::try_from(
            header
                .height
                .checked_sub(1)
                .ok_or("retarget producer RAW height zero")?,
        )
        .map_err(|_| "retarget producer RAW height width")?;
        let base = slot
            .checked_mul(WIDTH)
            .and_then(|b| b.checked_add(header_hash::SERIALIZER_OFFSET))
            .ok_or("retarget producer RAW port base overflow")?;
        for (wires, word) in [
            (&layout.timestamp[..], header.timestamp as u64),
            (&layout.n_bits[..], u64::from(header.n_bits)),
            (&layout.height[..], u64::from(header.height)),
        ] {
            for (bit, &wire) in wires.iter().enumerate() {
                let index = base
                    .checked_add(wire)
                    .ok_or("retarget producer RAW port overflow")?;
                if overlay.bit(index)? != (word >> bit & 1 != 0) {
                    return Err(format!("retarget producer RAW port mismatch at {index}"));
                }
            }
        }
    }
    let row_base = owner
        .checked_mul(OWNER_ROWS)
        .ok_or("retarget producer row base overflow")?;
    let mut residuals = vec![Fr::zero(); OWNER_ROWS];
    let counts = roster.visit_owner_terms(owner as u64, |term| {
        let row = term
            .row
            .checked_sub(row_base)
            .ok_or("retarget producer wrong residual owner")?;
        if row >= OWNER_ROWS {
            return Err("retarget producer residual row outside owner".into());
        }
        let left = Fr::from(overlay.bit(term.gate.left)? as u64);
        let right = Fr::from(overlay.bit(term.gate.right)? as u64);
        residuals[row] +=
            term.gate.c0 + term.gate.c1 * left + term.gate.c2 * right + term.gate.c3 * left * right;
        Ok(())
    })?;
    if let Some((row, _)) = residuals
        .iter()
        .enumerate()
        .find(|(_, value)| !value.is_zero())
    {
        return Err(format!(
            "retarget producer nonzero residual lane {} row {}",
            row >> 17,
            row & ((1 << 17) - 1)
        ));
    }
    let external_cells = overlay.cache.len();
    drop(overlay);
    let mut patches = Vec::with_capacity(BANKS.len());
    for (start, end) in BANKS {
        let mut bytes = vec![0u8; (end - start) / 8];
        for wire in start..end {
            if prepared.values[wire].is_one() {
                bytes[(wire - start) / 8] |= 1 << ((wire - start) % 8);
            }
        }
        patches.push((start / 8, bytes));
    }
    // Every fallible validation precedes these fixed, size-checked memory copies.
    for (start, bytes) in &patches {
        destination[*start..*start + bytes.len()].copy_from_slice(bytes);
    }
    let patch = DaaBankPatch { owner: owner as u64, class: prepared.class, banks: patches };
    Ok((Receipt {
        owner: owner as u64,
        class: prepared.class,
        counts,
        patched_bytes: PATCH_BYTES,
        external_cells,
    }, patch))
}

pub(crate) fn write_retarget<F: FnMut(usize) -> Result<bool, String>>(
    roster: &DaaHistoryRoster<'_>,
    owner: u64,
    raw: RawWindow<'_>,
    destination: &mut [u8],
    outside: F,
) -> Result<Receipt, String> {
    check_destination(destination)?;
    let prepared = prepare(roster, owner, raw)?;
    apply(roster, owner, prepared, destination, outside).map(|(receipt, _)| receipt)
}

/// Native producer path that retains the exact validated bank bytes it copied.
/// The ordinary writer remains source-compatible and discards this authority.
pub(crate) fn write_retarget_with_patch<F: FnMut(usize) -> Result<bool, String>>(
    roster: &DaaHistoryRoster<'_>,
    owner: u64,
    raw: RawWindow<'_>,
    destination: &mut [u8],
    outside: F,
) -> Result<(Receipt, DaaBankPatch), String> {
    check_destination(destination)?;
    let prepared = prepare(roster, owner, raw)?;
    apply(roster, owner, prepared, destination, outside)
}

#[cfg(test)]
pub(crate) fn write_fault_for_test<F: FnMut(usize) -> Result<bool, String>>(
    roster: &DaaHistoryRoster<'_>,
    owner: u64,
    raw: RawWindow<'_>,
    destination: &mut [u8],
    outside: F,
    fault: impl FnOnce(&mut Vec<Fr>),
) -> Result<Receipt, String> {
    check_destination(destination)?;
    let mut prepared = prepare(roster, owner, raw)?;
    fault(&mut prepared.values);
    apply(roster, owner, prepared, destination, outside).map(|(receipt, _)| receipt)
}

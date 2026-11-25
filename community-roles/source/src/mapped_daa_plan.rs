//! Immutable phase-bank owner map for the complete padded A1–A4 relation.
//!
//! The original 2^16 coordinates are preserved injectively, including A4
//! padding. The reserved phase-bank slack is separately constrained to zero.
//! The independent true-child A4 anchor release remains exactly rows
//! 348_440..356_632 in `daa_count.rs:931-975`; this upper-block map does not
//! consume it.
use ark_bn254::Fr;
use ark_ff::Zero;

use crate::{
    daa_finish::CompiledFinish,
    gkr::Gate,
    sparse::{Circuit, Term},
    work_tree_layout,
};

pub(crate) const ORIGINAL_INPUT_LOG: usize = 16;
pub(crate) const ORIGINAL_INPUT_LEN: usize = 1 << ORIGINAL_INPUT_LOG;
pub(crate) const MAPPED_INPUT_LOG: usize = 20;
pub(crate) const MAPPED_INPUT_LEN: usize = 1 << MAPPED_INPUT_LOG;
pub(crate) const BANK_SLACK_ROWS: usize = 16_384;

const PHASE_BANKS: [(usize, usize); 4] = [
    (819_200, 32_768),
    (663_552, 8_192),
    (688_128, 32_768),
    (991_232, 8_192),
];

/// Fixed mapping derived from the four owned `CompiledFinish` checkpoints.
/// Callers can inspect individual wire ownership but cannot provide a map.
pub(crate) struct MappedDaaPlan {
    circuit: Circuit,
    witness: Vec<Fr>,
    original_to_mapped: Vec<usize>,
    phase_spans: [(usize, usize); 4],
    phase_used: [usize; 4],
    a4_live_end: usize,
    slack_wires: Vec<usize>,
}

impl MappedDaaPlan {
    pub(crate) fn compile(compiled: &CompiledFinish) -> Result<Self, String> {
        let window = &compiled.joined.joined.joined;
        let original = window
            .circuit
            .as_ref()
            .ok_or("complete DAA circuit was not materialized")?;
        let count = &window.count;
        if original.input_len != ORIGINAL_INPUT_LEN
            || count.padded_input_bits != ORIGINAL_INPUT_LEN
            || original.row_count != count.padded_rows
            || original.terms.len() != count.terms
            || window.witness.len() != ORIGINAL_INPUT_LEN
        {
            return Err("complete padded DAA source geometry changed".into());
        }

        // Require the compiler's complete progress ledger before using its
        // boundaries. Endpoints are never reconstructed from fixture counts.
        let a2 = &compiled.joined.joined.increment;
        let a3 = &compiled.joined.increment;
        let a4 = &compiled.increment;
        if a3.before != a2.after {
            return Err("DAA A2/A3 checkpoint continuity mismatch".into());
        }
        if a4.before != a3.after {
            return Err("DAA A3/A4 checkpoint continuity mismatch".into());
        }
        let a1_end = a2.before.live_bits;
        let a2_end = a2.after.live_bits;
        let a3_end = a3.after.live_bits;
        let a4_end = a4.after.live_bits;
        if count.live_bits == 0
            || a4_end > count.live_bits
            || count.input_bits != count.live_bits
            || count.padded_input_bits != count.live_bits.checked_next_power_of_two().unwrap_or(0)
            || count.padded_input_bits.checked_sub(count.live_bits) != Some(count.padding_bits)
            || a4.after.rows > count.residual_rows
            || a4.after.terms > count.terms
            || count.padded_rows != count.residual_rows.checked_next_power_of_two().unwrap_or(0)
        {
            return Err("DAA final count, padding, or checkpoint ledger mismatch".into());
        }
        if let Some(child_nbits) = compiled.child_nbits.as_ref() {
            for (offset, wire) in child_nbits.iter().enumerate() {
                if a4_end.checked_add(offset) != Some(*wire) {
                    return Err("DAA child nBits wires do not start at the A4 checkpoint".into());
                }
            }
            if a4_end
                .checked_add(child_nbits.len())
                .map_or(true, |end| end > count.live_bits)
            {
                return Err("DAA child nBits wires escape the final live input".into());
            }
        }
        if original.terms.iter().any(|term| {
            term.gate.left >= ORIGINAL_INPUT_LEN || term.gate.right >= ORIGINAL_INPUT_LEN
        }) {
            return Err("original DAA term escapes the padded input domain".into());
        }
        if !(0 < a1_end
            && a1_end <= a2_end
            && a2_end <= a3_end
            && a3_end <= a4_end
            && a4_end <= ORIGINAL_INPUT_LEN)
        {
            return Err("DAA phase checkpoints are not monotone within the padded input".into());
        }
        let phase_spans = [
            (0, a1_end),
            (a1_end, a2_end),
            (a2_end, a3_end),
            (a3_end, ORIGINAL_INPUT_LEN),
        ];
        let phase_used = phase_spans.map(|(start, end)| end - start);
        let baseline = work_tree_layout::shared_baseline()
            .map_err(|error| format!("frozen work-tree owner inventory unavailable: {error}"))?;
        validate_banks(phase_used, &baseline.inventory.free_ranges)?;

        let mut original_to_mapped = vec![usize::MAX; ORIGINAL_INPUT_LEN];
        let mut mapped_owners = vec![false; MAPPED_INPUT_LEN];
        for (phase, ((old_start, old_end), (bank_start, bank_width))) in
            phase_spans.iter().copied().zip(PHASE_BANKS).enumerate()
        {
            if old_end - old_start > bank_width {
                return Err(format!("DAA phase {phase} exceeds its fixed bank"));
            }
            for old_wire in old_start..old_end {
                let mapped = bank_start + old_wire - old_start;
                if mapped >= bank_start + bank_width || mapped_owners[mapped] {
                    return Err("DAA phase map collision or bank overflow".into());
                }
                original_to_mapped[old_wire] = mapped;
                mapped_owners[mapped] = true;
            }
        }
        if original_to_mapped.iter().any(|wire| *wire == usize::MAX) {
            return Err("DAA phase map leaves original padded coordinates unmapped".into());
        }

        let map_wire = |wire: usize| -> Result<usize, String> {
            original_to_mapped
                .get(wire)
                .copied()
                .filter(|mapped| *mapped != usize::MAX)
                .ok_or_else(|| "DAA source wire is outside the owned map".into())
        };
        let mut terms = Vec::with_capacity(original.terms.len() + BANK_SLACK_ROWS);
        for term in &original.terms {
            if term.row >= count.residual_rows {
                return Err("original DAA term escaped its residual-row prefix".into());
            }
            let mut gate = term.gate.clone();
            gate.left = map_wire(gate.left)?;
            gate.right = map_wire(gate.right)?;
            terms.push(Term {
                row: term.row,
                gate,
            });
        }

        if count
            .residual_rows
            .checked_add(BANK_SLACK_ROWS)
            .map_or(true, |end| end > original.row_count)
        {
            return Err("DAA bank slack exceeds available padded residual rows".into());
        }
        let mut slack_wires = Vec::with_capacity(BANK_SLACK_ROWS);
        for (bank_index, ((bank_start, bank_width), used)) in
            PHASE_BANKS.into_iter().zip(phase_used).enumerate()
        {
            for wire in bank_start + used..bank_start + bank_width {
                let row = count.residual_rows + slack_wires.len();
                if row >= original.row_count {
                    return Err(format!("DAA bank {bank_index} slack row exceeds padding"));
                }
                terms.push(Term {
                    row,
                    gate: Gate {
                        left: wire,
                        right: 0,
                        c0: Fr::zero(),
                        c1: Fr::from(1u64),
                        c2: Fr::zero(),
                        c3: Fr::zero(),
                    },
                });
                slack_wires.push(wire);
            }
        }
        if slack_wires.len() != BANK_SLACK_ROWS {
            return Err("DAA phase-bank slack count changed".into());
        }

        let mut witness = vec![Fr::zero(); MAPPED_INPUT_LEN];
        for (old_wire, mapped_wire) in original_to_mapped.iter().copied().enumerate() {
            witness[mapped_wire] = window.witness[old_wire];
        }
        let circuit = Circuit {
            input_len: MAPPED_INPUT_LEN,
            row_count: original.row_count,
            terms,
        };
        if circuit.terms.len() != original.terms.len() + BANK_SLACK_ROWS {
            return Err("mapped DAA term count changed".into());
        }
        Ok(Self {
            circuit,
            witness,
            original_to_mapped,
            phase_spans,
            phase_used,
            a4_live_end: a4_end,
            slack_wires,
        })
    }

    /// Compile a short-profile DAA map. The mature allocator above deliberately
    /// remains unchanged: short profiles retain their live phase offsets,
    /// place source padding in globally ordered free bank cells, and reserve
    /// the remaining cells for explicit zero constraints.
    pub(crate) fn compile_short(compiled: &CompiledFinish) -> Result<Self, String> {
        let window = &compiled.joined.joined.joined;
        if !(2..=7).contains(&window.external.len()) {
            return Err("short DAA requires two through seven source ratios".into());
        }
        let original = window
            .circuit
            .as_ref()
            .ok_or("complete DAA circuit was not materialized")?;
        let count = &window.count;
        if original.input_len != ORIGINAL_INPUT_LEN
            || count.padded_input_bits != ORIGINAL_INPUT_LEN
            || original.row_count != count.padded_rows
            || original.terms.len() != count.terms
            || window.witness.len() != ORIGINAL_INPUT_LEN
        {
            return Err("complete padded DAA source geometry changed".into());
        }
        let a2 = &compiled.joined.joined.increment;
        let a3 = &compiled.joined.increment;
        let a4 = &compiled.increment;
        if a3.before != a2.after {
            return Err("DAA A2/A3 checkpoint continuity mismatch".into());
        }
        if a4.before != a3.after {
            return Err("DAA A3/A4 checkpoint continuity mismatch".into());
        }
        let a1_end = a2.before.live_bits;
        let a2_end = a2.after.live_bits;
        let a3_end = a3.after.live_bits;
        let a4_end = a4.after.live_bits;
        if count.live_bits == 0
            || count.live_bits > ORIGINAL_INPUT_LEN
            || count.input_bits != count.live_bits
            || count.padded_input_bits != ORIGINAL_INPUT_LEN
            || count.padded_input_bits.checked_sub(count.live_bits) != Some(count.padding_bits)
            || a4_end > count.live_bits
            || a4_end
                .checked_add(32)
                .map_or(true, |end| end > count.live_bits)
            || a4.after.rows > count.residual_rows
            || a4.after.terms > count.terms
            || count.padded_rows != count.residual_rows.checked_next_power_of_two().unwrap_or(0)
            || count
                .residual_rows
                .checked_add(BANK_SLACK_ROWS)
                .map_or(true, |end| end > original.row_count)
            || count
                .terms
                .checked_add(BANK_SLACK_ROWS)
                .map_or(true, |terms| terms > crate::daa_integer::MAX_MATERIAL_TERMS)
        {
            return Err("short DAA final count, padding, or capacity ledger mismatch".into());
        }
        let child_nbits = compiled
            .child_nbits
            .as_ref()
            .ok_or("short DAA child nBits handles are missing")?;
        if child_nbits.len() != 32
            || child_nbits
                .iter()
                .enumerate()
                .any(|(offset, wire)| a4_end.checked_add(offset) != Some(*wire))
        {
            return Err("short DAA child nBits wires do not start at A4".into());
        }
        if original.terms.iter().any(|term| {
            term.row >= count.residual_rows
                || term.gate.left >= ORIGINAL_INPUT_LEN
                || term.gate.right >= ORIGINAL_INPUT_LEN
        }) {
            return Err("short DAA source term escapes its padded domain".into());
        }
        if !(0 < a1_end
            && a1_end <= a2_end
            && a2_end <= a3_end
            && a3_end <= a4_end
            && a4_end <= count.live_bits
            && count.live_bits <= ORIGINAL_INPUT_LEN)
        {
            return Err("short DAA phase checkpoints are not monotone".into());
        }
        let phase_spans = [
            (0, a1_end),
            (a1_end, a2_end),
            (a2_end, a3_end),
            (a3_end, count.live_bits),
        ];
        let phase_used = phase_spans.map(|(start, end)| end - start);
        let baseline = work_tree_layout::shared_baseline()
            .map_err(|error| format!("frozen work-tree owner inventory unavailable: {error}"))?;
        validate_short_banks(phase_used, &baseline.inventory.free_ranges)?;

        let mut original_to_mapped = vec![usize::MAX; ORIGINAL_INPUT_LEN];
        let mut mapped_owners = vec![false; MAPPED_INPUT_LEN];
        for ((old_start, old_end), (bank_start, bank_width)) in
            phase_spans.iter().copied().zip(PHASE_BANKS)
        {
            for old_wire in old_start..old_end {
                let mapped = bank_start + old_wire - old_start;
                if mapped >= bank_start + bank_width || mapped_owners[mapped] {
                    return Err("short DAA live map collision or bank overflow".into());
                }
                original_to_mapped[old_wire] = mapped;
                mapped_owners[mapped] = true;
            }
        }
        let mut free_cells = Vec::with_capacity(BANK_SLACK_ROWS + count.padding_bits);
        for (bank_start, bank_width) in PHASE_BANKS {
            for mapped in bank_start..bank_start + bank_width {
                if !mapped_owners[mapped] {
                    free_cells.push(mapped);
                }
            }
        }
        free_cells.sort_unstable();
        if free_cells.len() != BANK_SLACK_ROWS + count.padding_bits {
            return Err("short DAA free-bank capacity changed".into());
        }
        for (offset, old_wire) in (count.live_bits..ORIGINAL_INPUT_LEN).enumerate() {
            let mapped = free_cells[offset];
            original_to_mapped[old_wire] = mapped;
            mapped_owners[mapped] = true;
        }
        if original_to_mapped.iter().any(|wire| *wire == usize::MAX) {
            return Err("short DAA map leaves a source coordinate unmapped".into());
        }
        let slack_wires = free_cells[count.padding_bits..].to_vec();
        if slack_wires.len() != BANK_SLACK_ROWS
            || slack_wires.iter().any(|wire| mapped_owners[*wire])
        {
            return Err("short DAA slack map is not disjoint".into());
        }
        let map_wire = |wire: usize| -> Result<usize, String> {
            original_to_mapped
                .get(wire)
                .copied()
                .filter(|mapped| *mapped != usize::MAX)
                .ok_or_else(|| "short DAA source wire is outside the map".into())
        };
        let mut terms = Vec::with_capacity(original.terms.len() + BANK_SLACK_ROWS);
        for term in &original.terms {
            let mut gate = term.gate.clone();
            gate.left = map_wire(gate.left)?;
            gate.right = map_wire(gate.right)?;
            terms.push(Term {
                row: term.row,
                gate,
            });
        }
        for (offset, wire) in slack_wires.iter().copied().enumerate() {
            terms.push(Term {
                row: count.residual_rows + offset,
                gate: Gate {
                    left: wire,
                    right: 0,
                    c0: Fr::zero(),
                    c1: Fr::from(1u64),
                    c2: Fr::zero(),
                    c3: Fr::zero(),
                },
            });
        }
        let mut witness = vec![Fr::zero(); MAPPED_INPUT_LEN];
        for (old_wire, mapped_wire) in original_to_mapped.iter().copied().enumerate() {
            if old_wire >= count.live_bits && !window.witness[old_wire].is_zero() {
                return Err("short DAA native padding witness is nonzero".into());
            }
            witness[mapped_wire] = window.witness[old_wire];
        }
        if slack_wires.iter().any(|wire| !witness[*wire].is_zero()) {
            return Err("short DAA slack witness is nonzero".into());
        }
        let circuit = Circuit {
            input_len: MAPPED_INPUT_LEN,
            row_count: original.row_count,
            terms,
        };
        if circuit.terms.len() != original.terms.len() + BANK_SLACK_ROWS {
            return Err("short DAA term count changed".into());
        }
        Ok(Self {
            circuit,
            witness,
            original_to_mapped,
            phase_spans,
            phase_used,
            a4_live_end: a4_end,
            slack_wires,
        })
    }

    pub(crate) fn circuit(&self) -> &Circuit {
        &self.circuit
    }

    pub(crate) fn witness(&self) -> &[Fr] {
        &self.witness
    }

    pub(crate) fn mapped_wire(&self, original_wire: usize) -> Result<usize, String> {
        self.original_to_mapped
            .get(original_wire)
            .copied()
            .filter(|wire| *wire != usize::MAX)
            .ok_or_else(|| "DAA source wire is outside the owned map".into())
    }

    /// Identity of every owned coordinate, phase, residual term and slack gate.
    /// The consumer obtains its expected identity from its own native template.
    pub(crate) fn map_identity(&self) -> [u8; 32] {
        use blake2::{digest::consts::U32, Blake2b, Digest};
        let mut hash = Blake2b::<U32>::new();
        hash.update(b"short-daa-live-banks-global-padding-map-v1");
        for value in [
            self.circuit.input_len,
            self.circuit.row_count,
            self.a4_live_end,
        ] {
            hash.update((value as u64).to_le_bytes());
        }
        for (start, end) in self.phase_spans {
            hash.update((start as u64).to_le_bytes());
            hash.update((end as u64).to_le_bytes());
        }
        for entries in [
            &self.original_to_mapped[..],
            &self.phase_used[..],
            &self.slack_wires[..],
        ] {
            hash.update((entries.len() as u64).to_le_bytes());
            for value in entries {
                hash.update((*value as u64).to_le_bytes());
            }
        }
        hash.update((self.circuit.terms.len() as u64).to_le_bytes());
        hash.update(work_tree_layout::hash_terms(&self.circuit.terms).as_bytes());
        hash.finalize().into()
    }

    #[cfg(test)]
    pub(crate) fn phase_spans(&self) -> [(usize, usize); 4] {
        self.phase_spans
    }

    #[cfg(test)]
    pub(crate) fn phase_used(&self) -> [usize; 4] {
        self.phase_used
    }

    #[cfg(test)]
    pub(crate) fn a4_live_end(&self) -> usize {
        self.a4_live_end
    }

    #[cfg(test)]
    pub(crate) fn slack_wires(&self) -> &[usize] {
        &self.slack_wires
    }

    #[cfg(test)]
    pub(crate) fn phase_slack_ranges(&self) -> [(usize, usize); 4] {
        std::array::from_fn(|phase| {
            let (start, width) = PHASE_BANKS[phase];
            (start + self.phase_used[phase], start + width)
        })
    }

    pub(crate) fn phase_bank_ranges(&self) -> [(usize, usize); 4] {
        PHASE_BANKS.map(|(start, width)| (start, start + width))
    }

    /// Consume a diagnostic mapped witness while preserving only the fixed
    /// circuit and immutable source-to-bank map for history coefficients.
    pub(crate) fn into_history_parts(self) -> (Circuit, Vec<usize>, [(usize, usize); 4]) {
        let banks = self.phase_bank_ranges();
        (self.circuit, self.original_to_mapped, banks)
    }
}

fn validate_banks(phase_used: [usize; 4], free_ranges: &[(usize, usize)]) -> Result<(), String> {
    let mut total_slack = 0usize;
    for (phase, ((start, width), used)) in PHASE_BANKS.into_iter().zip(phase_used).enumerate() {
        let end = start.checked_add(width).ok_or("DAA bank range overflow")?;
        if end > MAPPED_INPUT_LEN || used > width {
            return Err(format!("DAA phase {phase} escapes its fixed input bank"));
        }
        if !free_ranges
            .iter()
            .any(|(free_start, free_end)| start >= *free_start && end <= *free_end)
        {
            return Err(format!(
                "complete DAA phase {phase} bank is not inside a frozen baseline free range"
            ));
        }
        total_slack = total_slack
            .checked_add(width - used)
            .ok_or("DAA bank slack overflow")?;
        for (other_start, other_width) in PHASE_BANKS.iter().take(phase) {
            let other_end = *other_start + *other_width;
            if start < other_end && *other_start < end {
                return Err("fixed DAA phase banks overlap".into());
            }
        }
    }
    if total_slack != BANK_SLACK_ROWS {
        return Err("fixed phase-bank slack total changed".into());
    }
    Ok(())
}

fn validate_short_banks(
    phase_used: [usize; 4],
    free_ranges: &[(usize, usize)],
) -> Result<(), String> {
    for (phase, ((start, width), used)) in PHASE_BANKS.into_iter().zip(phase_used).enumerate() {
        let end = start.checked_add(width).ok_or("DAA bank range overflow")?;
        if end > MAPPED_INPUT_LEN || used > width {
            return Err(format!(
                "short DAA phase {phase} escapes its fixed input bank"
            ));
        }
        if !free_ranges
            .iter()
            .any(|(free_start, free_end)| start >= *free_start && end <= *free_end)
        {
            return Err(format!(
                "short DAA phase {phase} bank is not inside a frozen baseline free range"
            ));
        }
        for (other_start, other_width) in PHASE_BANKS.iter().take(phase) {
            let other_end = *other_start + *other_width;
            if start < other_end && *other_start < end {
                return Err("short DAA phase banks overlap".into());
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod short_ledger_tests {
    use super::*;
    use crate::daa_integer::{ShortLegacyProfile, TwoRatioInputs};
    use ark_ff::One;

    fn measure(name: &str, compiled: CompiledFinish) -> bool {
        let window = &compiled.joined.joined.joined;
        let count = &window.count;
        let circuit = window.circuit.as_ref().unwrap();
        let a2 = &compiled.joined.joined.increment;
        let a3 = &compiled.joined.increment;
        let a4 = &compiled.increment;
        assert_eq!(a2.after, a3.before);
        assert_eq!(a3.after, a4.before);
        let ends = [
            a2.before.live_bits,
            a2.after.live_bits,
            a3.after.live_bits,
            count.live_bits,
        ];
        assert!(ends.windows(2).all(|pair| pair[0] <= pair[1]));
        let live_widths = [
            ends[0],
            ends[1] - ends[0],
            ends[2] - ends[1],
            ends[3] - ends[2],
        ];
        let child = compiled.child_nbits.as_ref().expect("child nBits required");
        assert_eq!(
            child.as_slice(),
            (a4.after.live_bits..a4.after.live_bits + 32).collect::<Vec<_>>()
        );
        assert!(a4.after.live_bits + 32 <= count.live_bits);
        assert_eq!(circuit.input_len, ORIGINAL_INPUT_LEN);
        assert_eq!(count.padded_input_bits, ORIGINAL_INPUT_LEN);
        assert_eq!(circuit.row_count, count.padded_rows);
        assert_eq!(circuit.terms.len(), count.terms);
        assert_eq!(count.padding_bits, ORIGINAL_INPUT_LEN - count.live_bits);
        assert!(crate::daa_finish::finish_residuals(&compiled)
            .unwrap()
            .iter()
            .all(Zero::is_zero));
        assert!(circuit
            .terms
            .iter()
            .all(|term| term.row < count.residual_rows
                && term.gate.left < ORIGINAL_INPUT_LEN
                && term.gate.right < ORIGINAL_INPUT_LEN));

        let first_padding_row = count.residual_rows - count.padding_bits;
        let padding: Vec<_> = circuit
            .terms
            .iter()
            .filter(|term| term.row >= first_padding_row)
            .collect();
        assert_eq!(padding.len(), count.padding_bits);
        for (offset, term) in padding.into_iter().enumerate() {
            assert_eq!(term.row, first_padding_row + offset);
            assert_eq!(term.gate.left, count.live_bits + offset);
            assert_eq!(term.gate.right, 0);
            assert_eq!(
                [term.gate.c0, term.gate.c1, term.gate.c2, term.gate.c3],
                [Fr::zero(), Fr::one(), Fr::zero(), Fr::zero()]
            );
            assert!(window.witness[count.live_bits + offset].is_zero());
        }

        let old_error = match MappedDaaPlan::compile(&compiled) {
            Err(error) => Some(error),
            Ok(_) => None,
        };
        let old_map_rejected = old_error.is_some();
        let phase4_overflow = ORIGINAL_INPUT_LEN - ends[2] > PHASE_BANKS[3].1;
        let bank_capacity: usize = PHASE_BANKS.iter().map(|(_, width)| width).sum();
        assert_eq!(bank_capacity, 81920);
        let live_fit = live_widths
            .iter()
            .zip(PHASE_BANKS)
            .all(|(used, (_, width))| *used <= width);
        let remaining_after_live = bank_capacity.checked_sub(count.live_bits);
        let remaining_after_padding =
            remaining_after_live.and_then(|remaining| remaining.checked_sub(count.padding_bits));
        let padding_fit = remaining_after_padding == Some(BANK_SLACK_ROWS);
        let row_fit = count
            .residual_rows
            .checked_add(BANK_SLACK_ROWS)
            .is_some_and(|rows| rows <= circuit.row_count);
        let term_fit = count
            .terms
            .checked_add(BANK_SLACK_ROWS)
            .is_some_and(|terms| terms <= crate::daa_integer::MAX_MATERIAL_TERMS);
        let hex = |bytes: &[u8]| bytes.iter().map(|b| format!("{b:02x}")).collect::<String>();
        println!(
            "{}",
            serde_json::json!({
                "profile":name,"phase_ends":ends,"a4_increment_end":a4.after.live_bits,
                "child_nbits":child.to_vec(),"child_decoder_auxiliary_bits":count.live_bits-(a4.after.live_bits+32),"live_phase_widths":live_widths,
                "original_input_len":circuit.input_len,"padded_rows":circuit.row_count,
                "residual_rows":count.residual_rows,"terms":count.terms,
                "live_bits":count.live_bits,"original_padding":count.padding_bits,
                "phase_capacities":PHASE_BANKS.map(|(_,width)|width),
                "remaining_after_live":remaining_after_live,"remaining_after_padding":remaining_after_padding,
                "topology_blake2b256":hex(&count.topology_blake2b256),"old_map_rejected":old_map_rejected,
                "old_map_error":old_error,"phase4_overflow":phase4_overflow,
                "live_fit":live_fit,"padding_fit":padding_fit,"row_fit":row_fit,"term_fit":term_fit,
                "scope":"short physical-map feasibility only"
            })
        );
        old_map_rejected && phase4_overflow && live_fit && padding_fit && row_fit && term_fit
    }

    #[test]
    fn native_short_profiles_fit_live_phase_banks_and_explicit_padding_rows() {
        let q = crate::daa_count::q();
        let raws = crate::daa_two_ratio_join::fixture_raws();
        let headers: Vec<_> = raws
            .iter()
            .map(|raw| ergo_header_core::Header::decode(raw, None).unwrap())
            .collect();
        assert_eq!(
            headers.iter().map(|h| h.height).collect::<Vec<_>>(),
            [1024, 2048, 3072, 3073]
        );
        assert_eq!(headers[3].parent_id, ergo_header_core::blake2b256(&raws[2]));
        assert_eq!(headers[3].n_bits, 0x0700_a8a7);
        assert_eq!(
            [headers[1].n_bits, headers[2].n_bits],
            [0x0601_1765, 0x0613_3b15]
        );
        assert_eq!(
            [
                headers[0].timestamp,
                headers[1].timestamp,
                headers[2].timestamp
            ],
            [1_561_986_131_991, 1_561_993_105_670, 1_562_018_260_215]
        );
        let m2 = crate::daa_finish::compile_two_finish_with_child(
            &q,
            TwoRatioInputs {
                nbits: [headers[1].n_bits, headers[2].n_bits],
                timestamps: [
                    headers[0].timestamp,
                    headers[1].timestamp,
                    headers[2].timestamp,
                ],
            },
            headers[3].n_bits,
            true,
        )
        .unwrap();
        let mut failed = Vec::new();
        if !measure("M2", m2) {
            failed.push("M2");
        }
        for (profile, name, raw) in [
            (ShortLegacyProfile::M3, "M3", 0x0700_be31),
            (ShortLegacyProfile::M4, "M4", 0x0700_bd4a),
            (ShortLegacyProfile::M5, "M5", 0x0700_b138),
            (ShortLegacyProfile::M6, "M6", 0x0700_ab6f),
            (ShortLegacyProfile::M7, "M7", 0x0700_a288),
        ] {
            let input = crate::daa_integer::mainnet_short_legacy_test_inputs(profile);
            let compiled =
                crate::daa_finish::compile_short_legacy_with_child(&q, input, raw, true).unwrap();
            if !measure(name, compiled) {
                failed.push(name);
            }
        }
        assert!(failed.is_empty(), "short-map feasibility HOLD: {failed:?}");
    }

    fn residuals(circuit: &Circuit, witness: &[Fr]) -> Vec<Fr> {
        let mut rows = vec![Fr::zero(); circuit.row_count];
        for term in &circuit.terms {
            rows[term.row] += term.gate.evaluate(witness);
        }
        rows
    }

    fn assert_short_map(compiled: &CompiledFinish, expected_live: usize) {
        let window = &compiled.joined.joined.joined;
        let source = window.circuit.as_ref().unwrap();
        let mapped = MappedDaaPlan::compile_short(compiled).unwrap();
        assert_eq!(window.count.live_bits, expected_live);
        assert_eq!(mapped.phase_used.iter().sum::<usize>(), expected_live);
        assert_eq!(mapped.original_to_mapped.len(), ORIGINAL_INPUT_LEN);
        let mut seen = vec![false; MAPPED_INPUT_LEN];
        for wire in &mapped.original_to_mapped {
            assert!(*wire < MAPPED_INPUT_LEN);
            assert!(!seen[*wire], "short map collision at {wire}");
            seen[*wire] = true;
        }
        assert_eq!(mapped.slack_wires.len(), BANK_SLACK_ROWS);
        assert!(mapped.slack_wires.windows(2).all(|pair| pair[0] < pair[1]));
        assert!(mapped.slack_wires.iter().all(|wire| !seen[*wire]));
        assert_eq!(
            mapped.circuit.terms.len(),
            source.terms.len() + BANK_SLACK_ROWS
        );
        for (source_term, mapped_term) in source
            .terms
            .iter()
            .zip(mapped.circuit.terms.iter().take(source.terms.len()))
        {
            let mut expected = source_term.gate.clone();
            expected.left = mapped.original_to_mapped[expected.left];
            expected.right = mapped.original_to_mapped[expected.right];
            assert_eq!(mapped_term.row, source_term.row);
            assert_eq!(mapped_term.gate, expected);
        }
        for (offset, term) in mapped
            .circuit
            .terms
            .iter()
            .skip(source.terms.len())
            .enumerate()
        {
            assert_eq!(term.row, window.count.residual_rows + offset);
            assert_eq!(term.gate.left, mapped.slack_wires[offset]);
            assert_eq!(term.gate.right, 0);
            assert_eq!(
                [term.gate.c0, term.gate.c1, term.gate.c2, term.gate.c3],
                [Fr::zero(), Fr::one(), Fr::zero(), Fr::zero()]
            );
            assert!(mapped.witness[term.gate.left].is_zero());
        }
        let native_residuals = residuals(source, &window.witness);
        assert!(native_residuals.iter().all(Zero::is_zero));
        assert_eq!(
            native_residuals,
            residuals(&mapped.circuit, &mapped.witness)
        );
        assert!(window.witness[expected_live..].iter().all(Zero::is_zero));
    }

    #[test]
    fn short_allocator_preserves_native_terms_witness_and_mature_rejection() {
        let q = crate::daa_count::q();
        let raws = crate::daa_two_ratio_join::fixture_raws();
        let headers: Vec<_> = raws
            .iter()
            .map(|raw| ergo_header_core::Header::decode(raw, None).unwrap())
            .collect();
        let m2 = crate::daa_finish::compile_two_finish_with_child(
            &q,
            TwoRatioInputs {
                nbits: [headers[1].n_bits, headers[2].n_bits],
                timestamps: [
                    headers[0].timestamp,
                    headers[1].timestamp,
                    headers[2].timestamp,
                ],
            },
            headers[3].n_bits,
            true,
        )
        .unwrap();
        assert_short_map(&m2, 34473);
        assert!(MappedDaaPlan::compile(&m2).is_err());
        for (profile, raw, expected_live) in [
            (ShortLegacyProfile::M3, 0x0700_be31, 38955),
            (ShortLegacyProfile::M4, 0x0700_bd4a, 43402),
            (ShortLegacyProfile::M5, 0x0700_b138, 47770),
            (ShortLegacyProfile::M6, 0x0700_ab6f, 52186),
            (ShortLegacyProfile::M7, 0x0700_a288, 56530),
        ] {
            let input = crate::daa_integer::mainnet_short_legacy_test_inputs(profile);
            let compiled =
                crate::daa_finish::compile_short_legacy_with_child(&q, input, raw, true).unwrap();
            assert_short_map(&compiled, expected_live);
            assert!(MappedDaaPlan::compile(&compiled).is_err());
        }
    }

    #[test]
    fn short_mapped_identity_rejects_coordinate_and_slack_mutants() {
        use crate::short_daa_layout::{Profile, ShortDaaLayout};
        let layout = ShortDaaLayout::compile(Profile::M2, 3073, 12).unwrap();
        let raws = crate::daa_two_ratio_join::fixture_raws();
        let headers: Vec<_> = raws
            .iter()
            .map(|raw| ergo_header_core::Header::decode(raw, None).unwrap())
            .collect();
        let compiled = crate::daa_finish::compile_two_finish_with_child(
            &crate::daa_count::q(),
            TwoRatioInputs {
                nbits: [headers[1].n_bits, headers[2].n_bits],
                timestamps: [
                    headers[0].timestamp,
                    headers[1].timestamp,
                    headers[2].timestamp,
                ],
            },
            headers[3].n_bits,
            true,
        )
        .unwrap();
        let mut mapped = layout.admit(&compiled).unwrap();
        let rejected = |map: &MappedDaaPlan| {
            assert_eq!(
                layout.validate_mapped(map).err().as_deref(),
                Some("short DAA mapped identity mismatch")
            )
        };
        let live = compiled.joined.joined.joined.count.live_bits;
        for index in [0, live] {
            let old = mapped.original_to_mapped[index];
            mapped.original_to_mapped[index] = old + 1;
            rejected(&mapped);
            mapped.original_to_mapped[index] = usize::MAX;
            rejected(&mapped);
            mapped.original_to_mapped[index] = mapped.original_to_mapped[index + 1];
            rejected(&mapped);
            mapped.original_to_mapped[index] = old;
        }
        mapped.original_to_mapped.swap(live, live + 1);
        rejected(&mapped);
        mapped.original_to_mapped.swap(live, live + 1);
        let end = mapped.phase_spans[0].1;
        mapped.phase_spans[0].1 += 1;
        rejected(&mapped);
        mapped.phase_spans[0].1 = end;
        mapped.a4_live_end += 1;
        rejected(&mapped);
        mapped.a4_live_end -= 1;
        mapped.phase_used[3] += 1;
        rejected(&mapped);
        mapped.phase_used[3] -= 1;
        mapped.slack_wires.swap(0, 1);
        rejected(&mapped);
        mapped.slack_wires.swap(0, 1);
        let slack = mapped.slack_wires[0];
        mapped.slack_wires[0] = mapped.slack_wires[1];
        rejected(&mapped);
        mapped.slack_wires[0] = slack;
        let removed = mapped.slack_wires.pop().unwrap();
        rejected(&mapped);
        mapped.slack_wires.push(removed);
        let first = compiled.joined.joined.joined.count.terms;
        let term = mapped.circuit.terms[first].clone();
        for fault in 0..7 {
            let changed = &mut mapped.circuit.terms[first];
            match fault {
                0 => changed.row += 1,
                1 => changed.gate.left += 1,
                2 => changed.gate.right += 1,
                3 => changed.gate.c0 += Fr::one(),
                4 => changed.gate.c1 += Fr::one(),
                5 => changed.gate.c2 += Fr::one(),
                _ => changed.gate.c3 += Fr::one(),
            }
            rejected(&mapped);
            mapped.circuit.terms[first] = term.clone();
        }
        let last = mapped.circuit.terms.pop().unwrap();
        rejected(&mapped);
        mapped.circuit.terms.push(last.clone());
        mapped.circuit.terms.push(last);
        rejected(&mapped);
        mapped.circuit.terms.pop();
        mapped.circuit.terms.swap(first, first + 1);
        rejected(&mapped);
        mapped.circuit.terms.swap(first, first + 1);
        layout.validate_mapped(&mapped).unwrap();
        // The witness is committed separately. Mutating a slack witness does
        // not change the relation identity; its unique residual gate rejects it.
        mapped.witness[slack] = Fr::one();
        let bad = residuals(&mapped.circuit, &mapped.witness);
        let failed: Vec<_> = bad
            .iter()
            .enumerate()
            .filter_map(|(i, r)| (!r.is_zero()).then_some(i))
            .collect();
        assert_eq!(
            failed,
            vec![compiled.joined.joined.joined.count.residual_rows]
        );
        mapped.witness[slack] = Fr::zero();
        assert!(residuals(&mapped.circuit, &mapped.witness)
            .iter()
            .all(Zero::is_zero));
    }
}

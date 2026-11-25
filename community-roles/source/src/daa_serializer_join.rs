//! Code-owned join from mature native DAA windows to full header serializers.
//!
//! This diagnostic candidate reuses the complete serializer relation in A/B
//! roles, the complete native A1-A4 relation in the DAA role, and an alias
//! relation that pins source headers and every imported field. It does not
//! authenticate historical inclusion or prove history, PoW, or consensus.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use blake2::{digest::consts::U32, Blake2b, Digest};
use ergo_header_core::Header;

use crate::{
    daa_finish::{self, CompiledFinish},
    daa_header_window::{self, Action},
    gkr::{Gate, InputClaim},
    mapped_daa_plan::{MappedDaaPlan, MAPPED_INPUT_LEN, MAPPED_INPUT_LOG, ORIGINAL_INPUT_LEN},
    packed::{PackedFile, PackedFileWriter},
    serializer::{self, Compiled as CompiledSerializer, Fields},
    sparse::{self, Circuit, Term},
};

const GLOBAL_LOG: usize = 22;
const GLOBAL_LEN: usize = 1 << GLOBAL_LOG;
const SERIALIZER_LOG: usize = 17;
const SERIALIZER_LEN: usize = 1 << SERIALIZER_LOG;
const SERIALIZER_SLOTS: usize = 10;
const SERIALIZER_REGION_LEN: usize = 1 << 21;
const SERIALIZER_REGION_END: usize = SERIALIZER_SLOTS * SERIALIZER_LEN;
const GLOBAL_DAA_OFFSET: usize = SERIALIZER_REGION_LEN;
const DAA_LEN: usize = MAPPED_INPUT_LEN;
const IMPORT_COUNT: usize = 896;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Role {
    SerializerA,
    SerializerB,
    Daa,
    Aliases,
}

const ROLE_ORDER: [Role; 4] = [
    Role::SerializerA,
    Role::SerializerB,
    Role::Daa,
    Role::Aliases,
];

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RoleMetadata {
    pub role: Role,
    pub input_log: usize,
    pub row_log: usize,
    pub term_count: usize,
    pub log_copies: usize,
    pub embedding_selector: Vec<bool>,
}

/// Immutable view into one fixed mandatory relation and its common witness slice.
pub(crate) struct RoleView<'a> {
    role: Role,
    circuit: &'a Circuit,
    input: &'a [Fr],
    log_copies: usize,
    selector: &'static [bool],
}

impl<'a> RoleView<'a> {
    pub(crate) fn role(&self) -> Role {
        self.role
    }
    pub(crate) fn circuit(&self) -> &'a Circuit {
        self.circuit
    }
    pub(crate) fn input(&self) -> &'a [Fr] {
        self.input
    }
    pub(crate) fn log_copies(&self) -> usize {
        self.log_copies
    }
    pub(crate) fn selector(&self) -> &'static [bool] {
        self.selector
    }
}

/// Immutable code-owned relation metadata for a fresh verifier. It exposes no
/// witness, map, selector setter, or caller-controlled role construction.
pub(crate) struct RoleSpec<'a> {
    role: Role,
    circuit: &'a Circuit,
    log_copies: usize,
    selector: &'static [bool],
}

impl<'a> RoleSpec<'a> {
    pub(crate) fn role(&self) -> Role {
        self.role
    }
    pub(crate) fn circuit(&self) -> &'a Circuit {
        self.circuit
    }
    pub(crate) fn log_copies(&self) -> usize {
        self.log_copies
    }
    pub(crate) fn selector(&self) -> &'static [bool] {
        self.selector
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ResidualReport {
    pub serializer_a_nonzero_rows: usize,
    pub serializer_b_nonzero_rows: usize,
    pub daa_nonzero_rows: usize,
    pub alias_nonzero_rows: usize,
}

#[derive(Clone, Debug)]
struct AliasRows {
    raw: Vec<Vec<usize>>,
    lengths: Vec<Vec<usize>>,
    heights: Vec<Vec<usize>>,
    nbits: Vec<Vec<usize>>,
    timestamps: Vec<Vec<usize>>,
    x0: Vec<usize>,
    child_nbits: Vec<usize>,
}

/// All inputs are copied and decoded during construction. No caller-supplied
/// map, callback, or later header can replace these source bytes silently.
pub(crate) struct JoinPlan {
    serializer: CompiledSerializer,
    daa: CompiledFinish,
    mapped_daa: MappedDaaPlan,
    alias: Circuit,
    fields: Vec<Fields>,
    alias_rows: AliasRows,
    heights: Vec<u32>,
    raw_headers: Vec<Vec<u8>>,
    import_count: usize,
}

impl JoinPlan {
    /// Accepts only a mature Mainnet retarget already admitted by the native
    /// window selector. Carry, reset, immature, malformed, and unsupported
    /// heights retain the selector's fail-closed behavior.
    pub(crate) fn build(samples_raw: [&[u8]; 9], child_raw: &[u8]) -> Result<Self, String> {
        let selected = daa_header_window::select_window(samples_raw[8], child_raw, &samples_raw)?;
        let Action::Retarget(epoch) = selected.action() else {
            return Err("selected DAA window is not a retarget".into());
        };
        let mut fields = Vec::with_capacity(SERIALIZER_SLOTS);
        let mut heights = Vec::with_capacity(SERIALIZER_SLOTS);
        let raw_headers = samples_raw
            .iter()
            .map(|raw| raw.to_vec())
            .chain(std::iter::once(child_raw.to_vec()))
            .collect::<Vec<_>>();
        for raw in samples_raw.into_iter().chain(std::iter::once(child_raw)) {
            let header =
                Header::decode(raw, None).map_err(|error| format!("header decode: {error:?}"))?;
            heights.push(header.height);
            fields.push(Fields::from_header(&header)?);
        }
        if fields.len() != SERIALIZER_SLOTS || heights.len() != SERIALIZER_SLOTS {
            return Err("source header roster must contain nine samples and one child".into());
        }

        let serializer = serializer::build(None)?;
        if serializer.circuit.input_len != SERIALIZER_LEN
            || serializer.circuit.row_count != 1 << 18
            || serializer.circuit.terms.len() != 315_546
        {
            return Err("full serializer template geometry changed".into());
        }
        let daa = daa_finish::compile_finish_with_child(
            epoch,
            &crate::daa_count::q(),
            selected.prediction(),
            selected.child_nbits(),
            true,
        )?;
        let mapped_daa = MappedDaaPlan::compile(&daa)?;
        if mapped_daa.circuit().input_len != DAA_LEN {
            return Err("complete A1-A4 relation input width changed".into());
        }
        let (alias, alias_rows, import_count) = build_alias_circuit(
            &serializer,
            &daa,
            &mapped_daa,
            &samples_raw,
            child_raw,
            &heights,
        )?;
        if import_count != IMPORT_COUNT || alias.input_len != GLOBAL_LEN {
            return Err("alias relation import count or input width changed".into());
        }

        let plan = Self {
            serializer,
            daa,
            mapped_daa,
            alias,
            fields,
            alias_rows,
            heights,
            raw_headers,
            import_count,
        };
        plan.validate_roles()?;
        Ok(plan)
    }

    pub(crate) fn import_count(&self) -> usize {
        self.import_count
    }

    pub(crate) fn raw_headers(&self) -> &[Vec<u8>] {
        &self.raw_headers
    }

    pub(crate) fn validate_boolean_witness(witness: &[Fr]) -> Result<(), String> {
        if witness.len() != GLOBAL_LEN {
            return Err("shared witness must have exactly 2^22 fields".into());
        }
        if let Some((index, _)) = witness
            .iter()
            .enumerate()
            .find(|(_, value)| !value.is_zero() && !value.is_one())
        {
            return Err(format!("shared witness coordinate {index} is not Boolean"));
        }
        Ok(())
    }

    pub(crate) fn role_views<'a>(&'a self, witness: &'a [Fr]) -> Result<[RoleView<'a>; 4], String> {
        Self::validate_boolean_witness(witness)?;
        Ok([
            RoleView {
                role: Role::SerializerA,
                circuit: &self.serializer.circuit,
                input: &witness[..1 << 20],
                log_copies: 3,
                selector: &[false, false],
            },
            RoleView {
                role: Role::SerializerB,
                circuit: &self.serializer.circuit,
                input: &witness[8 * SERIALIZER_LEN..SERIALIZER_REGION_END],
                log_copies: 1,
                selector: &[false, false, true, false],
            },
            RoleView {
                role: Role::Daa,
                circuit: self.mapped_daa.circuit(),
                input: &witness[GLOBAL_DAA_OFFSET..GLOBAL_DAA_OFFSET + DAA_LEN],
                log_copies: 0,
                selector: &[false, true],
            },
            RoleView {
                role: Role::Aliases,
                circuit: &self.alias,
                input: witness,
                log_copies: 0,
                selector: &[],
            },
        ])
    }

    pub(crate) fn role_specs(&self) -> Result<[RoleSpec<'_>; 4], String> {
        self.validate_roles()?;
        Ok([
            RoleSpec {
                role: Role::SerializerA,
                circuit: &self.serializer.circuit,
                log_copies: 3,
                selector: &[false, false],
            },
            RoleSpec {
                role: Role::SerializerB,
                circuit: &self.serializer.circuit,
                log_copies: 1,
                selector: &[false, false, true, false],
            },
            RoleSpec {
                role: Role::Daa,
                circuit: self.mapped_daa.circuit(),
                log_copies: 0,
                selector: &[false, true],
            },
            RoleSpec {
                role: Role::Aliases,
                circuit: &self.alias,
                log_copies: 0,
                selector: &[],
            },
        ])
    }

    /// Check every coordinate before create-new packing; active values are never coerced.
    pub(crate) fn write_boolean_packed(
        path: impl AsRef<std::path::Path>,
        witness: &[Fr],
    ) -> Result<PackedFile, String> {
        Self::validate_boolean_witness(witness)?;
        let mut writer = PackedFileWriter::create_new(path, GLOBAL_LOG)?;
        let mut bytes = Vec::with_capacity(64 * 1024);
        for chunk in witness.chunks(8) {
            let mut byte = 0u8;
            for (bit, value) in chunk.iter().enumerate() {
                if value.is_one() {
                    byte |= 1 << bit;
                }
            }
            bytes.push(byte);
            if bytes.len() == bytes.capacity() {
                writer.write_bytes(&bytes)?;
                bytes.clear();
            }
        }
        if !bytes.is_empty() {
            writer.write_bytes(&bytes)?;
        }
        writer.finish()
    }

    pub(crate) fn role_metadata(&self, role: Role) -> Result<RoleMetadata, String> {
        let (input_log, row_log, term_count, log_copies, embedding_selector) = match role {
            Role::SerializerA => (
                20,
                21,
                self.serializer.circuit.terms.len(),
                3,
                vec![false, false],
            ),
            Role::SerializerB => (
                18,
                19,
                self.serializer.circuit.terms.len(),
                1,
                vec![false, false, true, false],
            ),
            Role::Daa => {
                let circuit = self.mapped_daa.circuit();
                (
                    MAPPED_INPUT_LOG,
                    log_width(circuit.row_count)?,
                    circuit.terms.len(),
                    0,
                    vec![false, true],
                )
            }
            Role::Aliases => (
                GLOBAL_LOG,
                log_width(self.alias.row_count)?,
                self.alias.terms.len(),
                0,
                vec![],
            ),
        };
        Ok(RoleMetadata {
            role,
            input_log,
            row_log,
            term_count,
            log_copies,
            embedding_selector,
        })
    }

    pub(crate) fn validate_mandatory_roster(roles: &[Role]) -> Result<(), String> {
        if roles != ROLE_ORDER {
            return Err("mandatory DAA/serializer role roster changed".into());
        }
        Ok(())
    }

    /// Embeds a local GKR claim in the fixed 2^22 plan using code-owned high
    /// coordinates. The returned point is suitable for the shared PCS domain.
    pub(crate) fn embed_point(role: Role, point: &[Fr]) -> Result<Vec<Fr>, String> {
        let selector: &[bool] = match role {
            Role::SerializerA => &[false, false],
            Role::SerializerB => &[false, false, true, false],
            Role::Daa => &[false, true],
            Role::Aliases => &[],
        };
        let local_log = GLOBAL_LOG
            .checked_sub(selector.len())
            .ok_or("selector width exceeds global log")?;
        if point.len() != local_log {
            return Err("role claim has wrong local point dimension".into());
        }
        let mut embedded = Vec::with_capacity(GLOBAL_LOG);
        embedded.extend_from_slice(point);
        embedded.extend(selector.iter().map(|bit| Fr::from(*bit as u64)));
        Self::validate_embedded_point(role, &embedded)?;
        Ok(embedded)
    }

    pub(crate) fn validate_embedded_point(role: Role, point: &[Fr]) -> Result<(), String> {
        if point.len() != GLOBAL_LOG {
            return Err("global claim point has wrong dimension".into());
        }
        let selector: &[bool] = match role {
            Role::SerializerA => &[false, false],
            Role::SerializerB => &[false, false, true, false],
            Role::Daa => &[false, true],
            Role::Aliases => &[],
        };
        let start = GLOBAL_LOG - selector.len();
        if point[start..]
            .iter()
            .zip(selector)
            .any(|(actual, expected)| *actual != Fr::from(*expected as u64))
        {
            return Err("global claim point has wrong role selector".into());
        }
        Ok(())
    }

    /// Materializes the shared 2^22 vector, including the mapped DAA block
    /// and the full-domain alias relation.
    pub(crate) fn materialize_witness(&self) -> Result<Vec<Fr>, String> {
        let mut witness = vec![Fr::zero(); GLOBAL_LEN];
        for (slot, fields) in self.fields.iter().enumerate() {
            let assigned = self.serializer.assign(fields);
            if assigned.len() != SERIALIZER_LEN {
                return Err("serializer witness width changed".into());
            }
            let start = slot
                .checked_mul(SERIALIZER_LEN)
                .ok_or("serializer slot offset overflow")?;
            let end = start
                .checked_add(SERIALIZER_LEN)
                .ok_or("serializer slot end overflow")?;
            witness[start..end].copy_from_slice(&assigned);
        }
        if daa_witness(&self.daa)?.len() != ORIGINAL_INPUT_LEN {
            return Err("DAA witness width changed".into());
        }
        let daa_end = GLOBAL_DAA_OFFSET
            .checked_add(DAA_LEN)
            .ok_or("DAA offset overflow")?;
        witness[GLOBAL_DAA_OFFSET..daa_end].copy_from_slice(self.mapped_daa.witness());
        Ok(witness)
    }

    /// Checks all four complete relations against the same supplied vector.
    /// This is a local residual consumer, not a GKR proof verifier or host
    /// header decoder. A nonzero row in any role rejects the join.
    pub(crate) fn check_residuals(&self, witness: &[Fr]) -> Result<ResidualReport, String> {
        if witness.len() != GLOBAL_LEN {
            return Err("shared witness must have exactly 2^22 fields".into());
        }
        self.validate_roles()?;
        let mut report = ResidualReport {
            serializer_a_nonzero_rows: 0,
            serializer_b_nonzero_rows: 0,
            daa_nonzero_rows: 0,
            alias_nonzero_rows: 0,
        };
        for slot in 0..8 {
            let start = slot * SERIALIZER_LEN;
            report.serializer_a_nonzero_rows += nonzero_rows(
                &self.serializer.circuit,
                &witness[start..start + SERIALIZER_LEN],
            )?;
        }
        for slot in 8..10 {
            let start = slot * SERIALIZER_LEN;
            report.serializer_b_nonzero_rows += nonzero_rows(
                &self.serializer.circuit,
                &witness[start..start + SERIALIZER_LEN],
            )?;
        }
        let daa_end = GLOBAL_DAA_OFFSET + DAA_LEN;
        report.daa_nonzero_rows = nonzero_rows(
            self.mapped_daa.circuit(),
            &witness[GLOBAL_DAA_OFFSET..daa_end],
        )?;
        report.alias_nonzero_rows = nonzero_rows(&self.alias, witness)?;
        if report.serializer_a_nonzero_rows
            + report.serializer_b_nonzero_rows
            + report.daa_nonzero_rows
            + report.alias_nonzero_rows
            != 0
        {
            return Err(format!("joined residuals are nonzero: {report:?}"));
        }
        Ok(report)
    }

    #[cfg(test)]
    fn target_rows(&self) -> &AliasRows {
        &self.alias_rows
    }

    fn validate_roles(&self) -> Result<(), String> {
        Self::validate_mandatory_roster(&ROLE_ORDER)?;
        if self.fields.len() != SERIALIZER_SLOTS || self.heights.len() != SERIALIZER_SLOTS {
            return Err("source roster length changed".into());
        }
        let a = sparse::validate(&self.serializer.circuit, 3)
            .map_err(|error| format!("role A shape: {error:?}"))?;
        let b = sparse::validate(&self.serializer.circuit, 1)
            .map_err(|error| format!("role B shape: {error:?}"))?;
        if a.input_bits + 3 != 20 || b.input_bits + 1 != 18 {
            return Err("serializer role embedding dimensions changed".into());
        }
        let d = sparse::validate(self.mapped_daa.circuit(), 0)
            .map_err(|error| format!("DAA role shape: {error:?}"))?;
        let aliases = sparse::validate(&self.alias, 0)
            .map_err(|error| format!("alias role shape: {error:?}"))?;
        if d.input_bits != MAPPED_INPUT_LOG || aliases.input_bits != GLOBAL_LOG {
            return Err("DAA or alias role embedding dimensions changed".into());
        }
        Ok(())
    }
}

fn daa_circuit(compiled: &CompiledFinish) -> Result<&Circuit, String> {
    compiled
        .joined
        .joined
        .joined
        .circuit
        .as_ref()
        .ok_or_else(|| "DAA circuit was not materialized".into())
}

fn daa_witness(compiled: &CompiledFinish) -> Result<&[Fr], String> {
    Ok(&compiled.joined.joined.joined.witness)
}

fn log_width(value: usize) -> Result<usize, String> {
    if value == 0 || !value.is_power_of_two() {
        return Err("role dimension is not a power of two".into());
    }
    Ok(value.trailing_zeros() as usize)
}

fn nonzero_rows(circuit: &Circuit, input: &[Fr]) -> Result<usize, String> {
    if input.len() != circuit.input_len {
        return Err("role input width mismatch".into());
    }
    let mut rows = vec![Fr::zero(); circuit.row_count];
    for term in &circuit.terms {
        if term.row >= rows.len() || term.gate.left >= input.len() || term.gate.right >= input.len()
        {
            return Err("role contains an out-of-range term".into());
        }
        rows[term.row] += term.gate.evaluate(input);
    }
    Ok(rows.into_iter().filter(|value| !value.is_zero()).count())
}

fn equality_term(row: usize, wire: usize, value: bool) -> Term {
    Term {
        row,
        gate: Gate {
            left: wire,
            right: 0,
            c0: -Fr::from(value as u64),
            c1: Fr::one(),
            c2: Fr::zero(),
            c3: Fr::zero(),
        },
    }
}

fn append_constant(
    _rows: &mut AliasRows,
    terms: &mut Vec<Term>,
    wire: usize,
    value: bool,
    group: &mut Vec<usize>,
) -> Result<(), String> {
    let row = terms.len();
    terms.push(equality_term(row, wire, value));
    group.push(row);
    Ok(())
}

fn append_import(terms: &mut Vec<Term>, left: usize, right: usize, group: &mut Vec<usize>) {
    let row = terms.len();
    terms.push(Term {
        row,
        gate: Gate {
            left,
            right,
            c0: Fr::zero(),
            c1: Fr::one(),
            c2: -Fr::one(),
            c3: Fr::zero(),
        },
    });
    group.push(row);
}

fn build_alias_circuit(
    serializer: &CompiledSerializer,
    daa: &CompiledFinish,
    mapped_daa: &MappedDaaPlan,
    samples_raw: &[&[u8]; 9],
    child_raw: &[u8],
    heights: &[u32],
) -> Result<(Circuit, AliasRows, usize), String> {
    if serializer.layout.bytes.len() != 514
        || serializer.layout.length.len() != 10
        || samples_raw.len() != 9
        || heights.len() != 10
    {
        return Err("alias source dimensions changed".into());
    }
    let daa_window = &daa.joined.joined.joined;
    if daa_window.external.len() != 8 {
        return Err("DAA relation must expose eight native imports".into());
    }
    let x0 = &daa.joined.output.x0_bits;
    let child_nbits = daa
        .child_nbits
        .as_ref()
        .ok_or("child nBits binding missing")?;
    if x0.len() != 32 || child_nbits.len() != 32 {
        return Err("DAA anchor width changed".into());
    }
    validate_local_maps(serializer, daa, mapped_daa, x0, child_nbits)?;

    let raws: Vec<&[u8]> = samples_raw
        .iter()
        .copied()
        .chain(std::iter::once(child_raw))
        .collect();
    let mut terms = Vec::with_capacity(44_000);
    let mut row_maps = AliasRows {
        raw: Vec::with_capacity(10),
        lengths: Vec::with_capacity(10),
        heights: Vec::with_capacity(10),
        nbits: Vec::with_capacity(8),
        timestamps: Vec::with_capacity(9),
        x0: Vec::with_capacity(32),
        child_nbits: Vec::with_capacity(32),
    };

    // Pin the complete fixed 514-byte output and encoded byte length for each
    // code-owned header. The serializer relation separately enforces padding.
    for (slot, raw) in raws.iter().enumerate() {
        if raw.is_empty() || raw.len() > 514 {
            return Err("raw header exceeds serializer cap".into());
        }
        let mut raw_rows = Vec::with_capacity(514 * 8);
        for (byte_index, bits) in serializer.layout.bytes.iter().enumerate() {
            let byte = raw.get(byte_index).copied().unwrap_or(0);
            for (bit, &wire) in bits.iter().enumerate() {
                append_constant(
                    &mut row_maps,
                    &mut terms,
                    slot * SERIALIZER_LEN + wire,
                    ((byte >> bit) & 1) != 0,
                    &mut raw_rows,
                )?;
            }
        }
        row_maps.raw.push(raw_rows);
        let mut length_rows = Vec::with_capacity(10);
        for (bit, &wire) in serializer.layout.length.iter().enumerate() {
            append_constant(
                &mut row_maps,
                &mut terms,
                slot * SERIALIZER_LEN + wire,
                ((raw.len() >> bit) & 1) != 0,
                &mut length_rows,
            )?;
        }
        row_maps.lengths.push(length_rows);
        let mut height_rows = Vec::with_capacity(32);
        for (bit, &wire) in serializer.layout.fields.height.iter().enumerate() {
            append_constant(
                &mut row_maps,
                &mut terms,
                slot * SERIALIZER_LEN + wire,
                ((heights[slot] >> bit) & 1) != 0,
                &mut height_rows,
            )?;
        }
        row_maps.heights.push(height_rows);
    }

    // Eight nBits values import sample[1..=8]; nine timestamp values import
    // sample[0..=8]. Source maps are derived from the compiled relations.
    for index in 0..8 {
        let mut rows = Vec::with_capacity(32);
        let sample_nbits = &serializer.layout.fields.n_bits;
        for bit in 0..32 {
            append_import(
                &mut terms,
                GLOBAL_DAA_OFFSET
                    + mapped_daa.mapped_wire(daa_window.external[index].nbits[bit])?,
                (index + 1) * SERIALIZER_LEN + sample_nbits[bit],
                &mut rows,
            );
        }
        row_maps.nbits.push(rows);
    }
    for index in 0..9 {
        let wires: &[usize] = if index == 8 {
            &daa_window.external[7].end_timestamp
        } else {
            &daa_window.external[index].start_timestamp
        };
        let mut rows = Vec::with_capacity(64);
        for bit in 0..64 {
            append_import(
                &mut terms,
                GLOBAL_DAA_OFFSET + mapped_daa.mapped_wire(wires[bit])?,
                index * SERIALIZER_LEN + serializer.layout.fields.timestamp[bit],
                &mut rows,
            );
        }
        row_maps.timestamps.push(rows);
    }
    let mut x0_rows = Vec::with_capacity(32);
    for bit in 0..32 {
        append_import(
            &mut terms,
            GLOBAL_DAA_OFFSET + mapped_daa.mapped_wire(x0[bit])?,
            SERIALIZER_LEN + serializer.layout.fields.height[bit],
            &mut x0_rows,
        );
    }
    row_maps.x0 = x0_rows;
    let mut child_rows = Vec::with_capacity(32);
    for bit in 0..32 {
        append_import(
            &mut terms,
            GLOBAL_DAA_OFFSET + mapped_daa.mapped_wire(child_nbits[bit])?,
            9 * SERIALIZER_LEN + serializer.layout.fields.n_bits[bit],
            &mut child_rows,
        );
    }
    row_maps.child_nbits = child_rows;

    let rows = terms.len();
    if rows > 1 << 20 {
        return Err("alias relation exceeds sparse base-term cap".into());
    }
    let row_count = rows
        .checked_next_power_of_two()
        .ok_or("alias row count overflow")?;
    if row_count > 1 << 24 {
        return Err("alias relation exceeds sparse row cap".into());
    }
    let circuit = Circuit {
        input_len: GLOBAL_LEN,
        row_count,
        terms,
    };
    Ok((circuit, row_maps, IMPORT_COUNT))
}

fn validate_local_maps(
    serializer: &CompiledSerializer,
    daa: &CompiledFinish,
    mapped_daa: &MappedDaaPlan,
    x0: &[usize],
    child_nbits: &[usize],
) -> Result<(), String> {
    for bits in &serializer.layout.bytes {
        validate_wire_indices("serializer byte", bits, SERIALIZER_LEN)?;
    }
    validate_wire_indices(
        "serializer length",
        &serializer.layout.length,
        SERIALIZER_LEN,
    )?;
    validate_wire_indices(
        "serializer height",
        &serializer.layout.fields.height,
        SERIALIZER_LEN,
    )?;
    validate_wire_indices(
        "serializer timestamp",
        &serializer.layout.fields.timestamp,
        SERIALIZER_LEN,
    )?;
    validate_wire_indices(
        "serializer nBits",
        &serializer.layout.fields.n_bits,
        SERIALIZER_LEN,
    )?;
    validate_wire_indices("DAA x0", x0, ORIGINAL_INPUT_LEN)?;
    validate_wire_indices("DAA child nBits", child_nbits, ORIGINAL_INPUT_LEN)?;
    let external = &daa.joined.joined.joined.external;
    if external.len() != 8 {
        return Err("DAA external map count changed".into());
    }
    for entry in external {
        validate_wire_indices("DAA nBits", &entry.nbits, ORIGINAL_INPUT_LEN)?;
        validate_wire_indices(
            "DAA start timestamp",
            &entry.start_timestamp,
            ORIGINAL_INPUT_LEN,
        )?;
        validate_wire_indices(
            "DAA end timestamp",
            &entry.end_timestamp,
            ORIGINAL_INPUT_LEN,
        )?;
        for wire in entry
            .nbits
            .iter()
            .chain(&entry.start_timestamp)
            .chain(&entry.end_timestamp)
        {
            if GLOBAL_DAA_OFFSET + mapped_daa.mapped_wire(*wire)? >= GLOBAL_LEN {
                return Err("mapped DAA import escapes the common input".into());
            }
        }
    }
    for wire in x0.iter().chain(child_nbits) {
        if GLOBAL_DAA_OFFSET + mapped_daa.mapped_wire(*wire)? >= GLOBAL_LEN {
            return Err("mapped DAA anchor escapes the common input".into());
        }
    }
    timestamp_maps_shared(external)
}

fn validate_wire_indices(label: &str, wires: &[usize], limit: usize) -> Result<(), String> {
    if wires.iter().any(|wire| *wire >= limit) {
        return Err(format!("{label} map escapes its local input"));
    }
    Ok(())
}

fn timestamp_maps_shared(external: &[crate::daa_integer::ExternalBits]) -> Result<(), String> {
    if external.len() != 8 {
        return Err("DAA external map count changed".into());
    }
    for pair in external.windows(2) {
        if pair[0].end_timestamp != pair[1].start_timestamp {
            return Err("DAA adjacent timestamp maps are not shared".into());
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::work_tree_layout;
    use ark_ff::One;
    use serde::Deserialize;
    use std::collections::HashMap;

    const FIXTURE: &str = include_str!("../fixtures/mainnet-daa-windows-v1.json");

    #[derive(Deserialize)]
    struct Fixture {
        cases: Vec<Case>,
        headers: Vec<FixtureHeader>,
    }
    #[derive(Deserialize)]
    struct Case {
        child: u32,
        parent: u32,
        samples: Vec<u32>,
    }
    #[derive(Deserialize)]
    struct FixtureHeader {
        height: u32,
        raw_hex: String,
    }

    fn fixture() -> (Fixture, HashMap<u32, Vec<u8>>) {
        let fixture: Fixture = serde_json::from_str(FIXTURE).unwrap();
        let mut headers = HashMap::new();
        for entry in &fixture.headers {
            let raw = entry
                .raw_hex
                .as_bytes()
                .chunks_exact(2)
                .map(|pair| u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).unwrap())
                .collect::<Vec<_>>();
            assert_eq!(Header::decode(&raw, None).unwrap().height, entry.height);
            assert!(headers.insert(entry.height, raw).is_none());
        }
        (fixture, headers)
    }

    fn plan_for(child: u32) -> JoinPlan {
        let (fixture, headers) = fixture();
        let case = fixture
            .cases
            .iter()
            .find(|case| case.child == child)
            .unwrap();
        assert_eq!(case.parent + 1, child);
        let samples: Vec<&[u8]> = case
            .samples
            .iter()
            .map(|height| headers.get(height).unwrap().as_slice())
            .collect();
        let samples: [&[u8]; 9] = samples.try_into().unwrap();
        JoinPlan::build(samples, headers.get(&child).unwrap()).unwrap()
    }

    fn role_nonzero(plan: &JoinPlan, circuit: &Circuit, witness: &[Fr]) -> usize {
        nonzero_rows(circuit, witness).unwrap()
    }

    fn mapping_error(compiled: &CompiledFinish) -> String {
        match MappedDaaPlan::compile(compiled) {
            Ok(_) => panic!("malformed DAA plan was admitted"),
            Err(error) => error,
        }
    }

    fn assert_mapped_alias_endpoint(plan: &JoinPlan, row: usize, original_wire: usize) {
        let term = plan
            .alias
            .terms
            .iter()
            .find(|term| term.row == row)
            .unwrap();
        assert_eq!(
            term.gate.left,
            GLOBAL_DAA_OFFSET + plan.mapped_daa.mapped_wire(original_wire).unwrap()
        );
    }

    #[test]
    fn three_native_windows_satisfy_all_four_complete_roles_and_embeddings() {
        for child in [9_217, 844_673, 844_801] {
            let plan = plan_for(child);
            assert_eq!(plan.import_count(), IMPORT_COUNT);
            let witness = plan.materialize_witness().unwrap();
            let report = plan.check_residuals(&witness).unwrap();
            assert_eq!(
                report,
                ResidualReport {
                    serializer_a_nonzero_rows: 0,
                    serializer_b_nonzero_rows: 0,
                    daa_nonzero_rows: 0,
                    alias_nonzero_rows: 0
                }
            );
            let original_daa = daa_circuit(&plan.daa).unwrap();
            let mapped_daa = plan.mapped_daa.circuit();
            let frozen_owners = work_tree_layout::shared_baseline().unwrap();
            for (phase, (start, end)) in plan.mapped_daa.phase_bank_ranges().into_iter().enumerate()
            {
                assert!(
                    frozen_owners
                        .inventory
                        .free_ranges
                        .iter()
                        .any(|(free_start, free_end)| start >= *free_start && end <= *free_end),
                    "phase {phase} bank is not wholly in a frozen free range"
                );
            }
            assert_eq!(plan.mapped_daa.phase_spans()[3].1, ORIGINAL_INPUT_LEN);
            assert!(plan.mapped_daa.a4_live_end() <= ORIGINAL_INPUT_LEN);
            assert_eq!(
                mapped_daa.terms.len(),
                original_daa.terms.len() + crate::mapped_daa_plan::BANK_SLACK_ROWS
            );
            let mut owned = vec![false; MAPPED_INPUT_LEN];
            for old_wire in 0..ORIGINAL_INPUT_LEN {
                let mapped_wire = plan.mapped_daa.mapped_wire(old_wire).unwrap();
                assert!(
                    !owned[mapped_wire],
                    "duplicate mapped DAA wire {mapped_wire}"
                );
                owned[mapped_wire] = true;
                assert_eq!(
                    plan.mapped_daa.witness()[mapped_wire],
                    daa_witness(&plan.daa).unwrap()[old_wire]
                );
            }
            for (old, mapped) in original_daa.terms.iter().zip(mapped_daa.terms.iter()) {
                let mut expected = old.gate.clone();
                expected.left = plan.mapped_daa.mapped_wire(expected.left).unwrap();
                expected.right = plan.mapped_daa.mapped_wire(expected.right).unwrap();
                assert_eq!(mapped.row, old.row);
                assert_eq!(mapped.gate, expected);
            }
            let slack = plan.mapped_daa.slack_wires();
            assert_eq!(slack.len(), crate::mapped_daa_plan::BANK_SLACK_ROWS);
            assert!(slack
                .iter()
                .all(|wire| plan.mapped_daa.witness()[*wire].is_zero()));
            let mut slack_offset = 0usize;
            for (phase, (start, end)) in
                plan.mapped_daa.phase_slack_ranges().into_iter().enumerate()
            {
                if start < end {
                    let wire = start;
                    let slack_term = &mapped_daa.terms[original_daa.terms.len() + slack_offset];
                    assert_eq!(slack_term.gate.left, wire);
                    assert_eq!(plan.mapped_daa.witness()[wire], Fr::zero());
                    let mut bad_slack = plan.mapped_daa.witness().to_vec();
                    bad_slack[wire] = Fr::one();
                    let slack_rows = residual_vector(mapped_daa, &bad_slack).unwrap();
                    assert!(
                        !slack_rows[slack_term.row].is_zero(),
                        "phase {phase} slack mutant"
                    );
                }
                slack_offset += end - start;
            }
            assert_eq!(slack_offset, crate::mapped_daa_plan::BANK_SLACK_ROWS);

            let original_witness = daa_witness(&plan.daa).unwrap();
            let original_base = residual_vector(original_daa, original_witness).unwrap();
            let mapped_base = residual_vector(mapped_daa, plan.mapped_daa.witness()).unwrap();
            let compared_rows = plan.daa.joined.joined.joined.count.residual_rows;
            assert_eq!(
                &mapped_base[..compared_rows],
                &original_base[..compared_rows]
            );
            let boundaries = [
                0,
                plan.mapped_daa.phase_spans()[0].1,
                plan.mapped_daa.phase_spans()[1].1,
                plan.mapped_daa.phase_spans()[2].1,
                plan.daa.joined.joined.joined.count.live_bits,
            ];
            for (boundary_index, old_wire) in boundaries.into_iter().enumerate() {
                assert!(old_wire < ORIGINAL_INPUT_LEN);
                let mut original_changed = original_witness.to_vec();
                let old_value = original_changed[old_wire];
                assert!(old_value.is_zero() || old_value.is_one());
                if boundary_index == 4 {
                    assert!(
                        old_value.is_zero(),
                        "first original padding wire must start at zero"
                    );
                }
                original_changed[old_wire] = if old_value.is_zero() {
                    Fr::one()
                } else {
                    Fr::zero()
                };
                let mut mapped_changed = plan.mapped_daa.witness().to_vec();
                let mapped_wire = plan.mapped_daa.mapped_wire(old_wire).unwrap();
                mapped_changed[mapped_wire] = original_changed[old_wire];
                let original_rows = residual_vector(original_daa, &original_changed).unwrap();
                let mapped_rows = residual_vector(mapped_daa, &mapped_changed).unwrap();
                assert_eq!(
                    &mapped_rows[..compared_rows],
                    &original_rows[..compared_rows],
                    "original/mapped residual differential at wire {old_wire}"
                );
                let changed_rows = original_rows[..compared_rows]
                    .iter()
                    .zip(&original_base[..compared_rows])
                    .enumerate()
                    .filter_map(|(row, (changed, base))| (changed != base).then_some(row))
                    .collect::<Vec<_>>();
                let touched_rows = original_daa
                    .terms
                    .iter()
                    .filter(|term| term.gate.left == old_wire || term.gate.right == old_wire)
                    .map(|term| term.row)
                    .collect::<Vec<_>>();
                assert!(changed_rows.iter().all(|row| touched_rows.contains(row)));
                if boundary_index < 4 {
                    assert!(
                        !changed_rows.is_empty(),
                        "live boundary wire {old_wire} should alter its owned rows"
                    );
                } else {
                    assert!(
                        !touched_rows.is_empty(),
                        "first padding wire must be constrained by the original circuit"
                    );
                    assert!(
                        !changed_rows.is_empty(),
                        "first padding wire mutation must change the original residual"
                    );
                }
            }
            for (role, expected) in [
                (Role::SerializerA, 20),
                (Role::SerializerB, 18),
                (Role::Daa, 20),
                (Role::Aliases, 22),
            ] {
                let metadata = plan.role_metadata(role).unwrap();
                assert_eq!(metadata.input_log, expected);
                assert_eq!(
                    metadata.input_log + metadata.embedding_selector.len(),
                    GLOBAL_LOG
                );
                assert_eq!(metadata.term_count > 0, true);
                let point = vec![Fr::from(2u64); expected];
                let embedded = JoinPlan::embed_point(role, &point).unwrap();
                JoinPlan::validate_embedded_point(role, &embedded).unwrap();
                let mut wrong = embedded;
                if !metadata.embedding_selector.is_empty() {
                    *wrong.last_mut().unwrap() = Fr::one();
                }
                if plan.role_metadata(role).unwrap().embedding_selector.last() == Some(&false) {
                    assert!(JoinPlan::validate_embedded_point(role, &wrong).is_err());
                }
            }
            let views = plan.role_views(&witness).unwrap();
            for (view, expected_log) in views.iter().zip([20, 18, 20, 22]) {
                assert_eq!(
                    view.input().len(),
                    view.circuit().input_len * (1usize << view.log_copies())
                );
                assert_eq!(view.input().len(), 1usize << expected_log);
            }
            assert_eq!(
                views[1].input(),
                &witness[8 * SERIALIZER_LEN..SERIALIZER_REGION_END],
                "B must be exactly serializer slots 8 and 9"
            );
            assert_eq!(
                views[2].input(),
                &witness[GLOBAL_DAA_OFFSET..GLOBAL_DAA_OFFSET + DAA_LEN]
            );
            assert_eq!(views[3].input(), witness);

            let external = &plan.daa.joined.joined.joined.external;
            for sample in 0..8 {
                for bit in 0..32 {
                    assert_mapped_alias_endpoint(
                        &plan,
                        plan.alias_rows.nbits[sample][bit],
                        external[sample].nbits[bit],
                    );
                }
            }
            for sample in 0..9 {
                for bit in 0..64 {
                    let original_wire = if sample == 0 {
                        external[0].start_timestamp[bit]
                    } else {
                        external[sample - 1].end_timestamp[bit]
                    };
                    assert_mapped_alias_endpoint(
                        &plan,
                        plan.alias_rows.timestamps[sample][bit],
                        original_wire,
                    );
                }
            }
            for bit in 0..32 {
                assert_mapped_alias_endpoint(
                    &plan,
                    plan.alias_rows.x0[bit],
                    plan.daa.joined.output.x0_bits[bit],
                );
                assert_mapped_alias_endpoint(
                    &plan,
                    plan.alias_rows.child_nbits[bit],
                    plan.daa.child_nbits.as_ref().unwrap()[bit],
                );
            }
        }
    }

    #[test]
    fn isolated_import_and_public_anchor_rows_fail_on_their_own_mutation() {
        let plan = plan_for(844_801);
        let witness = plan.materialize_witness().unwrap();
        let maps = plan.target_rows();
        let cases = [
            maps.nbits[0][0],
            maps.timestamps[0][0],
            maps.x0[0],
            maps.child_nbits[0],
            maps.heights[3][0],
            maps.heights[9][0],
            maps.lengths[0][0],
            maps.raw[2][8],
        ];
        for target in cases {
            let term = plan
                .alias
                .terms
                .iter()
                .find(|term| term.row == target)
                .unwrap();
            let mut changed = witness.clone();
            changed[term.gate.left] = Fr::one() - changed[term.gate.left];
            let rows = residual_vector(&plan.alias, &changed).unwrap();
            assert!(!rows[target].is_zero(), "target row {target}");
            let failed: Vec<usize> = rows
                .iter()
                .enumerate()
                .filter_map(|(row, value)| (!value.is_zero()).then_some(row))
                .collect();
            let shared_wire_rows: Vec<usize> = plan
                .alias
                .terms
                .iter()
                .filter(|candidate| candidate.gate.left == term.gate.left)
                .map(|candidate| candidate.row)
                .collect();
            assert_eq!(failed, shared_wire_rows);
        }
    }

    fn residual_vector(circuit: &Circuit, input: &[Fr]) -> Result<Vec<Fr>, String> {
        if input.len() != circuit.input_len {
            return Err("test role width".into());
        }
        let mut rows = vec![Fr::zero(); circuit.row_count];
        for term in &circuit.terms {
            rows[term.row] += term.gate.evaluate(input);
        }
        Ok(rows)
    }

    #[test]
    fn mandatory_roster_and_top_selector_fail_closed() {
        assert!(JoinPlan::validate_mandatory_roster(&ROLE_ORDER).is_ok());
        assert!(JoinPlan::validate_mandatory_roster(&ROLE_ORDER[..3]).is_err());
        assert!(JoinPlan::validate_mandatory_roster(&[
            Role::SerializerA,
            Role::SerializerA,
            Role::Daa,
            Role::Aliases
        ])
        .is_err());
        let alias_point = vec![Fr::from(3u64); GLOBAL_LOG];
        let embedded = JoinPlan::embed_point(Role::Aliases, &alias_point).unwrap();
        assert_eq!(embedded, alias_point);
        let mut wrong_top = embedded;
        wrong_top[21] = Fr::one();
        assert!(JoinPlan::validate_embedded_point(Role::Aliases, &wrong_top).is_ok());
        assert!(JoinPlan::embed_point(Role::SerializerB, &alias_point).is_err());
        for (role, local_log, selector) in [
            (Role::SerializerA, 20, &[false, false][..]),
            (Role::SerializerB, 18, &[false, false, true, false][..]),
            (Role::Daa, 20, &[false, true][..]),
            (Role::Aliases, 22, &[][..]),
        ] {
            let point = JoinPlan::embed_point(role, &vec![Fr::from(3u64); local_log]).unwrap();
            let selector_start = GLOBAL_LOG - selector.len();
            for (offset, bit) in selector.iter().enumerate() {
                let mut changed = point.clone();
                changed[selector_start + offset] = Fr::from((!*bit) as u64);
                assert!(JoinPlan::validate_embedded_point(role, &changed).is_err());
            }
        }
    }

    #[test]
    fn local_map_overflow_and_unshared_timestamp_maps_fail_closed() {
        assert!(validate_wire_indices("test map", &[SERIALIZER_LEN - 1], SERIALIZER_LEN).is_ok());
        assert!(validate_wire_indices("test map", &[SERIALIZER_LEN], SERIALIZER_LEN).is_err());
        let plan = plan_for(9_217);
        let mut external = plan.daa.joined.joined.joined.external.clone();
        external[1].start_timestamp[0] += ORIGINAL_INPUT_LEN;
        assert!(timestamp_maps_shared(&external).is_err());
    }

    #[test]
    fn immutable_mapping_rejects_checkpoint_count_and_capacity_mutants() {
        let mut bad_a3 = plan_for(844_801);
        bad_a3.daa.joined.increment.before.live_bits += 1;
        let error = mapping_error(&bad_a3.daa);
        assert!(error.contains("A2/A3 checkpoint continuity"), "{error}");

        let mut bad_a4 = plan_for(844_801);
        bad_a4.daa.increment.before.live_bits += 1;
        let error = mapping_error(&bad_a4.daa);
        assert!(error.contains("A3/A4 checkpoint continuity"), "{error}");

        let mut bad_count = plan_for(844_801);
        bad_count.daa.joined.joined.joined.count.live_bits += 1;
        let error = mapping_error(&bad_count.daa);
        assert!(error.contains("final count, padding"), "{error}");

        let mut bad_child_map = plan_for(844_801);
        bad_child_map.daa.child_nbits.as_mut().unwrap()[0] += 1;
        let error = mapping_error(&bad_child_map.daa);
        assert!(error.contains("child nBits wires do not start"), "{error}");

        let mut over_capacity = plan_for(844_801);
        let final_live = over_capacity.daa.increment.after.live_bits;
        assert!(
            final_live > 32_771,
            "fixture must span enough input for capacity mutant"
        );
        let a2_after = {
            let a2 = &mut over_capacity.daa.joined.joined.increment;
            a2.before.live_bits = 32_769;
            a2.after.live_bits = 32_770;
            a2.after
        };
        let a3_after = {
            let a3 = &mut over_capacity.daa.joined.increment;
            a3.before = a2_after;
            a3.after.live_bits = final_live - 1;
            a3.after
        };
        over_capacity.daa.increment.before = a3_after;
        let error = mapping_error(&over_capacity.daa);
        assert!(
            error.contains("DAA phase 0 escapes its fixed input bank"),
            "{error}"
        );
    }

    #[test]
    fn recomputed_serializer_cannot_replace_code_owned_raw_anchor() {
        let plan = plan_for(9_217);
        let witness = plan.materialize_witness().unwrap();
        let mut changed_fields = plan.fields[0].clone();
        changed_fields.parent_id[0] ^= 1;
        let assigned = plan.serializer.assign(&changed_fields);
        assert_eq!(
            nonzero_rows(&plan.serializer.circuit, &assigned).unwrap(),
            0
        );
        let mut changed = witness;
        changed[..SERIALIZER_LEN].copy_from_slice(&assigned);
        // The full serializer still accepts its recomputed witness; the alias
        // consumer rejects the first changed public raw byte anchor.
        assert_eq!(
            role_nonzero(&plan, &plan.serializer.circuit, &changed[..SERIALIZER_LEN]),
            0
        );
        let alias_rows = residual_vector(&plan.alias, &changed).unwrap();
        let target = plan.alias_rows.raw[0][8 * 1];
        assert!(!alias_rows[target].is_zero());
        assert!(plan.check_residuals(&changed).is_err());
    }

    #[test]
    fn coordinated_timestamp_change_passes_daa_but_fails_serializer_imports() {
        let original = plan_for(844_801);
        let original_witness = original.materialize_witness().unwrap();
        let (fixture, headers) = fixture();
        let case = fixture
            .cases
            .iter()
            .find(|case| case.child == 844_801)
            .unwrap();
        let mut shifted_samples = case
            .samples
            .iter()
            .map(|height| {
                let mut header = Header::decode(headers.get(height).unwrap(), None).unwrap();
                header.timestamp = header.timestamp.checked_add(1).unwrap();
                header.encode().unwrap()
            })
            .collect::<Vec<_>>();
        let mut child = Header::decode(headers.get(&case.child).unwrap(), None).unwrap();
        child.timestamp = child.timestamp.checked_add(1).unwrap();
        child.parent_id = Blake2b::<U32>::digest(&shifted_samples[8]).into();
        let shifted_child = child.encode().unwrap();
        let shifted_refs: [&[u8]; 9] = shifted_samples
            .iter()
            .map(Vec::as_slice)
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();
        let shifted = JoinPlan::build(shifted_refs, &shifted_child).unwrap();
        let shifted_witness = shifted.materialize_witness().unwrap();

        // The translated window has identical DAA intervals and result, so its
        // complete arithmetic relation remains satisfied on the altered times.
        let original_result = read_bits(
            daa_witness(&original.daa).unwrap(),
            &original.daa.output.numeric_result,
        );
        let shifted_result = read_bits(
            daa_witness(&shifted.daa).unwrap(),
            &shifted.daa.output.numeric_result,
        );
        assert_eq!(original_result, shifted_result);
        let shifted_daa = &shifted_witness[GLOBAL_DAA_OFFSET..GLOBAL_DAA_OFFSET + DAA_LEN];
        assert_eq!(
            nonzero_rows(shifted.mapped_daa.circuit(), shifted_daa).unwrap(),
            0
        );
        assert_eq!(original.mapped_daa.circuit(), shifted.mapped_daa.circuit());
        assert_eq!(
            nonzero_rows(original.mapped_daa.circuit(), shifted_daa).unwrap(),
            0
        );

        let mut mixed = original_witness;
        mixed[GLOBAL_DAA_OFFSET..GLOBAL_DAA_OFFSET + DAA_LEN].copy_from_slice(shifted_daa);
        for slot in 0..SERIALIZER_SLOTS {
            let start = slot * SERIALIZER_LEN;
            assert_eq!(
                nonzero_rows(
                    &original.serializer.circuit,
                    &mixed[start..start + SERIALIZER_LEN]
                )
                .unwrap(),
                0
            );
        }
        let failed = residual_vector(&original.alias, &mixed).unwrap();
        let failed_rows: Vec<usize> = failed
            .iter()
            .enumerate()
            .filter_map(|(row, value)| (!value.is_zero()).then_some(row))
            .collect();
        let timestamp_rows: Vec<usize> = original
            .alias_rows
            .timestamps
            .iter()
            .flatten()
            .copied()
            .collect();
        assert!(!failed_rows.is_empty());
        assert!(failed_rows.iter().all(|row| timestamp_rows.contains(row)));
        assert!(original.check_residuals(&mixed).is_err());
    }

    #[test]
    fn first_zero_tail_byte_is_a_direct_raw_anchor() {
        let plan = plan_for(9_217);
        let mut witness = plan.materialize_witness().unwrap();
        let (fixture, headers) = fixture();
        let case = fixture
            .cases
            .iter()
            .find(|case| case.child == 9_217)
            .unwrap();
        let first_sample = headers.get(&case.samples[0]).unwrap();
        let target = plan.alias_rows.raw[0][first_sample.len() * 8];
        let term = plan
            .alias
            .terms
            .iter()
            .find(|term| term.row == target)
            .unwrap();
        let wire = term.gate.left;
        assert_eq!(witness[wire], Fr::zero());
        witness[wire] = Fr::one();
        let rows = residual_vector(&plan.alias, &witness).unwrap();
        assert!(!rows[target].is_zero());
        assert!(plan.check_residuals(&witness).is_err());
    }

    #[test]
    fn alias_role_uses_full_global_domain_without_an_embedding_selector() {
        let plan = plan_for(9_217);
        let point = (0..GLOBAL_LOG)
            .map(|index| Fr::from((index * 29 + 7) as u64))
            .collect::<Vec<_>>();
        assert_eq!(JoinPlan::embed_point(Role::Aliases, &point).unwrap(), point);
        assert!(JoinPlan::validate_embedded_point(Role::Aliases, &point).is_ok());
        assert_eq!(plan.alias.input_len, GLOBAL_LEN);
        let metadata = plan.role_metadata(Role::Aliases).unwrap();
        assert_eq!(metadata.input_log, GLOBAL_LOG);
        assert!(metadata.embedding_selector.is_empty());
    }

    fn read_bits(witness: &[Fr], bits: &[usize]) -> Vec<bool> {
        bits.iter()
            .map(|wire| witness[*wire] == Fr::one())
            .collect()
    }
}

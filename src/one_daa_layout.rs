//! Verifier-owned physical imports for the bounded Legacy M1 DAA relation.
//! Admission binds the native relation and serializer fields; it does not
//! authenticate history or prove the imported headers are in a common roster.
use crate::{
    daa_count, daa_finish,
    daa_header_window::{self, Action},
    daa_integer::{self, Epoch, ExternalBits, Inputs, OutputBits},
    daa_one_ratio_finish::{self, CompiledOne, Output},
    header_hash,
    mapped_one_daa::{
        MappedM1, ARITHMETIC_ROW_LOG, IMAGE_END, IMAGE_START, MAPPED_INPUT_LOG, SOURCE_INPUT_LEN,
    },
    serializer,
    sparse::{self, Circuit, Term},
    transcript::Transcript,
};
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use blake2::{digest::consts::U32, Blake2b, Digest};

const ALIAS_ROW_LOG: usize = 8;
const LOCAL_SLOT_LOG: usize = MAPPED_INPUT_LOG;
const SLOT_LEN: usize = 1 << LOCAL_SLOT_LOG;
const START_SLOT: usize = 1023;
const END_SLOT: usize = 2047;
const CHILD_SLOT: usize = 2048;
const CHILD_HEIGHT: u64 = 2049;
const FALLBACK: &str = daa_finish::INITIAL_DIFFICULTY_HEX;
const PROFILE: &[u8] = b"legacy-one-ratio-native-physical-v1";
#[cfg(test)]
pub(crate) const M1_ENDPOINT_PROFILE: &[u8] = PROFILE;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Port {
    source_slot: usize,
    serializer_wire: usize,
    daa_wire: usize,
}

/// Fixed M1 template, history domain and consumer-owned import ledger.
pub(crate) struct OneDaaLayout {
    headers: u64,
    slot_log: usize,
    template: CompiledOne,
    mapped: MappedM1,
    shape: sparse::Shape,
    ports: Vec<Port>,
    descriptor: [u8; 32],
}

/// The complete fixed M1 import window; not a whole-history packet source.
#[cfg(test)]
pub(crate) struct M1AliasEndpointIndex<'a> {
    source: &'a OneDaaLayout,
    left: std::collections::BTreeMap<usize, Vec<usize>>,
    right: Vec<usize>,
}
#[cfg(test)]
impl<'a> M1AliasEndpointIndex<'a> {
    pub(crate) fn identity(&self) -> ([u8; 32], [u8; 32]) {
        (self.source.mapped.identity(), self.source.descriptor)
    }
    pub(crate) fn term(&self, index: usize) -> Result<Term, String> {
        self.source.alias_term(index)
    }
    pub(crate) fn visit(&self, profile: &[u8], map: [u8; 32], descriptor: [u8; 32],
        left: bool, slot: usize, mut sink: impl FnMut(usize, Term) -> Result<(), String>) -> Result<usize, String> {
        if profile != PROFILE || (map, descriptor) != self.identity() || slot >= 4096 {
            return Err("M1 endpoint scope or identity rejected".into());
        }
        let indices: &[usize] = if left { self.left.get(&slot).map(Vec::as_slice).unwrap_or(&[]) }
            else if slot == CHILD_SLOT { &self.right } else { &[] };
        let mut count = 0;
        for &index in indices { sink(index, self.source.alias_term(index)?)?; count += 1; }
        Ok(count)
    }
}

impl OneDaaLayout {
    pub(crate) fn compile(headers: u64, slot_log: usize) -> Result<Self, String> {
        validate_domain(headers, slot_log)?;
        let native_branch = daa_header_window::for_child_height(CHILD_HEIGHT as u32)?;
        if native_branch.action() != Action::Retarget(Epoch::Legacy)
            || native_branch.sample_heights() != [START_SLOT as u32 + 1, END_SLOT as u32 + 1]
        {
            return Err("M1 child height no longer selects the fixed Legacy sample pair".into());
        }
        let template = compile_seed()?;
        validate_native_template(&template)?;
        let mapped = MappedM1::compile(&template)?;
        let shape = sparse::validate(mapped.circuit(), 0)
            .map_err(|error| format!("M1 mapped shape rejected: {error:?}"))?;
        if shape.input_bits != MAPPED_INPUT_LOG || shape.row_bits != ARITHMETIC_ROW_LOG {
            return Err("M1 mapped arithmetic dimensions changed".into());
        }
        let ports = derive_ports(&template, &mapped)?;
        let descriptor = descriptor(headers, slot_log, mapped.identity(), &ports);
        Ok(Self {
            headers,
            slot_log,
            template,
            mapped,
            shape,
            ports,
            descriptor,
        })
    }

    /// Admit a producer only when its full native circuit and typed handles
    /// match this consumer's independently compiled template.
    pub(crate) fn admit(&self, compiled: &CompiledOne) -> Result<MappedM1, String> {
        validate_domain(self.headers, self.slot_log)?;
        let expected = &self.template.arithmetic;
        let actual = &compiled.arithmetic;
        let actual_circuit = actual
            .circuit
            .as_ref()
            .ok_or("M1 producer circuit was not materialized")?;
        let expected_circuit = expected
            .circuit
            .as_ref()
            .ok_or("M1 consumer template circuit missing")?;
        if actual_circuit != expected_circuit {
            return Err("M1 native circuit differs from consumer template".into());
        }
        if !same_semantic_count(&actual.count, &expected.count)
            || actual.witness.len() != SOURCE_INPUT_LEN
            || actual_circuit.input_len != SOURCE_INPUT_LEN
            || actual_circuit.row_count != expected_circuit.row_count
        {
            return Err("M1 native semantic count or witness shape mismatch".into());
        }
        if actual.external.nbits != expected.external.nbits
            || actual.external.start_timestamp != expected.external.start_timestamp
            || actual.external.end_timestamp != expected.external.end_timestamp
            || !same_a1_handles(&actual.output, &expected.output)
            || compiled.output != self.template.output
        {
            return Err("M1 native external, A1, finish, or checkpoint handles mismatch".into());
        }
        if actual.witness[actual.count.live_bits..]
            .iter()
            .any(|value| !value.is_zero())
        {
            return Err("M1 producer native padding is nonzero".into());
        }
        let mapped = MappedM1::compile(compiled)?;
        if mapped.identity() != self.mapped.identity()
            || derive_ports(compiled, &mapped)? != self.ports
        {
            return Err("M1 mapped relation or physical port ledger mismatch".into());
        }
        Ok(mapped)
    }

    pub(crate) fn bind(&self, transcript: &mut Transcript) {
        transcript.append_bytes(b"one-daa-profile", PROFILE);
        transcript.append_bytes(b"one-daa-descriptor", &self.descriptor);
    }

    pub(crate) fn descriptor(&self) -> [u8; 32] {
        self.descriptor
    }

    pub(crate) fn mapped_relation(&self) -> &Circuit {
        self.mapped.circuit()
    }

    #[cfg(test)]
    pub(crate) fn m1_endpoint_index(&self) -> Result<M1AliasEndpointIndex<'_>, String> {
        if self.headers != 3073 || self.slot_log != 12 || self.ports.len() != 192
            || derive_ports(&self.template, &self.mapped)? != self.ports
            || descriptor(self.headers, self.slot_log, self.mapped.identity(), &self.ports) != self.descriptor {
            return Err("named M1 alias source rejected".into());
        }
        let mut left = std::collections::BTreeMap::<usize, Vec<usize>>::new();
        let mut right = Vec::with_capacity(192);
        for (index, port) in self.ports.iter().enumerate() {
            left.entry(port.source_slot).or_default().push(index); right.push(index);
        }
        Ok(M1AliasEndpointIndex { source: self, left, right })
    }

    fn alias_term(&self, index: usize) -> Result<Term, String> {
        let slot_width = 1usize
            .checked_shl(self.slot_log as u32)
            .ok_or("M1 history slot width overflow")?;
        let port = self.ports.get(index).ok_or("M1 alias index outside source")?;
        let source = port
            .source_slot
            .checked_mul(SLOT_LEN)
            .and_then(|base| base.checked_add(port.serializer_wire))
            .ok_or("M1 alias source coordinate overflow")?;
        let target = CHILD_SLOT
            .checked_mul(SLOT_LEN)
            .and_then(|base| base.checked_add(port.daa_wire))
            .ok_or("M1 alias target coordinate overflow")?;
        if port.source_slot >= slot_width || CHILD_SLOT >= slot_width {
            return Err("M1 alias owner is outside admitted history domain".into());
        }
        Ok(Term {
            row: (CHILD_SLOT << ALIAS_ROW_LOG) + index,
            gate: crate::gkr::Gate {
                left: source,
                right: target,
                c0: Fr::zero(),
                c1: Fr::one(),
                c2: -Fr::one(),
                c3: Fr::zero(),
            },
        })
    }

    pub(crate) fn visit_alias_terms(
        &self,
        mut sink: impl FnMut(Term) -> Result<(), String>,
    ) -> Result<usize, String> {
        for index in 0..self.ports.len() {
            sink(self.alias_term(index)?)?;
        }
        Ok(self.ports.len())
    }

    pub(crate) fn alias_coefficients(
        &self,
        r: &[Fr],
        u: &[Fr],
        v: &[Fr],
    ) -> Result<[Fr; 4], String> {
        if r.len() != ALIAS_ROW_LOG + self.slot_log
            || u.len() != LOCAL_SLOT_LOG + self.slot_log
            || v.len() != u.len()
        {
            return Err("M1 alias point dimensions rejected".into());
        }
        let mut out = [Fr::zero(); 4];
        self.visit_alias_terms(|term| {
            let weight = eq_at(r, term.row) * eq_at(u, term.gate.left) * eq_at(v, term.gate.right);
            out[1] += weight;
            out[2] -= weight;
            Ok(())
        })?;
        Ok(out)
    }

    pub(crate) fn arithmetic_coefficients(
        &self,
        r: &[Fr],
        u: &[Fr],
        v: &[Fr],
    ) -> Result<[Fr; 4], String> {
        if r.len() != ARITHMETIC_ROW_LOG + self.slot_log
            || u.len() != LOCAL_SLOT_LOG + self.slot_log
            || v.len() != u.len()
        {
            return Err("M1 arithmetic point dimensions rejected".into());
        }
        let mut out = sparse::wiring(
            self.mapped.circuit(),
            &self.shape,
            &r[..ARITHMETIC_ROW_LOG],
            &u[..LOCAL_SLOT_LOG],
            &v[..LOCAL_SLOT_LOG],
        )
        .map_err(|error| format!("M1 arithmetic wiring rejected: {error:?}"))?;
        let factor = eq_at(&r[ARITHMETIC_ROW_LOG..], CHILD_SLOT)
            * eq_at(&u[LOCAL_SLOT_LOG..], CHILD_SLOT)
            * eq_at(&v[LOCAL_SLOT_LOG..], CHILD_SLOT);
        for coefficient in &mut out {
            *coefficient *= factor;
        }
        Ok(out)
    }
}

fn compile_seed() -> Result<CompiledOne, String> {
    daa_one_ratio_finish::compile(
        &daa_count::q(),
        Inputs {
            nbits: 0x0101_0000,
            start_timestamp: 0,
            end_timestamp: 122_880_000,
        },
        0x0101_0000,
        true,
    )
}

fn validate_domain(headers: u64, slot_log: usize) -> Result<(), String> {
    if headers < CHILD_HEIGHT || slot_log > 21 {
        return Err("M1 history count or slot domain rejected".into());
    }
    let domain = 1u64
        .checked_shl(slot_log as u32)
        .ok_or("M1 history slot domain overflow")?;
    let minimal = headers
        .checked_next_power_of_two()
        .ok_or("M1 history count overflow")?
        .trailing_zeros() as usize;
    if headers > domain || minimal != slot_log {
        return Err("M1 history count does not match its minimal slot domain".into());
    }
    Ok(())
}

fn validate_native_template(compiled: &CompiledOne) -> Result<(), String> {
    let arithmetic = &compiled.arithmetic;
    let circuit = arithmetic
        .circuit
        .as_ref()
        .ok_or("M1 native seed did not materialize")?;
    let count = &arithmetic.count;
    if count.live_bits != 6414
        || count.input_bits != 6414
        || count.padded_input_bits != SOURCE_INPUT_LEN
        || count.residual_rows != 12554
        || count.padded_rows != 1 << ARITHMETIC_ROW_LOG
        || count.terms != 44729
        || count.padding_bits != 1778
        || count.source_nbits_bits != 64
        || count.source_timestamp_bits != 128
        || count.topology_blake2b256
            != [
                0xfa, 0xba, 0x9d, 0x1e, 0xf6, 0x74, 0x17, 0x86, 0xc2, 0x73, 0x67, 0x74, 0xbe, 0x8c,
                0xd8, 0xde, 0xd9, 0x7c, 0x91, 0x24, 0x70, 0x3e, 0x9d, 0xcc, 0x29, 0x62, 0xac, 0x21,
                0xd5, 0xa1, 0x81, 0x15,
            ]
        || circuit.input_len != SOURCE_INPUT_LEN
        || circuit.row_count != 1 << ARITHMETIC_ROW_LOG
        || circuit.terms.len() != count.terms
        || arithmetic.witness.len() != SOURCE_INPUT_LEN
        || compiled.output.child_nbits.len() != 32
        || progress(&compiled.output.before) != [4111, 6206, 32642]
        || progress(&compiled.output.after_profile) != [4174, 6336, 32962]
        || progress(&compiled.output.after_fallback) != [4741, 7470, 35246]
        || progress(&compiled.output.before_child) != [5287, 8562, 37712]
        || progress(&compiled.output.increment.after) != [6414, 10776, 42951]
    {
        return Err("M1 native template differs from frozen measured shape".into());
    }
    Ok(())
}

fn same_semantic_count(a: &daa_integer::Count, b: &daa_integer::Count) -> bool {
    let fields = |c: &daa_integer::Count| {
        [
            c.live_bits,
            c.input_bits,
            c.padded_input_bits,
            c.residual_rows,
            c.padded_rows,
            c.terms,
            c.boolean_rows,
            c.linear_rows,
            c.bilinear_rows,
            c.maximum_column_signed_abs_bits,
            c.maximum_degree,
            c.source_nbits_bits,
            c.source_timestamp_bits,
            c.decoded_bits,
            c.wrapped_delta_bits,
            c.denominator_bits,
            c.numerator_bits,
            c.quotient_bits,
            c.remainder_bits,
            c.quotient_sign_bits,
            c.remainder_sign_bits,
            c.auxiliary_bits,
            c.padding_bits,
            c.peak_row_terms,
        ]
    };
    fields(a) == fields(b) && a.topology_blake2b256 == b.topology_blake2b256
}

fn same_a1_handles(a: &OutputBits, b: &OutputBits) -> bool {
    a.decoded_difficulty == b.decoded_difficulty
        && a.wrapped_delta == b.wrapped_delta
        && a.denominator_magnitude == b.denominator_magnitude
        && a.numerator == b.numerator
        && a.quotient_magnitude == b.quotient_magnitude
        && a.quotient_negative == b.quotient_negative
        && a.remainder_magnitude == b.remainder_magnitude
        && a.remainder_negative == b.remainder_negative
}

fn derive_ports(compiled: &CompiledOne, mapped: &MappedM1) -> Result<Vec<Port>, String> {
    let external: &ExternalBits = &compiled.arithmetic.external;
    let output: &Output = &compiled.output;
    let serializer = serializer::build(None)?;
    let fields = &serializer.layout.fields;
    let mut ports = Vec::with_capacity(192);
    let mut append = |source_slot: usize, serializer_wire: usize, daa_wire: usize| {
        let wire = header_hash::SERIALIZER_OFFSET
            .checked_add(serializer_wire)
            .ok_or("M1 serializer offset overflow")?;
        if source_slot > CHILD_SLOT || wire >= SLOT_LEN || daa_wire >= SLOT_LEN {
            return Err("M1 physical import coordinate escapes its owner slot".into());
        }
        ports.push(Port {
            source_slot,
            serializer_wire: wire,
            daa_wire,
        });
        Ok::<(), String>(())
    };
    for bit in 0..64 {
        append(
            START_SLOT,
            fields.timestamp[bit],
            mapped.mapped_wire(external.start_timestamp[bit])?,
        )?;
    }
    for bit in 0..64 {
        append(
            END_SLOT,
            fields.timestamp[bit],
            mapped.mapped_wire(external.end_timestamp[bit])?,
        )?;
    }
    for bit in 0..32 {
        append(
            END_SLOT,
            fields.n_bits[bit],
            mapped.mapped_wire(external.nbits[bit])?,
        )?;
    }
    for bit in 0..32 {
        let target = mapped.mapped_wire(output.child_nbits[bit])?;
        append(CHILD_SLOT, fields.n_bits[bit], target)?;
    }
    if ports.len() != 192 {
        return Err("M1 physical import count changed".into());
    }
    Ok(ports)
}

fn descriptor(headers: u64, slot_log: usize, mapped: [u8; 32], ports: &[Port]) -> [u8; 32] {
    let mut hash = Blake2b::<U32>::new();
    hash.update(b"legacy-one-ratio-physical-descriptor-v1");
    hash.update(PROFILE);
    hash.update(mapped);
    for value in [
        headers,
        slot_log as u64,
        CHILD_HEIGHT,
        START_SLOT as u64,
        END_SLOT as u64,
        CHILD_SLOT as u64,
        ALIAS_ROW_LOG as u64,
        ARITHMETIC_ROW_LOG as u64,
        LOCAL_SLOT_LOG as u64,
        SOURCE_INPUT_LEN as u64,
        1u64 << ARITHMETIC_ROW_LOG,
        IMAGE_START as u64,
        IMAGE_END as u64,
        ports.len() as u64,
    ] {
        hash.update(value.to_le_bytes());
    }
    hash.update(FALLBACK.as_bytes());
    hash.update(daa_count::q().to_bytes_le());
    for port in ports {
        for value in [port.source_slot, port.serializer_wire, port.daa_wire] {
            hash.update((value as u64).to_le_bytes());
        }
    }
    hash.finalize().into()
}

fn progress(value: &crate::daa_regression::Progress) -> [usize; 3] {
    [value.live_bits, value.rows, value.terms]
}

fn eq_at(point: &[Fr], index: usize) -> Fr {
    point
        .iter()
        .enumerate()
        .fold(Fr::one(), |weight, (bit, value)| {
            weight
                * if (index >> bit) & 1 == 1 {
                    *value
                } else {
                    Fr::one() - value
                }
        })
}

//! One shared streamed relation for four private, serialized headers.
//!
//! This is a bounded producer experiment. It constrains the existing private
//! serializer and BLAKE relations, direct parent/digest links and public hash
//! endpoints, fixed heights 3072..3075, and the decoded-difficulty carry edge
//! 3073->3074 under one input commitment. It does not prove other DAA edges,
//! PoW, curve membership, timestamp ordering, or complete-history coverage.

use ark_bn254::Fr;
use ark_ff::{One, Zero};
use ark_serialize::CanonicalSerialize;
use blake2::{
    digest::{Update, VariableOutput},
    Blake2bVar,
};
use std::{collections::BTreeMap, ops::Range, path::Path};

use crate::{
    gkr::Gate,
    header_hash,
    packed::{PackedFile, PackedFileWriter},
    segment_adjacency::Relation,
    segment_relation::{self, CoreEdgeSource, Joined as HeaderRelation},
    sparse::{self, Circuit, Term},
    sparse_stream_roster::EdgeTerm,
    transcript::Transcript,
};

pub(crate) const INPUT_LOG: usize = 22;
pub(crate) const ROW_LOG: usize = 24;
pub(crate) const LOCAL_LOG: usize = 20;
pub(crate) const SLOT_LOG: usize = 2;
pub(crate) const BASE_ROW_LOG: usize = 20;
pub(crate) const FAMILY_LOG: usize = 2;
pub(crate) const MEMBER_ROW_BITS: [usize; 4] = [9, 19, 20, 20];
pub(crate) const TOTAL_TERMS: usize = 7_422_068;
pub(crate) const FIXED_HEIGHTS: [u32; 4] = [3072, 3073, 3074, 3075];
pub(crate) const CARRY_EDGE: [usize; 2] = [1, 2];
pub(crate) const EXTRA_TERMS: usize = 12_072;
pub(crate) const RELEASED_TERMS: usize = 4096;

const PROFILE: &[u8] = b"nipopow-v2-four-private-header-links-carry-v2";
const VERSION: u64 = 2;
const HEADER_COUNT: usize = 4;
const HEADER_WIDTH: usize = 1 << LOCAL_LOG;
const INPUT_WIDTH: usize = 1 << INPUT_LOG;
const FAMILY_ADJACENCY: usize = 0;
const FAMILY_BOUNDARY: usize = 1;
const FAMILY_CORE: usize = 2;
const FAMILY_CARRY: usize = 3;
const CARRY_OWNER: usize = 2;
const CARRY_BANK: Range<usize> = 917_772..921_868;
const CARRY_RELEASE: Range<usize> = 274_980..279_076;
const CARRY_HELPER_ROWS: usize = 8192;
const CARRY_HELPER_TERMS: usize = 11_804;
const BASE_CORE_TERMS: usize = 172_480;
const EXPECTED_BOUNDARY_TERMS: usize = 473_363;
const EXPECTED_CORE_TERMS_PER_SLOT: usize = 1_379_840;
const EXPECTED_CORE_TERMS: usize = 689_920;
const EXPECTED_ADJACENCY_TERMS: usize = 1_280;
const EXPECTED_TERMS_PER_HEADER: usize = 1_853_203;
const PACKED_BYTES_PER_HEADER: usize = HEADER_WIDTH / 8;

/// Canonical topology and public endpoints for one four-header diagnostic.
/// Private RAWs are used only by `write_witness`; they are not retained here.
pub(crate) struct Plan {
    template: HeaderRelation,
    adjacency: Relation,
    start: [u8; 32],
    tip: [u8; 32],
    descriptor: [u8; 32],
    core_terms: Vec<Term>,
    carry: crate::daa_integer::CompiledCarry,
    extra_terms: Vec<Term>,
    released_terms: Vec<Term>,
}

impl Plan {
    pub(crate) fn build(start: [u8; 32], tip: [u8; 32]) -> Result<Self, String> {
        let mut template = segment_relation::build(None)?;
        segment_relation::attach_serializer_relation(&mut template)?;
        check_template_shape(&template)?;

        // Validate the exact producer templates without expanding eight core
        // copies or materializing the global edge roster.
        CoreEdgeSource::new(&template)?;
        let core_terms = template.core4.terms[..BASE_CORE_TERMS].to_vec();
        sparse::validate(&template.boundary, SLOT_LOG)
            .map_err(|error| format!("four-header boundary admission: {error}"))?;
        sparse::validate(&template.core4, 1)
            .map_err(|error| format!("four-header core admission: {error}"))?;

        let adjacency = Relation::new(
            HEADER_COUNT,
            template.parent_wires,
            template.digest_wires,
            start,
            tip,
        )?;
        if adjacency.input_log() != INPUT_LOG || adjacency.row_count() != 1 << 11 {
            return Err("four-header adjacency dimensions changed".into());
        }
        let carry = crate::daa_integer::compile_carry(&crate::daa_count::q(), 0x0700a8a7, 0x0700a8a7, true)?;
        let (extra_terms, released_terms) = carry_roster(&template, &carry)?;
        let descriptor = topology_descriptor(&template, &adjacency, start, tip, &extra_terms, &released_terms)?;
        Ok(Self {
            template,
            adjacency,
            start,
            tip,
            descriptor,
            core_terms,
            carry,
            extra_terms,
            released_terms,
        })
    }

    pub(crate) fn start(&self) -> [u8; 32] {
        self.start
    }
    pub(crate) fn tip(&self) -> [u8; 32] {
        self.tip
    }
    pub(crate) fn descriptor(&self) -> [u8; 32] {
        self.descriptor
    }
    pub(crate) fn term_count(&self) -> usize {
        TOTAL_TERMS
    }

    /// Bind the plan statement before GKR challenges. The caller appends the
    /// admitted setup ID and encoded common commitment in the same preamble.
    pub(crate) fn bind(&self, transcript: &mut Transcript) {
        transcript.append_bytes(b"four-header-profile", PROFILE);
        transcript.append_u64(b"four-header-version", VERSION);
        transcript.append_u64(b"four-header-count", HEADER_COUNT as u64);
        transcript.append_u64(b"four-header-input-log", INPUT_LOG as u64);
        transcript.append_u64(b"four-header-row-log", ROW_LOG as u64);
        transcript.append_u64(b"four-header-local-log", LOCAL_LOG as u64);
        transcript.append_u64(b"four-header-slot-log", SLOT_LOG as u64);
        transcript.append_u64(b"four-header-base-row-log", BASE_ROW_LOG as u64);
        transcript.append_u64(b"four-header-family-log", FAMILY_LOG as u64);
        for (family, member_bits) in MEMBER_ROW_BITS.iter().enumerate() {
            transcript.append_u64(b"four-header-family", family as u64);
            transcript.append_u64(b"four-header-member-row-bits", *member_bits as u64);
        }
        transcript.append_u64(b"four-header-total-terms", TOTAL_TERMS as u64);
        for height in FIXED_HEIGHTS { transcript.append_u64(b"four-header-fixed-height", height as u64); }
        for slot in CARRY_EDGE { transcript.append_u64(b"four-header-carry-slot", slot as u64); }
        transcript.append_bytes(b"four-header-carry-q", &crate::daa_count::q().to_bytes_be());
        transcript.append_u64(b"four-header-carry-bank-start", CARRY_BANK.start as u64);
        transcript.append_u64(b"four-header-carry-bank-end", CARRY_BANK.end as u64);
        transcript.append_u64(b"four-header-carry-terms", EXTRA_TERMS as u64);
        transcript.append_u64(
            b"four-header-boundary-terms",
            EXPECTED_BOUNDARY_TERMS as u64,
        );
        transcript.append_u64(
            b"four-header-terms-per-slot",
            EXPECTED_TERMS_PER_HEADER as u64,
        );
        transcript.append_u64(
            b"four-header-core-terms-per-slot",
            EXPECTED_CORE_TERMS_PER_SLOT as u64,
        );
        transcript.append_u64(
            b"four-header-adjacency-terms",
            EXPECTED_ADJACENCY_TERMS as u64,
        );
        transcript.append_bytes(b"four-header-endpoint-hash", b"BLAKE2b-256");
        transcript.append_bytes(b"four-header-start", &self.start);
        transcript.append_bytes(b"four-header-tip", &self.tip);
        transcript.append_bytes(b"four-header-topology-hash", b"BLAKE2b-256");
        transcript.append_bytes(b"four-header-topology-descriptor", &self.descriptor);
        self.adjacency.bind(transcript);
    }

    /// Emit precisely the terms whose selected endpoint belongs to `slot`.
    /// Both passes preserve the same source slot and row for every gate.
    pub(crate) fn visit_endpoint(
        &self,
        left: bool,
        slot: usize,
        sink: &mut dyn FnMut(EdgeTerm) -> Result<(), String>,
    ) -> Result<(), String> {
        if slot >= HEADER_COUNT {
            return Err("four-header endpoint slot outside 0..4".into());
        }

        let mut sink_error = None;
        self.adjacency.visit_terms(|row, gate| {
            if sink_error.is_some() {
                return;
            }
            let endpoint = if left { gate.left } else { gate.right };
            if endpoint / HEADER_WIDTH != slot {
                return;
            }
            let owner = row >> 9;
            let member = row & 0x1ff;
            let family_row = (FAMILY_ADJACENCY << BASE_ROW_LOG) | member;
            let edge = EdgeTerm {
                source_slot: owner,
                family_row,
                term: Term { row: member, gate },
            };
            if let Err(error) = sink(edge) {
                sink_error = Some(error);
            }
        });
        if let Some(error) = sink_error {
            return Err(error);
        }

        let mut skipped = 0;
        segment_relation::emit_boundary_edges_for_slot(&self.template, slot, &[], &mut |edge| {
            if slot == CARRY_OWNER && CARRY_RELEASE.contains(&edge.term.row) {
                skipped += 1;
                Ok(())
            } else { sink(edge) }
        })?;
        if skipped != if slot == CARRY_OWNER { RELEASED_TERMS } else { 0 } {
            return Err("four-header carry anchor release census changed".into());
        }
        emit_core_terms_for_slot(&self.core_terms, slot, sink)?;
        for term in &self.extra_terms {
            let endpoint = if left { term.gate.left } else { term.gate.right };
            if endpoint / HEADER_WIDTH == slot {
                sink(EdgeTerm { source_slot: CARRY_OWNER,
                    family_row: (FAMILY_CARRY << BASE_ROW_LOG) | term.row, term: term.clone() })?;
            }
        }
        Ok(())
    }

    /// Factored base coefficients plus the exact bounded carry-family roster.
    /// Coordinates are little-endian: 24 row, 22 left, and 22 right bits.
    pub(crate) fn coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
        if r.len() != ROW_LOG || u.len() != INPUT_LOG || v.len() != INPUT_LOG {
            return Err("four-header coefficient point dimensions invalid".into());
        }

        let adjacency = self
            .adjacency
            .wiring_coefficients(&r[..11], u, v)
            .map_err(|error| error.to_string())?;
        let adjacency_factor = eq_index(&r[11..22], 0) * eq_index(&r[22..24], FAMILY_ADJACENCY);

        let boundary_shape = sparse::validate(&self.template.boundary, SLOT_LOG)
            .map_err(|error| error.to_string())?;
        let boundary = sparse::wiring(&self.template.boundary, &boundary_shape, &r[..21], u, v)
            .map_err(|error| error.to_string())?;
        let boundary_factor = (Fr::one() - r[21]) * eq_index(&r[22..24], FAMILY_BOUNDARY);

        let core_shape =
            sparse::validate(&self.template.core4, 1).map_err(|error| error.to_string())?;
        let core = sparse::wiring(
            &self.template.core4,
            &core_shape,
            &r[..20],
            &u[..19],
            &v[..19],
        )
        .map_err(|error| error.to_string())?;
        let core_padding = (Fr::one() - u[19]) * (Fr::one() - v[19]);
        let core_slot_factor = (0..HEADER_COUNT).fold(Fr::zero(), |sum, slot| {
            sum + eq_index(&r[20..22], slot)
                * eq_index(&u[20..22], slot)
                * eq_index(&v[20..22], slot)
        });
        let core_factor = core_padding * core_slot_factor * eq_index(&r[22..24], FAMILY_CORE);

        let mut output = std::array::from_fn(|index| {
            adjacency_factor * adjacency[index]
                + boundary_factor * boundary[index]
                + core_factor * core[index]
        });
        // Boundary member rows have 19 bits, unlike the 20-bit carry family.
        let released_factor = eq_index(&r[19..21], CARRY_OWNER)
            * (Fr::one() - r[21]) * eq_index(&r[22..24], FAMILY_BOUNDARY);
        add_term_coefficients(&mut output, &self.released_terms, &r[..19], u, v,
            -released_factor);
        let extra_factor = eq_index(&r[20..22], CARRY_OWNER)
            * eq_index(&r[22..24], FAMILY_CARRY);
        add_term_coefficients(&mut output, &self.extra_terms, &r[..20], u, v, extra_factor);
        Ok(output)
    }

    /// Build four private local assignments and append their packed bits to a
    /// single create-only log22 witness file. The RAW bytes are not retained.
    pub(crate) fn write_witness(
        &self,
        raws: &[Vec<u8>],
        path: &Path,
    ) -> Result<PackedFile, String> {
        if raws.len() != HEADER_COUNT {
            return Err("four-header witness requires exactly four RAWs".into());
        }
        let parent = ergo_header_core::Header::decode(&raws[CARRY_EDGE[0]], None)
            .map_err(|error| format!("carry parent RAW: {error:?}"))?;
        let child = ergo_header_core::Header::decode(&raws[CARRY_EDGE[1]], None)
            .map_err(|error| format!("carry child RAW: {error:?}"))?;
        let carry = crate::daa_integer::compile_carry(&crate::daa_count::q(),
            parent.n_bits, child.n_bits, true)?;
        if carry.circuit != self.carry.circuit {
            return Err("four-header private carry topology changed".into());
        }
        check_circuit_assignment(carry.circuit.as_ref().ok_or("carry circuit absent")?, &carry.witness)
            .map_err(|error| format!("decoded carry: {error}"))?;
        let mut writer = PackedFileWriter::create_new(path, INPUT_LOG)?;
        let mut parents = [[0u8; 32]; HEADER_COUNT];
        let mut digests = [[0u8; 32]; HEADER_COUNT];
        let mut extra_values = BTreeMap::new();

        for (slot, raw) in raws.iter().enumerate() {
            let mut assignment = build_slot_assignment(&self.template, raw)?;
            if read_bits_at(&assignment.input, header_hash::SERIALIZER_OFFSET,
                &self.template.serializer.layout.fields.height)? != FIXED_HEIGHTS[slot] as u64 {
                return Err("four-header fixed height mismatch".into());
            }
            if slot == CARRY_OWNER {
                assignment.input[CARRY_BANK.clone()].copy_from_slice(&carry.witness);
            }
            for term in &self.extra_terms {
                for wire in [term.gate.left, term.gate.right] {
                    if wire / HEADER_WIDTH == slot {
                        extra_values.insert(wire, assignment.input[wire % HEADER_WIDTH]);
                    }
                }
            }
            parents[slot] = assignment.parent;
            digests[slot] = assignment.digest;
            let packed = pack_boolean_bits(&assignment.input)?;
            if packed.len() != PACKED_BYTES_PER_HEADER {
                return Err("four-header packed slot byte count changed".into());
            }
            writer.write_bytes(&packed)?;
        }

        check_extra_values(&self.extra_terms, &extra_values)?;
        check_adjacency_projection(&self.template, &self.adjacency, &parents, &digests)?;
        let source = writer.finish()?;
        if source.input_len() != INPUT_WIDTH {
            return Err("four-header packed witness dimension changed".into());
        }
        Ok(source)
    }
}

struct SlotAssignment {
    input: Vec<Fr>,
    parent: [u8; 32],
    digest: [u8; 32],
}

fn build_slot_assignment(template: &HeaderRelation, raw: &[u8]) -> Result<SlotAssignment, String> {
    if !(1..=514).contains(&raw.len()) {
        return Err("four-header RAW length outside canonical serializer bound".into());
    }
    let header = ergo_header_core::Header::decode(raw, None)
        .map_err(|error| format!("four-header RAW decode: {error:?}"))?;
    if header
        .encode()
        .map_err(|error| format!("four-header native encode: {error:?}"))?
        != raw
    {
        return Err("four-header RAW is not a canonical native encoding".into());
    }
    let fields = crate::serializer::Fields::from_header(&header)?;
    let mut local = segment_relation::build(Some(&fields))?;
    segment_relation::attach_serializer_relation(&mut local)?;
    if local.core4 != template.core4
        || local.boundary != template.boundary
        || local.serializer.circuit != template.serializer.circuit
    {
        return Err("private assignment topology differs from the frozen plan".into());
    }
    let input = local
        .input
        .take()
        .ok_or("four-header private assignment missing")?;
    if input.len() != HEADER_WIDTH || input.iter().any(|bit| !bit.is_zero() && !bit.is_one()) {
        return Err("four-header private assignment is not a Boolean log20 slot".into());
    }

    check_core_assignment(&template.core4, &input)?;
    check_circuit_assignment(
        &template.serializer.circuit,
        &input[header_hash::SERIALIZER_OFFSET
            ..header_hash::SERIALIZER_OFFSET + template.serializer.circuit.input_len],
    )?;
    check_circuit_assignment(&template.boundary, &input)?;
    check_native_serialization(&local.serializer.layout, &input, raw)?;

    let parent = read_mapped_bytes(&input, &template.parent_wires)?;
    let digest = read_mapped_bytes(&input, &template.digest_wires)?;
    let native_digest = ergo_header_core::blake2b256(raw);
    if digest != native_digest {
        return Err("four-header BLAKE assignment differs from native BLAKE2b-256".into());
    }
    Ok(SlotAssignment {
        input,
        parent,
        digest,
    })
}

/// Code-owned carry and fixed-height roster. No private values choose wires,
/// rows, coefficients, or which existing padding anchors are removed.
fn carry_roster(template: &HeaderRelation, carry: &crate::daa_integer::CompiledCarry)
    -> Result<(Vec<Term>, Vec<Term>), String> {
    if crate::daa_header_window::for_child_height(FIXED_HEIGHTS[CARRY_EDGE[1]])?.action()
        != crate::daa_header_window::Action::Carry {
        return Err("four-header selected edge is not native Carry".into());
    }
    let circuit = carry.circuit.as_ref().ok_or("carry circuit not materialized")?;
    if carry.count.residual_rows != 6162 || circuit.input_len != RELEASED_TERMS || carry.witness.len() != RELEASED_TERMS
        || circuit.row_count != CARRY_HELPER_ROWS || circuit.terms.len() != CARRY_HELPER_TERMS {
        return Err("four-header carry helper geometry changed".into());
    }
    let released = segment_relation::padding_anchor_row_ranges_for_wires(template,
        &[CARRY_BANK.clone()])?;
    if released != [CARRY_RELEASE.clone()] {
        return Err("four-header carry bank maps to unexpected padding anchors".into());
    }
    let base = CARRY_OWNER * HEADER_WIDTH + CARRY_BANK.start;
    let mut terms = circuit.terms.iter().map(|term| Term {
        row: term.row,
        gate: Gate { left: base + term.gate.left, right: base + term.gate.right,
            c0: term.gate.c0, c1: term.gate.c1, c2: term.gate.c2, c3: term.gate.c3 },
    }).collect::<Vec<_>>();
    let mut row = CARRY_HELPER_ROWS;
    for (slot, raw_wires) in [(CARRY_EDGE[0], carry.parent_nbits), (CARRY_EDGE[1], carry.child_nbits)] {
        for (bit, wire) in raw_wires.into_iter().enumerate() {
            terms.push(Term { row, gate: Gate { left: base + wire, right: 0,
                c0: Fr::zero(), c1: Fr::one(), c2: Fr::zero(), c3: Fr::zero() } });
            terms.push(Term { row, gate: Gate {
                left: slot * HEADER_WIDTH + header_hash::SERIALIZER_OFFSET
                    + template.serializer.layout.fields.n_bits[bit], right: 0,
                c0: Fr::zero(), c1: -Fr::one(), c2: Fr::zero(), c3: Fr::zero() } });
            row += 1;
        }
    }
    for (slot, height) in FIXED_HEIGHTS.into_iter().enumerate() {
        for bit in 0..32 {
            terms.push(Term { row, gate: Gate {
                left: slot * HEADER_WIDTH + header_hash::SERIALIZER_OFFSET
                    + template.serializer.layout.fields.height[bit], right: 0,
                c0: Fr::zero(), c1: Fr::one(), c2: Fr::zero(), c3: Fr::zero() } });
            if (height >> bit) & 1 != 0 {
                terms.push(Term { row, gate: Gate { left: 0, right: 0,
                    c0: -Fr::one(), c1: Fr::zero(), c2: Fr::zero(), c3: Fr::zero() } });
            }
            row += 1;
        }
    }
    if row != CARRY_HELPER_ROWS + 64 + 128 || terms.len() != EXTRA_TERMS
        || terms.iter().any(|term| term.row >= 1 << BASE_ROW_LOG
            || term.gate.left >= INPUT_WIDTH || term.gate.right >= INPUT_WIDTH) {
        return Err("four-header carry/height inventory changed".into());
    }
    let removed = template.boundary.terms.iter()
        .filter(|term| CARRY_RELEASE.contains(&term.row))
        .map(|term| Term { row: term.row, gate: Gate {
            left: CARRY_OWNER * HEADER_WIDTH + term.gate.left,
            right: CARRY_OWNER * HEADER_WIDTH + term.gate.right,
            c0: term.gate.c0, c1: term.gate.c1, c2: term.gate.c2, c3: term.gate.c3 } })
        .collect::<Vec<_>>();
    if removed.len() != RELEASED_TERMS { return Err("carry removed-anchor census".into()); }
    Ok((terms, removed))
}

fn add_term_coefficients(output: &mut [Fr; 4], terms: &[Term],
    r: &[Fr], u: &[Fr], v: &[Fr], factor: Fr) {
    for term in terms {
        let weight = factor * eq_index(r, term.row)
            * eq_index(u, term.gate.left) * eq_index(v, term.gate.right);
        for (sum, coefficient) in output.iter_mut().zip([
            term.gate.c0, term.gate.c1, term.gate.c2, term.gate.c3]) {
            *sum += weight * coefficient;
        }
    }
}

fn check_extra_values(terms: &[Term], values: &BTreeMap<usize, Fr>) -> Result<(), String> {
    let mut rows = vec![Fr::zero(); CARRY_HELPER_ROWS + 64 + 128];
    for term in terms {
        let left = *values.get(&term.gate.left).ok_or("carry left witness value absent")?;
        let right = *values.get(&term.gate.right).ok_or("carry right witness value absent")?;
        rows[term.row] += term.gate.c0 + term.gate.c1 * left
            + term.gate.c2 * right + term.gate.c3 * left * right;
    }
    if rows.iter().any(|value| !value.is_zero()) {
        return Err("four-header carry/height assignment has nonzero residuals".into());
    }
    Ok(())
}

fn check_template_shape(template: &HeaderRelation) -> Result<(), String> {
    if template.core4.input_len != 1 << 18
        || template.core4.row_count != 1 << 19
        || template.core4.terms.len() != EXPECTED_CORE_TERMS
        || template.boundary.input_len != HEADER_WIDTH
        || template.boundary.row_count != 1 << 19
        || template.boundary.terms.len() != EXPECTED_BOUNDARY_TERMS
        || template.serializer.circuit.input_len != header_hash::SERIALIZER_WIDTH
        || template.serializer.circuit.row_count != 1 << 18
        || template.serializer.circuit.terms.len() != 315_546
        || template
            .parent_wires
            .iter()
            .any(|wire| *wire >= HEADER_WIDTH)
        || template
            .digest_wires
            .iter()
            .any(|wire| *wire >= HEADER_WIDTH)
        || template
            .parent_wires
            .iter()
            .any(|wire| template.digest_wires.contains(wire))
    {
        return Err("four-header canonical template dimensions or inventory changed".into());
    }
    let per_slot = template
        .boundary
        .terms
        .len()
        .checked_add(header_hash::CORE_COPIES * BASE_CORE_TERMS)
        .ok_or("four-header per-slot term count overflow")?;
    let total = HEADER_COUNT
        .checked_mul(per_slot)
        .and_then(|count| count.checked_add(EXPECTED_ADJACENCY_TERMS))
        .ok_or("four-header total term count overflow")?;
    if per_slot != EXPECTED_TERMS_PER_HEADER || total + EXTRA_TERMS - RELEASED_TERMS != TOTAL_TERMS {
        return Err("four-header canonical constraint inventory changed".into());
    }
    Ok(())
}

/// Replay the cached base template that CoreEdgeSource validated at Plan
/// construction. Revalidation is intentionally outside this hot callback:
/// the roster replays endpoint producers many times during one GKR.
fn emit_core_terms_for_slot(
    terms: &[Term],
    slot: usize,
    sink: &mut dyn FnMut(EdgeTerm) -> Result<(), String>,
) -> Result<(), String> {
    if slot >= HEADER_COUNT || terms.len() != BASE_CORE_TERMS {
        return Err("four-header BLAKE source slot or template shape invalid".into());
    }
    const CORE_ROWS: usize = 1 << 17;
    for copy in 0..header_hash::CORE_COPIES {
        let row_offset = copy * CORE_ROWS;
        let wire_offset = slot * HEADER_WIDTH + copy * header_hash::CORE_WIDTH;
        for base in terms {
            let row = row_offset + base.row;
            let family_row = (FAMILY_CORE << BASE_ROW_LOG) | row;
            let term = Term {
                row,
                gate: Gate {
                    left: wire_offset + base.gate.left,
                    right: wire_offset + base.gate.right,
                    c0: base.gate.c0,
                    c1: base.gate.c1,
                    c2: base.gate.c2,
                    c3: base.gate.c3,
                },
            };
            sink(EdgeTerm {
                source_slot: slot,
                family_row,
                term,
            })?;
        }
    }
    Ok(())
}

fn check_core_assignment(core4: &Circuit, input: &[Fr]) -> Result<(), String> {
    if input.len() < header_hash::CORE_COPIES * header_hash::CORE_WIDTH
        || core4.terms.len() != EXPECTED_CORE_TERMS
    {
        return Err("four-header BLAKE assignment shape changed".into());
    }
    let template = &core4.terms[..BASE_CORE_TERMS];
    for copy in 0..header_hash::CORE_COPIES {
        let start = copy * header_hash::CORE_WIDTH;
        check_term_assignment(
            template,
            &input[start..start + header_hash::CORE_WIDTH],
            1 << 17,
            "BLAKE compression",
        )?;
    }
    Ok(())
}

fn check_circuit_assignment(circuit: &Circuit, input: &[Fr]) -> Result<(), String> {
    check_term_assignment(&circuit.terms, input, circuit.row_count, "local circuit")
}

fn check_term_assignment(
    terms: &[Term],
    input: &[Fr],
    row_count: usize,
    label: &str,
) -> Result<(), String> {
    let mut rows = vec![Fr::zero(); row_count];
    for term in terms {
        if term.row >= row_count || term.gate.left >= input.len() || term.gate.right >= input.len()
        {
            return Err(format!("{label} term outside declared shape"));
        }
        rows[term.row] += term.gate.evaluate(input);
    }
    if rows.iter().any(|value| !value.is_zero()) {
        return Err(format!("{label} assignment has nonzero residuals"));
    }
    Ok(())
}

fn check_native_serialization(
    layout: &crate::serializer::Layout,
    input: &[Fr],
    raw: &[u8],
) -> Result<(), String> {
    let length = read_bits_at(input, header_hash::SERIALIZER_OFFSET, &layout.length)? as usize;
    if length != raw.len() {
        return Err("private serializer length differs from RAW length".into());
    }
    for (index, bits) in layout.bytes.iter().enumerate() {
        let byte = read_bits_at(input, header_hash::SERIALIZER_OFFSET, bits)? as u8;
        let expected = raw.get(index).copied().unwrap_or(0);
        if byte != expected {
            return Err("private serializer bytes differ from canonical RAW".into());
        }
    }
    Ok(())
}

fn read_bits_at(input: &[Fr], base: usize, wires: &[usize]) -> Result<u64, String> {
    if wires.len() > 64 {
        return Err("four-header bit word exceeds 64 bits".into());
    }
    let mut value = 0u64;
    for (bit, wire) in wires.iter().enumerate() {
        let index = base
            .checked_add(*wire)
            .ok_or("four-header serializer wire overflow")?;
        let field = input
            .get(index)
            .ok_or("four-header serializer wire outside slot")?;
        if field.is_one() {
            value |= 1u64 << bit;
        } else if !field.is_zero() {
            return Err("four-header serializer field is non-Boolean".into());
        }
    }
    Ok(value)
}

fn read_mapped_bytes(input: &[Fr], wires: &[usize; 256]) -> Result<[u8; 32], String> {
    let mut out = [0u8; 32];
    for (bit, wire) in wires.iter().enumerate() {
        let value = input
            .get(*wire)
            .ok_or("four-header mapped wire outside slot")?;
        if value.is_one() {
            out[bit / 8] |= 1 << (bit % 8);
        } else if !value.is_zero() {
            return Err("four-header mapped field is non-Boolean".into());
        }
    }
    Ok(out)
}

fn pack_boolean_bits(input: &[Fr]) -> Result<Vec<u8>, String> {
    if input.len() != HEADER_WIDTH {
        return Err("four-header slot input must be exactly log20".into());
    }
    let mut packed = vec![0u8; PACKED_BYTES_PER_HEADER];
    for (index, value) in input.iter().enumerate() {
        if value.is_one() {
            packed[index / 8] |= 1 << (index % 8);
        } else if !value.is_zero() {
            return Err("four-header witness contains a non-Boolean bit".into());
        }
    }
    Ok(packed)
}

fn check_adjacency_projection(
    template: &HeaderRelation,
    relation: &Relation,
    parents: &[[u8; 32]; HEADER_COUNT],
    digests: &[[u8; 32]; HEADER_COUNT],
) -> Result<(), String> {
    let mut rows = vec![Fr::zero(); relation.row_count()];
    relation.visit_terms(|row, gate| {
        if row >= rows.len() {
            return;
        }
        let left = projection_wire_value(template, gate.left, parents, digests);
        // The two public endpoint gates have zero right coefficients. Their
        // global right wire is the protocol's zero anchor, not a witness claim.
        let right = if gate.c2.is_zero() && gate.c3.is_zero() {
            Fr::zero()
        } else {
            projection_wire_value(template, gate.right, parents, digests)
        };
        rows[row] += gate.c0 + gate.c1 * left + gate.c2 * right + gate.c3 * left * right;
    });
    if let Some((row, _)) = rows.iter().enumerate().find(|(_, value)| !value.is_zero()) {
        return Err(format!("four-header adjacency residual at row {row}"));
    }
    Ok(())
}

fn projection_wire_value(
    template: &HeaderRelation,
    wire: usize,
    parents: &[[u8; 32]; HEADER_COUNT],
    digests: &[[u8; 32]; HEADER_COUNT],
) -> Fr {
    let slot = wire / HEADER_WIDTH;
    let local = wire % HEADER_WIDTH;
    if slot >= HEADER_COUNT {
        return Fr::zero();
    }
    if let Some(bit) = template
        .parent_wires
        .iter()
        .position(|mapped| *mapped == local)
    {
        return Fr::from(((parents[slot][bit / 8] >> (bit % 8)) & 1) as u64);
    }
    if let Some(bit) = template
        .digest_wires
        .iter()
        .position(|mapped| *mapped == local)
    {
        return Fr::from(((digests[slot][bit / 8] >> (bit % 8)) & 1) as u64);
    }
    Fr::zero()
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

fn topology_descriptor(
    template: &HeaderRelation,
    adjacency: &Relation,
    start: [u8; 32],
    tip: [u8; 32],
    extra_terms: &[Term],
    released_terms: &[Term],
) -> Result<[u8; 32], String> {
    let mut hasher = Blake2bVar::new(32).map_err(|_| "topology BLAKE2b-256 init failed")?;
    hasher.update(b"nipopow-v2-four-header-topology-descriptor-carry-v2");
    for height in FIXED_HEIGHTS { hash_usize(&mut hasher, height as usize); }
    for slot in CARRY_EDGE { hash_usize(&mut hasher, slot); }
    hasher.update(&crate::daa_count::q().to_bytes_be());
    hash_usize(&mut hasher, CARRY_BANK.start);
    hash_usize(&mut hasher, CARRY_BANK.end);
    hash_circuit_terms(&mut hasher, extra_terms)?;
    hash_circuit_terms(&mut hasher, released_terms)?;
    hash_usize(&mut hasher, INPUT_LOG);
    hash_usize(&mut hasher, ROW_LOG);
    hash_usize(&mut hasher, template.core4.input_len);
    hash_usize(&mut hasher, template.core4.row_count);
    hash_usize(&mut hasher, template.core4.terms.len());
    hash_circuit_terms(&mut hasher, &template.core4.terms)?;
    hash_usize(&mut hasher, template.boundary.input_len);
    hash_usize(&mut hasher, template.boundary.row_count);
    hash_usize(&mut hasher, template.boundary.terms.len());
    hash_circuit_terms(&mut hasher, &template.boundary.terms)?;
    hash_usize(&mut hasher, adjacency.input_log());
    hash_usize(&mut hasher, adjacency.row_count());
    for wire in template.parent_wires {
        hash_usize(&mut hasher, wire);
    }
    for wire in template.digest_wires {
        hash_usize(&mut hasher, wire);
    }
    hasher.update(&start);
    hasher.update(&tip);
    let mut digest = [0u8; 32];
    hasher
        .finalize_variable(&mut digest)
        .map_err(|_| "topology BLAKE2b-256 finalize failed")?;
    Ok(digest)
}

fn hash_usize(hasher: &mut Blake2bVar, value: usize) {
    hasher.update(&(value as u64).to_le_bytes());
}

fn hash_circuit_terms(hasher: &mut Blake2bVar, terms: &[Term]) -> Result<(), String> {
    let mut encoded = Vec::with_capacity(32);
    for term in terms {
        hash_usize(hasher, term.row);
        hash_usize(hasher, term.gate.left);
        hash_usize(hasher, term.gate.right);
        for coefficient in [&term.gate.c0, &term.gate.c1, &term.gate.c2, &term.gate.c3] {
            encoded.clear();
            coefficient
                .serialize_compressed(&mut encoded)
                .map_err(|error| format!("topology scalar encoding: {error}"))?;
            hasher.update(&encoded);
        }
    }
    Ok(())
}

#[cfg(test)]
pub(crate) const FIXTURE_START: [u8; 32] = [
    0x01, 0x5f, 0x32, 0xf7, 0xb2, 0xf5, 0xb8, 0xcf, 0x5e, 0x42, 0xdb, 0x44, 0x37, 0x0a, 0x9e, 0x79,
    0x69, 0xe4, 0x8b, 0xf8, 0x09, 0x9c, 0xea, 0x52, 0xf6, 0x9f, 0xf3, 0xba, 0xc8, 0xea, 0xe9, 0x68,
];

#[cfg(test)]
pub(crate) const FIXTURE_TIP: [u8; 32] = [
    0xed, 0x7e, 0xf8, 0x76, 0xa4, 0x51, 0x1e, 0xb2, 0x0d, 0xe1, 0x4c, 0x7b, 0x43, 0x3f, 0x64, 0x86,
    0xbf, 0x83, 0x61, 0x13, 0x76, 0xd4, 0x9d, 0x6c, 0x46, 0x91, 0xcf, 0xd0, 0xb6, 0x8f, 0xf3, 0xea,
];

#[cfg(test)]
pub(crate) fn fixture_raws() -> Result<Vec<Vec<u8>>, String> {
    let bytes = include_bytes!("../fixtures/four-header-linked-3072-3075-v1.raw.bin");
    let mut offset = 0usize;
    let mut raws = Vec::with_capacity(HEADER_COUNT);
    for _ in 0..HEADER_COUNT {
        let length_end = offset
            .checked_add(4)
            .ok_or("fixture frame offset overflow")?;
        let header = bytes
            .get(offset..length_end)
            .ok_or("fixture frame lacks length")?;
        let length = u32::from_le_bytes(header.try_into().unwrap()) as usize;
        offset = length_end;
        let end = offset
            .checked_add(length)
            .ok_or("fixture frame length overflow")?;
        let raw = bytes.get(offset..end).ok_or("fixture frame is truncated")?;
        raws.push(raw.to_vec());
        offset = end;
    }
    if offset != bytes.len() {
        return Err("fixture frame has trailing bytes".into());
    }
    Ok(raws)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        fs,
        sync::atomic::{AtomicU64, Ordering},
    };

    static NEXT: AtomicU64 = AtomicU64::new(0);

    fn temp_path() -> std::path::PathBuf {
        std::env::temp_dir().join(format!(
            "four-header-link-{}-{}.bits",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed),
        ))
    }

    fn points(seed: u64) -> (Vec<Fr>, Vec<Fr>, Vec<Fr>) {
        let r = (0..ROW_LOG)
            .map(|i| Fr::from(seed + 3 + i as u64 * 7))
            .collect();
        let u = (0..INPUT_LOG)
            .map(|i| Fr::from(seed + 5 + i as u64 * 11))
            .collect();
        let v = (0..INPUT_LOG)
            .map(|i| Fr::from(seed + 9 + i as u64 * 13))
            .collect();
        (r, u, v)
    }

    fn eq_table(point: &[Fr]) -> Vec<Fr> {
        (0..1usize << point.len())
            .map(|index| eq_index(point, index))
            .collect()
    }

    fn explicit_emitted_coefficients(
        plan: &Plan,
        r: &[Fr],
        u: &[Fr],
        v: &[Fr],
        mutation: Option<usize>,
    ) -> [Fr; 4] {
        let row_family = eq_table(&r[22..24]);
        let input_u_local = eq_table(&u[..LOCAL_LOG]);
        let input_v_local = eq_table(&v[..LOCAL_LOG]);
        let input_u_slot = eq_table(&u[LOCAL_LOG..]);
        let input_v_slot = eq_table(&v[LOCAL_LOG..]);
        let row_members: [Vec<Fr>; 4] =
            std::array::from_fn(|family| eq_table(&r[..MEMBER_ROW_BITS[family]]));
        let row_owners: [Vec<Fr>; 4] = std::array::from_fn(|family| {
            eq_table(&r[MEMBER_ROW_BITS[family]..MEMBER_ROW_BITS[family] + SLOT_LOG])
        });
        let row_gaps: [Fr; 4] = std::array::from_fn(|family| {
            let gap_start = MEMBER_ROW_BITS[family] + SLOT_LOG;
            if gap_start == 22 {
                Fr::one()
            } else {
                eq_index(&r[gap_start..22], 0)
            }
        });
        let mut output = [Fr::zero(); 4];
        let mut seen = 0usize;
        for slot in 0..HEADER_COUNT {
            plan.visit_endpoint(true, slot, &mut |mut edge| {
                let current = seen;
                seen += 1;
                if mutation == Some(current) {
                    return Ok(());
                }
                if mutation == Some(usize::MAX) && current == 0 {
                    edge.source_slot = (edge.source_slot + 1) % HEADER_COUNT;
                }
                let family = edge.family_row >> BASE_ROW_LOG;
                let member = edge.family_row & ((1 << BASE_ROW_LOG) - 1);
                let owner = edge.source_slot;
                let row_weight = row_family[family]
                    * row_owners[family][owner]
                    * row_members[family][member]
                    * row_gaps[family];
                let left_slot = edge.term.gate.left >> LOCAL_LOG;
                let left_local = edge.term.gate.left & (HEADER_WIDTH - 1);
                let right_slot = edge.term.gate.right >> LOCAL_LOG;
                let right_local = edge.term.gate.right & (HEADER_WIDTH - 1);
                let weight = row_weight
                    * input_u_slot[left_slot]
                    * input_u_local[left_local]
                    * input_v_slot[right_slot]
                    * input_v_local[right_local];
                for (sum, coefficient) in output.iter_mut().zip([
                    edge.term.gate.c0,
                    edge.term.gate.c1,
                    edge.term.gate.c2,
                    edge.term.gate.c3,
                ]) {
                    *sum += weight * coefficient;
                }
                Ok(())
            })
            .unwrap();
        }
        output
    }

    fn projection_bytes(template: &HeaderRelation, raw: &[u8]) -> ([u8; 32], [u8; 32]) {
        let assignment = build_slot_assignment(template, raw).unwrap();
        (assignment.parent, assignment.digest)
    }

    fn projection_failure_rows(
        plan: &Plan,
        parents: &[[u8; 32]; HEADER_COUNT],
        digests: &[[u8; 32]; HEADER_COUNT],
    ) -> Vec<usize> {
        let mut rows = vec![Fr::zero(); plan.adjacency.row_count()];
        plan.adjacency.visit_terms(|row, gate| {
            let left = projection_wire_value(&plan.template, gate.left, parents, digests);
            let right = if gate.c2.is_zero() && gate.c3.is_zero() {
                Fr::zero()
            } else {
                projection_wire_value(&plan.template, gate.right, parents, digests)
            };
            rows[row] += gate.c0 + gate.c1 * left + gate.c2 * right + gate.c3 * left * right;
        });
        rows.into_iter()
            .enumerate()
            .filter_map(|(row, value)| (!value.is_zero()).then_some(row))
            .collect()
    }

    #[test]
    fn plan_inventory_and_dimensions_are_exact() {
        let plan = Plan::build(FIXTURE_START, FIXTURE_TIP).unwrap();
        assert_eq!(plan.start(), FIXTURE_START);
        assert_eq!(plan.tip(), FIXTURE_TIP);
        assert_eq!(plan.term_count(), 7_422_068);
        assert_eq!(plan.template.boundary.terms.len(), 473_363);
        assert_eq!(plan.template.core4.terms.len(), 689_920);
        assert_eq!(plan.adjacency.row_count(), 2_048);
        assert_eq!(plan.adjacency.input_log(), 22);
        assert_ne!(plan.descriptor(), [0; 32]);
    }

    // Build a fully reserialized and relinked chain for each single fault.
    // Consequently the carry/height negatives cannot pass merely because a
    // BLAKE assignment, public endpoint, or parent edge was left stale.
    fn c583_linked_raws(parent: u32, child: u32, wrong_height: Option<usize>)
        -> (Vec<Vec<u8>>, [u8; 32], [u8; 32]) {
        let mut headers = fixture_raws().unwrap().iter().map(|raw|
            ergo_header_core::Header::decode(raw, None).unwrap()).collect::<Vec<_>>();
        headers[CARRY_EDGE[0]].n_bits = parent;
        headers[CARRY_EDGE[1]].n_bits = child;
        if let Some(slot) = wrong_height { headers[slot].height += 1; }
        let start = headers[0].parent_id;
        let mut raws: Vec<Vec<u8>> = Vec::new();
        for index in 0..HEADER_COUNT {
            if index != 0 { headers[index].parent_id = ergo_header_core::blake2b256(&raws[index - 1]); }
            raws.push(headers[index].encode().unwrap());
        }
        let tip = ergo_header_core::blake2b256(raws.last().unwrap());
        (raws, start, tip)
    }

    fn c583_values(plan: &Plan, raws: &[Vec<u8>], carry: &crate::daa_integer::CompiledCarry)
        -> BTreeMap<usize, Fr> {
        let mut values = BTreeMap::new();
        for (slot, raw) in raws.iter().enumerate() {
            let mut input = build_slot_assignment(&plan.template, raw).unwrap().input;
            if slot == CARRY_OWNER { input[CARRY_BANK.clone()].copy_from_slice(&carry.witness); }
            for term in &plan.extra_terms {
                for wire in [term.gate.left, term.gate.right] {
                    if wire / HEADER_WIDTH == slot { values.insert(wire, input[wire % HEADER_WIDTH]); }
                }
            }
        }
        values
    }

    #[test]
    fn c583_decoded_carry_alias_and_relinked_mismatch_are_isolated() {
        let q = crate::daa_count::q();
        // Unequal compacts for the same positive decoded integer must pass.
        let (raws, start, tip) = c583_linked_raws(0x03001200, 0x02120000, None);
        let plan = Plan::build(start, tip).unwrap();
        let alias = crate::daa_integer::compile_carry(&q, 0x03001200, 0x02120000, true).unwrap();
        assert_eq!(alias.circuit, plan.carry.circuit, "private values must not choose topology");
        let values = c583_values(&plan, &raws, &alias);
        assert!(check_extra_values(&plan.extra_terms, &values).is_ok());
        let path = temp_path();
        drop(plan.write_witness(&raws, &path).unwrap());
        fs::remove_file(path).unwrap();

        let (bad_raws, start, tip) = c583_linked_raws(0x0700a8a7, 0x0700a8a8, None);
        let plan = Plan::build(start, tip).unwrap();
        let bad = crate::daa_integer::compile_carry(&q, 0x0700a8a7, 0x0700a8a8, true).unwrap();
        let values = c583_values(&plan, &bad_raws, &bad);
        assert!(check_extra_values(&plan.extra_terms, &values).is_err());
        // Mutant omits ONLY the child decoder's constraints; source binding
        // and header validity remain, so this named fault becomes satisfiable.
        let child_rows = bad.decoder_rows[1].clone();
        let mutant = plan.extra_terms.iter().filter(|term| !child_rows.contains(&term.row))
            .cloned().collect::<Vec<_>>();
        assert!(check_extra_values(&mutant, &values).is_ok(), "omitted decoder mutant must admit this fault");
        let path = temp_path();
        assert!(plan.write_witness(&bad_raws, &path).err().unwrap().contains("decoded carry"));
        assert!(!path.exists());
    }

    #[test]
    fn c583_each_fixed_height_is_a_proved_constraint() {
        let carry = crate::daa_integer::compile_carry(&crate::daa_count::q(),
            0x0700a8a7, 0x0700a8a7, true).unwrap();
        for slot in 0..HEADER_COUNT {
            let (raws, start, tip) = c583_linked_raws(0x0700a8a7, 0x0700a8a7, Some(slot));
            let plan = Plan::build(start, tip).unwrap();
            let values = c583_values(&plan, &raws, &carry);
            assert!(check_extra_values(&plan.extra_terms, &values).is_err());
            let rows = CARRY_HELPER_ROWS + 64 + slot * 32..CARRY_HELPER_ROWS + 64 + (slot + 1) * 32;
            let mutant = plan.extra_terms.iter().filter(|term| !rows.contains(&term.row))
                .cloned().collect::<Vec<_>>();
            assert!(check_extra_values(&mutant, &values).is_ok(), "height-only mutant {slot}");
            let path = temp_path();
            assert!(plan.write_witness(&raws, &path).err().unwrap().contains("fixed height"));
            assert!(!path.exists());
        }
    }

    #[test]
    fn c583_each_raw_compact_binding_is_required() {
        let (raws, start, tip) = c583_linked_raws(0x03001200, 0x02120000, None);
        let plan = Plan::build(start, tip).unwrap();
        let carry = crate::daa_integer::compile_carry(&crate::daa_count::q(),
            0x03001200, 0x02120000, true).unwrap();
        let values = c583_values(&plan, &raws, &carry);
        for (edge_index, slot) in CARRY_EDGE.into_iter().enumerate() {
            for bit in 0..32 {
                let wire = slot * HEADER_WIDTH + header_hash::SERIALIZER_OFFSET
                    + plan.template.serializer.layout.fields.n_bits[bit];
                let mut changed = values.clone();
                *changed.get_mut(&wire).unwrap() = Fr::one() - values[&wire];
                assert!(check_extra_values(&plan.extra_terms, &changed).is_err());
                let omitted = CARRY_HELPER_ROWS + edge_index * 32 + bit;
                let mutant = plan.extra_terms.iter().filter(|term| term.row != omitted)
                    .cloned().collect::<Vec<_>>();
                assert!(check_extra_values(&mutant, &changed).is_ok(),
                    "raw binding ({edge_index},{bit}) must be decisive");
            }
        }
    }

    #[test]
    fn c583_explicit_stream_matches_carry_and_removed_anchor_coefficients() {
        let plan = Plan::build(FIXTURE_START, FIXTURE_TIP).unwrap();
        assert_eq!(plan.extra_terms.len(), 12_072);
        assert_eq!(plan.released_terms.len(), 4096);
        let (r, u, v) = points(31);
        assert_eq!(plan.coefficients(&r, &u, &v).unwrap(),
            explicit_emitted_coefficients(&plan, &r, &u, &v, None));
        let carry_base = CARRY_OWNER * HEADER_WIDTH + CARRY_BANK.start;
        for left in [true, false] {
            let mut seen = 0;
            let mut released = 0;
            for slot in 0..HEADER_COUNT {
                plan.visit_endpoint(left, slot, &mut |edge| {
                    if edge.family_row >> BASE_ROW_LOG == FAMILY_CARRY {
                        assert_eq!(edge.source_slot, CARRY_OWNER);
                        seen += 1;
                    }
                    if edge.family_row >> BASE_ROW_LOG == FAMILY_BOUNDARY
                        && edge.source_slot == CARRY_OWNER
                        && CARRY_RELEASE.contains(&edge.term.row) { released += 1; }
                    Ok(())
                }).unwrap();
            }
            assert_eq!(seen, EXTRA_TERMS);
            assert_eq!(released, 0);
        }
        assert!(plan.extra_terms.iter().any(|term| term.gate.left == carry_base));
    }

    #[test]
    fn authentic_fixture_writes_one_log22_boolean_witness() {
        let raws = fixture_raws().unwrap();
        assert_eq!(raws.len(), 4);
        let plan = Plan::build(FIXTURE_START, FIXTURE_TIP).unwrap();
        let path = temp_path();
        let source = plan.write_witness(&raws, &path).unwrap();
        assert_eq!(source.input_len(), 1 << INPUT_LOG);
        assert_eq!(fs::metadata(&path).unwrap().len(), (1 << INPUT_LOG) / 8);
        drop(source);
        fs::remove_file(path).unwrap();
    }

    #[test]
    fn factored_coefficients_match_independent_literal_edge_weights() {
        let plan = Plan::build(FIXTURE_START, FIXTURE_TIP).unwrap();
        for seed in [17u64, 113] {
            let (r, u, v) = points(seed);
            let actual = plan.coefficients(&r, &u, &v).unwrap();
            let explicit = explicit_emitted_coefficients(&plan, &r, &u, &v, None);
            assert_eq!(actual, explicit);
        }
        let (r, u, v) = points(17);
        let expected = plan.coefficients(&r, &u, &v).unwrap();
        assert_ne!(
            explicit_emitted_coefficients(&plan, &r, &u, &v, Some(0)),
            expected,
            "omitting a real first event must change the terminal coefficients"
        );
        assert_ne!(
            explicit_emitted_coefficients(&plan, &r, &u, &v, Some(usize::MAX)),
            expected,
            "relocating a real first event must change its literal row weight"
        );
    }

    #[test]
    fn endpoint_passes_replay_equal_inventory_and_cross_slot_links() {
        let plan = Plan::build(FIXTURE_START, FIXTURE_TIP).unwrap();
        let mut totals = [0usize; 2];
        let mut adjacency_left = 0usize;
        let mut adjacency_right_slot0 = 0usize;
        for left in [true, false] {
            for slot in 0..HEADER_COUNT {
                plan.visit_endpoint(left, slot, &mut |edge| {
                    totals[left as usize] += 1;
                    if edge.family_row >> BASE_ROW_LOG == FAMILY_ADJACENCY {
                        if left {
                            adjacency_left += 1;
                        }
                        if !left && slot == 0 && edge.term.gate.right == 0 {
                            adjacency_right_slot0 += 1;
                        }
                    }
                    Ok(())
                })
                .unwrap();
            }
        }
        assert_eq!(totals, [TOTAL_TERMS, TOTAL_TERMS]);
        assert_eq!(adjacency_left, EXPECTED_ADJACENCY_TERMS);
        assert_eq!(
            adjacency_right_slot0, 512,
            "all 512 public anchor gates route through global right wire zero"
        );
    }

    #[test]
    fn isolated_link_projection_faults_hit_their_own_rows() {
        let raws = fixture_raws().unwrap();
        let plan = Plan::build(FIXTURE_START, FIXTURE_TIP).unwrap();
        let mut parents = [[0u8; 32]; HEADER_COUNT];
        let mut digests = [[0u8; 32]; HEADER_COUNT];
        for slot in 0..HEADER_COUNT {
            (parents[slot], digests[slot]) = projection_bytes(&plan.template, &raws[slot]);
        }
        assert!(projection_failure_rows(&plan, &parents, &digests).is_empty());

        for child in 1..HEADER_COUNT {
            let mut changed = parents;
            changed[child][7] ^= 1 << 3;
            assert_eq!(
                projection_failure_rows(&plan, &changed, &digests),
                vec![child * 512 + 7 * 8 + 3]
            );
        }
        let mut bad_start = parents;
        bad_start[0][0] ^= 1;
        assert_eq!(
            projection_failure_rows(&plan, &bad_start, &digests),
            vec![0]
        );
        let mut bad_tip = digests;
        bad_tip[3][31] ^= 0x80;
        assert_eq!(
            projection_failure_rows(&plan, &parents, &bad_tip),
            vec![3 * 512 + 511]
        );

        // Swapping complete valid local projections preserves each local
        // assignment's relation but breaks adjacency at the affected links.
        let mut swapped_parents = parents;
        let mut swapped_digests = digests;
        swapped_parents.swap(1, 2);
        swapped_digests.swap(1, 2);
        assert!(!projection_failure_rows(&plan, &swapped_parents, &swapped_digests).is_empty());
    }

    #[test]
    fn local_assignment_rejects_digest_booleanity_serializer_and_padding_faults() {
        let raw = fixture_raws().unwrap().remove(0);
        let mut local = segment_relation::build(Some(
            &crate::serializer::Fields::from_header(
                &ergo_header_core::Header::decode(&raw, None).unwrap(),
            )
            .unwrap(),
        ))
        .unwrap();
        segment_relation::attach_serializer_relation(&mut local).unwrap();
        let input = local.input.as_mut().unwrap();

        let selected_digest_product = local
            .boundary
            .terms
            .iter()
            .find(|term| {
                term.row == local.digest_rows.start
                    && !term.gate.c3.is_zero()
                    && input[term.gate.left].is_one()
            })
            .unwrap()
            .gate
            .right;
        input[local.digest_wires[0]] = Fr::from(2u64);
        input[selected_digest_product] = Fr::from(2u64);
        let failures = residual_rows(&local.boundary, input);
        assert_eq!(failures, vec![local.digest_boolean_rows.start]);

        let mut local = segment_relation::build(Some(
            &crate::serializer::Fields::from_header(
                &ergo_header_core::Header::decode(&raw, None).unwrap(),
            )
            .unwrap(),
        ))
        .unwrap();
        segment_relation::attach_serializer_relation(&mut local).unwrap();
        let field_wire =
            header_hash::SERIALIZER_OFFSET + local.serializer.layout.fields.timestamp[0];
        let prior = local.input.as_ref().unwrap()[field_wire];
        local.input.as_mut().unwrap()[field_wire] = Fr::one() - prior;
        let serializer_input = &local.input.as_ref().unwrap()[header_hash::SERIALIZER_OFFSET
            ..header_hash::SERIALIZER_OFFSET + local.serializer.circuit.input_len];
        assert!(!residual_rows(&local.serializer.circuit, serializer_input).is_empty());

        let mut local = segment_relation::build(Some(
            &crate::serializer::Fields::from_header(
                &ergo_header_core::Header::decode(&raw, None).unwrap(),
            )
            .unwrap(),
        ))
        .unwrap();
        segment_relation::attach_serializer_relation(&mut local).unwrap();
        let original = local.input.as_ref().unwrap().clone();
        // Attaching the serializer releases 2^18 old padding anchors.
        // The first surviving anchor is wire 917772, at row 274980.
        let first = local
            .boundary
            .terms
            .iter()
            .find(|term| term.row == local.remaining_padding_rows.start)
            .unwrap();
        assert_eq!(first.gate.left, 917_772);
        assert_eq!(local.remaining_padding_rows.start, 274_980);
        for (wire, row) in [
            (917_772, local.remaining_padding_rows.start),
            (HEADER_WIDTH - 1, local.remaining_padding_rows.end - 1),
        ] {
            let mut changed = original.clone();
            changed[wire] = Fr::one();
            assert_eq!(residual_rows(&local.boundary, &changed), vec![row]);
        }
    }

    #[test]
    fn selector_each_compression_copy_and_serializer_length_faults_are_rejected() {
        let raw = fixture_raws().unwrap().remove(0);
        let header = ergo_header_core::Header::decode(&raw, None).unwrap();
        let fields = crate::serializer::Fields::from_header(&header).unwrap();
        let mut local = segment_relation::build(Some(&fields)).unwrap();
        segment_relation::attach_serializer_relation(&mut local).unwrap();
        let core4 = local.core4.clone();
        let input = local.input.as_mut().unwrap();

        for selector in 0..5 {
            let mut changed = input.clone();
            let wire = header_hash::AUX_OFFSET + selector;
            changed[wire] = Fr::one() - changed[wire];
            assert!(
                !residual_rows(&local.boundary, &changed).is_empty(),
                "selector bit {selector} must be constrained"
            );
        }

        for copy in 0..header_hash::CORE_COPIES {
            let mut changed = input.clone();
            changed[copy * header_hash::CORE_WIDTH] = Fr::from(2u64);
            assert!(
                check_core_assignment(&core4, &changed).is_err(),
                "compression copy {copy} must reject a non-Boolean input"
            );
        }

        let mut changed = input.clone();
        let length_wire = header_hash::SERIALIZER_OFFSET + local.serializer.layout.length[0];
        changed[length_wire] = Fr::one() - changed[length_wire];
        let serializer_input = &changed[header_hash::SERIALIZER_OFFSET
            ..header_hash::SERIALIZER_OFFSET + local.serializer.circuit.input_len];
        assert!(
            check_circuit_assignment(&local.serializer.circuit, serializer_input).is_err(),
            "serializer length mutation must violate serializer rows"
        );
        assert!(
            check_native_serialization(&local.serializer.layout, &changed, &raw).is_err(),
            "serializer length mutation must disagree with the RAW"
        );
    }

    #[test]
    fn invalid_slot_count_and_noncanonical_raw_fail_before_success() {
        let plan = Plan::build(FIXTURE_START, FIXTURE_TIP).unwrap();
        let path = temp_path();
        assert!(plan.write_witness(&[], &path).is_err());
        assert!(!path.exists());
        assert!(plan.visit_endpoint(true, 4, &mut |_| Ok(())).is_err());
        let raws = fixture_raws().unwrap();
        let mut wrong = raws.clone();
        wrong[3].pop();
        assert!(plan.write_witness(&wrong, &path).is_err());
        assert!(!path.exists());
    }

    #[test]
    fn core_source_rejects_changed_canonical_shape_and_template_replicas() {
        let mut changed_shape = segment_relation::build(None).unwrap();
        changed_shape.core4.input_len -= 1;
        assert!(
            CoreEdgeSource::new(&changed_shape).is_err(),
            "canonical four-copy input shape mutation must be rejected"
        );

        let mut changed_template = segment_relation::build(None).unwrap();
        changed_template.core4.terms[0].row = 1 << 17;
        assert!(
            CoreEdgeSource::new(&changed_template).is_err(),
            "canonical source term outside its local row allocation must be rejected"
        );

        let mut changed_replica = segment_relation::build(None).unwrap();
        changed_replica.core4.terms[3 * BASE_CORE_TERMS].gate.c0 += Fr::one();
        assert!(
            CoreEdgeSource::new(&changed_replica).is_err(),
            "replica coefficient divergence from the canonical source must be rejected"
        );
    }

    fn residual_rows(circuit: &Circuit, input: &[Fr]) -> Vec<usize> {
        let mut rows = vec![Fr::zero(); circuit.row_count];
        for term in &circuit.terms {
            rows[term.row] += term.gate.evaluate(input);
        }
        rows.into_iter()
            .enumerate()
            .filter_map(|(row, value)| (!value.is_zero()).then_some(row))
            .collect()
    }
}

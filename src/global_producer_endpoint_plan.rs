//! Canonical global incidence over the existing Work, DAA, and released HEADER sources.
//! The ordinary API is an incidence/accounting join. The cfg(test) N3 frontend
//! additionally joins complete native X to the existing diagnostic GKR/PCS path.

use std::convert::TryFrom;

use crate::{
    daa_history_roster::{DaaHistoryRoster, OwnerClass},
    daa_integer::Epoch,
    daa_schedule_wiring::ScheduleDomain,
    daa_work_actions::DaaWorkActions,
    short_daa_layout::Profile,
    sparse::Term,
    sparse_stream_roster::{global_edge_row, EdgeTerm},
    work_tree_history_plan::WorkTreeHistoryPlan,
    work_tree_layout::WIDTH,
    work_tree_wiring::Family,
    work_tree_work::LOCAL_ROW_WIDTH,
};

const WORK_BASE_ROW_BITS: usize = 13;
const WORK_FAMILY_BITS: usize = 3;
const WORK_MEMBER_ROW_BITS: [usize; 6] = [0, 11, 8, 8, 8, 13];
const ROSTER_BASE_ROW_BITS: usize = 19;
const ROSTER_MEMBER_ROW_BITS: [usize; 1] = [19];
const SHORT_PROFILES: [Profile; 6] = [
    Profile::M2,
    Profile::M3,
    Profile::M4,
    Profile::M5,
    Profile::M6,
    Profile::M7,
];
const RIGHT0_U_ROUNDS: u128 = 21;
const U_ROUNDS: u128 = 21;
const V_ROUNDS: u128 = 21;
const FULL_OWNER_VECTORS_PER_SLOT: u128 = 43;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum GlobalProducerRole {
    Work,
    DaaRoster,
    ReleasedHeader,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum EndpointSide {
    Left,
    Right,
}

impl EndpointSide {
    fn is_left(self) -> bool {
        matches!(self, Self::Left)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ProducerEndpointShape {
    pub(crate) input_log: usize,
    pub(crate) row_log: usize,
    pub(crate) slot_log: usize,
    pub(crate) slots: usize,
    pub(crate) base_row_bits: usize,
    pub(crate) family_bits: usize,
    pub(crate) member_row_bits: Vec<usize>,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct OccurrenceCounts {
    pub(crate) emitted: u128,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct CheckedCensus {
    pub(crate) role: GlobalProducerRole,
    pub(crate) terms: u128,
    pub(crate) numeric_terms: u128,
    pub(crate) slot_count: u128,
    pub(crate) input_log: usize,
    pub(crate) row_log: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// One role's existing fallback lower bound. Cumulative field payload is not
/// RSS or I/O and does not price time, cache misses, or execution budgets.
pub(crate) struct FallbackAccounting {
    pub(crate) role: GlobalProducerRole,
    pub(crate) terms: u128,
    pub(crate) census_callbacks: u128,
    pub(crate) u_replay_callbacks: u128,
    pub(crate) u_scalar_right_reads: u128,
    pub(crate) v_replay_callbacks: u128,
    pub(crate) replay_callbacks: u128,
    pub(crate) line_owner_requests: u128,
    pub(crate) full_owner_vector_expansions: u128,
    pub(crate) expanded_field_elements: u128,
    pub(crate) field_bytes: u128,
    pub(crate) cumulative_expansion_bytes: u128,
    pub(crate) numeric_right0_u_scalar_reads: u128,
}

/// One immutable parent owns all three relations and their endpoint sources.
pub(crate) struct GlobalProducerEndpointPlan<'p> {
    parent: &'p WorkTreeHistoryPlan,
    work: crate::native_work_relation::NativeWorkRelation<'p>,
    roster: DaaHistoryRoster<'p>,
    numeric: DaaWorkActions<'p>,
    a4_release_terms: usize,
}

impl<'p> GlobalProducerEndpointPlan<'p> {
    pub(crate) fn new(parent: &'p WorkTreeHistoryPlan) -> Result<Self, String> {
        let work = crate::native_work_relation::NativeWorkRelation::new(parent)?;
        let roster = DaaHistoryRoster::compile(parent)?;
        let numeric = DaaWorkActions::new(parent)?;
        if !std::ptr::eq(parent, roster.endpoint_parent())
            || !std::ptr::eq(parent, numeric.endpoint_parent())
            || work.input_log() != 20usize.checked_add(parent.slot_log()).ok_or("Work input log overflow")?
            || work.row_log() != 16usize.checked_add(parent.slot_log()).ok_or("Work row log overflow")?
            || roster.input_log() != numeric.input_log()
            || roster.row_log() != 19usize.checked_add(parent.slot_log()).ok_or("roster row log overflow")?
        {
            return Err("global producer sources do not share the exact parent geometry".into());
        }
        let a4_release_terms = Self::derive_a4_release_terms(parent, &roster)?;
        Ok(Self {
            parent,
            work,
            roster,
            numeric,
            a4_release_terms,
        })
    }

    pub(crate) fn shape(&self, role: GlobalProducerRole) -> Result<ProducerEndpointShape, String> {
        let slot_log = self.parent.slot_log();
        let slots = 1usize
            .checked_shl(u32::try_from(slot_log).map_err(|_| "endpoint slot log width")?)
            .ok_or("endpoint slot count overflow")?;
        let slots_u64 = u64::try_from(slots).map_err(|_| "endpoint slot count width")?;
        if slots != self.parent.slots() || self.parent.headers() > slots_u64 {
            return Err("endpoint parent slot geometry changed".into());
        }
        let input_log = 20usize.checked_add(slot_log).ok_or("endpoint input log overflow")?;
        let (row_log, base_row_bits, family_bits, member_row_bits) = match role {
            GlobalProducerRole::Work => (
                16usize.checked_add(slot_log).ok_or("Work row log overflow")?,
                WORK_BASE_ROW_BITS,
                WORK_FAMILY_BITS,
                WORK_MEMBER_ROW_BITS.to_vec(),
            ),
            GlobalProducerRole::DaaRoster | GlobalProducerRole::ReleasedHeader => (
                19usize.checked_add(slot_log).ok_or("roster row log overflow")?,
                ROSTER_BASE_ROW_BITS,
                0,
                ROSTER_MEMBER_ROW_BITS.to_vec(),
            ),
        };
        if row_log >= usize::BITS as usize || input_log >= usize::BITS as usize {
            return Err("endpoint dimensions exceed the machine index width".into());
        }
        Ok(ProducerEndpointShape {
            input_log,
            row_log,
            slot_log,
            slots,
            base_row_bits,
            family_bits,
            member_row_bits,
        })
    }

    fn require_native_header_geometry(&self) -> Result<(), String> {
        let shape = self.shape(GlobalProducerRole::ReleasedHeader)?;
        if self.parent.headers() != 3
            || (shape.slot_log, shape.slots, shape.input_log, shape.row_log) != (2, 4, 22, 21)
        {
            return Err("native HEADER diagnostic requires exact N3/H2/input22/rows21".into());
        }
        Ok(())
    }

    /// Shared public statement framing. Producer ownership checks are separate;
    /// this routine depends only on the public plan and canonical key/C fields.
    fn bind_native_header_statement(
        &self, key_id: &[u8; 32], commitment_bytes: &[u8],
        transcript: &mut crate::transcript::Transcript,
    ) -> Result<(), String> {
        self.require_native_header_geometry()?;
        let source_binding = crate::packed_owner_assembly::NativePcsSource::public_binding(self.parent)?;
        let expected = crate::verifier_key::admit(22, include_bytes!("../fixtures/verifier-keys-v1/log22.vk"))?;
        // Complete every fallible check before publishing any statement bytes.
        if transcript.challenges() != 0 || key_id != expected.id() {
            return Err("native HEADER public key identity or challenged transcript".into());
        }
        crate::pcs::decode_commitment(commitment_bytes)?;
        transcript.append_bytes(b"native-header-role", b"ReleasedHEADER-N3-v1");
        transcript.append_bytes(b"native-header-source", &source_binding);
        for value in [3, 2, 4, 20, 22, 21] { transcript.append_u64(b"native-header-dimension", value); }
        transcript.append_bytes(b"native-header-key22", key_id);
        transcript.append_bytes(b"native-header-C", commitment_bytes);
        self.roster.bind(transcript);
        Ok(())
    }

    pub(crate) fn validate_edge(
        &self,
        role: GlobalProducerRole,
        edge: &EdgeTerm,
    ) -> Result<(), String> {
        let shape = self.shape(role)?;
        Self::validate_edge_shape(&shape, edge)
    }

    fn validate_edge_shape(shape: &ProducerEndpointShape, edge: &EdgeTerm) -> Result<(), String> {
        let row = global_edge_row(
            edge.source_slot,
            edge.family_row,
            shape.slot_log,
            shape.base_row_bits,
            shape.family_bits,
            &shape.member_row_bits,
        )?;
        if row != edge.term.row {
            return Err("global edge metadata does not reconstruct its stored canonical row".into());
        }
        let row_count = power_of_two(shape.row_log)?;
        let input_len = power_of_two(shape.input_log)?;
        if edge.term.row >= row_count
            || edge.term.gate.left >= input_len
            || edge.term.gate.right >= input_len
        {
            return Err("global edge row or endpoint is outside its declared domain".into());
        }
        Ok(())
    }

    fn pack_work_edge(
        shape: &ProducerEndpointShape,
        tag: usize,
        source_slot: usize,
        local_row: usize,
        mut term: Term,
    ) -> Result<EdgeTerm, String> {
        let member_bits = *WORK_MEMBER_ROW_BITS.get(tag).ok_or("Work family tag outside source roster")?;
        let member_rows = power_of_two(member_bits)?;
        if local_row >= member_rows {
            return Err("Work local row outside its ragged member range".into());
        }
        let untagged_source_row = checked_shift(source_slot, member_bits)?
            .checked_add(local_row)
            .ok_or("Work untagged source row overflow")?;
        if term.row != untagged_source_row {
            return Err("Work source emitter row differs from its row-owner metadata".into());
        }
        let family_row = checked_shift(tag, WORK_BASE_ROW_BITS)?
            .checked_add(local_row)
            .ok_or("Work family row overflow")?;
        let tagged_offset = checked_shift(
            tag,
            WORK_BASE_ROW_BITS
                .checked_add(shape.slot_log)
                .ok_or("Work family tag shift overflow")?,
        )?;
        let stored_row = untagged_source_row
            .checked_add(tagged_offset)
            .ok_or("Work tagged source row overflow")?;
        let reconstructed = global_edge_row(
            source_slot,
            family_row,
            shape.slot_log,
            WORK_BASE_ROW_BITS,
            WORK_FAMILY_BITS,
            &WORK_MEMBER_ROW_BITS,
        )?;
        if reconstructed != stored_row {
            return Err("Work source metadata and tag do not reconstruct one row".into());
        }
        term.row = stored_row;
        let edge = EdgeTerm {
            source_slot,
            family_row,
            term,
        };
        Self::validate_edge_shape(shape, &edge)?;
        Ok(edge)
    }

    fn canonical_work_edge(
        shape: &ProducerEndpointShape,
        term: Term,
    ) -> Result<EdgeTerm, String> {
        let family_shift = WORK_BASE_ROW_BITS
            .checked_add(shape.slot_log)
            .ok_or("Work canonical family shift overflow")?;
        let tag = term.row >> family_shift;
        let low_bits = WORK_BASE_ROW_BITS
            .checked_add(shape.slot_log)
            .ok_or("Work canonical row width overflow")?;
        let low_mask = power_of_two(low_bits)?
            .checked_sub(1)
            .ok_or("Work canonical row mask underflow")?;
        let untagged_source_row = term.row & low_mask;
        let member_bits = *WORK_MEMBER_ROW_BITS.get(tag).ok_or("Work canonical tag outside source roster")?;
        let local_mask = power_of_two(member_bits)?
            .checked_sub(1)
            .ok_or("Work local row mask underflow")?;
        let source_slot = untagged_source_row >> member_bits;
        let local_row = untagged_source_row & local_mask;
        let family_row = checked_shift(tag, WORK_BASE_ROW_BITS)?
            .checked_add(local_row)
            .ok_or("Work canonical family row overflow")?;
        let edge = EdgeTerm {
            source_slot,
            family_row,
            term,
        };
        Self::validate_edge_shape(shape, &edge)?;
        Ok(edge)
    }

    fn canonical_roster_edge(
        shape: &ProducerEndpointShape,
        term: Term,
    ) -> Result<EdgeTerm, String> {
        let mask = power_of_two(ROSTER_BASE_ROW_BITS)?
            .checked_sub(1)
            .ok_or("roster row mask underflow")?;
        let edge = EdgeTerm {
            source_slot: term.row >> ROSTER_BASE_ROW_BITS,
            family_row: term.row & mask,
            term,
        };
        Self::validate_edge_shape(shape, &edge)?;
        Ok(edge)
    }

    fn send_edge(
        shape: &ProducerEndpointShape,
        role: GlobalProducerRole,
        side: EndpointSide,
        endpoint_owner: usize,
        edge: EdgeTerm,
        sink: &mut impl FnMut(EdgeTerm) -> Result<(), String>,
        count: &mut u128,
    ) -> Result<(), String> {
        Self::validate_edge_shape(shape, &edge)?;
        let wire = if side.is_left() {
            edge.term.gate.left
        } else {
            edge.term.gate.right
        };
        if wire / WIDTH != endpoint_owner {
            return Err(format!("{} {:?} endpoint owner differs from its selected partition", role_name(role), side));
        }
        sink(edge)?;
        *count = count.checked_add(1).ok_or("endpoint occurrence count overflow")?;
        Ok(())
    }

    fn validate_header_locality(
        shape: &ProducerEndpointShape,
        owner: usize,
        edge: &EdgeTerm,
    ) -> Result<(), String> {
        Self::validate_edge_shape(shape, edge)?;
        if owner >= shape.slots || edge.source_slot != owner
            || edge.term.gate.left / WIDTH != owner
            || edge.term.gate.right / WIDTH != owner
        {
            return Err("released HEADER is not owner-local on both wires".into());
        }
        Ok(())
    }

    fn work_family(&self, tag: usize) -> Result<&Family, String> {
        match tag {
            2..=4 => self
                .parent
                .work_boundary()
                .links()
                .get(tag - 2)
                .ok_or_else(|| "Work link family missing".to_owned()),
            5 => {
                let mut matches = self.parent.topology().families.iter().filter(|family| {
                    family.name == "header_to_leaf_raw_length_nbits_height"
                });
                let family = matches.next().ok_or("Work released HEADER alias missing")?;
                if matches.next().is_some() {
                    return Err("Work released HEADER alias is ambiguous".into());
                }
                Ok(family)
            }
            _ => Err("Work endpoint family tag outside inverse sources".into()),
        }
    }

    fn visit_work_boundary_endpoint(
        &self,
        shape: &ProducerEndpointShape,
        side: EndpointSide,
        endpoint_owner: usize,
        sink: &mut impl FnMut(EdgeTerm) -> Result<(), String>,
    ) -> Result<u128, String> {
        let row_base = endpoint_owner
            .checked_mul(LOCAL_ROW_WIDTH)
            .ok_or("Work local endpoint row base overflow")?;
        let mut count = 0u128;
        let mut first_error: Option<String> = None;
        let emitted = self.parent.work_boundary().emit_slot(endpoint_owner, |term| {
            if first_error.is_some() {
                return;
            }
            let attempt = (|| -> Result<(), String> {
                let local_row = term
                    .row
                    .checked_sub(row_base)
                    .ok_or("Work local endpoint row precedes owner")?;
                if local_row >= LOCAL_ROW_WIDTH {
                    return Err("Work local endpoint row outside owner member".into());
                }
                let edge = Self::pack_work_edge(shape, 1, endpoint_owner, local_row, term)?;
                Self::send_edge(
                    shape,
                    GlobalProducerRole::Work,
                    side,
                    endpoint_owner,
                    edge,
                    sink,
                    &mut count,
                )
            })();
            if let Err(error) = attempt {
                first_error = Some(error);
            }
        });
        emitted?;
        if let Some(error) = first_error {
            return Err(error);
        }
        Ok(count)
    }

    pub(crate) fn visit_endpoint(
        &self,
        role: GlobalProducerRole,
        side: EndpointSide,
        endpoint_owner: usize,
        mut sink: impl FnMut(EdgeTerm) -> Result<(), String>,
    ) -> Result<OccurrenceCounts, String> {
        let shape = self.shape(role)?;
        if endpoint_owner >= shape.slots {
            return Err("global endpoint owner outside declared slot domain".into());
        }
        let mut emitted = 0u128;
        match role {
            GlobalProducerRole::Work => {
                let before = emitted;
                let reported = self.numeric.visit_endpoint_terms(
                    side.is_left(),
                    endpoint_owner,
                    |term| {
                        let source_slot = term.row;
                        let edge = Self::pack_work_edge(&shape, 0, source_slot, 0, term)?;
                        Self::send_edge(
                            &shape,
                            role,
                            side,
                            endpoint_owner,
                            edge,
                            &mut sink,
                            &mut emitted,
                        )
                    },
                )?;
                if usize_to_u128(reported)? != emitted.checked_sub(before).ok_or("Work numeric count underflow")? {
                    return Err("Work numeric endpoint count differs from its source".into());
                }

                let boundary_count = self.visit_work_boundary_endpoint(
                    &shape,
                    side,
                    endpoint_owner,
                    &mut sink,
                )?;
                emitted = emitted.checked_add(boundary_count).ok_or("Work endpoint count overflow")?;

                for tag in 2..=5 {
                    let family = self.work_family(tag)?;
                    let before = emitted;
                    family.emit_endpoint_terms(
                        self.parent.descriptor(),
                        side.is_left(),
                        endpoint_owner,
                        |source_slot, local_row, term| {
                            let edge = Self::pack_work_edge(
                                &shape,
                                tag,
                                source_slot,
                                local_row,
                                term,
                            )?;
                            Self::send_edge(
                                &shape,
                                role,
                                side,
                                endpoint_owner,
                                edge,
                                &mut sink,
                                &mut emitted,
                            )
                        },
                    )?;
                    let _family_count = emitted
                        .checked_sub(before)
                        .ok_or("Work family endpoint count underflow")?;
                }
            }
            GlobalProducerRole::DaaRoster => {
                let reported = self.roster.visit_history_endpoint_terms(
                    side.is_left(),
                    endpoint_owner,
                    |term| {
                        let edge = Self::canonical_roster_edge(&shape, term)?;
                        Self::send_edge(
                            &shape,
                            role,
                            side,
                            endpoint_owner,
                            edge,
                            &mut sink,
                            &mut emitted,
                        )
                    },
                )?;
                let reported_total = reported.lanes.iter().try_fold(0u128, |sum, lane| {
                    sum.checked_add(usize_to_u128(*lane)?)
                        .ok_or_else(|| "DAA endpoint lane count overflow".to_owned())
                })?;
                if reported_total != emitted {
                    return Err("DAA endpoint count differs from its canonical source".into());
                }
            }
            GlobalProducerRole::ReleasedHeader => {
                let source_owner =
                    u64::try_from(endpoint_owner).map_err(|_| "released HEADER owner width")?;
                let reported = self.roster.visit_header_terms(source_owner, |term| {
                    let edge = Self::canonical_roster_edge(&shape, term)?;
                    Self::validate_header_locality(&shape, endpoint_owner, &edge)?;
                    Self::send_edge(
                        &shape,
                        role,
                        side,
                        endpoint_owner,
                        edge,
                        &mut sink,
                        &mut emitted,
                    )
                })?;
                if usize_to_u128(reported.emitted)? != emitted {
                    return Err("released HEADER endpoint count differs from its owner source".into());
                }
            }
        }
        Ok(OccurrenceCounts { emitted })
    }

    pub(crate) fn global_census(
        &self,
        role: GlobalProducerRole,
    ) -> Result<CheckedCensus, String> {
        let shape = self.shape(role)?;
        let lanes = self.roster.term_census()?.lanes;
        let total_daa = lanes.iter().try_fold(0u128, |sum, lane| {
            sum.checked_add(usize_to_u128(*lane)?)
                .ok_or_else(|| "DAA global census overflow".to_owned())
        })?;
        let numeric_terms = usize_to_u128(lanes[2])?;
        let terms = match role {
            GlobalProducerRole::Work => self.work_census(&shape, numeric_terms)?,
            GlobalProducerRole::DaaRoster => total_daa,
            GlobalProducerRole::ReleasedHeader => self.header_census(&shape)?,
        };
        Ok(CheckedCensus {
            role,
            terms,
            numeric_terms: if role == GlobalProducerRole::ReleasedHeader {
                0
            } else {
                numeric_terms
            },
            slot_count: usize_to_u128(shape.slots)?,
            input_log: shape.input_log,
            row_log: shape.row_log,
        })
    }

    fn work_census(
        &self,
        shape: &ProducerEndpointShape,
        numeric_terms: u128,
    ) -> Result<u128, String> {
        let descriptor = self.parent.descriptor();
        let groups = self.parent.work_boundary().groups();
        let mut genuine_template = 0u128;
        let mut padding_template = 0u128;
        let mut padding_groups = 0usize;
        for group in groups {
            let terms = usize_to_u128(group.term_count)?;
            if group.name == "padding_arithmetic_zero" {
                padding_groups = padding_groups.checked_add(1).ok_or("Work padding group count")?;
                padding_template = padding_template.checked_add(terms).ok_or("Work padding template count")?;
            } else {
                genuine_template = genuine_template.checked_add(terms).ok_or("Work genuine template count")?;
            }
        }
        if padding_groups != 1 {
            return Err("Work boundary padding template is not unique".into());
        }
        let genuine = usize_to_u128(descriptor.genuine)?;
        let padding_slots = usize_to_u128(
            descriptor
                .leaves
                .checked_sub(descriptor.genuine)
                .ok_or("Work padded leaf count underflow")?,
        )?;
        let local = genuine
            .checked_mul(genuine_template)
            .and_then(|n| n.checked_add(padding_slots.checked_mul(padding_template)?))
            .ok_or("Work global local-term census overflow")?;

        let mut family_terms = 0u128;
        for (index, family) in self.work_families()?.into_iter().enumerate() {
            let count = family.count(descriptor)?;
            let member_bits: usize = if index == 3 { 13 } else { 8 };
            if count.global_input_bits != shape.input_log
                || count.row_log
                    != member_bits
                        .checked_add(shape.slot_log)
                        .ok_or("Work family row log overflow")?
            {
                return Err("Work family count geometry differs from the packed member".into());
            }
            family_terms = family_terms
                .checked_add(u128::from(count.terms))
                .ok_or("Work global family census overflow")?;
        }
        numeric_terms
            .checked_add(local)
            .and_then(|n| n.checked_add(family_terms))
            .ok_or_else(|| "Work global census overflow".to_owned())
    }

    fn work_families(&self) -> Result<Vec<&Family>, String> {
        let links = self.parent.work_boundary().links();
        let mut alias_matches = self.parent.topology().families.iter().filter(|family| {
            family.name == "header_to_leaf_raw_length_nbits_height"
        });
        let alias = alias_matches.next().ok_or("Work released HEADER alias missing")?;
        if alias_matches.next().is_some() {
            return Err("Work released HEADER alias is ambiguous".into());
        }
        Ok(vec![&links[0], &links[1], &links[2], alias])
    }

    fn header_census(&self, shape: &ProducerEndpointShape) -> Result<u128, String> {
        let _tail = self.roster.canonical_header_tail()?;
        let source = self.parent.header_boundary().canonical_circuit();
        if source.input_len != WIDTH
            || source.row_count != power_of_two(ROSTER_BASE_ROW_BITS)?
            || self.roster.headers() != self.parent.headers()
            || self.roster.slot_log() != shape.slot_log
        {
            return Err("released HEADER canonical factory geometry changed".into());
        }
        let canonical = usize_to_u128(source.terms.len())?;
        let retired = usize_to_u128(self.parent.retirement_counts().terms)?;
        let retained_per_slot = canonical
            .checked_sub(retired)
            .ok_or("released HEADER retirement exceeds its canonical factory")?;
        let retained = usize_to_u128(shape.slots)?
            .checked_mul(retained_per_slot)
            .ok_or("released HEADER retained census overflow")?;

        let schedule = ScheduleDomain::new(self.parent.headers(), shape.slot_log)?;
        let mature = u128::from(schedule.mature_retarget_count(Epoch::Legacy))
            .checked_add(u128::from(schedule.mature_retarget_count(Epoch::Eip)))
            .ok_or("released HEADER mature owner census overflow")?;
        let short = self.active_short_count()?;
        let released_owners = mature.checked_add(short).ok_or("released HEADER released owner count")?;
        let releases = released_owners
            .checked_mul(usize_to_u128(self.a4_release_terms)?)
            .ok_or("released HEADER A4 release census overflow")?;
        retained
            .checked_sub(releases)
            .ok_or_else(|| "released HEADER A4 release exceeds its retained census".to_owned())
    }

    fn active_short_count(&self) -> Result<u128, String> {
        let mut count = 0u128;
        for profile in SHORT_PROFILES {
            let owner = profile
                .child_height()
                .checked_sub(1)
                .ok_or("short profile owner underflow")?;
            let owner = u64::try_from(owner).map_err(|_| "short profile owner width")?;
            if owner >= self.parent.headers() {
                continue;
            }
            match self.roster.owner_class(owner)? {
                OwnerClass::Short(found) if found == profile => {
                    count = count.checked_add(1).ok_or("short release owner count overflow")?;
                }
                _ => return Err("active short profile differs from the roster owner class".into()),
            }
        }
        Ok(count)
    }

    fn derive_a4_release_terms(
        parent: &WorkTreeHistoryPlan,
        roster: &DaaHistoryRoster<'_>,
    ) -> Result<usize, String> {
        let _tail = roster.canonical_header_tail()?;
        let source = parent.header_boundary().canonical_circuit();
        let legacy = parent
            .header_boundary()
            .mature_layout(Epoch::Legacy)
            .a4_anchor_rows();
        let eip = parent
            .header_boundary()
            .mature_layout(Epoch::Eip)
            .a4_anchor_rows();
        if legacy != eip || legacy.start >= legacy.end {
            return Err("canonical A4 release row ranges differ".into());
        }
        let terms = source
            .terms
            .iter()
            .filter(|term| legacy.contains(&term.row))
            .count();
        if terms == 0 {
            return Err("canonical A4 release factory has no terms".into());
        }
        Ok(terms)
    }

    pub(crate) fn fallback_accounting(
        &self,
        role: GlobalProducerRole,
        field_bytes: u128,
    ) -> Result<FallbackAccounting, String> {
        if field_bytes == 0 {
            return Err("fallback field byte width must be positive".into());
        }
        let census = self.global_census(role)?;
        let census_callbacks = checked_mul_u128(census.terms, 2, "fallback census callbacks overflow")?;
        let u_replay_callbacks = checked_mul_u128(census.terms, U_ROUNDS, "fallback U replay callbacks overflow")?;
        let v_replay_callbacks = checked_mul_u128(census.terms, V_ROUNDS, "fallback V replay callbacks overflow")?;
        let replay_callbacks = u_replay_callbacks
            .checked_add(v_replay_callbacks)
            .ok_or("fallback replay callback total overflow")?;
        let line_owner_requests = census.slot_count;
        let full_owner_vector_expansions = checked_mul_u128(
            census.slot_count,
            FULL_OWNER_VECTORS_PER_SLOT,
            "fallback full-owner vector count overflow",
        )?;
        let expanded_field_elements = checked_mul_u128(
            full_owner_vector_expansions,
            usize_to_u128(WIDTH)?,
            "fallback expanded field-element count overflow",
        )?;
        let cumulative_expansion_bytes = checked_mul_u128(
            expanded_field_elements,
            field_bytes,
            "fallback cumulative expansion byte count overflow",
        )?;
        let numeric_right0_u_scalar_reads = if role == GlobalProducerRole::ReleasedHeader {
            0
        } else {
            checked_mul_u128(
                census.numeric_terms,
                RIGHT0_U_ROUNDS,
                "fallback numeric RIGHT0 scalar-read count overflow",
            )?
        };
        Ok(FallbackAccounting {
            role,
            terms: census.terms,
            census_callbacks,
            u_replay_callbacks,
            u_scalar_right_reads: u_replay_callbacks,
            v_replay_callbacks,
            replay_callbacks,
            line_owner_requests,
            full_owner_vector_expansions,
            expanded_field_elements,
            field_bytes,
            cumulative_expansion_bytes,
            numeric_right0_u_scalar_reads,
        })
    }

    #[cfg(test)]
    fn test_work_relation(&self) -> &crate::native_work_relation::NativeWorkRelation<'p> {
        &self.work
    }
}

fn role_name(role: GlobalProducerRole) -> &'static str {
    match role {
        GlobalProducerRole::Work => "Work",
        GlobalProducerRole::DaaRoster => "DAA roster",
        GlobalProducerRole::ReleasedHeader => "released HEADER",
    }
}

fn power_of_two(bits: usize) -> Result<usize, String> {
    1usize
        .checked_shl(u32::try_from(bits).map_err(|_| "power-of-two width")?)
        .ok_or_else(|| "power-of-two shift overflow".to_owned())
}

fn checked_shift(value: usize, bits: usize) -> Result<usize, String> {
    value
        .checked_mul(power_of_two(bits)?)
        .ok_or_else(|| "row shift overflow".to_owned())
}

fn usize_to_u128(value: usize) -> Result<u128, String> {
    u128::try_from(value).map_err(|_| "usize does not fit checked census".to_owned())
}

fn checked_mul_u128(left: u128, right: u128, error: &'static str) -> Result<u128, String> {
    left.checked_mul(right).ok_or_else(|| error.to_owned())
}

/// Public inputs for the fixed N3 HEADER diagnostic, not an authenticated
/// history/work statement. No native source, witness or prover setup is held.
#[derive(Clone, Debug)]
pub(crate) struct NativeHeaderPublicStatement {
    root: [u8; 32],
    total: [u8; 28],
    key_id: [u8; 32],
    commitment_bytes: Vec<u8>,
}

fn require_header_key22(key: &crate::verifier_key::AdmittedVerifierKey) -> Result<(), String> {
    let fixture = include_bytes!("../fixtures/verifier-keys-v1/log22.vk");
    let expected = crate::verifier_key::admit(22, fixture)?;
    if key.log_n() != 22 || key.id() != expected.id()
        || crate::pcs::encode(&dory_pcs::backends::arkworks::ArkworksVerifierSetup(key.verifier().clone()))?.as_slice() != fixture
    {
        return Err("native HEADER diagnostic requires the pinned key22".into());
    }
    Ok(())
}

impl NativeHeaderPublicStatement {
    pub(crate) fn new(
        root: [u8; 32], total: [u8; 28], key: &crate::verifier_key::AdmittedVerifierKey,
        commitment_bytes: &[u8],
    ) -> Result<Self, String> {
        require_header_key22(key)?;
        crate::pcs::decode_commitment(commitment_bytes)?;
        Ok(Self { root, total, key_id: *key.id(), commitment_bytes: commitment_bytes.to_vec() })
    }
}

/// Error attribution at the joined public verification boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum NativeHeaderVerificationError {
    Statement(String),
    GkrEncoding(String),
    PcsEncoding(String),
    Gkr(crate::gkr::GkrError),
    Pcs(String),
}

impl std::fmt::Display for NativeHeaderVerificationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Statement(error) => write!(f, "HEADER statement: {error}"),
            Self::GkrEncoding(error) => write!(f, "HEADER GKR encoding: {error}"),
            Self::PcsEncoding(error) => write!(f, "HEADER PCS encoding: {error}"),
            Self::Gkr(error) => write!(f, "HEADER {error}"),
            Self::Pcs(error) => write!(f, "HEADER PCS: {error}"),
        }
    }
}

impl std::error::Error for NativeHeaderVerificationError {}

/// Crate-local source-free consumer of one fixed diagnostic HEADER role.
/// Its parent/roster is public wiring, not native witness/factory state. A
/// successful claim is not validation of chain work, origin, PoW or history.
pub(crate) struct NativeHeaderPublicVerifier<'p, 'k> {
    plan: GlobalProducerEndpointPlan<'p>,
    statement: NativeHeaderPublicStatement,
    key: &'k crate::verifier_key::AdmittedVerifierKey,
    commitment: dory_pcs::backends::arkworks::ArkGT,
}

impl<'p, 'k> NativeHeaderPublicVerifier<'p, 'k> {
    pub(crate) fn new(
        parent: &'p WorkTreeHistoryPlan, statement: NativeHeaderPublicStatement,
        key: &'k crate::verifier_key::AdmittedVerifierKey,
    ) -> Result<Self, NativeHeaderVerificationError> {
        use NativeHeaderVerificationError::Statement;
        require_header_key22(key).map_err(Statement)?;
        if parent.descriptor().root != statement.root
            || parent.work_profile().total_be28 != statement.total || *key.id() != statement.key_id
        {
            return Err(Statement("public parent/statement/key identity mismatch".into()));
        }
        let commitment = crate::pcs::decode_commitment(&statement.commitment_bytes).map_err(Statement)?;
        let plan = GlobalProducerEndpointPlan::new(parent).map_err(Statement)?;
        plan.require_native_header_geometry().map_err(Statement)?;
        Ok(Self { plan, statement, key, commitment })
    }

    pub(crate) fn bind(&self, transcript: &mut crate::transcript::Transcript)
        -> Result<(), NativeHeaderVerificationError> {
        self.plan.bind_native_header_statement(&self.statement.key_id, &self.statement.commitment_bytes, transcript)
            .map_err(NativeHeaderVerificationError::Statement)
    }

    pub(crate) fn coefficients(
        &self, r: &[ark_bn254::Fr], u: &[ark_bn254::Fr], v: &[ark_bn254::Fr],
    ) -> Result<[ark_bn254::Fr; 4], String> {
        self.plan.roster.header_coefficients(r, u, v)
    }

    /// Derive q/value from GKR, then authenticate that exact claim and
    /// continuation with PCS. Failure never publishes a partial continuation.
    pub(crate) fn verify_on(
        &self, proof: &crate::gkr::GkrProof,
        opening: &dory_pcs::backends::arkworks::ArkDoryProof,
        transcript: &mut crate::transcript::Transcript,
    ) -> Result<crate::gkr::InputClaim, NativeHeaderVerificationError> {
        let mut next = transcript.clone();
        let mut prepared = next.clone();
        self.bind(&mut prepared)?;
        let claim = crate::gkr::verify_with_wiring(&[22], 1 << 21, proof, &mut next,
            |bound| *bound = prepared,
            |_layer, r, u, v| self.coefficients(r, u, v).map_err(|_| crate::gkr::GkrError::TerminalExpression),
        ).map_err(NativeHeaderVerificationError::Gkr)?;
        crate::pcs::verify_admitted(self.commitment, claim.value, &claim.point, opening, self.key, &mut next)
            .map_err(NativeHeaderVerificationError::Pcs)?;
        *transcript = next;
        Ok(claim)
    }

    pub(crate) fn verify_encoded_on(
        &self, proof_bytes: &[u8], opening_bytes: &[u8], transcript: &mut crate::transcript::Transcript,
    ) -> Result<crate::gkr::InputClaim, NativeHeaderVerificationError> {
        let proof = crate::gkr::decode_dimensions(&[22], proof_bytes)
            .map_err(NativeHeaderVerificationError::GkrEncoding)?;
        let opening = crate::pcs::decode_proof(opening_bytes, 22)
            .map_err(NativeHeaderVerificationError::PcsEncoding)?;
        self.verify_on(&proof, &opening, transcript)
    }
}

/// Sealed, bounded diagnostic only. Source, topology and coefficients all
/// belong to the same immutable parent; callers cannot replace its loader.
#[cfg(test)]
pub(crate) struct NativeReleasedHeaderAdmission<'p, 'a, 'n> {
    plan: &'p GlobalProducerEndpointPlan<'a>,
    source: &'p crate::packed_owner_assembly::NativePcsSource<'p, 'n>,
    grouped: crate::sparse_stream_roster::GroupedVAdmission,
}

#[cfg(test)]
pub(crate) struct NativeReleasedHeaderContext {
    committed: crate::packed::NativePcsCommitted,
    source_binding: [u8; 32],
    key_id: [u8; 32],
    commitment_bytes: Vec<u8>,
}

#[cfg(test)]
impl NativeReleasedHeaderContext {
    pub(crate) fn committed(&self) -> &crate::packed::NativePcsCommitted { &self.committed }
    pub(crate) fn commitment_bytes(&self) -> &[u8] { &self.commitment_bytes }
}

#[cfg(test)]
impl<'p, 'a, 'n> NativeReleasedHeaderAdmission<'p, 'a, 'n> {
    pub(crate) fn new(
        plan: &'p GlobalProducerEndpointPlan<'a>,
        source: &'p crate::packed_owner_assembly::NativePcsSource<'p, 'n>,
    ) -> Result<Self, String> {
        source.require_parent(plan.parent)?;
        let shape = plan.shape(GlobalProducerRole::ReleasedHeader)?;
        if plan.parent.headers() != 3 || (shape.slot_log, shape.slots, shape.input_log, shape.row_log) != (2, 4, 22, 21) {
            return Err("native HEADER diagnostic requires exact N3/H2/input22/rows21".into());
        }
        let mut expected = None;
        let mut total = 0usize;
        for owner in 0..4 {
            let mut counted = 0usize;
            let counts = plan.roster.visit_header_terms(owner, |term| {
                let edge = GlobalProducerEndpointPlan::canonical_roster_edge(&shape, term)?;
                GlobalProducerEndpointPlan::validate_header_locality(&shape, owner as usize, &edge)?;
                counted = counted.checked_add(1).ok_or("native HEADER term counter overflow")?;
                Ok(())
            })?;
            if counted == 0 || counts.emitted != counted || expected.is_some_and(|value| value != counted) {
                return Err("native HEADER N3 owners do not share one retained term census".into());
            }
            expected = Some(counted);
            total = total.checked_add(counted).ok_or("native HEADER total overflow")?;
        }
        if total as u128 != plan.global_census(GlobalProducerRole::ReleasedHeader)?.terms {
            return Err("native HEADER census differs from its complete canonical source".into());
        }
        let grouped = crate::sparse_stream_roster::GroupedVAdmission::try_new(
            2, &[0; 4], &[expected.ok_or("native HEADER retained group missing")?],
        )?;
        Ok(Self { plan, source, grouped })
    }

    pub(crate) fn load_owner(&self, owner: usize) -> Result<Vec<ark_bn254::Fr>, String> {
        self.source.require_parent(self.plan.parent)?;
        let packed = self.source.read_owner(owner)?;
        let mut values = Vec::with_capacity(WIDTH);
        for byte in packed.packed_bytes() {
            for bit in 0..8 { values.push(ark_bn254::Fr::from(((byte >> bit) & 1) as u64)); }
        }
        if values.len() != WIDTH || values.capacity() != WIDTH {
            return Err("native HEADER complete owner expansion width or capacity".into());
        }
        Ok(values)
    }

    pub(crate) fn visit_owner_terms(
        &self, owner: usize, sink: &mut dyn FnMut(Term) -> Result<(), String>,
    ) -> Result<(), String> { self.plan.c573_visit_header_owner_terms(owner,sink) }

    pub(crate) fn coefficients(&self, r: &[ark_bn254::Fr], u: &[ark_bn254::Fr], v: &[ark_bn254::Fr])
        -> Result<[ark_bn254::Fr; 4], String> {
        self.plan.roster.header_coefficients(r, u, v)
    }

    pub(crate) fn prepare_context(
        &self, setup: &crate::pcs::Setup, key: &crate::verifier_key::AdmittedVerifierKey,
    ) -> Result<NativeReleasedHeaderContext, String> {
        self.source.require_parent(self.plan.parent)?;
        let pinned = include_bytes!("../fixtures/verifier-keys-v1/log22.vk");
        let expected = crate::verifier_key::admit(22, pinned)?;
        let canonical = crate::pcs::encode(&dory_pcs::backends::arkworks::ArkworksVerifierSetup(setup.verifier.clone()))?;
        if setup.log_n != 22 || key.log_n() != 22 || key.id() != expected.id()
            || setup.id != *key.id() || canonical.as_slice() != pinned
        {
            return Err("native HEADER diagnostic setup/key22 identity".into());
        }
        // The only context constructor commits this exact source, before any
        // challenge. It cannot accept caller commitment bytes or a replacement X.
        let committed = crate::packed::commit_native(self.source, setup)?;
        let commitment_bytes = crate::pcs::encode_commitment(&committed.commitment())?;
        Ok(NativeReleasedHeaderContext {
            committed, source_binding: self.source.binding(), key_id: *key.id(), commitment_bytes,
        })
    }

    pub(crate) fn bind(&self, context: &NativeReleasedHeaderContext, transcript: &mut crate::transcript::Transcript)
        -> Result<(), String> {
        self.source.require_parent(self.plan.parent)?;
        let canonical = crate::pcs::encode_commitment(&context.committed.commitment())?;
        let public_binding = crate::packed_owner_assembly::NativePcsSource::public_binding(self.plan.parent)?;
        if context.source_binding != self.source.binding() || context.source_binding != public_binding
            || context.commitment_bytes != canonical
        {
            return Err("native HEADER diagnostic context identity".into());
        }
        self.plan.bind_native_header_statement(&context.key_id, &context.commitment_bytes, transcript)
    }

    pub(crate) fn prove_on(&self, context: &NativeReleasedHeaderContext, transcript: &mut crate::transcript::Transcript)
        -> Result<(crate::gkr::GkrProof, crate::gkr::InputClaim,
            crate::sparse_stream_roster::GroupedVStats, crate::sparse_stream_roster::BooleanUPreweightStats), String> {
        let mut next = transcript.clone();
        // Prepare every fallible binder check before entering an infallible
        // callback; no caller continuation is published on an error.
        let mut prepared = next.clone();
        self.bind(context, &mut prepared)?;
        let result = crate::sparse_stream_roster::prove_with_boolean_u_grouped_v_for_test(
            20, 2, 19, 0, &[19], Some(0), &self.grouped,
            |owner| self.load_owner(owner), &mut next, |bound| *bound = prepared,
            |owner, sink| self.visit_owner_terms(owner, sink),
            |r, u, v| self.coefficients(r, u, v),
        )?;
        *transcript = next;
        Ok(result)
    }

    pub(crate) fn verify_on(
        &self, context: &NativeReleasedHeaderContext, proof: &crate::gkr::GkrProof,
        transcript: &mut crate::transcript::Transcript,
    ) -> Result<crate::gkr::InputClaim, String> {
        let mut next = transcript.clone();
        let mut prepared = next.clone();
        self.bind(context, &mut prepared)?;
        let claim = crate::gkr::verify_with_wiring(&[22], 1 << 21, proof, &mut next,
            |bound| *bound = prepared,
            |_layer, r, u, v| self.coefficients(r, u, v).map_err(|_| crate::gkr::GkrError::TerminalExpression),
        ).map_err(|error| error.to_string())?;
        *transcript = next;
        Ok(claim)
    }
}

#[cfg(test)]
#[path = "global_producer_endpoint_plan_tests.rs"]
mod tests;

#[cfg(test)]
impl<'p> GlobalProducerEndpointPlan<'p>{
    fn c573_visit_header_owner_terms(&self,owner:usize,sink:&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String>{
        let shape = self.shape(GlobalProducerRole::ReleasedHeader)?;
        self.visit_endpoint(GlobalProducerRole::ReleasedHeader, EndpointSide::Left, owner, |edge| {
            GlobalProducerEndpointPlan::validate_header_locality(&shape, owner, &edge)?;
            let mut local = edge.term;
            local.row = local.row.checked_sub(owner.checked_mul(1 << 19).ok_or("native HEADER row offset overflow")?)
                .ok_or("native HEADER row normalization underflow")?;
            let offset = owner.checked_mul(WIDTH).ok_or("native HEADER wire offset overflow")?;
            local.gate.left = local.gate.left.checked_sub(offset).ok_or("native HEADER LEFT normalization underflow")?;
            local.gate.right = local.gate.right.checked_sub(offset).ok_or("native HEADER RIGHT normalization underflow")?;
            sink(local)
        })?;
        Ok(())
    
    }
}

/// PACKED diagnostic path; does not claim NativePcsSource provenance authority.
#[cfg(test)]
pub(crate) fn c573_prove_packed_header_on(lease:&crate::numeric_daa_authenticated::C573PcsLease<'_,'_>,
    transcript:&mut crate::transcript::Transcript)->Result<(Vec<u8>,Vec<u8>),String>
{
    lease.check()?;let plan=GlobalProducerEndpointPlan::new(lease.parent())?;
    plan.require_native_header_geometry()?;let shape=plan.shape(GlobalProducerRole::ReleasedHeader)?;
    let mut expected=None;let mut total=0usize;
    for owner in 0..4{
        let mut counted=0usize;
        let counts=plan.roster.visit_header_terms(owner,|term|{
            let edge=GlobalProducerEndpointPlan::canonical_roster_edge(&shape,term)?;
            GlobalProducerEndpointPlan::validate_header_locality(&shape,owner as usize,&edge)?;
            counted=counted.checked_add(1).ok_or("C573 HEADER count overflow")?;Ok(())
        })?;
        if counted==0||counts.emitted!=counted||expected.is_some_and(|n|n!=counted){return Err("C573 HEADER equal owner census".into());}
        expected=Some(counted);total=total.checked_add(counted).ok_or("C573 HEADER total overflow")?;
    }
    if total as u128!=plan.global_census(GlobalProducerRole::ReleasedHeader)?.terms{return Err("C573 HEADER global census".into());}
    let grouped=crate::sparse_stream_roster::GroupedVAdmission::try_new(2,&[0;4],&[expected.ok_or("C573 HEADER empty census")?])?;
    let statement=NativeHeaderPublicStatement::new(lease.parent().descriptor().root,
        lease.parent().work_profile().total_be28,lease.key(),lease.commitment_bytes())?;
    let public=NativeHeaderPublicVerifier::new(lease.parent(),statement,lease.key()).map_err(|e|e.to_string())?;
    let mut next=transcript.clone();let mut prepared=next.clone();public.bind(&mut prepared).map_err(|e|e.to_string())?;
    let(proof,claim,_,_)=crate::sparse_stream_roster::prove_with_boolean_u_grouped_v_for_test(
        20,2,19,0,&[19],Some(0),&grouped,
        |owner|{
            let view=lease.source().h2_boolean_view()?;view.require_same_source(lease.source())?;let bits=view.read_copy(owner)?;
            if bits.len()!=WIDTH||bits.capacity_bytes()>131072{return Err("C573 HEADER packed owner".into());}
            let mut values=Vec::new();values.try_reserve_exact(WIDTH).map_err(|_|"C573 HEADER allocation")?;
            if values.capacity()!=WIDTH{return Err("C573 HEADER capacity".into());}
            for i in 0..WIDTH{values.push(ark_bn254::Fr::from(bits.bit_at(i)as u64));}Ok(values)
        },&mut next,|bound|*bound=prepared,|owner,sink|plan.c573_visit_header_owner_terms(owner,sink),
        |r,u,v|public.coefficients(r,u,v))?;
    if claim.point.len()!=22||lease.source().evaluate(&claim.point)?!=claim.value{return Err("C573 HEADER original-X claim".into());}
    let opening=crate::packed::open(lease.committed(),lease.source(),&claim.point,lease.setup(),&mut next)?;
    let g=crate::gkr::encode_proof(&proof)?;let p=crate::pcs::encode_proof(&opening)?;
    if g.len()!=5024||p.len()!=29421{return Err("C573 HEADER encoded extent".into());}
    crate::gkr::decode_dimensions(&[22],&g)?;crate::pcs::decode_proof(&p,22)?;
    *transcript=next;Ok((g,p))
}

//! Typed owner-local source lease for exactly the two Eligible08 Map spans.
//!
//! This lease carries source bits and ordered relation terms; it does not
//! place rows, mutate a packed owner, or claim global X/ROW closure.

use super::*;
use crate::{
    daa_history_roster::OwnerClass,
    legacy_envelope_map::{Binding as MapBinding, Kind, Map},
    packed_owner_assembly::{
        HeaderSourceBinding, NativeTreeSourceLease,
    },
    sparse::Term,
    work_tree_layout::WIDTH,
};
use blake2::{digest::consts::U32, Blake2b, Digest};

const MAP_BASE: usize = 671_744;
const CONTEXT_BITS: usize = 8_192;
const LIVE_BITS: usize = 5_757;
const TAIL_BITS: usize = 7_898 - LIVE_BITS;
const CONTEXTS: usize = 2;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MapPairSourceAuthor {
    Header,
    Tree,
}

/// Resolve one imported bit only when exactly one typed source lease owns it,
/// and require the source role prescribed by the import kind.
pub(crate) fn resolve_typed_map_import(
    kind: Kind,
    from_header: Option<bool>,
    from_tree: Option<bool>,
) -> Result<(MapPairSourceAuthor, bool), String> {
    let (author, value) = match (from_header, from_tree) {
        (Some(_), Some(_)) => {
            return Err("C438 imported bit has ambiguous Header/Tree authors".into());
        }
        (None, None) => {
            return Err("C438 imported bit has no typed Header/Tree author".into());
        }
        (Some(value), None) => (MapPairSourceAuthor::Header, value),
        (None, Some(value)) => (MapPairSourceAuthor::Tree, value),
    };
    let required_author = match kind {
        Kind::Difficulty => MapPairSourceAuthor::Tree,
        Kind::Timestamp => MapPairSourceAuthor::Header,
    };
    if author != required_author {
        return Err(format!("C438 typed import author mismatch kind={kind:?}"));
    }
    Ok((author, value))
}

/// One imported bit and its exact typed physical source. Stored values are
/// bytes so the shared shape validator can reject malformed non-Boolean data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Eligible08MapPairImport {
    context: usize,
    kind: Kind,
    source_owner: usize,
    source_local: usize,
    source_width: usize,
    bit: usize,
    physical_wire: usize,
    source_binding: HeaderSourceBinding,
    author: MapPairSourceAuthor,
    value: u8,
}

impl Eligible08MapPairImport {
    pub(crate) fn context(&self) -> usize { self.context }
    pub(crate) fn kind(&self) -> Kind { self.kind }
    pub(crate) fn source_owner(&self) -> usize { self.source_owner }
    pub(crate) fn source_local(&self) -> usize { self.source_local }
    pub(crate) fn source_width(&self) -> usize { self.source_width }
    pub(crate) fn bit(&self) -> usize { self.bit }
    pub(crate) fn physical_wire(&self) -> usize { self.physical_wire }
    pub(crate) fn author(&self) -> MapPairSourceAuthor { self.author }
    pub(crate) fn value(&self) -> u8 { self.value }
}

/// A physical Map author claim. `value` is checked to be 0/1 by the shared
/// validator before a producer can use it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Eligible08MapPairCell {
    wire: usize,
    context: usize,
    offset: usize,
    value: u8,
}

impl Eligible08MapPairCell {
    pub(crate) fn physical_wire(&self) -> usize { self.wire }
    pub(crate) fn context(&self) -> usize { self.context }
    pub(crate) fn offset(&self) -> usize { self.offset }
    pub(crate) fn value(&self) -> bool { self.value == 1 }

    #[cfg(test)]
    pub(crate) fn synthetic_for_test(
        wire: usize, context: usize, offset: usize, value: u8,
    ) -> Self {
        Self { wire, context, offset, value }
    }
}

/// Parent- and cut-bound Map0/Map1 source evidence for one H21 owner.
#[derive(Clone)]
pub(crate) struct Eligible08MapPairLease {
    binding: HeaderSourceBinding,
    owner: usize,
    class: OwnerClass,
    cut_identity: Vec<u8>,
    maps: [Map; CONTEXTS],
    map_bindings: [MapBinding; CONTEXTS],
    imports: Vec<Eligible08MapPairImport>,
    imports_digest: [u8; 32],
    cells: Vec<Eligible08MapPairCell>,
    cells_digest: [u8; 32],
    terms: [Vec<Term>; CONTEXTS],
    tail_values: [Vec<u8>; CONTEXTS],
}

/// One physical Slack source bit in the exact packed owner domain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Eligible08SlackCell {
    wire: usize,
    context: usize,
    value: bool,
}

impl Eligible08SlackCell {
    pub(crate) fn physical_wire(&self) -> usize { self.wire }
    pub(crate) fn context(&self) -> usize { self.context }
    pub(crate) fn value(&self) -> bool { self.value }
}

/// Opaque paired Map and Slack source evidence minted from one generated
/// Map stage. It carries no packed-row mutation or completion authority.
#[derive(Clone)]
pub(crate) struct Eligible08MapSlackBundle {
    map_lease: Eligible08MapPairLease,
    slack_leases: [super::super::h21_eligible_slack::SlackLease; CONTEXTS],
}

/// First-anchor Map, Slack and both Score contexts from one generated Map
/// stage, retaining its native typed Upper source. No physical writer lives here.
#[cfg_attr(test, derive(Clone))]
pub(crate) struct Eligible08MapSlackAnchorBundle {
    map_slack: Eligible08MapSlackBundle,
    score: super::h21_eligible_score::FirstScoreAnchorSource,
}

/// Second-anchor Map, Slack, and full two-anchor Score replay from one
/// generated Map stage. Packed writing remains owned by the physical producer.
#[cfg_attr(test, derive(Clone))]
pub(crate) struct Eligible08MapSlackSecondAnchorBundle {
    map_slack: Eligible08MapSlackBundle,
    score: super::h21_eligible_score::SecondScoreAnchorSource,
}

impl Eligible08MapSlackSecondAnchorBundle {
    pub(crate) fn map_slack(&self) -> &Eligible08MapSlackBundle { &self.map_slack }

    pub(crate) fn checked_score_cells(&self, expected: &HeaderSourceBinding,
        owner: usize, class: OwnerClass,
    ) -> Result<Vec<Eligible08ScoreAnchorCell>, String> {
        self.map_slack.checked_slack_cells(expected, owner, class)?;
        self.score.checked_cells(expected, owner, class, &self.map_slack)
    }

    pub(crate) fn checked_score_terms(&self, expected: &HeaderSourceBinding,
        owner: usize, class: OwnerClass, context: usize,
    ) -> Result<Vec<Term>, String> {
        self.checked_score_cells(expected, owner, class)?;
        self.score.terms(expected, owner, class, &self.map_slack, context)
            .map(|terms| terms.to_vec())
    }

    pub(crate) fn checked_predecessor_packed(
        &self, first: &crate::packed_owner_assembly::NativePackedRow,
    ) -> Result<(), String> {
        self.score.checked_predecessor_packed(first)
    }

    #[cfg(test)]
    pub(crate) fn flip_first_r_lease_for_test(&mut self, context: usize)
        -> Result<(), String> { self.score.flip_first_r_lease_for_test(context) }

    #[cfg(test)]
    pub(crate) fn mutate_second_upper_for_test(&mut self, kind: usize)
        -> Result<(), String> { self.score.mutate_second_upper_for_test(kind) }

    #[cfg(test)]
    pub(crate) fn remove_zero_second_score_for_test(&mut self, context: usize)
        -> Result<usize, String> { self.score.remove_zero_second_score_for_test(context) }

    #[cfg(test)]
    pub(crate) fn swap_second_score_terms_for_test(&mut self, context: usize)
        -> Result<(), String> { self.score.swap_second_score_terms_for_test(context) }

    #[cfg(test)]
    pub(crate) fn mutate_second_binding_for_test(&mut self, kind: usize)
        -> Result<(), String> { self.score.mutate_second_binding_for_test(kind) }
}

impl Eligible08MapSlackAnchorBundle {
    pub(crate) fn map_slack(&self) -> &Eligible08MapSlackBundle { &self.map_slack }

    pub(crate) fn checked_score_cells(&self, expected: &HeaderSourceBinding,
        owner: usize, class: OwnerClass,
    ) -> Result<Vec<Eligible08ScoreAnchorCell>, String> {
        self.map_slack.checked_slack_cells(expected, owner, class)?;
        self.score.checked_cells(expected, owner, class, &self.map_slack)
    }

    pub(crate) fn checked_score_terms(&self, expected: &HeaderSourceBinding,
        owner: usize, class: OwnerClass, context: usize,
    ) -> Result<&[Term], String> {
        self.checked_score_cells(expected, owner, class)?;
        self.score.terms(context)
    }

    /// The C443 predecessor-bit negative uses this exact source/packed check;
    /// it does not fabricate the second native Upper publication.
    #[cfg(test)]
    pub(crate) fn checked_packed_for_test(
        &self, first: &crate::packed_owner_assembly::NativePackedRow,
    ) -> Result<(), String> {
        self.score.checked_packed(&self.map_slack, first)
    }

    /// Shape/arithmetic fixture with exact [55,55] Maps only; no native source
    /// construction or authentic packed producer is asserted.
    #[cfg(test)]
    pub(crate) fn synthetic_for_test() -> Result<(HeaderSourceBinding, Self), String> {
        let (expected, map_slack) = Eligible08MapSlackBundle::synthetic_for_test(
            417_790, OwnerClass::Carry)?;
        let score = super::h21_eligible_score::FirstScoreAnchorSource::synthetic_for_test(&map_slack)?;
        let bundle = Self { map_slack, score };
        bundle.checked_score_cells(&expected, 417_790, OwnerClass::Carry)?;
        Ok((expected, bundle))
    }

    /// Geometry/arithmetic fixture using the same binding as the ordinary ROW
    /// plan. Synthetic bits do not establish native physical authorship.
    #[cfg(test)]
    pub(crate) fn synthetic_for_plan_for_test(plan: &WorkTreeHistoryPlan)
        -> Result<Self, String> {
        let owner = 417_790;
        let class = OwnerClass::Carry;
        let expected = HeaderSourceBinding::for_plan(plan, owner)?;
        let map_lease = Eligible08MapPairLease::synthetic_valid_for_test(
            expected.clone(), owner, class, H21EligibleMapStage::source_maps()?,
        )?;
        let slack_leases = [
            super::super::h21_eligible_slack::SlackLease::synthetic_for_plan_bundle_test(
                plan, &expected, map_lease.map_binding(0)?, owner, 0,
            )?,
            super::super::h21_eligible_slack::SlackLease::synthetic_for_plan_bundle_test(
                plan, &expected, map_lease.map_binding(1)?, owner, 1,
            )?,
        ];
        let map_slack = Eligible08MapSlackBundle { map_lease, slack_leases };
        let score = super::h21_eligible_score::FirstScoreAnchorSource::synthetic_with_plan_for_test(
            &map_slack, Some(plan),
        )?;
        let bundle = Self { map_slack, score };
        bundle.checked_score_cells(&expected, owner, class)?;
        Ok(bundle)
    }

    #[cfg(test)]
    pub(crate) fn map_slack_mut_for_test(&mut self) -> &mut Eligible08MapSlackBundle {
        &mut self.map_slack
    }
    #[cfg(test)]
    pub(crate) fn remove_score_bit_for_test(&mut self, context: usize, index: usize)
        -> Result<(), String> { self.score.remove_bit_for_test(context, index) }
    #[cfg(test)]
    pub(crate) fn flip_score_bit_for_test(&mut self, context: usize, index: usize)
        -> Result<(), String> { self.score.flip_bit_for_test(context, index) }
    #[cfg(test)]
    pub(crate) fn alter_score_term_for_test(&mut self, context: usize, index: usize)
        -> Result<(), String> { self.score.alter_term_for_test(context, index) }
    #[cfg(test)]
    pub(crate) fn swap_score_contexts_for_test(&mut self) { self.score.swap_contexts_for_test(); }
    #[cfg(test)]
    pub(crate) fn swap_score_maps_for_test(&mut self) { self.score.swap_maps_for_test(); }
    #[cfg(test)]
    pub(crate) fn mutate_upper_for_test(&mut self, kind: usize)
        -> Result<(), String> { self.score.mutate_upper_for_test(kind) }
    #[cfg(test)]
    pub(crate) fn replace_score_map_for_test(&mut self, context: usize, map: Map)
        -> Result<(), String> { self.score.replace_map_for_test(context, map) }
}

impl Eligible08MapSlackBundle {
    pub(crate) fn map_lease(&self) -> &Eligible08MapPairLease { &self.map_lease }

    /// Structural fixture only. Its zero values and terms are synthetic and
    /// do not establish authenticated Map generation or physical authorship.
    #[cfg(test)]
    pub(crate) fn synthetic_for_test(
        owner: usize,
        class: OwnerClass,
    ) -> Result<(HeaderSourceBinding, Self), String> {
        let descriptor = crate::bank53_map::CutDescriptor::eligible08();
        let expected = HeaderSourceBinding::from_sink_for_test(
            [0x51; 32], [0x52; 28], [0x53; 32],
            descriptor.canonical_identity(), owner,
        );
        let maps = super::H21EligibleMapStage::source_maps()?;
        let map_lease = Eligible08MapPairLease::synthetic_valid_for_test(
            expected.clone(), owner, class, maps,
        )?;
        let slack_leases = [
            super::super::h21_eligible_slack::SlackLease::synthetic_for_bundle_test(
                &expected, map_lease.map_binding(0)?, owner, 0,
            )?,
            super::super::h21_eligible_slack::SlackLease::synthetic_for_bundle_test(
                &expected, map_lease.map_binding(1)?, owner, 1,
            )?,
        ];
        Ok((expected, Self { map_lease, slack_leases }))
    }

    pub(crate) fn checked_slack_cells(
        &self,
        expected: &HeaderSourceBinding,
        owner: usize,
        class: OwnerClass,
    ) -> Result<Vec<Eligible08SlackCell>, String> {
        self.map_lease.checked_cells(expected, owner, class)?;
        let owner_base = owner.checked_mul(WIDTH)
            .ok_or("C440 Slack owner base overflow")?;
        let mut cells = Vec::with_capacity(CONTEXTS * 387);
        for context in 0..CONTEXTS {
            let map_binding = self.map_lease.map_binding(context)?;
            let (bits, _) = self.slack_leases[context].checked_bundle_source(
                expected, map_binding, owner, context,
            )?;
            let domain = H21EligibleMapStage::slack_live(context)?;
            if bits.len() != domain.len() || bits.len() != 387 {
                return Err("C440 Slack ordered physical cell census".into());
            }
            for (local, value) in domain.zip(bits.iter().copied()) {
                let wire = owner_base.checked_add(local)
                    .ok_or("C440 Slack physical wire overflow")?;
                cells.push(Eligible08SlackCell { wire, context, value });
            }
        }
        if cells.len() != CONTEXTS * 387 {
            return Err("C440 Slack pair physical cell census".into());
        }
        Ok(cells)
    }

    pub(crate) fn checked_slack_terms(
        &self,
        expected: &HeaderSourceBinding,
        owner: usize,
        class: OwnerClass,
        context: usize,
    ) -> Result<&[Term], String> {
        if context >= CONTEXTS {
            return Err("C440 Slack context outside ordered pair".into());
        }
        self.map_lease.checked_cells(expected, owner, class)?;
        let map_binding = self.map_lease.map_binding(context)?;
        let (_, terms) = self.slack_leases[context].checked_bundle_source(
            expected, map_binding, owner, context,
        )?;
        Ok(terms)
    }

    #[cfg(test)]
    pub(crate) fn remove_slack_bit_for_test(
        &mut self, context: usize, index: usize,
    ) -> Result<(), String> {
        let lease = self.slack_leases.get_mut(context)
            .ok_or_else(|| "C440 test Slack context outside pair".to_string())?;
        lease.remove_bit_for_test(index)
    }

    #[cfg(test)]
    pub(crate) fn remove_slack_term_for_test(
        &mut self, context: usize, index: usize,
    ) -> Result<(), String> {
        let lease = self.slack_leases.get_mut(context)
            .ok_or_else(|| "C442 test Slack context outside pair".to_string())?;
        lease.remove_term_for_test(index)
    }

    #[cfg(test)]
    pub(crate) fn set_slack_bit_for_test(
        &mut self, context: usize, index: usize, value: bool,
    ) -> Result<(), String> {
        let lease = self.slack_leases.get_mut(context)
            .ok_or_else(|| "C440 test Slack context outside pair".to_string())?;
        lease.set_bit_for_test(index, value)
    }

    #[cfg(test)]
    pub(crate) fn alter_slack_row_term_for_test(
        &mut self, context: usize, index: usize,
    ) -> Result<(), String> {
        let lease = self.slack_leases.get_mut(context)
            .ok_or_else(|| "C440 test Slack context outside pair".to_string())?;
        lease.alter_row_term_for_test(index)
    }

    #[cfg(test)]
    pub(crate) fn swap_slack_contexts_for_test(&mut self) {
        self.slack_leases.swap(0, 1);
    }

    #[cfg(test)]
    pub(crate) fn mutate_map_cell_value_for_test(&mut self, index: usize) -> Result<(), String> {
        let value = self.map_lease.cells.get(index)
            .ok_or("C440 test Map cell index outside pair")?.value;
        if value > 1 { return Err("C440 test Map source already non-Boolean".into()); }
        self.map_lease.mutate_cell_value_for_test(index, value ^ 1);
        Ok(())
    }
}

impl Eligible08MapPairLease {
    pub(crate) fn checked_cells(
        &self,
        expected: &HeaderSourceBinding,
        owner: usize,
        class: OwnerClass,
    ) -> Result<&[Eligible08MapPairCell], String> {
        validate_shape(
            expected, &self.binding, owner, self.owner, class, self.class,
            &self.cut_identity, &self.maps, &self.map_bindings, &self.imports,
            &self.cells, &self.terms, &self.tail_values, &self.imports_digest,
            &self.cells_digest,
        )?;
        Ok(&self.cells)
    }

    pub(crate) fn reserves_local(&self, local: usize) -> bool {
        (0..CONTEXTS).any(|context| {
            let start = MAP_BASE + context * CONTEXT_BITS;
            (start..start + LIVE_BITS).contains(&local)
        })
    }

    pub(crate) fn imports(&self) -> &[Eligible08MapPairImport] { &self.imports }

    pub(crate) fn map_binding(&self, context: usize) -> Result<&MapBinding, String> {
        self.map_bindings.get(context)
            .ok_or_else(|| "C438 Map pair context outside ordered bindings".into())
    }

    pub(crate) fn terms(&self, context: usize) -> Result<&[Term], String> {
        self.terms.get(context).map(Vec::as_slice)
            .ok_or_else(|| "C438 Map pair context outside ordered pair".into())
    }

    pub(crate) fn binding(&self) -> &HeaderSourceBinding { &self.binding }

    #[cfg(test)]
    pub(crate) fn synthetic_for_test(
        binding: HeaderSourceBinding,
        owner: usize,
        class: OwnerClass,
        cut_identity: Vec<u8>,
        maps: [Map; CONTEXTS],
        map_bindings: [MapBinding; CONTEXTS],
        imports: Vec<Eligible08MapPairImport>,
        cells: Vec<Eligible08MapPairCell>,
        terms: [Vec<Term>; CONTEXTS],
        tail_values: [Vec<u8>; CONTEXTS],
    ) -> Self {
        let imports_digest = imports_digest(&imports);
        let cells_digest = cells_digest(&cells);
        Self { binding, owner, class, cut_identity, maps, map_bindings,
            imports, imports_digest, cells, cells_digest, terms, tail_values }
    }

    /// Build a shape-only fixture. Source bits and authors are synthetic and
    /// establish no authenticated import value or producer authorship.
    #[cfg(test)]
    pub(crate) fn synthetic_valid_for_test(
        binding: HeaderSourceBinding,
        owner: usize,
        class: OwnerClass,
        maps: [Map; CONTEXTS],
    ) -> Result<Self, String> {
        let descriptor = crate::bank53_map::CutDescriptor::eligible08();
        let cut_identity = descriptor.canonical_identity();
        let map_bindings = [maps[0].binding(), maps[1].binding()];
        let mut imports = Vec::new();
        for context in 0..CONTEXTS {
            for import in maps[context].imports(owner as u64)? {
                let source_owner = usize::try_from(import.owner)
                    .map_err(|_| "C438 synthetic import owner conversion")?;
                let mut source_binding = binding.clone();
                source_binding.owner = source_owner;
                let author = match import.kind {
                    Kind::Difficulty => MapPairSourceAuthor::Tree,
                    Kind::Timestamp => MapPairSourceAuthor::Header,
                };
                for bit in 0..import.width {
                    imports.push(Eligible08MapPairImport {
                        context,
                        kind: import.kind,
                        source_owner,
                        source_local: import.local,
                        source_width: import.width,
                        bit,
                        physical_wire: maps[context].input_index(import, bit)?,
                        source_binding: source_binding.clone(),
                        author,
                        value: 0,
                    });
                }
            }
        }
        let owner_base = owner.checked_mul(WIDTH)
            .ok_or("C438 synthetic owner wire overflow")?;
        let mut cells = Vec::with_capacity(CONTEXTS * LIVE_BITS);
        for context in 0..CONTEXTS {
            for offset in 0..LIVE_BITS {
                cells.push(Eligible08MapPairCell {
                    wire: owner_base + MAP_BASE + context * CONTEXT_BITS + offset,
                    context,
                    offset,
                    value: 0,
                });
            }
        }
        let terms = [
            crate::bank53_map::map_owner_terms_for_descriptor(
                &maps[0], owner as u64, 0, descriptor,
            )?,
            crate::bank53_map::map_owner_terms_for_descriptor(
                &maps[1], owner as u64, 1, descriptor,
            )?,
        ];
        let tail_values = [vec![0; TAIL_BITS], vec![0; TAIL_BITS]];
        Ok(Self::synthetic_for_test(
            binding, owner, class, cut_identity, maps, map_bindings,
            imports, cells, terms, tail_values,
        ))
    }

    #[cfg(test)]
    pub(crate) fn cells_mut_for_test(&mut self) -> &mut Vec<Eligible08MapPairCell> {
        &mut self.cells
    }
    /// A test-only synthetic value with a matching fixture digest. This is
    /// not an authenticated Map producer or a production resealing API.
    #[cfg(test)]
    pub(crate) fn reseal_cell_value_for_test(
        &mut self, index: usize, value: u8,
    ) -> Result<(), String> {
        if value > 1 {
            return Err("C503 test Map value must be Boolean".into());
        }
        self.cells.get_mut(index)
            .ok_or("C503 test Map cell outside pair")?.value = value;
        self.cells_digest = cells_digest(&self.cells);
        Ok(())
    }
    #[cfg(test)]
    pub(crate) fn imports_mut_for_test(&mut self) -> &mut Vec<Eligible08MapPairImport> {
        &mut self.imports
    }
    #[cfg(test)]
    pub(crate) fn tails_mut_for_test(&mut self) -> &mut [Vec<u8>; CONTEXTS] {
        &mut self.tail_values
    }
    #[cfg(test)]
    pub(crate) fn replace_map_for_test(&mut self, context: usize, map: Map) -> Result<(), String> {
        let target = self.maps.get_mut(context)
            .ok_or_else(|| "C438 test Map context outside pair".to_string())?;
        *target = map;
        Ok(())
    }
    #[cfg(test)]
    pub(crate) fn replace_terms_for_test(
        &mut self, context: usize, terms: Vec<Term>,
    ) -> Result<(), String> {
        let target = self.terms.get_mut(context)
            .ok_or_else(|| "C438 test term context outside pair".to_string())?;
        *target = terms;
        Ok(())
    }
}

impl<'a> H21EligibleContext<'a> {
    /// Mint one paired lease from the context's own generated Maps and exact
    /// native Header/Tree import authorities. No caller supplies bits/authors.
    pub(crate) fn map_pair_lease(
        &self,
        owner: usize,
    ) -> Result<Eligible08MapPairLease, String> {
        let (stage, generated) = self.map_stage(owner)?;
        self.map_pair_lease_from_generated(owner, &stage, &generated)
    }

    fn map_pair_lease_from_generated(
        &self,
        owner: usize,
        stage: &H21EligibleMapStage,
        generated: &[crate::legacy_envelope_map::OwnerRow; 2],
    ) -> Result<Eligible08MapPairLease, String> {
        let class = self.producer.roster.owner_class(owner as u64)?;
        let binding = HeaderSourceBinding::for_plan(self.producer.plan, owner)?;
        let cut_identity = self.descriptor.canonical_identity();
        let maps = self.maps.clone();
        let map_bindings = [maps[0].binding(), maps[1].binding()];
        if stage.owner != owner || stage.class != class
            || stage.parent_root != self.producer.plan.descriptor().root
            || stage.parent_total != self.producer.plan.work_profile().total_be28
            || stage.parent_profile != self.producer.input.profile()
            || stage.cut_identity != cut_identity
            || stage.map_bindings != map_bindings
        {
            return Err("C438 generated Map stage parent/cut/owner/class pair".into());
        }
        let mut cells = Vec::with_capacity(CONTEXTS * LIVE_BITS);
        let mut tail_values: [Vec<u8>; CONTEXTS] = [Vec::new(), Vec::new()];
        for context in 0..CONTEXTS {
            let row = &generated[context];
            if row.owner != owner as u64
                || row.binding != map_bindings[context]
                || row.bits.len() != crate::legacy_envelope_map::BANK
                || row.bits[LIVE_BITS..].iter().any(|bit| *bit)
            {
                return Err("C438 Map pair generated owner/binding/zero-tail".into());
            }
            for (offset, value) in row.bits[..LIVE_BITS].iter().copied().enumerate() {
                let local = MAP_BASE.checked_add(context * CONTEXT_BITS)
                    .and_then(|base| base.checked_add(offset))
                    .ok_or("C438 Map pair local wire overflow")?;
                let wire = owner.checked_mul(WIDTH).and_then(|base| base.checked_add(local))
                    .ok_or("C438 Map pair physical wire overflow")?;
                cells.push(Eligible08MapPairCell {
                    wire, context, offset, value: value as u8,
                });
            }
            tail_values[context] = row.bits[LIVE_BITS..].iter()
                .map(|bit| *bit as u8).collect();
        }

        let mut imports = Vec::new();
        let mut source_leases = std::collections::BTreeMap::new();
        for context in 0..CONTEXTS {
            for import in maps[context].imports(owner as u64)? {
                let source_owner = usize::try_from(import.owner)
                    .map_err(|_| "C438 imported source owner conversion")?;
                if !source_leases.contains_key(&source_owner) {
                    let source_binding = HeaderSourceBinding::for_plan(
                        self.producer.plan, source_owner,
                    )?;
                    let header = self.producer.header_source_lease(source_owner)?;
                    header.check_binding(&source_binding)?;
                    let tree = NativeTreeSourceLease::from_prefix(
                        self.producer.plan, self.producer.input, source_owner,
                    )?;
                    source_leases.insert(source_owner, (source_binding, header, tree));
                }
                let (source_binding, header, tree) = source_leases.get(&source_owner)
                    .ok_or("C438 typed source lease cache missing owner")?;
                for bit in 0..import.width {
                    let physical_wire = maps[context].input_index(import, bit)?;
                    let from_header = header.read_header_bit(source_binding, physical_wire)?;
                    let from_tree = tree.read_tree_bit(source_binding, physical_wire)?;
                    let (author, value) = resolve_typed_map_import(
                        import.kind, from_header, from_tree,
                    ).map_err(|error| format!("{error} wire={physical_wire}"))?;
                    let exported = self.producer.exports.bit(physical_wire)?;
                    if value != exported {
                        return Err(format!("C438 typed import/export value mismatch wire={physical_wire}"));
                    }
                    imports.push(Eligible08MapPairImport {
                        context,
                        kind: import.kind,
                        source_owner,
                        source_local: import.local,
                        source_width: import.width,
                        bit,
                        physical_wire,
                        source_binding: source_binding.clone(),
                        author,
                        value: value as u8,
                    });
                }
            }
        }

        let terms = stage.map_terms.clone();
        let imports_digest = imports_digest(&imports);
        let cells_digest = cells_digest(&cells);
        let lease = Eligible08MapPairLease {
            binding, owner, class, cut_identity, maps, map_bindings,
            imports, imports_digest, cells, cells_digest, terms, tail_values,
        };
        let expected_class = self.producer.roster.owner_class(owner as u64)?;
        lease.checked_cells(&lease.binding, owner, expected_class)?;
        Ok(lease)
    }

    /// Mint both typed source families from one generated Map stage. This
    /// source bundle does not claim packed X/ROW cells or establish closure.
    pub(crate) fn map_pair_slack_bundle(
        &self,
        owner: usize,
    ) -> Result<Eligible08MapSlackBundle, String> {
        H21EligibleMapStage::require_header_owned_slack_live(&self.parent_mask)?;
        let (stage, generated) = self.map_stage(owner)?;
        let map_lease = self.map_pair_lease_from_generated(owner, &stage, &generated)?;
        let slack_leases = [
            super::super::h21_eligible_slack::SlackLease::from_generated(&stage, 0, &generated[0])?,
            super::super::h21_eligible_slack::SlackLease::from_generated(&stage, 1, &generated[1])?,
        ];
        let bundle = Eligible08MapSlackBundle { map_lease, slack_leases };
        let binding = HeaderSourceBinding::for_plan(self.producer.plan, owner)?;
        let class = self.producer.roster.owner_class(owner as u64)?;
        bundle.checked_slack_cells(&binding, owner, class)?;
        for context in 0..CONTEXTS {
            bundle.checked_slack_terms(&binding, owner, class, context)?;
        }
        Ok(bundle)
    }

    /// Mint only owner417790's complete first-anchor source. All three source
    /// families consume the same generated Map stage and ordered Map rows.
    pub(crate) fn map_pair_slack_anchor_bundle(&self, owner: usize)
        -> Result<Eligible08MapSlackAnchorBundle, String> {
        if owner != 417_790
            || self.producer.roster.owner_class(owner as u64)? != OwnerClass::Carry {
            return Err("C441 first-anchor bundle requires owner417790 Carry".into());
        }
        H21EligibleMapStage::require_header_owned_slack_live(&self.parent_mask)?;
        let (stage, generated) = self.map_stage(owner)?;
        let map_lease = self.map_pair_lease_from_generated(owner, &stage, &generated)?;
        let slack_leases = [
            super::super::h21_eligible_slack::SlackLease::from_generated(&stage, 0, &generated[0])?,
            super::super::h21_eligible_slack::SlackLease::from_generated(&stage, 1, &generated[1])?,
        ];
        let score = self.first_score_anchor_from_stage(stage)?;
        let bundle = Eligible08MapSlackAnchorBundle {
            map_slack: Eligible08MapSlackBundle { map_lease, slack_leases }, score,
        };
        let binding = HeaderSourceBinding::for_plan(self.producer.plan, owner)?;
        bundle.checked_score_cells(&binding, owner, OwnerClass::Carry)?;
        Ok(bundle)
    }

    /// Mint owner845758's second-anchor bundle from one generated Map stage,
    /// retaining a checked full replay and the matching first-anchor source.
    pub(crate) fn map_pair_slack_second_anchor_bundle(&self, owner: usize,
        first: &Eligible08MapSlackAnchorBundle,
        premodern: &super::h21_eligible_score::PremodernRPublication,
    ) -> Result<Eligible08MapSlackSecondAnchorBundle, String> {
        if owner != 845_758
            || self.producer.roster.owner_class(owner as u64)? != OwnerClass::Carry {
            return Err("C443 second-anchor bundle requires owner845758 Carry".into());
        }
        H21EligibleMapStage::require_header_owned_slack_live(&self.parent_mask)?;
        let (stage, generated) = self.map_stage(owner)?;
        let map_lease = self.map_pair_lease_from_generated(owner, &stage, &generated)?;
        let slack_leases = [
            super::super::h21_eligible_slack::SlackLease::from_generated(&stage, 0, &generated[0])?,
            super::super::h21_eligible_slack::SlackLease::from_generated(&stage, 1, &generated[1])?,
        ];
        let map_slack = Eligible08MapSlackBundle { map_lease, slack_leases };
        let score = super::h21_eligible_score::SecondScoreAnchorSource::new(
            stage, premodern, &first.score, &first.map_slack,
        )?;
        let bundle = Eligible08MapSlackSecondAnchorBundle { map_slack, score };
        let binding = HeaderSourceBinding::for_plan(self.producer.plan, owner)?;
        bundle.checked_score_cells(&binding, owner, OwnerClass::Carry)?;
        Ok(bundle)
    }
}

fn validate_shape(
    expected_binding: &HeaderSourceBinding,
    binding: &HeaderSourceBinding,
    expected_owner: usize,
    owner: usize,
    expected_class: OwnerClass,
    class: OwnerClass,
    cut_identity: &[u8],
    maps: &[Map; CONTEXTS],
    map_bindings: &[MapBinding; CONTEXTS],
    imports: &[Eligible08MapPairImport],
    cells: &[Eligible08MapPairCell],
    terms: &[Vec<Term>; CONTEXTS],
    tail_values: &[Vec<u8>; CONTEXTS],
    expected_imports_digest: &[u8; 32],
    expected_cells_digest: &[u8; 32],
) -> Result<(), String> {
    let descriptor = crate::bank53_map::CutDescriptor::eligible08();
    let expected_cut = descriptor.canonical_identity();
    if binding != expected_binding || owner != expected_owner || binding.owner != owner
        || class != expected_class || cut_identity != expected_cut.as_slice()
        || maps.iter().any(|map| map.n() == 0 || map.h() != 21
            || map.binding().parent_root.is_some())
        || maps.iter().enumerate().any(|(context, map)| {
            map.n() != descriptor.terminals()[context] as u64
                || map.binding() != map_bindings[context]
        })
    {
        return Err("C438 Map pair parent/cut/owner/class/context binding".into());
    }
    if tail_values.iter().any(|tail| tail.len() != TAIL_BITS
        || tail.iter().any(|value| *value != 0))
    {
        return Err("C438 Map pair noncanonical or incomplete zero tail".into());
    }

    let expected_cell_count = CONTEXTS.checked_mul(LIVE_BITS)
        .ok_or("C438 Map pair cell count overflow")?;
    if cells.len() != expected_cell_count {
        return Err("C438 Map pair live cell census".into());
    }
    let owner_base = owner.checked_mul(WIDTH).ok_or("C438 Map pair owner base overflow")?;
    let mut cursor = 0;
    for context in 0..CONTEXTS {
        let base = MAP_BASE.checked_add(context * CONTEXT_BITS)
            .ok_or("C438 Map pair context base overflow")?;
        for offset in 0..LIVE_BITS {
            let cell = &cells[cursor];
            let expected_wire = owner_base.checked_add(base)
                .and_then(|wire| wire.checked_add(offset))
                .ok_or("C438 Map pair expected wire overflow")?;
            if cell.context != context || cell.offset != offset || cell.wire != expected_wire
                || cell.value > 1
            {
                return Err("C438 Map pair ordered live cell/domain/Boolean".into());
            }
            cursor += 1;
        }
    }
    if cells_digest(cells) != *expected_cells_digest {
        return Err("C438 Map pair generated live cell receipt drift".into());
    }

    let mut import_cursor = 0;
    for context in 0..CONTEXTS {
        for import in maps[context].imports(owner as u64)? {
            for bit in 0..import.width {
                let record = imports.get(import_cursor)
                    .ok_or("C438 Map pair missing typed import record")?;
                let wire = maps[context].input_index(import, bit)?;
                let source_owner = usize::try_from(import.owner)
                    .map_err(|_| "C438 import owner conversion")?;
                if record.context != context || record.kind != import.kind
                    || record.source_owner != source_owner
                    || record.source_local != import.local
                    || record.source_width != import.width || record.bit != bit
                    || record.physical_wire != wire || record.value > 1
                    || record.source_binding.owner != source_owner
                    || record.source_binding.root != binding.root
                    || record.source_binding.total != binding.total
                    || record.source_binding.profile != binding.profile
                    || record.source_binding.cut != binding.cut
                    || record.source_binding.layout != binding.layout
                    || record.author != (match import.kind {
                        Kind::Difficulty => MapPairSourceAuthor::Tree,
                        Kind::Timestamp => MapPairSourceAuthor::Header,
                    })
                {
                    return Err("C438 Map pair typed import record binding/order".into());
                }
                import_cursor += 1;
            }
        }
        let expected_terms = crate::bank53_map::map_owner_terms_for_descriptor(
            &maps[context], owner as u64, context, descriptor,
        )?;
        if terms[context] != expected_terms {
            return Err("C438 Map pair ordered term source/cut mismatch".into());
        }
    }
    if import_cursor != imports.len() {
        return Err("C438 Map pair extra typed import record".into());
    }
    if imports_digest(imports) != *expected_imports_digest {
        return Err("C438 Map pair typed source author/value receipt drift".into());
    }
    Ok(())
}

fn imports_digest(imports: &[Eligible08MapPairImport]) -> [u8; 32] {
    let mut h = Blake2b::<U32>::new();
    h.update(b"c438-eligible08-map-pair-imports-v1\n");
    for record in imports {
        h.update((record.context as u64).to_le_bytes());
        h.update([match record.kind { Kind::Difficulty => 0, Kind::Timestamp => 1 }]);
        h.update((record.source_owner as u64).to_le_bytes());
        h.update((record.source_local as u64).to_le_bytes());
        h.update((record.source_width as u64).to_le_bytes());
        h.update((record.bit as u64).to_le_bytes());
        h.update((record.physical_wire as u64).to_le_bytes());
        h.update(record.source_binding.root);
        h.update(record.source_binding.total);
        h.update(record.source_binding.profile);
        h.update((record.source_binding.cut.len() as u64).to_le_bytes());
        h.update(&record.source_binding.cut);
        h.update(record.source_binding.layout);
        h.update((record.source_binding.owner as u64).to_le_bytes());
        h.update([match record.author {
            MapPairSourceAuthor::Header => 0,
            MapPairSourceAuthor::Tree => 1,
        }]);
        h.update([record.value]);
    }
    h.finalize().into()
}

fn cells_digest(cells: &[Eligible08MapPairCell]) -> [u8; 32] {
    let mut h = Blake2b::<U32>::new();
    h.update(b"c438-eligible08-map-pair-live-cells-v1\n");
    for cell in cells {
        h.update((cell.wire as u64).to_le_bytes());
        h.update((cell.context as u64).to_le_bytes());
        h.update((cell.offset as u64).to_le_bytes());
        h.update([cell.value]);
    }
    h.finalize().into()
}

#[cfg(test)]
impl Eligible08MapPairLease {
    pub(crate) fn mutate_import_value_for_test(&mut self, index: usize, value: u8) {
        self.imports[index].value = value;
    }
    pub(crate) fn mutate_import_author_for_test(
        &mut self, index: usize, author: MapPairSourceAuthor,
    ) {
        self.imports[index].author = author;
    }
    pub(crate) fn mutate_import_binding_for_test(
        &mut self, index: usize, binding: HeaderSourceBinding,
    ) {
        self.imports[index].source_binding = binding;
    }
    pub(crate) fn mutate_import_binding_field_for_test(&mut self, index: usize, field: usize) {
        self.imports[index].source_binding =
            self.imports[index].source_binding.mutated_field_for_test(field);
    }
    pub(crate) fn mutate_cell_value_for_test(&mut self, index: usize, value: u8) {
        self.cells[index].value = value;
    }
    pub(crate) fn swap_cell_contexts_for_test(&mut self) {
        for cell in &mut self.cells { cell.context = 1 - cell.context; }
    }
    #[cfg(test)]
    pub(crate) fn remove_cell_for_test(&mut self, index: usize) {
        self.cells.remove(index);
    }
    #[cfg(test)]
    pub(crate) fn duplicate_cell_for_test(&mut self, index: usize) {
        let duplicate = self.cells[index].clone();
        self.cells.insert(index + 1, duplicate);
    }
    #[cfg(test)]
    pub(crate) fn shift_cell_wire_for_test(&mut self, index: usize, delta: usize) {
        self.cells[index].wire = self.cells[index].wire.saturating_add(delta);
    }
}

//! Private, source-replayed V/MAX/Cap loan for bounded consumer preparation.
//! Synthetic-provider tests exercise binding only; they make no H21 value claim.
use std::collections::BTreeMap;

use ark_bn254::Fr;
use ark_ff::{One, Zero};
use num_bigint::BigUint;

use crate::{
    h21_scheduled_max_cap::{CutDescriptor, OwnerCells, Patch, Prepared, Writer},
    packed_owner_assembly::{validate_native_plan_input, NativePrefix},
    work_tree_history_plan::WorkTreeHistoryPlan,
};

const FIRST_D: usize = 844_672;
const LAST_D: usize = 1_827_840;
const D_COUNT: usize = LAST_D - FIRST_D + 1;
const H21_HEADERS: usize = 1_827_840;
const H21_SLOT_LOG: usize = 21;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ParentIdentity {
    headers: usize,
    slot_log: usize,
    root: [u8; 32],
    total: [u8; 28],
    profile: [u8; 32],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct DSourceTag {
    first_height: usize,
    last_height: usize,
    count: usize,
}

const SOURCE_TAG: DSourceTag = DSourceTag {
    first_height: FIRST_D,
    last_height: LAST_D,
    count: D_COUNT,
};

/// This private trait has only a validated NativePrefix adapter and a sealed
/// test fixture implementation. It cannot be supplied through a public API.
trait DifficultySource {
    fn identity(&self) -> Result<ParentIdentity, String>;
    fn compact_n_bits(&self, height: usize) -> Result<u32, String>;
}

struct NativeSource<'a> {
    plan: &'a WorkTreeHistoryPlan,
    prefix: &'a NativePrefix,
}

impl DifficultySource for NativeSource<'_> {
    fn identity(&self) -> Result<ParentIdentity, String> {
        validate_native_plan_input(self.plan, self.prefix)?;
        if self.plan.headers() != H21_HEADERS as u64
            || self.plan.slot_log() != H21_SLOT_LOG
            || self.prefix.header_count() != H21_HEADERS
        {
            return Err("V loan requires the pinned H21 parent geometry".into());
        }
        Ok(ParentIdentity {
            headers: self.prefix.header_count(),
            slot_log: self.plan.slot_log(),
            root: self.prefix.root(),
            total: self.prefix.total_be28(),
            profile: self.prefix.profile(),
        })
    }

    fn compact_n_bits(&self, height: usize) -> Result<u32, String> {
        self.prefix.compact_n_bits(height)
    }
}

struct DStream<'a> {
    source: &'a dyn DifficultySource,
    next_height: usize,
    yielded: usize,
    first_d: Option<BigUint>,
    failure: Option<String>,
}

impl Iterator for DStream<'_> {
    type Item = (usize, BigUint);

    fn next(&mut self) -> Option<Self::Item> {
        if self.next_height > LAST_D || self.failure.is_some() {
            return None;
        }
        let height = self.next_height;
        self.next_height += 1;
        match self.source.compact_n_bits(height)
            .and_then(crate::work_tree_work::native_decode)
        {
            Ok(d) => {
                if self.first_d.is_none() { self.first_d=Some(d.clone()); }
                self.yielded += 1;
                Some((height, d))
            }
            Err(error) => {
                self.failure = Some(format!("V native D source height={height}: {error}"));
                None
            }
        }
    }
}

struct PreparedReplay { prepared: Prepared, first_d: BigUint }

fn prepared_from_source(source: &dyn DifficultySource) -> Result<PreparedReplay, String> {
    prepared_from_source_with_descriptor(source,CutDescriptor::diagnostic08())
}

fn prepared_from_source_with_descriptor(source:&dyn DifficultySource,descriptor:CutDescriptor)->Result<PreparedReplay,String> {
    let mut stream = DStream {
        source,
        next_height: FIRST_D,
        yielded: 0,
        first_d: None,
        failure: None,
    };
    let prepared_result = Prepared::from_d_iter_with_descriptor(descriptor,&mut stream);
    if let Some(error) = stream.failure.take() {
        return Err(error);
    }
    let prepared = prepared_result?;
    if stream.yielded != D_COUNT || stream.next_height != LAST_D + 1 {
        return Err("V native D source count/endpoint mismatch".into());
    }
    let first_d=stream.first_d.take().ok_or("V native D first value missing")?;
    Ok(PreparedReplay { prepared, first_d })
}

/// Immutable source-owned snapshot. No per-height D vector is retained.
pub(crate) struct NativeVLoan {
    parent: ParentIdentity,
    source: DSourceTag,
    descriptor: CutDescriptor,
    prepared: Prepared,
}

impl NativeVLoan {
    /// Issue replays the complete D stream once. This immutable projection
    /// checks the consuming parent once, rather than replaying it per origin.
    pub(crate) fn score_spans(
        &self,
        plan:&WorkTreeHistoryPlan,
        prefix:&NativePrefix,
        context:usize,
    )->Result<Vec<crate::h21_scheduled_max_cap::ScoreSpan>,String> {
        self.score_spans_with_descriptor(plan,prefix,context,CutDescriptor::diagnostic08())
    }

    pub(crate) fn score_spans_eligible08(
        &self,plan:&WorkTreeHistoryPlan,prefix:&NativePrefix,context:usize,
    )->Result<Vec<crate::h21_scheduled_max_cap::ScoreSpan>,String> {
        self.score_spans_with_descriptor(plan,prefix,context,CutDescriptor::eligible08())
    }

    fn score_spans_with_descriptor(&self,plan:&WorkTreeHistoryPlan,prefix:&NativePrefix,
        context:usize,descriptor:CutDescriptor,
    )->Result<Vec<crate::h21_scheduled_max_cap::ScoreSpan>,String> {
        if self.descriptor!=descriptor || self.prepared.descriptor()!=descriptor {
            return Err("Score V cut descriptor mismatch".into());
        }
        if self.source!=SOURCE_TAG || (NativeSource {plan,prefix}).identity()?!=self.parent {
            return Err("Score V source parent/range mismatch".into());
        }
        self.prepared.score_spans(context)
    }

    pub(crate) fn issue(
        plan: &WorkTreeHistoryPlan,
        prefix: &NativePrefix,
    ) -> Result<Self, String> {
        let source = NativeSource { plan, prefix };
        Self::issue_from(&source)
    }

    pub(crate) fn issue_eligible08(plan:&WorkTreeHistoryPlan,prefix:&NativePrefix)->Result<Self,String> {
        Self::issue_from_with_descriptor(&NativeSource {plan,prefix},CutDescriptor::eligible08())
    }

    fn issue_from(source: &dyn DifficultySource) -> Result<Self, String> {
        Self::issue_from_with_descriptor(source,CutDescriptor::diagnostic08())
    }

    fn issue_from_with_descriptor(source:&dyn DifficultySource,descriptor:CutDescriptor)->Result<Self,String> {
        let parent = source.identity()?;
        let replay = prepared_from_source_with_descriptor(source,descriptor)?;
        Ok(Self { parent, source: SOURCE_TAG, descriptor, prepared:replay.prepared })
    }

    /// Replays every compact D source before exposing patches to the consumer.
    pub(crate) fn consume(
        &self,
        plan: &WorkTreeHistoryPlan,
        prefix: &NativePrefix,
        owner: usize,
        consumer: &Prepared,
        residual: impl FnOnce(&Patch) -> Result<(), String>,
        destination: &mut VLoanDestination,
    ) -> Result<(), String> {
        let source = NativeSource { plan, prefix };
        self.consume_from(&source, owner, consumer, None, residual, destination)
    }

    fn consume_from(
        &self,
        source: &dyn DifficultySource,
        owner: usize,
        consumer: &Prepared,
        supplied_tags: Option<&[Writer]>,
        residual: impl FnOnce(&Patch) -> Result<(), String>,
        destination: &mut VLoanDestination,
    ) -> Result<(), String> {
        if self.source != SOURCE_TAG {
            return Err("V loan source range/count mismatch".into());
        }
        if self.descriptor!=self.prepared.descriptor() || self.descriptor!=consumer.descriptor() {
            return Err("V loan cut descriptor mismatch".into());
        }
        if destination.patches.contains_key(&owner) {
            return Err("V loan destination duplicate owner".into());
        }
        let replayed_parent = source.identity()?;
        let replayed = prepared_from_source_with_descriptor(source,self.descriptor)?;
        if replayed_parent != self.parent || !self.prepared.source_replay_matches(&replayed.prepared) {
            return Err("V loan immutable source replay mismatch".into());
        }

        let source_patch = self.prepared.owner_patch(owner)?;
        let consumer_patch = consumer.owner_patch(owner)?;
        let consumer_tags = consumer_patch.writers();
        let tags = supplied_tags.unwrap_or(&consumer_tags);
        let expected = expected_writer_tags(owner);
        if !expected.is_empty() && tags != expected.as_slice() {
            return Err("V writer/context/end/origin binding mismatch".into());
        }
        if !source_patch.source_replay_matches(&consumer_patch) {
            return Err("V consumer patch source/value mismatch".into());
        }
        let mut checked = OwnerCells::new(owner)?;
        source_patch.apply(&mut checked)?;
        residual(&source_patch)?;
        destination.patches.insert(owner, source_patch);
        Ok(())
    }

    /// Replays one native D stream and returns the three validated source
    /// patches, the first decoded D, and both 65-bit Cap values. This helper
    /// does not publish patches into a consumer destination.
    #[cfg(test)]
    pub(crate) fn replay_group(
        &self,
        plan:&WorkTreeHistoryPlan,
        prefix:&NativePrefix,
    )->Result<NativeVGroup,String> {
        let source=NativeSource {plan,prefix};
        self.replay_group_from(&source)
    }

    #[cfg(test)]
    fn replay_group_from(
        &self,
        source:&dyn DifficultySource,
    )->Result<NativeVGroup,String> {
        const OWNERS:[usize;3]=[844_670,844_798,845_759];
        if self.source!=SOURCE_TAG {
            return Err("V loan source range/count mismatch".into());
        }
        let replayed_parent=source.identity()?;
        if replayed_parent!=self.parent {
            return Err("V loan immutable source replay mismatch".into());
        }
        if self.descriptor!=self.prepared.descriptor() {
            return Err("V loan cut descriptor mismatch".into());
        }
        let replay=prepared_from_source_with_descriptor(source,self.descriptor)?;
        if !self.prepared.source_replay_matches(&replay.prepared) {
            return Err("V loan immutable source replay mismatch".into());
        }
        let mut patch_vec=Vec::with_capacity(OWNERS.len());
        for owner in OWNERS { patch_vec.push(self.prepared.owner_patch(owner)?); }
        let patches:[Patch;3]=patch_vec.try_into()
            .map_err(|_|"V group patch count".to_string())?;
        validate_group_patches(&self.prepared,&patches)?;
        let cap_values=[patches[2].cap_value_65(0)?,patches[2].cap_value_65(1)?];
        for (owner,patch) in OWNERS.into_iter().zip(patches.iter()) {
            let mut cells=OwnerCells::new(owner)?;
            patch.apply(&mut cells)?;
        }
        Ok(NativeVGroup {patches,first_d:replay.first_d,cap_values})
    }

    #[cfg(test)]
    fn prepared_for_test(&self) -> &Prepared { &self.prepared }
}

#[cfg(test)]
#[derive(Clone,Debug,PartialEq,Eq)]
pub(crate) struct NativeVGroup {
    pub(crate) patches:[Patch;3],
    pub(crate) first_d:BigUint,
    pub(crate) cap_values:[BigUint;2],
}

#[cfg(test)]
fn validate_group_patches(prepared:&Prepared,patches:&[Patch;3])->Result<(),String> {
    for (owner,patch) in [844_670,844_798,845_759].into_iter().zip(patches) {
        if patch.writers()!=expected_writer_tags(owner) {
            return Err("V group writer/context/end/origin binding mismatch".into());
        }
        let expected=prepared.owner_patch(owner)?;
        if !expected.source_replay_matches(patch) {
            return Err("V group source patch owner/value mismatch".into());
        }
    }
    Ok(())
}

fn expected_writer_tags(owner: usize) -> Vec<Writer> {
    match owner {
        844_670 => vec![
            Writer::Max { context: 0, end: 844_672 },
            Writer::Max { context: 1, end: 844_672 },
        ],
        844_798 => vec![
            Writer::Max { context: 0, end: 844_800 },
            Writer::Max { context: 1, end: 844_800 },
        ],
        845_759 => vec![
            Writer::Cap { context: 0, origin: 845_760 },
            Writer::Cap { context: 1, origin: 845_760 },
        ],
        _ => Vec::new(),
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct VLoanDestination {
    patches: BTreeMap<usize, Patch>,
}

#[cfg(test)]
struct SyntheticSource {
    parent: ParentIdentity,
    changed_height: Option<usize>,
    compact: u32,
    reads: std::cell::Cell<usize>,
}

#[cfg(test)]
impl SyntheticSource {
    fn canonical() -> Self {
        Self {
            parent: ParentIdentity {
                headers: H21_HEADERS,
                slot_log: H21_SLOT_LOG,
                root: [0x41; 32],
                total: [0x52; 28],
                profile: [0x63; 32],
            },
            changed_height: None,
            compact: 0x0101_0000,
            reads:std::cell::Cell::new(0),
        }
    }

    fn changed_d() -> Self {
        Self { changed_height: Some(FIRST_D), compact: 0x0102_0000, ..Self::canonical() }
    }

    fn changed_parent() -> Self {
        let mut source=Self::canonical();
        source.parent.root[0]^=1;
        source
    }
}

#[cfg(test)]
impl DifficultySource for SyntheticSource {
    fn identity(&self) -> Result<ParentIdentity, String> { Ok(self.parent) }

    fn compact_n_bits(&self, height: usize) -> Result<u32, String> {
        self.reads.set(self.reads.get()+1);
        Ok(if self.changed_height == Some(height) { self.compact } else { 0x0101_0000 })
    }
}

#[cfg(test)]
#[path = "native_v_max_cap_loan_tests.rs"]
mod tests;

#[cfg(test)]
mod eligible_calendar_tests {
    use super::*;
    #[test]
    fn c164_eligible_native_loan_replays_same_descriptor_and_rejects_profile_swap() {
        let source=SyntheticSource::canonical();
        let eligible=NativeVLoan::issue_from_with_descriptor(&source,CutDescriptor::eligible08()).unwrap();
        let diagnostic=NativeVLoan::issue_from(&source).unwrap();
        assert_eq!(eligible.parent,diagnostic.parent);
        assert_eq!(diagnostic.descriptor,CutDescriptor::diagnostic08());
        assert_ne!(eligible.descriptor.canonical_identity(),diagnostic.descriptor.canonical_identity());
        assert!(!eligible.prepared.source_replay_matches(&diagnostic.prepared));
        for (loan,consumer) in [(&eligible,&diagnostic.prepared),(&diagnostic,&eligible.prepared)] {
            let mut destination=VLoanDestination::default();let before=destination.clone();source.reads.set(0);
            assert_eq!(loan.consume_from(&source,844670,consumer,None,
                |_|panic!("profile swap reached residual"),&mut destination).unwrap_err(),"V loan cut descriptor mismatch");
            assert_eq!(source.reads.get(),0);assert_eq!(destination,before);
        }
        for owner in [844670,1810840,1810841,1810904,1827838] {
            let mut destination=VLoanDestination::default();source.reads.set(0);
            eligible.consume_from(&source,owner,&eligible.prepared,None,|patch| {
                assert!(!patch.writers().is_empty());Ok(())
            },&mut destination).unwrap();
            assert_eq!(source.reads.get(),983169);assert_eq!(destination.patches.len(),1);
        }
    }
    #[test]
    fn c164_eligible_native_loan_rejects_interior_d_and_internal_profile_drift_atomically() {
        let source=SyntheticSource::canonical();
        let mut loan=NativeVLoan::issue_from_with_descriptor(&source,CutDescriptor::eligible08()).unwrap();
        let changed=SyntheticSource {changed_height:Some(900001),compact:0x0102_0000,..SyntheticSource::canonical()};
        let mut destination=VLoanDestination::default();let before=destination.clone();
        assert_eq!(loan.consume_from(&changed,844670,&loan.prepared,None,
            |_|panic!("interior D reached residual"),&mut destination).unwrap_err(),"scheduled D changes within epoch");
        assert_eq!(destination,before);
        loan.descriptor=CutDescriptor::diagnostic08();
        assert_eq!(loan.consume_from(&source,844670,&loan.prepared,None,
            |_|panic!("internal profile drift reached residual"),&mut destination).unwrap_err(),"V loan cut descriptor mismatch");
        assert_eq!(destination,before);
        assert_eq!(loan.replay_group_from(&source).unwrap_err(),"V loan cut descriptor mismatch");
    }
}

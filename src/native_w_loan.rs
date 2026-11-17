//! Private, source-replayed W loan for bounded H21 consumer preparation.
//! This module is test-only and makes no frame or production claim.
use num_bigint::BigUint;
use std::collections::BTreeMap;

use crate::{
    native_owner_exports::NativeExports,
    packed_owner_assembly::{
        validate_native_plan_input, validate_native_row_for_history_test, NativeOwnerProducer,
        NativePackedRow, NativePrefix,
    },
    work_tree_history_plan::WorkTreeHistoryPlan,
    work_tree_layout::WIDTH,
};

const W_LOCAL: usize = 987_450;
const W_BITS: usize = 224;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct WSourceTag {
    pub height: usize,
    pub local: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ParentIdentity {
    headers: usize,
    slot_log: usize,
    root: [u8; 32],
    total: [u8; 28],
    profile: [u8; 32],
}

impl ParentIdentity {
    fn from_source(plan: &WorkTreeHistoryPlan, prefix: &NativePrefix) -> Result<Self, String> {
        validate_native_plan_input(plan, prefix)?;
        Ok(Self {
            headers: prefix.header_count(),
            slot_log: plan.slot_log(),
            root: prefix.root(),
            total: prefix.total_be28(),
            profile: prefix.profile(),
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct PackedSourceCopy {
    owner: usize,
    class: crate::daa_history_roster::OwnerClass,
    bytes: Vec<u8>,
}

impl PackedSourceCopy {
    fn from_row(row: &NativePackedRow) -> Self {
        Self { owner: row.owner(), class: row.class(), bytes: row.packed_bytes().to_vec() }
    }

    fn matches(&self, row: &NativePackedRow, owner: usize) -> bool {
        self.owner == owner && row.owner() == owner && self.class == row.class()
            && self.bytes.as_slice() == row.packed_bytes()
    }
}

/// A private W snapshot tied to one verified prefix, owner, consumer context,
/// and exact native Upper source coordinate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct NativeWLoan {
    parent: ParentIdentity,
    context: usize,
    owner: usize,
    source: WSourceTag,
    value: BigUint,
    packed_source: PackedSourceCopy,
}

fn source_value(prefix: &NativePrefix, source: WSourceTag) -> Result<BigUint, String> {
    let (_, upper) = prefix.interval(source.height)?;
    Ok(BigUint::from_bytes_be(&upper))
}

fn bit_at(bytes: &[u8], local: usize) -> Result<bool, String> {
    let byte = bytes.get(local / 8).ok_or("W source row coordinate outside packed row")?;
    Ok((byte >> (local % 8)) & 1 != 0)
}

fn replay_source(
    plan: &WorkTreeHistoryPlan,
    prefix: &NativePrefix,
    context: usize,
    owner: usize,
    source: WSourceTag,
) -> Result<(ParentIdentity, BigUint, NativePackedRow), String> {
    if context >= 2 { return Err("W loan context outside selected pair".into()); }
    if owner >= prefix.genuine_count() || owner >= plan.slots() as usize {
        return Err("W loan owner outside native prefix".into());
    }
    if source.height != owner.checked_add(2).ok_or("W height overflow")? || source.local != W_LOCAL {
        return Err("W loan source height/local mismatch".into());
    }
    let parent = ParentIdentity::from_source(plan, prefix)?;
    let expected = source_value(prefix, source)?;
    if expected.bits() > W_BITS as u64 { return Err("W Upper exceeds U224".into()); }

    let exports = NativeExports::new_for_history(plan, prefix)?;
    let producer = NativeOwnerProducer::new_for_history(plan, prefix)?;
    let row = producer.produce(owner)?;
    validate_native_row_for_history_test(plan, prefix, &row, |wire| exports.bit(wire))?;
    for bit in 0..W_BITS {
        let address = owner.checked_mul(WIDTH).and_then(|base| base.checked_add(W_LOCAL + bit))
            .ok_or("W export coordinate overflow")?;
        if exports.bit(address)? != expected.bit(bit as u64)
            || bit_at(row.packed_bytes(), W_LOCAL + bit)? != expected.bit(bit as u64) {
            return Err(format!("W Upper source replay mismatch at bit {bit}"));
        }
    }
    Ok((parent, expected, row))
}

impl NativeWLoan {
    pub(crate) fn issue(
        plan: &WorkTreeHistoryPlan,
        prefix: &NativePrefix,
        context: usize,
        owner: usize,
        source: WSourceTag,
    ) -> Result<Self, String> {
        let (parent, value, row) = replay_source(plan, prefix, context, owner, source)?;
        Ok(Self { parent, context, owner, source, value, packed_source: PackedSourceCopy::from_row(&row) })
    }

    /// Replays the source before running the consumer alias/residual callback.
    /// Publication is last, so every failure leaves the destination unchanged.
    pub(crate) fn consume(
        &self,
        plan: &WorkTreeHistoryPlan,
        prefix: &NativePrefix,
        context: usize,
        owner: usize,
        source: WSourceTag,
        consumer_value: &BigUint,
        consumer_row: &NativePackedRow,
        residual: impl FnOnce(&BigUint, &BigUint) -> Result<(), String>,
        destination: &mut WLoanDestination,
    ) -> Result<(), String> {
        if context != self.context || owner != self.owner || source != self.source {
            return Err("W loan consumer context/owner/source mismatch".into());
        }
        if destination.cells.contains_key(&(context, owner)) {
            return Err("W loan destination duplicate".into());
        }
        let (parent, replayed, row) = replay_source(plan, prefix, context, owner, source)?;
        if parent != self.parent || replayed != self.value || !self.packed_source.matches(&row, owner) {
            return Err("W loan immutable source replay mismatch".into());
        }
        if !self.packed_source.matches(consumer_row, owner) {
            return Err("W consumer packed source row mismatch".into());
        }
        let exports = NativeExports::new_for_history(plan, prefix)?;
        validate_native_row_for_history_test(plan, prefix, consumer_row, |wire| exports.bit(wire))?;
        if consumer_value != &replayed {
            return Err("W consumer alias value mismatch".into());
        }
        residual(&replayed, consumer_value)?;
        destination.cells.insert((context, owner), replayed);
        Ok(())
    }

    #[cfg(test)]
    pub(crate) fn flip_value_bit_for_test(&mut self, bit: u64) {
        self.value.set_bit(bit, !self.value.bit(bit));
    }

    #[cfg(test)]
    pub(crate) fn value_for_test(&self) -> &BigUint { &self.value }

    #[cfg(test)]
    pub(crate) fn replace_value_for_test(&mut self, value: BigUint) { self.value = value; }
}

/// Test-only source-owned group for the three selected W coordinates.
/// It performs one complete physical row validation per owner at issue.
#[cfg(test)]
#[derive(Clone)]
pub(crate) struct NativeWLoanGroup {
    parent: ParentIdentity,
    owners: Vec<usize>,
    rows: BTreeMap<usize, NativePackedRow>,
    loans: BTreeMap<(usize, usize), NativeWLoan>,
}

#[cfg(test)]
impl NativeWLoanGroup {
    const SELECTED_OWNERS: [usize; 3] = [417_789, 845_757, 845_758];

    pub(crate) fn issue(plan: &WorkTreeHistoryPlan, prefix: &NativePrefix) -> Result<Self, String> {
        Self::issue_owners(plan, prefix, &Self::SELECTED_OWNERS)
    }

    /// Small-prefix seam; the native selection remains fixed by `issue`.
    pub(crate) fn issue_for_test(plan: &WorkTreeHistoryPlan, prefix: &NativePrefix, owners: &[usize]) -> Result<Self, String> {
        Self::issue_owners(plan, prefix, owners)
    }

    fn issue_owners(plan: &WorkTreeHistoryPlan, prefix: &NativePrefix, owners: &[usize]) -> Result<Self, String> {
        if owners.is_empty() || owners.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err("W group owners must be nonempty and strictly ordered".into());
        }
        let parent = ParentIdentity::from_source(plan, prefix)?;
        let mut rows = BTreeMap::new();
        let mut loans = BTreeMap::new();
        for &owner in owners {
            let source = WSourceTag { height: owner.checked_add(2).ok_or("W height overflow")?, local: W_LOCAL };
            let (replayed_parent, value, row) = replay_source(plan, prefix, 0, owner, source)?;
            if replayed_parent != parent { return Err("W group parent changed during issue".into()); }
            rows.insert(owner, row.clone());
            let packed_source = PackedSourceCopy::from_row(&row);
            for context in 0..2 {
                loans.insert((context, owner), NativeWLoan {
                    parent, context, owner, source, value: value.clone(), packed_source: packed_source.clone(),
                });
            }
        }
        Ok(Self { parent, owners: owners.to_vec(), rows, loans })
    }

    /// Rechecks parent, source aliases, and retained row bytes without another
    /// full row production. Residuals run before any staged destination is published.
    pub(crate) fn consume(
        &self,
        plan: &WorkTreeHistoryPlan,
        prefix: &NativePrefix,
        mut residual: impl FnMut(usize, usize, &BigUint, &BigUint) -> Result<(), String>,
        destination: &mut WLoanDestination,
    ) -> Result<(), String> {
        if ParentIdentity::from_source(plan, prefix)? != self.parent {
            return Err("W group parent mismatch".into());
        }
        if self.rows.len() != self.owners.len() || self.loans.len() != self.owners.len() * 2 {
            return Err("W group cardinality mismatch".into());
        }
        for &owner in &self.owners {
            let source = WSourceTag { height: owner.checked_add(2).ok_or("W height overflow")?, local: W_LOCAL };
            for context in 0..2 {
                let loan = self.loans.get(&(context, owner)).ok_or("W group loan missing")?;
                if loan.context != context || loan.owner != owner || loan.source != source {
                    return Err("W group context/owner/source mismatch".into());
                }
                if loan.parent != self.parent { return Err("W group loan parent mismatch".into()); }
                if destination.cells.contains_key(&(context, owner)) {
                    return Err("W group destination duplicate".into());
                }
            }
        }

        let exports = NativeExports::new_for_history(plan, prefix)?;
        let mut staged = BTreeMap::new();
        for &owner in &self.owners {
            let source = WSourceTag { height: owner.checked_add(2).ok_or("W height overflow")?, local: W_LOCAL };
            if ParentIdentity::from_source(plan, prefix)? != self.parent {
                return Err("W group parent mismatch".into());
            }
            let value = source_value(prefix, source)?;
            if value.bits() > W_BITS as u64 { return Err("W Upper exceeds U224".into()); }
            let row = self.rows.get(&owner).ok_or("W group packed source row missing")?;
            let alias = packed_w_alias(row)?;
            if alias != value { return Err("W group 224-bit consumer alias mismatch".into()); }
            for bit in 0..W_BITS {
                let address = owner.checked_mul(WIDTH).and_then(|base| base.checked_add(W_LOCAL + bit))
                    .ok_or("W export coordinate overflow")?;
                if exports.bit(address)? != value.bit(bit as u64) || bit_at(row.packed_bytes(), W_LOCAL + bit)? != value.bit(bit as u64) {
                    return Err(format!("W group source replay mismatch at bit {bit}"));
                }
            }
            for context in 0..2 {
                let loan = self.loans.get(&(context, owner)).ok_or("W group loan missing")?;
                if loan.value != value { return Err("W group 224-bit loan alias mismatch".into()); }
                if !loan.packed_source.matches(row, owner) { return Err("W group packed source row mismatch".into()); }
                residual(context, owner, &value, &alias)?;
                staged.insert((context, owner), value.clone());
            }
        }
        destination.cells.extend(staged);
        Ok(())
    }

    #[cfg(test)]
    pub(crate) fn logical_loan_count_for_test(&self) -> usize { self.loans.len() }
    #[cfg(test)]
    pub(crate) fn replace_context_for_test(&mut self, key: (usize, usize), context: usize) { if let Some(x)=self.loans.get_mut(&key) { x.context=context; } }
    #[cfg(test)]
    pub(crate) fn replace_owner_for_test(&mut self, key: (usize, usize), owner: usize) { if let Some(x)=self.loans.get_mut(&key) { x.owner=owner; } }
    #[cfg(test)]
    pub(crate) fn replace_source_for_test(&mut self, key: (usize, usize), source: WSourceTag) { if let Some(x)=self.loans.get_mut(&key) { x.source=source; } }
    #[cfg(test)]
    pub(crate) fn corrupt_packed_source_for_test(&mut self, key: (usize, usize)) { if let Some(x)=self.loans.get_mut(&key) { if let Some(byte)=x.packed_source.bytes.get_mut(W_LOCAL/8) { *byte ^= 1 << (W_LOCAL%8); } } }
    #[cfg(test)]
    pub(crate) fn corrupt_retained_row_for_test(&mut self, owner: usize, byte_index: usize) {
        if let Some(row) = self.rows.get_mut(&owner) {
            let mut bytes = row.packed_bytes().to_vec();
            if let Some(byte) = bytes.get_mut(byte_index) {
                *byte ^= 1;
                if let Ok(changed) = row.with_packed_bytes_for_test(&bytes) { *row = changed; }
            }
        }
    }
    #[cfg(test)]
    pub(crate) fn flip_value_bit_for_test(&mut self, key: (usize, usize), bit: u64) { if let Some(x)=self.loans.get_mut(&key) { x.value.set_bit(bit, !x.value.bit(bit)); } }
    #[cfg(test)]
    pub(crate) fn corrupt_group_parent_for_test(&mut self) { self.parent.root[0] ^= 1; }
    #[cfg(test)]
    pub(crate) fn corrupt_loan_parent_for_test(&mut self, key: (usize, usize)) { if let Some(x)=self.loans.get_mut(&key) { x.parent.root[0] ^= 1; } }
}

#[cfg(test)]
fn packed_w_alias(row: &NativePackedRow) -> Result<BigUint, String> {
    let mut alias = BigUint::default();
    for bit in 0..W_BITS { if bit_at(row.packed_bytes(), W_LOCAL + bit)? { alias.set_bit(bit as u64, true); } }
    Ok(alias)
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct WLoanDestination {
    cells: BTreeMap<(usize, usize), BigUint>,
}

impl WLoanDestination {
    #[cfg(test)]
    pub(crate) fn get(&self, context: usize, owner: usize) -> Option<&BigUint> {
        self.cells.get(&(context, owner))
    }

    #[cfg(test)]
    pub(crate) fn insert_for_test(&mut self, context: usize, owner: usize, value: BigUint) {
        self.cells.insert((context, owner), value);
    }
}

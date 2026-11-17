//! Test-only common witness for the first three or four real Mainnet headers.
//! This is the bounded integration input, not historical producer admission.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use ergo_header_core::Header;
use num_bigint::BigUint;
use std::collections::BTreeMap;

use crate::{
    daa_history_layout, header_order::MAINNET_GENESIS, serializer::Fields,
    work_tree_fixed_hash as fixed, work_tree_history_plan::WorkTreeHistoryPlan,
    work_tree_layout::WIDTH, work_tree_leaf_hash as leaf, work_tree_work as work,
};

const N: usize = 3;
const S: usize = 4;

#[cfg(test)]
#[path = "historical_prefix_witness_stream40.rs"]
pub(crate) mod stream40;

pub(crate) struct PrefixWitness {
    pub(crate) values: Vec<Fr>,
    pub(crate) root: [u8; 32],
    pub(crate) total: [u8; 28],
    pub(crate) tip: [u8; 32],
    pub(crate) tip_time: i64,
    pub(crate) raw: Vec<Vec<u8>>,
}

pub(crate) fn retained_headers() -> Result<Vec<Header>, String> {
    retained_headers_n(N)
}

pub(crate) fn retained_headers_n(n: usize) -> Result<Vec<Header>, String> {
    if !matches!(n, 3 | 4) {
        return Err("prefix fixture supports exactly three or four headers".into());
    }
    let fixture: serde_json::Value = serde_json::from_str(include_str!(
        "../vendor/header-core/fixtures/governance-contiguous-header-packs-v1.json"
    ))
    .map_err(|e| e.to_string())?;
    (0..n)
        .map(|i| {
            let hex = fixture["networks"]["mainnet"]["source_headers_hex"][i]
                .as_str()
                .ok_or("missing native prefix RAW")?;
            if hex.len() % 2 != 0 {
                return Err("prefix RAW has an incomplete hex byte".into());
            }
            let raw = hex
                .as_bytes()
                .chunks_exact(2)
                .map(|pair| {
                    u8::from_str_radix(std::str::from_utf8(pair).map_err(|e| e.to_string())?, 16)
                        .map_err(|e| e.to_string())
                })
                .collect::<Result<Vec<_>, String>>()?;
            let header =
                Header::decode(&raw, None).map_err(|e| format!("native prefix decode: {e:?}"))?;
            if header
                .encode()
                .map_err(|e| format!("native prefix encode: {e:?}"))?
                != raw
            {
                return Err("prefix RAW is not canonical".into());
            }
            Ok(header)
        })
        .collect()
}

fn be28(value: &BigUint) -> Result<[u8; 28], String> {
    let bytes = value.to_bytes_be();
    if bytes.len() > 28 {
        return Err("prefix work overflow".into());
    }
    let mut out = [0; 28];
    out[28 - bytes.len()..].copy_from_slice(&bytes);
    Ok(out)
}
fn merge(values: &mut BTreeMap<usize, Fr>, wire: usize, value: Fr) -> Result<(), String> {
    if wire >= S * WIDTH {
        return Err("prefix merge wire outside input".into());
    }
    if value != Fr::zero() && value != Fr::one() {
        return Err("prefix merge non-Boolean value".into());
    }
    if let Some(previous) = values.get(&wire) {
        if *previous != value {
            return Err(format!("prefix conflicting live assignment at {wire}"));
        }
    } else {
        values.insert(wire, value);
    }
    Ok(())
}
fn merge_owner(
    values: &mut BTreeMap<usize, Fr>,
    owner: usize,
    local: BTreeMap<usize, Fr>,
) -> Result<(), String> {
    if owner >= S || local.keys().any(|wire| *wire >= WIDTH) {
        return Err("prefix local assignment outside owner".into());
    }
    for (wire, value) in local {
        merge(values, owner * WIDTH + wire, value)?;
    }
    Ok(())
}
fn put_integer(
    values: &mut BTreeMap<usize, Fr>,
    owner: usize,
    wires: &[usize],
    n: &BigUint,
) -> Result<(), String> {
    for (bit, &wire) in wires.iter().enumerate() {
        merge(
            values,
            owner * WIDTH + wire,
            Fr::from(n.bit(bit as u64) as u64),
        )?;
    }
    Ok(())
}
/// Admit only a canonical contiguous N3/N4 prefix rooted at the fixed genesis.
/// Difficulty correctness is left to the actual relation consumer below.
pub(crate) fn build(headers: &[Header]) -> Result<PrefixWitness, String> {
    build_inner(headers, Fault::None)
}
#[derive(Clone, Copy)]
pub(crate) enum Fault {
    None,
    ForeignLeafRaw,
    IntervalGap,
    PaddingPosition,
}
pub(crate) fn build_inner(headers: &[Header], fault: Fault) -> Result<PrefixWitness, String> {
    let n = headers.len();
    if !matches!(n, 3 | 4) {
        return Err("prefix fixture requires exactly three or four headers".into());
    }
    if matches!(fault, Fault::PaddingPosition) && n != 4 {
        return Err("padding-position fault requires the N4 padding slot".into());
    }
    let mut raw = Vec::new();
    let mut previous = [0; 32];
    for (i, header) in headers.iter().enumerate() {
        let bytes = header
            .encode()
            .map_err(|e| format!("prefix encode: {e:?}"))?;
        let canonical = Header::decode(&bytes, None)
            .map_err(|e| format!("prefix re-decode: {e:?}"))?
            .encode()
            .map_err(|e| format!("prefix re-encode: {e:?}"))?;
        if canonical != bytes || header.height as usize != i + 1 || header.parent_id != previous {
            return Err("prefix canonical height or parent identity mismatch".into());
        }
        previous = ergo_header_core::blake2b256(&bytes);
        if i == 0 && previous != MAINNET_GENESIS {
            return Err("prefix genesis identity mismatch".into());
        }
        raw.push(bytes);
    }
    let engine = fixed::engine()?;
    let e = &engine.base.endpoints;
    let leaf_profile = leaf::LeafProfile::new(n, [0; 32])?;
    let leaf_boundary = leaf::compile(engine, leaf_profile)?;
    let leaf_profile = &leaf_boundary.profile;
    let mut profile_bytes = fixed::PROFILE_PREFIX.to_vec();
    profile_bytes.extend_from_slice(&MAINNET_GENESIS);
    let profile = ergo_header_core::blake2b256(&profile_bytes);
    let mut assigned = BTreeMap::new();
    let mut leaves = Vec::new();
    let mut lower = BigUint::from(0u64);
    for (slot, header) in headers.iter().skip(1).enumerate() {
        let mut leaf_header = header.clone();
        if slot == 0 && matches!(fault, Fault::ForeignLeafRaw) {
            leaf_header.timestamp ^= 1;
        }
        if slot == 1 && matches!(fault, Fault::IntervalGap) {
            lower += BigUint::from(1u64);
        }
        let difficulty = work::native_decode(header.n_bits)?;
        let upper = &lower + &difficulty;
        let leaf = leaf::assign_header_leaf(
            engine,
            &leaf_boundary,
            slot,
            &leaf_header,
            be28(&lower)?,
            be28(&upper)?,
            profile,
        )?;
        leaves.push(leaf.digest);
        merge_owner(&mut assigned, slot, leaf.values)?;
        put_integer(
            &mut assigned,
            slot,
            &e.n_bits,
            &BigUint::from(header.n_bits),
        )?;
        put_integer(&mut assigned, slot, &e.lower, &lower)?;
        put_integer(&mut assigned, slot, &e.upper, &upper)?;
        put_integer(&mut assigned, slot, &e.work, &difficulty)?;
        put_integer(
            &mut assigned,
            slot,
            &e.work_minus_one,
            &(&difficulty - BigUint::from(1u64)),
        )?;
        merge(
            &mut assigned,
            slot * WIDTH + e.exponent[(header.n_bits >> 24) as usize],
            Fr::one(),
        )?;
        lower = upper;
    }
    for slot in n - 1..S {
        let leaf_assignment = if matches!(fault, Fault::PaddingPosition)
            && leaf_profile.role(slot)? == leaf::Role::Padding
        {
            leaf::assign_padding_position_fault_for_prefix(engine, &leaf_boundary, slot, profile)?
        } else {
            leaf::assign_inactive_leaf_for_prefix(engine, &leaf_boundary, slot, profile)?
        };
        if leaf_profile.role(slot)? == leaf::Role::Padding {
            leaves.push(leaf_assignment.digest);
        }
        merge_owner(&mut assigned, slot, leaf_assignment.values)?;
    }
    if leaves.len() != leaf_profile.tree.leaves {
        return Err("prefix work-leaf assignment does not fill the descriptor".into());
    }

    // Build every native node at its descriptor-owned level and slot. The
    // N3 shape naturally remains node0/profile1/dummy2-3.
    let fixed_profile = fixed::FixedProfile::new(n, [0; 32])?;
    let mut layer = leaves;
    let levels = leaf_profile.tree.leaves.trailing_zeros() as usize;
    let mut root_slot = usize::MAX;
    for level in 1..=levels {
        let (base, count) = leaf_profile.tree.level(level)?;
        let mut next = Vec::with_capacity(count);
        for (position, pair) in layer.chunks_exact(2).enumerate() {
            if position >= count {
                return Err("prefix node level has inconsistent child count".into());
            }
            let slot = base + position;
            let mut bytes = vec![b'N', level as u8];
            bytes.extend_from_slice(&(position as u32).to_be_bytes());
            bytes.extend_from_slice(&pair[0]);
            bytes.extend_from_slice(&pair[1]);
            if bytes.len() != 70 {
                return Err("prefix native node preimage length changed".into());
            }
            let node = leaf::assign_fixed_slot_for_prefix(engine, &fixed_profile, slot, &bytes)?;
            next.push(node.digest);
            merge_owner(&mut assigned, slot, node.values)?;
            if level == levels {
                root_slot = slot;
            }
        }
        if next.len() != count {
            return Err("prefix node layer does not match descriptor level".into());
        }
        layer = next;
    }
    if layer.len() != 1 || root_slot != leaf_profile.tree.root_node_slot {
        return Err("prefix root slot differs from the descriptor".into());
    }
    let root = layer[0];
    let profile_node = leaf::assign_fixed_slot_for_prefix(
        engine,
        &fixed_profile,
        leaf_profile.tree.profile_node_slot,
        &profile_bytes,
    )?;
    if profile_node.digest != profile {
        return Err("prefix native profile mismatch".into());
    }
    merge_owner(
        &mut assigned,
        leaf_profile.tree.profile_node_slot,
        profile_node.values,
    )?;
    for owner in leaf_profile.tree.profile_node_slot + 1..S {
        let dummy = leaf::assign_fixed_slot_for_prefix(engine, &fixed_profile, owner, &[])?;
        merge_owner(&mut assigned, owner, dummy.values)?;
    }
    // Use the actual public root/total plan for header assignment ownership.
    let total = be28(&lower)?;
    let plan = WorkTreeHistoryPlan::compile(n as u64, 2, root, total)?;
    let replaced = plan.assignment_replacement_mask()?;
    for owner in 0..S {
        let i = owner.min(n - 1);
        let fields = Fields::from_header(&headers[i])?;
        let mut joined = daa_history_layout::full_header_boundary(Some(&fields))?;
        let (height, time, first) = if i == 0 {
            (0, 0, true)
        } else {
            (headers[i - 1].height, headers[i - 1].timestamp, false)
        };
        crate::header_compact_links::assign_order(&mut joined, &fields, height, time, first)?;
        let input = joined
            .base
            .base
            .base
            .input
            .as_ref()
            .ok_or("prefix full-header assignment absent")?;
        if input.len() != WIDTH {
            return Err("prefix header input geometry changed".into());
        }
        for (wire, &value) in input.iter().enumerate() {
            if !replaced[wire] {
                merge(&mut assigned, owner * WIDTH + wire, value)?;
            }
        }
    }
    let mut values = vec![Fr::zero(); S * WIDTH];
    for (wire, value) in assigned {
        values[wire] = value;
    }
    Ok(PrefixWitness {
        values,
        root,
        total,
        tip: previous,
        tip_time: headers[n - 1].timestamp,
        raw,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn conflicting_nonboolean_and_out_of_range_assignments_fail_closed() {
        let mut map = BTreeMap::new();
        merge(&mut map, 42, Fr::one()).unwrap();
        merge(&mut map, 42, Fr::one()).unwrap();
        assert!(merge(&mut map, 42, Fr::zero())
            .unwrap_err()
            .contains("conflicting"));
        assert!(merge(&mut map, 43, Fr::from(2u64))
            .unwrap_err()
            .contains("non-Boolean"));
        assert!(merge(&mut map, S * WIDTH, Fr::zero()).is_err());
        assert_eq!(map.len(), 1);
        assert_eq!(map[&42], Fr::one());
        assert!(merge_owner(&mut map, S, BTreeMap::new()).is_err());
        assert!(merge_owner(&mut map, 0, BTreeMap::from([(WIDTH, Fr::zero())])).is_err());
    }
}

use super::*;
use blake2::{digest::consts::U32, Blake2b, Digest};
use num_bigint::BigUint;
use num_traits::One;
use serde_json::Value;
use crate::packed_owner_assembly::NativePrefix;

fn fixture_raws(count: usize) -> Vec<Vec<u8>> {
    let pack: Value = serde_json::from_str(include_str!("../vendor/header-core/fixtures/governance-contiguous-header-packs-v1.json")).unwrap();
    let entries = pack["networks"]["mainnet"]["source_headers_hex"]
        .as_array()
        .expect("embedded mainnet header list");
    assert!(entries.len() >= count);
    entries.iter().take(count).map(|entry| {
        let text = entry.as_str().expect("header hex");
        assert_eq!(text.len() % 2, 0);
        text.as_bytes().chunks_exact(2).map(|pair| {
            u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).unwrap()
        }).collect()
    }).collect()
}

fn fixture_prefix(count: usize) -> NativePrefix {
    NativePrefix::from_raw_iter(count, fixture_raws(count).into_iter().map(Ok)).unwrap()
}

fn be28(value: &BigUint) -> [u8; 28] {
    assert!(value.bits() <= 224);
    let bytes = value.to_bytes_be();
    assert!(bytes.len() <= 28);
    let mut out = [0u8; 28];
    if !bytes.is_empty() { out[28 - bytes.len()..].copy_from_slice(&bytes); }
    out
}

fn make_opening(
    prefix: &NativePrefix,
    context: &NativeWorkMembershipContext,
    position: usize,
) -> NativeWorkOpening {
    let height = position + 2;
    let (lower_be28, upper_be28) = prefix.interval(height).unwrap();
    let raw = prefix.raw(height).unwrap().to_vec();
    let mut siblings = Vec::new();
    for level in 1..=context.depth() {
        let child_position = position >> (level - 1);
        let sibling_position = child_position ^ 1;
        let sibling = if level == 1 {
            prefix.leaf_digest(sibling_position).unwrap()
        } else {
            let (base, count) = context.descriptor.level(level - 1).unwrap();
            assert!(sibling_position < count);
            prefix.node_digest(base + sibling_position).unwrap()
        };
        siblings.push(sibling);
    }
    NativeWorkOpening::new(position as u32, lower_be28, upper_be28, raw, siblings)
}

fn owned_case(
    headers: usize,
    positions: &[usize],
) -> (NativeWorkMembershipContext, Vec<NativeWorkOpening>) {
    let prefix = fixture_prefix(headers);
    let context = NativeWorkMembershipContext::new(headers, prefix.root(), prefix.total_be28()).unwrap();
    let openings = positions.iter().map(|&position| make_opening(&prefix, &context, position)).collect();
    drop(prefix);
    (context, openings)
}

fn independent_profile() -> [u8; 32] {
    let mut preimage = b"nipopow-v2/work-profile/v1\0".to_vec();
    preimage.extend_from_slice(&crate::header_order::MAINNET_GENESIS);
    Blake2b::<U32>::digest(preimage).into()
}

fn golden_leaf_preimage(
    headers: usize,
    profile: [u8; 32],
    height: u32,
    lower: [u8; 28],
    upper: [u8; 28],
    raw: &[u8],
) -> Vec<u8> {
    let mut bytes = vec![b'L'];
    bytes.extend_from_slice(&profile);
    bytes.extend_from_slice(&(headers as u32).to_be_bytes());
    bytes.extend_from_slice(&height.to_be_bytes());
    bytes.extend_from_slice(&lower);
    bytes.extend_from_slice(&upper);
    bytes.extend_from_slice(&(raw.len() as u16).to_be_bytes());
    bytes.extend_from_slice(raw);
    bytes
}

fn golden_node_preimage(level: u8, position: u32, left: [u8; 32], right: [u8; 32]) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(70);
    bytes.push(b'N');
    bytes.push(level);
    bytes.extend_from_slice(&position.to_be_bytes());
    bytes.extend_from_slice(&left);
    bytes.extend_from_slice(&right);
    bytes
}

fn golden_hash(bytes: &[u8]) -> [u8; 32] {
    Blake2b::<U32>::digest(bytes).into()
}

// Test-only self-consistent root oracle. It uses literal preimages and BLAKE2b,
// not the production path verifier or its native hash helpers.
fn reseal_root(
    headers: usize,
    opening: &NativeWorkOpening,
    position: usize,
    leaf_height: u32,
    profile: [u8; 32],
) -> [u8; 32] {
    let mut digest = golden_hash(&golden_leaf_preimage(
        headers, profile, leaf_height, opening.lower_be28, opening.upper_be28, &opening.raw,
    ));
    for (index, sibling) in opening.siblings.iter().enumerate() {
        let level = index + 1;
        let parent_position = position >> level;
        let child_position = position >> (level - 1);
        let (left, right) = if child_position & 1 == 0 {
            (digest, *sibling)
        } else {
            (*sibling, digest)
        };
        digest = golden_hash(&golden_node_preimage(level as u8, parent_position as u32, left, right));
    }
    digest
}

fn reseal_root_with_swapped_level(
    headers: usize,
    opening: &NativeWorkOpening,
    position: usize,
    leaf_height: u32,
    profile: [u8; 32],
    swapped_level: usize,
) -> [u8; 32] {
    let mut digest = golden_hash(&golden_leaf_preimage(
        headers, profile, leaf_height, opening.lower_be28, opening.upper_be28, &opening.raw,
    ));
    for (index, sibling) in opening.siblings.iter().enumerate() {
        let level = index + 1;
        let parent_position = position >> level;
        let child_position = position >> (level - 1);
        let current_is_left = child_position & 1 == 0;
        let swap = level == swapped_level;
        let (left, right) = if current_is_left ^ swap {
            (digest, *sibling)
        } else {
            (*sibling, digest)
        };
        digest = golden_hash(&golden_node_preimage(level as u8, parent_position as u32, left, right));
    }
    digest
}

fn header_with_nbits(raw: &[u8], n_bits: u32) -> Vec<u8> {
    let mut header = ergo_header_core::Header::decode(raw, None).unwrap();
    header.n_bits = n_bits;
    header.encode().unwrap()
}

fn noncanonical_v1_distance(raw: &[u8]) -> Vec<u8> {
    let header = ergo_header_core::Header::decode(raw, None).unwrap();
    let distance_len = match &header.pow {
        ergo_header_core::PowSolution::V1 { distance, .. } => distance.len(),
        ergo_header_core::PowSolution::V2 { .. } => panic!("height-2 fixture must use V1"),
    };
    assert!(distance_len > 0 && distance_len < u8::MAX as usize);
    let length_at = raw.len() - distance_len - 1;
    assert_eq!(usize::from(raw[length_at]), distance_len);
    let mut out = raw.to_vec();
    out[length_at] = (distance_len + 1) as u8;
    out.insert(length_at + 1, 0);
    out
}

fn assert_error<T>(result: Result<T, NativeWorkOpeningError>, expected: NativeWorkOpeningError) {
    match result {
        Err(actual) => assert_eq!(actual, expected),
        Ok(_) => panic!("expected isolated C565 opening rejection: {expected:?}"),
    }
}

#[test]
fn c565_owned_fixture_membership_n3_n6_n9_and_larger_total_scope() {
    let cases = vec![
        (3usize, vec![0usize, 1]),
        (6usize, vec![0usize, 1, 2, 4]),
        (9usize, vec![0usize, 3, 7]),
    ];
    let mut accepted = 0usize;
    for (headers, positions) in cases {
        let (context, openings) = owned_case(headers, &positions);
        for opening in &openings {
            let lower = BigUint::from_bytes_be(&opening.lower_be28);
            let upper = BigUint::from_bytes_be(&opening.upper_be28);
            assert!(lower < upper);
            for coordinate in [lower.clone(), &upper - BigUint::one()] {
                let membership = context.verify(be28(&coordinate), opening).unwrap();
                assert_eq!(membership.headers(), headers);
                assert_eq!(membership.root(), context.root);
                assert_eq!(membership.total_be28(), context.total_be28);
                assert_eq!(membership.profile(), independent_profile());
                assert_eq!(membership.position(), opening.position);
                assert_eq!(membership.height(), opening.position + 2);
                assert_eq!(membership.interval_be28(), (opening.lower_be28, opening.upper_be28));
                assert_eq!(membership.raw(), opening.raw.as_slice());
                assert_eq!(membership.header().height, membership.height());
                accepted += 1;
            }
        }
    }
    assert_eq!(accepted, 18);

    // Supplied-root membership alone does not authenticate that a larger total
    // is structurally valid; the full pi_s verifier owns that predicate.
    let (context, openings) = owned_case(6, &[0]);
    let opening = &openings[0];
    let larger_total = &context.total + BigUint::one();
    assert!(larger_total.bits() <= 224);
    let larger = NativeWorkMembershipContext::new(6, context.root, be28(&larger_total)).unwrap();
    assert!(larger.verify(opening.lower_be28, opening).is_ok());
}

#[test]
fn c565_context_rejects_zero_total_and_descriptor_outside_envelope() {
    assert_error(
        NativeWorkMembershipContext::new(6, [0; 32], [0; 28]),
        NativeWorkOpeningError::Context,
    );
    assert_error(
        NativeWorkMembershipContext::new(2, [0; 32], be28(&BigUint::from(1u8))),
        NativeWorkOpeningError::Context,
    );
    assert_error(
        NativeWorkMembershipContext::new(1usize << 31, [0; 32], be28(&BigUint::from(1u8))),
        NativeWorkOpeningError::Context,
    );
}

#[test]
fn c565_existing_leaf_and_node_preimages_match_independent_golden_bytes() {
    let prefix = fixture_prefix(6);
    let context = NativeWorkMembershipContext::new(6, prefix.root(), prefix.total_be28()).unwrap();
    let opening = make_opening(&prefix, &context, 4);
    let profile = independent_profile();
    assert_eq!(context.profile, profile);

    let leaf_bytes = golden_leaf_preimage(
        6, profile, 6, opening.lower_be28, opening.upper_be28, &opening.raw,
    );
    assert_eq!(leaf_bytes.len(), 99 + opening.raw.len());
    let leaf_digest = golden_hash(&leaf_bytes);
    assert_eq!(
        leaf::native_leaf_preimage_hash(
            &context.leaf_profile, 4, &opening.raw, 6, opening.lower_be28, opening.upper_be28, profile,
        ).unwrap(),
        leaf_digest,
    );
    assert_eq!(prefix.leaf_digest(4).unwrap(), leaf_digest);

    // Position 4 is the last genuine leaf of N=6; its first sibling is the
    // padding leaf at position 5. The independent parent tuple is exact N||L||P||left||right.
    let parent_slot = context.descriptor.level(1).unwrap().0 + 2;
    let node_bytes = golden_node_preimage(1, 2, leaf_digest, opening.siblings[0]);
    assert_eq!(node_bytes.len(), 70);
    assert_eq!(
        leaf::native_fixed_preimage_hash(&context.fixed_profile, parent_slot, &node_bytes).unwrap(),
        golden_hash(&node_bytes),
    );
}

#[test]
fn c565_rejects_coordinate_interval_total_position_and_root_faults() {
    let (context, openings) = owned_case(6, &[0, 1]);
    let first = &openings[0];
    let lower = BigUint::from_bytes_be(&first.lower_be28);
    let upper = BigUint::from_bytes_be(&first.upper_be28);
    let total = BigUint::from_bytes_be(&context.total_be28);
    assert!(upper < total);
    assert_error(context.verify(context.total_be28, first), NativeWorkOpeningError::Coordinate);
    assert_error(context.verify(be28(&upper), first), NativeWorkOpeningError::IntervalWork);

    let second = &openings[1];
    let second_lower = BigUint::from_bytes_be(&second.lower_be28);
    assert!(second_lower > BigUint::from(0u8));
    let below_lower = &second_lower - BigUint::one();
    assert_error(context.verify(be28(&below_lower), second), NativeWorkOpeningError::IntervalWork);

    let small_total = &lower + BigUint::one();
    assert!(small_total < upper);
    let too_small = NativeWorkMembershipContext::new(6, context.root, be28(&small_total)).unwrap();
    assert_error(too_small.verify(first.lower_be28, first), NativeWorkOpeningError::IntervalWork);

    let mut padding = first.clone();
    padding.position = 5;
    assert_error(context.verify(first.lower_be28, &padding), NativeWorkOpeningError::Position);
    let mut overflow = first.clone();
    overflow.position = u32::MAX;
    assert_error(context.verify(first.lower_be28, &overflow), NativeWorkOpeningError::Position);

    let mut wrong_interval = first.clone();
    let changed_upper = &upper + BigUint::one();
    wrong_interval.upper_be28 = be28(&changed_upper);
    let synthetic_root = reseal_root(6, &wrong_interval, 0, 2, independent_profile());
    let resealed_context = NativeWorkMembershipContext::new(6, synthetic_root, be28(&changed_upper)).unwrap();
    assert_error(
        resealed_context.verify(wrong_interval.lower_be28, &wrong_interval),
        NativeWorkOpeningError::IntervalWork,
    );

    let mut wrong_lower = first.clone();
    let changed_lower = &lower + BigUint::one();
    assert!(changed_lower < upper);
    wrong_lower.lower_be28 = be28(&changed_lower);
    let lower_root = reseal_root(6, &wrong_lower, 0, 2, independent_profile());
    let lower_context = NativeWorkMembershipContext::new(6, lower_root, context.total_be28).unwrap();
    assert_error(
        lower_context.verify(wrong_lower.lower_be28, &wrong_lower),
        NativeWorkOpeningError::IntervalWork,
    );

    for level in 0..first.siblings.len() {
        let mut changed = first.clone();
        changed.siblings[level][0] ^= 1;
        assert_error(context.verify(first.lower_be28, &changed), NativeWorkOpeningError::RootMismatch);
    }
    let wrong_root = NativeWorkMembershipContext::new(6, [0x99; 32], context.total_be28).unwrap();
    assert_error(wrong_root.verify(first.lower_be28, first), NativeWorkOpeningError::RootMismatch);

    let (odd_context, odd_openings) = owned_case(6, &[1]);
    let odd = &odd_openings[0];
    let wrong_orientation_root = reseal_root_with_swapped_level(
        6, odd, 1, 3, independent_profile(), 1,
    );
    let wrong_orientation = NativeWorkMembershipContext::new(
        6, wrong_orientation_root, odd_context.total_be28,
    ).unwrap();
    assert_error(
        wrong_orientation.verify(odd.lower_be28, odd),
        NativeWorkOpeningError::RootMismatch,
    );
}

#[test]
fn c565_height_and_raw_canonicality_negatives_use_self_consistent_roots() {
    let (context, openings) = owned_case(6, &[0]);
    let first = &openings[0];

    let mut wrong_height = first.clone();
    wrong_height.position = 1;
    let decoded = ergo_header_core::Header::decode(&wrong_height.raw, None).unwrap();
    let height_root = reseal_root(6, &wrong_height, 1, decoded.height, independent_profile());
    let height_context = NativeWorkMembershipContext::new(6, height_root, context.total_be28).unwrap();
    assert_error(height_context.verify(wrong_height.lower_be28, &wrong_height), NativeWorkOpeningError::Raw);

    let mut genesis = first.clone();
    genesis.raw = fixture_raws(1).remove(0);
    let genesis_root = reseal_root(6, &genesis, 0, 1, independent_profile());
    let genesis_context = NativeWorkMembershipContext::new(6, genesis_root, context.total_be28).unwrap();
    assert_error(genesis_context.verify(genesis.lower_be28, &genesis), NativeWorkOpeningError::Raw);

    let mut trailing_raw = first.clone();
    trailing_raw.raw.push(0);
    let trailing_root = reseal_root(6, &trailing_raw, 0, 2, independent_profile());
    let trailing_context = NativeWorkMembershipContext::new(6, trailing_root, context.total_be28).unwrap();
    assert_error(trailing_context.verify(trailing_raw.lower_be28, &trailing_raw), NativeWorkOpeningError::Raw);

    let mut noncanonical_raw = first.clone();
    noncanonical_raw.raw = noncanonical_v1_distance(&first.raw);
    let noncanonical_root = reseal_root(6, &noncanonical_raw, 0, 2, independent_profile());
    let noncanonical_context = NativeWorkMembershipContext::new(6, noncanonical_root, context.total_be28).unwrap();
    assert_error(
        noncanonical_context.verify(noncanonical_raw.lower_be28, &noncanonical_raw),
        NativeWorkOpeningError::Raw,
    );

    let mut changed_raw = first.clone();
    changed_raw.raw[10] ^= 1;
    assert_error(context.verify(changed_raw.lower_be28, &changed_raw), NativeWorkOpeningError::RootMismatch);

    let mut empty_raw = first.clone();
    empty_raw.raw.clear();
    assert_error(context.verify(first.lower_be28, &empty_raw), NativeWorkOpeningError::Raw);
    let mut oversized_raw = first.clone();
    oversized_raw.raw.resize(515, 0);
    assert_error(context.verify(first.lower_be28, &oversized_raw), NativeWorkOpeningError::Raw);
}

#[test]
fn c565_native_difficulty_aliases_are_preserved_and_invalid_work_isolated() {
    let (context, openings) = owned_case(6, &[0]);
    let first = &openings[0];
    let alias = 0x0300_0100;
    let canonical = 0x0201_0000;
    assert_eq!(work_tree_work::native_decode(alias).unwrap(), BigUint::from(256u32));
    assert_eq!(work_tree_work::native_decode(alias).unwrap(), work_tree_work::native_decode(canonical).unwrap());

    let mut aliased = first.clone();
    aliased.raw = header_with_nbits(&first.raw, alias);
    aliased.lower_be28 = [0; 28];
    aliased.upper_be28 = be28(&BigUint::from(256u32));
    let alias_root = reseal_root(6, &aliased, 0, 2, independent_profile());
    let alias_context = NativeWorkMembershipContext::new(6, alias_root, aliased.upper_be28).unwrap();
    assert!(alias_context.verify([0; 28], &aliased).is_ok());

    for n_bits in [0u32, 0x0100_0001, 0x0080_0001, (32u32 << 24) | 1] {
        let mut invalid = first.clone();
        invalid.raw = header_with_nbits(&first.raw, n_bits);
        let invalid_root = reseal_root(6, &invalid, 0, 2, independent_profile());
        let invalid_context = NativeWorkMembershipContext::new(6, invalid_root, context.total_be28).unwrap();
        assert_error(
            invalid_context.verify(invalid.lower_be28, &invalid),
            NativeWorkOpeningError::IntervalWork,
        );
    }
}

#[test]
fn c565_component_codec_roundtrips_and_rejects_isolated_framing_faults() {
    let (context, openings) = owned_case(6, &[0]);
    let opening = &openings[0];
    let bytes = opening.encode(&context).unwrap();
    assert_eq!(bytes.len(), FIXED_OVERHEAD + opening.raw.len() + 3 * 32);
    assert!(bytes.len() <= MAX_OPENING_BYTES);
    let decoded = NativeWorkOpening::decode(&context, &bytes).unwrap();
    assert_eq!(&decoded, opening);
    assert_eq!(decoded.encode(&context).unwrap(), bytes);
    assert!(context.verify_encoded(opening.lower_be28, &bytes).is_ok());

    let mut bad_work = opening.clone();
    let changed_upper = &BigUint::from_bytes_be(&bad_work.upper_be28) + BigUint::one();
    bad_work.upper_be28 = be28(&changed_upper);
    let synthetic_root = reseal_root(6, &bad_work, 0, 2, independent_profile());
    let bad_work_context = NativeWorkMembershipContext::new(6, synthetic_root, be28(&changed_upper)).unwrap();
    let bad_work_bytes = bad_work.encode(&bad_work_context).unwrap();
    assert_error(
        bad_work_context.verify(bad_work.lower_be28, &bad_work),
        NativeWorkOpeningError::IntervalWork,
    );
    assert_error(
        bad_work_context.verify_encoded(bad_work.lower_be28, &bad_work_bytes),
        NativeWorkOpeningError::IntervalWork,
    );

    let mut bad = bytes.clone();
    bad[0] ^= 1;
    assert_error(NativeWorkOpening::decode(&context, &bad), NativeWorkOpeningError::Encoding);
    assert_error(NativeWorkOpening::decode(&context, &bytes[..bytes.len() - 1]), NativeWorkOpeningError::Encoding);
    let mut trailing = bytes.clone();
    trailing.push(0);
    assert_error(NativeWorkOpening::decode(&context, &trailing), NativeWorkOpeningError::Encoding);
    let mut zero_raw = bytes.clone();
    zero_raw[68..70].copy_from_slice(&0u16.to_be_bytes());
    assert_error(NativeWorkOpening::decode(&context, &zero_raw), NativeWorkOpeningError::Encoding);
    let mut too_long_raw = bytes.clone();
    too_long_raw[68..70].copy_from_slice(&515u16.to_be_bytes());
    assert_error(NativeWorkOpening::decode(&context, &too_long_raw), NativeWorkOpeningError::Encoding);

    let mut missing_sibling = bytes.clone();
    missing_sibling.truncate(missing_sibling.len() - 32);
    assert_error(NativeWorkOpening::decode(&context, &missing_sibling), NativeWorkOpeningError::Encoding);
    let mut extra_sibling = bytes.clone();
    extra_sibling.extend_from_slice(&[0; 32]);
    assert_error(NativeWorkOpening::decode(&context, &extra_sibling), NativeWorkOpeningError::Encoding);
    assert_error(NativeWorkOpening::decode(&context, &vec![0; MAX_OPENING_BYTES + 1]), NativeWorkOpeningError::Encoding);

    let mut invalid_position = bytes.clone();
    invalid_position[8..12].copy_from_slice(&5u32.to_be_bytes());
    assert_error(NativeWorkOpening::decode(&context, &invalid_position), NativeWorkOpeningError::Position);
    let mut malformed_typed = opening.clone();
    malformed_typed.siblings.pop();
    assert_error(malformed_typed.encode(&context), NativeWorkOpeningError::PathShape);
    let mut extra_typed = opening.clone();
    extra_typed.siblings.push([0; 32]);
    assert_error(extra_typed.encode(&context), NativeWorkOpeningError::PathShape);
    assert_error(context.verify(opening.lower_be28, &extra_typed), NativeWorkOpeningError::PathShape);
}

#[test]
fn c565_max_descriptor_depth_codec_and_synthetic_membership_are_bounded() {
    let prefix = fixture_prefix(3);
    let (lower_be28, upper_be28) = prefix.interval(2).unwrap();
    let raw = prefix.raw(2).unwrap().to_vec();
    drop(prefix);
    let headers = (1usize << 31) - 1;
    let mut opening = NativeWorkOpening::new(0, lower_be28, upper_be28, raw, vec![[0x5a; 32]; 31]);
    let total = upper_be28;
    let initial = NativeWorkMembershipContext::new(headers, [0; 32], total).unwrap();
    assert_eq!(initial.depth(), 31);
    let decoded = ergo_header_core::Header::decode(&opening.raw, None).unwrap();
    let synthetic_root = reseal_root(headers, &opening, 0, decoded.height, independent_profile());
    let context = NativeWorkMembershipContext::new(headers, synthetic_root, total).unwrap();
    let bytes = opening.encode(&context).unwrap();
    assert_eq!(MAX_OPENING_BYTES, 1576);
    assert_eq!(bytes.len(), FIXED_OVERHEAD + opening.raw.len() + 31 * 32);
    assert!(bytes.len() <= MAX_OPENING_BYTES);
    opening = NativeWorkOpening::decode(&context, &bytes).unwrap();
    assert!(context.verify_encoded(lower_be28, &opening.encode(&context).unwrap()).is_ok());
}


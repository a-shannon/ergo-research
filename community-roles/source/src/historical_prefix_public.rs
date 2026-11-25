//! Native expected public statement for the bounded retained-header prefix.
//!
//! This path derives public bytes from canonical RAW headers and native
//! compact-work decoding. It deliberately does not use the field witness
//! builder or the circuit-side leaf assignment.

use num_bigint::BigUint;

use crate::{
    header_order::MAINNET_GENESIS, historical_prefix_witness, work_tree_fixed_hash::PROFILE_PREFIX,
    work_tree_work::native_decode,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct NativePublic {
    pub(crate) headers: u64,
    pub(crate) root: [u8; 32],
    pub(crate) total: [u8; 28],
    pub(crate) tip: [u8; 32],
    pub(crate) tip_time: i64,
}

// One code-owned policy shared by the unchanged encoder and the tiny byte receiver.
pub(crate) const PROFILE: &[u8] = b"historical-prefix-n3-common-seven-daa-v2";
pub(crate) const PROFILE_N4: &[u8] = b"historical-prefix-n4-common-seven-daa-v2";
pub(crate) const ROLES: [&[u8]; 7] = [b"corepool11", b"retained-header", b"worktree-roster",
    b"point-membership", b"height-work-and-daa-roster-v2", b"header-id", b"metadata-order"];
pub(crate) const FRAME_BYTES: usize = 568;

/// Untrusted fields only. No RAW, expected public, commitment or transcript input.
pub(crate) fn decode_tiny_candidate(bytes: &[u8]) -> Result<NativePublic, String> {
    struct Cursor<'a> { bytes: &'a [u8], at: usize }
    impl<'a> Cursor<'a> {
        fn take(&mut self, n: usize) -> Result<&'a [u8], String> {
            let end = self.at.checked_add(n).ok_or("generic37 cursor overflow")?;
            let value = self.bytes.get(self.at..end).ok_or("generic37 truncated frame")?;
            self.at = end; Ok(value)
        }
        fn fixed<const N: usize>(&mut self) -> Result<[u8; N], String> {
            self.take(N)?.try_into().map_err(|_| "generic37 fixed field".into())
        }
        fn integer(&mut self) -> Result<u64, String> { Ok(u64::from_le_bytes(self.fixed()?)) }
    }
    if bytes.len() != FRAME_BYTES { return Err("generic37 frame extent".into()); }
    let mut c = Cursor { bytes, at: 0 };
    let profile = c.take(PROFILE.len())?;
    if profile != PROFILE && profile != PROFILE_N4 { return Err("generic37 profile policy".into()); }
    if c.take(32)? != MAINNET_GENESIS { return Err("generic37 genesis policy".into()); }
    if c.take(32)? != [0u8; 32] { return Err("generic37 parent anchor".into()); }
    let headers = c.integer()?;
    let expected_profile = match headers { 3 => PROFILE, 4 => PROFILE_N4,
        _ => return Err("generic37 tiny header policy".into()) };
    if profile != expected_profile { return Err("generic37 profile/header pairing".into()); }
    for expected in [4u64, 2, 22] {
        if c.integer()? != expected { return Err("generic37 cheap geometry".into()); }
    }
    let public = NativePublic { headers, root: c.fixed()?, total: c.fixed()?, tip: c.fixed()?,
        tip_time: i64::from_le_bytes(c.fixed()?) };
    // These are the admitted tiny policy, not dimensions accepted from a package.
    for (role, (input, row)) in [22u64,22,22,15,22,22,22].into_iter()
        .zip([23u64,21,21,16,22,11,14]).enumerate() {
        if c.integer()? != role as u64 { return Err("generic37 role order".into()); }
        if c.integer()? != ROLES[role].len() as u64 { return Err("generic37 role tag extent".into()); }
        if c.take(ROLES[role].len())? != ROLES[role] { return Err("generic37 role tag".into()); }
        if c.integer()? != input || c.integer()? != row { return Err("generic37 role geometry".into()); }
    }
    if c.at != bytes.len() { return Err("generic37 trailing frame".into()); }
    Ok(public)
}

/// Independently derive the bounded N3/N4 public statement from retained RAW.
pub(crate) fn expected(headers: u64) -> Result<NativePublic, String> {
    if !matches!(headers, 3 | 4) {
        return Err("native public supports exactly three or four headers".into());
    }
    let header_count =
        u32::try_from(headers).map_err(|_| "native public header count does not fit u32")?;
    let header_len =
        usize::try_from(headers).map_err(|_| "native public header count does not fit usize")?;
    let retained = historical_prefix_witness::retained_headers_n(header_len)?;
    if retained.len() != header_len {
        return Err("native public retained header count mismatch".into());
    }

    let mut raw_headers: Vec<Vec<u8>> = Vec::with_capacity(header_len);
    for (index, header) in retained.iter().enumerate() {
        let expected_height = u32::try_from(
            index
                .checked_add(1)
                .ok_or("native public header index overflow")?,
        )
        .map_err(|_| "native public height does not fit u32")?;
        if header.height != expected_height {
            return Err("native public prefix heights are not contiguous".into());
        }
        let raw = header
            .encode()
            .map_err(|error| format!("native public header encode: {error:?}"))?;
        let decoded = ergo_header_core::Header::decode(&raw, None)
            .map_err(|error| format!("native public canonical decode: {error:?}"))?;
        if decoded.encode().map_err(|error| format!("{error:?}"))? != raw {
            return Err("native public RAW header is not canonical".into());
        }
        let id = ergo_header_core::blake2b256(&raw);
        if index == 0 {
            if header.parent_id != [0; 32] || id != MAINNET_GENESIS {
                return Err("native public fixed genesis identity mismatch".into());
            }
        } else if header.parent_id != ergo_header_core::blake2b256(&raw_headers[index - 1]) {
            return Err("native public parent identity mismatch".into());
        }
        raw_headers.push(raw);
    }

    let mut profile_preimage = Vec::with_capacity(PROFILE_PREFIX.len() + MAINNET_GENESIS.len());
    profile_preimage.extend_from_slice(PROFILE_PREFIX);
    profile_preimage.extend_from_slice(&MAINNET_GENESIS);
    let profile = ergo_header_core::blake2b256(&profile_preimage);

    let leaf_count = header_len
        .checked_sub(1)
        .ok_or("native public leaf count underflow")?;
    let padded_leaves = leaf_count
        .checked_next_power_of_two()
        .ok_or("native public leaf padding overflow")?;
    let mut level_digests = Vec::with_capacity(padded_leaves);
    let mut lower = BigUint::default();
    for (header, raw) in retained.iter().skip(1).zip(raw_headers.iter().skip(1)) {
        let difficulty = native_decode(header.n_bits)?;
        if difficulty == BigUint::default() || difficulty.bits() > 224 {
            return Err("native public difficulty is outside positive U224".into());
        }
        let upper = &lower + &difficulty;
        if upper.bits() > 224 {
            return Err("native public cumulative work exceeds U224".into());
        }
        let lower_bytes = be28(&lower)?;
        let upper_bytes = be28(&upper)?;
        let raw_length = u16::try_from(raw.len())
            .map_err(|_| "native public header RAW length does not fit u16")?;
        let mut preimage = Vec::with_capacity(1 + 32 + 4 + 4 + 28 + 28 + 2 + raw.len());
        preimage.push(b'L');
        preimage.extend_from_slice(&profile);
        preimage.extend_from_slice(&header_count.to_be_bytes());
        preimage.extend_from_slice(&header.height.to_be_bytes());
        preimage.extend_from_slice(&lower_bytes);
        preimage.extend_from_slice(&upper_bytes);
        preimage.extend_from_slice(&raw_length.to_be_bytes());
        preimage.extend_from_slice(raw);
        level_digests.push(ergo_header_core::blake2b256(&preimage));
        lower = upper;
    }
    if level_digests.len() != leaf_count || lower == BigUint::default() || lower.bits() > 224 {
        return Err("native public leaf/work census mismatch".into());
    }

    for slot in leaf_count..padded_leaves {
        let slot =
            u32::try_from(slot).map_err(|_| "native public padding slot does not fit u32")?;
        let mut preimage = Vec::with_capacity(1 + 32 + 4 + 4);
        preimage.push(b'P');
        preimage.extend_from_slice(&profile);
        preimage.extend_from_slice(&header_count.to_be_bytes());
        preimage.extend_from_slice(&slot.to_be_bytes());
        level_digests.push(ergo_header_core::blake2b256(&preimage));
    }

    let mut level = 1usize;
    while level_digests.len() > 1 {
        if level_digests.len() % 2 != 0 {
            return Err("native public Merkle layer is not pairwise".into());
        }
        let level_byte =
            u8::try_from(level).map_err(|_| "native public Merkle level does not fit u8")?;
        let parent_count = level_digests.len() / 2;
        let mut parents = Vec::with_capacity(parent_count);
        for (position, pair) in level_digests.chunks_exact(2).enumerate() {
            let position = u32::try_from(position)
                .map_err(|_| "native public Merkle position does not fit u32")?;
            let mut preimage = Vec::with_capacity(1 + 1 + 4 + 32 + 32);
            preimage.push(b'N');
            preimage.push(level_byte);
            preimage.extend_from_slice(&position.to_be_bytes());
            preimage.extend_from_slice(&pair[0]);
            preimage.extend_from_slice(&pair[1]);
            parents.push(ergo_header_core::blake2b256(&preimage));
        }
        level_digests = parents;
        level = level
            .checked_add(1)
            .ok_or("native public Merkle level overflow")?;
    }

    let tip = raw_headers
        .last()
        .ok_or("native public tip RAW is absent")?;
    let tip_header = retained
        .last()
        .ok_or("native public tip header is absent")?;
    Ok(NativePublic {
        headers: u64::from(header_count),
        root: level_digests[0],
        total: be28(&lower)?,
        tip: ergo_header_core::blake2b256(tip),
        tip_time: tip_header.timestamp,
    })
}

fn be28(value: &BigUint) -> Result<[u8; 28], String> {
    let bytes = value.to_bytes_be();
    if bytes.len() > 28 || value.bits() > 224 {
        return Err("native public integer exceeds U224".into());
    }
    let mut encoded = [0u8; 28];
    encoded[28 - bytes.len()..].copy_from_slice(&bytes);
    Ok(encoded)
}

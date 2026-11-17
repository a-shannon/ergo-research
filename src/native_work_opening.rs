//! Bounded, source-free membership of one RAW header and U224 work interval
//! under a caller-supplied fixed-tree context. This is not a structural
//! certificate and does not perform native PoW validation.

use blake2::{digest::consts::U32, Blake2b, Digest};
use num_bigint::BigUint;
use num_traits::Zero;
use std::fmt;

use crate::{
    header_order,
    work_tree_fixed_hash::{self as fixed, FixedProfile},
    work_tree_leaf_hash::{self as leaf, LeafProfile},
    work_tree_wiring::Descriptor,
    work_tree_work,
};

const MAGIC: &[u8; 8] = b"NIPOWP01";
const RAW_MAX: usize = 514;
const DEPTH_MAX: usize = 31;
const FIXED_OVERHEAD: usize = 70;
pub(crate) const MAX_OPENING_BYTES: usize = FIXED_OVERHEAD + RAW_MAX + DEPTH_MAX * 32;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum NativeWorkOpeningError {
    Context,
    Coordinate,
    Position,
    Encoding,
    Raw,
    IntervalWork,
    PathShape,
    RootMismatch,
}

impl fmt::Display for NativeWorkOpeningError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Context => "native work membership context rejected",
            Self::Coordinate => "native work coordinate outside supplied total",
            Self::Position => "native work leaf position rejected",
            Self::Encoding => "native work opening encoding rejected",
            Self::Raw => "native work RAW header rejected",
            Self::IntervalWork => "native work interval/difficulty rejected",
            Self::PathShape => "native work opening path shape rejected",
            Self::RootMismatch => "native work opening root mismatch",
        })
    }
}

impl std::error::Error for NativeWorkOpeningError {}

/// Public context for one fixed-tree membership check. The fields are
/// caller-supplied statement data; construction does not certify the tree.
pub(crate) struct NativeWorkMembershipContext {
    headers: usize,
    root: [u8; 32],
    total_be28: [u8; 28],
    total: BigUint,
    descriptor: Descriptor,
    leaf_profile: LeafProfile,
    fixed_profile: FixedProfile,
    profile: [u8; 32],
}

/// A bounded opening packet after framing has been parsed. No caller may
/// choose hash tags, directions, node positions, levels, or a profile.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct NativeWorkOpening {
    position: u32,
    lower_be28: [u8; 28],
    upper_be28: [u8; 28],
    raw: Vec<u8>,
    siblings: Vec<[u8; 32]>,
}

/// Successful membership only. This owns its header/RAW and records the
/// supplied context; it is not a verified structural certificate or PoW token.
pub(crate) struct NativeWorkMembership {
    headers: usize,
    root: [u8; 32],
    total_be28: [u8; 28],
    profile: [u8; 32],
    coordinate_be28: [u8; 28],
    position: u32,
    height: u32,
    lower_be28: [u8; 28],
    upper_be28: [u8; 28],
    raw: Vec<u8>,
    header: ergo_header_core::Header,
}

impl NativeWorkMembershipContext {
    pub(crate) fn new(
        headers: usize,
        root: [u8; 32],
        total_be28: [u8; 28],
    ) -> Result<Self, NativeWorkOpeningError> {
        if !(3..=(1usize << 31) - 1).contains(&headers) {
            return Err(NativeWorkOpeningError::Context);
        }
        let total = BigUint::from_bytes_be(&total_be28);
        if total.is_zero() {
            return Err(NativeWorkOpeningError::Context);
        }
        let descriptor = Descriptor::new(headers, root)
            .and_then(|d| { d.validate()?; Ok(d) })
            .map_err(|_| NativeWorkOpeningError::Context)?;
        let leaf_profile = LeafProfile::new(headers, root)
            .and_then(|p| { p.validate()?; Ok(p) })
            .map_err(|_| NativeWorkOpeningError::Context)?;
        let fixed_profile = FixedProfile::new(headers, root)
            .and_then(|p| { p.validate()?; Ok(p) })
            .map_err(|_| NativeWorkOpeningError::Context)?;
        if leaf_profile.tree != descriptor || fixed_profile.tree != descriptor {
            return Err(NativeWorkOpeningError::Context);
        }

        let mut profile_bytes = fixed::PROFILE_PREFIX.to_vec();
        profile_bytes.extend_from_slice(&header_order::MAINNET_GENESIS);
        let profile: [u8; 32] = Blake2b::<U32>::digest(profile_bytes).into();
        Ok(Self {
            headers, root, total_be28, total, descriptor, leaf_profile, fixed_profile, profile,
        })
    }

    fn depth(&self) -> usize {
        self.descriptor.leaves.trailing_zeros() as usize
    }

    fn validate_shape(
        &self,
        opening: &NativeWorkOpening,
    ) -> Result<usize, NativeWorkOpeningError> {
        let position = usize::try_from(opening.position)
            .map_err(|_| NativeWorkOpeningError::Position)?;
        if position >= self.descriptor.genuine
            || self.descriptor.validate_leaf_position(position, position).is_err()
        {
            return Err(NativeWorkOpeningError::Position);
        }
        if opening.raw.is_empty() || opening.raw.len() > RAW_MAX {
            return Err(NativeWorkOpeningError::Raw);
        }
        if opening.siblings.len() != self.depth() {
            return Err(NativeWorkOpeningError::PathShape);
        }
        Ok(position)
    }

    pub(crate) fn verify(
        &self,
        coordinate_be28: [u8; 28],
        opening: &NativeWorkOpening,
    ) -> Result<NativeWorkMembership, NativeWorkOpeningError> {
        let position = self.validate_shape(opening)?;
        let coordinate = BigUint::from_bytes_be(&coordinate_be28);
        if coordinate >= self.total {
            return Err(NativeWorkOpeningError::Coordinate);
        }
        let lower = BigUint::from_bytes_be(&opening.lower_be28);
        let upper = BigUint::from_bytes_be(&opening.upper_be28);
        if lower >= upper || lower > coordinate || coordinate >= upper || upper > self.total {
            return Err(NativeWorkOpeningError::IntervalWork);
        }

        let expected_height = u32::try_from(position)
            .ok()
            .and_then(|p| p.checked_add(2))
            .ok_or(NativeWorkOpeningError::Position)?;
        let header = ergo_header_core::Header::decode(&opening.raw, None)
            .map_err(|_| NativeWorkOpeningError::Raw)?;
        if header.height != expected_height
            || header.encode().map_err(|_| NativeWorkOpeningError::Raw)? != opening.raw
        {
            return Err(NativeWorkOpeningError::Raw);
        }
        let work = work_tree_work::native_decode(header.n_bits)
            .map_err(|_| NativeWorkOpeningError::IntervalWork)?;
        if &upper - &lower != work {
            return Err(NativeWorkOpeningError::IntervalWork);
        }

        let mut digest = leaf::native_leaf_preimage_hash(
            &self.leaf_profile,
            position,
            &opening.raw,
            expected_height,
            opening.lower_be28,
            opening.upper_be28,
            self.profile,
        )
        .map_err(|_| NativeWorkOpeningError::Raw)?;

        for (level_index, sibling) in opening.siblings.iter().enumerate() {
            let level = level_index + 1;
            let (base, count) = self.descriptor.level(level)
                .map_err(|_| NativeWorkOpeningError::PathShape)?;
            let parent_position = position >> level;
            if parent_position >= count {
                return Err(NativeWorkOpeningError::PathShape);
            }
            let parent_slot = base.checked_add(parent_position)
                .ok_or(NativeWorkOpeningError::PathShape)?;
            let child_position = position >> (level - 1);
            let (left, right) = if child_position & 1 == 0 {
                (digest, *sibling)
            } else {
                (*sibling, digest)
            };
            let level_byte = u8::try_from(level)
                .map_err(|_| NativeWorkOpeningError::PathShape)?;
            let node_position = u32::try_from(parent_position)
                .map_err(|_| NativeWorkOpeningError::PathShape)?;
            let mut preimage = Vec::with_capacity(70);
            preimage.push(b'N');
            preimage.push(level_byte);
            preimage.extend_from_slice(&node_position.to_be_bytes());
            preimage.extend_from_slice(&left);
            preimage.extend_from_slice(&right);
            if preimage.len() != 70 {
                return Err(NativeWorkOpeningError::PathShape);
            }
            digest = leaf::native_fixed_preimage_hash(
                &self.fixed_profile, parent_slot, &preimage,
            )
            .map_err(|_| NativeWorkOpeningError::PathShape)?;
        }
        if digest != self.root {
            return Err(NativeWorkOpeningError::RootMismatch);
        }

        Ok(NativeWorkMembership {
            headers: self.headers,
            root: self.root,
            total_be28: self.total_be28,
            profile: self.profile,
            coordinate_be28,
            position: opening.position,
            height: expected_height,
            lower_be28: opening.lower_be28,
            upper_be28: opening.upper_be28,
            raw: opening.raw.clone(),
            header,
        })
    }

    pub(crate) fn verify_encoded(
        &self,
        coordinate_be28: [u8; 28],
        bytes: &[u8],
    ) -> Result<NativeWorkMembership, NativeWorkOpeningError> {
        let opening = NativeWorkOpening::decode(self, bytes)?;
        if opening.encode(self)?.as_slice() != bytes {
            return Err(NativeWorkOpeningError::Encoding);
        }
        self.verify(coordinate_be28, &opening)
    }
}

impl NativeWorkOpening {
    pub(crate) fn new(
        position: u32,
        lower_be28: [u8; 28],
        upper_be28: [u8; 28],
        raw: Vec<u8>,
        siblings: Vec<[u8; 32]>,
    ) -> Self {
        Self { position, lower_be28, upper_be28, raw, siblings }
    }

    pub(crate) fn encode(
        &self,
        context: &NativeWorkMembershipContext,
    ) -> Result<Vec<u8>, NativeWorkOpeningError> {
        context.validate_shape(self)?;
        let packet_len = FIXED_OVERHEAD
            .checked_add(self.raw.len())
            .and_then(|n| n.checked_add(self.siblings.len().checked_mul(32)?))
            .filter(|n| *n <= MAX_OPENING_BYTES)
            .ok_or(NativeWorkOpeningError::Encoding)?;
        let raw_len = u16::try_from(self.raw.len())
            .map_err(|_| NativeWorkOpeningError::Encoding)?;
        let mut out = Vec::with_capacity(packet_len);
        out.extend_from_slice(MAGIC);
        out.extend_from_slice(&self.position.to_be_bytes());
        out.extend_from_slice(&self.lower_be28);
        out.extend_from_slice(&self.upper_be28);
        out.extend_from_slice(&raw_len.to_be_bytes());
        out.extend_from_slice(&self.raw);
        for sibling in &self.siblings {
            out.extend_from_slice(sibling);
        }
        if out.len() != packet_len {
            return Err(NativeWorkOpeningError::Encoding);
        }
        Ok(out)
    }

    pub(crate) fn decode(
        context: &NativeWorkMembershipContext,
        bytes: &[u8],
    ) -> Result<Self, NativeWorkOpeningError> {
        if bytes.len() < FIXED_OVERHEAD || bytes.len() > MAX_OPENING_BYTES || &bytes[..8] != MAGIC {
            return Err(NativeWorkOpeningError::Encoding);
        }
        let position = u32::from_be_bytes(
            bytes[8..12].try_into().map_err(|_| NativeWorkOpeningError::Encoding)?,
        );
        let lower_be28 = bytes[12..40].try_into()
            .map_err(|_| NativeWorkOpeningError::Encoding)?;
        let upper_be28 = bytes[40..68].try_into()
            .map_err(|_| NativeWorkOpeningError::Encoding)?;
        let raw_len = usize::from(u16::from_be_bytes(
            bytes[68..70].try_into().map_err(|_| NativeWorkOpeningError::Encoding)?,
        ));
        if raw_len == 0 || raw_len > RAW_MAX {
            return Err(NativeWorkOpeningError::Encoding);
        }
        let depth = context.depth();
        if depth > DEPTH_MAX {
            return Err(NativeWorkOpeningError::Context);
        }
        let expected_len = FIXED_OVERHEAD
            .checked_add(raw_len)
            .and_then(|n| n.checked_add(depth.checked_mul(32)?))
            .filter(|n| *n <= MAX_OPENING_BYTES)
            .ok_or(NativeWorkOpeningError::Encoding)?;
        if bytes.len() != expected_len {
            return Err(NativeWorkOpeningError::Encoding);
        }
        let siblings_start = FIXED_OVERHEAD + raw_len;
        let mut siblings = Vec::with_capacity(depth);
        for chunk in bytes[siblings_start..].chunks_exact(32) {
            siblings.push(chunk.try_into().map_err(|_| NativeWorkOpeningError::Encoding)?);
        }
        let opening = Self {
            position, lower_be28, upper_be28,
            raw: bytes[FIXED_OVERHEAD..siblings_start].to_vec(),
            siblings,
        };
        context.validate_shape(&opening)?;
        Ok(opening)
    }
}

impl NativeWorkMembership {
    pub(crate) fn headers(&self) -> usize { self.headers }
    pub(crate) fn root(&self) -> [u8; 32] { self.root }
    pub(crate) fn total_be28(&self) -> [u8; 28] { self.total_be28 }
    pub(crate) fn profile(&self) -> [u8; 32] { self.profile }
    pub(crate) fn coordinate_be28(&self) -> [u8; 28] { self.coordinate_be28 }
    pub(crate) fn position(&self) -> u32 { self.position }
    pub(crate) fn height(&self) -> u32 { self.height }
    pub(crate) fn interval_be28(&self) -> ([u8; 28], [u8; 28]) {
        (self.lower_be28, self.upper_be28)
    }
    pub(crate) fn raw(&self) -> &[u8] { &self.raw }
    pub(crate) fn header(&self) -> &ergo_header_core::Header { &self.header }
}

#[cfg(test)]
#[path = "native_work_opening_tests.rs"]
mod tests;


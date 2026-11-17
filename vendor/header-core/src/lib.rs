#![no_std]

//! Canonical full header bytes for Ergo commit 8995ff243b140e7fe716bd3204423dd35690c2e4.
//! This codec checks framing, canonical encoding and optional header identity.
//! It does not check consensus admission, ancestry, difficulty or proof of work.
extern crate alloc;

use alloc::vec::Vec;
use blake2::{digest::consts::U32, Blake2b, Digest};
use k256::{elliptic_curve::sec1::ToEncodedPoint, PublicKey};

/// Largest canonical representation: v1 with ten timestamp bytes, five height
/// bytes, two compressed points, eight nonce bytes and a 255-byte distance.
pub const MAX_HEADER_BYTES: usize = 514;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    UnexpectedEof,
    TrailingBytes,
    VlqOverflow,
    NonMinimalVlq,
    HeightOutOfRange,
    NonCanonicalPoint,
    InvalidPoint,
    NonCanonicalDistance,
    DistanceTooLong,
    ExtensionNotAllowed,
    ExtensionTooLong,
    PowVersionMismatch,
    NonCanonicalHeader,
    IdMismatch,
}

/// Canonical sigma-state 6.0.3 group encoding, including 33-byte infinity.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GroupElement([u8; 33]);

impl GroupElement {
    pub const INFINITY: Self = Self([0; 33]);

    pub fn from_bytes(bytes: [u8; 33]) -> Result<Self, Error> {
        if bytes[0] == 0 {
            return if bytes == [0; 33] {
                Ok(Self::INFINITY)
            } else {
                Err(Error::NonCanonicalPoint)
            };
        }
        if bytes[0] != 2 && bytes[0] != 3 {
            return Err(Error::InvalidPoint);
        }
        let point = PublicKey::from_sec1_bytes(&bytes).map_err(|_| Error::InvalidPoint)?;
        if point.to_encoded_point(true).as_bytes() != bytes {
            return Err(Error::NonCanonicalPoint);
        }
        Ok(Self(bytes))
    }

    pub const fn as_bytes(&self) -> &[u8; 33] {
        &self.0
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PowSolution {
    V1 {
        pk: GroupElement,
        w: GroupElement,
        nonce: [u8; 8],
        /// Unsigned big-endian magnitude. Under BC 1.66, zero is empty.
        distance: Vec<u8>,
    },
    V2 {
        pk: GroupElement,
        nonce: [u8; 8],
    },
}

/// Fields may be constructed or changed by callers; `encode` rechecks every
/// variable-length and version-dependent invariant before producing bytes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Header {
    pub version: i8,
    pub parent_id: [u8; 32],
    pub ad_proofs_root: [u8; 32],
    pub transactions_root: [u8; 32],
    pub state_root: [u8; 33],
    /// The native JVM Long interpretation, preserving all unsigned VLQ bits.
    pub timestamp: i64,
    pub extension_root: [u8; 32],
    /// Raw four-byte big-endian value; compact difficulty semantics are separate.
    pub n_bits: u32,
    pub height: u32,
    pub votes: [u8; 3],
    pub unparsed_bytes: Vec<u8>,
    pub pow: PowSolution,
}

impl Header {
    pub fn decode(bytes: &[u8], expected_id: Option<&[u8; 32]>) -> Result<Self, Error> {
        let mut reader = Reader { bytes, pos: 0 };
        let version = reader.byte()? as i8;
        let parent_id = reader.array()?;
        let ad_proofs_root = reader.array()?;
        let transactions_root = reader.array()?;
        let state_root = reader.array()?;
        let timestamp = reader.vlq()? as i64;
        let extension_root = reader.array()?;
        let n_bits = u32::from_be_bytes(reader.array()?);
        let height = reader.vlq()?;
        if height > i32::MAX as u64 {
            return Err(Error::HeightOutOfRange);
        }
        let votes = reader.array()?;
        let unparsed_bytes = if version > 1 {
            let len = reader.byte()? as usize;
            if version > 4 { reader.take(len)?.to_vec() } else { Vec::new() }
        } else {
            Vec::new()
        };
        let pk = GroupElement::from_bytes(reader.array()?)?;
        let pow = if version == 1 {
            let w = GroupElement::from_bytes(reader.array()?)?;
            let nonce = reader.array()?;
            let len = reader.byte()? as usize;
            let distance = reader.take(len)?.to_vec();
            PowSolution::V1 { pk, w, nonce, distance }
        } else {
            PowSolution::V2 { pk, nonce: reader.array()? }
        };
        if reader.pos != bytes.len() {
            return Err(Error::TrailingBytes);
        }
        let header = Self {
            version, parent_id, ad_proofs_root, transactions_root, state_root,
            timestamp, extension_root, n_bits, height: height as u32, votes,
            unparsed_bytes, pow,
        };
        let canonical = header.encode()?;
        if canonical != bytes {
            return Err(Error::NonCanonicalHeader);
        }
        if let Some(expected) = expected_id {
            if &blake2b256(&canonical) != expected {
                return Err(Error::IdMismatch);
            }
        }
        Ok(header)
    }

    pub fn encode(&self) -> Result<Vec<u8>, Error> {
        if self.height > i32::MAX as u32 {
            return Err(Error::HeightOutOfRange);
        }
        if self.version <= 4 && !self.unparsed_bytes.is_empty() {
            return Err(Error::ExtensionNotAllowed);
        }
        if self.unparsed_bytes.len() > u8::MAX as usize {
            return Err(Error::ExtensionTooLong);
        }
        match (&self.pow, self.version) {
            (PowSolution::V1 { distance, .. }, 1) => {
                if distance.len() > u8::MAX as usize {
                    return Err(Error::DistanceTooLong);
                }
                if distance.first() == Some(&0) {
                    return Err(Error::NonCanonicalDistance);
                }
            }
            (PowSolution::V2 { .. }, version) if version != 1 => {}
            _ => return Err(Error::PowVersionMismatch),
        }
        let mut out = Vec::with_capacity(MAX_HEADER_BYTES);
        out.push(self.version as u8);
        out.extend_from_slice(&self.parent_id);
        out.extend_from_slice(&self.ad_proofs_root);
        out.extend_from_slice(&self.transactions_root);
        out.extend_from_slice(&self.state_root);
        put_vlq(self.timestamp as u64, &mut out);
        out.extend_from_slice(&self.extension_root);
        out.extend_from_slice(&self.n_bits.to_be_bytes());
        put_vlq(self.height as u64, &mut out);
        out.extend_from_slice(&self.votes);
        if self.version > 1 {
            out.push(self.unparsed_bytes.len() as u8);
            out.extend_from_slice(&self.unparsed_bytes);
        }
        match &self.pow {
            PowSolution::V1 { pk, w, nonce, distance } => {
                out.extend_from_slice(pk.as_bytes());
                out.extend_from_slice(w.as_bytes());
                out.extend_from_slice(nonce);
                out.push(distance.len() as u8);
                out.extend_from_slice(distance);
            }
            PowSolution::V2 { pk, nonce } => {
                out.extend_from_slice(pk.as_bytes());
                out.extend_from_slice(nonce);
            }
        }
        debug_assert!(out.len() <= MAX_HEADER_BYTES);
        Ok(out)
    }

    pub fn id(&self) -> Result<[u8; 32], Error> {
        Ok(blake2b256(&self.encode()?))
    }
}

pub fn blake2b256(bytes: &[u8]) -> [u8; 32] {
    Blake2b::<U32>::digest(bytes).into()
}

fn put_vlq(mut value: u64, out: &mut Vec<u8>) {
    while value >= 128 {
        out.push((value as u8 & 0x7f) | 0x80);
        value >>= 7;
    }
    out.push(value as u8);
}

struct Reader<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> Reader<'a> {
    fn take(&mut self, len: usize) -> Result<&'a [u8], Error> {
        let end = self.pos.checked_add(len).ok_or(Error::UnexpectedEof)?;
        let bytes = self.bytes.get(self.pos..end).ok_or(Error::UnexpectedEof)?;
        self.pos = end;
        Ok(bytes)
    }

    fn byte(&mut self) -> Result<u8, Error> {
        Ok(self.take(1)?[0])
    }

    fn array<const N: usize>(&mut self) -> Result<[u8; N], Error> {
        let mut out = [0; N];
        out.copy_from_slice(self.take(N)?);
        Ok(out)
    }

    fn vlq(&mut self) -> Result<u64, Error> {
        let mut value = 0u64;
        for group in 0..10 {
            let byte = self.byte()?;
            if group == 9 && byte > 1 {
                return Err(Error::VlqOverflow);
            }
            let payload = byte & 0x7f;
            value |= (payload as u64) << (7 * group);
            if byte & 0x80 == 0 {
                if group != 0 && payload == 0 {
                    return Err(Error::NonMinimalVlq);
                }
                return Ok(value);
            }
        }
        Err(Error::VlqOverflow)
    }
}

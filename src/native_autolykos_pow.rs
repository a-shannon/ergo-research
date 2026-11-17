//! Native per-header Autolykos at Ergo 8995ff243b140e7fe716bd3204423dd35690c2e4.
//! Membership plus this predicate does not certify complete structural history.

use ergo_header_core::{GroupElement, Header, PowSolution};
use k256::{elliptic_curve::PrimeField, ProjectivePoint, PublicKey, Scalar};
use num_bigint::BigUint;
use num_traits::Zero;
use std::fmt;

use crate::native_work_opening::NativeWorkMembership;

const Q_BE: [u8; 32] = [
    0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xfe,
    0xba,0xae,0xdc,0xe6,0xaf,0x48,0xa0,0x3b,0xbf,0xd2,0x5e,0x8c,0xd0,0x36,0x41,0x41,
];
const N_BASE: u32 = 1 << 26;
const N_START: u32 = 614_400;
const N_PERIOD: u32 = 51_200;
const N_CAP_HEIGHT: u32 = 4_198_400;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum NativePowError { Encoding, Difficulty, Target, FinitePoint, Scalar, Equation, Sum, MembershipIdentity }

impl fmt::Display for NativePowError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Encoding => "native PoW canonical encoding rejected",
            Self::Difficulty => "native PoW positive difficulty rejected",
            Self::Target => "native PoW strict target rejected",
            Self::FinitePoint => "native PoW finite point rejected",
            Self::Scalar => "native PoW scalar rejected",
            Self::Equation => "native PoW V1 equation rejected",
            Self::Sum => "native PoW V2 sum encoding rejected",
            Self::MembershipIdentity => "native PoW membership/header identity rejected",
        })
    }
}
impl std::error::Error for NativePowError {}

/// Owns exactly the membership whose own header passed PoW. No detached header,
/// caller-supplied hit, or structural-validity token is accepted or returned.
pub(crate) struct NativePowMembership { membership: NativeWorkMembership }
impl NativePowMembership {
    pub(crate) fn membership(&self) -> &NativeWorkMembership { &self.membership }
    pub(crate) fn into_membership(self) -> NativeWorkMembership { self.membership }
}

pub(crate) fn verify_membership(membership: NativeWorkMembership) -> Result<NativePowMembership, NativePowError> {
    let raw = membership.header().encode().map_err(|_| NativePowError::Encoding)?;
    if raw.as_slice() != membership.raw() { return Err(NativePowError::MembershipIdentity); }
    verify_header(membership.header())?;
    Ok(NativePowMembership { membership })
}

pub(crate) fn verify_header(header: &Header) -> Result<(), NativePowError> {
    let message = message(header)?;
    let target = order() / difficulty(header.n_bits)?;
    if header.version == 1 {
        let PowSolution::V1 { pk, w, nonce, distance } = &header.pow else { return Err(NativePowError::Encoding); };
        let d = BigUint::from_bytes_be(distance);
        strict_target(&d, &target)?;
        let pk_point = finite_point(pk)?;
        let w_point = finite_point(w)?;
        let f = v1_scalar(&message, nonce, pk, w);
        v1_equation(pk_point, w_point, scalar(&d)?, scalar(&f)?)
    } else {
        let PowSolution::V2 { nonce, .. } = &header.pow else { return Err(NativePowError::Encoding); };
        strict_target(&BigUint::from_bytes_be(&v2_hit(&message, nonce, header.height)?), &target)
    }
}

fn order() -> BigUint { BigUint::from_bytes_be(&Q_BE) }
fn hash(bytes: &[u8]) -> [u8; 32] { ergo_header_core::blake2b256(bytes) }
fn hash_parts(parts: &[&[u8]]) -> [u8; 32] {
    use blake2::{digest::consts::U32, Blake2b, Digest};
    let mut h = Blake2b::<U32>::new();
    for part in parts { h.update(part); }
    h.finalize().into()
}

fn message(header: &Header) -> Result<[u8; 32], NativePowError> {
    let raw = header.encode().map_err(|_| NativePowError::Encoding)?;
    let tail = match (&header.pow, header.version) {
        (PowSolution::V1 { distance, .. }, 1) => 75usize.checked_add(distance.len()).ok_or(NativePowError::Encoding)?,
        (PowSolution::V2 { .. }, version) if version != 1 => 41,
        _ => return Err(NativePowError::Encoding),
    };
    let prefix = raw.len().checked_sub(tail).ok_or(NativePowError::Encoding)?;
    Ok(hash(&raw[..prefix]))
}

// This is the native compact integer, not the work-tree's extra U224 interval
// bound. Positive aliases and truncated low mantissa bits remain accepted.
fn difficulty(bits: u32) -> Result<BigUint, NativePowError> {
    if bits & 0x0080_0000 != 0 { return Err(NativePowError::Difficulty); }
    let exponent = bits >> 24;
    let mantissa = bits & 0x007f_ffff;
    let d = if exponent <= 3 { BigUint::from(mantissa >> (8 * (3 - exponent))) }
        else { BigUint::from(mantissa) << (8 * (exponent - 3)) as usize };
    if d.is_zero() { Err(NativePowError::Difficulty) } else { Ok(d) }
}
fn strict_target(value: &BigUint, target: &BigUint) -> Result<(), NativePowError> {
    if value < target { Ok(()) } else { Err(NativePowError::Target) }
}
fn scalar(value: &BigUint) -> Result<Scalar, NativePowError> {
    let bytes = magnitude32(value).map_err(|_| NativePowError::Scalar)?;
    Option::<Scalar>::from(Scalar::from_repr(bytes.into())).ok_or(NativePowError::Scalar)
}
fn finite_point(point: &GroupElement) -> Result<ProjectivePoint, NativePowError> {
    // SEC1 PublicKey excludes the canonical 33-byte sigma infinity encoding.
    PublicKey::from_sec1_bytes(point.as_bytes()).map(ProjectivePoint::from).map_err(|_| NativePowError::FinitePoint)
}
fn v1_equation(pk: ProjectivePoint, w: ProjectivePoint, d: Scalar, f: Scalar) -> Result<(), NativePowError> {
    // Intermediate identity results are legitimate; only supplied pk/w must be finite.
    if w * f == ProjectivePoint::GENERATOR * d + pk { Ok(()) } else { Err(NativePowError::Equation) }
}
fn table_size(height: u32, version: i8) -> u32 {
    let mut n = N_BASE;
    let capped = height.min(N_CAP_HEIGHT);
    if version != 1 && capped >= N_START {
        for _ in 0..=((capped - N_START) / N_PERIOD) { n = (n / 100) * 105; }
    }
    n
}
fn m_bytes() -> [u8; 8192] {
    let mut m = [0u8; 8192];
    for (i, chunk) in m.chunks_exact_mut(8).enumerate() { chunk.copy_from_slice(&(i as u64).to_be_bytes()); }
    m
}
fn indices(seed: &[u8; 32], n: u32) -> [u32; 32] {
    let mut extended = [0u8; 35];
    extended[..32].copy_from_slice(seed); extended[32..].copy_from_slice(&seed[..3]);
    std::array::from_fn(|i| u32::from_be_bytes(extended[i..i+4].try_into().expect("fixed four-byte window")) % n)
}
fn mod_q_with(mut digest: [u8; 32], mut rehash: impl FnMut(&[u8]) -> [u8; 32]) -> BigUint {
    // q > 2^255 implies floor(2^256/q)*q == q. No production retry cap.
    while digest >= Q_BE { digest = rehash(&digest); }
    BigUint::from_bytes_be(&digest)
}
fn v1_scalar(message: &[u8; 32], nonce: &[u8; 8], pk: &GroupElement, w: &GroupElement) -> BigUint {
    let seed = hash_parts(&[message, nonce]);
    let m = m_bytes();
    let mut sum = BigUint::zero();
    for index in indices(&seed, N_BASE) {
        let digest = hash_parts(&[&index.to_be_bytes(), &m, pk.as_bytes(), message, w.as_bytes()]);
        sum += mod_q_with(digest, hash);
    }
    sum % order()
}
fn magnitude32(value: &BigUint) -> Result<[u8; 32], NativePowError> {
    let bytes = value.to_bytes_be();
    if bytes.len() > 32 { return Err(NativePowError::Sum); }
    let mut out = [0u8; 32]; out[32-bytes.len()..].copy_from_slice(&bytes); Ok(out)
}
fn v2_hit(message: &[u8; 32], nonce: &[u8; 8], height: u32) -> Result<[u8; 32], NativePowError> {
    let n = table_size(height, 2);
    let height_bytes = height.to_be_bytes();
    let m = m_bytes();
    let digest = hash_parts(&[message, nonce]);
    let preindex = (u64::from_be_bytes(digest[24..].try_into().expect("fixed eight-byte suffix")) % u64::from(n)) as u32;
    let first = hash_parts(&[&preindex.to_be_bytes(), &height_bytes, &m]);
    let seed = hash_parts(&[&first[1..], message, nonce]);
    let mut sum = BigUint::zero();
    for index in indices(&seed, n) {
        let element = hash_parts(&[&index.to_be_bytes(), &height_bytes, &m]);
        sum += BigUint::from_bytes_be(&element[1..]);
    }
    // The 32 31-byte terms fit 253 bits. They are NOT reduced modulo q.
    Ok(hash(&magnitude32(&sum)?))
}

#[cfg(test)]
#[path = "native_autolykos_pow_tests.rs"]
mod tests;

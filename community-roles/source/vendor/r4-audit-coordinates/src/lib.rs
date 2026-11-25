//! Work-coordinate derivation for the local r4 audit framing candidate.
//! These coordinates alone carry no history or admission authority.

use num_bigint::BigUint;
use sha2::{Digest, Sha512};

pub type Work = [u8; 28];
pub const DRAWS_PER_SCALE: u32 = 466;
const NAMESPACE_TAG: &[u8] = b"Ergo-NiPoPoW-V2/audit/r4/1\0";

fn to_work(x: &BigUint) -> Result<Work, &'static str> {
    let bytes = x.to_bytes_be();
    let mut out = [0; 28];
    let start = out.len().checked_sub(bytes.len()).ok_or("work exceeds U224")?;
    out[start..].copy_from_slice(&bytes);
    Ok(out)
}

fn namespace(x: &[u8], proof: &[u8]) -> Result<Sha512, &'static str> {
    if x.is_empty() || proof.is_empty() {
        return Err("empty structural statement or proof");
    }
    let mut state = Sha512::new();
    state.update(NAMESPACE_TAG);
    for field in [x, proof] {
        let len = u64::try_from(field.len()).map_err(|_| "structural field length exceeds U64")?;
        state.update(len.to_be_bytes());
        state.update(field);
    }
    Ok(state)
}

fn draw(
    scale: &BigUint, start: &BigUint, cutoff: &BigUint,
    mut oracle: impl FnMut(u32) -> [u8; 64],
) -> Result<Work, &'static str> {
    for attempt in [1, 2] {
        let value = BigUint::from_bytes_be(&oracle(attempt));
        if value < *cutoff {
            return to_work(&(start + value % scale));
        }
    }
    Err("both audit attempts rejected")
}

/// Retains every draw, including repeats, in scale and sample order.
/// The caller supplying these bytes determines the proposed audit namespace.
/// Certificate consumers must obtain them from completed structural verification.
pub fn coordinates(
    canonical_x: &[u8], complete_proof: &[u8], work: Work, following_work: Work,
) -> Result<Vec<Work>, &'static str> {
    let total = BigUint::from_bytes_be(&work);
    let mut scale = BigUint::from_bytes_be(&following_work);
    if scale == BigUint::default() || scale > total {
        return Err("expected 0 < F <= W");
    }
    let prefix = namespace(canonical_x, complete_proof)?;
    let space = BigUint::from(1u8) << 512usize;
    let mut result = Vec::new();
    loop {
        let cutoff = &space - (&space % &scale);
        let start = &total - &scale;
        let mut scale_state = prefix.clone();
        scale_state.update(to_work(&scale)?);
        for index in 0..DRAWS_PER_SCALE {
            let mut index_state = scale_state.clone();
            index_state.update(index.to_be_bytes());
            result.push(draw(&scale, &start, &cutoff, |attempt| {
                let mut state = index_state.clone();
                state.update(attempt.to_be_bytes());
                state.finalize().into()
            })?);
        }
        if scale == total { break; }
        scale = (scale << 1usize).min(total.clone());
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn small(x: u8) -> Work {
        let mut result = [0; 28];
        result[27] = x;
        result
    }

    #[test]
    fn width_cutoff_retry_and_abort() {
        // For ell=3, 2^512 mod ell=1. The largest 512-bit word is rejected.
        let three = BigUint::from(3u8);
        let cutoff = (BigUint::from(1u8) << 512usize) - 1u8;
        let mut calls = Vec::new();
        let coordinate = draw(&three, &BigUint::from(7u8), &cutoff, |attempt| {
            calls.push(attempt);
            if attempt == 1 { [255; 64] } else { [0; 64] }
        }).unwrap();
        assert_eq!(calls, [1, 2]);
        assert_eq!(coordinate, small(7));
        let mut below = [255; 64];
        below[63] = 254;
        assert_eq!(draw(&three, &BigUint::from(7u8), &cutoff, |attempt| {
            assert_eq!(attempt, 1); below
        }), Ok(small(9)));
        assert!(draw(&three, &BigUint::default(), &cutoff, |_| [255; 64]).is_err());
        // Divisor two has no rejected words, even when X = 2^512 - 1.
        let space = BigUint::from(1u8) << 512usize;
        assert_eq!(draw(&BigUint::from(2u8), &BigUint::default(), &space, |attempt| {
            assert_eq!(attempt, 1); [255; 64]
        }), Ok(small(1)));
    }

    #[test]
    fn schedule_and_domain_fields() {
        let coord = |x: &[u8], p: &[u8], w, f| coordinates(x, p, small(w), small(f));
        let draws = coord(b"xy", b"z", 10, 3).unwrap();
        // The exact scales are 3, 6 and 10. Keep multiplicity at all scales.
        assert_eq!(draws.len(), 3 * 466);
        for (chunk, min) in draws.chunks_exact(466).zip([7, 4, 0]) {
            assert!(chunk.iter().all(|v| small(min) <= *v && *v < small(10)));
        }
        assert_ne!(draws, coord(b"x", b"yz", 10, 3).unwrap());
        assert_ne!(draws, coord(b"xY", b"z", 10, 3).unwrap());
        assert_ne!(draws, coord(b"xy", b"Z", 10, 3).unwrap());
        assert_eq!(coord(b"x", b"p", 8, 2).unwrap().len(), 3 * 466);
        assert_eq!(coord(b"x", b"p", 3, 3).unwrap().len(), 466);
        assert_eq!(coord(b"x", b"p", 1, 1).unwrap(), vec![small(0); 466]);
        for (w,f) in [(0,0), (9,0), (8,9)] { assert!(coord(b"x", b"p", w, f).is_err()); }
        assert!(coord(b"", b"p", 1, 1).is_err());
        assert!(coord(b"x", b"", 1, 1).is_err());
    }
}

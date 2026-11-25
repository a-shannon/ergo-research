//! Exact multilinear wiring sums for a masked, non-wrapping index shift.
//! This module checks an index kernel, not the DAA branch/sampler semantics.
use ark_bn254::Fr;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RightIndex {
    SameRow,
    GlobalZero,
}

fn eq_bit(point: Fr, bit: u8) -> Fr {
    if bit == 0 { Fr::from(1u64)-point } else { point }
}

fn subtract_bit(bit: u8, operand: u64, position: usize, borrow: usize) -> (u8, usize) {
    let difference = bit as i8 - ((operand >> position) & 1) as i8 - borrow as i8;
    (difference.rem_euclid(2) as u8, usize::from(difference < 0))
}

/// Sum eq(r,i) eq(u,i-offset) eq(v,right(i)) over lo <= i < hi,
/// i >= offset, and i divisible by 2^align_log. Points use LSB-first bits.
///
/// Uses eight states (the three subtraction borrows), at most 16*h+8
/// transitions and at most 48*h+h+8 field multiplications, and constant scratch
/// space. The final forced-zero bit has no multilinear weight; it is needed
/// when hi or offset equals 2^h. No table proportional to 2^h is allocated.
pub fn evaluate_shift(
    r: &[Fr], u: &[Fr], v: &[Fr], offset: u64, lo: u64, hi: u64,
    align_log: usize, right: RightIndex,
) -> Result<Fr, String> {
    let h = r.len();
    if h > 63 || u.len() != h || v.len() != h {
        return Err("index points must have equal dimensions at most 63".into());
    }
    if align_log > 63 { return Err("alignment logarithm exceeds 63".into()); }
    let domain = 1u64 << h;
    if lo > hi || hi > domain || offset > domain {
        return Err("index interval or offset is outside the domain".into());
    }
    let zero = Fr::from(0u64);
    let mut state = [zero; 8];
    state[0] = Fr::from(1u64);
    for position in 0..=h {
        let mut next = [zero; 8];
        let high = position == h;
        let max_bit = if high || position < align_log { 0 } else { 1 };
        for (index, value) in state.iter().enumerate() {
            for bit in 0..=max_bit {
                let (shifted, b_offset) = subtract_bit(bit, offset, position, index & 1);
                let (_, b_lower) = subtract_bit(bit, lo, position, (index >> 1) & 1);
                let (_, b_upper) = subtract_bit(bit, hi, position, (index >> 2) & 1);
                let destination = b_offset | (b_lower << 1) | (b_upper << 2);
                let weight = if high { Fr::from(1u64) } else {
                    let weight = eq_bit(r[position], bit) * eq_bit(u[position], shifted);
                    match right {
                        RightIndex::SameRow => weight * eq_bit(v[position], bit),
                        RightIndex::GlobalZero => weight,
                    }
                };
                next[destination] += *value * weight;
            }
        }
        state = next;
    }
    // offset and lower subtractions do not underflow; upper does.
    let mut result = state[4];
    if right == RightIndex::GlobalZero {
        for coordinate in v { result *= Fr::from(1u64)-coordinate; }
    }
    Ok(result)
}

/// An unsigned magnitude with an explicit source direction. This avoids both
/// wrapping indices and converting a 63-bit domain into signed arithmetic.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SourceDelta {
    Add(u64),
    Sub(u64),
}

/// Sum eq(r,x) eq(u,x+delta) eq(v,right(x)) over lo <= x < hi,
/// x mod 2^residue_log = residue, and 0 <= x+delta < 2^h.
/// Points use LSB-first bits. `Sub(k)` means delta = -k.
///
/// The eight states track source carry/borrow and the two interval borrows.
/// At most 16*h+8 transitions and two eight-field arrays give O(h) work and
/// constant scratch. The final forced-zero bit has no multilinear weight;
/// requiring its source bit and carry/borrow to be zero prevents wrapping,
/// including when a bound or source magnitude equals 2^h. No owner table or
/// exceptional-point correction is included.
pub fn evaluate_residue_shift(
    r: &[Fr], u: &[Fr], v: &[Fr], delta: SourceDelta, lo: u64, hi: u64,
    residue_log: usize, residue: u64, right: RightIndex,
) -> Result<Fr, String> {
    let h = r.len();
    if h > 63 || u.len() != h || v.len() != h {
        return Err("index points must have equal dimensions at most 63".into());
    }
    if residue_log > 63 { return Err("residue logarithm exceeds 63".into()); }
    if residue >= 1u64 << residue_log {
        return Err("residue is outside its modulus".into());
    }
    let domain = 1u64 << h;
    let magnitude = match delta { SourceDelta::Add(k) | SourceDelta::Sub(k) => k };
    if lo > hi || hi > domain || magnitude > domain {
        return Err("index interval or source magnitude is outside the domain".into());
    }
    let zero = Fr::from(0u64);
    // If the modulus exceeds the domain, a residue outside the domain has no
    // representative. This also enforces residue bits beyond the final bit.
    if residue >= domain { return Ok(zero); }
    let mut state = [zero; 8];
    state[0] = Fr::from(1u64);
    for position in 0..=h {
        let mut next = [zero; 8];
        let high = position == h;
        let (first_bit, last_bit) = if high { (0, 0) }
            else if position < residue_log {
                let bit = ((residue >> position) & 1) as u8;
                (bit, bit)
            } else { (0, 1) };
        for (index, value) in state.iter().enumerate() {
            for bit in first_bit..=last_bit {
                let (shifted, source_state) = match delta {
                    SourceDelta::Add(_) => {
                        let sum = bit + ((magnitude >> position) & 1) as u8
                            + (index & 1) as u8;
                        (sum & 1, (sum >> 1) as usize)
                    },
                    SourceDelta::Sub(_) => subtract_bit(bit, magnitude, position, index & 1),
                };
                if high && (shifted != 0 || source_state != 0) { continue; }
                let (_, b_lower) = subtract_bit(bit, lo, position, (index >> 1) & 1);
                let (_, b_upper) = subtract_bit(bit, hi, position, (index >> 2) & 1);
                let destination = source_state | (b_lower << 1) | (b_upper << 2);
                let weight = if high { Fr::from(1u64) } else {
                    let weight = eq_bit(r[position], bit) * eq_bit(u[position], shifted);
                    match right {
                        RightIndex::SameRow => weight * eq_bit(v[position], bit),
                        RightIndex::GlobalZero => weight,
                    }
                };
                next[destination] += *value * weight;
            }
        }
        state = next;
    }
    let mut result = state[4];
    if right == RightIndex::GlobalZero {
        for coordinate in v { result *= Fr::from(1u64)-coordinate; }
    }
    Ok(result)
}

#[cfg(test)]
mod residue_tests {
    use super::*;

    fn eq_index(point: &[Fr], index: u64) -> Fr {
        point.iter().enumerate().fold(Fr::from(1u64), |weight, (bit, coordinate)| {
            weight * if index & (1u64 << bit) == 0 { Fr::from(1u64)-coordinate }
                else { *coordinate }
        })
    }

    fn point(h: usize, seed: u64) -> Vec<Fr> {
        (0..h).map(|bit| Fr::from(seed + 37*(bit as u64+1))).collect()
    }

    fn bits(h: usize, value: u64) -> Vec<Fr> {
        (0..h).map(|bit| Fr::from((value >> bit)&1)).collect()
    }

    // Independent bounded integer enumeration: no carry/borrow state machine.
    fn direct(r: &[Fr], u: &[Fr], v: &[Fr], delta: SourceDelta, lo: u64, hi: u64,
              q: usize, residue: u64, right: RightIndex) -> Fr {
        assert!(hi-lo <= 4096, "reference enumeration cap");
        let domain = 1u64 << r.len();
        let mut sum = Fr::from(0u64);
        for x in lo..hi {
            if x % (1u64 << q) != residue { continue; }
            let source = match delta {
                SourceDelta::Add(k) => x.checked_add(k),
                SourceDelta::Sub(k) => x.checked_sub(k),
            };
            if let Some(source) = source.filter(|source| *source < domain) {
                let second = if right == RightIndex::SameRow { x } else { 0 };
                sum += eq_index(r,x)*eq_index(u,source)*eq_index(v,second);
            }
        }
        sum
    }

    fn check(h: usize, delta: SourceDelta, lo: u64, hi: u64, q: usize, residue: u64) {
        let r = point(h,3);
        let u = point(h,29);
        let v = point(h,101);
        for right in [RightIndex::SameRow, RightIndex::GlobalZero] {
            assert_eq!(evaluate_residue_shift(&r,&u,&v,delta,lo,hi,q,residue,right).unwrap(),
                direct(&r,&u,&v,delta,lo,hi,q,residue,right),
                "h={h} delta={delta:?} interval={lo}..{hi} q={q} residue={residue} right={right:?}");
        }
    }

    #[test]
    fn residue_non_boolean_small_domain_differential() {
        for h in 0..=10 {
            let n = 1u64 << h;
            for magnitude in [0,1,n/2,n-1,n,128,1089].into_iter().filter(|k| *k <= n) {
                for delta in [SourceDelta::Add(magnitude),SourceDelta::Sub(magnitude)] {
                    for q in [0,h,(h+1).min(63),7,63] {
                        let modulus = 1u64 << q;
                        for residue in [0,modulus-1,63%modulus,126%modulus] {
                            check(h,delta,0,n,q,residue);
                            check(h,delta,n/2,(n/2+3).min(n),q,residue);
                            check(h,delta,n,n,q,residue);
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn residue_interval_and_signed_source_borrow_differential() {
        for h in 1..=11 {
            let n = 1u64 << h;
            for case in 0..48u64 {
                let a = (case*73+11)%(n+1);
                let b = (case*197+31)%(n+1);
                let magnitude = (case*43+7)%(n+1);
                let q = case as usize % (h+2);
                let residue = (case*61+3)%(1u64 << q);
                for delta in [SourceDelta::Add(magnitude),SourceDelta::Sub(magnitude)] {
                    check(h,delta,a.min(b),a.max(b),q,residue);
                }
            }
            for pivot in (0..h).map(|bit| 1u64 << bit) {
                for magnitude in [pivot-1,pivot,pivot+1] {
                    for delta in [SourceDelta::Add(magnitude),SourceDelta::Sub(magnitude)] {
                        check(h,delta,pivot-1,(pivot+2).min(n),0,0);
                    }
                }
            }
        }
    }

    #[test]
    fn residue_boolean_owner_source_pairs_and_right_modes() {
        for h in 0..=4 {
            let n = 1u64 << h;
            for x in 0..n {
                for source in 0..n {
                    for delta in [SourceDelta::Add(0),SourceDelta::Add(1),SourceDelta::Sub(1),
                                  SourceDelta::Add(n),SourceDelta::Sub(n)] {
                        for q in [0,h,7] {
                            let residue = x % (1u64 << q);
                            let actual_source = match delta {
                                SourceDelta::Add(k) => x.checked_add(k),
                                SourceDelta::Sub(k) => x.checked_sub(k),
                            };
                            let expected = Fr::from(u64::from(actual_source == Some(source)));
                            let r = bits(h,x);
                            let u = bits(h,source);
                            for right in [RightIndex::SameRow,RightIndex::GlobalZero] {
                                let v = bits(h,if right == RightIndex::SameRow {x} else {0});
                                assert_eq!(evaluate_residue_shift(&r,&u,&v,delta,0,n,q,residue,right).unwrap(),expected);
                                if h > 0 {
                                    let wrong_v = bits(h,if right == RightIndex::SameRow {x^1} else {1});
                                    assert_eq!(evaluate_residue_shift(&r,&u,&wrong_v,delta,0,n,q,residue,right).unwrap(),Fr::from(0u64));
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn residue_schedule_offsets_and_isolated_confusion_mutants() {
        for residue in [63,126] {
            for delta in [SourceDelta::Add(0),SourceDelta::Add(128),SourceDelta::Sub(128),SourceDelta::Sub(1089)] {
                for center in [63u64,126,127,128,1088,1089,1215,2047,4095] {
                    check(12,delta,center.saturating_sub(2),(center+3).min(4096),7,residue);
                }
            }
        }
        // Change only the residue: the residue-zero mutant drops owner 126.
        let p = bits(12,126);
        let correct = evaluate_residue_shift(&p,&p,&p,SourceDelta::Add(0),0,4096,7,126,RightIndex::SameRow).unwrap();
        let residue_zero = evaluate_residue_shift(&p,&p,&p,SourceDelta::Add(0),0,4096,7,0,RightIndex::SameRow).unwrap();
        assert_eq!(correct,Fr::from(1u64));
        assert_eq!(residue_zero,Fr::from(0u64));
        // Change only source displacement: owner 1215 reads source 126,
        // independently of the separate owner-minus-1090 activation predicate.
        let r = bits(12,1215);
        let u = bits(12,126);
        assert_eq!(evaluate_residue_shift(&r,&u,&r,SourceDelta::Sub(1089),0,4096,7,63,RightIndex::SameRow).unwrap(),Fr::from(1u64));
        assert_eq!(evaluate_residue_shift(&r,&u,&r,SourceDelta::Sub(1090),0,4096,7,63,RightIndex::SameRow).unwrap(),Fr::from(0u64));
        // A modular-wrap mutant would select these owner/source pairs.
        for (x,source,delta) in [(4095,127,SourceDelta::Add(128)),(63,4031,SourceDelta::Sub(128))] {
            assert_eq!(eq_index(&bits(12,source),source),Fr::from(1u64));
            assert_eq!(evaluate_residue_shift(&bits(12,x),&bits(12,source),&bits(12,x),delta,0,4096,7,x%128,RightIndex::SameRow).unwrap(),Fr::from(0u64));
        }
    }

    #[test]
    fn residue_high_bit_no_wrap_and_no_domain_table() {
        for h in [40usize,63] {
            let n = 1u64 << h;
            for delta in [SourceDelta::Add(0),SourceDelta::Add(128),SourceDelta::Sub(128),
                          SourceDelta::Sub(1089),SourceDelta::Add(n),SourceDelta::Sub(n)] {
                for residue in [63,126] {
                    check(h,delta,0,256,7,residue);
                    check(h,delta,n-256,n,7,residue);
                }
            }
            // These wrap only after the h-th bit; lower bits alone are valid.
            let top = bits(h,n-1);
            let zero = bits(h,0);
            assert_eq!(evaluate_residue_shift(&top,&zero,&top,SourceDelta::Add(1),0,n,0,0,RightIndex::SameRow).unwrap(),Fr::from(0u64));
            assert_eq!(evaluate_residue_shift(&zero,&top,&zero,SourceDelta::Sub(1),0,n,0,0,RightIndex::SameRow).unwrap(),Fr::from(0u64));
            // A modulus larger than a small domain still constrains high bits.
            check(3,SourceDelta::Add(0),0,8,63,n-1);
        }
    }

    #[test]
    fn residue_invalid_inputs_reject_and_old_alignment_agrees() {
        let p = point(3,1);
        let evaluate = |r: &[Fr],u: &[Fr],v: &[Fr],d,lo,hi,q,residue| {
            evaluate_residue_shift(r,u,v,d,lo,hi,q,residue,RightIndex::SameRow)
        };
        assert!(evaluate(&p,&p[..2],&p,SourceDelta::Add(0),0,8,0,0).is_err());
        assert!(evaluate(&p,&p,&p[..2],SourceDelta::Add(0),0,8,0,0).is_err());
        let wide = point(64,1);
        assert!(evaluate(&wide,&wide,&wide,SourceDelta::Add(0),0,1,0,0).is_err());
        for delta in [SourceDelta::Add(9),SourceDelta::Sub(9),SourceDelta::Add(u64::MAX),SourceDelta::Sub(u64::MAX)] {
            assert!(evaluate(&p,&p,&p,delta,0,8,0,0).is_err());
        }
        assert!(evaluate(&p,&p,&p,SourceDelta::Add(0),7,6,0,0).is_err());
        assert!(evaluate(&p,&p,&p,SourceDelta::Add(0),0,9,0,0).is_err());
        assert!(evaluate(&p,&p,&p,SourceDelta::Add(0),0,8,64,0).is_err());
        assert!(evaluate(&p,&p,&p,SourceDelta::Add(0),0,8,0,1).is_err());
        assert!(evaluate(&p,&p,&p,SourceDelta::Add(0),0,8,7,128).is_err());
        assert!(evaluate(&p,&p,&p,SourceDelta::Add(0),0,8,63,1u64<<63).is_err());
        for h in 0..=8 {
            let n = 1u64 << h;
            let r = point(h,3);
            let u = point(h,29);
            let v = point(h,101);
            for k in [0,1,n/2,n] {
                for q in [0,h,63] {
                    for right in [RightIndex::SameRow,RightIndex::GlobalZero] {
                        assert_eq!(evaluate_residue_shift(&r,&u,&v,SourceDelta::Sub(k),0,n,q,0,right).unwrap(),
                            evaluate_shift(&r,&u,&v,k,0,n,q,right).unwrap());
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn eq_index(point: &[Fr], index: u64) -> Fr {
        point.iter().enumerate().map(|(bit, coordinate)| {
            if (index >> bit) & 1 == 1 { *coordinate }
            else { Fr::from(1u64)-coordinate }
        }).fold(Fr::from(1u64), |a,b| a*b)
    }

    // Independent integer iteration oracle. Its bound is the requested
    // interval length, not a table allocation or a second borrow automaton.
    fn direct(r: &[Fr], u: &[Fr], v: &[Fr], k: u64, lo: u64, hi: u64,
              e: usize, right: RightIndex) -> Fr {
        assert!(hi-lo <= 4096, "reference enumeration cap");
        let divisor = 1u64 << e;
        let mut sum = Fr::from(0u64);
        for i in lo..hi {
            if i < k || i % divisor != 0 { continue; }
            let right_index = if right == RightIndex::SameRow { i } else { 0 };
            sum += eq_index(r,i)*eq_index(u,i-k)*eq_index(v,right_index);
        }
        sum
    }

    fn point(h: usize, seed: u64) -> Vec<Fr> {
        (0..h).map(|i| Fr::from(seed.wrapping_add((i as u64+1)*37))).collect()
    }

    fn check(h: usize, k: u64, lo: u64, hi: u64, e: usize) {
        let r = point(h,3);
        let u = point(h,29);
        let v = point(h,101);
        for right in [RightIndex::SameRow, RightIndex::GlobalZero] {
            assert_eq!(evaluate_shift(&r,&u,&v,k,lo,hi,e,right).unwrap(),
                       direct(&r,&u,&v,k,lo,hi,e,right),
                       "h={h} k={k} lo={lo} hi={hi} e={e} mode={right:?}");
        }
    }

    #[test]
    fn direct_sum_small_dimensions_and_boundaries() {
        for h in 0..=12 {
            let n = 1u64 << h;
            for k in [0, n/2, n-1, n] {
                for e in [0, h, 63] {
                    check(h,k,0,n,e);
                    check(h,k,n,n,e);
                    check(h,k,n-1,n,e);
                }
            }
            if h > 0 {
                check(h,1,0,n,0);
                check(h,n/2-1,n/2-1,n/2+1,0);
                check(h,n/2,n/2-1,n/2+1,0);
                check(h,n/2+1,n/2-1,n/2+1,0);
                check(h,1,n/2,n-1,1);
            }
        }
    }

    #[test]
    fn deterministic_interval_offset_differential() {
        // Cover independent interval/offset borrows, including cases where
        // the first difference propagates through many higher zero bits.
        for h in 1..=12 {
            let n = 1u64 << h;
            for case in 0..32u64 {
                let a = (case*73+11)%(n+1);
                let b = (case*197+31)%(n+1);
                let k = (case*43+7)%(n+1);
                check(h,k,a.min(b),a.max(b),(case as usize)%(h+2));
            }
            for bit in 0..h {
                let pivot = 1u64 << bit;
                check(h,pivot-1,pivot-1,(pivot+2).min(n),0);
                check(h,pivot,pivot-1,(pivot+2).min(n),0);
                check(h,pivot+1,pivot-1,(pivot+2).min(n),0);
            }
        }
    }

    #[test]
    fn boolean_points_select_exact_rows_and_zero_index() {
        for h in 0..=7 {
            let n = 1u64 << h;
            for row in 0..n {
                let bits = |value: u64| -> Vec<Fr> {
                    (0..h).map(|bit| Fr::from((value >> bit)&1)).collect()
                };
                for k in [0,1,n] {
                    let r = bits(row);
                    let u = bits(row.saturating_sub(k));
                    let v = bits(row);
                    let expected = Fr::from(u64::from(row >= k));
                    assert_eq!(evaluate_shift(&r,&u,&v,k,0,n,0,RightIndex::SameRow).unwrap(), expected);
                    let v_zero = bits(0);
                    assert_eq!(evaluate_shift(&r,&u,&v_zero,k,0,n,0,RightIndex::GlobalZero).unwrap(), expected);
                    if h > 0 {
                        assert_eq!(evaluate_shift(&r,&u,&bits(1),k,0,n,0,RightIndex::GlobalZero).unwrap(), Fr::from(0u64));
                    }
                }
            }
        }
    }

    #[test]
    fn mainnet_offsets_in_bounded_windows_are_kernel_only() {
        // Heights/epochs are frozen native-source constants, but these tests
        // assert ONLY the weighted index kernel, not DAA branch precedence.
        for e in [7usize,10] {
            let epoch = 1u64 << e;
            for j in 0..=8 {
                let offset = j*epoch+1;
                for center in [epoch,8*epoch,417791,417792,417793,844671,844672,844673] {
                    let lo = center.saturating_sub(17);
                    check(20,offset,lo,center+18,e);
                }
                // Exact recalculation rows straddling activation/startup.
                for center in [epoch,8*epoch,417792,844672] {
                    check(20,offset,center,center+1,e);
                }
            }
        }
    }

    #[test]
    fn large_dimensions_need_no_domain_sized_allocation() {
        for h in [40usize,63] {
            let n = 1u64 << h;
            let r = point(h,5);
            let u = point(h,13);
            let v = point(h,71);
            for right in [RightIndex::SameRow,RightIndex::GlobalZero] {
                // Full-domain alignment e=h admits only i=0.
                let expected = eq_index(&r,0)*eq_index(&u,0)*eq_index(&v,0);
                assert_eq!(evaluate_shift(&r,&u,&v,0,0,n,h,right).unwrap(), expected);
                assert_eq!(evaluate_shift(&r,&u,&v,n,0,n,0,right).unwrap(), Fr::from(0u64));
                assert_eq!(evaluate_shift(&r,&u,&v,n-1,n-1,n,0,right).unwrap(),
                    direct(&r,&u,&v,n-1,n-1,n,0,right));
            }
        }
    }

    #[test]
    fn malformed_dimensions_intervals_and_alignment_reject() {
        let p = point(3,1);
        let mode = RightIndex::SameRow;
        assert!(evaluate_shift(&p,&p[..2],&p,0,0,8,0,mode).is_err());
        assert!(evaluate_shift(&p,&p,&p[..2],0,0,8,0,mode).is_err());
        assert!(evaluate_shift(&point(64,1),&point(64,2),&point(64,3),0,0,1,0,mode).is_err());
        assert!(evaluate_shift(&p,&p,&p,9,0,8,0,mode).is_err());
        assert!(evaluate_shift(&p,&p,&p,0,0,9,0,mode).is_err());
        assert!(evaluate_shift(&p,&p,&p,0,7,6,0,mode).is_err());
        assert!(evaluate_shift(&p,&p,&p,0,0,8,64,mode).is_err());
    }
}

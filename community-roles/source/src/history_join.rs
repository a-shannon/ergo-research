//! Bounded 0..=514-byte BLAKE2b-256 join with a fixed-129 compatibility API.
//! This proves a hash preimage relation, not native header/history validity.
use ark_bn254::Fr;
use crate::circuit::{self, CompressionInput, CompressionLayout};
use crate::gkr::Gate;
use crate::sparse::{Circuit, Term};

pub const MESSAGE_LEN: usize = 129;
pub const MAX_MESSAGE_LEN: usize = 514;

pub struct Joined {
    pub base: Circuit,
    pub boundary: Circuit,
    pub input: Option<Vec<Fr>>,
    pub base_input_len: usize,
    pub log_copies: usize,
    pub layout: CompressionLayout,
}

/// Build verifier-owned topology from the independently expected digest.
/// Some adds the two distinct witnesses; a wrong digest remains a nonzero
/// boundary residual instead of being hidden by a native preflight check.
pub fn build(message: Option<&[u8]>, expected_digest: [u8; 32]) -> Result<Joined, String> {
    build_bounded(message, MESSAGE_LEN, expected_digest)
}

/// Length is public and independently supplied by the verifier. Real blocks
/// form one compression chain; padding copies independently hash the empty
/// message. All copies always satisfy the same compression core.
pub fn build_bounded(message: Option<&[u8]>, message_len: usize, expected_digest: [u8; 32])
    -> Result<Joined, String> {
    if message_len > MAX_MESSAGE_LEN {
        return Err("hash join message length exceeds 514".into());
    }
    if message.is_some_and(|bytes| bytes.len() != message_len) {
        return Err("hash join message length mismatch".into());
    }
    // The checked bound precedes addition, allocation and indexing.
    let real_blocks = ((message_len + 127) / 128).max(1);
    let copies = real_blocks.next_power_of_two();
    let log_copies = copies.trailing_zeros() as usize;
    let last_real = real_blocks-1;
    let tail = message_len-128*last_real; // zero only for the empty message
    let initial = circuit::blake2b256_initial_state();
    let first_input = message.map(|bytes| {
        let mut block = [0u8; 128];
        let used = message_len.min(128);
        block[..used].copy_from_slice(&bytes[..used]);
        CompressionInput { state: initial, block, counter: used as u64,
                           final_flag: real_blocks == 1 }
    });
    let mut first = circuit::build_compression(first_input.as_ref())?;
    let width = first.compiled.circuit.input_len;
    let total_width = width.checked_mul(copies).ok_or("input width overflow")?;
    let mut input = first.compiled.input.take();
    if let (Some(bytes), Some(values)) = (message, input.as_mut()) {
        values.reserve(total_width-width);
        let mut previous_output = first.output.ok_or("missing first compression output")?;
        for copy in 1..copies {
            let mut block = [0u8; 128];
            let (state, counter, final_flag) = if copy < real_blocks {
                let start = copy*128;
                let end = (start+128).min(message_len);
                block[..end-start].copy_from_slice(&bytes[start..end]);
                (previous_output, end as u64, copy == last_real)
            } else {
                (initial, 0, true)
            };
            let next = circuit::build_compression(Some(&CompressionInput {
                state, block, counter, final_flag,
            }))?;
            if next.compiled.circuit != first.compiled.circuit || next.layout != first.layout {
                return Err("compression topology differs between copies".into());
            }
            previous_output = next.output.ok_or("missing compression output")?;
            values.extend(next.compiled.input.ok_or("missing compression witness")?);
        }
    }
    let layout = first.layout;
    let zero = Fr::from(0u64);
    let one = Fr::from(1u64);
    let mut terms = Vec::new();
    // Every call contributes its own row; equalities cannot cancel each other.
    let mut anchor = |index: usize, value: bool| {
        terms.push(Term { row: terms.len(), gate: Gate { left: index, right: 0,
            c0: -Fr::from(u64::from(value)), c1: one, c2: zero, c3: zero } });
    };
    for word in 0..8 { for bit in 0..64 {
        anchor(layout.state[word][bit], (initial[word] >> bit) & 1 != 0);
    }}
    // Preserve the original fixed-129 order: initial, counters/flags,
    // final padding, digest, then links. Dummy anchors follow all real rows.
    for copy in 0..real_blocks {
        let counter = ((copy+1)*128).min(message_len) as u64;
        for bit in 0..64 { anchor(copy*width + layout.counter[bit], (counter >> bit) & 1 != 0); }
        anchor(copy*width + layout.final_flag, copy == last_real);
    }
    for byte in tail..128 { for bit in 0..8 {
        anchor(last_real*width + layout.message[byte/8][(byte%8)*8+bit], false);
    }}
    for byte in 0..32 { for bit in 0..8 {
        anchor(last_real*width + layout.output[byte/8][(byte%8)*8+bit],
               (expected_digest[byte] >> bit) & 1 != 0);
    }}
    for copy in 1..real_blocks { for word in 0..8 { for bit in 0..64 {
        terms.push(Term { row: terms.len(), gate: Gate {
            left: copy*width + layout.state[word][bit],
            right: (copy-1)*width + layout.output[word][bit],
            c0: zero, c1: one, c2: -one, c3: zero,
        } });
    }}}
    let mut anchor = |index: usize, value: bool| {
        terms.push(Term { row: terms.len(), gate: Gate { left: index, right: 0,
            c0: -Fr::from(u64::from(value)), c1: one, c2: zero, c3: zero } });
    };
    for copy in real_blocks..copies {
        for word in 0..8 { for bit in 0..64 {
            anchor(copy*width + layout.state[word][bit], (initial[word] >> bit) & 1 != 0);
        }}
        for word in 0..16 { for bit in 0..64 {
            anchor(copy*width + layout.message[word][bit], false);
        }}
        for bit in 0..64 { anchor(copy*width + layout.counter[bit], false); }
        anchor(copy*width + layout.final_flag, true);
    }
    let boundary = Circuit { input_len: total_width,
        row_count: terms.len().next_power_of_two(), terms };
    Ok(Joined { base: first.compiled.circuit, boundary, input,
                base_input_len: width, log_copies, layout })
}

#[cfg(test)]
mod tests {
    use super::*;
    use blake2::{Blake2bVar, digest::{Update, VariableOutput}};

    fn digest(message: &[u8]) -> [u8; 32] {
        let mut hash = Blake2bVar::new(32).unwrap();
        hash.update(message);
        let mut out = [0; 32];
        hash.finalize_variable(&mut out).unwrap();
        out
    }
    fn residuals(circuit: &Circuit, input: &[Fr]) -> Vec<Fr> {
        let mut rows = vec![Fr::from(0u64); circuit.row_count];
        for term in &circuit.terms { rows[term.row] += term.gate.evaluate(input); }
        rows
    }
    fn is_zero(circuit: &Circuit, input: &[Fr]) -> bool {
        residuals(circuit, input).into_iter().all(|x| x == Fr::from(0u64))
    }

    #[test]
    fn two_distinct_blocks_match_blake2b_and_public_topology() {
        for kind in 0..3 {
            let message: Vec<u8> = (0..MESSAGE_LEN).map(|i| match kind {
                0 => 0, 1 => 255, _ => (i as u8).wrapping_mul(37).wrapping_add(11),
            }).collect();
            let expected = digest(&message);
            let joined = build(Some(&message), expected).unwrap();
            let public = build(None, expected).unwrap();
            assert_eq!(joined.base, public.base);
            assert_eq!(joined.boundary, public.boundary);
            assert_eq!(joined.layout, public.layout);
            let input = joined.input.unwrap();
            assert_eq!(input.len(), 2*joined.base_input_len);
            let copies: Vec<_> = input.chunks_exact(joined.base_input_len).collect();
            assert_ne!(copies[0], copies[1]);
            assert!(copies.iter().all(|copy| is_zero(&joined.base, copy)));
            assert!(is_zero(&joined.boundary, &input));
            assert_eq!(joined.boundary.terms.len(), 2426);
            eprintln!("generic compression used={} padded={} rows={} terms={} boundary_rows={}",
                joined.layout.used_input_len, joined.base_input_len, joined.base.row_count,
                joined.base.terms.len(), joined.boundary.row_count);
        }
    }

    #[test]
    fn boundary_fields_fail_individually_without_claiming_core_validity() {
        let message: Vec<u8> = (0..MESSAGE_LEN).map(|i| i as u8).collect();
        let joined = build(Some(&message), digest(&message)).unwrap();
        let input = joined.input.unwrap();
        let w = joined.base_input_len;
        let l = joined.layout;
        // A single witness bit is flipped only to test the boundary evaluator.
        // The altered witness is not asserted to satisfy the compression core.
        for index in [l.state[0][0], l.counter[0], w+l.counter[63],
            l.final_flag, w+l.final_flag, w+l.message[0][8],
            w+l.output[0][0], w+l.state[0][0], w+l.state[7][63]] {
            let mut altered = input.clone();
            altered[index] = Fr::from(1u64)-altered[index];
            let nonzero = residuals(&joined.boundary, &altered).into_iter()
                .filter(|x| *x != Fr::from(0u64)).count();
            assert_eq!(nonzero, 1, "index {index}");
        }
        let mut wrong_digest = digest(&message);
        wrong_digest[0] ^= 1;
        let wrong = build(None, wrong_digest).unwrap();
        assert!(!is_zero(&wrong.boundary, &input));
        let mut endian = digest(&message);
        for word in endian.chunks_exact_mut(8) { word.reverse(); }
        assert!(!is_zero(&build(None, endian).unwrap().boundary, &input));
    }

    #[test]
    fn unlinked_valid_compressions_fail_full_state_link() {
        let message = [19u8; MESSAGE_LEN];
        let joined = build(Some(&message), digest(&message)).unwrap();
        let w = joined.base_input_len;
        let input = joined.input.unwrap();
        for word in [0usize, 7] {
            let mut state = [0u64; 8];
            for i in 0..8 { for bit in 0..64 {
                if input[w+joined.layout.state[i][bit]] == Fr::from(1u64) { state[i] |= 1u64 << bit; }
            }}
            state[word] ^= 1;
            let mut block = [0u8; 128]; block[0] = message[128];
            let other = circuit::build_compression(Some(&CompressionInput {
                state, block, counter: 129, final_flag: true,
            })).unwrap();
            let mut alternate_digest = [0u8; 32];
            for (i, value) in other.output.unwrap()[..4].iter().enumerate() {
                alternate_digest[i*8..i*8+8].copy_from_slice(&value.to_le_bytes());
            }
            let boundary = build(None, alternate_digest).unwrap().boundary;
            let mut alternate = input[..w].to_vec();
            alternate.extend(other.compiled.input.unwrap());
            assert!(is_zero(&joined.base, &alternate[..w]));
            assert!(is_zero(&joined.base, &alternate[w..]));
            assert_eq!(residuals(&boundary, &alternate).into_iter()
                .filter(|x| *x != Fr::from(0u64)).count(), 1);
            // Omission mutant: removing all state-link rows wrongly accepts.
            let mut mutant = boundary.clone();
            mutant.terms.truncate(mutant.terms.len()-512);
            assert!(is_zero(&mutant, &alternate));
        }
    }

    #[test]
    fn length_and_input_padding_are_checked() {
        assert!(build(Some(&[0; 128]), [0; 32]).is_err());
        assert!(build(Some(&[0; 130]), [0; 32]).is_err());
        let message = [0u8; MESSAGE_LEN];
        let joined = build(Some(&message), digest(&message)).unwrap();
        let mut input = joined.input.unwrap();
        assert!(joined.layout.used_input_len < joined.base_input_len);
        input[joined.layout.used_input_len] = Fr::from(1u64);
        assert!(!is_zero(&joined.base, &input[..joined.base_input_len]));
    }

    #[test]
    fn bounded_lengths_match_native_hash_and_public_schedule() {
        for length in [0usize,1,127,128,129,255,256,257,384,385,512,513,514] {
            let message: Vec<u8> = (0..length)
                .map(|i| (i as u8).wrapping_mul(37).wrapping_add(11)).collect();
            let expected = digest(&message);
            let joined = build_bounded(Some(&message), length, expected).unwrap();
            let public = build_bounded(None, length, expected).unwrap();
            assert_eq!(joined.base, public.base);
            assert_eq!(joined.boundary, public.boundary);
            assert_eq!(joined.layout, public.layout);
            let real = ((length+127)/128).max(1);
            let copies = real.next_power_of_two();
            assert_eq!(1usize << joined.log_copies, copies);
            let tail = length-128*(real-1);
            let expected_rows = 256+577*real+8*(128-tail)+1601*(copies-real);
            assert_eq!(joined.boundary.terms.len(), expected_rows);
            assert_eq!(joined.boundary.row_count, expected_rows.next_power_of_two());
            let input = joined.input.unwrap();
            assert_eq!(input.len(), copies*joined.base_input_len);
            assert!(input.chunks_exact(joined.base_input_len)
                .all(|copy| is_zero(&joined.base, copy)), "core at length {length}");
            assert!(is_zero(&joined.boundary, &input), "boundary at length {length}");
            // Native digest equality above also catches an extra final block
            // at exact multiples. Check the schedule flags explicitly.
            for copy in 0..copies {
                assert_eq!(input[copy*joined.base_input_len+joined.layout.final_flag],
                    Fr::from(u64::from(copy >= real-1)));
            }
            if length == MESSAGE_LEN {
                let legacy = build(Some(&message), expected).unwrap();
                assert_eq!(legacy.base, joined.base);
                assert_eq!(legacy.boundary, joined.boundary);
                assert_eq!(legacy.input.unwrap(), input);
            }
            eprintln!("bounded len={length} real={real} copies={copies} constraints={expected_rows}");
        }
        assert!(build_bounded(None, 515, [0;32]).is_err());
        assert!(build_bounded(None, usize::MAX, [0;32]).is_err());
        assert!(build_bounded(Some(&[0;128]), 129, [0;32]).is_err());
        assert!(build_bounded(Some(&[0;1]), 0, [0;32]).is_err());
    }

    #[test]
    fn bounded_real_and_dummy_anchors_fail_individually() {
        let message: Vec<u8> = (0..513).map(|i| (i as u8).wrapping_add(13)).collect();
        let joined = build_bounded(Some(&message), message.len(), digest(&message)).unwrap();
        let input = joined.input.unwrap();
        let w = joined.base_input_len;
        let l = joined.layout;
        let mut indices = Vec::new();
        // Each real counter/flag; every real link, in both state halves.
        for copy in 0..5 {
            indices.extend([copy*w+l.counter[0], copy*w+l.counter[63], copy*w+l.final_flag]);
            if copy != 0 { indices.extend([copy*w+l.state[0][0], copy*w+l.state[7][63]]); }
        }
        indices.push(4*w+l.message[0][8]); // first byte of final-block padding
        // All dummy copies, including first/last state/message bits and counter.
        for copy in 5..8 {
            indices.extend([copy*w+l.state[0][0], copy*w+l.state[7][63],
                copy*w+l.message[0][0], copy*w+l.message[15][63],
                copy*w+l.counter[0], copy*w+l.counter[63], copy*w+l.final_flag]);
        }
        for index in indices {
            let mut altered = input.clone();
            altered[index] = Fr::from(1u64)-altered[index];
            // Boundary-only single-fault test; no core-validity assertion.
            assert_eq!(residuals(&joined.boundary, &altered).into_iter()
                .filter(|x| *x != Fr::from(0u64)).count(), 1, "slot {index}");
        }
        // The two lengths have identical block/copy counts and zero-padded
        // witness block bytes here; the public counter still distinguishes them.
        let wrong_length = build_bounded(None, 514, digest(&message)).unwrap();
        assert!(!is_zero(&wrong_length.boundary, &input));
    }

    #[test]
    fn alternative_valid_dummy_requires_its_anchor() {
        let message = vec![31u8;257];
        let joined = build_bounded(Some(&message), message.len(), digest(&message)).unwrap();
        let w = joined.base_input_len;
        let mut input = joined.input.unwrap();
        let mut block = [0u8;128]; block[0] = 1;
        let other = circuit::build_compression(Some(&CompressionInput {
            state: circuit::blake2b256_initial_state(), block, counter: 0, final_flag: true,
        })).unwrap();
        let alternate = other.compiled.input.unwrap();
        assert!(is_zero(&joined.base, &alternate));
        input[3*w..4*w].copy_from_slice(&alternate);
        assert_eq!(residuals(&joined.boundary, &input).into_iter()
            .filter(|x| *x != Fr::from(0u64)).count(), 1);
        let bad_slot = 3*w+joined.layout.message[0][0];
        let mut mutant = joined.boundary.clone();
        let before = mutant.terms.len();
        mutant.terms.retain(|term| term.gate.left != bad_slot);
        assert_eq!(mutant.terms.len(), before-1);
        assert!(is_zero(&mutant, &input));
    }

    #[test]
    fn public_digest_is_anchored_at_last_real_not_last_padded_copy() {
        let message = vec![73u8;257];
        let joined = build_bounded(Some(&message), message.len(), digest(&message)).unwrap();
        let input = joined.input.unwrap();
        let empty_digest = digest(&[]);
        assert_ne!(empty_digest, digest(&message));
        let wrong = build_bounded(None, message.len(), empty_digest).unwrap();
        assert!(!is_zero(&wrong.boundary, &input));
        // Actual defect mutant: move every public digest anchor from real
        // copy 2 to dummy copy 3. It would accept the empty digest instead.
        let mut mutant = wrong.boundary;
        let mut moved = 0;
        for term in &mut mutant.terms {
            if term.gate.c1 != Fr::from(1u64) || term.gate.c2 != Fr::from(0u64) { continue; }
            for word in &joined.layout.output[..4] { for index in word {
                if term.gate.left == 2*joined.base_input_len+index {
                    term.gate.left += joined.base_input_len;
                    moved += 1;
                }
            }}
        }
        assert_eq!(moved, 256);
        assert!(is_zero(&mutant, &input));
    }
}

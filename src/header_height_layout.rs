//! Serialized height equals the valid logical slot plus one.
//! This relation does not prove header hashes, ancestry or genesis identity.
use crate::{gkr::Gate, header_hash, serializer, sparse::Term, work_tree_layout};
use ark_bn254::Fr;
use ark_ff::{One, Zero};

const INPUT_BITS: usize = 20;
const ROW_BITS: usize = 5;
const WIDTH: usize = 1 << INPUT_BITS;

pub(crate) struct HeaderHeightLayout {
    n: u64,
    slot_log: usize,
    wires: [usize; 32],
    fingerprint: String,
}

fn eq(point: &[Fr], index: usize) -> Fr {
    point.iter().enumerate().fold(Fr::one(), |a, (bit, x)| {
        a * if (index >> bit) & 1 == 1 {
            *x
        } else {
            Fr::one() - x
        }
    })
}

// MSB-first strict-prefix sum, with optional Boolean slot-coordinate masks.
// The extra zero top bit distinguishes n==2^h from n==0 without wraparound.
fn prefix(weights: &[[Fr; 2]], n: u64, ones: u64, zeros: u64) -> Fr {
    if ones & zeros != 0 {
        return Fr::zero();
    }
    let h = weights.len();
    let mut state = [Fr::one(), Fr::zero()]; // equal, less
    for position in (0..=h).rev() {
        let top = position == h;
        let upper = ((n >> position) & 1) as usize;
        let mut next = [Fr::zero(); 2];
        for less in 0..2 {
            for bit in 0..=usize::from(!top) {
                if !top
                    && ((ones >> position) & 1 == 1 && bit == 0
                        || (zeros >> position) & 1 == 1 && bit == 1)
                {
                    continue;
                }
                if less == 0 && bit > upper {
                    continue;
                }
                let destination = usize::from(less == 1 || bit < upper);
                let weight = if top {
                    Fr::one()
                } else {
                    weights[position][bit]
                };
                next[destination] += state[less] * weight;
            }
        }
        state = next;
    }
    state[1]
}

impl HeaderHeightLayout {
    pub(crate) fn compile(n: u64, slot_log: usize) -> Result<Self, String> {
        if n == 0 || slot_log > 21 || n > i32::MAX as u64 || n > (1u64 << slot_log) {
            return Err("height history dimensions exceed the fixed profile".into());
        }
        let fields = serializer::build(None)?.layout.fields.height;
        let mut wires = [0; 32];
        for (bit, source) in fields.into_iter().enumerate() {
            wires[bit] = header_hash::SERIALIZER_OFFSET
                .checked_add(source)
                .filter(|wire| *wire < WIDTH)
                .ok_or("height wire outside local input")?;
            if wires[..bit].contains(&wires[bit]) {
                return Err("duplicate height wire".into());
            }
        }
        let mut descriptor = b"serialized-height-slot-plus-one-v1".to_vec();
        for value in [n, slot_log as u64, INPUT_BITS as u64, ROW_BITS as u64]
            .into_iter()
            .chain(wires.iter().map(|wire| *wire as u64))
        {
            descriptor.extend_from_slice(&value.to_le_bytes());
        }
        Ok(Self {
            n,
            slot_log,
            wires,
            fingerprint: work_tree_layout::hash_bytes(&descriptor),
        })
    }
    pub(crate) fn fingerprint(&self) -> &str {
        &self.fingerprint
    }
    pub(crate) fn height_wire(&self, bit: usize) -> Option<usize> {
        self.wires.get(bit).copied()
    }

    pub(crate) fn visit_slot_terms(
        &self,
        slot: u64,
        mut sink: impl FnMut(Term) -> Result<(), String>,
    ) -> Result<usize, String> {
        if slot >= self.n {
            return Err("height slot outside valid history".into());
        }
        let s = usize::try_from(slot).map_err(|_| "height slot usize overflow")?;
        let row = s.checked_mul(32).ok_or("height row overflow")?;
        let input = s.checked_mul(WIDTH).ok_or("height input overflow")?;
        let height = slot.checked_add(1).ok_or("height increment overflow")?;
        // All translations are validated before the first externally visible term.
        row.checked_add(31).ok_or("height final row overflow")?;
        input
            .checked_add(WIDTH - 1)
            .ok_or("height final input overflow")?;
        for bit in 0..32 {
            sink(Term {
                row: row + bit,
                gate: Gate {
                    left: input + self.wires[bit],
                    right: input,
                    c0: -Fr::from((height >> bit) & 1),
                    c1: Fr::one(),
                    c2: Fr::zero(),
                    c3: Fr::zero(),
                },
            })?;
        }
        Ok(32)
    }

    pub(crate) fn coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
        let h = self.slot_log;
        if r.len() != ROW_BITS + h || u.len() != INPUT_BITS + h || v.len() != INPUT_BITS + h {
            return Err("height coefficient point dimensions rejected".into());
        }
        let weights: Vec<_> = (0..h)
            .map(|j| {
                let (a, b, c) = (r[ROW_BITS + j], u[INPUT_BITS + j], v[INPUT_BITS + j]);
                [
                    (Fr::one() - a) * (Fr::one() - b) * (Fr::one() - c),
                    a * b * c,
                ]
            })
            .collect();
        let total = prefix(&weights, self.n, 0, 0);
        let right_zero = eq(&v[..INPUT_BITS], 0);
        let mut result = [Fr::zero(); 4];
        for bit in 0..32 {
            let weight =
                eq(&r[..ROW_BITS], bit) * eq(&u[..INPUT_BITS], self.wires[bit]) * right_zero;
            let lower = (1u64 << bit) - 1;
            let height_bit = if bit < h {
                let current = 1u64 << bit;
                prefix(&weights, self.n, current, 0) - prefix(&weights, self.n, current | lower, 0)
                    + prefix(&weights, self.n, lower, current)
            } else if bit == h {
                prefix(&weights, self.n, lower, 0)
            } else {
                Fr::zero()
            };
            result[0] -= weight * height_bit;
            result[1] += weight * total;
        }
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn bits(value: usize, width: usize) -> Vec<Fr> {
        (0..width)
            .map(|bit| Fr::from(((value >> bit) & 1) as u64))
            .collect()
    }
    fn point(width: usize, seed: usize) -> Vec<Fr> {
        (0..width)
            .map(|i| Fr::from((seed + 11 * i) as u64))
            .collect()
    }
    #[test]
    fn global_height_factory_matches_emitted_terms_and_isolated_boundaries() {
        for h in 0..=5 {
            let domain = 1u64 << h;
            let mut lengths = vec![1, domain];
            if domain > 1 {
                lengths.push(domain - 1);
            }
            lengths.sort();
            lengths.dedup();
            for n in lengths {
                let factory = HeaderHeightLayout::compile(n, h).unwrap();
                let (r, u, v) = (point(5 + h, 3), point(20 + h, 29), point(20 + h, 101));
                let mut expected = [Fr::zero(); 4];
                for slot in 0..n {
                    let count = factory
                        .visit_slot_terms(slot, |term| {
                            let weight =
                                eq(&r, term.row) * eq(&u, term.gate.left) * eq(&v, term.gate.right);
                            for (out, c) in expected.iter_mut().zip([
                                term.gate.c0,
                                term.gate.c1,
                                term.gate.c2,
                                term.gate.c3,
                            ]) {
                                *out += weight * c;
                            }
                            Ok(())
                        })
                        .unwrap();
                    assert_eq!(count, 32);
                }
                assert_eq!(
                    factory.coefficients(&r, &u, &v).unwrap(),
                    expected,
                    "N{n} h{h}"
                );
                for slot in 0..domain {
                    for bit in 0..32 {
                        let row = bits((slot as usize) * 32 + bit, 5 + h);
                        let left = bits((slot as usize) * WIDTH + factory.wires[bit], 20 + h);
                        let right = bits((slot as usize) * WIDTH, 20 + h);
                        let want = if slot < n {
                            [
                                -Fr::from(((slot + 1) >> bit) & 1),
                                Fr::one(),
                                Fr::zero(),
                                Fr::zero(),
                            ]
                        } else {
                            [Fr::zero(); 4]
                        };
                        assert_eq!(factory.coefficients(&row, &left, &right).unwrap(), want);
                        if h > 0 {
                            let mut wrong = left.clone();
                            wrong[20] = Fr::one() - wrong[20];
                            assert_eq!(
                                factory.coefficients(&row, &wrong, &right).unwrap(),
                                [Fr::zero(); 4]
                            );
                        }
                    }
                }
                let mut called = false;
                assert!(factory
                    .visit_slot_terms(n, |_| {
                        called = true;
                        Ok(())
                    })
                    .is_err());
                assert!(!called);
                assert_eq!(
                    factory
                        .visit_slot_terms(0, |_| Err("sink-stop".into()))
                        .unwrap_err(),
                    "sink-stop"
                );
                assert!(factory.coefficients(&r[..r.len() - 1], &u, &v).is_err());
                assert!(factory.coefficients(&r, &u[..u.len() - 1], &v).is_err());
                assert!(factory.coefficients(&r, &u, &v[..v.len() - 1]).is_err());
            }
        }
        for (n, h) in [(0, 0), (2, 0), (1, 22), (i32::MAX as u64 + 1, 21)] {
            assert!(HeaderHeightLayout::compile(n, h).is_err());
        }
        // Check every actual emitted native bit gate, with isolated bit flips.
        let factory = HeaderHeightLayout::compile(2, 1).unwrap();
        let mut input = vec![Fr::zero(); WIDTH];
        for slot in 0..2 {
            let mut terms = Vec::new();
            factory
                .visit_slot_terms(slot, |mut term| {
                    term.row -= slot as usize * 32;
                    term.gate.left -= slot as usize * WIDTH;
                    term.gate.right -= slot as usize * WIDTH;
                    terms.push(term);
                    Ok(())
                })
                .unwrap();
            for bit in 0..32 {
                input[factory.wires[bit]] = Fr::from(((slot + 1) >> bit) & 1);
            }
            assert!(terms
                .iter()
                .all(|term| term.gate.evaluate(&input).is_zero()));
            for bit in 0..32 {
                let wire = factory.wires[bit];
                input[wire] = Fr::one() - input[wire];
                let bad: Vec<_> = terms
                    .iter()
                    .filter(|term| !term.gate.evaluate(&input).is_zero())
                    .map(|term| term.row)
                    .collect();
                assert_eq!(bad, vec![bit]);
                input[wire] = Fr::one() - input[wire];
            }
        }
        for n in [(1u64 << 21) - 1, 1u64 << 21] {
            let factory = HeaderHeightLayout::compile(n, 21).unwrap();
            for slot in [0, n - 1, (1 << 21) - 1] {
                for bit in 0..32 {
                    let row = bits(slot as usize * 32 + bit, 26);
                    let left = bits(slot as usize * WIDTH + factory.wires[bit], 41);
                    let right = bits(slot as usize * WIDTH, 41);
                    let want = if slot < n {
                        [
                            -Fr::from(((slot + 1) >> bit) & 1),
                            Fr::one(),
                            Fr::zero(),
                            Fr::zero(),
                        ]
                    } else {
                        [Fr::zero(); 4]
                    };
                    assert_eq!(factory.coefficients(&row, &left, &right).unwrap(), want);
                }
            }
        }
        println!("height32 global emitted differential, bit flips, genesis, padding, dimensions, upperlog21 all passed");
    }
}

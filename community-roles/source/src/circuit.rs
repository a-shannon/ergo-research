//! Single-block BLAKE2b-256 as a local-operation GKR circuit.
//!
//! Input bits include every addition/XOR result as a private witness. Each
//! local operation, every bit's Booleanity, and the public digest are checked
//! by the final zero-residual layer. Prover and verifier build identical gates.

use ark_bn254::Fr;
use std::collections::BTreeMap;

use crate::gkr::{Gate, Layer};
use crate::sparse::{Circuit as SparseCircuit, Term};

const IV: [u64; 8] = [
    0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b,
    0xa54ff53a5f1d36f1, 0x510e527fade682d1, 0x9b05688c2b3e6c1f,
    0x1f83d9abfb41bd6b, 0x5be0cd19137e2179,
];
const SIGMA: [[usize; 16]; 12] = [
    [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],
    [14,10,4,8,9,15,13,6,1,12,0,2,11,7,5,3],
    [11,8,12,0,5,2,15,13,10,14,3,6,7,1,9,4],
    [7,9,3,1,13,12,11,14,2,6,5,10,4,0,15,8],
    [9,0,5,7,2,4,10,15,14,1,11,12,6,8,3,13],
    [2,12,6,10,0,11,8,3,4,13,7,5,15,14,1,9],
    [12,5,1,15,14,13,4,10,0,7,6,3,9,2,8,11],
    [13,11,7,14,12,1,3,9,5,0,15,4,8,6,2,10],
    [6,15,14,9,11,3,0,8,12,2,13,7,1,4,10,5],
    [10,2,8,4,7,6,1,5,15,11,9,14,3,12,13,0],
    [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],
    [14,10,4,8,9,15,13,6,1,12,0,2,11,7,5,3],
];

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Mode { LocalOps }

#[derive(Clone, Debug, Default)]
pub struct Stats {
    pub witness_bits: usize,
    pub add_words: usize,
    pub xor_words: usize,
    pub residuals: usize,
    pub logical_gates: usize,
    pub padded_gates: usize,
    pub max_dependency_depth: usize,
    pub max_layer_width: usize,
    pub nonzero_residuals: Option<usize>,
}

pub struct Compiled {
    pub input: Option<Vec<Fr>>,
    pub input_len: usize,
    pub layers: Vec<Layer>,
    pub stats: Stats,
}

pub struct SparseCompiled {
    pub input: Option<Vec<Fr>>,
    pub circuit: SparseCircuit,
    pub stats: Stats,
}

/// Fixed sequential BLAKE2b profile: 64-bit byte counter, high counter zero,
/// no last-node flag. Every exposed index addresses a Boolean witness bit.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompressionLayout {
    pub state: [[usize; 64]; 8],
    pub message: [[usize; 64]; 16],
    pub counter: [usize; 64],
    pub final_flag: usize,
    pub output: [[usize; 64]; 8],
    pub used_input_len: usize,
}

pub struct CompressionInput {
    pub state: [u64; 8],
    pub block: [u8; 128],
    pub counter: u64,
    pub final_flag: bool,
}

pub struct CompressionCompiled {
    pub compiled: SparseCompiled,
    pub layout: CompressionLayout,
    pub output: Option<[u64; 8]>,
}

/// Values for the fixed canonical compression relation, without another
/// circuit allocation. Consumers retain their own canonical compiled core.
pub(crate) struct CompressionAssignment {
    pub(crate) input: Vec<Fr>,
    pub(crate) layout: CompressionLayout,
    pub(crate) output: [u64; 8],
}

pub fn blake2b256_initial_state() -> [u64; 8] {
    let mut state = IV;
    state[0] ^= 0x01010020;
    state
}

#[derive(Clone, Copy)]
enum Bit { Const(bool), Var(usize) }
type Word = [Bit; 64];

#[derive(Clone, Copy)]
enum Ref { Input(usize), Node(usize) }

#[derive(Clone)]
struct Node {
    left: Ref,
    right: Ref,
    c0: Fr,
    c1: Fr,
    c2: Fr,
    c3: Fr,
    depth: usize,
    value: Option<Fr>,
}

struct Builder {
    input: Option<Vec<Fr>>,
    input_len: usize,
    nodes: Vec<Node>,
    residuals: Vec<Ref>,
    stats: Stats,
    assignment_only: bool,
}

impl Builder {
    fn new(evaluate: bool) -> Self {
        Self::with_mode(evaluate, false)
    }

    fn with_mode(evaluate: bool, assignment_only: bool) -> Self {
        assert!(!assignment_only || evaluate, "assignment requires concrete values");
        let mut builder = Self {
            input: evaluate.then(|| vec![Fr::from(0u64)]), input_len: 1,
            nodes: Vec::new(), residuals: Vec::new(), stats: Stats::default(), assignment_only,
        };
        // Input 0 is a constrained zero, used as a dummy child for unary gates.
        if !assignment_only {
            let zero = builder.gate(Ref::Input(0), Ref::Input(0),
                                    Fr::from(0u64), Fr::from(1u64),
                                    Fr::from(0u64), Fr::from(0u64));
            builder.residuals.push(zero);
        }
        builder
    }

    fn val(&self, r: Ref) -> Option<Fr> {
        match r {
            Ref::Input(i) => self.input.as_ref().map(|v| v[i]),
            Ref::Node(i) => self.nodes[i].value,
        }
    }
    fn depth(&self, r: Ref) -> usize {
        match r { Ref::Input(_) => 0, Ref::Node(i) => self.nodes[i].depth }
    }
    fn gate(&mut self, left: Ref, right: Ref, c0: Fr, c1: Fr, c2: Fr, c3: Fr) -> Ref {
        assert!(!self.assignment_only, "assignment cannot emit a gate");
        let depth = self.depth(left).max(self.depth(right)) + 1;
        let value = self.val(left).zip(self.val(right))
            .map(|(l, r)| c0 + c1*l + c2*r + c3*l*r);
        let id = self.nodes.len();
        self.nodes.push(Node { left, right, c0, c1, c2, c3, depth, value });
        Ref::Node(id)
    }
    fn bit_value(&self, b: Bit) -> Option<bool> {
        match b {
            Bit::Const(v) => Some(v),
            Bit::Var(i) => self.input.as_ref().map(|v| v[i] == Fr::from(1u64)),
        }
    }
    fn witness(&mut self, value: Option<bool>) -> Bit {
        let index = self.input_len;
        self.input_len += 1;
        if let Some(input) = &mut self.input {
            input.push(Fr::from(u64::from(value.expect("value in prover mode"))));
        }
        self.stats.witness_bits += 1;
        if self.assignment_only { return Bit::Var(index); }
        let r = Ref::Input(index);
        let check = self.gate(r, r, Fr::from(0u64), -Fr::from(1u64),
                              Fr::from(0u64), Fr::from(1u64));
        self.residuals.push(check);
        Bit::Var(index)
    }
    fn word_value(&self, word: &Word) -> Option<u64> {
        let mut out = 0u64;
        for (i, bit) in word.iter().enumerate() {
            if self.bit_value(*bit)? { out |= 1u64 << i; }
        }
        Some(out)
    }
    fn const_word(value: u64) -> Word {
        std::array::from_fn(|i| Bit::Const((value >> i) & 1 != 0))
    }
    fn add_term(terms: &mut Vec<(Ref, Fr)>, constant: &mut Fr, bit: Bit, coeff: Fr) {
        match bit {
            Bit::Const(true) => *constant += coeff,
            Bit::Const(false) => {},
            Bit::Var(i) => terms.push((Ref::Input(i), coeff)),
        }
    }
    fn linear_residual(&mut self, terms: Vec<(Ref, Fr)>, constant: Fr) {
        let zero = Ref::Input(0);
        let mut level: Vec<Ref> = if terms.is_empty() {
            vec![self.gate(zero, zero, constant, Fr::from(0u64),
                           Fr::from(0u64), Fr::from(0u64))]
        } else {
            terms.chunks(2).enumerate().map(|(i, pair)| {
                let (left, c1) = pair[0];
                let (right, c2) = if pair.len() == 2 { pair[1] }
                                  else { (zero, Fr::from(0u64)) };
                self.gate(left, right, if i == 0 { constant } else { Fr::from(0u64) },
                          c1, c2, Fr::from(0u64))
            }).collect()
        };
        while level.len() > 1 {
            level = level.chunks(2).map(|pair| {
                let right = if pair.len() == 2 { pair[1] } else { zero };
                self.gate(pair[0], right, Fr::from(0u64), Fr::from(1u64),
                          if pair.len() == 2 { Fr::from(1u64) } else { Fr::from(0u64) },
                          Fr::from(0u64))
            }).collect();
        }
        self.residuals.push(level[0]);
    }
    fn add_words(&mut self, a: &Word, b: &Word) -> Word {
        self.stats.add_words += 1;
        let native = self.word_value(a).zip(self.word_value(b))
            .map(|(x,y)| (x as u128) + (y as u128));
        let sum: Word = std::array::from_fn(|i| self.witness(native.map(|n| (n >> i) & 1 != 0)));
        let carry = self.witness(native.map(|n| (n >> 64) & 1 != 0));
        if self.assignment_only { return sum; }
        let mut terms = Vec::with_capacity(193);
        let mut constant = Fr::from(0u64);
        let mut weight = Fr::from(1u64);
        for i in 0..64 {
            Self::add_term(&mut terms, &mut constant, a[i], weight);
            Self::add_term(&mut terms, &mut constant, b[i], weight);
            Self::add_term(&mut terms, &mut constant, sum[i], -weight);
            weight += weight;
        }
        Self::add_term(&mut terms, &mut constant, carry, -weight);
        self.linear_residual(terms, constant);
        sum
    }
    fn xor_bit(&mut self, a: Bit, b: Bit) -> Bit {
        let value = self.bit_value(a).zip(self.bit_value(b)).map(|(x,y)| x ^ y);
        let z = self.witness(value);
        if self.assignment_only { return z; }
        let (a0, a1, left) = match a {
            Bit::Const(v) => (Fr::from(u64::from(v)), Fr::from(0u64), Ref::Input(0)),
            Bit::Var(i) => (Fr::from(0u64), Fr::from(1u64), Ref::Input(i)),
        };
        let (b0, b1, right) = match b {
            Bit::Const(v) => (Fr::from(u64::from(v)), Fr::from(0u64), Ref::Input(0)),
            Bit::Var(i) => (Fr::from(0u64), Fr::from(1u64), Ref::Input(i)),
        };
        let two = Fr::from(2u64);
        let xor = self.gate(left, right, a0+b0-two*a0*b0,
                            a1*(Fr::from(1u64)-two*b0),
                            b1*(Fr::from(1u64)-two*a0), -two*a1*b1);
        let residual = self.gate(xor, Ref::Input(match z { Bit::Var(i) => i, _ => unreachable!() }),
                                 Fr::from(0u64), Fr::from(1u64),
                                 -Fr::from(1u64), Fr::from(0u64));
        self.residuals.push(residual);
        z
    }
    fn xor_words(&mut self, a: &Word, b: &Word) -> Word {
        self.stats.xor_words += 1;
        std::array::from_fn(|i| self.xor_bit(a[i], b[i]))
    }
    fn rotate(word: &Word, distance: usize) -> Word {
        std::array::from_fn(|i| word[(i + distance) % 64])
    }
    fn g(&mut self, v: &mut [Word;16], a: usize,b: usize,c: usize,d: usize,
         x: &Word,y: &Word) {
        let first = self.add_words(&v[a], &v[b]);
        v[a] = self.add_words(&first, x);
        v[d] = Self::rotate(&self.xor_words(&v[d], &v[a]), 32);
        v[c] = self.add_words(&v[c], &v[d]);
        v[b] = Self::rotate(&self.xor_words(&v[b], &v[c]), 24);
        let second = self.add_words(&v[a], &v[b]);
        v[a] = self.add_words(&second, y);
        v[d] = Self::rotate(&self.xor_words(&v[d], &v[a]), 16);
        v[c] = self.add_words(&v[c], &v[d]);
        v[b] = Self::rotate(&self.xor_words(&v[b], &v[c]), 63);
    }
    fn hash(&mut self, message_len: usize, message: Option<&[u8]>, expected: [u8;32]) {
        let mut block_bits = [Bit::Const(false); 1024];
        for byte_index in 0..message_len {
            for bit in 0..8 {
                let value = message.map(|m| (m[byte_index] >> bit) & 1 != 0);
                block_bits[byte_index*8+bit] = self.witness(value);
            }
        }
        let m: [Word;16] = std::array::from_fn(|i| std::array::from_fn(|j| block_bits[i*64+j]));
        let h: [Word;8] = std::array::from_fn(|i| Self::const_word(
            if i == 0 { IV[i] ^ 0x01010020 } else { IV[i] }));
        let mut v: [Word;16] = std::array::from_fn(|i| Self::const_word(
            if i < 8 { if i == 0 { IV[0] ^ 0x01010020 } else { IV[i] } }
            else if i == 12 { IV[4] ^ message_len as u64 }
            else if i == 14 { IV[6] ^ u64::MAX }
            else { IV[i-8] }));
        for s in SIGMA {
            self.g(&mut v,0,4,8,12,&m[s[0]],&m[s[1]]);
            self.g(&mut v,1,5,9,13,&m[s[2]],&m[s[3]]);
            self.g(&mut v,2,6,10,14,&m[s[4]],&m[s[5]]);
            self.g(&mut v,3,7,11,15,&m[s[6]],&m[s[7]]);
            self.g(&mut v,0,5,10,15,&m[s[8]],&m[s[9]]);
            self.g(&mut v,1,6,11,12,&m[s[10]],&m[s[11]]);
            self.g(&mut v,2,7,8,13,&m[s[12]],&m[s[13]]);
            self.g(&mut v,3,4,9,14,&m[s[14]],&m[s[15]]);
        }
        let digest: [Word;4] = std::array::from_fn(|i| {
            let t = self.xor_words(&h[i], &v[i]);
            self.xor_words(&t, &v[i+8])
        });
        for (word_index, word) in digest.iter().enumerate() {
            for (bit_index, bit) in word.iter().enumerate() {
                let expected_bit = (expected[word_index*8 + bit_index/8] >> (bit_index%8)) & 1;
                let mut terms = Vec::with_capacity(1);
                let mut constant = -Fr::from(expected_bit as u64);
                Self::add_term(&mut terms, &mut constant, *bit, Fr::from(1u64));
                self.linear_residual(terms, constant);
            }
        }
    }
    // All local-operation residuals are degree at most two in input bits.
    // The reduction tree is linear; its only nonlinear leaves are XOR and
    // Booleanity gates whose children are direct inputs.
    fn expand_residual(
        &self, wire: Ref, scale: Fr, constant: &mut Fr,
        linear: &mut BTreeMap<usize, Fr>, quadratic: &mut BTreeMap<(usize, usize), Fr>,
    ) -> Result<(), String> {
        if scale == Fr::from(0u64) { return Ok(()); }
        match wire {
            Ref::Input(index) => *linear.entry(index).or_insert(Fr::from(0u64)) += scale,
            Ref::Node(index) => {
                let node = &self.nodes[index];
                *constant += scale * node.c0;
                self.expand_residual(node.left, scale * node.c1, constant, linear, quadratic)?;
                self.expand_residual(node.right, scale * node.c2, constant, linear, quadratic)?;
                if node.c3 != Fr::from(0u64) {
                    let (Ref::Input(left), Ref::Input(right)) = (node.left, node.right) else {
                        return Err(format!("non-input product at node {index}"));
                    };
                    let pair = if left <= right { (left, right) } else { (right, left) };
                    *quadratic.entry(pair).or_insert(Fr::from(0u64)) += scale * node.c3;
                }
            }
        }
        Ok(())
    }
    fn finish_sparse(mut self) -> Result<SparseCompiled, String> {
        self.input_len = self.input_len.next_power_of_two();
        if let Some(input) = &mut self.input {
            input.resize(self.input_len, Fr::from(0u64));
        }
        let residual_count = self.residuals.len();
        let row_count = residual_count.next_power_of_two();
        let mut terms = Vec::new();
        let zero = Fr::from(0u64);
        for (row, residual) in self.residuals.iter().enumerate() {
            let mut constant = zero;
            let mut linear = BTreeMap::new();
            let mut quadratic = BTreeMap::new();
            self.expand_residual(*residual, Fr::from(1u64), &mut constant,
                                 &mut linear, &mut quadratic)?;
            let mut row_gates = Vec::new();
            for ((left, right), c3) in quadratic {
                if c3 != zero {
                    let c1 = linear.remove(&left).unwrap_or(zero);
                    let c2 = if left == right { zero }
                             else { linear.remove(&right).unwrap_or(zero) };
                    row_gates.push(Gate { left, right, c0:zero, c1, c2, c3 });
                }
            }
            let nonzero_linear: Vec<_> = linear.into_iter()
                .filter(|(_, coefficient)| *coefficient != zero).collect();
            for pair in nonzero_linear.chunks(2) {
                let (left, c1) = pair[0];
                let (right, c2) = if pair.len() == 2 { pair[1] } else { (0, zero) };
                row_gates.push(Gate { left, right, c0:zero, c1, c2, c3:zero });
            }
            if row_gates.is_empty() {
                row_gates.push(Gate { left:0, right:0, c0:constant,
                                      c1:zero, c2:zero, c3:zero });
            } else {
                row_gates[0].c0 = constant;
            }
            terms.extend(row_gates.into_iter().map(|gate| Term { row, gate }));
        }
        self.stats.residuals = residual_count;
        self.stats.logical_gates = terms.len();
        self.stats.padded_gates = terms.len();
        self.stats.max_dependency_depth = 1;
        self.stats.max_layer_width = self.input_len.max(row_count);
        self.stats.nonzero_residuals = self.input.as_ref().map(|_| self.residuals.iter()
            .filter(|r| self.val(**r) != Some(zero)).count());
        Ok(SparseCompiled {
            input:self.input,
            circuit:SparseCircuit {input_len:self.input_len, row_count, terms},
            stats:self.stats,
        })
    }
    fn finish(mut self) -> Compiled {
        let actual_input_len = self.input_len;
        self.input_len = self.input_len.next_power_of_two();
        if let Some(input) = &mut self.input {
            input.resize(self.input_len, Fr::from(0u64));
        }
        let depth = self.residuals.iter().map(|r| self.depth(*r)).max().unwrap_or(0);
        let total_nodes = self.input_len + self.nodes.len();
        let id = |r: Ref| match r { Ref::Input(i) => i, Ref::Node(i) => self.input_len+i };
        let mut last_use = vec![0usize; total_nodes];
        for node in &self.nodes {
            let d = node.depth;
            last_use[id(node.left)] = last_use[id(node.left)].max(d);
            last_use[id(node.right)] = last_use[id(node.right)].max(d);
        }
        for r in &self.residuals { last_use[id(*r)] = depth+1; }
        let mut prior = vec![None; total_nodes];
        for i in 0..self.input_len { prior[i] = Some(i); }
        let zero = Fr::from(0u64);
        let one = Fr::from(1u64);
        let mut layers = Vec::with_capacity(depth+1);
        let mut logical_gates = 0usize;
        let mut padded_gates = 0usize;
        let mut max_layer_width = self.input_len;
        for d in 1..=depth {
            let mut layer = Vec::new();
            let mut next = vec![None; total_nodes];
            for i in 0..total_nodes {
                let made = if i < self.input_len { 0 } else { self.nodes[i-self.input_len].depth };
                if made < d && last_use[i] >= d {
                    let from = prior[i].expect("live wire must exist on previous layer");
                    next[i] = Some(layer.len());
                    layer.push(Gate { left:from, right:from, c0:zero,c1:one,c2:zero,c3:zero });
                }
            }
            for (i,node) in self.nodes.iter().enumerate() {
                if node.depth != d { continue; }
                let left = prior[id(node.left)].expect("gate left must exist on prior layer");
                let right = prior[id(node.right)].expect("gate right must exist on prior layer");
                next[self.input_len+i] = Some(layer.len());
                layer.push(Gate {left,right,c0:node.c0,c1:node.c1,c2:node.c2,c3:node.c3});
            }
            logical_gates += layer.len();
            let target = layer.len().next_power_of_two();
            layer.resize_with(target, || Gate {left:0,right:0,c0:zero,c1:zero,c2:zero,c3:zero});
            padded_gates += layer.len();
            max_layer_width = max_layer_width.max(layer.len());
            layers.push(layer);
            prior = next;
        }
        let mut final_layer = Vec::with_capacity(self.residuals.len());
        for r in &self.residuals {
            let from = prior[id(*r)].expect("residual must exist on prior layer");
            final_layer.push(Gate {left:from,right:from,c0:zero,c1:one,c2:zero,c3:zero});
        }
        logical_gates += final_layer.len();
        let target = final_layer.len().next_power_of_two();
        final_layer.resize_with(target, || Gate {left:0,right:0,c0:zero,c1:zero,c2:zero,c3:zero});
        padded_gates += final_layer.len();
        max_layer_width = max_layer_width.max(final_layer.len());
        layers.push(final_layer);
        let nonzero_residuals = self.input.as_ref().map(|_| self.residuals.iter()
            .filter(|r| self.val(**r) != Some(zero)).count());
        self.stats.residuals = self.residuals.len();
        self.stats.logical_gates = logical_gates;
        self.stats.padded_gates = padded_gates;
        self.stats.max_dependency_depth = depth+1;
        self.stats.max_layer_width = max_layer_width;
        self.stats.nonzero_residuals = nonzero_residuals;
        // Unreferenced power-of-two padding is fixed to zero in the prover's input.
        debug_assert!(actual_input_len <= self.input_len);
        Compiled {input:self.input,input_len:self.input_len,layers,stats:self.stats}
    }
}

/// Export each local-operation residual as sparse affine-bilinear terms over
/// the original witness input. Missing padded output rows evaluate to zero.
pub fn build_sparse(message: Option<&[u8]>, message_len: usize, expected: [u8;32])
    -> Result<SparseCompiled, String> {
    if message_len > 128 { return Err("single-block message length exceeds 128".into()); }
    if let Some(bytes) = message {
        if bytes.len() != message_len { return Err("message length mismatch".into()); }
    }
    let mut builder = Builder::new(message.is_some());
    builder.hash(message_len, message, expected);
    builder.finish_sparse()
}

/// A reusable compression relation. Public topology is independent of all
/// supplied values; callers must separately anchor the state/counter/flags.
/// All eight output words and every unused padded input slot are constrained.
fn compression_program(b: &mut Builder, input: Option<&CompressionInput>)
    -> (CompressionLayout, Option<[u64; 8]>) {
    fn indices(word: &Word) -> [usize; 64] {
        word.map(|bit| match bit { Bit::Var(i) => i, _ => unreachable!() })
    }
    let h: [Word; 8] = std::array::from_fn(|i| std::array::from_fn(|j|
        b.witness(input.map(|x| (x.state[i] >> j) & 1 != 0))));
    let m: [Word; 16] = std::array::from_fn(|i| std::array::from_fn(|j|
        b.witness(input.map(|x| (x.block[i*8+j/8] >> (j%8)) & 1 != 0))));
    let counter: Word = std::array::from_fn(|j|
        b.witness(input.map(|x| (x.counter >> j) & 1 != 0)));
    let flag = b.witness(input.map(|x| x.final_flag));
    let mut v: [Word; 16] = std::array::from_fn(|i|
        if i < 8 { h[i] } else { Builder::const_word(IV[i-8]) });
    v[12] = b.xor_words(&v[12], &counter);
    // Counter high word is the constant zero. The flag is a single Boolean
    // broadcast to all 64 mask bits, not 64 independent selector bits.
    v[14] = b.xor_words(&v[14], &[flag; 64]);
    for s in SIGMA {
        b.g(&mut v,0,4,8,12,&m[s[0]],&m[s[1]]);
        b.g(&mut v,1,5,9,13,&m[s[2]],&m[s[3]]);
        b.g(&mut v,2,6,10,14,&m[s[4]],&m[s[5]]);
        b.g(&mut v,3,7,11,15,&m[s[6]],&m[s[7]]);
        b.g(&mut v,0,5,10,15,&m[s[8]],&m[s[9]]);
        b.g(&mut v,1,6,11,12,&m[s[10]],&m[s[11]]);
        b.g(&mut v,2,7,8,13,&m[s[12]],&m[s[13]]);
        b.g(&mut v,3,4,9,14,&m[s[14]],&m[s[15]]);
    }
    let out: [Word; 8] = std::array::from_fn(|i| {
        let intermediate = b.xor_words(&h[i], &v[i]);
        b.xor_words(&intermediate, &v[i+8])
    });
    let output = input.map(|_| std::array::from_fn(|i| b.word_value(&out[i]).unwrap()));
    let layout = CompressionLayout {
        state: h.map(|w| indices(&w)), message: m.map(|w| indices(&w)),
        counter: indices(&counter),
        final_flag: match flag { Bit::Var(i) => i, _ => unreachable!() },
        output: out.map(|w| indices(&w)), used_input_len: b.input_len,
    };
    (layout, output)
}

/// The classic builder remains the circuit and differential reference path.
pub fn build_compression(input: Option<&CompressionInput>)
    -> Result<CompressionCompiled, String> {
    let mut b = Builder::new(input.is_some());
    let (layout, output) = compression_program(&mut b, input);
    let padded = b.input_len.next_power_of_two();
    let used = b.input_len;
    b.input_len = padded;
    if let Some(values) = &mut b.input { values.resize(padded, Fr::from(0u64)); }
    for index in used..padded {
        b.linear_residual(vec![(Ref::Input(index), Fr::from(1u64))], Fr::from(0u64));
    }
    Ok(CompressionCompiled { compiled: b.finish_sparse()?, layout, output })
}

/// Assign the same operation sequence against the consumer's canonical shape.
/// Caller geometry is checked after a fixed-size assignment and before padding;
/// no caller circuit or requested width controls the assignment allocations.
pub(crate) fn assign_compression(
    input: &CompressionInput,
    expected_layout: &CompressionLayout,
    expected_input_len: usize,
) -> Result<CompressionAssignment, String> {
    let mut b = Builder::with_mode(true, true);
    let (layout, output) = compression_program(&mut b, Some(input));
    if &layout != expected_layout {
        return Err("compression assignment canonical layout mismatch".into());
    }
    let padded = b.input_len.next_power_of_two();
    if expected_input_len != padded {
        return Err("compression assignment canonical input width mismatch".into());
    }
    if !b.nodes.is_empty() || !b.residuals.is_empty() {
        return Err("compression assignment retained circuit state".into());
    }
    let mut values = b.input.take().ok_or("compression assignment values missing")?;
    if values.len() != layout.used_input_len {
        return Err("compression assignment used input width mismatch".into());
    }
    values.resize(padded, Fr::from(0u64));
    Ok(CompressionAssignment {
        input: values,
        layout,
        output: output.ok_or("compression assignment output missing")?,
    })
}

/// Build a one-block, unkeyed BLAKE2b-256 relation with fixed public length.
/// `None` constructs only topology; `Some` adds a complete local-operation witness.
pub fn build(message: Option<&[u8]>, message_len: usize, expected: [u8;32],
             mode: Mode) -> Result<Compiled, String> {
    if message_len > 128 { return Err("single-block message length exceeds 128".into()); }
    if let Some(bytes) = message {
        if bytes.len() != message_len { return Err("message length mismatch".into()); }
    }
    match mode { Mode::LocalOps => {} }
    let mut builder = Builder::new(message.is_some());
    builder.hash(message_len,message,expected);
    Ok(builder.finish())
}

#[cfg(test)]
mod tests {
    use super::*;
    use blake2::{Blake2bVar, digest::{Update, VariableOutput}};

    fn digest(message: &[u8]) -> [u8;32] {
        let mut hasher = Blake2bVar::new(32).unwrap();
        hasher.update(message);
        let mut out = [0u8;32];
        hasher.finalize_variable(&mut out).unwrap();
        out
    }
    fn evaluate(input: Vec<Fr>, layers: &[Layer]) -> Vec<Fr> {
        layers.iter().fold(input, |prior, layer| {
            layer.iter().map(|g| g.evaluate(&prior)).collect()
        })
    }
    fn evaluate_sparse(input: &[Fr], circuit: &SparseCircuit) -> Vec<Fr> {
        let mut rows = vec![Fr::from(0u64); circuit.row_count];
        for term in &circuit.terms {
            rows[term.row] += term.gate.evaluate(input);
        }
        rows
    }
    // Independent native word-arithmetic implementation of compression. The
    // schedule constants are shared; external Blake2bVar vectors separately
    // check the schedule and complete hash in history_join's tests.
    fn reference_compression(input: &CompressionInput) -> [u64; 8] {
        fn mix(v: &mut [u64; 16], p: [usize; 4], x: u64, y: u64) {
            let [a,b,c,d] = p;
            v[a] = v[a].wrapping_add(v[b]).wrapping_add(x);
            v[d] = (v[d] ^ v[a]).rotate_right(32);
            v[c] = v[c].wrapping_add(v[d]);
            v[b] = (v[b] ^ v[c]).rotate_right(24);
            v[a] = v[a].wrapping_add(v[b]).wrapping_add(y);
            v[d] = (v[d] ^ v[a]).rotate_right(16);
            v[c] = v[c].wrapping_add(v[d]);
            v[b] = (v[b] ^ v[c]).rotate_right(63);
        }
        let m: [u64; 16] = std::array::from_fn(|i|
            u64::from_le_bytes(input.block[i*8..i*8+8].try_into().unwrap()));
        let mut v = [0u64; 16];
        v[..8].copy_from_slice(&input.state);
        v[8..].copy_from_slice(&IV);
        v[12] ^= input.counter;
        if input.final_flag { v[14] = !v[14]; }
        let positions = [[0,4,8,12],[1,5,9,13],[2,6,10,14],[3,7,11,15],
                         [0,5,10,15],[1,6,11,12],[2,7,8,13],[3,4,9,14]];
        for schedule in SIGMA {
            for (i, position) in positions.iter().enumerate() {
                mix(&mut v, *position, m[schedule[2*i]], m[schedule[2*i+1]]);
            }
        }
        std::array::from_fn(|i| input.state[i] ^ v[i] ^ v[i+8])
    }

    #[test]
    fn compression_assignment_matches_classic_witness_and_preserves_core() {
        let template = build_compression(None).unwrap();
        assert_eq!(template.compiled.circuit.input_len, 65536);
        assert_eq!(template.compiled.circuit.row_count, 131072);
        assert_eq!(template.compiled.circuit.terms.len(), 172480);
        let before = crate::work_tree_layout::hash_terms(&template.compiled.circuit.terms);
        let mut cases = Vec::new();
        for filled in [false, true] {
            for counter in [0, 128, 256, u64::MAX] {
                for final_flag in [false, true] {
                    cases.push(CompressionInput {
                        state: [if filled { u64::MAX } else { 0 }; 8],
                        block: [if filled { 255 } else { 0 }; 128],
                        counter,
                        final_flag,
                    });
                }
            }
        }
        fn next(seed: &mut u64) -> u64 {
            *seed ^= *seed << 13;
            *seed ^= *seed >> 7;
            *seed ^= *seed << 17;
            *seed
        }
        let mut seed = 0x7165_e8bd_c923_04a1u64;
        for case in 0..8 {
            cases.push(CompressionInput {
                state: std::array::from_fn(|_| next(&mut seed)),
                block: std::array::from_fn(|_| next(&mut seed) as u8),
                counter: next(&mut seed),
                final_flag: case % 2 == 0,
            });
        }
        for (case, input) in cases.iter().enumerate() {
            let classic = build_compression(Some(input)).unwrap();
            let assigned = assign_compression(
                input, &template.layout, template.compiled.circuit.input_len,
            ).unwrap();
            assert_eq!(classic.compiled.circuit, template.compiled.circuit, "case{case}");
            assert_eq!(classic.layout, template.layout, "case{case}");
            assert_eq!(assigned.layout, classic.layout, "case{case}");
            assert_eq!(assigned.input, *classic.compiled.input.as_ref().unwrap(), "case{case}");
            assert_eq!(assigned.output, classic.output.unwrap(), "case{case}");
            assert_eq!(assigned.output, reference_compression(input), "case{case}");
            assert!(evaluate_sparse(&assigned.input, &template.compiled.circuit)
                .into_iter().all(|value| value == Fr::from(0u64)), "case{case}");
            assert!(assigned.input[assigned.layout.used_input_len..]
                .iter().all(|value| *value == Fr::from(0u64)));
        }
        let after = build_compression(None).unwrap();
        assert_eq!(after.layout, template.layout);
        assert_eq!(after.compiled.circuit, template.compiled.circuit);
        assert_eq!(crate::work_tree_layout::hash_terms(&after.compiled.circuit.terms), before);
        println!("compression assignment: 24 full witness/output/reference differentials; canonical core unchanged");
    }

    #[test]
    fn compression_assignment_rejects_geometry_and_isolated_core_faults() {
        let template = build_compression(None).unwrap();
        let source = CompressionInput {
            state: blake2b256_initial_state(),
            block: std::array::from_fn(|index| (index as u8).wrapping_mul(197)),
            counter: 128,
            final_flag: true,
        };
        for width in [0, template.compiled.circuit.input_len - 1,
            template.compiled.circuit.input_len + 1, usize::MAX] {
            assert!(assign_compression(&source, &template.layout, width)
                .err().unwrap().contains("canonical input width"));
        }
        for fault in 0..7 {
            let mut layout = template.layout.clone();
            match fault {
                0 => layout.state[0][0] += 1,
                1 => layout.message[0][0] += 1,
                2 => layout.counter[0] += 1,
                3 => layout.final_flag += 1,
                4 => layout.output[0][0] += 1,
                5 => layout.used_input_len += 1,
                _ => layout.state[7][63] = usize::MAX,
            }
            assert!(assign_compression(&source, &layout, template.compiled.circuit.input_len)
                .err().unwrap().contains("canonical layout"));
        }
        let assigned = assign_compression(
            &source, &template.layout, template.compiled.circuit.input_len,
        ).unwrap();
        let core = &template.compiled.circuit;
        assert!(evaluate_sparse(&assigned.input, core).iter().all(|value| *value == Fr::from(0u64)));
        let faults = [
            ("zero", 0usize),
            ("state", assigned.layout.state[0][0]),
            ("message", assigned.layout.message[3][7]),
            ("counter", assigned.layout.counter[63]),
            ("flag", assigned.layout.final_flag),
            ("output", assigned.layout.output[7][63]),
            ("padding", assigned.layout.used_input_len),
        ];
        assert!(assigned.layout.used_input_len < core.input_len);
        for (name, wire) in faults {
            let mut changed = assigned.input.clone();
            changed[wire] = Fr::from(1u64) - changed[wire];
            let residuals = evaluate_sparse(&changed, core);
            let row = residuals.iter().position(|value| *value != Fr::from(0u64))
                .unwrap_or_else(|| panic!("{name} single-cell mutation was accepted"));
            assert!(core.terms.iter().any(|term| term.row == row &&
                ((term.gate.left == wire && (term.gate.c1 != Fr::from(0u64) || term.gate.c3 != Fr::from(0u64))) ||
                 (term.gate.right == wire && (term.gate.c2 != Fr::from(0u64) || term.gate.c3 != Fr::from(0u64))))),
                "{name} rejection must consume the mutated cell");
            if name == "zero" || name == "padding" {
                assert!(core.terms.iter().any(|term| term.row == row && term.gate.left == wire &&
                    term.gate.c0 == Fr::from(0u64) && term.gate.c1 == Fr::from(1u64) &&
                    term.gate.c2 == Fr::from(0u64) && term.gate.c3 == Fr::from(0u64)),
                    "{name} mutation must reach the original zero anchor");
            }
            println!("compression isolated fault={name} wire={wire} rejected_row={row}");
        }
        let mut non_boolean = assigned.input.clone();
        let wire = assigned.layout.state[0][0];
        non_boolean[wire] = Fr::from(2u64);
        let residuals = evaluate_sparse(&non_boolean, core);
        assert_eq!(residuals[1], Fr::from(2u64), "first state bit must reach its Boolean predicate");
        assert!(core.terms.iter().any(|term| term.row == 1 && term.gate.left == wire &&
            term.gate.right == wire && term.gate.c0 == Fr::from(0u64) &&
            term.gate.c1 == -Fr::from(1u64) && term.gate.c2 == Fr::from(0u64) && term.gate.c3 == Fr::from(1u64)));
        println!("compression assignment guards: 4 widths,7 layouts,8 isolated core predicates rejected");
    }

    #[test]
    fn generic_compression_matches_all_eight_native_words() {
        for final_flag in [false, true] {
            let input = CompressionInput {
                state: std::array::from_fn(|i| IV[i] ^ (0xdeadbeefu64 << i)),
                block: std::array::from_fn(|i| (i as u8).wrapping_mul(197)),
                counter: if final_flag { u64::MAX } else { 1 << 63 }, final_flag,
            };
            let compiled = build_compression(Some(&input)).unwrap();
            assert_eq!(compiled.output.unwrap(), reference_compression(&input));
            assert_eq!(compiled.compiled.stats.nonzero_residuals, Some(0));
            let values = compiled.compiled.input.unwrap();
            assert!(evaluate_sparse(&values, &compiled.compiled.circuit)
                .into_iter().all(|x| x == Fr::from(0u64)));
            for word in 0..8 {
                let mut altered = values.clone();
                let index = compiled.layout.output[word][word*7];
                altered[index] = Fr::from(1u64)-altered[index];
                assert!(evaluate_sparse(&altered, &compiled.compiled.circuit)
                    .into_iter().any(|x| x != Fr::from(0u64)));
            }
        }
    }
    #[test]
    fn sparse_matches_every_layered_residual_over_field() {
        for length in [0usize, 1, 128] {
            let message: Vec<u8> = (0..length)
                .map(|i| (i as u8).wrapping_mul(37).wrapping_add(11)).collect();
            let expected = digest(&message);
            let layered = build(Some(&message), length, expected, Mode::LocalOps).unwrap();
            let sparse = build_sparse(Some(&message), length, expected).unwrap();
            let verifier = build_sparse(None, length, expected).unwrap();
            assert_eq!(sparse.circuit.input_len, layered.input_len);
            assert_eq!(sparse.circuit.input_len, verifier.circuit.input_len);
            assert_eq!(sparse.circuit.row_count, layered.layers.last().unwrap().len());
            assert_eq!(sparse.circuit.row_count, verifier.circuit.row_count);
            assert_eq!(sparse.circuit.terms.len(), verifier.circuit.terms.len());
            for (prover_term, verifier_term) in sparse.circuit.terms.iter()
                .zip(&verifier.circuit.terms) {
                assert_eq!(prover_term.row, verifier_term.row);
                assert_eq!(prover_term.gate, verifier_term.gate);
            }
            let honest = layered.input.unwrap();
            assert_eq!(evaluate(honest.clone(), &layered.layers),
                       evaluate_sparse(&honest, &sparse.circuit));
            let arbitrary: Vec<Fr> = (0..sparse.circuit.input_len).map(|i| {
                Fr::from((i as u64).wrapping_mul(0x9e3779b97f4a7c15)
                    .wrapping_add(0x243f6a8885a308d3))
            }).collect();
            assert_eq!(evaluate(arbitrary.clone(), &layered.layers),
                       evaluate_sparse(&arbitrary, &sparse.circuit));
            eprintln!("sparse_length={length} rows={} terms={}",
                      sparse.circuit.row_count, sparse.circuit.terms.len());
        }
    }
    #[test]
    fn hash_and_topology() {
        for length in [0usize, 1, 128] {
            let message: Vec<u8> = (0..length).map(|i| (i as u8).wrapping_mul(37).wrapping_add(11)).collect();
            let expected = digest(&message);
            let prover = build(Some(&message), length, expected, Mode::LocalOps).unwrap();
            let verifier = build(None, length, expected, Mode::LocalOps).unwrap();
            assert_eq!(prover.input_len, verifier.input_len);
            assert_eq!(prover.layers, verifier.layers);
            assert_eq!(prover.stats.nonzero_residuals, Some(0));
            eprintln!("blake_length={length} input={} layers={} logical_gates={} padded_gates={} max_layer_width={} adds={} xor_words={} residuals={}",
                      prover.input_len, prover.layers.len(), prover.stats.logical_gates,
                      prover.stats.padded_gates, prover.stats.max_layer_width,
                      prover.stats.add_words, prover.stats.xor_words, prover.stats.residuals);
            assert!(evaluate(prover.input.clone().unwrap(), &prover.layers)
                    .iter().all(|x| *x == Fr::from(0u64)));
            let mut altered = prover.input.clone().unwrap();
            altered[1] += Fr::from(1u64);
            assert!(evaluate(altered, &prover.layers)
                    .iter().any(|x| *x != Fr::from(0u64)));
            let mut wrong = expected;
            wrong[0] ^= 1;
            let bad = build(Some(&message), length, wrong, Mode::LocalOps).unwrap();
            assert!(bad.stats.nonzero_residuals.unwrap() > 0);
        }
    }
    #[test]
    fn rejects_invalid_length() {
        assert!(build(None, 129, [0;32], Mode::LocalOps).is_err());
        assert!(build(Some(&[1]), 0, [0;32], Mode::LocalOps).is_err());
    }

    fn one_nonzero_residual(input: Vec<Fr>, layers: &[Layer]) -> Fr {
        let nonzero: Vec<Fr> = evaluate(input, layers)
            .into_iter().filter(|value| *value != Fr::from(0u64)).collect();
        assert_eq!(nonzero.len(), 1);
        nonzero[0]
    }

    #[test]
    fn booleanity_rejects_field_two_alone() {
        let mut builder = Builder::new(true);
        builder.witness(Some(false));
        let compiled = builder.finish();
        assert_eq!(compiled.stats.residuals, 2); // dummy zero + one Booleanity
        let mut input = compiled.input.unwrap();
        input[1] = Fr::from(2u64);
        assert_eq!(one_nonzero_residual(input, &compiled.layers), Fr::from(2u64));
    }

    #[test]
    fn packed_add_carry_flip_isolated() {
        let mut builder = Builder::new(true);
        let max = Builder::const_word(u64::MAX);
        let one = Builder::const_word(1);
        builder.add_words(&max, &one);
        let carry_index = builder.input_len - 1;
        let compiled = builder.finish();
        assert_eq!(compiled.stats.residuals, 67); // dummy + 65 bits + packed add
        let mut input = compiled.input.unwrap();
        assert_eq!(input[carry_index], Fr::from(1u64));
        input[carry_index] = Fr::from(0u64);
        let mut two_to_64 = Fr::from(1u64);
        for _ in 0..64 { two_to_64 += two_to_64; }
        assert_eq!(one_nonzero_residual(input, &compiled.layers), two_to_64);
    }

    #[test]
    fn xor_result_flip_isolated() {
        let mut builder = Builder::new(true);
        let a = builder.witness(Some(false));
        let b = builder.witness(Some(true));
        let z = builder.xor_bit(a, b);
        let z_index = match z { Bit::Var(i) => i, Bit::Const(_) => unreachable!() };
        let compiled = builder.finish();
        assert_eq!(compiled.stats.residuals, 5); // dummy + three bits + XOR
        let mut input = compiled.input.unwrap();
        assert_eq!(input[z_index], Fr::from(1u64));
        input[z_index] = Fr::from(0u64);
        assert_eq!(one_nonzero_residual(input, &compiled.layers), Fr::from(1u64));
    }

    #[test]
    fn dummy_zero_is_constrained() {
        let compiled = Builder::new(true).finish();
        assert_eq!(compiled.stats.residuals, 1);
        let mut input = compiled.input.unwrap();
        input[0] = Fr::from(1u64);
        assert_eq!(one_nonzero_residual(input, &compiled.layers), Fr::from(1u64));
    }
}

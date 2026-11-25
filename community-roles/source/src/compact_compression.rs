//! Private one-compression diagnostic. Internal gate storage changes; the
//! adjacent-layer polynomial, literal circuit transcript and GKR codec do not.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use blake2::{Blake2b512, Digest};
use std::mem::{align_of, size_of};

use crate::{circuit, gkr, transcript::Transcript};

pub(crate) const INPUT_WIDTH: usize = 2048;
pub(crate) const USED_INPUT: usize = 1602;
pub(crate) const PRIMARY_NODES: usize = 693569;
pub(crate) const PRIMARY_GATES: usize = 15138816;
const MAX_GATES: usize = 33554432;
const LOGICAL_LIMIT: usize = 1024 * 1024 * 1024;
const UNUSED: u32 = u32::MAX;
const GRAPH_BLAKE: &str = "9C7B85DA31C5375FF8915C640AC13F254BCFAEEC70E4033E4EA44FAF33788EFD60D3733FF09B7B5819EAD4313CADBD4B723931089C9791B5E60D2C151D1D7111";
const WIDTH_BLAKE: &str = "CC1D29348944A8E14FCF3D10A3E3249EAB2A8C0FD84D414898ACE93DDB78B2772D1967B2DDB9BA294C6258B3B173180A9CC1359CFB2D0CA34D23535B634A1863";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub(crate) struct CompactGate {
    pub(crate) left: u32,
    pub(crate) right: u32,
    pub(crate) kind: u8,
    pub(crate) expectedbit: u8,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Error {
    Capacity, Shape, GateKind, GateParameter, WireIndex, InputDimension,
    NonzeroOutput, PointDimension, Oracle, Gkr(gkr::GkrError),
}
impl From<gkr::GkrError> for Error {
    fn from(e: gkr::GkrError) -> Self { Self::Gkr(e) }
}

fn validate_raw(g: CompactGate, previous: usize) -> Result<(), Error> {
    if g.left as usize >= previous || g.right as usize >= previous {
        return Err(Error::WireIndex);
    }
    if g.kind > 6 { return Err(Error::GateKind); }
    if g.expectedbit > 1 || (!matches!(g.kind, 0 | 6) && g.expectedbit != 0) {
        return Err(Error::GateParameter);
    }
    if g.kind == 5 && g.left != g.right { return Err(Error::GateParameter); }
    Ok(())
}

pub(crate) fn decode_gate(g: CompactGate, previous: usize) -> Result<gkr::Gate, Error> {
    validate_raw(g, previous)?;
    let z = Fr::zero();
    let o = Fr::one();
    let (c0, c1, c2, c3) = match g.kind {
        0 => (Fr::from(g.expectedbit as u64), z, z, z),
        1 => (z, o, z, z),
        2 => (z, o, o, -Fr::from(2u64)),
        3 => (z, z, z, o),
        4 => (z, o, o, z),
        5 => (z, -o, z, o),
        6 => (-Fr::from(g.expectedbit as u64), o, z, z),
        _ => return Err(Error::GateKind),
    };
    Ok(gkr::Gate { left: g.left as usize, right: g.right as usize, c0, c1, c2, c3 })
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct Resources {
    pub(crate) used_input: usize,
    pub(crate) input_width: usize,
    pub(crate) layers: usize,
    pub(crate) primitive_nodes: usize,
    pub(crate) forwarding_gates: usize,
    pub(crate) logical_gates: usize,
    pub(crate) padding_gates: usize,
    pub(crate) padded_gates: usize,
    pub(crate) max_width: usize,
    pub(crate) dependency_depth: usize,
    pub(crate) gate_capacity_bytes: usize,
    pub(crate) node_capacity_bytes: usize,
    pub(crate) map_peak_bytes: usize,
    pub(crate) layer_header_bytes: usize,
    pub(crate) values_bytes: usize,
    pub(crate) phase_peak_bytes: usize,
    pub(crate) proof_scalars: usize,
    pub(crate) proof_bytes: usize,
    pub(crate) challenges: usize,
    pub(crate) compiler_peak_bytes: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Audit {
    pub(crate) graph_blake: [u8; 64],
    pub(crate) widths_blake: [u8; 64],
}

pub(crate) struct Compiled {
    input_len: usize,
    layers: Vec<Vec<CompactGate>>,
    dimensions: Vec<usize>,
    resources: Resources,
    audit: Audit,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct EvaluationResources {
    pub(crate) values_len_bytes: usize,
    pub(crate) values_capacity_bytes: usize,
    pub(crate) layer_headers_bytes: usize,
}
pub(crate) struct Evaluation<'a> {
    circuit: &'a Compiled,
    values: Vec<Vec<Fr>>,
    resources: EvaluationResources,
}
impl Evaluation<'_> {
    /// Index0 is the input; index1 is the first computed layer.
    pub(crate) fn layer(&self, index: usize) -> &[Fr] { &self.values[index] }
    pub(crate) fn resources(&self) -> EvaluationResources { self.resources }
}

fn abi() -> Result<(), Error> {
    if size_of::<Fr>() != 32 || align_of::<Fr>() != 8
        || size_of::<CompactGate>() != 12 || align_of::<CompactGate>() != 4
        || size_of::<Node>() != 16 || align_of::<Node>() != 4 {
        return Err(Error::Capacity);
    }
    Ok(())
}
fn hex64(s: &str) -> Result<[u8; 64], Error> {
    if s.len() != 128 { return Err(Error::Shape); }
    let mut result = [0; 64];
    for (i, b) in result.iter_mut().enumerate() {
        *b = u8::from_str_radix(&s[2*i..2*i+2], 16).map_err(|_| Error::Shape)?;
    }
    Ok(result)
}

// No field element in the compiler's graph. Node IDs are canonical original
// input/node IDs, not physical positions in any adjacent layer.
#[derive(Clone, Copy)]
#[repr(C)]
struct Node { left: u32, right: u32, depth: u32, kind: u8, expectedbit: u8 }
struct Builder {
    nodes: Vec<Node>, last: Vec<u32>, residuals: Vec<u32>, graph: Blake2b512,
    additions: usize, word_xors: usize,
}
type Word = [u32; 64];
impl Builder {
    fn new() -> Self {
        let mut last = Vec::with_capacity(INPUT_WIDTH + PRIMARY_NODES);
        last.resize(INPUT_WIDTH, 0);
        Self { nodes: Vec::with_capacity(PRIMARY_NODES), last,
            residuals: Vec::with_capacity(2560), graph: Blake2b512::new(),
            additions: 0, word_xors: 0 }
    }
    fn depth(&self, id: u32) -> u32 {
        if (id as usize) < INPUT_WIDTH { 0 } else { self.nodes[id as usize - INPUT_WIDTH].depth }
    }
    fn emit(&mut self, kind: u8, expectedbit: u8, left: u32, right: u32) -> u32 {
        assert!(self.nodes.len() < PRIMARY_NODES, "fixed native graph extent");
        let id = (INPUT_WIDTH + self.nodes.len()) as u32;
        assert!(left < id && right < id, "topological native graph");
        let depth = self.depth(left).max(self.depth(right)) + 1;
        self.last[left as usize] = self.last[left as usize].max(depth);
        self.last[right as usize] = self.last[right as usize].max(depth);
        self.last.push(0);
        self.nodes.push(Node { left, right, depth, kind, expectedbit });
        let op = match kind { 0 => 1, 1 => 6, 2 => 2, 3 => 3, 4 => 4, 5 => 5, 6 => 7, _ => unreachable!() };
        self.graph.update([op]);
        for value in [id, left, right, depth] { self.graph.update(value.to_le_bytes()); }
        id
    }
    fn xor_word(&mut self, a: Word, b: Word) -> Word {
        self.word_xors += 1;
        std::array::from_fn(|i| self.emit(2, 0, a[i], b[i]))
    }
    fn add_word(&mut self, a: Word, b: Word) -> Word {
        self.additions += 1;
        let original: Word = std::array::from_fn(|i| self.emit(2, 0, a[i], b[i]));
        let mut p = original;
        let mut g: Word = std::array::from_fn(|i| self.emit(3, 0, a[i], b[i]));
        for distance in [1usize, 2, 4, 8, 16, 32] {
            let old_p = p;
            let old_g = g;
            for i in 0..64 {
                if i < distance { p[i] = old_p[i]; g[i] = old_g[i]; }
                else {
                    p[i] = self.emit(3, 0, old_p[i], old_p[i-distance]);
                    let v = self.emit(3, 0, old_p[i], old_g[i-distance]);
                    g[i] = self.emit(4, 0, old_g[i], v);
                }
            }
        }
        std::array::from_fn(|i| self.emit(2, 0, original[i], if i == 0 { 0 } else { g[i-1] }))
    }
    fn rotate(w: Word, distance: usize) -> Word {
        std::array::from_fn(|i| w[(i+distance)%64])
    }
    fn g(&mut self, v: &mut [Word; 16], a: usize,b: usize,c: usize,d: usize,x: Word,y: Word) {
        let first = self.add_word(v[a], v[b]);
        v[a] = self.add_word(first, x);
        v[d] = Self::rotate(self.xor_word(v[d], v[a]), 32);
        v[c] = self.add_word(v[c], v[d]);
        v[b] = Self::rotate(self.xor_word(v[b], v[c]), 24);
        let second = self.add_word(v[a], v[b]);
        v[a] = self.add_word(second, y);
        v[d] = Self::rotate(self.xor_word(v[d], v[a]), 16);
        v[c] = self.add_word(v[c], v[d]);
        v[b] = Self::rotate(self.xor_word(v[b], v[c]), 63);
    }
}

const IV: [u64; 8] = [
    0x6a09e667f3bcc908,0xbb67ae8584caa73b,0x3c6ef372fe94f82b,0xa54ff53a5f1d36f1,
    0x510e527fade682d1,0x9b05688c2b3e6c1f,0x1f83d9abfb41bd6b,0x5be0cd19137e2179,
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

pub(crate) fn compile(expected: [u64; 8]) -> Result<Compiled, Error> {
    abi()?;
    let mut b = Builder::new();
    let one = b.emit(0, 1, 0, 0);
    for i in 0..INPUT_WIDTH {
        let r = b.emit(if (1..=1601).contains(&i) { 5 } else { 1 }, 0, i as u32, i as u32);
        b.residuals.push(r);
    }
    let h: [Word; 8] = std::array::from_fn(|i| std::array::from_fn(|j| (1+64*i+j) as u32));
    let m: [Word; 16] = std::array::from_fn(|i| std::array::from_fn(|j| (513+64*i+j) as u32));
    let mut v: [Word; 16] = std::array::from_fn(|i| if i < 8 { h[i] }
        else { std::array::from_fn(|j| if (IV[i-8] >> j)&1 != 0 { one } else { 0 }) });
    v[12] = b.xor_word(v[12], std::array::from_fn(|j| (1537+j) as u32));
    v[14] = b.xor_word(v[14], [1601; 64]);
    for s in SIGMA {
        for [a,c0,c1,d,x,y] in [[0,4,8,12,0,1],[1,5,9,13,2,3],
            [2,6,10,14,4,5],[3,7,11,15,6,7],[0,5,10,15,8,9],
            [1,6,11,12,10,11],[2,7,8,13,12,13],[3,4,9,14,14,15]] {
            b.g(&mut v,a,c0,c1,d,m[s[x]],m[s[y]]);
        }
    }
    let outputs: [Word; 8] = std::array::from_fn(|i| {
        let t = b.xor_word(h[i], v[i]); b.xor_word(t, v[i+8])
    });
    for i in 0..8 {
        for j in 0..64 {
            let r = b.emit(6, ((expected[i] >> j)&1) as u8, outputs[i][j], 0);
            b.residuals.push(r);
        }
    }
    if b.nodes.len() != PRIMARY_NODES || b.residuals.len() != 2560
        || b.additions != 576 || b.word_xors != 402 { return Err(Error::Shape); }
    let depth = b.residuals.iter().map(|&id| b.depth(id)).max().ok_or(Error::Shape)? as usize;
    if depth != 1852 { return Err(Error::Shape); }
    for &id in &b.residuals { b.last[id as usize] = (depth+1) as u32; }
    let graph_blake: [u8; 64] = b.graph.clone().finalize().into();
    if graph_blake != hex64(GRAPH_BLAKE)? { return Err(Error::Shape); }

    // Depth buckets and sorted live original IDs give the exact finish order
    // without scanning all693569 nodes at each of1852 depths.
    let mut histogram = vec![0usize; depth+1];
    for n in &b.nodes { histogram[n.depth as usize] += 1; }
    let mut buckets: Vec<Vec<u32>> = histogram.iter().map(|&n| Vec::with_capacity(n)).collect();
    for (i,n) in b.nodes.iter().enumerate() { buckets[n.depth as usize].push((INPUT_WIDTH+i) as u32); }
    let mut prior = vec![UNUSED; b.last.len()];
    let mut next = vec![UNUSED; b.last.len()];
    for i in 0..INPUT_WIDTH { prior[i] = i as u32; }
    let mut live = Vec::with_capacity(8192);
    live.extend((0..INPUT_WIDTH).map(|i| i as u32));
    let mut next_live = Vec::with_capacity(8192);
    let mut layers = Vec::with_capacity(depth+1);
    let mut widths = Blake2b512::new();
    let mut forwarding = 0usize;
    let mut logical = 0usize;
    for d in 1..=depth {
        let forwards = live.iter().filter(|&&id| b.depth(id) < d as u32 && b.last[id as usize] >= d as u32).count();
        let raw = forwards + buckets[d].len();
        let target = raw.checked_next_power_of_two().ok_or(Error::Capacity)?;
        if target > 8192 { return Err(Error::Capacity); }
        let mut layer = Vec::with_capacity(target);
        next_live.clear();
        for &id in &live {
            if b.depth(id) < d as u32 && b.last[id as usize] >= d as u32 {
                let from = prior[id as usize];
                if from == UNUSED { return Err(Error::Shape); }
                next[id as usize] = layer.len() as u32;
                layer.push(CompactGate { left: from, right: from, kind: 1, expectedbit: 0 });
                next_live.push(id);
            }
        }
        for &id in &buckets[d] {
            let n = b.nodes[id as usize-INPUT_WIDTH];
            let left = prior[n.left as usize];
            let right = prior[n.right as usize];
            if left == UNUSED || right == UNUSED { return Err(Error::Shape); }
            next[id as usize] = layer.len() as u32;
            layer.push(CompactGate { left, right, kind: n.kind, expectedbit: n.expectedbit });
            next_live.push(id);
        }
        if layer.len() != raw { return Err(Error::Shape); }
        widths.update((raw as u32).to_le_bytes());
        widths.update((target as u32).to_le_bytes());
        layer.resize(target, CompactGate { left: 0, right: 0, kind: 0, expectedbit: 0 });
        forwarding += forwards;
        logical += raw;
        layers.push(layer);
        next_live.sort_unstable();
        std::mem::swap(&mut live, &mut next_live);
        std::mem::swap(&mut prior, &mut next);
    }
    let mut final_layer = Vec::with_capacity(4096);
    for &id in &b.residuals {
        let from = prior[id as usize];
        if from == UNUSED { return Err(Error::Shape); }
        final_layer.push(CompactGate { left: from, right: from, kind: 1, expectedbit: 0 });
    }
    widths.update((final_layer.len() as u32).to_le_bytes());
    widths.update(4096u32.to_le_bytes());
    logical += final_layer.len();
    final_layer.resize(4096, CompactGate { left: 0, right: 0, kind: 0, expectedbit: 0 });
    layers.push(final_layer);
    let widths_blake: [u8; 64] = widths.finalize().into();
    if widths_blake != hex64(WIDTH_BLAKE)? { return Err(Error::Shape); }
    let mut result = finish(INPUT_WIDTH, layers, Audit { graph_blake, widths_blake })?;
    let r = &mut result.resources;
    r.used_input = USED_INPUT;
    r.primitive_nodes = b.nodes.len();
    r.forwarding_gates = forwarding;
    r.logical_gates = logical;
    r.padding_gates = r.padded_gates.checked_sub(logical).ok_or(Error::Shape)?;
    r.dependency_depth = depth;
    r.node_capacity_bytes = b.nodes.capacity()*size_of::<Node>();
    r.map_peak_bytes = (b.last.capacity()+prior.capacity()+next.capacity()+live.capacity()+next_live.capacity())*size_of::<u32>()
        + buckets.iter().map(|x| x.capacity()*size_of::<u32>()).sum::<usize>()
        + buckets.capacity()*size_of::<Vec<u32>>() + histogram.capacity()*size_of::<usize>();
    r.compiler_peak_bytes = r.gate_capacity_bytes+r.node_capacity_bytes+r.map_peak_bytes+r.layer_header_bytes
        + b.residuals.capacity()*size_of::<u32>()+32768;
    if r.padded_gates != PRIMARY_GATES || r.forwarding_gates != 9646972
        || r.logical_gates != 10343101 || r.padding_gates != 4795715
        || r.layers != 1853 || r.max_width != 8192 || r.values_bytes != 484507648
        || r.phase_peak_bytes != 1310720 || r.proof_scalars != 174105 || r.challenges != 50021
        || r.compiler_peak_bytes > LOGICAL_LIMIT { return Err(Error::Shape); }
    // Nodes, maps, buckets and residual-ID vectors die here; Compiled owns only
    // compact layers, dimensions and scalar metadata. No compiler Fr existed.
    Ok(result)
}

fn finish(input_len: usize, layers: Vec<Vec<CompactGate>>, audit: Audit) -> Result<Compiled, Error> {
    abi()?;
    if !input_len.is_power_of_two() || input_len.trailing_zeros() > 24 || layers.is_empty() {
        return Err(Error::InputDimension);
    }
    let mut resources = Resources { used_input: input_len, input_width: input_len,
        layers: layers.len(), max_width: input_len, ..Resources::default() };
    let mut dimensions = Vec::with_capacity(layers.len());
    let mut previous = input_len;
    resources.values_bytes = input_len*size_of::<Fr>();
    for layer in &layers {
        if !layer.len().is_power_of_two() { return Err(Error::Shape); }
        for &g in layer { validate_raw(g, previous)?; }
        resources.padded_gates = resources.padded_gates.checked_add(layer.len()).ok_or(Error::Capacity)?;
        resources.gate_capacity_bytes += layer.capacity()*size_of::<CompactGate>();
        if resources.padded_gates > MAX_GATES { return Err(Error::Capacity); }
        let dimension = previous.trailing_zeros() as usize;
        dimensions.push(dimension);
        resources.proof_scalars += 7*dimension+3;
        resources.challenges += 2*dimension+1;
        resources.phase_peak_bytes = resources.phase_peak_bytes.max((layer.len()+4*previous)*size_of::<Fr>());
        resources.values_bytes += layer.len()*size_of::<Fr>();
        resources.max_width = resources.max_width.max(layer.len());
        previous = layer.len();
    }
    resources.challenges += previous.trailing_zeros() as usize;
    resources.proof_bytes = resources.proof_scalars*32;
    resources.layer_header_bytes = layers.capacity()*size_of::<Vec<CompactGate>>()
        + dimensions.capacity()*size_of::<usize>();
    if resources.gate_capacity_bytes+resources.values_bytes+resources.phase_peak_bytes
        + resources.proof_bytes+64*1024*1024 > LOGICAL_LIMIT { return Err(Error::Capacity); }
    Ok(Compiled { input_len, layers, dimensions, resources, audit })
}

/// Bounded unit fixtures only. This cannot admit a caller-supplied native shape.
pub(crate) fn tiny(input_len: usize, layers: Vec<Vec<CompactGate>>) -> Result<Compiled, Error> {
    if input_len > 2048 || layers.len() > 32
        || layers.iter().map(|x| x.capacity()).sum::<usize>() > 65536 { return Err(Error::Capacity); }
    finish(input_len, layers, Audit { graph_blake: [0;64], widths_blake: [0;64] })
}

impl Compiled {
    pub(crate) fn input_len(&self) -> usize { self.input_len }
    pub(crate) fn layers(&self) -> &[Vec<CompactGate>] { &self.layers }
    pub(crate) fn dimensions(&self) -> &[usize] { &self.dimensions }
    pub(crate) fn resources(&self) -> Resources { self.resources }
    pub(crate) fn audit(&self) -> Audit { self.audit }
    pub(crate) fn validate_candidate_gate(&self, layer: usize, index: usize, candidate: CompactGate) -> Result<(), Error> {
        let expected = self.layers.get(layer).and_then(|x| x.get(index)).ok_or(Error::Shape)?;
        if candidate != *expected { return Err(Error::Shape); }
        Ok(())
    }
    pub(crate) fn bind(&self, transcript: &mut Transcript) {
        transcript.append_bytes(b"gkr-profile", b"sparse-bilinear-lsb-zero-output-v1");
        gkr::append_usize(transcript, b"gkr-input-width", self.input_len);
        gkr::append_usize(transcript, b"gkr-layer-count", self.layers.len());
        let mut previous = self.input_len;
        for layer in &self.layers {
            gkr::append_usize(transcript, b"gkr-layer-width", layer.len());
            for &compact in layer {
                let gate = decode_gate(compact, previous).expect("immutable admitted gate");
                gkr::append_usize(transcript, b"gkr-left-wire", gate.left);
                gkr::append_usize(transcript, b"gkr-right-wire", gate.right);
                for (label, coefficient) in [(b"gkr-c0".as_slice(), gate.c0), (b"gkr-c1".as_slice(), gate.c1),
                    (b"gkr-c2".as_slice(), gate.c2), (b"gkr-c3".as_slice(), gate.c3)] {
                    transcript.append_scalar(label, &coefficient);
                }
            }
            previous = layer.len();
        }
    }
    pub(crate) fn evaluate<'a>(&'a self, input: &[Fr]) -> Result<Evaluation<'a>, Error> {
        if input.len() != self.input_len { return Err(Error::InputDimension); }
        let mut values: Vec<Vec<Fr>> = Vec::with_capacity(self.layers.len()+1);
        values.push(input.to_vec());
        for layer in &self.layers {
            let previous = values.last().ok_or(Error::Shape)?;
            let mut output = Vec::with_capacity(layer.len());
            for &compact in layer { output.push(decode_gate(compact, previous.len())?.evaluate(previous)); }
            values.push(output);
        }
        let resources = EvaluationResources {
            values_len_bytes: values.iter().map(|x| x.len()*size_of::<Fr>()).sum(),
            values_capacity_bytes: values.iter().map(|x| x.capacity()*size_of::<Fr>()).sum(),
            layer_headers_bytes: values.capacity()*size_of::<Vec<Fr>>(),
        };
        if resources.values_capacity_bytes+resources.layer_headers_bytes+self.resources.gate_capacity_bytes
            + self.resources.phase_peak_bytes+self.resources.proof_bytes+64*1024*1024 > LOGICAL_LIMIT {
            return Err(Error::Capacity);
        }
        Ok(Evaluation { circuit: self, values, resources })
    }
    fn wiring(&self, index: usize, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr;4], gkr::GkrError> {
        let layer = &self.layers[index];
        let previous = if index == 0 { self.input_len } else { self.layers[index-1].len() };
        if r.len() != layer.len().trailing_zeros() as usize
            || u.len() != previous.trailing_zeros() as usize || v.len() != u.len() {
            return Err(gkr::GkrError::PointDimension);
        }
        let weights = gkr::eq_weights(r);
        self.wiring_with_weights(index, &weights, u, v)
    }
    fn wiring_with_weights(&self, index: usize, weights: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr;4], gkr::GkrError> {
        let layer = &self.layers[index];
        let previous = if index == 0 { self.input_len } else { self.layers[index-1].len() };
        if weights.len() != layer.len() || u.len() != previous.trailing_zeros() as usize || v.len() != u.len() {
            return Err(gkr::GkrError::PointDimension);
        }
        let left = gkr::eq_weights(u);
        let right = gkr::eq_weights(v);
        let mut coefficients = [Fr::zero();4];
        for (&compact, weight) in layer.iter().zip(weights) {
            let g = decode_gate(compact, previous).expect("immutable admitted gate");
            let scale = *weight*left[g.left]*right[g.right];
            coefficients[0] += scale*g.c0;
            coefficients[1] += scale*g.c1;
            coefficients[2] += scale*g.c2;
            coefficients[3] += scale*g.c3;
        }
        Ok(coefficients)
    }
    pub(crate) fn prove(&self, input: &[Fr], transcript: &mut Transcript) -> Result<(gkr::GkrProof,gkr::InputClaim),Error> {
        let evaluated = self.evaluate(input)?;
        self.prove_evaluated(&evaluated, transcript)
    }
    pub(crate) fn prove_evaluated(&self, evaluated: &Evaluation<'_>, transcript: &mut Transcript) -> Result<(gkr::GkrProof,gkr::InputClaim),Error> {
        if !std::ptr::eq(self, evaluated.circuit) { return Err(Error::Shape); }
        if evaluated.values.last().ok_or(Error::Shape)?.iter().any(|x| !x.is_zero()) {
            return Err(Error::NonzeroOutput);
        }
        self.bind(transcript);
        let mut point = gkr::output_point(self.layers.last().ok_or(Error::Shape)?.len(), transcript);
        let mut claim = Fr::zero();
        let mut proof = gkr::GkrProof { layers: Vec::with_capacity(self.layers.len()) };
        for layer_index in (0..self.layers.len()).rev() {
            gkr::append_usize(transcript, b"gkr-layer-index", layer_index);
            let layer = &self.layers[layer_index];
            let previous = &evaluated.values[layer_index];
            let weights = gkr::eq_weights(&point);
            let mut a = vec![Fr::zero();previous.len()];
            let mut b = vec![Fr::zero();previous.len()];
            for (&compact, weight) in layer.iter().zip(&weights) {
                let g = decode_gate(compact, previous.len())?;
                a[g.left] += *weight*(g.c1+g.c3*previous[g.right]);
                b[g.left] += *weight*(g.c0+g.c2*previous[g.right]);
            }
            let mut rounds = Vec::new();
            let (u,left_value) = gkr::prove_phase(a,b,previous,&mut claim,&mut rounds,transcript)?;
            let left_weights = gkr::eq_weights(&u);
            let mut c = vec![Fr::zero();previous.len()];
            let mut d = vec![Fr::zero();previous.len()];
            for (&compact, weight) in layer.iter().zip(&weights) {
                let g = decode_gate(compact, previous.len())?;
                let weighted_left = *weight*left_weights[g.left];
                c[g.right] += weighted_left*(g.c2+g.c3*left_value);
                d[g.right] += weighted_left*(g.c0+g.c1*left_value);
            }
            let (v,right_value) = gkr::prove_phase(c,d,previous,&mut claim,&mut rounds,transcript)?;
            let coefficients = self.wiring_with_weights(layer_index,&weights,&u,&v)?;
            if coefficients[0]+coefficients[1]*left_value+coefficients[2]*right_value
                +coefficients[3]*left_value*right_value != claim {
                return Err(Error::Gkr(gkr::GkrError::TerminalExpression));
            }
            let line_coefficients = gkr::line_polynomial(previous,&u,&v);
            transcript.append_scalar(b"gkr-left-value",&left_value);
            transcript.append_scalar(b"gkr-right-value",&right_value);
            gkr::append_polynomial(transcript,b"gkr-line-polynomial",&line_coefficients);
            let merge = transcript.challenge_scalar(b"gkr-line-challenge");
            point = gkr::line_point(&u,&v,merge);
            claim = gkr::eval_polynomial(&line_coefficients,merge);
            proof.layers.push(gkr::LayerProof { rounds,left_value,right_value,line_coefficients });
        }
        Ok((proof,gkr::InputClaim { point,value:claim }))
    }
    pub(crate) fn verify(&self, proof: &gkr::GkrProof, transcript: &mut Transcript) -> Result<gkr::InputClaim,Error> {
        Ok(gkr::verify_with_wiring(&self.dimensions,self.layers.last().ok_or(Error::Shape)?.len(),proof,transcript,
            |tr| self.bind(tr), |i,r,u,v| self.wiring(i,r,u,v))?)
    }
}

pub(crate) fn native_layout() -> circuit::CompressionLayout {
    circuit::CompressionLayout {
        state: std::array::from_fn(|i| std::array::from_fn(|j| 1+64*i+j)),
        message: std::array::from_fn(|i| std::array::from_fn(|j| 513+64*i+j)),
        counter: std::array::from_fn(|j| 1537+j), final_flag: 1601,
        output: std::array::from_fn(|i| std::array::from_fn(|j| 63810+128*i+j)), used_input_len: 64770,
    }
}
pub(crate) fn native_reference(input: &circuit::CompressionInput) -> Result<circuit::CompressionAssignment,Error> {
    let reference = circuit::assign_compression(input,&native_layout(),65536).map_err(|_| Error::Oracle)?;
    if reference.input.len() != 65536 || reference.input.capacity() > 65536 { return Err(Error::Capacity); }
    Ok(reference)
}
pub(crate) fn input_from_compression(input: &circuit::CompressionInput) -> Vec<Fr> {
    let mut values = vec![Fr::zero();INPUT_WIDTH];
    for i in 0..8 { for j in 0..64 { values[1+64*i+j] = Fr::from((input.state[i]>>j)&1); } }
    for i in 0..128 { for j in 0..8 { values[513+8*i+j] = Fr::from(((input.block[i]>>j)&1) as u64); } }
    for j in 0..64 { values[1537+j] = Fr::from((input.counter>>j)&1); }
    values[1601] = Fr::from(input.final_flag as u64);
    values
}
pub(crate) fn subcube_point(point: &[Fr]) -> Result<Vec<Fr>,Error> {
    if point.len() != 11 { return Err(Error::PointDimension); }
    let mut result = Vec::with_capacity(18);
    result.extend_from_slice(point);
    result.resize(18,Fr::zero());
    Ok(result)
}
pub(crate) fn pcs_input18(input: &[Fr]) -> Result<Vec<Fr>,Error> {
    if input.len() != INPUT_WIDTH { return Err(Error::InputDimension); }
    let mut values = Vec::with_capacity(1<<18);
    values.extend_from_slice(input);
    values.resize(1<<18,Fr::zero());
    Ok(values)
}

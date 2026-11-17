//! Fixed-shape serializer/private-length BLAKE2b-256 join experiment.
//! Finite secp256k1 point membership remains absent from the serializer.
//! This module constructs residual circuits and witnesses, not a proof profile.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use std::ops::Range;
use crate::{circuit::{self, CompressionInput, CompressionLayout}, gkr::Gate,
    serializer, sparse::{Circuit, Term}};

pub const CORE_WIDTH: usize = 65536;
pub const CORE_COPIES: usize = 8;
pub const SERIALIZER_OFFSET: usize = 524288;
pub const SERIALIZER_WIDTH: usize = 131072;
pub const AUX_OFFSET: usize = 655360;
pub const GLOBAL_WIDTH: usize = 1048576;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BoundaryRows {
    pub auxiliary_boolean: Range<usize>,
    pub one_hot: Range<usize>,
    pub length: Range<usize>,
    pub last_block_range: Range<usize>,
    pub message_aliases: Range<usize>,
    pub message_padding: Range<usize>,
    pub initial_state: Range<usize>,
    pub state_links: Range<usize>,
    pub dummy_state: Range<usize>,
    pub counters: Range<usize>,
    pub flags: Range<usize>,
    pub digest: Range<usize>,
    pub global_padding: Range<usize>,
}

pub struct Joined {
    pub core: Circuit,
    pub serializer: serializer::Compiled,
    pub boundary: Circuit,
    pub input: Option<Vec<Fr>>,
    pub compression_layout: CompressionLayout,
    pub selectors: [usize; 5],
    pub remainder: [usize; 7],
    pub boundary_rows: BoundaryRows,
}

struct Rows { terms: Vec<Term>, rows: usize }
impl Rows {
    fn new() -> Self { Self { terms: Vec::new(), rows: 0 } }
    fn term(&mut self, left: usize, right: usize, c0: Fr, c1: Fr, c2: Fr, c3: Fr) {
        self.terms.push(Term { row: self.rows, gate: Gate { left, right, c0, c1, c2, c3 } });
    }
    fn linear(&mut self, index: usize, coefficient: Fr) {
        self.term(index, 0, Fr::zero(), coefficient, Fr::zero(), Fr::zero());
    }
    fn constant(&mut self, value: Fr) {
        self.term(0, 0, value, Fr::zero(), Fr::zero(), Fr::zero());
    }
    fn product(&mut self, a: usize, b: usize, coefficient: Fr) {
        self.term(a, b, Fr::zero(), Fr::zero(), Fr::zero(), coefficient);
    }
    fn end(&mut self) { self.rows += 1; }
    fn anchor(&mut self, index: usize, value: bool) {
        self.term(index, 0, -Fr::from(value as u64), Fr::one(), Fr::zero(), Fr::zero());
        self.end();
    }
    fn category(&mut self, source_span: &'static str, f: impl FnOnce(&mut Self)) -> Range<usize> {
        let first = self.rows;
        let first_term = self.terms.len();
        f(self);
        #[cfg(test)]
        crate::c425_span_census::append_source_span(source_span, first_term, self.terms.len());
        first..self.rows
    }
}

fn message_index(layout: &CompressionLayout, byte: usize, bit: usize) -> usize {
    (byte / 128) * CORE_WIDTH + layout.message[(byte % 128) / 8][(byte % 8) * 8 + bit]
}

fn boundary(layout: &CompressionLayout, serialized: &serializer::Layout,
            expected_digest: [u8; 32], selectors: &[usize; 5], remainder: &[usize; 7])
    -> (Circuit, BoundaryRows)
{
    let mut r = Rows::new(); let one = Fr::one(); let zero = Fr::zero();
    let initial = circuit::blake2b256_initial_state();
    let auxiliary_boolean = r.category("header_hash.boundary.auxiliary_boolean", |r| {
        for &index in selectors.iter().chain(remainder) {
            r.term(index, index, zero, -one, zero, one); r.end();
        }
    });
    let one_hot = r.category("header_hash.boundary.one_hot", |r| {
        r.constant(-one); for &f in selectors { r.linear(f, one); } r.end();
    });
    let length = r.category("header_hash.boundary.length", |r| {
        r.constant(-one);
        for (bit, &index) in serialized.length.iter().enumerate() {
            r.linear(SERIALIZER_OFFSET + index, Fr::from(1u64 << bit));
        }
        for (j, &f) in selectors.iter().enumerate() { r.linear(f, -Fr::from((128*j) as u64)); }
        for (bit, &d) in remainder.iter().enumerate() { r.linear(d, -Fr::from(1u64 << bit)); }
        r.end();
    });
    let last_block_range = r.category("header_hash.boundary.last_block_range", |r| {
        for &d in &remainder[1..] { r.product(selectors[4], d, one); r.end(); }
    });
    let message_aliases = r.category("header_hash.boundary.message_aliases", |r| {
        for byte in 0..514 { for bit in 0..8 {
            r.term(message_index(layout, byte, bit), SERIALIZER_OFFSET + serialized.bytes[byte][bit],
                   zero, one, -one, zero); r.end();
        }}
    });
    let message_padding = r.category("header_hash.boundary.message_padding", |r| {
        for byte in 514..1024 { for bit in 0..8 { r.anchor(message_index(layout, byte, bit), false); }}
    });
    let initial_state = r.category("header_hash.boundary.initial_state", |r| {
        for word in 0..8 { for bit in 0..64 {
            r.anchor(layout.state[word][bit], (initial[word] >> bit) & 1 != 0);
        }}
    });
    let state_links = r.category("header_hash.boundary.state_links", |r| {
        for copy in 1..5 { for word in 0..8 { for bit in 0..64 {
            let iv = Fr::from((initial[word] >> bit) & 1);
            r.constant(-iv); r.linear(copy * CORE_WIDTH + layout.state[word][bit], one);
            for &f in &selectors[copy..] {
                r.linear(f, iv);
                r.product(f, (copy-1)*CORE_WIDTH + layout.output[word][bit], -one);
            }
            r.end();
        }}}
    });
    let dummy_state = r.category("header_hash.boundary.dummy_state", |r| {
        for copy in 5..8 { for word in 0..8 { for bit in 0..64 {
            r.anchor(copy*CORE_WIDTH + layout.state[word][bit], (initial[word] >> bit) & 1 != 0);
        }}}
    });
    // Packed equality is injective here: a Boolean u64 is below the field order,
    // and the selector/length constraints bound the right side by 514.
    let counters = r.category("header_hash.boundary.counters", |r| {
        for copy in 0..8 {
            for (bit, &index) in layout.counter.iter().enumerate() {
                r.linear(copy*CORE_WIDTH + index, Fr::from(1u64 << bit));
            }
            if copy < 5 {
                for &f in &selectors[copy+1..] { r.linear(f, -Fr::from((128*(copy+1)) as u64)); }
                for (bit, &index) in serialized.length.iter().enumerate() {
                    r.product(selectors[copy], SERIALIZER_OFFSET + index, -Fr::from(1u64 << bit));
                }
            }
            r.end();
        }
    });
    let flags = r.category("header_hash.boundary.flags", |r| {
        for copy in 0..8 {
            r.constant(-one); r.linear(copy*CORE_WIDTH + layout.final_flag, one);
            if copy < 5 { for &f in &selectors[copy+1..] { r.linear(f, one); } }
            r.end();
        }
    });
    let digest = r.category("header_hash.boundary.digest", |r| {
        for byte in 0..32 { for bit in 0..8 {
            r.constant(-Fr::from(((expected_digest[byte] >> bit) & 1) as u64));
            for (copy, &f) in selectors.iter().enumerate() {
                r.product(f, copy*CORE_WIDTH + layout.output[byte/8][(byte%8)*8+bit], one);
            }
            r.end();
        }}
    });
    let global_padding = r.category("header_hash.boundary.global_padding", |r| {
        for index in AUX_OFFSET+12..GLOBAL_WIDTH { r.anchor(index, false); }
    });
    let rows = BoundaryRows { auxiliary_boolean, one_hot, length, last_block_range,
        message_aliases, message_padding, initial_state, state_links, dummy_state,
        counters, flags, digest, global_padding };
    (Circuit { input_len: GLOBAL_WIDTH, row_count: r.rows.next_power_of_two(), terms: r.terms }, rows)
}

/// Constraints that bind the serializer length to an explicit public length
/// and force every byte after that prefix to zero. The row/term shape is fixed
/// for all lengths; only public coefficients change. `first_row` must name a
/// reserved gap in the enclosing boundary relation.
pub fn canonical_length_padding_rows(
    serialized: &serializer::Layout,
    expected_length: usize,
    first_row: usize,
) -> Result<(Vec<Term>, Range<usize>), String> {
    if !(1..=514).contains(&expected_length) || serialized.length.len() != 10 || serialized.bytes.len() != 514 {
        return Err("canonical BLAKE length outside bounded serializer shape".into());
    }
    let row_count = 10 + 1 + 514 * 8;
    let end_row = first_row.checked_add(row_count).ok_or("canonical padding row overflow")?;
    if end_row > 1 << 19 {
        return Err("canonical padding rows exceed the existing boundary domain".into());
    }
    let zero = Fr::zero();
    let one = Fr::one();
    let mut terms = Vec::with_capacity(10 + 11 + 514 * 8);
    let mut row = first_row;
    for &wire in &serialized.length {
        let index = SERIALIZER_OFFSET + wire;
        terms.push(Term { row, gate: Gate { left: index, right: index,
            c0: zero, c1: -one, c2: zero, c3: one } });
        row += 1;
    }
    terms.push(Term { row, gate: Gate { left: 0, right: 0,
        c0: -Fr::from(expected_length as u64), c1: zero, c2: zero, c3: zero } });
    for (bit, &wire) in serialized.length.iter().enumerate() {
        terms.push(Term { row, gate: Gate { left: SERIALIZER_OFFSET + wire, right: 0,
            c0: zero, c1: Fr::from(1u64 << bit), c2: zero, c3: zero } });
    }
    row += 1;
    for (byte, bits) in serialized.bytes.iter().enumerate() {
        let is_padding = Fr::from((byte >= expected_length) as u64);
        for &wire in bits {
            terms.push(Term { row, gate: Gate { left: SERIALIZER_OFFSET + wire, right: 0,
                c0: zero, c1: is_padding, c2: zero, c3: zero } });
            row += 1;
        }
    }
    if row != end_row || terms.iter().any(|term| term.row < first_row || term.row >= end_row) {
        return Err("canonical padding row inventory changed".into());
    }
    Ok((terms, first_row..end_row))
}

fn word(input: &[Fr], indices: &[usize]) -> Result<u64, String> {
    let mut value = 0;
    for (bit, &index) in indices.iter().enumerate() {
        if input[index].is_one() { value |= 1u64 << bit; }
        else if !input[index].is_zero() { return Err("serializer assignment is non-Boolean".into()); }
    }
    Ok(value)
}

/// Public topology depends only on the expected digest, never on private fields
/// or their encoded length. Malformed fields are not certified by assignment;
/// acceptance requires all three residual circuits to vanish.
pub fn build(fields: Option<&serializer::Fields>, expected_digest: [u8; 32]) -> Result<Joined, String> {
    let core = circuit::build_compression(None)?;
    let serialized = serializer::build(None)?;
    if core.compiled.circuit.input_len != CORE_WIDTH || serialized.circuit.input_len != SERIALIZER_WIDTH {
        return Err("header hash component dimensions changed".into());
    }
    let selectors = std::array::from_fn(|i| AUX_OFFSET+i);
    let remainder = std::array::from_fn(|i| AUX_OFFSET+5+i);
    let (boundary, boundary_rows) = boundary(&core.layout, &serialized.layout, expected_digest, &selectors, &remainder);
    let input = fields.map(|fields| assign_from_template(&core.layout, &serialized, fields))
        .transpose()?;
    Ok(Joined { core: core.compiled.circuit, serializer: serialized, boundary, input,
        compression_layout: core.layout, selectors, remainder, boundary_rows })
}

/// Assign the same private hash program with the consumer's retained canonical
/// components. Acceptance still requires all serializer, core and boundary
/// relations; this helper supplies values and never changes their circuits.
pub(crate) fn assign_from_template(
    compression_layout: &CompressionLayout,
    serialized: &serializer::Compiled,
    fields: &serializer::Fields,
) -> Result<Vec<Fr>, String> {
    if serialized.circuit.input_len != SERIALIZER_WIDTH {
        return Err("header hash component dimensions changed".into());
    }
    let serializer_input = serialized.assign(fields);
    let length = word(&serializer_input, &serialized.layout.length)? as usize;
    if !(1..=514).contains(&length) { return Err("serializer length cannot be assigned to bounded hash".into()); }
    let mut bytes = [0u8; 514];
    for (byte, indices) in bytes.iter_mut().zip(&serialized.layout.bytes) {
        *byte = word(&serializer_input, indices)? as u8;
    }
    let last = (length-1)/128;
    let mut input = Vec::with_capacity(GLOBAL_WIDTH);
    let initial = circuit::blake2b256_initial_state(); let mut previous = initial;
    for copy in 0..CORE_COPIES {
        let mut block = [0u8; 128];
        let (state, counter, final_flag) = if copy <= last {
            let first = copy*128; let end = ((copy+1)*128).min(length);
            block[..end-first].copy_from_slice(&bytes[first..end]);
            (previous, end as u64, copy == last)
        } else { (initial, 0, true) };
        let compression_input = CompressionInput { state, block, counter, final_flag };
        let compression = circuit::assign_compression(
            &compression_input, compression_layout, CORE_WIDTH,
        )?;
        if &compression.layout != compression_layout || compression.input.len() != CORE_WIDTH {
            return Err("private compression topology differs".into());
        }
        previous = compression.output;
        input.extend(compression.input);
    }
    input.extend(serializer_input);
    input.resize(GLOBAL_WIDTH, Fr::zero());
    input[AUX_OFFSET+last] = Fr::one();
    let d = (length-1)%128;
    for bit in 0..7 { input[AUX_OFFSET+5+bit] = Fr::from(((d >> bit) & 1) as u64); }
    Ok(input)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ergo_header_core::{Header, PowSolution, GroupElement};

    fn fields(version: i8, payload_len: usize) -> serializer::Fields {
        let mut payload = [0; 255];
        for (i, b) in payload[..payload_len].iter_mut().enumerate() { *b = 0x80 | (i as u8 & 0x7f); }
        serializer::Fields { version, parent_id:[0x11;32], ad_proofs_root:[0x22;32],
            transactions_root:[0x33;32], state_root:[0x44;33], timestamp:0,
            extension_root:[0x55;32], n_bits:0x00800001, height:0, votes:[0x66,0x77,0x88],
            pk:[0;33], w:[0;33], nonce:[1,2,3,4,5,6,7,0x80], payload_len:payload_len as u8, payload }
    }
    fn native(f: &serializer::Fields) -> Vec<u8> {
        let pk = GroupElement::from_bytes(f.pk).unwrap();
        let pow = if f.version == 1 { PowSolution::V1 { pk, w:GroupElement::from_bytes(f.w).unwrap(),
            nonce:f.nonce, distance:f.payload[..f.payload_len as usize].to_vec() } }
            else { PowSolution::V2 { pk, nonce:f.nonce } };
        Header { version:f.version, parent_id:f.parent_id, ad_proofs_root:f.ad_proofs_root,
            transactions_root:f.transactions_root, state_root:f.state_root, timestamp:f.timestamp,
            extension_root:f.extension_root, n_bits:f.n_bits, height:f.height, votes:f.votes,
            unparsed_bytes:if f.version>4 {f.payload[..f.payload_len as usize].to_vec()}else{vec![]}, pow }.encode().unwrap()
    }
    fn from_header(h: &Header) -> serializer::Fields {
        let mut f = fields(h.version, 0);
        f.parent_id=h.parent_id; f.ad_proofs_root=h.ad_proofs_root; f.transactions_root=h.transactions_root;
        f.state_root=h.state_root; f.timestamp=h.timestamp; f.extension_root=h.extension_root;
        f.n_bits=h.n_bits; f.height=h.height; f.votes=h.votes;
        let payload = match &h.pow {
            PowSolution::V1 { pk, w, nonce, distance } => {f.pk=*pk.as_bytes(); f.w=*w.as_bytes(); f.nonce=*nonce; distance},
            PowSolution::V2 { pk, nonce } => {f.pk=*pk.as_bytes(); f.nonce=*nonce; &h.unparsed_bytes},
        };
        assert!(payload.len()<=255); f.payload_len=payload.len() as u8;
        f.payload[..payload.len()].copy_from_slice(payload); f
    }
    fn residuals(c: &Circuit, input: &[Fr]) -> Vec<Fr> {
        assert_eq!(input.len(), c.input_len);
        let mut out = vec![Fr::zero(); c.row_count];
        for term in &c.terms {out[term.row] += term.gate.evaluate(input);}
        out
    }
    fn valid_components(j: &Joined) {
        let input = j.input.as_ref().unwrap();
        assert!(input.iter().all(|x|x.is_zero()||x.is_one()));
        for copy in input[..SERIALIZER_OFFSET].chunks_exact(CORE_WIDTH) {
            assert!(residuals(&j.core, copy).iter().all(|x|x.is_zero()));
        }
        assert!(residuals(&j.serializer.circuit, &input[SERIALIZER_OFFSET..AUX_OFFSET]).iter().all(|x|x.is_zero()));
        assert!(residuals(&j.boundary, input).iter().all(|x|x.is_zero()));
    }
    // This helper tests an omission mutant of the BOUNDARY subrelation. It does
    // not claim that every raw wire mutation is a valid compression witness.
    fn boundary_fault(j: &Joined, input: &[Fr], omitted: Range<usize>) {
        let values = residuals(&j.boundary, input);
        assert!(values[omitted.clone()].iter().any(|x|!x.is_zero()));
        assert!(values.iter().enumerate().all(|(row,x)|omitted.contains(&row)||x.is_zero()),
            "mutation affects another boundary family");
        let accepted_without_family = j.boundary.terms.iter().filter(|t|!omitted.contains(&t.row))
            .fold(vec![Fr::zero(); j.boundary.row_count], |mut rows,t| {rows[t.row]+=t.gate.evaluate(input);rows});
        assert!(accepted_without_family.iter().all(|x|x.is_zero()));
    }

    struct RemovePackedFile(std::path::PathBuf);
    impl Drop for RemovePackedFile {
        fn drop(&mut self) { let _ = std::fs::remove_file(&self.0); }
    }

    #[test]
    fn native_positive_shapes_and_private_topology() {
        let digest = [0x41;32]; let public = build(None,digest).unwrap();
        assert!(public.input.is_none()); assert!(public.serializer.input.is_none());
        assert_eq!(public.core.input_len,CORE_WIDTH); assert_eq!(public.serializer.circuit.input_len,SERIALIZER_WIDTH);
        assert_eq!(public.boundary.input_len,GLOBAL_WIDTH);
        assert_eq!(public.boundary_rows.global_padding.end,405784);
        assert_eq!(public.boundary.row_count,1<<19);
        // Different signed-version branches and encoded lengths share all gates.
        for f in [fields(-1,0),fields(4,0),fields(1,0),fields(5,128)] {
            let private = build(Some(&f),digest).unwrap();
            assert_eq!(private.core,public.core); assert_eq!(private.serializer.circuit,public.serializer.circuit);
            assert_eq!(private.boundary,public.boundary); assert_eq!(private.boundary_rows,public.boundary_rows);
            let raw=native(&f); let correct=build(Some(&f),ergo_header_core::blake2b256(&raw)).unwrap();
            valid_components(&correct);
        }
    }

    #[test]
    fn native_block_boundaries_and_last_live_byte() {
        // Version 1's 246-byte minimal encoding can reach every next block edge.
        for target in [255usize,256,257,383,384,385,511,512,513,514] {
            let mut f=fields(1,0);
            if target>=511 {f.timestamp=-1;f.height=i32::MAX as u32;}
            let base=native(&f).len(); assert!(target>=base && target-base<=255);
            f=serializer::Fields {payload_len:(target-base) as u8,..f};
            for b in &mut f.payload[..f.payload_len as usize] {*b=0xa5;}
            let raw=native(&f); assert_eq!(raw.len(),target);
            let j=build(Some(&f),ergo_header_core::blake2b256(&raw)).unwrap(); valid_components(&j);
            let input=j.input.as_ref().unwrap(); let last=(target-1)/128;
            assert_eq!(input[j.selectors[last]],Fr::one());
            assert_eq!(word(&input[SERIALIZER_OFFSET..AUX_OFFSET],&j.serializer.layout.length).unwrap(),target as u64);
            if target==514 {assert_ne!(raw[513],0);assert_eq!(input[message_index(&j.compression_layout,513,0)],Fr::one());}
        }
    }

    #[test]
    fn retained_header_samples_and_wrong_digest() {
        let pack:serde_json::Value=serde_json::from_str(include_str!("../vendor/header-core/fixtures/governance-contiguous-header-packs-v1.json")).unwrap();
        for network in ["mainnet","testnet"] {
            let text=pack["networks"][network]["source_headers_hex"][0].as_str().unwrap();
            let raw:Vec<u8>=text.as_bytes().chunks_exact(2).map(|p|u8::from_str_radix(std::str::from_utf8(p).unwrap(),16).unwrap()).collect();
            let h=Header::decode(&raw,None).unwrap();let f=from_header(&h);
            assert_eq!(native(&f),raw);
            let mut j=build(Some(&f),ergo_header_core::blake2b256(&raw)).unwrap();valid_components(&j);
            // Digest constants alone change; witness assignment remains usable.
            let mut wrong=ergo_header_core::blake2b256(&raw);wrong[0]^=1;
            let (bad_boundary,_)=boundary(&j.compression_layout,&j.serializer.layout,wrong,&j.selectors,&j.remainder);
            j.boundary=bad_boundary;boundary_fault(&j,j.input.as_ref().unwrap(),j.boundary_rows.digest.clone());
        }
    }

    #[test]
    fn two_valid_component_witnesses_require_serializer_message_aliases() {
        let a=fields(4,0);let mut b=a.clone();b.parent_id[0]^=1;
        let mut j=build(Some(&b),ergo_header_core::blake2b256(&native(&b))).unwrap();valid_components(&j);
        let assigned=j.serializer.assign(&a);
        assert!(residuals(&j.serializer.circuit,&assigned).iter().all(|x|x.is_zero()));
        j.input.as_mut().unwrap()[SERIALIZER_OFFSET..AUX_OFFSET].copy_from_slice(&assigned);
        boundary_fault(&j,j.input.as_ref().unwrap(),j.boundary_rows.message_aliases.clone());
    }

    #[test]
    fn valid_cores_and_rebound_digest_still_require_upper_state_link() {
        let f=fields(4,0);let raw=native(&f);assert_eq!((raw.len()-1)/128,1);
        let mut j=build(Some(&f),ergo_header_core::blake2b256(&raw)).unwrap();
        let original=j.input.as_ref().unwrap();let l=&j.compression_layout;
        let last=&original[CORE_WIDTH..2*CORE_WIDTH];
        let mut state=std::array::from_fn(|i|word(last,&l.state[i]).unwrap());
        state[7]^=1u64<<63; // Beyond the 256 digest bits, inside the 512-bit chaining state.
        let mut block=[0u8;128];
        for (i,bytes) in block.chunks_exact_mut(8).enumerate() {
            bytes.copy_from_slice(&word(last,&l.message[i]).unwrap().to_le_bytes());
        }
        let fresh=circuit::build_compression(Some(&CompressionInput {state,block,
            counter:word(last,&l.counter).unwrap(),final_flag:true})).unwrap();
        assert_eq!(fresh.compiled.circuit,j.core);assert_eq!(fresh.layout,j.compression_layout);
        let out=fresh.output.unwrap();let mut digest=[0u8;32];
        for (bytes,value) in digest.chunks_exact_mut(8).zip(out) {bytes.copy_from_slice(&value.to_le_bytes());}
        j.input.as_mut().unwrap()[CORE_WIDTH..2*CORE_WIDTH].copy_from_slice(fresh.compiled.input.as_ref().unwrap());
        j.boundary=boundary(&j.compression_layout,&j.serializer.layout,digest,&j.selectors,&j.remainder).0;
        let input=j.input.as_ref().unwrap();
        for copy in input[..SERIALIZER_OFFSET].chunks_exact(CORE_WIDTH) {
            assert!(residuals(&j.core,copy).iter().all(|x|x.is_zero()));
        }
        assert!(residuals(&j.serializer.circuit,&input[SERIALIZER_OFFSET..AUX_OFFSET]).iter().all(|x|x.is_zero()));
        let failed:Vec<_>=residuals(&j.boundary,input).iter().enumerate()
            .filter_map(|(i,x)|(!x.is_zero()).then_some(i)).collect();
        assert_eq!(failed,vec![j.boundary_rows.state_links.start+511]);
        boundary_fault(&j,input,j.boundary_rows.state_links.clone());
    }

    #[test]
    fn boundary_single_faults_and_category_omission_mutants() {
        let f=fields(4,0);let j=build(Some(&f),ergo_header_core::blake2b256(&native(&f))).unwrap();
        let original=j.input.as_ref().unwrap();let l=&j.compression_layout;let r=&j.boundary_rows;
        let cases=[
            (message_index(l,514,0),r.message_padding.clone()),
            (message_index(l,1023,7),r.message_padding.clone()),
            (l.state[7][63],r.initial_state.clone()),
            (CORE_WIDTH+l.state[7][63],r.state_links.clone()),
            (4*CORE_WIDTH+l.state[7][63],r.state_links.clone()),
            (5*CORE_WIDTH+l.state[7][63],r.dummy_state.clone()),
            (7*CORE_WIDTH+l.state[0][0],r.dummy_state.clone()),
            (l.counter[63],r.counters.clone()),
            (7*CORE_WIDTH+l.counter[0],r.counters.clone()),
            (l.final_flag,r.flags.clone()),
            (7*CORE_WIDTH+l.final_flag,r.flags.clone()),
            (AUX_OFFSET+12,r.global_padding.clone()),
            (GLOBAL_WIDTH-1,r.global_padding.clone()),
        ];
        for (index,range) in cases {
            let mut changed=original.clone();changed[index]=Fr::one()-changed[index];
            boundary_fault(&j,&changed,range);
        }
        // The final live byte is constrained by the alias family, even at 513.
        let mut changed=original.clone();let index=message_index(l,513,7);
        changed[index]=Fr::one()-changed[index];boundary_fault(&j,&changed,r.message_aliases.clone());
    }

    #[test]
    fn auxiliary_length_subrelation_exactly_one_to_514() {
        let j=build(None,[0;32]).unwrap();let ranges=&j.boundary_rows;
        let mut input=vec![Fr::zero();GLOBAL_WIDTH];
        let mut check=|length:usize,flags:[Fr;5],ds:[Fr;7],skip:Option<&Range<usize>>| {
            for (bit,&index) in j.serializer.layout.length.iter().enumerate() {input[SERIALIZER_OFFSET+index]=Fr::from(((length>>bit)&1) as u64);}
            for (index,value) in j.selectors.iter().zip(flags) {input[*index]=value;}
            for (index,value) in j.remainder.iter().zip(ds) {input[*index]=value;}
            let mut out=vec![Fr::zero();ranges.last_block_range.end];
            for t in j.boundary.terms.iter().take_while(|t|t.row<ranges.last_block_range.end) {
                if !skip.is_some_and(|s|s.contains(&t.row)) {out[t.row]+=t.gate.evaluate(&input);}
            }
            out.iter().all(|v|v.is_zero())
        };
        for length in 1..=514 {let last=(length-1)/128;let d=(length-1)%128;
            let flags=std::array::from_fn(|i|Fr::from((i==last) as u64));
            let ds=std::array::from_fn(|i|Fr::from(((d>>i)&1) as u64));
            assert!(check(length,flags,ds,None));assert!(!check(length^1,flags,ds,None));
        }
        let zero=Fr::zero();let one=Fr::one();
        let flags=[one,zero,zero,zero,zero];let ds=[zero;7];
        assert!(!check(0,flags,ds,None));assert!(check(0,flags,ds,Some(&ranges.length)));
        assert!(!check(1,[zero;5],ds,None));assert!(check(1,[zero;5],ds,Some(&ranges.one_hot)));
        let mut high=[zero;5];high[4]=one;let mut ds=[zero;7];ds[1]=one;
        assert!(!check(515,high,ds,None));assert!(check(515,high,ds,Some(&ranges.last_block_range)));
        let mut fractional=[zero;5];fractional[0]=one-one/Fr::from(128u64);fractional[1]=one/Fr::from(128u64);
        assert!(!check(2,fractional,[zero;7],None));assert!(check(2,fractional,[zero;7],Some(&ranges.auxiliary_boolean)));
        let mut nonboolean_d=[zero;7];nonboolean_d[0]=Fr::from(2u64);
        assert!(!check(3,flags,nonboolean_d,None));assert!(check(3,flags,nonboolean_d,Some(&ranges.auxiliary_boolean)));
        for last in 0..5 {for d in 0..128 {
            let flags=std::array::from_fn(|i|Fr::from((i==last) as u64));
            let ds=std::array::from_fn(|i|Fr::from(((d>>i)&1) as u64));
            assert_eq!(check(128*last+1+d,flags,ds,None),128*last+1+d<=514);
        }}
    }

    #[test]
    fn finite_curve_membership_is_still_explicitly_absent() {
        let mut f=fields(4,0);f.pk[0]=2;
        assert!(GroupElement::from_bytes(f.pk).is_err()); // x=0 has no curve point.
        let serialized=serializer::build(Some(&f)).unwrap();
        let input=serialized.input.as_ref().unwrap();
        let length=word(input,&serialized.layout.length).unwrap() as usize;
        let raw:Vec<u8>=serialized.layout.bytes[..length].iter().map(|b|word(input,b).unwrap() as u8).collect();
        let j=build(Some(&f),ergo_header_core::blake2b256(&raw)).unwrap();
        valid_components(&j);
    }

    #[test]
    fn retained_header_hash_gkr_and_dory_open_global_slot_in_2pow24_commitment() {
        use crate::{packed::PackedFileWriter, transcript::Transcript};

        const LOG_N:usize=24;
        const GLOBAL_SLOT_COUNT:usize=16;
        const ACTIVE_SLOT:usize=1;
        let pack:serde_json::Value=serde_json::from_str(include_str!("../vendor/header-core/fixtures/governance-contiguous-header-packs-v1.json")).unwrap();
        let encoded=pack["networks"]["mainnet"]["source_headers_hex"][128].as_str().unwrap();
        let raw=encoded.as_bytes().chunks_exact(2).map(|pair|
            u8::from_str_radix(std::str::from_utf8(pair).unwrap(),16).unwrap()).collect::<Vec<_>>();
        let header=Header::decode(&raw,None).unwrap();
        assert_eq!(header.height,129);
        assert_eq!(header.encode().unwrap(),raw);
        assert_eq!(raw.len(),279);
        let fields=serializer::Fields::from_header(&header).unwrap();
        let digest=ergo_header_core::blake2b256(&raw);
        let mut joined=build(Some(&fields),digest).unwrap();
        let input=joined.input.take().unwrap();
        assert_eq!(input.len(),GLOBAL_WIDTH);
        assert!(input.iter().all(|value|value.is_zero()||value.is_one()));

        let serializer_input=&input[SERIALIZER_OFFSET..AUX_OFFSET];
        let serializer_assignment=joined.serializer.assign(&fields);
        assert_eq!(serializer_input,serializer_assignment.as_slice());
        let public_length=word(serializer_input,&joined.serializer.layout.length).unwrap() as usize;
        assert_eq!(public_length,raw.len());
        let serialized_bytes=joined.serializer.layout.bytes.iter()
            .map(|byte|word(serializer_input,byte).unwrap() as u8).collect::<Vec<_>>();
        assert_eq!(&serialized_bytes[..public_length],raw.as_slice());

        // Drop the broad padding anchors and add the explicit public-length and
        // zero-suffix rows used by the current streamed ten-slot candidate.
        let global_padding=joined.boundary_rows.global_padding.clone();
        let mut boundary_circuit=joined.boundary;
        boundary_circuit.terms.retain(|term|!global_padding.contains(&term.row));
        let (length_terms,length_rows)=canonical_length_padding_rows(
            &joined.serializer.layout,public_length,global_padding.end).unwrap();
        boundary_circuit.terms.extend(length_terms);
        assert_eq!(boundary_circuit.input_len,GLOBAL_WIDTH);
        assert_eq!(boundary_circuit.row_count,1<<19);
        assert_eq!(length_rows.len(),4_123);
        assert_eq!(boundary_circuit.terms.len(),30_890);

        // The public digest is an active boundary constraint, not prover advice.
        let mut wrong_digest=digest;
        wrong_digest[0]^=1;
        let (mut wrong_boundary,_)=boundary(&joined.compression_layout,
            &joined.serializer.layout,wrong_digest,&joined.selectors,&joined.remainder);
        wrong_boundary.terms.retain(|term|!global_padding.contains(&term.row));
        let (wrong_length_terms,_)=canonical_length_padding_rows(
            &joined.serializer.layout,public_length,global_padding.end).unwrap();
        wrong_boundary.terms.extend(wrong_length_terms);
        let mut wrong_transcript=Transcript::new(b"nipopow-v2-one-header-wrong-digest-falsifier-v1");
        assert_eq!(crate::sparse::prove(&wrong_boundary,&input,0,&mut wrong_transcript).unwrap_err(),
            crate::gkr::GkrError::NonzeroOutput,
            "a changed public digest must be rejected before a proof is produced");

        let packed_path=std::env::temp_dir().join(format!(
            "nipopow-v2-header-hash-k24-{}-{}.bits",std::process::id(),
            std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
        let mut writer=PackedFileWriter::create_new(&packed_path,LOG_N).unwrap();
        let packed_cleanup=RemovePackedFile(packed_path);
        let mut packed_bytes=vec![0u8;input.len()/8];
        for (index,value) in input.iter().enumerate(){
            if value.is_one(){packed_bytes[index/8]|=1u8<<(index%8);}
        }
        let empty_slot=vec![0u8;packed_bytes.len()];
        for slot in 0..GLOBAL_SLOT_COUNT{
            writer.write_bytes(if slot==ACTIVE_SLOT{&packed_bytes}else{&empty_slot}).unwrap();
        }
        let source=writer.finish().unwrap();
        drop(packed_bytes);
        drop(empty_slot);
        assert_eq!(source.input_len(),1usize<<LOG_N);

        let setup_started=std::time::Instant::now();
        let setup=crate::pcs::generate_setup(LOG_N).unwrap();
        let setup_ms=setup_started.elapsed().as_millis();
        let commitment_started=std::time::Instant::now();
        let committed=crate::packed::commit(&source,&setup).unwrap();
        let commitment_ms=commitment_started.elapsed().as_millis();
        let commitment_bytes=crate::pcs::encode_commitment(&committed.commitment).unwrap();
        let append_statement=|transcript:&mut Transcript,role:&[u8]|{
            transcript.append_bytes(b"diagnostic-profile",b"one-real-ergo-header-blake2b-gkr-dory-v1");
            transcript.append_bytes(b"claim-role",role);
            transcript.append_u64(b"header-slot",ACTIVE_SLOT as u64);
            transcript.append_u64(b"global-slot-count",GLOBAL_SLOT_COUNT as u64);
            transcript.append_u64(b"packed-input-log-n",LOG_N as u64);
            transcript.append_u64(b"header-length",public_length as u64);
            transcript.append_bytes(b"header-digest",&digest);
            transcript.append_bytes(b"pcs-setup-id",&setup.id);
            transcript.append_bytes(b"input-commitment",&commitment_bytes);
        };

        let mut core_prover=Transcript::new(b"nipopow-v2-one-header-blake-core-gkr-dory-v1");
        append_statement(&mut core_prover,b"eight-compression-core");
        let core_started=std::time::Instant::now();
        let (core_proof,core_claim)=crate::sparse::prove(
            &joined.core,&input[..SERIALIZER_OFFSET],3,&mut core_prover).unwrap();
        let core_gkr_ms=core_started.elapsed().as_millis();
        assert_eq!(core_claim.point.len(),19);
        let mut core_global_point=core_claim.point.clone();
        core_global_point.push(Fr::zero()); // The eight compression copies occupy the low half of the local slot.
        for bit in 0..4{core_global_point.push(Fr::from(((ACTIVE_SLOT>>bit)&1) as u64));}
        assert_eq!(core_global_point.len(),LOG_N);
        assert_eq!(source.evaluate(&core_global_point).unwrap(),core_claim.value);
        let mut wrong_core_slot=core_global_point.clone();
        wrong_core_slot[20]=Fr::zero();
        assert_eq!(source.evaluate(&wrong_core_slot).unwrap(),Fr::zero());
        assert_ne!(core_claim.value,Fr::zero(),"active core claim must distinguish the empty neighboring slot");
        let core_gkr_bytes=crate::gkr::encode_proof(&core_proof).unwrap();
        let decoded_core=crate::sparse::decode_proof(&joined.core,3,&core_gkr_bytes).unwrap();
        let core_open_started=std::time::Instant::now();
        let core_open=crate::packed::open(
            &committed,&source,&core_global_point,&setup,&mut core_prover).unwrap();
        let core_pcs_ms=core_open_started.elapsed().as_millis();
        let core_pcs_bytes=crate::pcs::encode_proof(&core_open).unwrap();
        let decoded_core_open=crate::pcs::decode_proof(&core_pcs_bytes,LOG_N).unwrap();
        let mut core_verifier=Transcript::new(b"nipopow-v2-one-header-blake-core-gkr-dory-v1");
        append_statement(&mut core_verifier,b"eight-compression-core");
        let core_verify_gkr_started=std::time::Instant::now();
        let checked_core=crate::sparse::verify(&joined.core,3,&decoded_core,&mut core_verifier).unwrap();
        let core_verify_gkr_ms=core_verify_gkr_started.elapsed().as_millis();
        assert_eq!(checked_core,core_claim);
        let core_verify_dory_started=std::time::Instant::now();
        crate::pcs::verify(committed.commitment,checked_core.value,&core_global_point,
            &decoded_core_open,&setup,&mut core_verifier).unwrap();
        let core_verify_dory_ms=core_verify_dory_started.elapsed().as_millis();
        let mut wrong_core_verifier=Transcript::new(b"nipopow-v2-one-header-blake-core-gkr-dory-v1");
        append_statement(&mut wrong_core_verifier,b"eight-compression-core");
        let checked_wrong_core=crate::sparse::verify(
            &joined.core,3,&decoded_core,&mut wrong_core_verifier).unwrap();
        assert_eq!(checked_wrong_core,core_claim);
        assert!(crate::pcs::verify(committed.commitment,checked_wrong_core.value,&wrong_core_slot,
            &decoded_core_open,&setup,&mut wrong_core_verifier).is_err(),
            "the valid slot-1 opening must fail when verified at slot 0");

        let mut boundary_prover=Transcript::new(b"nipopow-v2-one-header-blake-boundary-gkr-dory-v1");
        append_statement(&mut boundary_prover,b"serializer-length-chain-and-digest-boundary");
        let boundary_started=std::time::Instant::now();
        let (boundary_proof,boundary_claim)=crate::sparse::prove(
            &boundary_circuit,&input,0,&mut boundary_prover).unwrap();
        let boundary_gkr_ms=boundary_started.elapsed().as_millis();
        assert_eq!(boundary_claim.point.len(),20);
        let mut boundary_global_point=boundary_claim.point.clone();
        for bit in 0..4{boundary_global_point.push(Fr::from(((ACTIVE_SLOT>>bit)&1) as u64));}
        assert_eq!(boundary_global_point.len(),LOG_N);
        assert_eq!(source.evaluate(&boundary_global_point).unwrap(),boundary_claim.value);
        let mut wrong_boundary_slot=boundary_global_point.clone();
        wrong_boundary_slot[20]=Fr::zero();
        assert_eq!(source.evaluate(&wrong_boundary_slot).unwrap(),Fr::zero());
        assert_ne!(boundary_claim.value,Fr::zero(),"active boundary claim must distinguish the empty neighboring slot");
        let boundary_gkr_bytes=crate::gkr::encode_proof(&boundary_proof).unwrap();
        let decoded_boundary=crate::sparse::decode_proof(&boundary_circuit,0,&boundary_gkr_bytes).unwrap();
        let boundary_open_started=std::time::Instant::now();
        let boundary_open=crate::packed::open(
            &committed,&source,&boundary_global_point,&setup,&mut boundary_prover).unwrap();
        let boundary_pcs_ms=boundary_open_started.elapsed().as_millis();
        let boundary_pcs_bytes=crate::pcs::encode_proof(&boundary_open).unwrap();
        let decoded_boundary_open=crate::pcs::decode_proof(&boundary_pcs_bytes,LOG_N).unwrap();
        let mut boundary_verifier=Transcript::new(b"nipopow-v2-one-header-blake-boundary-gkr-dory-v1");
        append_statement(&mut boundary_verifier,b"serializer-length-chain-and-digest-boundary");
        let boundary_verify_gkr_started=std::time::Instant::now();
        let checked_boundary=crate::sparse::verify(
            &boundary_circuit,0,&decoded_boundary,&mut boundary_verifier).unwrap();
        let boundary_verify_gkr_ms=boundary_verify_gkr_started.elapsed().as_millis();
        assert_eq!(checked_boundary,boundary_claim);
        let boundary_verify_dory_started=std::time::Instant::now();
        crate::pcs::verify(committed.commitment,checked_boundary.value,&boundary_global_point,
            &decoded_boundary_open,&setup,&mut boundary_verifier).unwrap();
        let boundary_verify_dory_ms=boundary_verify_dory_started.elapsed().as_millis();

        // The batch statement is assembled only from GKR claims that this test
        // has already verified. Five additional Boolean points select cells in
        // the empty slot 0, so their MLE values are exactly zero.
        let mut batch_claims=Vec::with_capacity(crate::opening_batch::CLAIMS);
        batch_claims.push(crate::opening_batch::Claim{
            point:checked_core.point.iter().copied().chain([Fr::zero()])
                .chain((0..4).map(|bit|Fr::from(((ACTIVE_SLOT>>bit)&1) as u64))).collect(),
            value:checked_core.value,
        });
        batch_claims.push(crate::opening_batch::Claim{
            point:checked_boundary.point.iter().copied()
                .chain((0..4).map(|bit|Fr::from(((ACTIVE_SLOT>>bit)&1) as u64))).collect(),
            value:checked_boundary.value,
        });
        for bit in 0..(crate::opening_batch::CLAIMS-2) {
            let mut point=vec![Fr::zero();LOG_N];
            point[bit]=Fr::one();
            batch_claims.push(crate::opening_batch::Claim{point,value:Fr::zero()});
        }
        let claims:[crate::opening_batch::Claim;crate::opening_batch::CLAIMS]=
            batch_claims.try_into().unwrap();
        let mut corpus=b"nipopow-v2-one-header-k24-opening-batch-v1\0".to_vec();
        corpus.extend_from_slice(&digest);
        corpus.extend_from_slice(&(ACTIVE_SLOT as u64).to_le_bytes());
        corpus.extend_from_slice(&(GLOBAL_SLOT_COUNT as u64).to_le_bytes());
        corpus.extend_from_slice(b"core@slot1,boundary@slot1,slot0-mle-points-0..4");
        let batch_statement=crate::opening_batch::Statement{
            log_n:LOG_N,setup_id:setup.id,commitment:committed.commitment.clone(),
            corpus_id:Some(ergo_header_core::blake2b256(&corpus)),claims,
        };
        let batch_started=std::time::Instant::now();
        let (batch_proof,batch_metrics,batch_prover_transcript)=crate::opening_batch::prove(
            &source,&committed,&setup,&batch_statement).unwrap();
        let batch_packet=crate::opening_batch::encode_proof(&batch_proof,LOG_N).unwrap();
        let decoded_batch=crate::opening_batch::decode_proof(&batch_packet,LOG_N).unwrap();
        let batch_prove_ms=batch_started.elapsed().as_millis();
        let batch_verify_started=std::time::Instant::now();
        let batch_verifier_transcript=crate::opening_batch::verify(
            &batch_statement,&setup,&decoded_batch).unwrap();
        let batch_verify_ms=batch_verify_started.elapsed().as_millis();
        let ledger=|t:&Transcript|(t.challenges(),t.raw_queries(),t.bytes_absorbed());
        assert_eq!(ledger(&batch_prover_transcript),ledger(&batch_verifier_transcript),
            "batch prover and verifier transcript ledgers must match");
        let mut batch_prover_next=batch_prover_transcript.clone();
        let mut batch_verifier_next=batch_verifier_transcript.clone();
        assert_eq!(batch_prover_next.try_challenge_scalar(b"continuation").unwrap(),
            batch_verifier_next.try_challenge_scalar(b"continuation").unwrap(),
            "batch prover and verifier must derive the same next challenge");
        let mut wrong_slot_batch=batch_statement.clone();
        wrong_slot_batch.claims[0].point[20]=Fr::zero();
        let wrong_slot_batch_error=crate::opening_batch::verify(
            &wrong_slot_batch,&setup,&decoded_batch).err()
            .expect("core batch opening at empty slot 0 must reject");

        let proof_bytes=core_gkr_bytes.len()+core_pcs_bytes.len()+boundary_gkr_bytes.len()+boundary_pcs_bytes.len();
        println!("one-header global-slot BLAKE2b GKR+Dory: height={}, bytes={}, active_slot={}, global_slots={}, commitment_log_n={}, core_terms={}, core_copies=8, boundary_terms={}, setup_ms={}, commitment_ms={}, core_gkr_ms={}, core_dory_ms={}, core_verify_gkr_ms={}, core_verify_dory_ms={}, core_gkr_bytes={}, core_dory_bytes={}, boundary_gkr_ms={}, boundary_dory_ms={}, boundary_verify_gkr_ms={}, boundary_verify_dory_ms={}, boundary_gkr_bytes={}, boundary_dory_bytes={}, proof_bytes={}, wrong_slot_pcs=rejected, digest_mutation=rejected, result=pass",
            header.height,public_length,ACTIVE_SLOT,GLOBAL_SLOT_COUNT,LOG_N,joined.core.terms.len(),boundary_circuit.terms.len(),
            setup_ms,commitment_ms,core_gkr_ms,core_pcs_ms,core_verify_gkr_ms,core_verify_dory_ms,
            core_gkr_bytes.len(),core_pcs_bytes.len(),boundary_gkr_ms,boundary_pcs_ms,
            boundary_verify_gkr_ms,boundary_verify_dory_ms,boundary_gkr_bytes.len(),boundary_pcs_bytes.len(),proof_bytes);
        println!("one-header log24 seven-claim PCS batch: proof_bytes={}, prove_encode_decode_ms={}, verify_ms={}, projection_scans={}, transition_scans={}, projection_s={}, transition_s={}, pcs_s={}, transcript_match=true, wrong_slot_claim=rejected ({})",
            batch_packet.len(),batch_prove_ms,batch_verify_ms,batch_metrics.projection_scans,
            batch_metrics.transition_scans,batch_metrics.projection_seconds,batch_metrics.transition_seconds,
            batch_metrics.pcs_seconds,wrong_slot_batch_error);
        drop(source);
        drop(packed_cleanup);
    }

    #[test]
    fn ten_contiguous_mainnet_headers_use_three_global_log24_opening_batches() {
        use crate::{packed::PackedFileWriter, transcript::Transcript};

        const LOG_N:usize=24;
        const GLOBAL_SLOT_COUNT:usize=16;
        const FIRST_SLOT:usize=1;
        const FIRST_FIXTURE_INDEX:usize=128;
        const HEADER_COUNT:usize=10;

        struct RosterClaim {
            claim:crate::opening_batch::Claim,
            height:u32,
            slot:usize,
            role:&'static [u8],
            digest:[u8;32],
        }

        let pack:serde_json::Value=serde_json::from_str(
            include_str!("../vendor/header-core/fixtures/governance-contiguous-header-packs-v1.json"))
            .unwrap();
        let encoded_headers=&pack["networks"]["mainnet"]["source_headers_hex"];
        let mut raw_headers=Vec::with_capacity(HEADER_COUNT);
        for offset in 0..HEADER_COUNT {
            let encoded=encoded_headers[FIRST_FIXTURE_INDEX+offset].as_str().unwrap();
            let raw=encoded.as_bytes().chunks_exact(2).map(|pair|
                u8::from_str_radix(std::str::from_utf8(pair).unwrap(),16).unwrap()).collect::<Vec<_>>();
            let header=Header::decode(&raw,None).unwrap();
            assert_eq!(header.height,129+offset as u32);
            assert_eq!(header.encode().unwrap(),raw);
            assert_eq!(raw.len(),279);
            raw_headers.push(raw);
        }

        let packed_path=std::env::temp_dir().join(format!(
            "nipopow-v2-header-roster-k24-{}-{}.bits",std::process::id(),
            std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
        let mut writer=PackedFileWriter::create_new(&packed_path,LOG_N).unwrap();
        let packed_cleanup=RemovePackedFile(packed_path);
        let empty_slot=vec![0u8;GLOBAL_WIDTH/8];
        writer.write_bytes(&empty_slot).unwrap();
        let mut digests=Vec::with_capacity(HEADER_COUNT);
        for (offset,raw) in raw_headers.iter().enumerate() {
            let header=Header::decode(raw,None).unwrap();
            let fields=serializer::Fields::from_header(&header).unwrap();
            let digest=ergo_header_core::blake2b256(raw);
            let mut joined=build(Some(&fields),digest).unwrap();
            let input=joined.input.take().unwrap();
            assert_eq!(input.len(),GLOBAL_WIDTH);
            assert!(input.iter().all(|value|value.is_zero()||value.is_one()));
            let serializer_input=&input[SERIALIZER_OFFSET..AUX_OFFSET];
            assert_eq!(serializer_input,joined.serializer.assign(&fields).as_slice());
            let public_length=word(serializer_input,&joined.serializer.layout.length).unwrap() as usize;
            assert_eq!(public_length,raw.len());
            let serialized=joined.serializer.layout.bytes.iter()
                .map(|byte|word(serializer_input,byte).unwrap() as u8).collect::<Vec<_>>();
            assert_eq!(&serialized[..public_length],raw.as_slice());
            let mut packed_bytes=vec![0u8;input.len()/8];
            for (index,value) in input.iter().enumerate(){
                if value.is_one(){packed_bytes[index/8]|=1u8<<(index%8);}
            }
            writer.write_bytes(&packed_bytes).unwrap();
            digests.push(digest);
        }
        for _ in (FIRST_SLOT+HEADER_COUNT)..GLOBAL_SLOT_COUNT { writer.write_bytes(&empty_slot).unwrap(); }
        let source=writer.finish().unwrap();
        assert_eq!(source.input_len(),1usize<<LOG_N);

        let setup_started=std::time::Instant::now();
        let setup=crate::pcs::generate_setup(LOG_N).unwrap();
        let setup_ms=setup_started.elapsed().as_millis();
        let commitment_started=std::time::Instant::now();
        let committed=crate::packed::commit(&source,&setup).unwrap();
        let commitment_ms=commitment_started.elapsed().as_millis();
        let commitment_bytes=crate::pcs::encode_commitment(&committed.commitment).unwrap();
        let append_statement=|transcript:&mut Transcript,role:&[u8],height:u32,slot:usize,
                              raw_length:usize,digest:&[u8;32]|{
            transcript.append_bytes(b"diagnostic-profile",b"ten-contiguous-mainnet-header-roster-v1");
            transcript.append_bytes(b"claim-role",role);
            transcript.append_u64(b"header-height",height as u64);
            transcript.append_u64(b"header-slot",slot as u64);
            transcript.append_u64(b"global-slot-count",GLOBAL_SLOT_COUNT as u64);
            transcript.append_u64(b"packed-input-log-n",LOG_N as u64);
            transcript.append_u64(b"header-length",raw_length as u64);
            transcript.append_bytes(b"header-digest",digest);
            transcript.append_bytes(b"pcs-setup-id",&setup.id);
            transcript.append_bytes(b"input-commitment",&commitment_bytes);
        };

        let mut roster_claims=Vec::with_capacity(HEADER_COUNT*2);
        let mut gkr_proof_bytes=0usize;
        let mut gkr_prove_ms=0u128;
        let mut gkr_verify_ms=0u128;
        for (offset,raw) in raw_headers.iter().enumerate() {
            let slot=FIRST_SLOT+offset;
            let header=Header::decode(raw,None).unwrap();
            let fields=serializer::Fields::from_header(&header).unwrap();
            let digest=digests[offset];
            let mut joined=build(Some(&fields),digest).unwrap();
            let input=joined.input.take().unwrap();
            let serializer_input=&input[SERIALIZER_OFFSET..AUX_OFFSET];
            let public_length=word(serializer_input,&joined.serializer.layout.length).unwrap() as usize;

            let mut core_prover=Transcript::new(b"nipopow-v2-ten-header-core-gkr-v1");
            append_statement(&mut core_prover,b"eight-compression-core",header.height,slot,public_length,&digest);
            let started=std::time::Instant::now();
            let (core_proof,core_claim)=crate::sparse::prove(
                &joined.core,&input[..SERIALIZER_OFFSET],3,&mut core_prover).unwrap();
            gkr_prove_ms+=started.elapsed().as_millis();
            let core_bytes=crate::gkr::encode_proof(&core_proof).unwrap();
            gkr_proof_bytes+=core_bytes.len();
            let decoded_core=crate::sparse::decode_proof(&joined.core,3,&core_bytes).unwrap();
            let mut core_verifier=Transcript::new(b"nipopow-v2-ten-header-core-gkr-v1");
            append_statement(&mut core_verifier,b"eight-compression-core",header.height,slot,public_length,&digest);
            let started=std::time::Instant::now();
            let checked_core=crate::sparse::verify(&joined.core,3,&decoded_core,&mut core_verifier).unwrap();
            gkr_verify_ms+=started.elapsed().as_millis();
            assert_eq!(checked_core,core_claim);
            assert_eq!(checked_core.point.len(),19);
            let mut core_global_point=checked_core.point.clone();
            core_global_point.push(Fr::zero());
            for bit in 0..4{core_global_point.push(Fr::from(((slot>>bit)&1) as u64));}
            assert_eq!(core_global_point.len(),LOG_N);
            assert_eq!(source.evaluate(&core_global_point).unwrap(),checked_core.value);
            if offset==0 {
                let mut wrong_slot_point=core_global_point.clone();
                wrong_slot_point[20]=Fr::zero();
                assert_eq!(source.evaluate(&wrong_slot_point).unwrap(),Fr::zero());
                assert_ne!(checked_core.value,Fr::zero(),
                    "the active slot-1 core claim must distinguish empty slot 0");
            }
            roster_claims.push(RosterClaim{claim:crate::opening_batch::Claim{
                point:core_global_point,value:checked_core.value},height:header.height,slot,
                role:b"core",digest});

            let global_padding=joined.boundary_rows.global_padding.clone();
            let mut boundary_circuit=joined.boundary;
            boundary_circuit.terms.retain(|term|!global_padding.contains(&term.row));
            let (length_terms,length_rows)=canonical_length_padding_rows(
                &joined.serializer.layout,public_length,global_padding.end).unwrap();
            boundary_circuit.terms.extend(length_terms);
            assert_eq!(length_rows.len(),4_123);
            assert_eq!(boundary_circuit.terms.len(),30_890);
            let mut boundary_prover=Transcript::new(b"nipopow-v2-ten-header-boundary-gkr-v1");
            append_statement(&mut boundary_prover,b"serializer-length-chain-and-digest-boundary",
                header.height,slot,public_length,&digest);
            let started=std::time::Instant::now();
            let (boundary_proof,boundary_claim)=crate::sparse::prove(
                &boundary_circuit,&input,0,&mut boundary_prover).unwrap();
            gkr_prove_ms+=started.elapsed().as_millis();
            let boundary_bytes=crate::gkr::encode_proof(&boundary_proof).unwrap();
            gkr_proof_bytes+=boundary_bytes.len();
            let decoded_boundary=crate::sparse::decode_proof(&boundary_circuit,0,&boundary_bytes).unwrap();
            let mut boundary_verifier=Transcript::new(b"nipopow-v2-ten-header-boundary-gkr-v1");
            append_statement(&mut boundary_verifier,b"serializer-length-chain-and-digest-boundary",
                header.height,slot,public_length,&digest);
            let started=std::time::Instant::now();
            let checked_boundary=crate::sparse::verify(
                &boundary_circuit,0,&decoded_boundary,&mut boundary_verifier).unwrap();
            gkr_verify_ms+=started.elapsed().as_millis();
            assert_eq!(checked_boundary,boundary_claim);
            assert_eq!(checked_boundary.point.len(),20);
            let mut boundary_global_point=checked_boundary.point.clone();
            for bit in 0..4{boundary_global_point.push(Fr::from(((slot>>bit)&1) as u64));}
            assert_eq!(boundary_global_point.len(),LOG_N);
            assert_eq!(source.evaluate(&boundary_global_point).unwrap(),checked_boundary.value);
            roster_claims.push(RosterClaim{claim:crate::opening_batch::Claim{
                point:boundary_global_point,value:checked_boundary.value},height:header.height,slot,
                role:b"boundary",digest});
        }
        assert_eq!(roster_claims.len(),20);

        let mut batch_packet_sizes=Vec::with_capacity(3);
        let mut batch_metrics_projection=0.0f64;
        let mut batch_metrics_transition=0.0f64;
        let mut batch_metrics_pcs=0.0f64;
        let mut batch_metrics_projection_scans=0usize;
        let mut batch_metrics_transition_scans=0usize;
        let mut batch_prove_ms=0u128;
        let mut batch_verify_ms=0u128;
        let batch_transcript_match=true;
        for batch_index in 0..3 {
            let start=batch_index*crate::opening_batch::CLAIMS;
            let end=(start+crate::opening_batch::CLAIMS).min(roster_claims.len());
            let members=&roster_claims[start..end];
            let mut batch_claims=members.iter().map(|entry|entry.claim.clone()).collect::<Vec<_>>();
            let mut corpus=b"nipopow-v2-ten-header-roster-opening-batch-v1\0".to_vec();
            corpus.extend_from_slice(&(batch_index as u64).to_le_bytes());
            for entry in members {
                corpus.extend_from_slice(&entry.height.to_le_bytes());
                corpus.extend_from_slice(&(entry.slot as u64).to_le_bytes());
                corpus.extend_from_slice(entry.role);
                corpus.extend_from_slice(&entry.digest);
            }
            while batch_claims.len()<crate::opening_batch::CLAIMS {
                batch_claims.push(members.last().unwrap().claim.clone());
                corpus.extend_from_slice(b"pad-repeat-last-verified-claim");
            }
            let claims:[crate::opening_batch::Claim;crate::opening_batch::CLAIMS]=
                batch_claims.try_into().unwrap();
            let statement=crate::opening_batch::Statement{
                log_n:LOG_N,setup_id:setup.id,commitment:committed.commitment.clone(),
                corpus_id:Some(ergo_header_core::blake2b256(&corpus)),claims,
            };
            let started=std::time::Instant::now();
            let (proof,metrics,prover_transcript)=crate::opening_batch::prove(
                &source,&committed,&setup,&statement).unwrap();
            let packet=crate::opening_batch::encode_proof(&proof,LOG_N).unwrap();
            let decoded=crate::opening_batch::decode_proof(&packet,LOG_N).unwrap();
            batch_prove_ms+=started.elapsed().as_millis();
            batch_packet_sizes.push(packet.len());
            batch_metrics_projection+=metrics.projection_seconds;
            batch_metrics_transition+=metrics.transition_seconds;
            batch_metrics_pcs+=metrics.pcs_seconds;
            batch_metrics_projection_scans+=metrics.projection_scans;
            batch_metrics_transition_scans+=metrics.transition_scans;
            let started=std::time::Instant::now();
            let verifier_transcript=crate::opening_batch::verify(&statement,&setup,&decoded).unwrap();
            batch_verify_ms+=started.elapsed().as_millis();
            let ledger=|t:&Transcript|(t.challenges(),t.raw_queries(),t.bytes_absorbed());
            assert_eq!(ledger(&prover_transcript),ledger(&verifier_transcript));
            let mut prover_next=prover_transcript.clone();
            let mut verifier_next=verifier_transcript.clone();
            assert_eq!(prover_next.try_challenge_scalar(b"continuation").unwrap(),
                verifier_next.try_challenge_scalar(b"continuation").unwrap());

            if batch_index==0 {
                let mut wrong_slot=statement.clone();
                wrong_slot.claims[0].point[20]=Fr::zero();
                assert!(crate::opening_batch::verify(&wrong_slot,&setup,&decoded).is_err(),
                    "slot-1 core opening must reject at empty slot 0");
                let mut wrong_role=statement.clone();
                wrong_role.claims.swap(0,1);
                assert!(crate::opening_batch::verify(&wrong_role,&setup,&decoded).is_err(),
                    "swapping core and boundary roles must reject");
            }
        }
        let batch_bytes:usize=batch_packet_sizes.iter().sum();
        println!("ten-header log24 GKR+opening_batch: heights=129..138, active_slots=1..10, commitment_log_n={}, gkr_claims={}, batch_claims=21, gkr_bytes={}, batch_packet_sizes={:?}, batch_bytes={}, total_proof_bytes={}, setup_ms={}, commitment_ms={}, gkr_prove_ms={}, gkr_verify_ms={}, batch_prove_encode_decode_ms={}, batch_verify_ms={}, projection_scans={}, transition_scans={}, projection_s={}, transition_s={}, pcs_s={}, transcript_ledger_and_continuation_match={}, empty_slot_mutant=rejected, role_swap_mutant=rejected, result=pass",
            LOG_N,roster_claims.len(),gkr_proof_bytes,batch_packet_sizes,batch_bytes,
            gkr_proof_bytes+batch_bytes,setup_ms,commitment_ms,gkr_prove_ms,gkr_verify_ms,
            batch_prove_ms,batch_verify_ms,batch_metrics_projection_scans,batch_metrics_transition_scans,
            batch_metrics_projection,batch_metrics_transition,batch_metrics_pcs,batch_transcript_match);
        drop(source);
        drop(packed_cleanup);
    }
}

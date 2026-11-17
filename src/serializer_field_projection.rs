//! Bounded serializer projection for the fields consumed by the DAA join.
//!
//! This relation binds timestamp, compact difficulty, and height bits to the
//! corresponding canonical VLQ/fixed-width bytes in the serializer output.
//! It does not prove the rest of a header, its hash, proof of work, or point
//! membership.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use crate::{gkr::Gate, serializer, sparse::{Circuit, Term}};

const TIMESTAMP_START: usize = 130;
const NBITS_AFTER_TIMESTAMP: usize = 32;
const HEIGHT_AFTER_TIMESTAMP: usize = NBITS_AFTER_TIMESTAMP + 4;
const MAX_TIMESTAMP_BYTES: usize = 10;
const MAX_HEIGHT_BYTES: usize = 5;
const PROJECTED_BYTE_END: usize = TIMESTAMP_START + MAX_TIMESTAMP_BYTES
    + NBITS_AFTER_TIMESTAMP + 4 + MAX_HEIGHT_BYTES;

struct Builder {
    terms: Vec<Term>,
    or_recipes: Vec<(usize, usize, usize)>,
    rows: usize,
    next_wire: usize,
    input_len: usize,
}

impl Builder {
    fn new(input_len: usize, first_auxiliary: usize) -> Self {
        Self { terms: Vec::new(), or_recipes: Vec::new(), rows: 0,
            next_wire: first_auxiliary, input_len }
    }

    fn alloc(&mut self) -> Result<usize, String> {
        if self.next_wire >= self.input_len {
            return Err("field projection auxiliaries exceed the serializer slot".into());
        }
        let wire = self.next_wire;
        self.next_wire += 1;
        Ok(wire)
    }

    fn row(&mut self, gates: impl IntoIterator<Item=Gate>) {
        for gate in gates { self.terms.push(Term { row: self.rows, gate }); }
        self.rows += 1;
    }

    fn linear(wire: usize, coefficient: Fr, zero: usize) -> Gate {
        Gate { left: wire, right: zero, c0: Fr::zero(), c1: coefficient,
            c2: Fr::zero(), c3: Fr::zero() }
    }

    fn product(left: usize, right: usize, coefficient: Fr) -> Gate {
        Gate { left, right, c0: Fr::zero(), c1: Fr::zero(), c2: Fr::zero(), c3: coefficient }
    }

    fn require(&mut self, wire: usize, value: bool, zero: usize) {
        self.row([Gate { left: wire, right: zero, c0: -Fr::from(value as u64),
            c1: Fr::one(), c2: Fr::zero(), c3: Fr::zero() }]);
    }

    fn boolean(&mut self, wire: usize) {
        self.row([Gate { left: wire, right: wire, c0: Fr::zero(), c1: -Fr::one(),
            c2: Fr::zero(), c3: Fr::one() }]);
    }

    fn or(&mut self, left: usize, right: usize, zero: usize) -> Result<usize, String> {
        let out = self.alloc()?;
        let output = Self::linear(out, -Fr::one(), zero);
        self.row([
            Gate { left, right, c0: Fr::zero(), c1: Fr::one(), c2: Fr::one(), c3: -Fr::one() },
            output,
        ]);
        self.or_recipes.push((out, left, right));
        Ok(out)
    }

    fn equal(&mut self, left: usize, right: usize, zero: usize) {
        let a = Self::linear(left, Fr::one(), zero);
        let b = Self::linear(right, -Fr::one(), zero);
        self.row([a, b]);
    }

    fn gated_equal(&mut self, selector: usize, left: usize, right: usize) {
        self.row([Self::product(selector, left, Fr::one()),
            Self::product(selector, right, -Fr::one())]);
    }

    fn selected_bit(&mut self, selectors: &[usize], bytes: &[serializer::Byte],
        first_position: usize, bit: usize, zero: usize) -> Result<usize, String>
    {
        let selected = self.alloc()?;
        let mut gates = Vec::with_capacity(selectors.len()+1);
        gates.push(Self::linear(selected, -Fr::one(), zero));
        for (index,&selector) in selectors.iter().enumerate() {
            let position = first_position + index;
            let byte = bytes.get(position.checked_sub(TIMESTAMP_START)
                .ok_or("field projection byte precedes its local range")?)
                .ok_or("field projection byte exceeds its local range")?;
            gates.push(Self::product(selector, byte[bit], Fr::one()));
        }
        self.row(gates);
        Ok(selected)
    }
}

#[derive(Clone, Debug)]
struct ProjectionLayout {
    timestamp: [usize; 64],
    n_bits: [usize; 32],
    height: [usize; 32],
    bytes: Vec<serializer::Byte>,
    timestamp_active: [usize; MAX_TIMESTAMP_BYTES+1],
    timestamp_last: [usize; MAX_TIMESTAMP_BYTES],
    height_active: [usize; MAX_HEIGHT_BYTES+1],
    selected_n_bits: [[usize; 8]; 4],
    selected_height: [[usize; 8]; MAX_HEIGHT_BYTES],
}

pub(crate) struct Compiled {
    pub(crate) circuit: Circuit,
    pub(crate) residual_rows: usize,
    or_recipes: Vec<(usize, usize, usize)>,
    layout: ProjectionLayout,
}

impl Compiled {
    pub(crate) fn build(serializer: &serializer::Compiled) -> Result<Self, String> {
        let input_len = serializer.circuit.input_len;
        if input_len == 0 || serializer.stats.used_input_bits >= input_len {
            return Err("serializer input has no bounded projection workspace".into());
        }
        let source = &serializer.layout.fields;
        let byte_end = PROJECTED_BYTE_END;
        if byte_end > serializer.layout.bytes.len() {
            return Err("serializer output is too short for selected header fields".into());
        }
        let bytes = serializer.layout.bytes[TIMESTAMP_START..byte_end].to_vec();
        let zero = serializer.layout.zero;
        let one = serializer.layout.one;
        let mut b = Builder::new(input_len, serializer.stats.used_input_bits);

        b.require(zero, false, zero);
        b.require(one, true, zero);
        for &wire in source.timestamp.iter().chain(&source.n_bits).chain(&source.height) {
            b.boolean(wire);
        }
        b.require(source.height[31], false, zero);

        for byte in &bytes {
            for &wire in byte { b.boolean(wire); }
        }

        let mut timestamp_active = [zero; MAX_TIMESTAMP_BYTES+1];
        timestamp_active[0] = one;
        for group in (1..MAX_TIMESTAMP_BYTES).rev() {
            let start = 7*group;
            let mut iter = source.timestamp[start..].iter();
            let mut active = *iter.next().ok_or("empty timestamp VLQ suffix")?;
            for &wire in iter { active = b.or(active, wire, zero)?; }
            timestamp_active[group] = active;
        }
        timestamp_active[MAX_TIMESTAMP_BYTES] = zero;
        for &wire in &timestamp_active { b.boolean(wire); }

        let mut timestamp_last = [zero; MAX_TIMESTAMP_BYTES];
        for group in 0..MAX_TIMESTAMP_BYTES {
            let selector = b.alloc()?;
            let terms = [
                Builder::linear(selector, Fr::one(), zero),
                Builder::linear(timestamp_active[group], -Fr::one(), zero),
                Builder::linear(timestamp_active[group+1], Fr::one(), zero),
            ];
            b.row(terms);
            b.boolean(selector);
            timestamp_last[group] = selector;
        }
        let mut one_hot = vec![Builder::linear(one, -Fr::one(), zero)];
        one_hot.extend(timestamp_last.iter().map(|&wire|Builder::linear(wire,Fr::one(),zero)));
        b.row(one_hot);

        for group in 0..MAX_TIMESTAMP_BYTES {
            let byte = &bytes[group];
            for bit in 0..7 {
                let field_bit = source.timestamp.get(7*group+bit).copied().unwrap_or(zero);
                b.gated_equal(timestamp_active[group], byte[bit], field_bit);
            }
            b.gated_equal(timestamp_active[group], byte[7], timestamp_active[group+1]);
        }

        let mut selected_n_bits = [[zero; 8]; 4];
        for byte in 0..4 {
            for bit in 0..8 {
                let selected = b.selected_bit(&timestamp_last, &bytes,
                    TIMESTAMP_START+NBITS_AFTER_TIMESTAMP+1+byte, bit, zero)?;
                b.boolean(selected);
                b.equal(selected, source.n_bits[(3-byte)*8+bit], zero);
                selected_n_bits[byte][bit] = selected;
            }
        }

        let mut height_active = [zero; MAX_HEIGHT_BYTES+1];
        height_active[0] = one;
        for group in (1..MAX_HEIGHT_BYTES).rev() {
            let start = 7*group;
            let mut iter = source.height[start..31].iter();
            let mut active = *iter.next().ok_or("empty height VLQ suffix")?;
            for &wire in iter { active = b.or(active, wire, zero)?; }
            height_active[group] = active;
        }
        height_active[MAX_HEIGHT_BYTES] = zero;
        for &wire in &height_active { b.boolean(wire); }

        let mut selected_height = [[zero; 8]; MAX_HEIGHT_BYTES];
        for group in 0..MAX_HEIGHT_BYTES {
            for bit in 0..8 {
                let selected = b.selected_bit(&timestamp_last, &bytes,
                    TIMESTAMP_START+HEIGHT_AFTER_TIMESTAMP+1+group, bit, zero)?;
                b.boolean(selected);
                let expected = if bit == 7 {
                    height_active[group+1]
                } else {
                    source.height.get(7*group+bit).copied().unwrap_or(zero)
                };
                b.gated_equal(height_active[group], selected, expected);
                selected_height[group][bit] = selected;
            }
        }

        let residual_rows = b.rows;
        let row_count = residual_rows.checked_next_power_of_two()
            .ok_or("field projection row count overflow")?;
        if row_count > 1usize<<17 || b.terms.len() > 1usize<<20 {
            return Err("field projection exceeds the current local row or term cap".into());
        }
        Ok(Self {
            circuit: Circuit { input_len, row_count, terms: b.terms },
            residual_rows,
            or_recipes: b.or_recipes,
            layout: ProjectionLayout { timestamp: source.timestamp, n_bits: source.n_bits,
                height: source.height, bytes, timestamp_active, timestamp_last,
                height_active, selected_n_bits, selected_height },
        })
    }

    pub(crate) fn assign(&self, serializer_input: &[Fr]) -> Result<Vec<Fr>, String> {
        if serializer_input.len() != self.circuit.input_len {
            return Err("field projection input width mismatch".into());
        }
        let mut output = serializer_input.to_vec();
        for &(wire, left, right) in &self.or_recipes {
            output[wire] = output[left] + output[right] - output[left] * output[right];
        }
        let is_set = |wire: usize| serializer_input[wire].is_one();
        let mut timestamp_active = [false; MAX_TIMESTAMP_BYTES+1];
        timestamp_active[0] = true;
        for group in 1..MAX_TIMESTAMP_BYTES {
            timestamp_active[group] = self.layout.timestamp[7*group..]
                .iter().any(|&wire|is_set(wire));
        }
        let mut height_active = [false; MAX_HEIGHT_BYTES+1];
        height_active[0] = true;
        for group in 1..MAX_HEIGHT_BYTES {
            height_active[group] = self.layout.height[7*group..31]
                .iter().any(|&wire|is_set(wire));
        }
        for group in 0..=MAX_TIMESTAMP_BYTES {
            output[self.layout.timestamp_active[group]] = Fr::from(timestamp_active[group] as u64);
        }
        for group in 0..=MAX_HEIGHT_BYTES {
            output[self.layout.height_active[group]] = Fr::from(height_active[group] as u64);
        }
        let timestamp_last = std::array::from_fn::<_,MAX_TIMESTAMP_BYTES,_>(|group|
            timestamp_active[group] && !timestamp_active[group+1]);
        for group in 0..MAX_TIMESTAMP_BYTES {
            output[self.layout.timestamp_last[group]] = Fr::from(timestamp_last[group] as u64);
        }
        for byte in 0..4 {
            for bit in 0..8 {
                let value = timestamp_last.iter().enumerate().fold(Fr::zero(),|sum,(group,&active)|{
                    if active {sum+serializer_input[self.layout.bytes[NBITS_AFTER_TIMESTAMP+1+group+byte][bit]]}
                    else {sum}
                });
                output[self.layout.selected_n_bits[byte][bit]] = value;
            }
        }
        for group in 0..MAX_HEIGHT_BYTES {
            for bit in 0..8 {
                let value = timestamp_last.iter().enumerate().fold(Fr::zero(),|sum,(timestamp_group,&active)|{
                    if active {sum+serializer_input[self.layout.bytes[HEIGHT_AFTER_TIMESTAMP+1
                        +timestamp_group+group][bit]]} else {sum}
                });
                output[self.layout.selected_height[group][bit]] = value;
            }
        }
        Ok(output)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::{One, Zero};
    use ergo_header_core::Header;
    use serde_json::Value;

    fn hex_bytes(text:&str)->Vec<u8>{
        text.as_bytes().chunks_exact(2).map(|pair|
            u8::from_str_radix(std::str::from_utf8(pair).unwrap(),16).unwrap()).collect()
    }
    fn residuals(circuit:&Circuit,input:&[Fr])->Vec<Fr>{
        let mut rows=vec![Fr::zero();circuit.row_count];
        for term in &circuit.terms { rows[term.row]+=term.gate.evaluate(input); }
        rows
    }
    fn output_byte(serializer:&serializer::Compiled,input:&[Fr],position:usize)->u8{
        serializer.layout.bytes[position].iter().enumerate().fold(0u8,|value,(bit,&wire)|
            value|((input[wire].is_one() as u8)<<bit))
    }
    fn output_length(serializer:&serializer::Compiled,input:&[Fr])->usize{
        serializer.layout.length.iter().enumerate().map(|(bit,&wire)|
            (input[wire].is_one() as usize)<<bit).sum()
    }
    fn mainnet_header(height:usize)->(Header,Vec<u8>){
        let pack:Value=serde_json::from_str(include_str!("../vendor/header-core/fixtures/governance-contiguous-header-packs-v1.json")).unwrap();
        let encoded=pack["networks"]["mainnet"]["source_headers_hex"].as_array().unwrap();
        let raw=hex_bytes(encoded[height-1].as_str().unwrap());
        let header=Header::decode(&raw,None).unwrap();
        assert_eq!(header.height as usize,height);
        (header,raw)
    }
    fn valid_projection(projection:&Compiled,assignment:&[Fr])->Vec<Fr>{
        let projected=projection.assign(assignment).unwrap();
        assert!(residuals(&projection.circuit,&projected).iter().all(Zero::is_zero));
        projected
    }
    fn flip(input:&mut [Fr],wire:usize){
        input[wire]=if input[wire].is_zero(){Fr::one()}else{Fr::zero()};
    }
    fn rejects_mutation(projection:&Compiled,assignment:&[Fr],wire:usize,label:&str){
        let mut changed=assignment.to_vec();
        flip(&mut changed,wire);
        let projected=projection.assign(&changed).unwrap();
        assert!(residuals(&projection.circuit,&projected).iter().any(|x|!x.is_zero()),
            "field projection accepted isolated {label} mutation");
    }
    fn vlq_length(input:&[Fr],bits:&[usize])->usize{
        let width=bits.iter().rposition(|&wire|input[wire].is_one()).map_or(1,|bit|bit+1);
        (width+6)/7
    }

    #[test]
    fn selected_header_fields_match_serializer_bytes_and_reject_isolated_mutations(){
        let serializer=serializer::build(None).unwrap();
        let projection=Compiled::build(&serializer).unwrap();
        for height in [1usize,129,257,385,513,641,769,897,1025,1153]{
            let (header,raw)=mainnet_header(height);
            let fields=serializer::Fields::from_header(&header).unwrap();
            let assignment=serializer.assign(&fields);
            let projected=valid_projection(&projection,&assignment);
            assert_eq!(output_length(&serializer,&projected),raw.len());
            let encoded=(0..raw.len()).map(|position|output_byte(&serializer,&projected,position))
                .collect::<Vec<_>>();
            assert_eq!(encoded,raw,"serializer bytes differ from Mainnet header at height {height}");
        }

        let (header,_)=mainnet_header(1);
        let base_fields=serializer::Fields::from_header(&header).unwrap();
        for timestamp in [0i64,127,128,1i64<<56,-1] {
            for height in [0u32,127,128,0x7fff_ffff] {
                let mut fields=base_fields.clone();
                fields.timestamp=timestamp;
                fields.height=height;
                let assignment=serializer.assign(&fields);
                valid_projection(&projection,&assignment);
            }
        }

        let baseline=serializer.assign(&base_fields);
        let timestamp_length=vlq_length(&baseline,&projection.layout.timestamp);
        let n_bits_start=TIMESTAMP_START+NBITS_AFTER_TIMESTAMP+timestamp_length;
        let height_start=TIMESTAMP_START+HEIGHT_AFTER_TIMESTAMP+timestamp_length;
        rejects_mutation(&projection,&baseline,projection.layout.timestamp[0],"timestamp field bit");
        rejects_mutation(&projection,&baseline,projection.layout.n_bits[0],"nBits field bit");
        rejects_mutation(&projection,&baseline,projection.layout.height[0],"height field bit");
        rejects_mutation(&projection,&baseline,projection.layout.bytes[0][0],"timestamp output byte");
        rejects_mutation(&projection,&baseline,serializer.layout.bytes[n_bits_start][0],"nBits output byte");
        rejects_mutation(&projection,&baseline,serializer.layout.bytes[height_start][0],"height output byte");

        println!("serializer field projection: terms={}, rows={}, padded_rows={}, input_len={}, result=pass",
            projection.circuit.terms.len(),projection.residual_rows,projection.circuit.row_count,
            projection.circuit.input_len);
    }
}

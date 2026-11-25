//! Fixed-shape header byte-language experiment. Finite secp256k1 curve
//! membership is NOT checked here. This is not a canonical-header proof profile.
//! Every witness coordinate is Boolean, including byte-MUX outputs and padding.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use crate::{gkr::Gate, sparse::{Circuit, Term}};

pub type Byte = [usize; 8];

#[derive(Clone, Debug)]
pub struct Fields {
    pub version: i8,
    pub parent_id: [u8; 32],
    pub ad_proofs_root: [u8; 32],
    pub transactions_root: [u8; 32],
    pub state_root: [u8; 33],
    pub timestamp: i64,
    pub extension_root: [u8; 32],
    pub n_bits: u32,
    pub height: u32,
    pub votes: [u8; 3],
    pub pk: [u8; 33],
    pub w: [u8; 33],
    pub nonce: [u8; 8],
    pub payload_len: u8,
    pub payload: [u8; 255],
}

impl Fields {
    /// Maps one already-decoded Ergo header into the fixed serializer input.
    /// This does not validate proof of work, difficulty, or curve membership.
    pub fn from_header(header: &ergo_header_core::Header) -> Result<Self, String> {
        use ergo_header_core::PowSolution;
        let mut fields = Self {
            version: header.version,
            parent_id: header.parent_id,
            ad_proofs_root: header.ad_proofs_root,
            transactions_root: header.transactions_root,
            state_root: header.state_root,
            timestamp: header.timestamp,
            extension_root: header.extension_root,
            n_bits: header.n_bits,
            height: header.height,
            votes: header.votes,
            pk: [0; 33],
            w: [0; 33],
            nonce: [0; 8],
            payload_len: 0,
            payload: [0; 255],
        };
        let payload = match &header.pow {
            PowSolution::V1 { pk, w, nonce, distance } => {
                fields.pk = *pk.as_bytes();
                fields.w = *w.as_bytes();
                fields.nonce = *nonce;
                distance.as_slice()
            }
            PowSolution::V2 { pk, nonce } => {
                fields.pk = *pk.as_bytes();
                fields.nonce = *nonce;
                header.unparsed_bytes.as_slice()
            }
        };
        if payload.len() > fields.payload.len() {
            return Err("header proof payload exceeds fixed serializer cap".into());
        }
        fields.payload_len = payload.len() as u8;
        fields.payload[..payload.len()].copy_from_slice(payload);
        Ok(fields)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldLayout {
    pub version: Byte,
    pub parent_id: [Byte; 32],
    pub ad_proofs_root: [Byte; 32],
    pub transactions_root: [Byte; 32],
    pub state_root: [Byte; 33],
    pub timestamp: [usize; 64],
    pub extension_root: [Byte; 32],
    pub n_bits: [usize; 32],
    pub height: [usize; 32],
    pub votes: [Byte; 3],
    pub pk: [Byte; 33],
    pub w: [Byte; 33],
    pub nonce: [Byte; 8],
    pub payload_len: Byte,
    pub payload: [Byte; 255],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Layout {
    pub fields: FieldLayout,
    pub bytes: [Byte; 514],
    pub length: [usize; 10],
    pub v1: usize,
    pub extension: usize,
    pub extension_body: usize,
    pub zero: usize,
    pub one: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stats {
    pub source_bits: usize,
    pub used_input_bits: usize,
    pub padded_input_bits: usize,
    pub residual_rows: usize,
    pub padded_rows: usize,
    pub terms: usize,
    pub boolean_rows: usize,
    pub byte_muxes: usize,
}

#[derive(Clone, Debug)]
enum Recipe {
    Source(usize), Constant(bool), Not(usize), And(usize, usize),
    Or(usize, usize), Mux(usize, usize, usize),
    SumBit(usize, usize),
}

#[cfg(test)]
pub(crate) struct C334MuxTrace {
    pub(crate) base_7238: usize,
    pub(crate) arities_7238_to_7347: [u8; 110],
    pub(crate) end_7348: usize,
}

pub struct Compiled {
    pub circuit: Circuit,
    pub input: Option<Vec<Fr>>,
    pub layout: Layout,
    pub stats: Stats,
    recipes: Vec<Recipe>,
    sums: Vec<Vec<(usize, u64)>>,
    #[cfg(test)]
    pub(crate) c334_mux_trace: C334MuxTrace,
}

impl Fields {
    fn bits(&self) -> Vec<bool> {
        let mut out = Vec::with_capacity(4088);
        fn word(out: &mut Vec<bool>, n: u64, bits: usize) {
            out.extend((0..bits).map(|i| (n >> i) & 1 != 0));
        }
        fn bytes(out: &mut Vec<bool>, data: &[u8]) {
            for b in data { word(out, *b as u64, 8); }
        }
        word(&mut out, self.version as u8 as u64, 8);
        bytes(&mut out, &self.parent_id);
        bytes(&mut out, &self.ad_proofs_root);
        bytes(&mut out, &self.transactions_root);
        bytes(&mut out, &self.state_root);
        word(&mut out, self.timestamp as u64, 64);
        bytes(&mut out, &self.extension_root);
        word(&mut out, self.n_bits as u64, 32);
        word(&mut out, self.height as u64, 32);
        bytes(&mut out, &self.votes);
        bytes(&mut out, &self.pk);
        bytes(&mut out, &self.w);
        bytes(&mut out, &self.nonce);
        word(&mut out, self.payload_len as u64, 8);
        bytes(&mut out, &self.payload);
        assert_eq!(out.len(), 4088);
        out
    }
}

impl Compiled {
    /// Assigns auxiliaries without relying on semantic validation by the host.
    /// Malformed Fields produce an assignment with a nonzero residual.
    pub fn assign(&self, fields: &Fields) -> Vec<Fr> {
        let source = fields.bits();
        let mut bits = Vec::<bool>::with_capacity(self.circuit.input_len);
        for recipe in &self.recipes {
            let value = match *recipe {
                Recipe::Source(i) => source[i],
                Recipe::Constant(x) => x,
                Recipe::Not(a) => !bits[a],
                Recipe::And(a, b) => bits[a] && bits[b],
                Recipe::Or(a, b) => bits[a] || bits[b],
                Recipe::Mux(s, a, b) => if bits[s] { bits[b] } else { bits[a] },
                Recipe::SumBit(sum, bit) => {
                    let n: u64 = self.sums[sum].iter().map(|(i, w)| if bits[*i] { *w } else { 0 }).sum();
                    (n >> bit) & 1 != 0
                }
            };
            bits.push(value);
        }
        bits.resize(self.circuit.input_len, false);
        bits.into_iter().map(|b| Fr::from(b as u64)).collect()
    }
}

struct Builder {
    recipes: Vec<Recipe>, sums: Vec<Vec<(usize, u64)>>,
    terms: Vec<Term>, rows: usize, source: usize, muxes: usize,
    zero: usize, one: usize,
    #[cfg(test)]
    c334_emitted_terms: usize,
    #[cfg(test)]
    c334_base_7238: Option<usize>,
    #[cfg(test)]
    c334_arities_7238_to_7347: [u8; 110],
    #[cfg(test)]
    c334_recorded_rows: usize,
    #[cfg(test)]
    c334_end_7348: Option<usize>,
}

impl Builder {
    fn new() -> Self {
        let mut b = Self { recipes: vec![], sums: vec![], terms: vec![], rows: 0,
            source: 0, muxes: 0, zero: 0, one: 1,
            #[cfg(test)] c334_emitted_terms: 0,
            #[cfg(test)] c334_base_7238: None,
            #[cfg(test)] c334_arities_7238_to_7347: [0; 110],
            #[cfg(test)] c334_recorded_rows: 0,
            #[cfg(test)] c334_end_7348: None,
        };
        b.alloc(Recipe::Constant(false)); b.alloc(Recipe::Constant(true));
        b.require(0, false); b.require(1, true);
        b
    }
    fn alloc(&mut self, recipe: Recipe) -> usize {
        let i = self.recipes.len(); self.recipes.push(recipe); i
    }
    fn source_bit(&mut self) -> usize {
        let n = self.source; self.source += 1; self.alloc(Recipe::Source(n))
    }
    fn source_bits<const N: usize>(&mut self) -> [usize; N] {
        std::array::from_fn(|_| self.source_bit())
    }
    fn source_bytes<const N: usize>(&mut self) -> [Byte; N] {
        std::array::from_fn(|_| self.source_bits())
    }
    fn gate(&self, left: usize, right: usize, c0: Fr, c1: Fr, c2: Fr, c3: Fr) -> Gate {
        Gate { left, right, c0, c1, c2, c3 }
    }
    fn linear(&self, i: usize, coefficient: Fr) -> Gate {
        self.gate(i, self.zero, Fr::zero(), coefficient, Fr::zero(), Fr::zero())
    }
    fn row(&mut self, gates: impl IntoIterator<Item=Gate>) {
        #[cfg(test)]
        if self.rows == 7238 {
            assert!(self.c334_base_7238.replace(self.c334_emitted_terms).is_none());
        }
        #[cfg(test)]
        let mut c334_row_arity = 0usize;
        for gate in gates {
            self.terms.push(Term { row: self.rows, gate });
            #[cfg(test)]
            {
                self.c334_emitted_terms = self.c334_emitted_terms.checked_add(1)
                    .expect("C334 emitted-term counter overflow");
                c334_row_arity = c334_row_arity.checked_add(1)
                    .expect("C334 row-arity counter overflow");
            }
        }
        #[cfg(test)]
        if (7238..=7347).contains(&self.rows) {
            let index = self.rows - 7238;
            assert_eq!(index, self.c334_recorded_rows, "C334 MUX trace skipped a row");
            self.c334_arities_7238_to_7347[index] = u8::try_from(c334_row_arity)
                .expect("C334 MUX row arity exceeds u8");
            self.c334_recorded_rows += 1;
            if self.rows == 7347 {
                assert!(self.c334_end_7348.replace(self.c334_emitted_terms).is_none());
            }
        }
        self.rows += 1;
    }
    fn require(&mut self, i: usize, value: bool) {
        self.row([self.gate(i, self.zero, -Fr::from(value as u64), Fr::one(), Fr::zero(), Fr::zero())]);
    }
    fn not(&mut self, a: usize) -> usize {
        if a == self.zero { return self.one; } if a == self.one { return self.zero; }
        let z = self.alloc(Recipe::Not(a));
        self.row([self.gate(a,z,-Fr::one(),Fr::one(),Fr::one(),Fr::zero())]); z
    }
    fn and(&mut self, a: usize, b: usize) -> usize {
        if a == self.zero || b == self.zero { return self.zero; }
        if a == self.one { return b; } if b == self.one || a == b { return a; }
        let z = self.alloc(Recipe::And(a,b));
        self.row([self.gate(a,b,Fr::zero(),Fr::zero(),Fr::zero(),Fr::one()),self.linear(z,-Fr::one())]); z
    }
    fn or(&mut self, a: usize, b: usize) -> usize {
        if a == self.one || b == self.one { return self.one; }
        if a == self.zero { return b; } if b == self.zero || a == b { return a; }
        let z = self.alloc(Recipe::Or(a,b));
        self.row([self.gate(a,b,Fr::zero(),Fr::one(),Fr::one(),-Fr::one()),self.linear(z,-Fr::one())]); z
    }
    fn any(&mut self, bits: &[usize]) -> usize {
        bits.iter().fold(self.zero, |a,b| self.or(a,*b))
    }
    fn less_bits(&mut self, bits: &[usize], constant: &[bool]) -> usize {
        assert_eq!(bits.len(), constant.len());
        let mut less = self.zero;
        for (&x,&c) in bits.iter().zip(constant) {
            let nx = self.not(x);
            less = if c { self.or(nx,less) } else { self.and(nx,less) };
        }
        less
    }
    fn less(&mut self, bits: &[usize], constant: u64) -> usize {
        let c: Vec<_> = (0..bits.len()).map(|i| (constant >> i)&1 != 0).collect();
        self.less_bits(bits,&c)
    }
    fn sum_bits<const N: usize>(&mut self, items: Vec<(usize,u64)>) -> [usize;N] {
        let sum = self.sums.len(); self.sums.push(items.clone());
        let result = std::array::from_fn(|i| self.alloc(Recipe::SumBit(sum,i)));
        let mut gates = Vec::with_capacity(N+items.len());
        for (i,&wire) in result.iter().enumerate() { gates.push(self.linear(wire,Fr::from(1u64<<i))); }
        for (wire,w) in items { gates.push(self.linear(wire,-Fr::from(w))); }
        self.row(gates); result
    }
    fn zero_unless(&mut self, byte: Byte, active: usize) {
        let gates = (0..8).map(|i| {
            let w=Fr::from(1u64<<i);
            self.gate(byte[i],active,Fr::zero(),w,Fr::zero(),-w)
        }).collect::<Vec<_>>(); self.row(gates);
    }
    fn mux_byte(&mut self, s: usize, a: Byte, b: Byte) -> Byte {
        if a==b { return a; }
        if s==self.zero { return a; } if s==self.one { return b; }
        self.muxes += 1;
        let z = std::array::from_fn(|i| self.alloc(Recipe::Mux(s,a[i],b[i])));
        let mut gates=Vec::with_capacity(24);
        for i in 0..8 {
            let w=Fr::from(1u64<<i);
            gates.push(self.linear(z[i],w));
            gates.push(self.gate(a[i],s,Fr::zero(),-w,Fr::zero(),w));
            gates.push(self.gate(b[i],s,Fr::zero(),Fr::zero(),Fr::zero(),-w));
        }
        self.row(gates); z
    }
    // The caller has derived disjoint active positions. The packed equality
    // also rejects a non-disjoint OR assignment rather than discarding a carry.
    fn join_byte(&mut self, a: Byte, b: Byte) -> Byte {
        let zero=[self.zero;8]; if a==zero { return b; } if b==zero { return a; }
        let z=std::array::from_fn(|i| self.alloc(Recipe::Or(a[i],b[i])));
        let mut gates=Vec::with_capacity(24);
        for i in 0..8 {
            let w=Fr::from(1u64<<i);
            gates.extend([self.linear(z[i],w),self.linear(a[i],-w),self.linear(b[i],-w)]);
        }
        self.row(gates); z
    }
    fn shift(&mut self, mut bytes: Vec<Byte>, control: &[usize], capacity: usize) -> Vec<Byte> {
        bytes.resize(capacity,[self.zero;8]);
        for (bit,&s) in control.iter().enumerate() {
            let distance=1usize<<bit;
            assert!(distance<capacity);
            let keep=self.not(s);
            // Explicitly constrain dropped bytes. Capacity does not silently
            // discard a malicious nonzero suffix.
            for &byte in &bytes[capacity-distance..] { self.zero_unless(byte,keep); }
            bytes=(0..capacity).map(|j| {
                let moved=if j>=distance {bytes[j-distance]} else {[self.zero;8]};
                self.mux_byte(s,bytes[j],moved)
            }).collect();
        }
        bytes
    }
    fn vlq<const N: usize>(&mut self, bits: &[usize], count: usize) -> (Vec<Byte>,[usize;N]) {
        let mut active=vec![self.one];
        for i in 1..count { active.push(self.any(&bits[7*i..])); }
        let length=self.sum_bits(active.iter().map(|i|(*i,1)).collect());
        let bytes=(0..count).map(|group| std::array::from_fn(|bit| {
            if bit==7 { *active.get(group+1).unwrap_or(&self.zero) }
            else { *bits.get(7*group+bit).unwrap_or(&self.zero) }
        })).collect();
        (bytes,length)
    }
    fn point_format(&mut self, point: &[Byte;33]) {
        for &bit in &point[0][2..] { self.require(bit,false); }
        let finite=point[0][1];
        self.row([self.gate(point[0][0],finite,Fr::zero(),Fr::one(),Fr::zero(),-Fr::one())]);
        for &byte in &point[1..] { self.zero_unless(byte,finite); }
        let x: Vec<_>=point[1..].iter().rev().flat_map(|b| b.iter().copied()).collect();
        let mut q=[0xffu8;32]; q[27]=0xfe; q[30]=0xfc; q[31]=0x2f;
        let qb: Vec<_>=q.iter().rev().flat_map(|b|(0..8).map(move |i|(b>>i)&1!=0)).collect();
        let within=self.less_bits(&x,&qb); self.require(within,true);
        // No y witness or curve equation: finite membership remains pending.
    }
}

pub fn build(fields: Option<&Fields>) -> Result<Compiled,String> {
    let mut b=Builder::new();
    let f=FieldLayout {
        version:b.source_bits(), parent_id:b.source_bytes(), ad_proofs_root:b.source_bytes(),
        transactions_root:b.source_bytes(), state_root:b.source_bytes(), timestamp:b.source_bits(),
        extension_root:b.source_bytes(), n_bits:b.source_bits(), height:b.source_bits(),
        votes:b.source_bytes(), pk:b.source_bytes(), w:b.source_bytes(), nonce:b.source_bytes(),
        payload_len:b.source_bits(), payload:b.source_bytes(),
    };
    assert_eq!(b.source,4088);
    let zero=[b.zero;8];
    b.require(f.height[31],false);
    let mut v1=f.version[0];
    for &wire in &f.version[1..] { let n=b.not(wire); v1=b.and(v1,n); }
    let positive=b.not(f.version[7]);
    let at_least_two=b.any(&f.version[1..7]);
    let extension=b.and(positive,at_least_two);
    let low=b.or(f.version[0],f.version[1]);
    let five_to_seven=b.and(f.version[2],low);
    let high=b.any(&f.version[3..7]);
    let at_least_five=b.or(high,five_to_seven);
    let extension_body=b.and(positive,at_least_five);
    let payload_allowed=b.or(v1,extension_body);
    b.zero_unless(f.payload_len,payload_allowed);
    for (j,&byte) in f.payload.iter().enumerate() {
        let short=b.less(&f.payload_len,(j+1) as u64);
        let live=b.not(short); b.zero_unless(byte,live);
    }
    let nonempty=b.any(&f.payload_len);
    let distance_nonempty=b.and(v1,nonempty);
    let first_nonzero=b.any(&f.payload[0]);
    b.row([b.gate(distance_nonempty,first_nonzero,Fr::zero(),Fr::one(),Fr::zero(),-Fr::one())]);
    for &byte in &f.w { b.zero_unless(byte,v1); }
    b.point_format(&f.pk); b.point_format(&f.w);
    let (ts,tlen)=b.vlq::<4>(&f.timestamp,10);
    let (height,hlen)=b.vlq::<3>(&f.height[..31],5);

    let mut tail=vec![zero;330];
    tail[..33].copy_from_slice(&f.pk);
    for i in 0..33 { tail[33+i]=b.mux_byte(v1,if i<8 {f.nonce[i]} else {zero},f.w[i]); }
    for i in 0..8 { tail[66+i]=b.mux_byte(v1,zero,f.nonce[i]); }
    tail[74]=b.mux_byte(v1,zero,f.payload_len);
    for i in 0..255 { tail[75+i]=b.mux_byte(v1,zero,f.payload[i]); }
    let mut ext_items=vec![(extension,1)];
    for i in 0..8 { let x=b.and(extension,f.payload_len[i]); ext_items.push((x,1<<i)); }
    let ext_len=b.sum_bits::<9>(ext_items);
    let mut suffix=b.shift(tail,&ext_len,330);
    for i in 0..256 {
        let source=if i==0 {f.payload_len} else {f.payload[i-1]};
        let ext=b.mux_byte(extension,zero,source);
        suffix[i]=b.join_byte(suffix[i],ext);
    }
    let mut before_height=f.votes.to_vec(); before_height.extend(suffix);
    let mut after_height=b.shift(before_height,&hlen,338);
    for i in 0..5 { after_height[i]=b.join_byte(after_height[i],height[i]); }
    let mut before_ts=f.extension_root.to_vec();
    for byte in (0..4).rev() { before_ts.push(std::array::from_fn(|bit|f.n_bits[byte*8+bit])); }
    before_ts.extend(after_height);
    let mut after_ts=b.shift(before_ts,&tlen,384);
    for i in 0..10 { after_ts[i]=b.join_byte(after_ts[i],ts[i]); }
    let mut bytes=vec![f.version];
    bytes.extend(f.parent_id); bytes.extend(f.ad_proofs_root);
    bytes.extend(f.transactions_root); bytes.extend(f.state_root); bytes.extend(after_ts);
    let bytes:[Byte;514]=bytes.try_into().map_err(|_|"serializer capacity".to_string())?;
    let mut length_items=vec![(b.one,210),(v1,34),(extension,1)];
    for (i,&wire) in tlen.iter().enumerate() { length_items.push((wire,1<<i)); }
    for (i,&wire) in hlen.iter().enumerate() { length_items.push((wire,1<<i)); }
    for (i,&wire) in f.payload_len.iter().enumerate() { length_items.push((wire,1<<i)); }
    let length=b.sum_bits::<10>(length_items);
    let within=b.less(&length,515); b.require(within,true);
    for (j,&byte) in bytes.iter().enumerate() {
        let short=b.less(&length,(j+1) as u64); let live=b.not(short);
        b.zero_unless(byte,live);
    }
    let used=b.recipes.len();
    let input_len=used.next_power_of_two();
    for i in 0..used {
        #[cfg(test)]
        let serializer_term_ordinal=b.terms.len();
        b.row([b.gate(i,i,Fr::zero(),-Fr::one(),Fr::zero(),Fr::one())]);
        #[cfg(test)]
        crate::c425_span_census::record_serializer_family_term(
            serializer_term_ordinal,"serializer_boolean_diagonal",i);
    }
    for i in used..input_len {
        #[cfg(test)]
        let serializer_term_ordinal=b.terms.len();
        b.require(i,false);
        #[cfg(test)]
        crate::c425_span_census::record_serializer_family_term(
            serializer_term_ordinal,"serializer_input_padding",i-used);
    }
    let row_count=b.rows.next_power_of_two();
    if input_len>1<<24 || row_count>1<<24 || b.terms.len()>1<<20 {
        return Err("serializer exceeds bounded sparse limits".into());
    }
    let stats=Stats { source_bits:b.source,used_input_bits:used,padded_input_bits:input_len,
        residual_rows:b.rows,padded_rows:row_count,terms:b.terms.len(),boolean_rows:used,byte_muxes:b.muxes };
    #[cfg(test)]
    let c334_mux_trace = {
        if b.c334_recorded_rows != 110 || b.c334_emitted_terms != b.terms.len() {
            return Err("incomplete C334 MUX emission trace".into());
        }
        C334MuxTrace {
            base_7238: b.c334_base_7238.ok_or("missing C334 MUX trace base")?,
            arities_7238_to_7347: b.c334_arities_7238_to_7347,
            end_7348: b.c334_end_7348.ok_or("missing C334 MUX trace end")?,
        }
    };
    let layout=Layout {fields:f,bytes,length,v1,extension,extension_body,zero:b.zero,one:b.one};
    let mut compiled=Compiled { circuit:Circuit {input_len,row_count,terms:b.terms},input:None,
        layout,stats,recipes:b.recipes,sums:b.sums,
        #[cfg(test)] c334_mux_trace,
    };
    compiled.input=fields.map(|f|compiled.assign(f));
    Ok(compiled)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ergo_header_core::{Header,PowSolution};
    use std::io::{Cursor,Read};
    use std::time::Instant;

    fn sample(version:i8,len:usize)->Fields {
        let mut f=Fields {version,parent_id:[0x11;32],ad_proofs_root:[0x22;32],
            transactions_root:[0x33;32],state_root:[0x44;33],timestamp:0,extension_root:[0x55;32],
            n_bits:0x00800001,height:0,votes:[0x66,0x77,0x88],pk:[0;33],w:[0;33],nonce:[1,2,3,4,5,6,7,8],
            payload_len:len as u8,payload:[0;255]};
        for i in 0..len { f.payload[i]=0x80 | (i as u8 & 0x7f); } f
    }
    fn from_header(h:&Header)->Fields {
        Fields::from_header(h).expect("decoded header fits the fixed serializer payload")
    }
    fn native(f:&Fields)->Vec<u8> {
        use ergo_header_core::GroupElement;
        let pk=GroupElement::from_bytes(f.pk).unwrap();
        let pow=if f.version==1 {PowSolution::V1 {pk,w:GroupElement::from_bytes(f.w).unwrap(),nonce:f.nonce,
            distance:f.payload[..f.payload_len as usize].to_vec()}}
            else {PowSolution::V2 {pk,nonce:f.nonce}};
        Header {version:f.version,parent_id:f.parent_id,ad_proofs_root:f.ad_proofs_root,
            transactions_root:f.transactions_root,state_root:f.state_root,timestamp:f.timestamp,
            extension_root:f.extension_root,n_bits:f.n_bits,height:f.height,votes:f.votes,
            unparsed_bytes:if f.version>4 {f.payload[..f.payload_len as usize].to_vec()} else {vec![]},pow}.encode().unwrap()
    }
    fn value(input:&[Fr],bits:&[usize])->u64 {
        bits.iter().enumerate().map(|(i,w)|if input[*w]==Fr::one(){1u64<<i}else{0}).sum()
    }
    fn output(c:&Compiled,input:&[Fr])->(Vec<u8>,usize) {
        let bytes=c.layout.bytes.iter().map(|b|value(input,b) as u8).collect();
        (bytes,value(input,&c.layout.length) as usize)
    }
    fn residuals(c:&Compiled,input:&[Fr])->Vec<Fr> {
        let mut rows=vec![Fr::zero();c.circuit.row_count];
        for term in &c.circuit.terms { rows[term.row]+=term.gate.evaluate(input); } rows
    }
    fn valid(c:&Compiled,f:&Fields)->Vec<Fr> {
        let input=c.assign(f);
        assert!(input.iter().all(|x|x.is_zero()||x.is_one()));
        let bad=residuals(c,&input).iter().position(|x|!x.is_zero());
        assert_eq!(bad,None,"v={} payload={} timestamp={} height={}",f.version,f.payload_len,f.timestamp,f.height);
        let (bytes,len)=output(c,&input);assert_eq!(bytes[..len],native(f));
        assert!(bytes[len..].iter().all(|b|*b==0)); input
    }
    fn invalid(c:&Compiled,f:&Fields) {
        assert!(residuals(c,&c.assign(f)).iter().any(|x|!x.is_zero()));
    }
    fn hex(s:&str)->Vec<u8> {
        s.as_bytes().chunks_exact(2).map(|p|u8::from_str_radix(std::str::from_utf8(p).unwrap(),16).unwrap()).collect()
    }
    #[test]
    fn topology_constants_boolean_and_dimensions() {
        let start=Instant::now();let f=sample(1,255);let c=build(Some(&f)).unwrap();let public=build(None).unwrap();
        assert_eq!(c.circuit,public.circuit);assert_eq!(c.layout,public.layout);assert_eq!(c.stats,public.stats);
        assert_eq!(c.input.as_ref().unwrap(),&public.assign(&f));assert_eq!(c.stats.source_bits,4088);
        valid(&c,&f);
        eprintln!("serializer shape {:?}, elapsed {:?}",c.stats,start.elapsed());
    }
    #[test]
    fn signed_version_payload_and_vlq_boundaries() {
        let c=build(None).unwrap();
        for v in [i8::MIN,-1,0,1,2,3,4,5,127] {
            valid(&c,&sample(v,if v==1||v>4 {1}else{0}));
        }
        for len in [0,1,127,128,254,255] { for v in [1,5] { valid(&c,&sample(v,len)); } }
        for group in 1..=9 {
            let boundary=1u64<<(7*group);
            for n in [boundary-1,boundary] {let mut f=sample(4,0);f.timestamp=n as i64;valid(&c,&f);}
        }
        for group in 1..=4 {
            let boundary=1u32<<(7*group);
            for n in [boundary-1,boundary] {let mut f=sample(4,0);f.height=n;valid(&c,&f);}
        }
        for n in [0,i64::MIN,i64::MAX,-1] {let mut f=sample(4,0);f.timestamp=n;valid(&c,&f);}
        let mut max=sample(1,255);max.timestamp=-1;max.height=i32::MAX as u32;
        let input=valid(&c,&max);assert_eq!(value(&input,&c.layout.length),514);
        assert_ne!(output(&c,&input).0[513],0);
    }
    #[test]
    fn runtime_header_adapter_maps_v2_extension_and_rejects_oversize() {
        use ergo_header_core::GroupElement;
        let pk_bytes:[u8;33]=hex("0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798").try_into().unwrap();
        let pk=GroupElement::from_bytes(pk_bytes).unwrap();
        let mut header=Header {
            version:5,parent_id:[1;32],ad_proofs_root:[2;32],transactions_root:[3;32],state_root:[0;33],
            timestamp:128,extension_root:[4;32],n_bits:0x00800001,height:42,votes:[5,6,7],
            unparsed_bytes:vec![0x11,0x80,0xff],pow:PowSolution::V2 {pk,nonce:[8;8]},
        };
        let raw=header.encode().unwrap();
        let mut decoded=Header::decode(&raw,None).unwrap();
        assert_eq!(decoded,header);
        let fields=Fields::from_header(&decoded).unwrap();
        assert_eq!(fields.pk,pk_bytes);
        assert_eq!(fields.payload_len,3);
        assert_eq!(&fields.payload[..3],&[0x11,0x80,0xff]);
        assert!(fields.w.iter().all(|byte|*byte==0));
        assert_eq!(native(&fields),raw);
        valid(&build(None).unwrap(),&fields);

        decoded.unparsed_bytes=vec![0;256];
        assert!(Fields::from_header(&decoded).is_err());
    }
    #[test]
    fn semantic_negative_fields_and_explicit_pending_curve_membership() {
        let c=build(None).unwrap();
        let mut f=sample(4,0);f.height=1<<31;invalid(&c,&f);
        let mut f=sample(4,1);invalid(&c,&f);f.version=-1;invalid(&c,&f);
        let mut f=sample(5,1);f.payload[1]=1;invalid(&c,&f);
        let mut f=sample(1,1);f.payload[0]=0;invalid(&c,&f);
        let mut f=sample(4,0);f.w[0]=2;invalid(&c,&f);
        for role in [false,true] {
            let mut f=sample(1,0);if role {f.w[32]=1}else{f.pk[32]=1};invalid(&c,&f);
        }
        for role in [false,true] {for prefix in [1,4,5,6,7,255] {
            let mut f=sample(1,0);if role {f.w[0]=prefix}else{f.pk[0]=prefix};invalid(&c,&f);
        }}
        let mut q=[0xffu8;32];q[27]=0xfe;q[30]=0xfc;q[31]=0x2f;
        for coordinate in [q,[0xff;32]] {for role in [false,true] {
            let mut f=sample(1,0);let p=if role {&mut f.w}else{&mut f.pk};p[0]=2;p[1..].copy_from_slice(&coordinate);
            invalid(&c,&f);
        }}
        // x=0 has no secp256k1 square root of x^3+7. This experiment deliberately
        // accepts its format/range while the native membership oracle rejects.
        for role in [false,true] {
            let mut f=sample(1,0);if role {f.w[0]=2}else{f.pk[0]=2};
            let point=if role {f.w}else{f.pk};
            assert!(ergo_header_core::GroupElement::from_bytes(point).is_err());
            assert!(residuals(&c,&c.assign(&f)).iter().all(|x|x.is_zero()));
        }
    }
    #[test]
    fn isolated_wire_mutations_and_nonboolean_assignments_fail() {
        let c=build(None).unwrap();let f=sample(5,254);let input=valid(&c,&f);
        let mux=c.recipes.iter().position(|r|matches!(r,Recipe::Mux(..))).unwrap();
        let (_,len)=output(&c,&input);
        // Parent bytes are deliberately the same wires at their consumer and
        // serialization positions. Changing both is a valid different header;
        // later hash/public binding must anchor its identity.
        assert_eq!(c.layout.bytes[1..33],c.layout.fields.parent_id);
        let mut parent_changed=input.clone();
        let parent=c.layout.fields.parent_id[0][0];parent_changed[parent]=Fr::one()-parent_changed[parent];
        assert!(residuals(&c,&parent_changed).iter().all(|x|x.is_zero()));
        assert_ne!(output(&c,&parent_changed).0,output(&c,&input).0);
        let indices=[c.layout.zero,c.layout.one,c.layout.fields.timestamp[0],c.layout.v1,
            c.layout.extension,c.layout.extension_body,c.layout.length[0],mux,
            c.layout.bytes[len-1][0],c.layout.bytes[len][0],c.stats.used_input_bits];
        for i in indices {
            let mut changed=input.clone();changed[i]=Fr::one()-changed[i];
            assert!(residuals(&c,&changed).iter().any(|x|!x.is_zero()),"wire {i}");
        }
        let mut changed=input;changed[mux]=Fr::from(2u64);
        assert!(residuals(&c,&changed).iter().any(|x|!x.is_zero()));
    }
    #[test]
    fn all_signed_versions_and_finite_point_signs() {
        let c=build(None).unwrap();
        for byte in 0..=255u8 {
            let version=byte as i8;let f=sample(version,if version==1||version>4 {1}else{0});
            valid(&c,&f);
        }
        let x=hex("79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798");
        for role in [false,true] {for prefix in [2,3] {
            let mut f=sample(1,0);let point=if role {&mut f.w}else{&mut f.pk};
            point[0]=prefix;point[1..].copy_from_slice(&x);valid(&c,&f);
        }}
        // Exercise the live terminal nonce and distance bytes, including their
        // high bits, instead of relying only on zero-padded suffix fixtures.
        for (version,len) in [(4,0),(1,254),(1,255),(5,254),(5,255)] {
            let mut f=sample(version,len);f.nonce[7]=0x80;
            if len>0 {f.payload[len-1]=0xff;}
            let input=valid(&c,&f);let(bytes,length)=output(&c,&input);
            assert_ne!(bytes[length-1],0);
        }
    }
    #[test]
    fn retained_2306_headers_differential_with_measured_residual_batch() {
        let start=Instant::now();let c=build(None).unwrap();
        let pack:serde_json::Value=serde_json::from_str(include_str!("../vendor/header-core/fixtures/governance-contiguous-header-packs-v1.json")).unwrap();
        let mut fixtures=Vec::new();
        for network in ["mainnet","testnet"] {
            for raw in pack["networks"][network]["source_headers_hex"].as_array().unwrap() {
                let raw=hex(raw.as_str().unwrap());let h=Header::decode(&raw,None).unwrap();
                fixtures.push((raw,from_header(&h)));
            }
        }
        assert_eq!(fixtures.len(),2306);
        let batch=Instant::now();
        for (_,f) in fixtures.iter().take(8) {valid(&c,f);}
        let batch_seconds=batch.elapsed().as_secs_f64();
        eprintln!("serializer 8 full residuals: {batch_seconds:.3}s; projected 2306: {:.1}s",batch_seconds*2306.0/8.0);
        // No unbounded full-corpus field scan in the default focused tests.
        // All cases still generate the actual constrained assignment and compare
        // all output bytes/length; the full residual gate is explicitly separate.
        for (raw,f) in &fixtures {
            let input=c.assign(f);let(bytes,len)=output(&c,&input);
            assert_eq!(&bytes[..len],raw);assert!(bytes[len..].iter().all(|b|*b==0));
        }
        eprintln!("serializer 2306 assignment/native differentials elapsed {:?}",start.elapsed());
    }
    #[test]
    #[ignore = "run after measured focused batch; checks every retained residual"]
    fn retained_2306_full_residuals() {
        let c=build(None).unwrap();let start=Instant::now();
        let pack:serde_json::Value=serde_json::from_str(include_str!("../vendor/header-core/fixtures/governance-contiguous-header-packs-v1.json")).unwrap();
        let mut count=0;
        for network in ["mainnet","testnet"] {
            for raw in pack["networks"][network]["source_headers_hex"].as_array().unwrap() {
                let raw=hex(raw.as_str().unwrap());let h=Header::decode(&raw,None).unwrap();valid(&c,&from_header(&h));count+=1;
            }
        }
        assert_eq!(count,2306);eprintln!("serializer 2306 full residuals elapsed {:?}",start.elapsed());
    }
    #[test]
    #[ignore = "requires an export produced by the ErgoHistory Scala test"]
    fn ergo_history_export_satisfies_the_native_header_serializer() {
        use std::{env,fs};
        let path=env::var_os("NIPOPOW_V2_HEADER_EXPORT_PATH").expect("set Scala header export path");
        let bytes=fs::read(path).expect("read ErgoHistory header export");
        let mut input=Cursor::new(bytes.as_slice());let mut magic=[0u8;4];
        input.read_exact(&mut magic).expect("stream magic");assert_eq!(&magic,b"NPH2");
        let mut count_bytes=[0u8;4];input.read_exact(&mut count_bytes).expect("header count");
        let count=u32::from_be_bytes(count_bytes) as usize;assert!((1..=16).contains(&count));
        let c=build(None).unwrap();let mut prior:Option<Header>=None;
        for _ in 0..count {
            input.read_exact(&mut count_bytes).expect("header length");
            let len=u32::from_be_bytes(count_bytes) as usize;assert!((1..=514).contains(&len));
            let mut raw=vec![0u8;len];input.read_exact(&mut raw).expect("complete canonical header");
            let header=Header::decode(&raw,None).expect("decode Ergo header");
            if let Some(parent)=prior.as_ref() {
                assert_eq!(header.parent_id,parent.id().expect("parent ID hashes"));
                assert_eq!(header.height,parent.height+1);
            }
            let assignment=valid(&c,&from_header(&header));
            let (encoded,encoded_len)=output(&c,&assignment);
            assert_eq!(&encoded[..encoded_len],raw.as_slice());
            assert!(encoded[encoded_len..].iter().all(|byte|*byte==0));
            prior=Some(header);
        }
        assert_eq!(input.position() as usize,bytes.len(),"no unparsed trailing bytes");
    }
}

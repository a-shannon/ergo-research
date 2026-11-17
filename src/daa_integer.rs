//! Boolean, 16-bit-column lowering of the first Mainnet DAA arithmetic join.
//! The sparse circuit is fixed by `Epoch` and `Q`, never by private input values.
use ark_bn254::Fr;
use ark_ff::{One, PrimeField, Zero};
use ark_serialize::CanonicalSerialize;
use blake2::{digest::{Update,VariableOutput},Blake2bVar};
use num_bigint::BigUint;
use crate::{gkr::Gate,sparse::{Circuit,Term}};

pub const LIMB_BITS:usize=16;
pub const DENOM_BITS:usize=64;
pub const DIFFICULTY_BITS:usize=256;
pub const MAX_MATERIAL_TERMS:usize=1<<20;

// Both sides of each signed column residual fit below these integer bounds.
// This makes the Fr equality injective over the allowed Boolean assignments.
fn column_bound_bits()->(usize,usize){
    let limb=(1u128<<16)-1;
    let numerator_carry=(1u128<<27)-1;
    let numerator_abs=((1u128<<27)-1)*limb+numerator_carry+limb+(numerator_carry<<16);
    let product_carry=(1u128<<19)-1;
    let product_abs=4*limb*limb+product_carry+2*limb+(product_carry<<16);
    assert!(numerator_abs<1u128<<44 && product_abs<1u128<<36);
    assert!(Fr::MODULUS_BIT_SIZE>44);
    (44,36)
}

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub enum Epoch{Legacy,Eip}
impl Epoch{
    pub fn length(self)->u64{match self{Self::Legacy=>1024,Self::Eip=>128}}
    pub fn multiplier(self)->u64{120_000*self.length()}
    pub fn numerator_bits(self)->usize{match self{Self::Legacy=>283,Self::Eip=>280}}
}
#[derive(Clone,Copy,Debug)]
pub struct Inputs{pub nbits:u32,pub start_timestamp:i64,pub end_timestamp:i64}
#[derive(Clone,Copy,Debug)]
pub struct WindowInputs{pub nbits:[u32;8],pub timestamps:[i64;9]}
#[derive(Clone,Copy,Debug)]
pub struct TwoRatioInputs{pub nbits:[u32;2],pub timestamps:[i64;3]}

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) enum ShortLegacyProfile{M3,M4,M5,M6,M7}
impl ShortLegacyProfile{
    pub(crate) fn count(self)->usize{match self{Self::M3=>3,Self::M4=>4,Self::M5=>5,Self::M6=>6,Self::M7=>7}}
}
#[derive(Clone,Debug)]
pub(crate) struct ShortLegacyInputs{
    pub profile:ShortLegacyProfile,pub nbits:Vec<u32>,pub timestamps:Vec<i64>,
}

/// All externally authenticated fields have typed bit maps for later aliases.
#[derive(Clone,Debug)]
pub struct ExternalBits{
    pub nbits:[usize;32],pub start_timestamp:[usize;64],pub end_timestamp:[usize;64],
}
#[derive(Clone,Debug)]
pub struct OutputBits{
    pub decoded_difficulty:Vec<usize>,pub wrapped_delta:Vec<usize>,
    pub denominator_magnitude:Vec<usize>,pub numerator:Vec<usize>,
    pub quotient_magnitude:Vec<usize>,pub quotient_negative:usize,
    pub remainder_magnitude:Vec<usize>,pub remainder_negative:usize,
}
#[derive(Clone,Debug)]
pub struct Count{
    pub live_bits:usize,pub input_bits:usize,pub padded_input_bits:usize,
    pub residual_rows:usize,pub padded_rows:usize,pub terms:usize,
    pub boolean_rows:usize,pub linear_rows:usize,pub bilinear_rows:usize,
    pub maximum_column_signed_abs_bits:usize,pub maximum_degree:usize,
    pub source_nbits_bits:usize,pub source_timestamp_bits:usize,
    pub decoded_bits:usize,pub wrapped_delta_bits:usize,pub denominator_bits:usize,
    pub numerator_bits:usize,pub quotient_bits:usize,pub remainder_bits:usize,
    pub quotient_sign_bits:usize,pub remainder_sign_bits:usize,pub auxiliary_bits:usize,pub padding_bits:usize,
    pub witness_capacity:usize,pub retained_terms_capacity:usize,
    pub peak_row_terms:usize,pub peak_row_capacity_terms:usize,
    pub topology_blake2b256:[u8;32],
}
pub struct Compiled{
    pub count:Count,pub external:ExternalBits,pub output:OutputBits,
    pub circuit:Option<Circuit>,pub witness:Vec<Fr>,pub subtract_traces:Vec<SubtractTrace>,pub carry_wires:Vec<usize>,
}
pub struct CompiledWindow{
    pub count:Count,pub external:Vec<ExternalBits>,pub output:Vec<OutputBits>,
    pub circuit:Option<Circuit>,pub witness:Vec<Fr>,pub subtract_traces:Vec<SubtractTrace>,pub carry_wires:Vec<usize>,
}
#[derive(Clone,Debug)]
pub struct SubtractTrace{
    pub initial_borrow:usize,pub differences:Vec<usize>,pub borrows:Vec<usize>,
    pub minuend_constant:Option<BigUint>,pub minuend_wires:Vec<usize>,pub subtrahend_wires:Vec<usize>,
}
#[derive(Clone,Copy)]
struct Categories{nbits:usize,timestamps:usize,instances:usize,numerator_width:usize}

pub(crate) struct Builder{
    witness:Vec<Fr>,terms:Vec<Term>,materialize:bool,rows:usize,term_count:usize,
    boolean_rows:usize,linear_rows:usize,bilinear_rows:usize,hasher:Blake2bVar,
    max_column_bits:usize,live_before_padding:usize,peak_row_terms:usize,peak_row_capacity_terms:usize,
    additional_source_nbits_bits:usize,additional_decoded_bits:usize,
    subtract_traces:Vec<SubtractTrace>,carry_wires:Vec<usize>,
}
impl Builder{
    fn new(materialize:bool)->Self{
        let mut hasher=Blake2bVar::new(32).expect("digest length");hasher.update(b"daa-decode-quotient-boolean16-v1");
        Self{witness:Vec::new(),terms:Vec::new(),materialize,rows:0,term_count:0,
            boolean_rows:0,linear_rows:0,bilinear_rows:0,hasher,max_column_bits:0,
            live_before_padding:0,peak_row_terms:0,peak_row_capacity_terms:0,
            additional_source_nbits_bits:0,additional_decoded_bits:0,
            subtract_traces:Vec::new(),carry_wires:Vec::new()}
    }
    fn gate(left:usize,right:usize,c0:Fr,c1:Fr,c2:Fr,c3:Fr)->Gate{Gate{left,right,c0,c1,c2,c3}}
    pub(crate) fn linear(wire:usize,coefficient:Fr)->Gate{Self::gate(wire,0,Fr::zero(),coefficient,Fr::zero(),Fr::zero())}
    pub(crate) fn constant(coefficient:Fr)->Gate{Self::gate(0,0,coefficient,Fr::zero(),Fr::zero(),Fr::zero())}
    pub(crate) fn product(left:usize,right:usize,coefficient:Fr)->Gate{Self::gate(left,right,Fr::zero(),Fr::zero(),Fr::zero(),coefficient)}
    pub(crate) fn row(&mut self,gates:Vec<Gate>){
        self.peak_row_terms=self.peak_row_terms.max(gates.len());
        self.peak_row_capacity_terms=self.peak_row_capacity_terms.max(gates.capacity());
        let bilinear=gates.iter().any(|g|!g.c3.is_zero());
        if bilinear{self.bilinear_rows+=1}else{self.linear_rows+=1;}
        self.hasher.update(&(self.rows as u64).to_le_bytes());
        self.hasher.update(&(gates.len() as u64).to_le_bytes());
        for gate in gates{
            self.hasher.update(&(gate.left as u64).to_le_bytes());self.hasher.update(&(gate.right as u64).to_le_bytes());
            for c in [gate.c0,gate.c1,gate.c2,gate.c3]{let mut bytes=Vec::with_capacity(32);c.serialize_compressed(&mut bytes).expect("Vec serialization");self.hasher.update(&bytes);}
            if self.materialize{self.terms.push(Term{row:self.rows,gate});}
            self.term_count+=1;
        }
        self.rows+=1;
    }
    pub(crate) fn bit(&mut self,value:bool)->usize{
        let index=self.witness.len();let x=Fr::from(value as u64);self.witness.push(x);
        self.row(vec![Self::gate(index,index,Fr::zero(),-Fr::one(),Fr::zero(),Fr::one())]);
        self.boolean_rows+=1;index
    }
    pub(crate) fn bits_u64(&mut self,value:u64,width:usize)->Vec<usize>{(0..width).map(|i|self.bit(((value>>i)&1)!=0)).collect()}
    pub(crate) fn bits_big(&mut self,value:&BigUint,width:usize)->Vec<usize>{
        let bytes=value.to_bytes_le();(0..width).map(|i|self.bit(bytes.get(i/8).map(|b|((b>>(i%8))&1)!=0).unwrap_or(false))).collect()
    }
    pub(crate) fn value(&self,wire:usize)->bool{self.witness[wire]==Fr::one()}
    pub(crate) fn assert_zero(&mut self,wire:usize){self.row(vec![Self::linear(wire,Fr::one())]);}
    pub(crate) fn assert_one(&mut self,wire:usize){self.row(vec![Self::linear(wire,Fr::one()),Self::constant(-Fr::one())]);}
    pub(crate) fn not(&mut self,a:usize)->usize{
        let out=self.bit(!self.value(a));self.row(vec![Self::linear(out,Fr::one()),Self::linear(a,Fr::one()),Self::constant(-Fr::one())]);out
    }
    pub(crate) fn and(&mut self,a:usize,b:usize)->usize{
        let out=self.bit(self.value(a)&&self.value(b));self.row(vec![Self::linear(out,Fr::one()),Self::product(a,b,-Fr::one())]);out
    }
    fn or(&mut self,a:usize,b:usize)->usize{
        let out=self.bit(self.value(a)||self.value(b));self.row(vec![Self::linear(out,Fr::one()),Self::linear(a,-Fr::one()),Self::linear(b,-Fr::one()),Self::product(a,b,Fr::one())]);out
    }
    fn nonzero(&mut self,bits:&[usize]) -> usize{
        let mut accum=bits[0];for &b in &bits[1..]{accum=self.or(accum,b);}self.assert_one(accum);accum
    }
    pub(crate) fn progress(&self)->(usize,usize,usize){(self.witness.len(),self.rows,self.term_count)}
    pub(crate) fn note_column_bound(&mut self,bits:usize){self.max_column_bits=self.max_column_bits.max(bits);}
    fn pad(&mut self){
        self.live_before_padding=self.witness.len();
        let next=self.witness.len().next_power_of_two();
        for _ in self.witness.len()..next{let i=self.witness.len();self.witness.push(Fr::zero());self.assert_zero(i);}
    }
    fn finish(self,categories:Categories)->Result<(Count,Option<Circuit>,Vec<Fr>,Vec<SubtractTrace>,Vec<usize>),String>{
        let live=self.live_before_padding;
        if self.materialize && self.term_count>MAX_MATERIAL_TERMS{return Err("materialized sparse term cap".into());}
        let row_count=self.rows.next_power_of_two();
        let mut hash=[0;32];self.hasher.finalize_variable(&mut hash).expect("digest length");
        let source_nbits_bits=categories.nbits+self.additional_source_nbits_bits;
        let decoded_bits=categories.instances*DIFFICULTY_BITS+self.additional_decoded_bits;
        let known=source_nbits_bits+categories.timestamps+decoded_bits
            +categories.instances*(64+64+categories.numerator_width*2+64+2);
        if known>live{return Err("DAA bit-category accounting exceeds allocation".into());}
        let count=Count{live_bits:live,input_bits:live,padded_input_bits:self.witness.len(),residual_rows:self.rows,
            padded_rows:row_count,terms:self.term_count,boolean_rows:self.boolean_rows,
            linear_rows:self.linear_rows,bilinear_rows:self.bilinear_rows,
            maximum_column_signed_abs_bits:self.max_column_bits,maximum_degree:2,
            source_nbits_bits,source_timestamp_bits:categories.timestamps,
            decoded_bits,wrapped_delta_bits:categories.instances*64,
            denominator_bits:categories.instances*64,numerator_bits:categories.instances*categories.numerator_width,
            quotient_bits:categories.instances*categories.numerator_width,remainder_bits:categories.instances*64,
            quotient_sign_bits:categories.instances,remainder_sign_bits:categories.instances,auxiliary_bits:live-known,
            padding_bits:self.witness.len()-live,witness_capacity:self.witness.capacity(),
            retained_terms_capacity:self.terms.capacity(),peak_row_terms:self.peak_row_terms,
            peak_row_capacity_terms:self.peak_row_capacity_terms,
            topology_blake2b256:hash};
        let circuit=if self.materialize{Some(Circuit{input_len:self.witness.len(),row_count,terms:self.terms})}else{None};
        Ok((count,circuit,self.witness,self.subtract_traces,self.carry_wires))
    }
}

fn bit_value(value:&BigUint,index:usize)->bool{
    value.to_bytes_le().get(index/8).map(|b|((b>>(index%8))&1)!=0).unwrap_or(false)
}
fn bits_to_u64(builder:&Builder,bits:&[usize])->u64{
    bits.iter().enumerate().fold(0u64,|v,(i,w)|v|((builder.value(*w) as u64)<<i))
}
fn limb_value(builder:&Builder,bits:&[usize],limb:usize)->u64{
    (0..16).fold(0u64,|v,i|v|((bits.get(limb*16+i).map(|w|builder.value(*w)).unwrap_or(false) as u64)<<i))
}
fn limb_terms(bits:&[usize],limb:usize,coef:Fr)->Vec<Gate>{
    (0..16).filter_map(|i|bits.get(limb*16+i).copied().map(|wire|Builder::linear(wire,coef*Fr::from(1u64<<i)))).collect()
}
fn full_terms(bits:&[usize],coef:Fr)->Vec<Gate>{
    bits.iter().enumerate().map(|(i,&wire)|Builder::linear(wire,coef*Fr::from(1u64<<i))).collect()
}
fn require_nonzero(builder:&mut Builder,bits:&[usize]){builder.nonzero(bits);}
fn subtract_bits(builder:&mut Builder,a:&[usize],b:&[usize],initial_borrow:bool,require_no_borrow:bool)->Vec<usize>{
    let one=builder.bit(initial_borrow);
    if initial_borrow{builder.assert_one(one)}else{builder.assert_zero(one)}
    let mut borrow=one;let mut result=Vec::with_capacity(a.len());let mut borrows=Vec::with_capacity(a.len());
    for i in 0..a.len(){
        let av=builder.value(a[i]) as i32;let bv=builder.value(b[i]) as i32;let bin=builder.value(borrow) as i32;
        let raw=av-bv-bin;let bout=raw<0;let diff=builder.bit((raw&1)!=0);let next=builder.bit(bout);
        builder.row(vec![Builder::linear(a[i],Fr::one()),Builder::linear(b[i],-Fr::one()),
            Builder::linear(borrow,-Fr::one()),Builder::linear(diff,-Fr::one()),Builder::linear(next,Fr::from(2u64))]);
        result.push(diff);borrow=next;borrows.push(next);
    }
    if require_no_borrow{builder.assert_zero(borrow);}
    builder.subtract_traces.push(SubtractTrace{initial_borrow:one,differences:result.clone(),
        borrows,minuend_constant:None,minuend_wires:a.to_vec(),subtrahend_wires:b.to_vec()});
    result
}
fn subtract_constant_inner(builder:&mut Builder,constant:&BigUint,value:&[usize],initial_borrow:bool)->(Vec<usize>,usize){
    let borrow0=builder.bit(initial_borrow);
    if initial_borrow{builder.assert_one(borrow0)}else{builder.assert_zero(borrow0)}
    let mut borrow=borrow0;let mut result=Vec::with_capacity(value.len());let mut borrows=Vec::with_capacity(value.len());
    for i in 0..value.len(){
        let q=bit_value(constant,i) as i32;let v=builder.value(value[i]) as i32;let bin=builder.value(borrow) as i32;
        let raw=q-v-bin;let diff=builder.bit((raw&1)!=0);let next=builder.bit(raw<0);
        builder.row(vec![Builder::constant(Fr::from(q as u64)),Builder::linear(value[i],-Fr::one()),
            Builder::linear(borrow,-Fr::one()),Builder::linear(diff,-Fr::one()),Builder::linear(next,Fr::from(2u64))]);
        result.push(diff);borrow=next;borrows.push(next);
    }
    builder.assert_zero(borrow);
    builder.subtract_traces.push(SubtractTrace{initial_borrow:borrow0,differences:result.clone(),
        borrows,minuend_constant:Some(constant.clone()),minuend_wires:Vec::new(),subtrahend_wires:value.to_vec()});
    (result,borrow)
}
fn subtract_constant(builder:&mut Builder,constant:&BigUint,value:&[usize],initial_borrow:bool)->Vec<usize>{
    subtract_constant_inner(builder,constant,value,initial_borrow).0
}
pub(crate) fn subtract_constant_with_final_borrow(builder:&mut Builder,constant:&BigUint,value:&[usize],initial_borrow:bool)->usize{
    subtract_constant_inner(builder,constant,value,initial_borrow).1
}
fn decode_compact(nbits:u32)->BigUint{
    let exponent=(nbits>>24) as usize;let mantissa=(nbits&0x7fffff) as u64;
    match exponent{0=>BigUint::zero(),1=>BigUint::from(mantissa>>16),2=>BigUint::from(mantissa>>8),e=>BigUint::from(mantissa)<<(8*(e-3))}
}
fn decode_constraints(builder:&mut Builder,nbits:&[usize;32],q:&BigUint)->Vec<usize>{
    builder.assert_zero(nbits[23]);
    let mut selectors=Vec::with_capacity(34);
    let complements=(24..32).map(|i|builder.not(nbits[i])).collect::<Vec<_>>();
    for exponent in 1..=34usize{
        let mut s=builder.bit(true);builder.assert_one(s);
        for i in 0..8{s=builder.and(s,if (exponent>>i)&1==1{nbits[24+i]}else{complements[i]});}
        selectors.push(s);
    }
    let mut onehot=selectors.iter().map(|&s|Builder::linear(s,Fr::one())).collect::<Vec<_>>();
    onehot.push(Builder::constant(-Fr::one()));builder.row(onehot);
    let decoded=decode_compact(bits_to_u64(builder,nbits) as u32);
    let d=builder.bits_big(&decoded,DIFFICULTY_BITS);
    for position in 0..=270{
        let mut row=Vec::new();
        if position<DIFFICULTY_BITS{row.push(Builder::linear(d[position],-Fr::one()));}
        for exponent in 1..=34usize{
            for mantissa_bit in 0..23{
                let target=match exponent{1 if mantissa_bit>=16=>Some(mantissa_bit-16),
                    2 if mantissa_bit>=8=>Some(mantissa_bit-8),e if e>=3=>Some(8*(e-3)+mantissa_bit),_=>None};
                if target==Some(position){row.push(Builder::product(selectors[exponent-1],nbits[mantissa_bit],Fr::one()));}
            }
        }
        if !row.is_empty(){builder.row(row);}
    }
    require_nonzero(builder,&d);
    subtract_constant(builder,q,&d,false);
    d
}
fn decode_constraints_against(builder:&mut Builder,nbits:&[usize;32],q:&BigUint,
    expected:&[usize])->Result<(),String>{
    if expected.len()<DIFFICULTY_BITS{return Err("DAA result is narrower than decoded difficulty".into());}
    builder.assert_zero(nbits[23]);
    let complements=(24..32).map(|i|builder.not(nbits[i])).collect::<Vec<_>>();
    let mut selectors=Vec::with_capacity(34);
    for exponent in 1..=34usize{
        let mut selected=if exponent&1==1{nbits[24]}else{complements[0]};
        for i in 1..8{
            selected=builder.and(selected,if (exponent>>i)&1==1{nbits[24+i]}else{complements[i]});
        }
        selectors.push(selected);
    }
    let mut onehot=selectors.iter().map(|&s|Builder::linear(s,Fr::one())).collect::<Vec<_>>();
    onehot.push(Builder::constant(-Fr::one()));builder.row(onehot);
    for position in 0..=270{
        let mut row=Vec::new();
        if position<expected.len(){row.push(Builder::linear(expected[position],-Fr::one()));}
        for exponent in 1..=34usize{
            for mantissa_bit in 0..23{
                let target=match exponent{1 if mantissa_bit>=16=>Some(mantissa_bit-16),
                    2 if mantissa_bit>=8=>Some(mantissa_bit-8),e if e>=3=>Some(8*(e-3)+mantissa_bit),_=>None};
                if target==Some(position){row.push(Builder::product(selectors[exponent-1],nbits[mantissa_bit],Fr::one()));}
            }
        }
        if !row.is_empty(){builder.row(row);}
    }
    require_nonzero(builder,expected);
    subtract_constant(builder,q,expected,false);
    Ok(())
}
pub(crate) fn bind_child_nbits_to_result(builder:&mut Builder,nbits:u32,q:&BigUint,
    expected:&[usize])->Result<[usize;32],String>{
    if q.is_zero()||q.bits()>DIFFICULTY_BITS as u64{return Err("invalid child difficulty bound".into());}
    if expected.len()<DIFFICULTY_BITS{return Err("DAA result is narrower than decoded difficulty".into());}
    let raw:[usize;32]=builder.bits_u64(nbits as u64,32).try_into().map_err(|_|"child nBits map")?;
    decode_constraints_against(builder,&raw,q,expected)?;
    builder.additional_source_nbits_bits+=raw.len();
    builder.additional_decoded_bits+=DIFFICULTY_BITS;
    Ok(raw)
}
fn signed_difference(builder:&mut Builder,start:&[usize;64],end:&[usize;64])->(Vec<usize>,Vec<usize>){
    let delta=subtract_bits(builder,end,start,false,false);
    let sign=delta[63];
    let mut neg=Vec::with_capacity(64);let mut carry=builder.bit(true);builder.assert_one(carry);
    for &bit in &delta{
        let not=builder.not(bit);
        let raw=builder.value(not) as u8+builder.value(carry) as u8;
        let out=builder.bit(raw&1!=0);let next=builder.bit(raw>=2);
        builder.row(vec![Builder::linear(not,Fr::one()),Builder::linear(carry,Fr::one()),
            Builder::linear(out,-Fr::one()),Builder::linear(next,-Fr::from(2u64))]);
        neg.push(out);carry=next;
    }
    let mut magnitude=Vec::with_capacity(64);
    for i in 0..64{
        let v=if builder.value(sign){builder.value(neg[i])}else{builder.value(delta[i])};
        let out=builder.bit(v);
        builder.row(vec![Builder::linear(out,Fr::one()),Builder::linear(delta[i],-Fr::one()),
            Builder::product(sign,delta[i],Fr::one()),Builder::product(sign,neg[i],-Fr::one())]);
        magnitude.push(out);
    }
    require_nonzero(builder,&magnitude);
    (delta,magnitude)
}
fn constant_numerator(builder:&mut Builder,d:&[usize],epoch:Epoch)->Vec<usize>{
    let c=epoch.multiplier();let nwidth=epoch.numerator_bits();
    let dval=BigUint::from(bits_to_big(builder,d));let numerator=dval*BigUint::from(c);
    let n=builder.bits_big(&numerator,nwidth);
    let c_bits=64-c.leading_zeros() as usize;
    let carry_width=c_bits;let mut carry_value=0u64;let mut carry_bits:Vec<usize>=Vec::new();
    for limb in 0..nwidth.div_ceil(16){
        let column=c*limb_value(builder,d,limb)+carry_value;
        carry_value=column>>16;
        assert!(carry_value<(1u64<<carry_width),"numerator carry range");
        let next=if limb+1<nwidth.div_ceil(16){builder.bits_u64(carry_value,carry_width)}else{Vec::new()};
        builder.carry_wires.extend(&next);
        let mut row=limb_terms(d,limb,Fr::from(c));
        row.extend(full_terms(&carry_bits,Fr::one()));
        row.extend(limb_terms(&n,limb,-Fr::one()));
        row.extend(full_terms(&next,-Fr::from(1u64<<16)));
        builder.row(row);carry_bits=next;
    }
    builder.max_column_bits=builder.max_column_bits.max(column_bound_bits().0);
    n
}
fn bits_to_big(builder:&Builder,bits:&[usize])->BigUint{
    let mut bytes=vec![0u8;bits.len().div_ceil(8)];
    for (i,&wire) in bits.iter().enumerate(){if builder.value(wire){bytes[i/8]|=1<<(i%8);}}
    BigUint::from_bytes_le(&bytes)
}
fn quotient_product(builder:&mut Builder,n:&[usize],b:&[usize],denominator_negative:usize,epoch:Epoch)->(Vec<usize>,Vec<usize>,usize,usize){
    let numerator=bits_to_big(builder,n);let denom=bits_to_big(builder,b);
    let (quotient,remainder)=if denom.is_zero(){(BigUint::zero(),BigUint::zero())}else{(&numerator/&denom,&numerator%&denom)};
    let q=builder.bits_big(&quotient,epoch.numerator_bits());let r=builder.bits_big(&remainder,64);
    let remainder_negative=builder.bit(false);builder.assert_zero(remainder_negative);
    let q_nonzero=builder.nonzero_unasserted(&q);
    let sign=builder.and(denominator_negative,q_nonzero);
    let mut carry_value=0u64;let mut carry_bits=Vec::new();
    let qlimbs=q.len().div_ceil(16);let columns=qlimbs+4-1;
    for column in 0..columns{
        let mut column_value=carry_value+limb_value(builder,&r,column);
        let mut gates=full_terms(&carry_bits,Fr::one());
        gates.extend(limb_terms(&r,column,Fr::one()));
        gates.extend(limb_terms(n,column,-Fr::one()));
        for qi in 0..qlimbs{
            if column>=qi && column-qi<4{
                let bi=column-qi;column_value+=limb_value(builder,&q,qi)*limb_value(builder,b,bi);
                for x in 0..16{if let Some(&qw)=q.get(qi*16+x){
                    for y in 0..16{if let Some(&bw)=b.get(bi*16+y){
                        gates.push(Builder::product(qw,bw,Fr::from(1u64<<(x+y))));
                    }}
                }}
            }
        }
        carry_value=column_value>>16;
        assert!(carry_value<(1u64<<19),"product carry range");
        let next=if column+1<columns{builder.bits_u64(carry_value,19)}else{Vec::new()};
        builder.carry_wires.extend(&next);
        gates.extend(full_terms(&next,-Fr::from(1u64<<16)));
        builder.row(gates);carry_bits=next;
    }
    // remainder < nonzero denominator, including MIN signed denominator.
    let _difference=subtract_bits(builder,b,&r,true,true);
    builder.max_column_bits=builder.max_column_bits.max(column_bound_bits().1);
    (q,r,sign,remainder_negative)
}
impl Builder{
    pub(crate) fn nonzero_unasserted(&mut self,bits:&[usize])->usize{
        let mut accum=bits[0];for &b in &bits[1..]{accum=self.or(accum,b);}accum
    }
}

/// Compile the same fixed topology into a streaming count or bounded materialization.
/// `q` is the pinned 256-bit Autolykos bound supplied by the fixed descriptor.
pub fn compile(epoch:Epoch,q:&BigUint,input:Inputs,materialize:bool)->Result<Compiled,String>{
    compile_extended(epoch,q,input,materialize,|_,_,_|Ok(())).map(|(compiled,())|compiled)
}

/// Append an owned consumer before padding, retaining the original A1 handles.
pub(crate) fn compile_extended<T,F>(epoch:Epoch,q:&BigUint,input:Inputs,materialize:bool,
    extend:F)->Result<(Compiled,T),String>
where F:FnOnce(&mut Builder,&ExternalBits,&OutputBits)->Result<T,String>{
    if q.bits()>256 || q.is_zero(){return Err("invalid descriptor Q".into());}
    let mut b=Builder::new(materialize);
    let nbits: [usize;32]=b.bits_u64(input.nbits as u64,32).try_into().map_err(|_|"nbits map")?;
    let start:[usize;64]=b.bits_u64(input.start_timestamp as u64,64).try_into().map_err(|_|"start map")?;
    let end:[usize;64]=b.bits_u64(input.end_timestamp as u64,64).try_into().map_err(|_|"end map")?;
    let external=ExternalBits{nbits,start_timestamp:start,end_timestamp:end};
    let d=decode_constraints(&mut b,&external.nbits,q);
    let (delta,magnitude)=signed_difference(&mut b,&external.start_timestamp,&external.end_timestamp);
    let numerator=constant_numerator(&mut b,&d,epoch);
    let (quotient,remainder,quotient_negative,remainder_negative)=quotient_product(&mut b,&numerator,&magnitude,delta[63],epoch);
    // Signed quotient follows the wrapped signed denominator unless q=0.
    let q_nonzero=b.nonzero_unasserted(&quotient);
    b.row(vec![Builder::linear(quotient_negative,Fr::one()),Builder::product(delta[63],q_nonzero,-Fr::one())]);
    let output=OutputBits{decoded_difficulty:d,wrapped_delta:delta,denominator_magnitude:magnitude,
        numerator,quotient_magnitude:quotient,quotient_negative,remainder_magnitude:remainder,remainder_negative};
    let extra=extend(&mut b,&external,&output)?;
    b.pad();let (count,circuit,witness,subtract_traces,carry_wires)=b.finish(Categories{nbits:32,timestamps:128,instances:1,numerator_width:epoch.numerator_bits()})?;
    Ok((Compiled{count,external,output,circuit,witness,subtract_traces,carry_wires},extra))
}

#[cfg(test)]
#[path = "daa_integer_single_before_m1.rs"]
pub(crate) mod single_before_m1;

/// Eight adjacent quotients share exactly nine timestamp fields. Each end
/// sample has its own 32-bit compact difficulty and fresh private auxiliaries.
pub fn compile_eight(epoch:Epoch,q:&BigUint,input:WindowInputs,materialize:bool)->Result<CompiledWindow,String>{
    compile_eight_extended(epoch,q,input,materialize,|_,_|Ok(())).map(|(compiled,())|compiled)
}
pub(crate) fn compile_eight_extended<T,F>(epoch:Epoch,q:&BigUint,input:WindowInputs,materialize:bool,
    extend:F)->Result<(CompiledWindow,T),String>
where F:FnOnce(&mut Builder,&[OutputBits])->Result<T,String>{
    if q.bits()>256 || q.is_zero(){return Err("invalid descriptor Q".into());}
    let mut b=Builder::new(materialize);
    let mut nbits=Vec::with_capacity(8);
    for raw in input.nbits {nbits.push(b.bits_u64(raw as u64,32).try_into().map_err(|_|"nbits map")?);}
    let mut timestamps=Vec::with_capacity(9);
    for raw in input.timestamps {timestamps.push(b.bits_u64(raw as u64,64).try_into().map_err(|_|"timestamp map")?);}
    let mut external=Vec::with_capacity(8);let mut output=Vec::with_capacity(8);
    for j in 0..8{
        let source=ExternalBits{nbits:nbits[j],start_timestamp:timestamps[j],end_timestamp:timestamps[j+1]};
        let d=decode_constraints(&mut b,&source.nbits,q);
        let (delta,magnitude)=signed_difference(&mut b,&source.start_timestamp,&source.end_timestamp);
        let numerator=constant_numerator(&mut b,&d,epoch);
        let (quotient,remainder,quotient_negative,remainder_negative)=quotient_product(&mut b,&numerator,&magnitude,delta[63],epoch);
        let q_nonzero=b.nonzero_unasserted(&quotient);
        b.row(vec![Builder::linear(quotient_negative,Fr::one()),Builder::product(delta[63],q_nonzero,-Fr::one())]);
        output.push(OutputBits{decoded_difficulty:d,wrapped_delta:delta,denominator_magnitude:magnitude,
            numerator,quotient_magnitude:quotient,quotient_negative,remainder_magnitude:remainder,remainder_negative});
        external.push(source);
    }
    let extra=extend(&mut b,&output)?;
    b.pad();let (count,circuit,witness,subtract_traces,carry_wires)=b.finish(Categories{nbits:8*32,timestamps:9*64,instances:8,numerator_width:epoch.numerator_bits()})?;
    Ok((CompiledWindow{count,external,output,circuit,witness,subtract_traces,carry_wires},extra))
}

/// Compile the code-owned Legacy two-ratio profile over three shared timestamps.
pub fn compile_two(q:&BigUint,input:TwoRatioInputs,materialize:bool)->Result<CompiledWindow,String>{
    compile_two_extended(q,input,materialize,|_,_|Ok(())).map(|(compiled,())|compiled)
}
pub(crate) fn compile_two_extended<T,F>(q:&BigUint,input:TwoRatioInputs,materialize:bool,
    extend:F)->Result<(CompiledWindow,T),String>
where F:FnOnce(&mut Builder,&[OutputBits])->Result<T,String>{
    if q.bits()>256 || q.is_zero(){return Err("invalid descriptor Q".into());}
    let epoch=Epoch::Legacy;
    let mut b=Builder::new(materialize);
    let mut nbits=Vec::with_capacity(2);
    for raw in input.nbits {nbits.push(b.bits_u64(raw as u64,32).try_into().map_err(|_|"nbits map")?);}
    let mut timestamps=Vec::with_capacity(3);
    for raw in input.timestamps {timestamps.push(b.bits_u64(raw as u64,64).try_into().map_err(|_|"timestamp map")?);}
    let mut external=Vec::with_capacity(2);let mut output=Vec::with_capacity(2);
    for j in 0..2{
        let source=ExternalBits{nbits:nbits[j],start_timestamp:timestamps[j],end_timestamp:timestamps[j+1]};
        let d=decode_constraints(&mut b,&source.nbits,q);
        let (delta,magnitude)=signed_difference(&mut b,&source.start_timestamp,&source.end_timestamp);
        let numerator=constant_numerator(&mut b,&d,epoch);
        let (quotient,remainder,quotient_negative,remainder_negative)=quotient_product(&mut b,&numerator,&magnitude,delta[63],epoch);
        let q_nonzero=b.nonzero_unasserted(&quotient);
        b.row(vec![Builder::linear(quotient_negative,Fr::one()),Builder::product(delta[63],q_nonzero,-Fr::one())]);
        output.push(OutputBits{decoded_difficulty:d,wrapped_delta:delta,denominator_magnitude:magnitude,
            numerator,quotient_magnitude:quotient,quotient_negative,remainder_magnitude:remainder,remainder_negative});
        external.push(source);
    }
    let extra=extend(&mut b,&output)?;
    b.pad();let (count,circuit,witness,subtract_traces,carry_wires)=b.finish(Categories{
        nbits:2*32,timestamps:3*64,instances:2,numerator_width:epoch.numerator_bits()})?;
    Ok((CompiledWindow{count,external,output,circuit,witness,subtract_traces,carry_wires},extra))
}

/// Compile a code-owned Legacy m=3..7 profile without padding it to eight.
pub(crate) fn compile_short_legacy<T,F>(q:&BigUint,input:ShortLegacyInputs,materialize:bool,
    extend:F)->Result<(CompiledWindow,T),String>
where F:FnOnce(&mut Builder,&[OutputBits])->Result<T,String>{
    let m=input.profile.count();
    if input.nbits.len()!=m || input.timestamps.len()!=m+1{
        return Err("short Legacy input shape does not match profile".into());
    }
    if q.bits()>DIFFICULTY_BITS as u64 || q.is_zero(){return Err("invalid descriptor Q".into());}
    let mut b=Builder::new(materialize);
    let nbits=input.nbits.iter().map(|&raw|
        b.bits_u64(raw as u64,32).try_into().map_err(|_|"nbits map".to_owned()))
        .collect::<Result<Vec<[usize;32]>,String>>()?;
    let timestamps=input.timestamps.iter().map(|&raw|
        b.bits_u64(raw as u64,64).try_into().map_err(|_|"timestamp map".to_owned()))
        .collect::<Result<Vec<[usize;64]>,String>>()?;
    let mut external=Vec::with_capacity(m);let mut output=Vec::with_capacity(m);
    for j in 0..m{
        let source=ExternalBits{nbits:nbits[j],start_timestamp:timestamps[j],end_timestamp:timestamps[j+1]};
        let d=decode_constraints(&mut b,&source.nbits,q);
        let (delta,magnitude)=signed_difference(&mut b,&source.start_timestamp,&source.end_timestamp);
        let numerator=constant_numerator(&mut b,&d,Epoch::Legacy);
        let (quotient,remainder,quotient_negative,remainder_negative)
            =quotient_product(&mut b,&numerator,&magnitude,delta[63],Epoch::Legacy);
        let q_nonzero=b.nonzero_unasserted(&quotient);
        b.row(vec![Builder::linear(quotient_negative,Fr::one()),
            Builder::product(delta[63],q_nonzero,-Fr::one())]);
        output.push(OutputBits{decoded_difficulty:d,wrapped_delta:delta,denominator_magnitude:magnitude,
            numerator,quotient_magnitude:quotient,quotient_negative,remainder_magnitude:remainder,
            remainder_negative});
        external.push(source);
    }
    let extra=extend(&mut b,&output)?;
    b.pad();
    let (count,circuit,witness,subtract_traces,carry_wires)=b.finish(Categories{
        nbits:m*32,timestamps:(m+1)*64,instances:m,numerator_width:Epoch::Legacy.numerator_bits()})?;
    Ok((CompiledWindow{count,external,output,circuit,witness,subtract_traces,carry_wires},extra))
}

pub fn residuals(compiled:&Compiled)->Result<Vec<Fr>,String>{
    let circuit=compiled.circuit.as_ref().ok_or("count-only circuit")?;
    let mut rows=vec![Fr::zero();circuit.row_count];
    for term in &circuit.terms{rows[term.row]+=term.gate.evaluate(&compiled.witness);}
    Ok(rows)
}

#[cfg(test)]
mod tests{
    use super::*;
    use ark_ff::One;
    fn fixed_q()->BigUint{BigUint::parse_bytes(b"FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141",16).unwrap()}
    fn read_bits(witness:&[Fr],bits:&[usize])->BigUint{
        let mut bytes=vec![0u8;bits.len().div_ceil(8)];
        for (i,&wire) in bits.iter().enumerate(){if witness[wire]==Fr::one(){bytes[i/8]|=1<<(i%8);}}
        BigUint::from_bytes_le(&bytes)
    }
    fn reference_compact(nbits:u32)->BigUint{
        let bytes=nbits.to_be_bytes();let exponent=bytes[0] as usize;
        let mantissa=((bytes[1] as u64&0x7f)<<16)|((bytes[2] as u64)<<8)|bytes[3] as u64;
        if exponent<=3{BigUint::from(mantissa>>(8*(3-exponent)))}
        else{BigUint::from(mantissa)<<(8*(exponent-3))}
    }
    fn reference(input:Inputs,epoch:Epoch)->(BigUint,BigUint,BigUint,bool){
        let d=reference_compact(input.nbits);
        let delta=input.end_timestamp.wrapping_sub(input.start_timestamp);
        let magnitude=BigUint::from(delta.unsigned_abs());
        let n=d.clone()*BigUint::from(epoch.multiplier());
        let quotient=&n/&magnitude;let remainder=&n%&magnitude;
        (d,quotient,remainder,delta<0)
    }
    fn nonzero_rows(c:&Compiled)->Vec<usize>{residuals(c).unwrap().iter().enumerate().filter_map(|(i,x)|if x.is_zero(){None}else{Some(i)}).collect()}
    fn nonzero_window_rows(c:&CompiledWindow)->Vec<usize>{
        let circuit=c.circuit.as_ref().expect("materialized window circuit");
        let mut rows=vec![Fr::zero();circuit.row_count];
        for term in &circuit.terms{rows[term.row]+=term.gate.evaluate(&c.witness);}
        rows.iter().enumerate().filter_map(|(i,x)|if x.is_zero(){None}else{Some(i)}).collect()
    }
    fn mutate(c:&mut Compiled,wire:usize){c.witness[wire]=if c.witness[wire].is_zero(){Fr::one()}else{Fr::zero()};}
    fn mutate_window(c:&mut CompiledWindow,wire:usize){c.witness[wire]=if c.witness[wire].is_zero(){Fr::one()}else{Fr::zero()};}
    fn set_bits(witness:&mut [Fr],wires:&[usize],value:&BigUint){
        for (i,&wire) in wires.iter().enumerate(){witness[wire]=Fr::from(bit_value(value,i) as u64);}
    }
    fn witness_limb(witness:&[Fr],wires:&[usize],limb:usize)->u64{
        wires.iter().skip(16*limb).take(16).enumerate()
            .fold(0u64,|value,(i,&wire)|value|(((witness[wire]==Fr::one()) as u64)<<i))
    }
    #[test]
    fn daa_integer_native_shape_oracle_and_degenerate_signs(){
        let cases=[
            Inputs{nbits:0x01010000,start_timestamp:10,end_timestamp:13},
            Inputs{nbits:0x02000100,start_timestamp:13,end_timestamp:10},
            Inputs{nbits:0x03000001,start_timestamp:i64::MIN,end_timestamp:i64::MAX},
            Inputs{nbits:0x03000001,start_timestamp:i64::MAX,end_timestamp:i64::MIN},
            Inputs{nbits:0x03000001,start_timestamp:0,end_timestamp:i64::MIN},
            Inputs{nbits:0x22000001,start_timestamp:100,end_timestamp:101},
        ];
        for epoch in [Epoch::Legacy,Epoch::Eip]{
            let mut topology=None;
            for input in cases{
                let c=compile(epoch,&fixed_q(),input,true).unwrap();
                assert!(nonzero_rows(&c).is_empty(),"{:?} {:?}",epoch,input);
                let (d,quotient,remainder,negative)=reference(input,epoch);
                assert_eq!(read_bits(&c.witness,&c.output.decoded_difficulty),d);
                assert_eq!(read_bits(&c.witness,&c.output.quotient_magnitude),quotient);
                assert_eq!(read_bits(&c.witness,&c.output.remainder_magnitude),remainder);
                assert_eq!(c.witness[c.output.quotient_negative]==Fr::one(),negative && !quotient.is_zero());
                assert!(c.witness[c.output.remainder_negative].is_zero());
                assert_eq!(c.count.maximum_degree,2);
                assert!(c.count.maximum_column_signed_abs_bits<254);
                assert!(c.count.terms<=MAX_MATERIAL_TERMS);
                if let Some(previous)=topology{assert_eq!(c.count.topology_blake2b256,previous)}
                topology=Some(c.count.topology_blake2b256);
            }
        }
    }
    #[test]
    fn daa_integer_count_eight_shares_inputs_and_topology(){
        let inputs=WindowInputs{nbits:[0x03000001;8],timestamps:[0,1,2,3,4,5,6,7,8]};
        for epoch in [Epoch::Legacy,Epoch::Eip]{
            let one=compile(epoch,&fixed_q(),Inputs{nbits:0x03000001,start_timestamp:0,end_timestamp:1},false).unwrap();
            let eight=compile_eight(epoch,&fixed_q(),inputs,false).unwrap();
            assert_eq!(one.count.source_nbits_bits,32);assert_eq!(one.count.source_timestamp_bits,128);
            assert_eq!(eight.count.source_nbits_bits,256);assert_eq!(eight.count.source_timestamp_bits,576);
            assert_eq!(eight.external[0].end_timestamp,eight.external[1].start_timestamp);
            assert!(eight.count.live_bits<8*one.count.live_bits);
            // Padding contributes one assertion term per padded bit. Remove
            // those terms before comparing the 448 shared timestamp bits.
            assert_eq!(8*(one.count.terms-one.count.padding_bits)
                -(eight.count.terms-eight.count.padding_bits),7*64);
            assert!(eight.count.padded_input_bits.is_power_of_two());
            assert!(eight.count.padded_rows.is_power_of_two());
            let varied=WindowInputs{
                nbits:[0x03000001,0x02000100,0x01010000,0x22000001,
                    0x03000002,0x03000003,0x03000004,0x03000005],
                timestamps:[0,1,3,2,i64::MIN,0,i64::MAX,0,10]};
            let materialized=compile_eight(epoch,&fixed_q(),varied,true).unwrap();
            assert_eq!(materialized.count.topology_blake2b256,eight.count.topology_blake2b256);
            assert_eq!(materialized.count.live_bits,eight.count.live_bits);
            assert_eq!(materialized.count.terms,eight.count.terms);
            let circuit=materialized.circuit.as_ref().unwrap();
            let mut rows=vec![Fr::zero();circuit.row_count];
            for term in &circuit.terms{rows[term.row]+=term.gate.evaluate(&materialized.witness);}
            assert!(rows.iter().all(Zero::is_zero),"eight materialized residuals must vanish");
            for j in 0..8{
                let input=Inputs{nbits:varied.nbits[j],start_timestamp:varied.timestamps[j],
                    end_timestamp:varied.timestamps[j+1]};
                let (d,quotient,remainder,negative)=reference(input,epoch);
                let output=&materialized.output[j];
                assert_eq!(read_bits(&materialized.witness,&output.decoded_difficulty),d);
                assert_eq!(read_bits(&materialized.witness,&output.quotient_magnitude),quotient);
                assert_eq!(read_bits(&materialized.witness,&output.remainder_magnitude),remainder);
                assert_eq!(materialized.witness[output.quotient_negative]==Fr::one(),negative && !quotient.is_zero());
                assert!(materialized.witness[output.remainder_negative].is_zero());
            }
            let mut bad=inputs;bad.timestamps[4]=i64::MIN;
            let other=compile_eight(epoch,&fixed_q(),bad,false).unwrap();
            assert_eq!(eight.count.topology_blake2b256,other.count.topology_blake2b256);
        }
    }
    fn mainnet_3073_two_ratio_inputs()->TwoRatioInputs{
        fn raw_header(height:u32)->ergo_header_core::Header{
            let fixture:serde_json::Value=serde_json::from_str(include_str!("../fixtures/mainnet-daa-windows-v1.json")).unwrap();
            let entry=fixture["headers"].as_array().unwrap().iter()
                .find(|entry|entry["height"].as_u64()==Some(height as u64)).unwrap();
            let hex=entry["raw_hex"].as_str().unwrap();
            let raw=(0..hex.len()).step_by(2).map(|i|u8::from_str_radix(&hex[i..i+2],16).unwrap()).collect::<Vec<_>>();
            let header=ergo_header_core::Header::decode(&raw,None).unwrap();
            assert_eq!(header.height,height);
            header
        }
        let start=raw_header(1_024);let middle=raw_header(2_048);let end=raw_header(3_072);
        assert_eq!([start.timestamp,middle.timestamp,end.timestamp],
            [1_561_986_131_991,1_561_993_105_670,1_562_018_260_215]);
        assert_eq!([middle.n_bits,end.n_bits],[0x0601_1765,0x0613_3b15]);
        TwoRatioInputs{nbits:[middle.n_bits,end.n_bits],timestamps:[start.timestamp,middle.timestamp,end.timestamp]}
    }
    #[test]
    fn daa_integer_two_ratio_real_mainnet_a1_and_isolated_ports(){
        let q=fixed_q();let input=mainnet_3073_two_ratio_inputs();
        let counted=compile_two(&q,input,false).unwrap();
        let mut compiled=compile_two(&q,input,true).unwrap();
        assert_eq!(compiled.count.topology_blake2b256,counted.count.topology_blake2b256);
        assert_eq!(compiled.count.live_bits,counted.count.live_bits);
        assert_eq!(compiled.count.residual_rows,counted.count.residual_rows);
        assert_eq!(compiled.count.terms,counted.count.terms);
        assert_eq!(compiled.count.source_nbits_bits,64);
        assert_eq!(compiled.count.source_timestamp_bits,3*64);
        assert_eq!(compiled.output.len(),2);
        assert_eq!(compiled.external[0].end_timestamp,compiled.external[1].start_timestamp,
            "the middle timestamp must be one shared input map");
        for j in 0..2{
            let source=Inputs{nbits:input.nbits[j],start_timestamp:input.timestamps[j],end_timestamp:input.timestamps[j+1]};
            let (difficulty,quotient,remainder,negative)=reference(source,Epoch::Legacy);
            assert_eq!(read_bits(&compiled.witness,&compiled.external[j].nbits),BigUint::from(source.nbits));
            assert_eq!(read_bits(&compiled.witness,&compiled.external[j].start_timestamp),
                BigUint::from(source.start_timestamp as u64));
            assert_eq!(read_bits(&compiled.witness,&compiled.external[j].end_timestamp),
                BigUint::from(source.end_timestamp as u64));
            let output=&compiled.output[j];
            assert_eq!(read_bits(&compiled.witness,&output.decoded_difficulty),difficulty);
            assert_eq!(read_bits(&compiled.witness,&output.quotient_magnitude),quotient);
            assert_eq!(read_bits(&compiled.witness,&output.remainder_magnitude),remainder);
            assert_eq!(compiled.witness[output.quotient_negative]==Fr::one(),negative && !quotient.is_zero());
            assert!(compiled.witness[output.remainder_negative].is_zero());
        }
        assert_eq!(read_bits(&compiled.witness,&compiled.output[0].quotient_magnitude),
            BigUint::from(21_144_480_152_624u64));
        assert_eq!(read_bits(&compiled.witness,&compiled.output[1].quotient_magnitude),
            BigUint::from(103_290_806_896_731u64));
        assert_eq!(read_bits(&compiled.witness,&compiled.output[0].remainder_magnitude),BigUint::from(1_216_304u64));
        assert_eq!(read_bits(&compiled.witness,&compiled.output[1].remainder_magnitude),BigUint::from(12_427_605u64));
        assert!(nonzero_window_rows(&compiled).is_empty(),"both real Mainnet A1 instances must satisfy every row");

        let ports={
            let mut c=compile_two(&q,input,true).unwrap();
            let mut ports=Vec::new();
            for j in 0..2{
                ports.push((format!("instance {j} nBits"),c.external[j].nbits[0]));
                ports.push((format!("instance {j} start timestamp"),c.external[j].start_timestamp[0]));
                ports.push((format!("instance {j} end timestamp"),c.external[j].end_timestamp[0]));
            }
            ports
        };
        for (name,wire) in ports{
            let mut mutant=compile_two(&q,input,true).unwrap();mutate_window(&mut mutant,wire);
            assert!(!nonzero_window_rows(&mutant).is_empty(),"isolated input-port mutation accepted: {name}");
        }
        for j in 0..2{
            for (name,wire) in [
                ("quotient",compiled.output[j].quotient_magnitude[0]),
                ("remainder",compiled.output[j].remainder_magnitude[0]),
                ("quotient sign",compiled.output[j].quotient_negative),
                ("remainder sign",compiled.output[j].remainder_negative),
            ]{
                let mut mutant=compile_two(&q,input,true).unwrap();mutate_window(&mut mutant,wire);
                assert!(!nonzero_window_rows(&mutant).is_empty(),"isolated {name} mutation accepted for instance {j}");
            }
        }
        assert!(compile_two(&BigUint::zero(),input,false).is_err(),"zero Q must be rejected");
        assert!(compile_two(&(BigUint::one()<<257usize),input,false).is_err(),"over-width Q must be rejected");
        drop(compiled);
    }
    #[test]
    fn child_compact_binding_enforces_full_high_tail_and_count_metadata(){
        let residuals=|builder:&Builder|{
            let mut rows=vec![Fr::zero();builder.rows];
            for term in &builder.terms{rows[term.row]+=term.gate.evaluate(&builder.witness);}
            rows
        };
        let mut builder=Builder::new(true);
        let wide=(BigUint::one()<<300usize)+BigUint::one();
        let expected=builder.bits_big(&wide,333);
        let raw=bind_child_nbits_to_result(&mut builder,0x03000001,&fixed_q(),&expected).unwrap();
        assert_eq!(bits_to_u64(&builder,&raw),0x03000001);
        let failing=residuals(&builder).iter().enumerate()
            .filter_map(|(row,value)|(!value.is_zero()).then_some(row)).collect::<Vec<_>>();
        assert_eq!(failing.len(),1,"bit 300 must not be truncated from the A4 result");
        builder.terms.retain(|term|term.row!=failing[0]);
        assert!(residuals(&builder).iter().all(Zero::is_zero),
            "omitting the isolated high-tail equality must admit the synthetic mismatch");

        let mut counted=Builder::new(false);
        let expected=counted.bits_big(&BigUint::one(),333);
        bind_child_nbits_to_result(&mut counted,0x03000001,&fixed_q(),&expected).unwrap();
        counted.pad();
        let (count,_,_,_,_)=counted.finish(Categories{nbits:0,timestamps:0,instances:0,numerator_width:0}).unwrap();
        assert_eq!(count.source_nbits_bits,32);
        assert_eq!(count.decoded_bits,DIFFICULTY_BITS);
    }

    #[test]
    fn daa_integer_isolated_false_inputs_and_rows(){
        let valid=Inputs{nbits:0x03000001,start_timestamp:0,end_timestamp:1};
        let q=fixed_q();
        for bad in [Inputs{nbits:0x03800001,..valid},Inputs{nbits:0,..valid},
            Inputs{nbits:0x23010000,..valid},Inputs{end_timestamp:0,..valid}]{
            let c=compile(Epoch::Legacy,&q,bad,true).unwrap();assert!(!nonzero_rows(&c).is_empty());
        }
        let overflow=compile(Epoch::Legacy,&q,Inputs{nbits:0x22400001,..valid},true).unwrap();
        let failed=nonzero_rows(&overflow);assert_eq!(failed.len(),1,"high compact bit must have isolated row");
        let mut omitted=overflow;omitted.circuit.as_mut().unwrap().terms.retain(|t|t.row!=failed[0]);
        assert!(nonzero_rows(&omitted).is_empty(),"omitting high-shift range row would accept alias");
        let mut c=compile(Epoch::Legacy,&q,valid,true).unwrap();
        let wire=c.output.quotient_magnitude[20];mutate(&mut c,wire);
        let failed=nonzero_rows(&c);assert_eq!(failed.len(),1,"wrong quotient should isolate product column");
        c.circuit.as_mut().unwrap().terms.retain(|t|t.row!=failed[0]);
        assert!(nonzero_rows(&c).is_empty(),"omitting quotient column would accept wrong quotient");
        let mut high=compile(Epoch::Legacy,&q,
            Inputs{nbits:0x22000001,start_timestamp:0,end_timestamp:i64::MIN},true).unwrap();
        assert!(nonzero_rows(&high).is_empty());
        let top_quotient_wire=high.output.quotient_magnitude[282];
        mutate(&mut high,top_quotient_wire);
        let failed=nonzero_rows(&high);
        assert_eq!(failed.len(),1,"top partial quotient limb must reach final product column");
        let mut c=compile(Epoch::Legacy,&q,valid,true).unwrap();
        let wire=c.output.remainder_negative;mutate(&mut c,wire);assert!(!nonzero_rows(&c).is_empty());
        let mut c=compile(Epoch::Legacy,&q,valid,true).unwrap();
        let wire=c.output.remainder_magnitude[0];mutate(&mut c,wire);assert!(!nonzero_rows(&c).is_empty());
        let mut c=compile(Epoch::Legacy,&q,valid,true).unwrap();
        let wire=c.carry_wires[0];mutate(&mut c,wire);assert!(!nonzero_rows(&c).is_empty());
        let mut c=compile(Epoch::Legacy,&q,valid,true).unwrap();
        c.witness[c.output.quotient_magnitude[0]]=Fr::from(2u64);assert!(!nonzero_rows(&c).is_empty());
        // A'=A with q'=q-1 and r'=r+|B|: product columns and carries remain
        // consistent, leaving only the strict remainder range as a guard.
        let mut range=compile(Epoch::Legacy,&q,Inputs{end_timestamp:13,..valid},true).unwrap();
        let old_q=read_bits(&range.witness,&range.output.quotient_magnitude);
        let old_r=read_bits(&range.witness,&range.output.remainder_magnitude);
        let denominator=read_bits(&range.witness,&range.output.denominator_magnitude);
        assert!(old_q>BigUint::zero() && denominator==BigUint::from(13u8));
        assert_eq!((&old_q%BigUint::from(4u8)),BigUint::from(3u8),
            "decrement must preserve both nonzero OR-chain witnesses");
        set_bits(&mut range.witness,&range.output.quotient_magnitude,&(old_q-BigUint::one()));
        set_bits(&mut range.witness,&range.output.remainder_magnitude,&(old_r+&denominator));
        let qlimbs=range.output.quotient_magnitude.len().div_ceil(16);
        let columns=qlimbs+4-1;
        let product_carry_count=(columns-1)*19;
        let carry_start=range.carry_wires.len()-product_carry_count;
        let mut carry=0u64;
        for column in 0..columns{
            let mut value=carry+witness_limb(&range.witness,&range.output.remainder_magnitude,column);
            for qi in 0..qlimbs{
                if column>=qi && column-qi<4{
                    value+=witness_limb(&range.witness,&range.output.quotient_magnitude,qi)
                        *witness_limb(&range.witness,&range.output.denominator_magnitude,column-qi);
                }
            }
            carry=value>>16;
            if column+1<columns{
                for bit in 0..19{
                    let wire=range.carry_wires[carry_start+column*19+bit];
                    range.witness[wire]=Fr::from((carry>>bit)&1);
                }
            }
        }
        assert_eq!(carry,0,"last partial product column must have no overflow");
        let trace=range.subtract_traces.last().unwrap().clone();
        assert!(trace.minuend_constant.is_none());
        let mut borrow=1i32;
        for i in 0..trace.differences.len(){
            let a=(range.witness[trace.minuend_wires[i]]==Fr::one()) as i32;
            let b=(range.witness[trace.subtrahend_wires[i]]==Fr::one()) as i32;
            let raw=a-b-borrow;let next=(raw<0) as i32;
            range.witness[trace.differences[i]]=Fr::from((raw&1) as u64);
            range.witness[trace.borrows[i]]=Fr::from(next as u64);borrow=next;
        }
        assert_eq!(borrow,1,"r=|B| must fail strict range");
        let failed=nonzero_rows(&range);
        assert_eq!(failed.len(),1,"arithmetic-consistent alternate division must fail only range");
        range.circuit.as_mut().unwrap().terms.retain(|t|t.row!=failed[0]);
        assert!(nonzero_rows(&range).is_empty(),"omitted strict range row accepts alternate division");
        for input in [Inputs{start_timestamp:1,end_timestamp:0,..valid},
            Inputs{start_timestamp:0,end_timestamp:i64::MIN,..valid}]{
            let mut signed=compile(Epoch::Legacy,&q,input,true).unwrap();
            assert!(nonzero_rows(&signed).is_empty());
            let qzero=read_bits(&signed.witness,&signed.output.quotient_magnitude).is_zero();
            let sign_wire=signed.output.quotient_negative;
            assert_eq!(signed.witness[sign_wire]==Fr::one(),!qzero);
            mutate(&mut signed,sign_wire);
            let failed=nonzero_rows(&signed);
            assert_eq!(failed.len(),2,"both quotient-sign predicate rows must reject");
            signed.circuit.as_mut().unwrap().terms.retain(|t|!failed.contains(&t.row));
            assert!(nonzero_rows(&signed).is_empty(),"omitted sign family accepts invalid sign");
        }
    }
    #[test]
    fn daa_integer_fresh_recomputed_borrow_mutant(){
        let mut c=compile(Epoch::Legacy,&fixed_q(),Inputs{nbits:0x03000001,start_timestamp:0,end_timestamp:1},true).unwrap();
        assert!(nonzero_rows(&c).is_empty());
        let trace=c.subtract_traces[0].clone();let constant=trace.minuend_constant.unwrap();
        c.witness[trace.initial_borrow]=Fr::one();let mut borrow=1i32;
        for i in 0..trace.differences.len(){
            let a=bit_value(&constant,i) as i32;
            let b=(c.witness[trace.subtrahend_wires[i]]==Fr::one()) as i32;
            let raw=a-b-borrow;let next=(raw<0) as i32;
            c.witness[trace.differences[i]]=Fr::from((raw&1) as u64);
            c.witness[trace.borrows[i]]=Fr::from(next as u64);borrow=next;
        }
        assert_eq!(borrow,0);
        let failed=nonzero_rows(&c);assert_eq!(failed.len(),1,"recomputed chain should fail only initial anchor");
        c.circuit.as_mut().unwrap().terms.retain(|t|t.row!=failed[0]);
        assert!(nonzero_rows(&c).is_empty(),"omitted initial-borrow anchor would accept forged comparison");
    }
}

/// Carry uses numeric decoded equality, including noncanonical compact aliases.
/// The shared result is Boolean and each raw compact has its own decoder.
pub(crate) struct CompiledCarry {
    pub count: Count,
    pub parent_nbits: [usize; 32],
    pub child_nbits: [usize; 32],
    pub decoded: Vec<usize>,
    pub decoder_rows: [std::ops::Range<usize>; 2],
    pub circuit: Option<Circuit>,
    pub witness: Vec<Fr>,
}

pub(crate) fn compile_carry(
    q: &BigUint,
    parent: u32,
    child: u32,
    materialize: bool,
) -> Result<CompiledCarry, String> {
    if q.is_zero() || q.bits() > DIFFICULTY_BITS as u64 {
        return Err("invalid carry difficulty bound".into());
    }
    let mut builder = Builder::new(materialize);
    let decoded = builder.bits_big(&decode_compact(parent), DIFFICULTY_BITS);
    let parent_nbits: [usize; 32] = builder.bits_u64(parent as u64, 32)
        .try_into().map_err(|_| "carry parent raw map")?;
    let child_nbits: [usize; 32] = builder.bits_u64(child as u64, 32)
        .try_into().map_err(|_| "carry child raw map")?;
    let start = builder.rows;
    decode_constraints_against(&mut builder, &parent_nbits, q, &decoded)?;
    let middle = builder.rows;
    decode_constraints_against(&mut builder, &child_nbits, q, &decoded)?;
    let end = builder.rows;
    builder.additional_decoded_bits = DIFFICULTY_BITS;
    // Largest residual is the 34-selector one-hot sum minus one (< 2^6).
    builder.note_column_bound(6);
    builder.pad();
    let (count, circuit, witness, _, _) = builder.finish(Categories {
        nbits: 64, timestamps: 0, instances: 0, numerator_width: 0,
    })?;
    if count.padded_input_bits > (1 << 20) || count.padded_rows > (1 << 17) {
        return Err("carry helper exceeds common local domain".into());
    }
    Ok(CompiledCarry {
        count, parent_nbits, child_nbits, decoded,
        decoder_rows: [start..middle, middle..end], circuit, witness,
    })
}

#[cfg(test)]
pub(crate) fn mainnet_short_legacy_test_inputs(profile:ShortLegacyProfile)->ShortLegacyInputs{
    let fixture:serde_json::Value=serde_json::from_str(
        include_str!("../fixtures/mainnet-daa-windows-v1.json")).expect("pinned RAW fixture JSON");
    let headers=fixture["headers"].as_array().expect("pinned RAW roster");
    let m=profile.count();let mut nbits=Vec::with_capacity(m);let mut timestamps=Vec::with_capacity(m+1);
    for index in 0..=m{
        let height=1024*(index as u32+1);
        let item=headers.iter().find(|item|item["height"].as_u64()==Some(height as u64))
            .expect("expected sample height in pinned RAW roster");
        let hex=item["raw_hex"].as_str().expect("sample RAW hex");
        assert_eq!(hex.len()%2,0,"sample RAW hex length");
        let raw=hex.as_bytes().chunks_exact(2).map(|pair|{
            u8::from_str_radix(std::str::from_utf8(pair).expect("RAW hex ASCII"),16)
                .expect("RAW hex byte")
        }).collect::<Vec<_>>();
        let header=ergo_header_core::Header::decode(&raw,None).expect("pinned sample RAW decode");
        assert_eq!(header.height,height,"sample RAW height");
        timestamps.push(i64::try_from(header.timestamp).expect("early sample timestamp fits i64"));
        if index>0{nbits.push(header.n_bits);}
    }
    ShortLegacyInputs{profile,nbits,timestamps}
}

#[cfg(test)]
mod short_legacy_tests{
    use super::*;
    fn fixture(profile:ShortLegacyProfile)->ShortLegacyInputs{
        mainnet_short_legacy_test_inputs(profile)
    }
    fn rows(compiled:&CompiledWindow)->Vec<Fr>{
        let circuit=compiled.circuit.as_ref().expect("materialized short Legacy A1");
        let mut rows=vec![Fr::zero();circuit.row_count];
        for term in &circuit.terms{rows[term.row]+=term.gate.evaluate(&compiled.witness);}
        rows
    }
    #[test]
    fn short_legacy_profiles_keep_exact_a1_shape_and_shared_timestamps(){
        let q=crate::daa_count::q();
        for profile in [ShortLegacyProfile::M3,ShortLegacyProfile::M4,ShortLegacyProfile::M5,
            ShortLegacyProfile::M6,ShortLegacyProfile::M7]{
            let input=fixture(profile);let m=profile.count();
            let compiled=compile_short_legacy(&q,input.clone(),true,|_,_|Ok(())).unwrap().0;
            assert_eq!(compiled.count.source_nbits_bits,m*32);
            assert_eq!(compiled.count.source_timestamp_bits,(m+1)*64);
            assert_eq!(compiled.count.decoded_bits,m*DIFFICULTY_BITS);
            assert_eq!(compiled.external.len(),m);assert_eq!(compiled.output.len(),m);
            assert!(compiled.count.terms<=MAX_MATERIAL_TERMS);
            assert!(rows(&compiled).iter().all(Zero::is_zero),"{profile:?}");
            for j in 0..m-1{
                assert_eq!(compiled.external[j].end_timestamp,compiled.external[j+1].start_timestamp,
                    "profile={profile:?}, adjacent ratio={j}");
            }
            let mut changed=input.clone();changed.nbits[0]=0x0300_0002;changed.timestamps[0]+=7;
            let first=compile_short_legacy(&q,input,false,|_,_|Ok(())).unwrap().0.count;
            let second=compile_short_legacy(&q,changed,false,|_,_|Ok(())).unwrap().0.count;
            assert_eq!(first.topology_blake2b256,second.topology_blake2b256,"{profile:?}");
            assert_eq!((first.live_bits,first.residual_rows,first.terms),
                (second.live_bits,second.residual_rows,second.terms),"{profile:?}");
        }
    }
    #[test]
    fn short_legacy_rejects_profile_shape_before_compilation(){
        let q=crate::daa_count::q();
        for profile in [ShortLegacyProfile::M3,ShortLegacyProfile::M4,ShortLegacyProfile::M5,
            ShortLegacyProfile::M6,ShortLegacyProfile::M7]{
            let mut missing_nbits=fixture(profile);missing_nbits.nbits.pop();
            assert!(compile_short_legacy(&q,missing_nbits,false,|_,_|Ok(())).err().expect("shape rejected")
                .contains("input shape"));
            let mut missing_time=fixture(profile);missing_time.timestamps.pop();
            assert!(compile_short_legacy(&q,missing_time,false,|_,_|Ok(())).err().expect("shape rejected")
                .contains("input shape"));
            let mut extra_nbits=fixture(profile);extra_nbits.nbits.push(0x0300_0001);
            assert!(compile_short_legacy(&q,extra_nbits,false,|_,_|Ok(())).err().expect("shape rejected")
                .contains("input shape"));
            let mut extra_time=fixture(profile);extra_time.timestamps.push(1_562_900_000_000);
            assert!(compile_short_legacy(&q,extra_time,false,|_,_|Ok(())).err().expect("shape rejected")
                .contains("input shape"));
        }
    }
}

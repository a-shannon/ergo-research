//! Eight A1 quotient aliases joined to the native eight-point slope.
//! Historical sample authentication, forecast, clamps and encoding are separate joins.
use ark_bn254::Fr;
use ark_ff::{One, PrimeField, Zero};
use num_bigint::{BigInt, BigUint, Sign};
use crate::daa_integer::{self, Builder, Epoch, OutputBits, WindowInputs};
use crate::gkr::Gate;

pub const PRECISION:u64=1_000_000_000;
pub const WEIGHTS:[i64;8]=[-28,-20,-12,-4,4,12,20,28];

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub struct Progress{pub live_bits:usize,pub rows:usize,pub terms:usize}
impl From<(usize,usize,usize)> for Progress{
    fn from(value:(usize,usize,usize))->Self{
        Self{live_bits:value.0,rows:value.1,terms:value.2}
    }
}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub struct Increment{
    pub before:Progress,pub after:Progress,
    pub added_live_bits:usize,pub added_rows:usize,pub added_terms:usize,
}
#[derive(Clone,Debug)]
pub struct SignedAlias{
    pub magnitude:Vec<usize>,pub negative:usize,
    pub magnitude_binding_rows:Vec<usize>,pub sign_binding_row:usize,
}
#[derive(Clone,Debug)]
pub struct RegressionOutput{
    pub aliases:Vec<SignedAlias>,
    pub positive_sum:Vec<usize>,pub negative_sum:Vec<usize>,
    pub sum_magnitude:Vec<usize>,pub sum_negative:usize,
    pub numerator:Vec<usize>,pub slope_magnitude:Vec<usize>,pub slope_negative:usize,
    pub remainder:Vec<usize>,pub remainder_negative:usize,
    pub division_carries:Vec<Vec<usize>>,
    pub remainder_range_final_borrow:usize,
}
pub struct CompiledRegression{
    pub joined:daa_integer::CompiledWindow,
    pub output:RegressionOutput,
    pub increment:Increment,
}

fn bit_value(value:&BigUint,index:usize)->bool{
    value.to_bytes_le().get(index/8).map(|byte|(byte>>(index%8))&1!=0).unwrap_or(false)
}
fn read_bits(builder:&Builder,wires:&[usize])->BigUint{
    let mut bytes=vec![0u8;wires.len().div_ceil(8)];
    for (i,&wire) in wires.iter().enumerate(){
        if builder.value(wire){bytes[i/8]|=1<<(i%8);}
    }
    BigUint::from_bytes_le(&bytes)
}
fn limb(builder:&Builder,wires:&[usize],column:usize)->u64{
    (0..16).fold(0u64,|value,i|{
        value|((wires.get(16*column+i).map(|&wire|builder.value(wire)).unwrap_or(false) as u64)<<i)
    })
}
fn limb_terms(wires:&[usize],column:usize,coefficient:Fr)->Vec<Gate>{
    (0..16).filter_map(|i|wires.get(16*column+i).copied()
        .map(|wire|Builder::linear(wire,coefficient*Fr::from(1u64<<i)))).collect()
}
fn full_terms(wires:&[usize],coefficient:Fr)->Vec<Gate>{
    wires.iter().enumerate().map(|(i,&wire)|Builder::linear(wire,coefficient*Fr::from(1u64<<i))).collect()
}
fn bound_checks(epoch:Epoch){
    let sum_width=epoch.numerator_bits()+7;
    let numerator_width=match epoch{Epoch::Legacy=>330,Epoch::Eip=>324};
    let multiplier=PRECISION*epoch.length();
    let sum_limit=BigUint::one()<<sum_width;
    let numerator_limit=&sum_limit*BigUint::from(multiplier);
    assert!(numerator_limit.bits()<=numerator_width+1);
    // Each signed weighted-sum side is <128*2^A1Width. For one 16-bit
    // column, 128 limbs plus an 8-bit carry fit in 24 bits. The public
    // constant multiplier and division columns fit respectively in 57
    // and 48 bits, including both sides of each signed residual.
    let limb=(1u128<<16)-1;
    let weighted=128*limb+255+limb+(255u128<<16);
    let constant_carry=(1u128<<(64-multiplier.leading_zeros()))-1;
    let constant=(multiplier as u128)*limb+constant_carry+limb+(constant_carry<<16);
    let denominator=336u128*(epoch.length() as u128).pow(2);
    let denominator_carry=(1u128<<(128-denominator.leading_zeros()))-1;
    let division=denominator*limb+denominator_carry+2*limb+(denominator_carry<<16);
    assert!(weighted<1u128<<25 && constant<1u128<<57 && division<1u128<<48);
    assert!(Fr::MODULUS_BIT_SIZE>57);
}
fn slope_width(epoch:Epoch)->usize{match epoch{Epoch::Legacy=>330,Epoch::Eip=>324}}
fn sum_width(epoch:Epoch)->usize{epoch.numerator_bits()+7}
fn denominator(epoch:Epoch)->u64{336*epoch.length()*epoch.length()}

fn alias_outputs(builder:&mut Builder,a1:&[OutputBits],override_one:Option<(usize,BigUint,bool)>)->Vec<SignedAlias>{
    let mut aliases=Vec::with_capacity(8);
    for (j,source) in a1.iter().enumerate(){
        let mut magnitude=read_bits(builder,&source.quotient_magnitude);
        let mut negative=builder.value(source.quotient_negative);
        if let Some((target,ref replacement,replacement_sign))=override_one{
            if target==j{magnitude=replacement.clone();negative=replacement_sign;}
        }
        let magnitude_bits=builder.bits_big(&magnitude,source.quotient_magnitude.len());
        let sign_bit=builder.bit(negative);
        let mut binding_rows=Vec::with_capacity(magnitude_bits.len());
        for (&alias,&original) in magnitude_bits.iter().zip(&source.quotient_magnitude){
            binding_rows.push(builder.progress().1);
            builder.row(vec![Builder::linear(alias,Fr::one()),Builder::linear(original,-Fr::one())]);
        }
        let sign_binding_row=builder.progress().1;
        builder.row(vec![Builder::linear(sign_bit,Fr::one()),
            Builder::linear(source.quotient_negative,-Fr::one())]);
        aliases.push(SignedAlias{magnitude:magnitude_bits,negative:sign_bit,
            magnitude_binding_rows:binding_rows,sign_binding_row});
    }
    aliases
}
fn signed_sums(builder:&Builder,sources:&[(&[usize],usize)],weights:&[i64])->(BigUint,BigUint){
    assert_eq!(sources.len(),weights.len());
    let mut positive=BigUint::zero();let mut negative=BigUint::zero();
    for (j,&(magnitude,sign)) in sources.iter().enumerate(){
        let value=read_bits(builder,magnitude)*BigUint::from(weights[j].unsigned_abs());
        let is_positive=(weights[j]>0) != builder.value(sign);
        if is_positive{positive+=value}else{negative+=value}
    }
    (positive,negative)
}
fn weighted_column(builder:&mut Builder,sources:&[(&[usize],usize)],weights:&[i64],sum:&[usize],positive:bool){
    let columns=sum.len().div_ceil(16);let mut carry=0u64;let mut previous=Vec::new();
    for column in 0..columns{
        let mut value=carry;
        let mut gates=full_terms(&previous,Fr::one());
        for (j,&(magnitude,sign)) in sources.iter().enumerate(){
            let weight=weights[j].unsigned_abs();
            let same_side=(weights[j]>0)==positive;
            let selected=if same_side{!builder.value(sign)}else{builder.value(sign)};
            if selected{value+=weight*limb(builder,magnitude,column);}
            for i in 0..16{
                if let Some(&wire)=magnitude.get(16*column+i){
                    let coefficient=Fr::from(weight*(1u64<<i));
                    if same_side{
                        gates.push(Builder::linear(wire,coefficient));
                        gates.push(Builder::product(sign,wire,-coefficient));
                    }else{
                        gates.push(Builder::product(sign,wire,coefficient));
                    }
                }
            }
        }
        carry=value>>16;
        assert!(carry<256,"weighted-sum carry range");
        let next=if column+1<columns{builder.bits_u64(carry,8)}else{Vec::new()};
        gates.extend(limb_terms(sum,column,-Fr::one()));
        gates.extend(full_terms(&next,-Fr::from(1u64<<16)));
        builder.row(gates);previous=next;
    }
    assert_eq!(carry,0,"weighted sum exceeds fixed width");
    builder.note_column_bound(25);
}
pub(crate) fn emit_signed_sum(builder:&mut Builder,sources:&[(&[usize],usize)],weights:&[i64],width:usize)
    ->Result<(Vec<usize>,usize,Vec<usize>,Vec<usize>),String>{
    let (positive,negative)=signed_sums(builder,sources,weights);
    if positive.bits()>width as u64 || negative.bits()>width as u64{
        return Err("signed sum exceeds fixed width".into());
    }
    let positive_sum=builder.bits_big(&positive,width);
    let negative_sum=builder.bits_big(&negative,width);
    weighted_column(builder,sources,weights,&positive_sum,true);
    weighted_column(builder,sources,weights,&negative_sum,false);
    let (magnitude,sign)=subtract_signed_sums(builder,&positive_sum,&negative_sum);
    Ok((magnitude,sign,positive_sum,negative_sum))
}
fn subtract_signed_sums(builder:&mut Builder,positive:&[usize],negative:&[usize])
    ->(Vec<usize>,usize){
    assert_eq!(positive.len(),negative.len());
    let initial=builder.bit(false);builder.assert_zero(initial);
    let mut borrow=initial;let mut difference=Vec::with_capacity(positive.len());
    for i in 0..positive.len(){
        let raw=(builder.value(positive[i]) as i32)
            -(builder.value(negative[i]) as i32)-(builder.value(borrow) as i32);
        let out=builder.bit((raw&1)!=0);let next=builder.bit(raw<0);
        builder.row(vec![Builder::linear(positive[i],Fr::one()),
            Builder::linear(negative[i],-Fr::one()),Builder::linear(borrow,-Fr::one()),
            Builder::linear(out,-Fr::one()),Builder::linear(next,Fr::from(2u64))]);
        difference.push(out);borrow=next;
    }
    let sign=borrow;
    let mut carry=builder.bit(true);builder.assert_one(carry);
    let mut twos=Vec::with_capacity(difference.len());
    for &bit in &difference{
        let inverse=builder.not(bit);
        let raw=builder.value(inverse) as u8+builder.value(carry) as u8;
        let out=builder.bit(raw&1!=0);let next=builder.bit(raw>=2);
        builder.row(vec![Builder::linear(inverse,Fr::one()),Builder::linear(carry,Fr::one()),
            Builder::linear(out,-Fr::one()),Builder::linear(next,-Fr::from(2u64))]);
        twos.push(out);carry=next;
    }
    let mut magnitude=Vec::with_capacity(difference.len());
    for (&plain,&flipped) in difference.iter().zip(&twos){
        let selected=if builder.value(sign){builder.value(flipped)}else{builder.value(plain)};
        let out=builder.bit(selected);
        builder.row(vec![Builder::linear(out,Fr::one()),Builder::linear(plain,-Fr::one()),
            Builder::product(sign,plain,Fr::one()),Builder::product(sign,flipped,-Fr::one())]);
        magnitude.push(out);
    }
    // The subtraction borrow is zero when both positive sums are equal.
    let nonzero=builder.nonzero_unasserted(&magnitude);
    builder.row(vec![Builder::linear(sign,Fr::one()),Builder::product(sign,nonzero,-Fr::one())]);
    (magnitude,sign)
}
fn multiply_public(builder:&mut Builder,input:&[usize],multiplier:u64,width:usize)->Vec<usize>{
    let product=read_bits(builder,input)*BigUint::from(multiplier);
    assert!(product.bits()<=width as u64);
    let out=builder.bits_big(&product,width);
    let columns=width.div_ceil(16);let mut carry=0u64;let mut previous=Vec::new();
    let carry_width=(64-multiplier.leading_zeros()) as usize;
    for column in 0..columns{
        let value=multiplier*limb(builder,input,column)+carry;
        carry=value>>16;assert!(carry<(1u64<<carry_width));
        let next=if column+1<columns{builder.bits_u64(carry,carry_width)}else{Vec::new()};
        let mut gates=limb_terms(input,column,Fr::from(multiplier));
        gates.extend(full_terms(&previous,Fr::one()));
        gates.extend(limb_terms(&out,column,-Fr::one()));
        gates.extend(full_terms(&next,-Fr::from(1u64<<16)));
        builder.row(gates);previous=next;
    }
    assert_eq!(carry,0,"regression numerator exceeds fixed width");
    builder.note_column_bound(57);
    out
}
fn divide_public(builder:&mut Builder,numerator:&[usize],denominator:u64)
    ->(Vec<usize>,Vec<usize>,Vec<Vec<usize>>,usize){
    divide_public_override(builder,numerator,denominator,None)
}
fn divide_public_override(builder:&mut Builder,numerator:&[usize],denominator:u64,
    override_witness:Option<(BigUint,BigUint)>)->(Vec<usize>,Vec<usize>,Vec<Vec<usize>>,usize){
    let value=read_bits(builder,numerator);let d=BigUint::from(denominator);
    let (quotient,remainder)=override_witness.unwrap_or_else(||(&value/&d,&value%&d));
    assert!(quotient.bits()<=numerator.len() as u64);
    let q=builder.bits_big(&quotient,numerator.len());
    let d_bits=(64-denominator.leading_zeros()) as usize;
    assert!(remainder.bits()<=d_bits as u64,"division remainder must fit declared bits");
    let carry_max=(1u128<<d_bits)-1;
    let limb_max=(1u128<<16)-1;
    let signed_column_abs=(denominator as u128)*limb_max+carry_max
        +2*limb_max+(carry_max<<16);
    assert!(signed_column_abs<1u128<<57 && Fr::MODULUS_BIT_SIZE>57);
    let r=builder.bits_big(&remainder,d_bits);
    let columns=q.len().div_ceil(16)+d_bits.div_ceil(16);
    let mut carry=0u64;let mut previous=Vec::new();let mut carries=Vec::with_capacity(columns-1);
    for column in 0..columns{
        let value=denominator*limb(builder,&q,column)+limb(builder,&r,column)+carry;
        carry=value>>16;assert!(carry<(1u64<<d_bits));
        let next=if column+1<columns{builder.bits_u64(carry,d_bits)}else{Vec::new()};
        let mut gates=limb_terms(&q,column,Fr::from(denominator));
        gates.extend(limb_terms(&r,column,Fr::one()));
        gates.extend(full_terms(&previous,Fr::one()));
        gates.extend(limb_terms(numerator,column,-Fr::one()));
        gates.extend(full_terms(&next,-Fr::from(1u64<<16)));
        builder.row(gates);
        if column+1<columns{carries.push(next.clone());}
        previous=next;
    }
    assert_eq!(carry,0,"division product overflow");
    let range_final=daa_integer::subtract_constant_with_final_borrow(builder,&(d-BigUint::one()),&r,false);
    builder.note_column_bound(57);
    (q,r,carries,range_final)
}
fn emit_tail(builder:&mut Builder,a1:&[OutputBits],epoch:Epoch,
    override_one:Option<(usize,BigUint,bool)>)->Result<(RegressionOutput,Increment),String>{
    if a1.len()!=8{return Err("regression requires eight A1 quotients".into());}
    bound_checks(epoch);
    let before=Progress::from(builder.progress());
    let aliases=alias_outputs(builder,a1,override_one);
    let sources=aliases.iter().map(|alias|(alias.magnitude.as_slice(),alias.negative)).collect::<Vec<_>>();
    let width=sum_width(epoch);
    let (sum_magnitude,sum_negative,positive_sum,negative_sum)
        =emit_signed_sum(builder,&sources,&WEIGHTS,width)?;
    let numerator=multiply_public(builder,&sum_magnitude,PRECISION*epoch.length(),slope_width(epoch));
    let (slope_magnitude,remainder,division_carries,remainder_range_final_borrow)
        =divide_public(builder,&numerator,denominator(epoch));
    let q_nonzero=builder.nonzero_unasserted(&slope_magnitude);
    let slope_negative=builder.and(sum_negative,q_nonzero);
    builder.row(vec![Builder::linear(slope_negative,Fr::one()),
        Builder::product(sum_negative,q_nonzero,-Fr::one())]);
    let r_nonzero=builder.nonzero_unasserted(&remainder);
    let remainder_negative=builder.and(sum_negative,r_nonzero);
    builder.row(vec![Builder::linear(remainder_negative,Fr::one()),
        Builder::product(sum_negative,r_nonzero,-Fr::one())]);
    let after=Progress::from(builder.progress());
    let increment=Increment{before,after,added_live_bits:after.live_bits-before.live_bits,
        added_rows:after.rows-before.rows,added_terms:after.terms-before.terms};
    Ok((RegressionOutput{aliases,positive_sum,negative_sum,sum_magnitude,sum_negative,
        numerator,slope_magnitude,slope_negative,remainder,remainder_negative,
        division_carries,remainder_range_final_borrow},increment))
}
fn compile_extended<T,F>(epoch:Epoch,q:&BigUint,input:WindowInputs,materialize:bool,
    override_one:Option<(usize,BigUint,bool)>,extend:F)->Result<(CompiledRegression,T),String>
where F:FnOnce(&mut Builder,&RegressionOutput)->Result<T,String>{
    let (joined,((output,increment),extra))=daa_integer::compile_eight_extended(
        epoch,q,input,materialize,|builder,a1|{
            let pair=emit_tail(builder,a1,epoch,override_one)?;
            let extra=extend(builder,&pair.0)?;
            Ok((pair,extra))
        })?;
    Ok((CompiledRegression{joined,output,increment},extra))
}
fn compile_inner(epoch:Epoch,q:&BigUint,input:WindowInputs,materialize:bool,
    override_one:Option<(usize,BigUint,bool)>)->Result<CompiledRegression,String>{
    compile_extended(epoch,q,input,materialize,override_one,|_,_|Ok(())).map(|(compiled,())|compiled)
}
pub fn compile(epoch:Epoch,q:&BigUint,input:WindowInputs,materialize:bool)
    ->Result<CompiledRegression,String>{
    compile_inner(epoch,q,input,materialize,None)
}
pub fn residuals(compiled:&CompiledRegression)->Result<Vec<Fr>,String>{
    let circuit=compiled.joined.circuit.as_ref().ok_or("count-only regression")?;
    let mut rows=vec![Fr::zero();circuit.row_count];
    for term in &circuit.terms{rows[term.row]+=term.gate.evaluate(&compiled.joined.witness);}
    Ok(rows)
}
/// This oracle intentionally uses the native unsimplified sum formula.
pub fn native_slope_oracle(x0:i64,epoch:Epoch,values:&[BigInt;8])->BigInt{
    let e=epoch.length() as i64;
    let xs:Vec<BigInt>=(0..8).map(|i|BigInt::from(x0+i as i64*e)).collect();
    let xy_sum:BigInt=xs.iter().zip(values).map(|(x,y)|x*y).sum();
    let x_sum:BigInt=xs.iter().cloned().sum();
    let x2_sum:BigInt=xs.iter().map(|x|x*x).sum();
    let y_sum:BigInt=values.iter().cloned().sum();
    let size=BigInt::from(8u8);
    let numerator=(xy_sum*&size-&x_sum*y_sum)*BigInt::from(PRECISION);
    let denominator=x2_sum*size-&x_sum*&x_sum;
    numerator/denominator
}
pub fn signed_value(witness:&[Fr],magnitude:&[usize],negative:usize)->BigInt{
    let mut bytes=vec![0u8;magnitude.len().div_ceil(8)];
    for (i,&wire) in magnitude.iter().enumerate(){if witness[wire]==Fr::one(){bytes[i/8]|=1<<(i%8);}}
    let sign=if witness[negative]==Fr::one(){Sign::Minus}else{Sign::Plus};
    BigInt::from_biguint(sign,BigUint::from_bytes_le(&bytes))
}

pub const PREDICTION_WIDTH:usize=387;
#[derive(Clone,Debug)]
pub struct SignedDivisionTrace{
    pub quotient_magnitude:Vec<usize>,pub quotient_negative:usize,
    pub remainder_magnitude:Vec<usize>,pub remainder_negative:usize,
    pub carries:Vec<Vec<usize>>,pub range_final_borrow:usize,
}
#[derive(Clone,Copy,Debug)]
pub struct PredictionInput{pub window:WindowInputs,pub x0:u32}
#[derive(Clone,Debug)]
pub struct PredictionOutput{
    pub x0_bits:Vec<usize>,pub grid_x:Vec<Vec<usize>>,
    pub b_alias:SignedAlias,
    pub sum_x:Vec<usize>,pub y_magnitude:Vec<usize>,pub y_negative:usize,
    pub py_magnitude:Vec<usize>,pub b_sum_x_magnitude:Vec<usize>,
    pub x_magnitude:Vec<usize>,pub x_negative:usize,
    pub a_magnitude:Vec<usize>,pub a_negative:usize,
    pub a_remainder:Vec<usize>,pub a_remainder_negative:usize,
    pub a_division_carries:Vec<Vec<usize>>,pub a_range_final_borrow:usize,
    pub point_twos:Vec<usize>,pub point_magnitude:Vec<usize>,pub point_negative:usize,
    pub point_binding_rows:Vec<usize>,
    pub b_point_magnitude:Vec<usize>,
    pub term_magnitude:Vec<usize>,pub term_negative:usize,
    pub term_remainder:Vec<usize>,pub term_remainder_negative:usize,
    pub term_division_carries:Vec<Vec<usize>>,pub term_range_final_borrow:usize,
    pub prediction_magnitude:Vec<usize>,pub prediction_negative:usize,
}
pub struct CompiledPrediction{
    pub joined:CompiledRegression,pub output:PredictionOutput,pub increment:Increment,
}
fn prediction_bounds(epoch:Epoch){
    let qmax=(BigUint::one()<<epoch.numerator_bits())-BigUint::one();
    let ymax=BigUint::from(8u8)*&qmax;
    let grid_max=(i32::MAX as u64)-7*epoch.length();
    let lmax=8*grid_max+28*epoch.length();
    let bmax=(BigUint::one()<<slope_width(epoch))-BigUint::one();
    let pymax=&ymax*BigUint::from(PRECISION);
    let blmax=&bmax*BigUint::from(lmax);
    let xmax=&pymax+&blmax;
    let amax=&xmax/BigUint::from(8*PRECISION);
    let point_bound=BigUint::from(1u8)<<31usize;
    let bpointmax=&bmax*&point_bound;
    let termmax=&bpointmax/BigUint::from(PRECISION);
    let predictionmax=amax+termmax;
    assert!(ymax.bits()<=286 && lmax<(1u64<<34));
    assert!(pymax.bits()<=316 && blmax.bits()<=364 && xmax.bits()<=365);
    assert!(bpointmax.bits()<=361 && predictionmax.bits()<=333);
    assert!(predictionmax.bits()<PREDICTION_WIDTH as u64 && Fr::MODULUS_BIT_SIZE>57);
}
fn affine_public(builder:&mut Builder,source:&[usize],coefficient:u64,constant:u64,width:usize)
    ->Vec<usize>{
    let value=read_bits(builder,source)*BigUint::from(coefficient)+BigUint::from(constant);
    let output=builder.bits_big(&value,width);
    let columns=width.div_ceil(16);let mut carry=0u64;let mut previous=Vec::new();
    let carry_width=(64-coefficient.leading_zeros()) as usize+1;
    for column in 0..columns{
        let constant_limb=if column==0{constant&0xffff}
            else if column==1{(constant>>16)&0xffff}else{0};
        let value=coefficient*limb(builder,source,column)+constant_limb+carry;
        carry=value>>16;
        assert!(carry<(1u64<<carry_width));
        let next=if column+1<columns{builder.bits_u64(carry,carry_width)}else{Vec::new()};
        let mut gates=limb_terms(source,column,Fr::from(coefficient));
        if constant_limb!=0{gates.push(Builder::constant(Fr::from(constant_limb)));}
        gates.extend(full_terms(&previous,Fr::one()));
        gates.extend(limb_terms(&output,column,-Fr::one()));
        gates.extend(full_terms(&next,-Fr::from(1u64<<16)));
        builder.row(gates);previous=next;
    }
    builder.note_column_bound(57);
    output
}
fn variable_product(builder:&mut Builder,left:&[usize],right:&[usize],width:usize)->Vec<usize>{
    let product=read_bits(builder,left)*read_bits(builder,right);
    assert!(product.bits()<=width as u64);
    let output=builder.bits_big(&product,width);
    let columns=width.div_ceil(16);let mut carry=0u64;let mut previous=Vec::new();
    let left_limbs=left.len().div_ceil(16);let right_limbs=right.len().div_ceil(16);
    assert!(right_limbs<=3,"variable multiplier has at most three limbs");
    let limb_max=(1u128<<16)-1;
    let carry_max=(1u128<<19)-1;
    assert!(3*limb_max*limb_max+carry_max+limb_max+(carry_max<<16)<1u128<<36);
    for column in 0..columns{
        let mut value=carry;let mut gates=full_terms(&previous,Fr::one());
        for li in 0..left_limbs{
            if column>=li && column-li<right_limbs{
                let ri=column-li;
                value+=limb(builder,left,li)*limb(builder,right,ri);
                for i in 0..16{if let Some(&a)=left.get(16*li+i){
                    for j in 0..16{if let Some(&b)=right.get(16*ri+j){
                        gates.push(Builder::product(a,b,Fr::from(1u64<<(i+j))));
                    }}
                }}
            }
        }
        carry=value>>16;assert!(carry<(1u64<<19));
        let next=if column+1<columns{builder.bits_u64(carry,19)}else{Vec::new()};
        gates.extend(limb_terms(&output,column,-Fr::one()));
        gates.extend(full_terms(&next,-Fr::from(1u64<<16)));
        builder.row(gates);previous=next;
    }
    assert_eq!(carry,0,"variable product exceeds fixed width");
    builder.note_column_bound(36);
    output
}
fn twos_magnitude(builder:&mut Builder,twos:&[usize],override_point:Option<(BigUint,bool)>)
    ->(Vec<usize>,usize,Vec<usize>){
    let sign=twos[twos.len()-1];
    let mut carry=builder.bit(true);builder.assert_one(carry);
    let mut negative=Vec::with_capacity(twos.len());
    for &bit in twos{
        let inverse=builder.not(bit);
        let raw=builder.value(inverse) as u8+builder.value(carry) as u8;
        let out=builder.bit(raw&1!=0);let next=builder.bit(raw>=2);
        builder.row(vec![Builder::linear(inverse,Fr::one()),Builder::linear(carry,Fr::one()),
            Builder::linear(out,-Fr::one()),Builder::linear(next,-Fr::from(2u64))]);
        negative.push(out);carry=next;
    }
    let mut magnitude=Vec::with_capacity(twos.len());let mut binding_rows=Vec::with_capacity(twos.len()+1);
    for (i,(&plain,&flipped)) in twos.iter().zip(&negative).enumerate(){
        let normal=if builder.value(sign){builder.value(flipped)}else{builder.value(plain)};
        let assigned=override_point.as_ref().map(|(value,_)|bit_value(value,i)).unwrap_or(normal);
        let out=builder.bit(assigned);
        binding_rows.push(builder.progress().1);
        builder.row(vec![Builder::linear(out,Fr::one()),Builder::linear(plain,-Fr::one()),
            Builder::product(sign,plain,Fr::one()),Builder::product(sign,flipped,-Fr::one())]);
        magnitude.push(out);
    }
    let assigned_sign=override_point.as_ref().map(|(_,negative)|*negative).unwrap_or(builder.value(sign));
    let sign_alias=builder.bit(assigned_sign);
    binding_rows.push(builder.progress().1);
    builder.row(vec![Builder::linear(sign_alias,Fr::one()),Builder::linear(sign,-Fr::one())]);
    (magnitude,sign_alias,binding_rows)
}
fn bind_signed(builder:&mut Builder,magnitude:&[usize],negative:usize,
    override_value:Option<(BigUint,bool)>)->SignedAlias{
    let actual=read_bits(builder,magnitude);
    let assigned=override_value.as_ref().map(|(value,_)|value).unwrap_or(&actual);
    let assigned_sign=override_value.as_ref().map(|(_,sign)|*sign).unwrap_or(builder.value(negative));
    let bits=builder.bits_big(assigned,magnitude.len());let sign=builder.bit(assigned_sign);
    let mut rows=Vec::with_capacity(bits.len());
    for (&alias,&source) in bits.iter().zip(magnitude){
        rows.push(builder.progress().1);
        builder.row(vec![Builder::linear(alias,Fr::one()),Builder::linear(source,-Fr::one())]);
    }
    let sign_row=builder.progress().1;
    builder.row(vec![Builder::linear(sign,Fr::one()),Builder::linear(negative,-Fr::one())]);
    SignedAlias{magnitude:bits,negative:sign,magnitude_binding_rows:rows,sign_binding_row:sign_row}
}
fn signed_division_signs(builder:&mut Builder,negative:usize,q:&[usize],r:&[usize])
    ->(usize,usize){
    let q_nonzero=builder.nonzero_unasserted(q);
    let qsign=builder.and(negative,q_nonzero);
    builder.row(vec![Builder::linear(qsign,Fr::one()),
        Builder::product(negative,q_nonzero,-Fr::one())]);
    let r_nonzero=builder.nonzero_unasserted(r);
    let rsign=builder.and(negative,r_nonzero);
    builder.row(vec![Builder::linear(rsign,Fr::one()),
        Builder::product(negative,r_nonzero,-Fr::one())]);
    (qsign,rsign)
}
fn emit_prediction(builder:&mut Builder,regression:&RegressionOutput,epoch:Epoch,x0:u32,
    override_b:Option<(BigUint,bool)>,override_point:Option<(BigUint,bool)>,
    override_a_division:Option<(BigUint,BigUint)>,override_term_division:Option<(BigUint,BigUint)>)
    ->Result<(PredictionOutput,Increment),String>{
    prediction_bounds(epoch);
    let before=Progress::from(builder.progress());
    let x0_bits=builder.bits_u64(x0 as u64,32);
    builder.assert_zero(x0_bits[31]);
    let mut grid_x=Vec::with_capacity(8);
    for i in 0..8{
        let x=affine_public(builder,&x0_bits,1,i as u64*epoch.length(),33);
        builder.assert_zero(x[31]);builder.assert_zero(x[32]);
        grid_x.push(x);
    }
    let sum_x=affine_public(builder,&x0_bits,8,28*epoch.length(),35);
    builder.assert_zero(sum_x[34]);
    let b_alias=bind_signed(builder,&regression.slope_magnitude,regression.slope_negative,override_b);
    let alias_sources=regression.aliases.iter()
        .map(|alias|(alias.magnitude.as_slice(),alias.negative)).collect::<Vec<_>>();
    let (y_magnitude,y_negative,_,_)=emit_signed_sum(builder,&alias_sources,&[1;8],
        epoch.numerator_bits()+3)?;
    let py_magnitude=multiply_public(builder,&y_magnitude,PRECISION,PREDICTION_WIDTH);
    let b_sum_x_magnitude=variable_product(builder,&b_alias.magnitude,&sum_x,PREDICTION_WIDTH);
    let x_sources=[(py_magnitude.as_slice(),y_negative),
        (b_sum_x_magnitude.as_slice(),b_alias.negative)];
    let (x_magnitude,x_negative,_,_)=emit_signed_sum(builder,&x_sources,&[1,-1],PREDICTION_WIDTH)?;
    // For integers |X|=8Pq+r, 0<=r<8P:
    // trunc0(trunc0(X/8)/P)=sign(X)*q. The native two divisions forming a
    // are therefore one constrained quotient, unlike the later forecast division.
    let (a_magnitude,a_remainder,a_division_carries,a_range_final_borrow)
        =divide_public_override(builder,&x_magnitude,8*PRECISION,override_a_division);
    let (a_negative,a_remainder_negative)
        =signed_division_signs(builder,x_negative,&a_magnitude,&a_remainder);
    let point_twos=affine_public(builder,&x0_bits,1,8*epoch.length(),32);
    let (point_magnitude,point_negative,point_binding_rows)
        =twos_magnitude(builder,&point_twos,override_point);
    let b_point_magnitude=variable_product(builder,&b_alias.magnitude,
        &point_magnitude,PREDICTION_WIDTH);
    let sign_xor=builder.bit(builder.value(b_alias.negative)^builder.value(point_negative));
    builder.row(vec![Builder::linear(sign_xor,Fr::one()),
        Builder::linear(b_alias.negative,-Fr::one()),
        Builder::linear(point_negative,-Fr::one()),
        Builder::product(b_alias.negative,point_negative,Fr::from(2u64))]);
    let product_nonzero=builder.nonzero_unasserted(&b_point_magnitude);
    let product_negative=builder.and(sign_xor,product_nonzero);
    let (term_magnitude,term_remainder,term_division_carries,term_range_final_borrow)
        =divide_public_override(builder,&b_point_magnitude,PRECISION,override_term_division);
    let (term_negative,term_remainder_negative)
        =signed_division_signs(builder,product_negative,&term_magnitude,&term_remainder);
    let prediction_sources=[(a_magnitude.as_slice(),a_negative),
        (term_magnitude.as_slice(),term_negative)];
    let (prediction_magnitude,prediction_negative,_,_)
        =emit_signed_sum(builder,&prediction_sources,&[1,1],PREDICTION_WIDTH)?;
    let after=Progress::from(builder.progress());
    let increment=Increment{before,after,added_live_bits:after.live_bits-before.live_bits,
        added_rows:after.rows-before.rows,added_terms:after.terms-before.terms};
    Ok((PredictionOutput{x0_bits,grid_x,b_alias,sum_x,y_magnitude,y_negative,py_magnitude,
        b_sum_x_magnitude,x_magnitude,x_negative,a_magnitude,a_negative,a_remainder,
        a_remainder_negative,a_division_carries,a_range_final_borrow,point_twos,point_binding_rows,
        point_magnitude,point_negative,b_point_magnitude,term_magnitude,term_negative,
        term_remainder,term_remainder_negative,term_division_carries,term_range_final_borrow,
        prediction_magnitude,prediction_negative},increment))
}
fn compile_prediction_inner(epoch:Epoch,q:&BigUint,input:PredictionInput,materialize:bool,
    override_y:Option<(usize,BigUint,bool)>,override_b:Option<(BigUint,bool)>,
    override_point:Option<(BigUint,bool)>,override_a_division:Option<(BigUint,BigUint)>,
    override_term_division:Option<(BigUint,BigUint)>)
    ->Result<CompiledPrediction,String>{
    let (joined,(output,increment))=compile_extended(epoch,q,input.window,materialize,override_y,
        |builder,regression|emit_prediction(builder,regression,epoch,input.x0,override_b,override_point,
            override_a_division,override_term_division))?;
    Ok(CompiledPrediction{joined,output,increment})
}
pub fn compile_prediction(epoch:Epoch,q:&BigUint,input:PredictionInput,materialize:bool)
    ->Result<CompiledPrediction,String>{
    compile_prediction_inner(epoch,q,input,materialize,None,None,None,None,None)
}
/// Continue the same A1/A2/A3 emitter before its single final padding step.
pub(crate) fn compile_prediction_extended<T,F>(epoch:Epoch,q:&BigUint,input:PredictionInput,
    materialize:bool,extend:F)->Result<(CompiledPrediction,T),String>
where F:FnOnce(&mut Builder,&[OutputBits],&RegressionOutput,&PredictionOutput)->Result<T,String>{
    let (joined,((regression,prediction),extra))=daa_integer::compile_eight_extended(
        epoch,q,input.window,materialize,|builder,a1|{
            let regression=emit_tail(builder,a1,epoch,None)?;
            let prediction=emit_prediction(builder,&regression.0,epoch,input.x0,None,None,None,None)?;
            let extra=extend(builder,a1,&regression.0,&prediction.0)?;
            Ok(((regression,prediction),extra))
        })?;
    let regression=CompiledRegression{joined,output:regression.0,increment:regression.1};
    let prediction=CompiledPrediction{joined:regression,output:prediction.0,increment:prediction.1};
    Ok((prediction,extra))
}
pub fn prediction_residuals(compiled:&CompiledPrediction)->Result<Vec<Fr>,String>{
    residuals(&compiled.joined)
}
/// Independent, unsimplified native interpolation oracle with two divisions for a.
pub fn native_prediction_oracle(x0:i64,epoch:Epoch,values:&[BigInt;8])->(BigInt,BigInt,BigInt){
    let e=epoch.length() as i64;
    let xs:Vec<BigInt>=(0..8).map(|i|BigInt::from(x0+i as i64*e)).collect();
    let xy_sum:BigInt=xs.iter().zip(values).map(|(x,y)|x*y).sum();
    let x_sum:BigInt=xs.iter().cloned().sum();
    let x2_sum:BigInt=xs.iter().map(|x|x*x).sum();
    let y_sum:BigInt=values.iter().cloned().sum();
    let b=(BigInt::from(8)*xy_sum-&x_sum*&y_sum)*BigInt::from(PRECISION)
        /(BigInt::from(8)*x2_sum-&x_sum*&x_sum);
    let a=((y_sum*BigInt::from(PRECISION)-&b*&x_sum)/BigInt::from(8))
        /BigInt::from(PRECISION);
    let point=(x0+8*e) as i32;
    let prediction=&a+&b*BigInt::from(point)/BigInt::from(PRECISION);
    (b,a,prediction)
}

pub(crate) mod short_legacy{
    use super::*;
    use crate::daa_integer::{ShortLegacyInputs,ShortLegacyProfile};

    fn parameters(profile:ShortLegacyProfile)->(&'static [i64],u64){match profile{
        ShortLegacyProfile::M3=>(&[-1,0,1],2048),ShortLegacyProfile::M4=>(&[-3,-1,1,3],10240),
        ShortLegacyProfile::M5=>(&[-2,-1,0,1,2],10240),ShortLegacyProfile::M6=>(&[-5,-3,-1,1,3,5],35840),
        ShortLegacyProfile::M7=>(&[-3,-2,-1,0,1,2,3],28672),}}
    fn bounds(profile:ShortLegacyProfile){
        let (weights,denom)=parameters(profile);let weight_sum:u64=weights.iter().map(|w|w.unsigned_abs()).sum();
        let y=(BigUint::one()<<283usize)-BigUint::one();let sum=&y*BigUint::from(weight_sum);
        let numerator=&sum*BigUint::from(PRECISION);let d_bits=(64-denom.leading_zeros()) as usize;
        let limb=(1u128<<16)-1;let carry=(1u128<<d_bits)-1;
        let division=denom as u128*limb+carry+2*limb+(carry<<16);
        assert_eq!(weights.len(),profile.count());
        assert!(weight_sum<=18&&sum.bits()<=288&&numerator.bits()<=318);
        assert!(division<1u128<<57&&Fr::MODULUS_BIT_SIZE>57);
    }
    fn slope(builder:&mut Builder,a1:&[OutputBits],profile:ShortLegacyProfile,
        override_one:Option<(usize,BigUint,bool)>)
        ->Result<(RegressionOutput,Increment),String>{
        let (weights,denom)=parameters(profile);
        if a1.len()!=profile.count(){return Err("short Legacy regression profile count".into());}
        bounds(profile);let before=Progress::from(builder.progress());let aliases=alias_outputs(builder,a1,override_one);
        let sources=aliases.iter().map(|a|(a.magnitude.as_slice(),a.negative)).collect::<Vec<_>>();
        let (sum_magnitude,sum_negative,positive_sum,negative_sum)=emit_signed_sum(builder,&sources,weights,288)?;
        let numerator=multiply_public(builder,&sum_magnitude,PRECISION,318);
        let (slope_magnitude,remainder,division_carries,remainder_range_final_borrow)
            =divide_public(builder,&numerator,denom);
        let (slope_negative,remainder_negative)=signed_division_signs(builder,sum_negative,&slope_magnitude,&remainder);
        let after=Progress::from(builder.progress());let increment=Increment{before,after,
            added_live_bits:after.live_bits-before.live_bits,added_rows:after.rows-before.rows,
            added_terms:after.terms-before.terms};
        Ok((RegressionOutput{aliases,positive_sum,negative_sum,sum_magnitude,sum_negative,numerator,
            slope_magnitude,slope_negative,remainder,remainder_negative,division_carries,remainder_range_final_borrow},increment))
    }
    fn prediction(builder:&mut Builder,regression:&RegressionOutput,profile:ShortLegacyProfile,
        override_point:Option<(BigUint,bool)>)
        ->Result<(PredictionOutput,Increment,SignedDivisionTrace),String>{
        let m=profile.count();if regression.aliases.len()!=m{return Err("short Legacy prediction alias count".into());}
        let before=Progress::from(builder.progress());let x0_bits=builder.bits_u64(2048,32);
        for (i,&wire) in x0_bits.iter().enumerate(){if (2048u32>>i)&1==0{builder.assert_zero(wire)}else{builder.assert_one(wire)}}
        let mut grid_x=Vec::with_capacity(m);
        for i in 0..m{let x=affine_public(builder,&x0_bits,1,i as u64*1024,33);
            builder.assert_zero(x[31]);builder.assert_zero(x[32]);grid_x.push(x);}
        let sum_x=affine_public(builder,&x0_bits,m as u64,1024*m as u64*(m as u64-1)/2,35);
        builder.assert_zero(sum_x[34]);
        let b_alias=bind_signed(builder,&regression.slope_magnitude,regression.slope_negative,None);
        let sources=regression.aliases.iter().map(|a|(a.magnitude.as_slice(),a.negative)).collect::<Vec<_>>();
        let (y_magnitude,y_negative,_,_)=emit_signed_sum(builder,&sources,&vec![1;m],288)?;
        let py_magnitude=multiply_public(builder,&y_magnitude,PRECISION,PREDICTION_WIDTH);
        let b_sum_x_magnitude=variable_product(builder,&b_alias.magnitude,&sum_x,PREDICTION_WIDTH);
        let x_sources=[(py_magnitude.as_slice(),y_negative),(b_sum_x_magnitude.as_slice(),b_alias.negative)];
        let (x_magnitude,x_negative,_,_)=emit_signed_sum(builder,&x_sources,&[1,-1],PREDICTION_WIDTH)?;
        let (count_q,count_r,count_carries,count_range)=divide_public(builder,&x_magnitude,m as u64);
        let (count_q_negative,count_r_negative)=signed_division_signs(builder,x_negative,&count_q,&count_r);
        let intercept_count_division=SignedDivisionTrace{quotient_magnitude:count_q.clone(),
            quotient_negative:count_q_negative,remainder_magnitude:count_r,remainder_negative:count_r_negative,
            carries:count_carries,range_final_borrow:count_range};
        let (a_magnitude,a_remainder,a_division_carries,a_range_final_borrow)
            =divide_public(builder,&count_q,PRECISION);
        let (a_negative,a_remainder_negative)=signed_division_signs(builder,count_q_negative,&a_magnitude,&a_remainder);
        let point_twos=affine_public(builder,&x0_bits,1,m as u64*1024,32);
        let (point_magnitude,point_negative,point_binding_rows)=twos_magnitude(builder,&point_twos,override_point);
        let b_point_magnitude=variable_product(builder,&b_alias.magnitude,&point_magnitude,PREDICTION_WIDTH);
        let sign_xor=builder.bit(builder.value(b_alias.negative)^builder.value(point_negative));
        builder.row(vec![Builder::linear(sign_xor,Fr::one()),Builder::linear(b_alias.negative,-Fr::one()),
            Builder::linear(point_negative,-Fr::one()),Builder::product(b_alias.negative,point_negative,Fr::from(2u64))]);
        let product_nonzero=builder.nonzero_unasserted(&b_point_magnitude);let product_negative=builder.and(sign_xor,product_nonzero);
        let (term_magnitude,term_remainder,term_division_carries,term_range_final_borrow)
            =divide_public(builder,&b_point_magnitude,PRECISION);
        let (term_negative,term_remainder_negative)=signed_division_signs(builder,product_negative,&term_magnitude,&term_remainder);
        let (prediction_magnitude,prediction_negative,_,_)=emit_signed_sum(builder,
            &[(a_magnitude.as_slice(),a_negative),(term_magnitude.as_slice(),term_negative)],&[1,1],PREDICTION_WIDTH)?;
        let after=Progress::from(builder.progress());let increment=Increment{before,after,
            added_live_bits:after.live_bits-before.live_bits,added_rows:after.rows-before.rows,
            added_terms:after.terms-before.terms};
        let output=PredictionOutput{x0_bits,grid_x,b_alias,sum_x,y_magnitude,y_negative,py_magnitude,
            b_sum_x_magnitude,x_magnitude,x_negative,a_magnitude,a_negative,a_remainder,a_remainder_negative,
            a_division_carries,a_range_final_borrow,point_twos,point_magnitude,point_negative,point_binding_rows,b_point_magnitude,term_magnitude,
            term_negative,term_remainder,term_remainder_negative,term_division_carries,term_range_final_borrow,
            prediction_magnitude,prediction_negative};
        Ok((output,increment,intercept_count_division))
    }
    pub(crate) fn compile_extended<T,F>(q:&BigUint,input:ShortLegacyInputs,materialize:bool,extend:F)
        ->Result<(CompiledPrediction,T),String>
    where F:FnOnce(&mut Builder,&[OutputBits],&RegressionOutput,&PredictionOutput,&SignedDivisionTrace)->Result<T,String>{
        compile_extended_inner(q,input,materialize,None,None,extend)
    }
    #[cfg(test)]
    pub(crate) fn compile_alias_override(q:&BigUint,input:ShortLegacyInputs,materialize:bool,
        target:usize,magnitude:BigUint,negative:bool)->Result<CompiledPrediction,String>{
        compile_extended_inner(q,input,materialize,Some((target,magnitude,negative)),None,
            |_,_,_,_,_|Ok(())).map(|(compiled,())|compiled)
    }
    #[cfg(test)]
    pub(crate) fn compile_point_override(q:&BigUint,input:ShortLegacyInputs,materialize:bool,
        magnitude:BigUint,negative:bool)->Result<CompiledPrediction,String>{
        compile_extended_inner(q,input,materialize,None,Some((magnitude,negative)),
            |_,_,_,_,_|Ok(())).map(|(compiled,())|compiled)
    }
    fn compile_extended_inner<T,F>(q:&BigUint,input:ShortLegacyInputs,materialize:bool,
        override_one:Option<(usize,BigUint,bool)>,override_point:Option<(BigUint,bool)>,extend:F)
        ->Result<(CompiledPrediction,T),String>
    where F:FnOnce(&mut Builder,&[OutputBits],&RegressionOutput,&PredictionOutput,&SignedDivisionTrace)->Result<T,String>{
        let profile=input.profile;
        let (joined,((regression,prediction),extra))=daa_integer::compile_short_legacy(q,input,materialize,
            |builder,a1|{let regression=slope(builder,a1,profile,override_one)?;let (prediction,prediction_increment,trace)=prediction(builder,&regression.0,profile,override_point)?;
                let extra=extend(builder,a1,&regression.0,&prediction,&trace)?;
                Ok(((regression,(prediction,prediction_increment)),extra))})?;
        let joined=CompiledRegression{joined,output:regression.0,increment:regression.1};
        Ok((CompiledPrediction{joined,output:prediction.0,increment:prediction.1},extra))
    }
    pub(crate) fn compile(q:&BigUint,input:ShortLegacyInputs,materialize:bool)->Result<CompiledPrediction,String>{
        compile_extended(q,input,materialize,|_,_,_,_,_|Ok(())).map(|(compiled,())|compiled)
    }
    /// Native formula kept unsimplified so reduced profile constants are never their own oracle.
    pub(crate) fn native_oracle(values:&[BigInt])->Result<(BigInt,BigInt,BigInt),String>{
        if !(3..=7).contains(&values.len()){return Err("short Legacy oracle count".into());}
        let xs=(0..values.len()).map(|i|BigInt::from(2048+1024*i)).collect::<Vec<_>>();
        let m=BigInt::from(values.len());let p=BigInt::from(PRECISION);
        let sx:BigInt=xs.iter().cloned().sum();let sy:BigInt=values.iter().cloned().sum();
        let sxx:BigInt=xs.iter().map(|x|x*x).sum();let sxy:BigInt=xs.iter().zip(values).map(|(x,y)|x*y).sum();
        let slope=((&m*&sxy-&sx*&sy)*&p)/(&m*&sxx-&sx*&sx);
        let intercept=(&sy*&p-&slope*&sx)/&m/&p;let point=BigInt::from(2048+1024*values.len());
        let term=&slope*&point/&p;let prediction=&intercept+term;
        Ok((slope,intercept,prediction))
    }
}

/// Fixed Legacy child3073 profile. Its three samples have two ratios; none
/// of the mature-eight terms or constants are reused as a padded window.
pub(crate) mod two_ratio {
    use super::*;
    use crate::daa_integer::TwoRatioInputs;

    pub const X0: u32 = 2048;
    pub const SAMPLE_END_HEIGHTS: [u32; 2] = [2048, 3072];

    fn bounds() {
        // |y_i| < 2^283. Difference and sum < 2^284, scaled by P
        // < 2^314. Reuse conservative 387-bit signed products and sums.
        // b*sum(x) < 2^(314+13); b*point < 2^(314+13), so the
        // prediction is < 2^333, the existing Legacy finish bound.
        let qmax = (BigUint::one() << 283usize) - BigUint::one();
        let delta = &qmax * BigUint::from(2u8);
        let scaled = &delta * BigUint::from(PRECISION);
        let slope = &scaled / BigUint::from(1024u64);
        let intercept_numerator = &scaled + &slope * BigUint::from(5120u64);
        let prediction = &intercept_numerator / BigUint::from(2 * PRECISION)
            + &slope * BigUint::from(4096u64) / BigUint::from(PRECISION);
        assert!(delta.bits() <= 284 && scaled.bits() <= 314);
        assert!(prediction.bits() <= 333 && Fr::MODULUS_BIT_SIZE > 57);
    }

    fn slope(builder: &mut Builder, a1: &[OutputBits])
        -> Result<(RegressionOutput, Increment), String>
    {
        if a1.len() != 2 { return Err("two-ratio profile requires two A1 outputs".into()); }
        bounds();
        let before = Progress::from(builder.progress());
        let aliases = alias_outputs(builder, a1, None);
        let sources = aliases.iter().map(|a| (a.magnitude.as_slice(), a.negative)).collect::<Vec<_>>();
        // For x=[x0,x0+E], native numerator E*(y1-y0)*P and
        // denominator E^2 give exactly trunc0((y1-y0)*P/E).
        let (sum_magnitude, sum_negative, positive_sum, negative_sum) =
            emit_signed_sum(builder, &sources, &[-1, 1], 284)?;
        let numerator = multiply_public(builder, &sum_magnitude, PRECISION, 314);
        let (slope_magnitude, remainder, division_carries, remainder_range_final_borrow) =
            divide_public(builder, &numerator, 1024);
        let (slope_negative, remainder_negative) =
            signed_division_signs(builder, sum_negative, &slope_magnitude, &remainder);
        let after = Progress::from(builder.progress());
        let increment = Increment { before, after, added_live_bits: after.live_bits-before.live_bits,
            added_rows: after.rows-before.rows, added_terms: after.terms-before.terms };
        Ok((RegressionOutput { aliases, positive_sum, negative_sum, sum_magnitude, sum_negative,
            numerator, slope_magnitude, slope_negative, remainder, remainder_negative,
            division_carries, remainder_range_final_borrow }, increment))
    }

    fn prediction(builder: &mut Builder, regression: &RegressionOutput)
        -> Result<(PredictionOutput, Increment), String>
    {
        if regression.aliases.len() != 2 { return Err("two-ratio regression alias count".into()); }
        let before = Progress::from(builder.progress());
        let x0_bits = builder.bits_u64(X0 as u64, 32);
        for (i, &wire) in x0_bits.iter().enumerate() {
            if (X0 >> i) & 1 == 0 { builder.assert_zero(wire); } else { builder.assert_one(wire); }
        }
        let grid_x = (0..2).map(|i| affine_public(builder, &x0_bits, 1, i*1024, 33)).collect();
        let sum_x = affine_public(builder, &x0_bits, 2, 1024, 33);
        let b_alias = bind_signed(builder, &regression.slope_magnitude, regression.slope_negative, None);
        let sources = regression.aliases.iter().map(|a| (a.magnitude.as_slice(), a.negative)).collect::<Vec<_>>();
        let (y_magnitude, y_negative, _, _) = emit_signed_sum(builder, &sources, &[1, 1], 284)?;
        let py_magnitude = multiply_public(builder, &y_magnitude, PRECISION, PREDICTION_WIDTH);
        let b_sum_x_magnitude = variable_product(builder, &b_alias.magnitude, &sum_x, PREDICTION_WIDTH);
        let x_sources = [(py_magnitude.as_slice(), y_negative),
            (b_sum_x_magnitude.as_slice(), b_alias.negative)];
        let (x_magnitude, x_negative, _, _) = emit_signed_sum(builder, &x_sources, &[1, -1], PREDICTION_WIDTH)?;
        // Preserve the two native trunc0 divisions explicitly. The first
        // quotient and remainder remain constrained even though not exported.
        let (half, half_remainder, _, _) = divide_public(builder, &x_magnitude, 2);
        let (half_negative, _) = signed_division_signs(builder, x_negative, &half, &half_remainder);
        let (a_magnitude, a_remainder, a_division_carries, a_range_final_borrow) =
            divide_public(builder, &half, PRECISION);
        let (a_negative, a_remainder_negative) = signed_division_signs(builder,
            half_negative, &a_magnitude, &a_remainder);
        // x0=2048 is fixed in this profile; Scala Int's point is exactly4096.
        let point_twos = affine_public(builder, &x0_bits, 1, 2048, 32);
        let (point_magnitude, point_negative, point_binding_rows) = twos_magnitude(builder, &point_twos, None);
        let b_point_magnitude = variable_product(builder, &b_alias.magnitude, &point_magnitude, PREDICTION_WIDTH);
        let sign_xor = builder.bit(builder.value(b_alias.negative) ^ builder.value(point_negative));
        builder.row(vec![Builder::linear(sign_xor, Fr::one()),
            Builder::linear(b_alias.negative, -Fr::one()), Builder::linear(point_negative, -Fr::one()),
            Builder::product(b_alias.negative, point_negative, Fr::from(2u64))]);
        let product_nonzero = builder.nonzero_unasserted(&b_point_magnitude);
        let product_negative = builder.and(sign_xor, product_nonzero);
        let (term_magnitude, term_remainder, term_division_carries, term_range_final_borrow) =
            divide_public(builder, &b_point_magnitude, PRECISION);
        let (term_negative, term_remainder_negative) = signed_division_signs(builder,
            product_negative, &term_magnitude, &term_remainder);
        let (prediction_magnitude, prediction_negative, _, _) = emit_signed_sum(builder,
            &[(a_magnitude.as_slice(), a_negative), (term_magnitude.as_slice(), term_negative)],
            &[1, 1], PREDICTION_WIDTH)?;
        let after = Progress::from(builder.progress());
        let increment = Increment { before, after, added_live_bits: after.live_bits-before.live_bits,
            added_rows: after.rows-before.rows, added_terms: after.terms-before.terms };
        Ok((PredictionOutput { x0_bits, grid_x, b_alias, sum_x, y_magnitude, y_negative,
            py_magnitude, b_sum_x_magnitude, x_magnitude, x_negative, a_magnitude, a_negative,
            a_remainder, a_remainder_negative, a_division_carries, a_range_final_borrow,
            point_twos, point_magnitude, point_negative, point_binding_rows, b_point_magnitude,
            term_magnitude, term_negative, term_remainder, term_remainder_negative,
            term_division_carries, term_range_final_borrow, prediction_magnitude, prediction_negative }, increment))
    }

    pub(crate) fn compile_extended<T, F>(q: &BigUint, input: TwoRatioInputs, materialize: bool,
        extend: F) -> Result<(CompiledPrediction, T), String>
    where F: FnOnce(&mut Builder, &[OutputBits], &RegressionOutput, &PredictionOutput) -> Result<T, String>
    {
        let (joined, ((regression, prediction), extra)) = daa_integer::compile_two_extended(
            q, input, materialize, |builder, a1| {
                let regression = slope(builder, a1)?;
                let prediction = prediction(builder, &regression.0)?;
                let extra = extend(builder, a1, &regression.0, &prediction.0)?;
                Ok(((regression, prediction), extra))
            })?;
        let joined = CompiledRegression { joined, output: regression.0, increment: regression.1 };
        Ok((CompiledPrediction { joined, output: prediction.0, increment: prediction.1 }, extra))
    }

    pub(crate) fn compile(q: &BigUint, input: TwoRatioInputs, materialize: bool) -> Result<CompiledPrediction, String> {
        compile_extended(q, input, materialize, |_, _, _, _| Ok(())).map(|(c, ())| c)
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        fn input(deltas: [i64; 2]) -> TwoRatioInputs {
            TwoRatioInputs { nbits: [0x03000001; 2], timestamps: [0, deltas[0], deltas[0]+deltas[1]] }
        }
        fn native(c: &CompiledPrediction) -> (BigInt, BigInt, BigInt) {
            let w = &c.joined.joined.witness;
            let ys = c.joined.joined.output.iter().map(|o| signed_value(w,
                &o.quotient_magnitude, o.quotient_negative)).collect::<Vec<_>>();
            let xs = SAMPLE_END_HEIGHTS.map(BigInt::from);
            let sumx = &xs[0]+&xs[1]; let sumy = &ys[0]+&ys[1];
            let xy = &xs[0]*&ys[0]+&xs[1]*&ys[1]; let x2 = &xs[0]*&xs[0]+&xs[1]*&xs[1];
            let p = BigInt::from(PRECISION);
            let b = (2*xy-&sumx*&sumy)*&p/(2*x2-&sumx*&sumx);
            let a = (&sumy*&p-&b*&sumx)/2/&p;
            let forecast = &a+&b*BigInt::from(4096u32)/&p;
            (b, a, forecast)
        }
        #[test]
        fn two_ratio_signed_prediction_matches_unsimplified_native() {
            let mut inputs = [[1,1],[3,7],[7,3],[1,100],[-3,7],[3,-7],[-3,-7],[1,-1]]
                .map(input).to_vec();
            inputs.push(TwoRatioInputs { nbits: [0x22000001; 2], timestamps: [0,1,2] });
            for input in inputs {
                let c = compile(&crate::daa_count::q(), input, true).unwrap();
                assert!(prediction_residuals(&c).unwrap().iter().all(Zero::is_zero));
                let w = &c.joined.joined.witness; let (b,a,f) = native(&c);
                assert_eq!(signed_value(w, &c.joined.output.slope_magnitude, c.joined.output.slope_negative), b);
                assert_eq!(signed_value(w, &c.output.a_magnitude, c.output.a_negative), a);
                assert_eq!(signed_value(w, &c.output.prediction_magnitude, c.output.prediction_negative), f);
            }
            let zero_denominator = compile(&crate::daa_count::q(), input([0,1]), true).unwrap();
            assert!(prediction_residuals(&zero_denominator).unwrap().iter().any(|r| !r.is_zero()));
        }
        #[test]
        fn two_ratio_prediction_aliases_and_divisions_are_causal() {
            let mut c = compile(&crate::daa_count::q(), input([3,7]), true).unwrap();
            assert!(prediction_residuals(&c).unwrap().iter().all(Zero::is_zero));
            let w = &c.joined.joined.witness;
            let wires = [c.joined.output.aliases[0].magnitude[0], c.joined.output.aliases[1].magnitude[0],
                c.joined.output.slope_magnitude[0], c.output.b_alias.magnitude[0], c.output.x0_bits[0],
                c.output.a_magnitude[0], c.output.a_remainder[0], c.output.point_magnitude[0],
                c.output.term_magnitude[0], c.output.term_remainder[0], c.output.prediction_magnitude[0],
                c.joined.output.aliases[0].negative, c.joined.output.aliases[1].negative,
                c.joined.output.slope_negative, c.joined.output.remainder_negative,
                c.output.b_alias.negative, c.output.a_negative, c.output.a_remainder_negative,
                c.output.point_negative, c.output.term_negative, c.output.term_remainder_negative,
                c.output.prediction_negative];
            let original = wires.map(|wire| w[wire]);
            for (wire,value) in wires.into_iter().zip(original) {
                c.joined.joined.witness[wire] = Fr::one()-value;
                assert!(prediction_residuals(&c).unwrap().iter().any(|r| !r.is_zero()), "wire{wire}");
                c.joined.joined.witness[wire] = value;
            }
            for index in 0..2 {
                let alias = &c.joined.output.aliases[index];
                let wire = alias.negative; let row = alias.sign_binding_row;
                let value = c.joined.joined.witness[wire];
                c.joined.joined.witness[wire] = Fr::one()-value;
                assert!(!prediction_residuals(&c).unwrap()[row].is_zero(),
                    "isolated quotient sign alias {index}");
                c.joined.joined.witness[wire] = value;
            }
            // A coherently changed b alias still fails its actual import row.
            let a = &c.output.b_alias; let row = a.magnitude_binding_rows[0];
            let wire = a.magnitude[0]; c.joined.joined.witness[wire] = Fr::one()-c.joined.joined.witness[wire];
            assert!(!prediction_residuals(&c).unwrap()[row].is_zero());
            c.joined.joined.circuit.as_mut().unwrap().terms.retain(|t| t.row != row);
            assert!(prediction_residuals(&c).unwrap()[row].is_zero());
        }
    }
}

#[cfg(test)]
mod tests{
    use super::*;
    use crate::daa_count;
    use num_traits::Signed;
    fn hex(bytes:&[u8])->String{bytes.iter().map(|b|format!("{b:02x}")).collect()}
    fn window(deltas:[i64;8])->WindowInputs{
        let mut timestamps=[0i64;9];
        for i in 0..8{timestamps[i+1]=timestamps[i].wrapping_add(deltas[i]);}
        WindowInputs{nbits:[0x03000001;8],timestamps}
    }
    fn failed_rows(compiled:&CompiledRegression)->Vec<usize>{
        residuals(compiled).unwrap().iter().enumerate()
            .filter_map(|(row,value)|if value.is_zero(){None}else{Some(row)}).collect()
    }
    fn set_bits(witness:&mut [Fr],wires:&[usize],value:&BigUint){
        for (i,&wire) in wires.iter().enumerate(){witness[wire]=Fr::from(bit_value(value,i) as u64);}
    }
    fn witness_limb(witness:&[Fr],wires:&[usize],column:usize)->u64{
        (0..16).fold(0u64,|value,i|{
            value|((wires.get(16*column+i).map(|&wire|witness[wire]==Fr::one()).unwrap_or(false) as u64)<<i)
        })
    }
    #[test]
    fn a2_preserves_four_frozen_a1_pins(){
        let one=crate::daa_integer::Inputs{nbits:0x03000001,start_timestamp:0,end_timestamp:1};
        let fixtures=[
            (Epoch::Legacy,4111,10287,36723,"e9aa16dfb3e04a073684a47fdbecc3830bacee2fc756ad9f8424309b387823f1",
                32440,49528,261016,"033e48693d7b17d002c1029a019e4e3ead350c53c32f398950ec38d54ebb696b"),
            (Epoch::Eip,4048,6185,32303,"bf26e926b79fb18cd0904eef80bf044c5c9c91dafccdee267a693a3e1985d394",
                31936,49480,258424,"8c01828e468ecfeed28e5aef5a90d7d8a626326acd23aa9f16ad95a8b3b09058")];
        for (epoch,one_live,one_rows,one_terms,one_hash,eight_live,eight_rows,eight_terms,eight_hash) in fixtures{
            let single=crate::daa_integer::compile(epoch,&daa_count::q(),one,false).unwrap();
            assert_eq!((single.count.live_bits,single.count.residual_rows,single.count.terms),
                (one_live,one_rows,one_terms));
            assert_eq!(hex(&single.count.topology_blake2b256),one_hash);
            let eight=crate::daa_integer::compile_eight(epoch,&daa_count::q(),window([1;8]),false).unwrap();
            assert_eq!((eight.count.live_bits,eight.count.residual_rows,eight.count.terms),
                (eight_live,eight_rows,eight_terms));
            assert_eq!(hex(&eight.count.topology_blake2b256),eight_hash);
        }
    }
    #[test]
    fn a2_native_unsimplified_oracle_and_full_join(){
        let patterns=[[8,7,6,5,4,3,2,1],[1,2,3,4,5,6,7,8],[1;8],
            [1_000_000_000_000,-7,-6,-5,-4,-3,-2,-1]];
        let mut saw_positive=false;let mut saw_negative=false;let mut saw_zero=false;
        let mut saw_negative_remainder=false;let mut saw_nonexact=false;let mut saw_zero_y=false;
        for epoch in [Epoch::Legacy,Epoch::Eip]{
            let mut first_shape=None;
            for deltas in patterns{
                let compiled=compile(epoch,&daa_count::q(),window(deltas),true).unwrap();
                assert!(failed_rows(&compiled).is_empty(),"full A1+A2 rows, epoch={epoch:?}, deltas={deltas:?}");
                let c=&compiled.joined.count;
                let shape=(c.live_bits,c.padded_input_bits,c.residual_rows,c.padded_rows,c.terms,
                    c.topology_blake2b256,compiled.increment.added_live_bits,
                    compiled.increment.added_rows,compiled.increment.added_terms);
                if let Some(previous)=first_shape{assert_eq!(shape,previous,"fixed A2 topology/counts");}
                first_shape=Some(shape);
                let witness=&compiled.joined.witness;
                let ys:[BigInt;8]=std::array::from_fn(|j|{
                    let output=&compiled.joined.output[j];
                    signed_value(witness,&output.quotient_magnitude,output.quotient_negative)
                });
                saw_zero_y|=ys.iter().any(BigInt::is_zero);
                let slope=signed_value(witness,&compiled.output.slope_magnitude,compiled.output.slope_negative);
                let remainder=signed_value(witness,&compiled.output.remainder,compiled.output.remainder_negative);
                for x0 in [-100_000,0,1_000_000]{
                    assert_eq!(slope,native_slope_oracle(x0,epoch,&ys),
                        "native unsimplified BigInt formula, x0={x0}");
                }
                let signed_sum:BigInt=ys.iter().enumerate()
                    .map(|(i,y)|BigInt::from(WEIGHTS[i])*y).sum();
                let signed_numerator=signed_sum*BigInt::from(PRECISION*epoch.length());
                let d=BigInt::from(denominator(epoch));
                assert_eq!(signed_numerator,&slope*&d+&remainder);
                assert!(remainder.abs()<d);
                assert!(remainder.is_zero() || remainder.sign()==signed_numerator.sign());
                assert!(slope!=BigInt::zero() || witness[compiled.output.slope_negative]==Fr::zero());
                assert!(remainder!=BigInt::zero() || witness[compiled.output.remainder_negative]==Fr::zero());
                saw_positive|=slope>BigInt::zero();saw_negative|=slope<BigInt::zero();
                saw_zero|=slope.is_zero();saw_nonexact|=!remainder.is_zero();
                saw_negative_remainder|=remainder<BigInt::zero();
                let base=daa_count::eight(epoch).unwrap();
                assert_eq!(compiled.increment.before.live_bits,base.count.live_bits);
                assert_eq!(compiled.increment.before.rows,base.count.residual_rows-base.count.padding_bits);
                assert_eq!(compiled.increment.before.terms,base.count.terms-base.count.padding_bits);
                assert_eq!(compiled.increment.after.live_bits,
                    compiled.increment.before.live_bits+compiled.increment.added_live_bits);
                assert_eq!(compiled.joined.count.live_bits,compiled.increment.after.live_bits);
                assert_eq!(compiled.joined.count.maximum_degree,2);
                assert!(compiled.joined.count.maximum_column_signed_abs_bits<=57);
            }
        }
        assert!(saw_positive && saw_negative && saw_zero && saw_nonexact
            && saw_negative_remainder && saw_zero_y);
    }
    #[test]
    fn a2_alternative_alias_is_caught_only_by_binding(){
        let input=window([1;8]);
        let valid=compile(Epoch::Legacy,&daa_count::q(),input,true).unwrap();
        assert!(failed_rows(&valid).is_empty());
        for j in 0..8{
            let original=signed_value(&valid.joined.witness,&valid.joined.output[j].quotient_magnitude,
                valid.joined.output[j].quotient_negative).to_biguint().unwrap();
            assert!(!bit_value(&original,0));
            for sign_fault in [false,true]{
                let alternative=if sign_fault{original.clone()}else{&original+BigUint::one()};
                let mut changed=compile_inner(Epoch::Legacy,&daa_count::q(),input,true,
                    Some((j,alternative,sign_fault))).unwrap();
                let expected=if sign_fault{changed.output.aliases[j].sign_binding_row}
                    else{changed.output.aliases[j].magnitude_binding_rows[0]};
                let failed=failed_rows(&changed);
                assert_eq!(failed,vec![expected],"only alias {j} binding should fail");
                changed.joined.circuit.as_mut().unwrap().terms.retain(|term|term.row!=expected);
                assert!(failed_rows(&changed).is_empty(),"omitted alias binding accepts consistent alternate witness");
            }
        }
    }
    #[test]
    fn a2_range_sign_carry_and_borrow_mutants(){
        let epoch=Epoch::Legacy;
        let mut selected=None;
        let d=BigUint::from(denominator(epoch));
        let r_limit=BigUint::one()<<((64-denominator(epoch).leading_zeros()) as usize);
        for tail in 1..=2000i64{
            let deltas=[1,2,3,4,5,6,7,tail];
            let ys=std::array::from_fn::<BigInt,8,_>(|j|{
                BigInt::from(epoch.multiplier()/deltas[j] as u64)
            });
            let sum:BigInt=ys.iter().enumerate().map(|(j,y)|BigInt::from(WEIGHTS[j])*y).sum();
            let numerator=(sum*BigInt::from(PRECISION*epoch.length())).abs().to_biguint().unwrap();
            let quotient=&numerator/&d;let remainder=&numerator%&d;
            if quotient>BigUint::zero() && (&quotient%BigUint::from(4u8))==BigUint::from(3u8)
                && (&remainder%BigUint::from(1u64<<24))!=BigUint::zero()
                && &remainder+&d<r_limit{
                selected=Some(window(deltas));break;
            }
        }
        let input=selected.expect("bounded deterministic range fixture");
        let mut range=compile(epoch,&daa_count::q(),input,true).unwrap();
        assert!(failed_rows(&range).is_empty());
        let old_q=signed_value(&range.joined.witness,&range.output.slope_magnitude,range.output.slope_negative)
            .abs().to_biguint().unwrap();
        let old_r=signed_value(&range.joined.witness,&range.output.remainder,range.output.remainder_negative)
            .abs().to_biguint().unwrap();
        set_bits(&mut range.joined.witness,&range.output.slope_magnitude,&(old_q-BigUint::one()));
        set_bits(&mut range.joined.witness,&range.output.remainder,&(old_r+&d));
        let mut carry=0u64;
        let width=(64-denominator(epoch).leading_zeros()) as usize;
        let columns=range.output.slope_magnitude.len().div_ceil(16)+width.div_ceil(16);
        for column in 0..columns{
            let value=denominator(epoch)*witness_limb(&range.joined.witness,&range.output.slope_magnitude,column)
                +witness_limb(&range.joined.witness,&range.output.remainder,column)+carry;
            carry=value>>16;
            if column+1<columns{
                for (i,&wire) in range.output.division_carries[column].iter().enumerate(){
                    range.joined.witness[wire]=Fr::from((carry>>i)&1);
                }
            }
        }
        assert_eq!(carry,0);
        let trace=range.joined.subtract_traces.last().unwrap().clone();
        let constant=trace.minuend_constant.unwrap();let mut borrow=0i32;
        for i in 0..trace.differences.len(){
            let a=bit_value(&constant,i) as i32;
            let b=(range.joined.witness[trace.subtrahend_wires[i]]==Fr::one()) as i32;
            let raw=a-b-borrow;let next=(raw<0) as i32;
            range.joined.witness[trace.differences[i]]=Fr::from((raw&1) as u64);
            range.joined.witness[trace.borrows[i]]=Fr::from(next as u64);borrow=next;
        }
        assert_eq!(borrow,1);
        let failed=failed_rows(&range);
        assert_eq!(failed.len(),1,"arithmetic-consistent q-1,r+D must fail only strict range");
        range.joined.circuit.as_mut().unwrap().terms.retain(|term|term.row!=failed[0]);
        assert!(failed_rows(&range).is_empty(),"omitting range row accepts alternate division");

        let negative_input=window([1,2,3,4,5,6,7,8]);
        for selector in 0..2{
            let mut signed=compile(epoch,&daa_count::q(),negative_input,true).unwrap();
            let wire=if selector==0{signed.output.slope_negative}else{signed.output.remainder_negative};
            assert_eq!(signed.joined.witness[wire],Fr::one(),"negative nonzero sign fixture");
            signed.joined.witness[wire]=Fr::zero();
            let failed=failed_rows(&signed);
            assert_eq!(failed.len(),2,"both signed predicate rows enforce output sign");
            signed.joined.circuit.as_mut().unwrap().terms.retain(|term|!failed.contains(&term.row));
            assert!(failed_rows(&signed).is_empty(),"omitted sign family accepts wrong sign");
        }
        for selector in 0..2{
            let mut zero=compile(epoch,&daa_count::q(),window([1;8]),true).unwrap();
            let wire=if selector==0{zero.output.slope_negative}else{zero.output.remainder_negative};
            assert_eq!(zero.joined.witness[wire],Fr::zero(),"constant samples give canonical zero");
            zero.joined.witness[wire]=Fr::one();
            let failed=failed_rows(&zero);
            assert_eq!(failed.len(),2,"negative-zero sign must fail its predicate family");
            zero.joined.circuit.as_mut().unwrap().terms.retain(|term|!failed.contains(&term.row));
            assert!(failed_rows(&zero).is_empty(),"omitted zero-sign family accepts negative zero");
        }
        let mut carry_fault=compile(epoch,&daa_count::q(),negative_input,true).unwrap();
        let wire=carry_fault.output.division_carries[0][0];
        carry_fault.joined.witness[wire]=if carry_fault.joined.witness[wire]==Fr::one(){Fr::zero()}else{Fr::one()};
        assert_eq!(failed_rows(&carry_fault).len(),2,"product carry is consumed by adjacent columns");
        let mut borrow_fault=compile(epoch,&daa_count::q(),negative_input,true).unwrap();
        let trace=borrow_fault.joined.subtract_traces.last().unwrap().clone();
        borrow_fault.joined.witness[trace.initial_borrow]=Fr::one();
        let constant=trace.minuend_constant.unwrap();let mut borrow=1i32;
        for i in 0..trace.differences.len(){
            let raw=bit_value(&constant,i) as i32
                -(borrow_fault.joined.witness[trace.subtrahend_wires[i]]==Fr::one()) as i32-borrow;
            let next=(raw<0) as i32;
            borrow_fault.joined.witness[trace.differences[i]]=Fr::from((raw&1) as u64);
            borrow_fault.joined.witness[trace.borrows[i]]=Fr::from(next as u64);borrow=next;
        }
        assert_eq!(failed_rows(&borrow_fault).len(),1,"recomputed borrow chain fails anchored initial borrow");
    }
    fn prediction_failed(compiled:&CompiledPrediction)->Vec<usize>{
        prediction_residuals(compiled).unwrap().iter().enumerate()
            .filter_map(|(row,value)|if value.is_zero(){None}else{Some(row)}).collect()
    }
    fn witness_big(witness:&[Fr],wires:&[usize])->BigUint{
        let mut bytes=vec![0u8;wires.len().div_ceil(8)];
        for (i,&wire) in wires.iter().enumerate(){
            if witness[wire]==Fr::one(){bytes[i/8]|=1<<(i%8);}
        }
        BigUint::from_bytes_le(&bytes)
    }
    #[test]
    fn a3_frozen_a2_native_oracle_grid_and_wrap(){
        let positive=[8,7,6,5,4,3,2,1];let negative=[1,2,3,4,5,6,7,8];
        let signed=[1_000_000_000_000,-7,-6,-5,-4,-3,-2,-1];
        let zero=[1_000_000_000_000;8];
        let mut seen_sign_pairs=[false;4];let mut seen_a_negative=false;
        let mut seen_a_positive=false;let mut seen_a_zero=false;
        let mut nonexact_a=false;let mut nonexact_term=false;
        for epoch in [Epoch::Legacy,Epoch::Eip]{
            let baseline=compile(epoch,&daa_count::q(),window([1;8]),false).unwrap();
            let (expected_live,expected_hash)=match epoch{
                Epoch::Legacy=>(40156,"68095f57d94a5e18a8bbbeb071d668c05476c2508689536024d451fd3501c085"),
                Epoch::Eip=>(39351,"17005b25a2010d8d7b6b13512073b0e95eba0f769e14345df09676c11f044800")};
            assert_eq!(baseline.joined.count.live_bits,expected_live);
            assert_eq!(hex(&baseline.joined.count.topology_blake2b256),expected_hash);
            let e=epoch.length() as u32;
            let before_wrap=i32::MAX as u32-8*e;
            let after_wrap=before_wrap+1;
            let last_valid=i32::MAX as u32-7*e;
            let cases=[(positive,0),(negative,0),([1;8],0),(zero,0),(signed,0),
                (positive,before_wrap),(negative,after_wrap),(positive,last_valid),
                (negative,last_valid)];
            let mut first_shape=None;
            for (deltas,x0) in cases{
                let input=PredictionInput{window:window(deltas),x0};
                let compiled=compile_prediction(epoch,&daa_count::q(),input,true).unwrap();
                assert!(prediction_failed(&compiled).is_empty(),
                    "A1+A2+A3 residuals epoch={epoch:?} x0={x0} deltas={deltas:?}");
                let count=&compiled.joined.joined.count;
                let shape=(count.live_bits,count.padded_input_bits,count.residual_rows,
                    count.padded_rows,count.terms,count.topology_blake2b256,
                    compiled.increment.added_live_bits,compiled.increment.added_rows,
                    compiled.increment.added_terms);
                if let Some(previous)=first_shape{assert_eq!(shape,previous,"fixed A3 topology/counts");}
                first_shape=Some(shape);
                assert_eq!(compiled.increment.before.live_bits,baseline.joined.count.live_bits);
                assert_eq!(compiled.increment.before.rows,
                    baseline.joined.count.residual_rows-baseline.joined.count.padding_bits);
                assert_eq!(compiled.increment.before.terms,
                    baseline.joined.count.terms-baseline.joined.count.padding_bits);
                let witness=&compiled.joined.joined.witness;
                let ys:[BigInt;8]=std::array::from_fn(|j|{
                    let out=&compiled.joined.joined.output[j];
                    signed_value(witness,&out.quotient_magnitude,out.quotient_negative)
                });
                let (b,a,prediction)=native_prediction_oracle(x0 as i64,epoch,&ys);
                assert_eq!(signed_value(witness,&compiled.joined.output.slope_magnitude,
                    compiled.joined.output.slope_negative),b);
                assert_eq!(signed_value(witness,&compiled.output.a_magnitude,compiled.output.a_negative),a);
                assert_eq!(signed_value(witness,&compiled.output.prediction_magnitude,
                    compiled.output.prediction_negative),prediction);
                let point=(x0 as i64+8*epoch.length() as i64) as i32;
                assert_eq!(signed_value(witness,&compiled.output.point_magnitude,
                    compiled.output.point_negative),BigInt::from(point));
                assert_eq!(witness_big(witness,&compiled.output.sum_x),
                    BigUint::from(8*x0 as u64+28*epoch.length()));
                for j in 0..8{
                    assert_eq!(witness_big(witness,&compiled.output.grid_x[j]),
                        BigUint::from(x0 as u64+j as u64*epoch.length()));
                }
                let y_sum:BigInt=ys.iter().cloned().sum();
                let x_sum=BigInt::from(8*x0 as u64+28*epoch.length());
                let x=BigInt::from(PRECISION)*y_sum-&b*x_sum;
                let a_remainder=signed_value(witness,&compiled.output.a_remainder,
                    compiled.output.a_remainder_negative);
                assert_eq!(x,&a*BigInt::from(8*PRECISION)+&a_remainder);
                assert!(a_remainder.abs()<BigInt::from(8*PRECISION));
                let term=signed_value(witness,&compiled.output.term_magnitude,
                    compiled.output.term_negative);
                let term_remainder=signed_value(witness,&compiled.output.term_remainder,
                    compiled.output.term_remainder_negative);
                assert_eq!(&b*BigInt::from(point),&term*BigInt::from(PRECISION)+&term_remainder);
                assert!(term_remainder.abs()<BigInt::from(PRECISION));
                seen_a_negative|=a<BigInt::zero();seen_a_positive|=a>BigInt::zero();
                seen_a_zero|=a.is_zero();
                nonexact_a|=!a_remainder.is_zero();nonexact_term|=!term_remainder.is_zero();
                if !b.is_zero(){
                    let index=((b.sign()==Sign::Minus) as usize)*2+((point<0) as usize);
                    seen_sign_pairs[index]=true;
                }
                assert!(count.maximum_column_signed_abs_bits<=57);
                assert_eq!(count.maximum_degree,2);
            }
            let invalid=PredictionInput{window:window(positive),x0:last_valid+1};
            let rejected=compile_prediction(epoch,&daa_count::q(),invalid,true).unwrap();
            assert!(!prediction_failed(&rejected).is_empty(),"grid x7 beyond Int32Max must fail");
            let mut high=window(positive);high.nbits=[0x22000001;8];
            let high=compile_prediction(epoch,&daa_count::q(),
                PredictionInput{window:high,x0:0},true).unwrap();
            assert!(prediction_failed(&high).is_empty(),"high compact-width witness");
            let witness=&high.joined.joined.witness;
            let ys:[BigInt;8]=std::array::from_fn(|j|{
                let out=&high.joined.joined.output[j];
                signed_value(witness,&out.quotient_magnitude,out.quotient_negative)
            });
            let (_,_,prediction)=native_prediction_oracle(0,epoch,&ys);
            assert_eq!(signed_value(witness,&high.output.prediction_magnitude,
                high.output.prediction_negative),prediction);
        }
        assert!(seen_sign_pairs.iter().all(|value|*value),"b/point sign combinations");
        assert!(seen_a_negative && seen_a_positive && seen_a_zero && nonexact_a && nonexact_term);
    }
    #[test]
    fn a3_sources_and_nonwrapped_forecast_mutants(){
        let epoch=Epoch::Legacy;let input=PredictionInput{window:window([1,2,3,4,5,6,7,8]),x0:100};
        let valid=compile_prediction(epoch,&daa_count::q(),input,true).unwrap();
        assert!(prediction_failed(&valid).is_empty());
        let witness=&valid.joined.joined.witness;
        let y0=witness_big(witness,&valid.joined.joined.output[0].quotient_magnitude);
        assert!(!bit_value(&y0,0));
        let mut altered_y=compile_prediction_inner(epoch,&daa_count::q(),input,true,
            Some((0,&y0+BigUint::one(),false)),None,None,None,None).unwrap();
        let failed=prediction_failed(&altered_y);
        let binding=altered_y.joined.output.aliases[0].magnitude_binding_rows[0];
        assert_eq!(failed,vec![binding]);
        altered_y.joined.joined.circuit.as_mut().unwrap().terms.retain(|term|term.row!=binding);
        assert!(prediction_failed(&altered_y).is_empty(),"A1/A2 alias omission accepts coherent A3");
        let b=witness_big(witness,&valid.joined.output.slope_magnitude);
        let altered_b_value=if bit_value(&b,0){&b-BigUint::one()}else{&b+BigUint::one()};
        let bsign=witness[valid.joined.output.slope_negative]==Fr::one();
        let mut altered_b=compile_prediction_inner(epoch,&daa_count::q(),input,true,
            None,Some((altered_b_value,bsign)),None,None,None).unwrap();
        let failed=prediction_failed(&altered_b);
        let binding=altered_b.output.b_alias.magnitude_binding_rows[0];
        assert_eq!(failed,vec![binding]);
        altered_b.joined.joined.circuit.as_mut().unwrap().terms.retain(|term|term.row!=binding);
        assert!(prediction_failed(&altered_b).is_empty(),"A2 slope alias omission accepts coherent forecast");
        let mut altered_b_sign=compile_prediction_inner(epoch,&daa_count::q(),input,true,
            None,Some((b.clone(),!bsign)),None,None,None).unwrap();
        let failed=prediction_failed(&altered_b_sign);
        let sign_binding=altered_b_sign.output.b_alias.sign_binding_row;
        assert_eq!(failed,vec![sign_binding]);
        altered_b_sign.joined.joined.circuit.as_mut().unwrap().terms
            .retain(|term|term.row!=sign_binding);
        assert!(prediction_failed(&altered_b_sign).is_empty(),
            "omitting only the slope sign binding accepts the coherent alternate forecast");
        let x0=i32::MAX as u32-7*epoch.length() as u32;
        let wrapped=PredictionInput{window:window([1,2,3,4,5,6,7,8]),x0};
        let valid_wrapped=compile_prediction(epoch,&daa_count::q(),wrapped,true).unwrap();
        assert!(prediction_failed(&valid_wrapped).is_empty());
        let point_witness=&valid_wrapped.joined.joined.witness;
        let point=witness_big(point_witness,&valid_wrapped.output.point_magnitude);
        let point_sign=point_witness[valid_wrapped.output.point_negative]==Fr::one();
        let mut altered_point_sign=compile_prediction_inner(epoch,&daa_count::q(),wrapped,true,
            None,None,Some((point,!point_sign)),None,None).unwrap();
        let failed=prediction_failed(&altered_point_sign);
        let sign_binding=*altered_point_sign.output.point_binding_rows.last().unwrap();
        assert_eq!(failed,vec![sign_binding]);
        altered_point_sign.joined.joined.circuit.as_mut().unwrap().terms
            .retain(|term|term.row!=sign_binding);
        assert!(prediction_failed(&altered_point_sign).is_empty(),
            "omitting only the point sign binding accepts the coherent alternate forecast");
        let nonwrapped=BigUint::from(x0 as u64+8*epoch.length());
        let mut false_point=compile_prediction_inner(epoch,&daa_count::q(),wrapped,true,
            None,None,Some((nonwrapped,false)),None,None).unwrap();
        let failed=prediction_failed(&false_point);
        assert!(!failed.is_empty());
        assert!(failed.iter().all(|row|false_point.output.point_binding_rows.contains(row)),
            "coherent nonwrapped forecast must fail only point binding");
        let binding=&false_point.output.point_binding_rows;
        false_point.joined.joined.circuit.as_mut().unwrap().terms.retain(|term|!binding.contains(&term.row));
        assert!(prediction_failed(&false_point).is_empty(),
            "omitted signed-wrap binding accepts coherent nonwrapped forecast");
    }
    #[test]
    fn a3_division_boundaries_and_isolated_mutants(){
        let epoch=Epoch::Legacy;let w=window([1,2,3,4,5,6,7,8]);
        for (denominator,two_stage) in [(8*PRECISION,true),(PRECISION,false)]{
            for delta in [-1i64,1]{
                for negative in [false,true]{
                    let center=BigUint::from(denominator)*BigUint::from(3u8);
                    let magnitude=if delta<0{&center-BigUint::one()}else{&center+BigUint::one()};
                    let (compiled,(q,r,qsign,rsign))=daa_integer::compile_eight_extended(
                        epoch,&daa_count::q(),w,true,|builder,_|{
                            let n=builder.bits_big(&magnitude,PREDICTION_WIDTH);
                            let sign=builder.bit(negative);
                            let (q,r,_,_)=divide_public(builder,&n,denominator);
                            let (qs,rs)=signed_division_signs(builder,sign,&q,&r);
                            Ok((q,r,qs,rs))
                        }).unwrap();
                    let circuit=compiled.circuit.as_ref().unwrap();
                    let mut residuals=vec![Fr::zero();circuit.row_count];
                    for term in &circuit.terms{residuals[term.row]+=term.gate.evaluate(&compiled.witness);}
                    assert!(residuals.iter().all(Zero::is_zero));
                    let signed=BigInt::from_biguint(if negative{Sign::Minus}else{Sign::Plus},magnitude);
                    let direct=if two_stage{(&signed/BigInt::from(8u8))/BigInt::from(PRECISION)}
                        else{&signed/BigInt::from(PRECISION)};
                    let quotient=signed_value(&compiled.witness,&q,qsign);
                    let remainder=signed_value(&compiled.witness,&r,rsign);
                    assert_eq!(quotient,direct);
                    assert_eq!(signed,&quotient*BigInt::from(denominator)+remainder);
                }
            }
        }
        for (x0,which) in [(41u32,0usize),(60u32,1usize)]{
            let input=PredictionInput{window:w,x0};
            let valid=compile_prediction(epoch,&daa_count::q(),input,true).unwrap();
            assert!(prediction_failed(&valid).is_empty());
            let witness=&valid.joined.joined.witness;
            let (qbits,rbits,d,carries)=if which==0{
                (&valid.output.a_magnitude,&valid.output.a_remainder,8*PRECISION,
                    &valid.output.a_division_carries)
            }else{
                (&valid.output.term_magnitude,&valid.output.term_remainder,PRECISION,
                    &valid.output.term_division_carries)
            };
            let q=witness_big(witness,qbits);let r=witness_big(witness,rbits);
            assert!(q>BigUint::zero() && r>BigUint::zero());
            assert!((&r+BigUint::from(d)).bits()<=rbits.len() as u64);
            let alternate=(q-BigUint::one(),r+BigUint::from(d));
            let mut range=compile_prediction_inner(epoch,&daa_count::q(),input,true,
                None,None,None,if which==0{Some(alternate.clone())}else{None},
                if which==1{Some(alternate)}else{None}).unwrap();
            let failed=prediction_failed(&range);
            assert_eq!(failed.len(),1,"arithmetic-consistent q-1,r+D fails strict remainder range");
            range.joined.joined.circuit.as_mut().unwrap().terms.retain(|term|term.row!=failed[0]);
            assert!(prediction_failed(&range).is_empty(),"omitted range row accepts alternate division");
            let mut carry_fault=compile_prediction(epoch,&daa_count::q(),input,true).unwrap();
            let wire=if which==0{carry_fault.output.a_division_carries[0][0]}
                else{carry_fault.output.term_division_carries[0][0]};
            carry_fault.joined.joined.witness[wire]=if carry_fault.joined.joined.witness[wire]==Fr::one(){
                Fr::zero()}else{Fr::one()};
            assert_eq!(prediction_failed(&carry_fault).len(),2,"carry belongs to adjacent columns");
            let mut borrow_fault=compile_prediction(epoch,&daa_count::q(),input,true).unwrap();
            let final_wire=if which==0{borrow_fault.output.a_range_final_borrow}
                else{borrow_fault.output.term_range_final_borrow};
            let trace=borrow_fault.joined.joined.subtract_traces.iter()
                .find(|trace|trace.borrows.last()==Some(&final_wire)).unwrap().clone();
            let constant=trace.minuend_constant.unwrap();
            borrow_fault.joined.joined.witness[trace.initial_borrow]=Fr::one();
            let mut borrow=1i32;
            for i in 0..trace.differences.len(){
                let b=(borrow_fault.joined.joined.witness[trace.subtrahend_wires[i]]==Fr::one()) as i32;
                let raw=bit_value(&constant,i) as i32-b-borrow;let next=(raw<0) as i32;
                borrow_fault.joined.joined.witness[trace.differences[i]]=Fr::from((raw&1) as u64);
                borrow_fault.joined.joined.witness[trace.borrows[i]]=Fr::from(next as u64);borrow=next;
            }
            assert_eq!(prediction_failed(&borrow_fault).len(),1,"anchored initial borrow rejects recomputed chain");
            assert!(!carries.is_empty());
        }
        for wire_kind in 0..5{
            let input=PredictionInput{window:window([1_000_000_000_000;8]),x0:0};
            let mut zero=compile_prediction(epoch,&daa_count::q(),input,true).unwrap();
            assert!(prediction_failed(&zero).is_empty());
            let wire=match wire_kind{
                0=>zero.output.a_negative,1=>zero.output.a_remainder_negative,
                2=>zero.output.term_negative,3=>zero.output.term_remainder_negative,
                _=>zero.output.prediction_negative};
            assert_eq!(zero.joined.joined.witness[wire],Fr::zero());
            zero.joined.joined.witness[wire]=Fr::one();
            assert!(!prediction_failed(&zero).is_empty(),"negative zero is rejected");
        }
    }
}

#[cfg(test)]
mod short_legacy_range_causality_tests{
    use super::*;
    use crate::daa_integer::{ShortLegacyInputs,ShortLegacyProfile};

    #[test]
    fn each_short_profile_rejects_only_out_of_range_remainder(){
        let profiles=[(ShortLegacyProfile::M3,2048u64),(ShortLegacyProfile::M4,10240),
            (ShortLegacyProfile::M5,10240),(ShortLegacyProfile::M6,35840),
            (ShortLegacyProfile::M7,28672)];
        let q=crate::daa_count::q();
        for (profile,denominator) in profiles{
            let m=profile.count();let input=ShortLegacyInputs{profile,nbits:vec![0x03000001;m],
                timestamps:(0..=m).map(|i|i as i64*10).collect()};
            let numerator_value=BigUint::from(3u8)*BigUint::from(denominator);
            let (valid,(_valid_q,_valid_r,valid_q_value,valid_r_value))=
                short_legacy::compile_extended(&q,input.clone(),true,
                |builder,_,_,_,_|{
                    let numerator=builder.bits_big(&numerator_value,32);
                    for (i,&wire) in numerator.iter().enumerate(){
                        if bit_value(&numerator_value,i){builder.assert_one(wire)}else{builder.assert_zero(wire)}
                    }
                    let (quotient,remainder,_,range_final)=divide_public_override(
                        builder,&numerator,denominator,None);
                    assert!(!builder.value(range_final),"{profile:?} valid r=0 is in range");
                    let q_value=read_bits(builder,&quotient);let r_value=read_bits(builder,&remainder);
                    Ok((quotient,remainder,q_value,r_value))
                }).unwrap();
            assert!(prediction_residuals(&valid).unwrap().iter().all(Zero::is_zero),
                "{profile:?} q=3,r=0 reference witness");
            assert_eq!(valid_q_value,BigUint::from(3u8));
            assert_eq!(valid_r_value,BigUint::zero());

            let (mut invalid,(range_row,invalid_q_value,invalid_r_value))=
                short_legacy::compile_extended(&q,input,true,|builder,_,_,_,_|{
                    let numerator=builder.bits_big(&numerator_value,32);
                    for (i,&wire) in numerator.iter().enumerate(){
                        if bit_value(&numerator_value,i){builder.assert_one(wire)}else{builder.assert_zero(wire)}
                    }
                    let row_before=builder.progress().1;
                    let (quotient,remainder,_,range_final)=divide_public_override(builder,&numerator,
                        denominator,Some((BigUint::from(2u8),BigUint::from(denominator))));
                    assert!(builder.value(range_final),"{profile:?} r=D trips final borrow");
                    let range_row=builder.progress().1-1;
                    assert!(range_row>=row_before);
                    let q_value=read_bits(builder,&quotient);let r_value=read_bits(builder,&remainder);
                    Ok((range_row,q_value,r_value))
                }).unwrap();
            assert_eq!(invalid_q_value,BigUint::from(2u8));
            assert_eq!(invalid_r_value,BigUint::from(denominator));
            let failed=prediction_residuals(&invalid).unwrap().iter().enumerate()
                .filter_map(|(row,value)|if value.is_zero(){None}else{Some(row)}).collect::<Vec<_>>();
            assert_eq!(failed,vec![range_row],"{profile:?} only strict remainder range row fails");
            invalid.joined.joined.circuit.as_mut().unwrap().terms.retain(|term|term.row!=range_row);
            assert!(prediction_residuals(&invalid).unwrap().iter().all(Zero::is_zero),
                "{profile:?} q=2,r=D is accepted when only range row is omitted");
        }
    }
}

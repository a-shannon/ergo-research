//! Numeric mature-eight DAA finish after the A1/A2/A3 join.
//! Historical grid authentication and short-window selection are separate joins.
use ark_bn254::Fr;
use ark_ff::{One,Zero};
use num_bigint::{BigInt,BigUint,Sign};
use num_traits::ToPrimitive;
use crate::daa_integer::{self,Builder,Epoch,OutputBits};
use crate::daa_regression::{self,CompiledPrediction,Increment,PredictionInput,PredictionOutput,
    Progress,RegressionOutput};

pub const PREDICTION_BOUND_BITS:usize=333;
pub const INITIAL_DIFFICULTY_HEX:&str="011765000000";

#[derive(Clone,Debug)]
pub struct FinishOutput{
    pub use_prediction:usize,pub predictive:Vec<usize>,
    pub lower:Option<Vec<usize>>,pub upper:Option<Vec<usize>>,
    pub limited:Option<Vec<usize>>,pub average_magnitude:Option<Vec<usize>>,
    pub average_negative:Option<usize>,pub precompact:Option<Vec<usize>>,
    pub numeric_result:Vec<usize>,
}
pub struct CompiledFinish{
    pub joined:CompiledPrediction,pub output:FinishOutput,pub increment:Increment,
    pub child_nbits:Option<[usize;32]>,
    #[cfg(test)]
    pub(crate) intercept_count_trace:Option<daa_regression::SignedDivisionTrace>,
}

fn bit_value(value:&BigUint,index:usize)->bool{
    value.to_bytes_le().get(index/8).map(|byte|(byte>>(index%8))&1!=0).unwrap_or(false)
}
fn read_bits(builder:&Builder,bits:&[usize])->BigUint{
    let mut bytes=vec![0u8;bits.len().div_ceil(8)];
    for (i,&wire) in bits.iter().enumerate(){if builder.value(wire){bytes[i/8]|=1<<(i%8);}}
    BigUint::from_bytes_le(&bytes)
}
fn limb(builder:&Builder,bits:&[usize],column:usize)->u64{
    (0..16).fold(0u64,|value,i|{
        value|((bits.get(16*column+i).map(|&wire|builder.value(wire)).unwrap_or(false) as u64)<<i)
    })
}
fn limb_terms(bits:&[usize],column:usize,coefficient:Fr)->Vec<crate::gkr::Gate>{
    (0..16).filter_map(|i|bits.get(16*column+i).map(|&wire|
        Builder::linear(wire,coefficient*Fr::from(1u64<<i)))).collect()
}
fn wire_terms(bits:&[usize],coefficient:Fr)->Vec<crate::gkr::Gate>{
    bits.iter().enumerate().map(|(i,&wire)|Builder::linear(wire,coefficient*Fr::from(1u64<<i))).collect()
}
fn bit_or(builder:&mut Builder,a:usize,b:usize)->usize{
    let out=builder.bit(builder.value(a)||builder.value(b));
    builder.row(vec![Builder::linear(out,Fr::one()),Builder::linear(a,-Fr::one()),
        Builder::linear(b,-Fr::one()),Builder::product(a,b,Fr::one())]);out
}
fn initial()->BigUint{BigUint::parse_bytes(INITIAL_DIFFICULTY_HEX.as_bytes(),16).unwrap()}

/// Numeric decode(encode(v)) for v >= 0. A suffix OR at bit 8j+23 controls
/// removal of byte j, matching Java's signed BigInteger byte length.
fn compact_positive_with_trace(builder:&mut Builder,input:&[usize],trace:Option<&mut Vec<Option<usize>>>)
    ->Vec<usize>{
    let mut suffix=vec![None;input.len()+1];
    for i in (0..input.len()).rev(){
        suffix[i]=Some(if let Some(next)=suffix[i+1]{bit_or(builder,input[i],next)}else{input[i]});
    }
    let output=input.iter().enumerate().map(|(i,&wire)|{
        let threshold=8*(i/8)+23;
        if threshold>=input.len(){return wire;}
        let high=suffix[threshold].expect("suffix flag");
        let out=builder.bit(builder.value(wire)&&!builder.value(high));
        builder.row(vec![Builder::linear(out,Fr::one()),Builder::linear(wire,-Fr::one()),
            Builder::product(wire,high,Fr::one())]);out
    }).collect();
    if let Some(trace)=trace{*trace=suffix;}
    output
}
pub(crate) fn compact_positive(builder:&mut Builder,input:&[usize])->Vec<usize>{
    compact_positive_with_trace(builder,input,None)
}
fn choose_fallback(builder:&mut Builder,prediction:&PredictionOutput)->(usize,Vec<usize>){
    for &high in &prediction.prediction_magnitude[PREDICTION_BOUND_BITS..]{builder.assert_zero(high);}
    let magnitude=&prediction.prediction_magnitude[..PREDICTION_BOUND_BITS];
    let nonzero=builder.nonzero_unasserted(magnitude);
    let nonnegative=builder.not(prediction.prediction_negative);
    let use_prediction=builder.and(nonzero,nonnegative);
    let fixed=initial();
    assert!(fixed.bits()<=256);
    let selected=magnitude.iter().enumerate().map(|(i,&source)|{
        let constant=bit_value(&fixed,i);
        let assigned=if builder.value(use_prediction){builder.value(source)}else{constant};
        let out=builder.bit(assigned);
        if constant{
            builder.row(vec![Builder::linear(out,Fr::one()),Builder::constant(-Fr::one()),
                Builder::linear(use_prediction,Fr::one()),Builder::product(use_prediction,source,-Fr::one())]);
        }else{
            builder.row(vec![Builder::linear(out,Fr::one()),Builder::product(use_prediction,source,-Fr::one())]);
        }
        out
    }).collect();
    (use_prediction,selected)
}
fn add_positive(builder:&mut Builder,a:&[usize],b:&[usize],width:usize)->Vec<usize>{
    let value=read_bits(builder,a)+read_bits(builder,b);
    assert!(value.bits()<=width as u64);
    let out=builder.bits_big(&value,width);
    let mut carry=0u64;let mut previous=None;
    for column in 0..width.div_ceil(16){
        let sum=limb(builder,a,column)+limb(builder,b,column)+carry;
        carry=sum>>16;assert!(carry<=1);
        let next=if column+1<width.div_ceil(16){Some(builder.bit(carry!=0))}else{None};
        let mut row=limb_terms(a,column,Fr::one());row.extend(limb_terms(b,column,Fr::one()));
        if let Some(wire)=previous{row.push(Builder::linear(wire,Fr::one()));}
        row.extend(limb_terms(&out,column,-Fr::one()));
        if let Some(wire)=next{row.push(Builder::linear(wire,-Fr::from(1u64<<16)));}
        builder.row(row);previous=next;
    }
    assert_eq!(carry,0);builder.note_column_bound(18);out
}
/// Fixed-width unsigned comparator. Each 16-bit difference and borrow is
/// Boolean; the integer residual of a column is below 2^18 for any assignment.
fn less(builder:&mut Builder,a:&[usize],b:&[usize])->usize{
    let width=a.len().max(b.len()).div_ceil(16)*16;
    let mut borrow=builder.bit(false);builder.assert_zero(borrow);
    for column in 0..width/16{
        let raw=limb(builder,a,column) as i64-limb(builder,b,column) as i64-builder.value(borrow) as i64;
        let difference=builder.bits_u64((raw&0xffff) as u64,16);
        let next=builder.bit(raw<0);
        let mut row=limb_terms(a,column,Fr::one());row.extend(limb_terms(b,column,-Fr::one()));
        row.push(Builder::linear(borrow,-Fr::one()));
        row.extend(wire_terms(&difference,-Fr::one()));
        row.push(Builder::linear(next,Fr::from(1u64<<16)));
        builder.row(row);borrow=next;
    }
    builder.note_column_bound(18);borrow
}
fn clamp(builder:&mut Builder,value:&[usize],negative:Option<usize>,lower:&[usize],upper:&[usize])
    ->Vec<usize>{
    let below_magnitude=less(builder,value,lower);
    let above_magnitude=less(builder,upper,value);
    let (below,above)=if let Some(sign)=negative{
        let below=bit_or(builder,sign,below_magnitude);
        let positive=builder.not(sign);
        (below,builder.and(positive,above_magnitude))
    }else{(below_magnitude,above_magnitude)};
    let not_below=builder.not(below);let not_above=builder.not(above);
    let middle=builder.and(not_below,not_above);
    builder.row(vec![Builder::linear(below,Fr::one()),Builder::linear(middle,Fr::one()),
        Builder::linear(above,Fr::one()),Builder::constant(-Fr::one())]);
    let output=(0..upper.len()).map(|i|{
        let selected=if builder.value(below){builder.value(lower[i])}
            else if builder.value(above){builder.value(upper[i])}
            else{value.get(i).map(|&w|builder.value(w)).unwrap_or(false)};
        let out=builder.bit(selected);
        let mut row=vec![Builder::linear(out,Fr::one()),Builder::product(below,lower[i],-Fr::one()),
            Builder::product(above,upper[i],-Fr::one())];
        if let Some(&source)=value.get(i){row.push(Builder::product(middle,source,-Fr::one()));}
        builder.row(row);out
    }).collect::<Vec<_>>();
    for &high in value.iter().skip(upper.len()){
        builder.row(vec![Builder::product(middle,high,Fr::one())]);
    }
    output
}
fn emit_finish(builder:&mut Builder,a1:&[OutputBits],regression:&RegressionOutput,
    prediction:&PredictionOutput,epoch:Epoch)->Result<(FinishOutput,Increment),String>{
    if a1.len()!=8{return Err("finish requires eight A1 outputs".into());}
    let before=Progress::from(builder.progress());
    let (use_prediction,selected)=choose_fallback(builder,prediction);
    let predictive=compact_positive(builder,&selected);
    let (lower,upper,limited,average_magnitude,average_negative,precompact,numeric_result)=
        if epoch==Epoch::Legacy{
            (None,None,None,None,None,None,predictive.clone())
        }else{
            let last=&a1[7].decoded_difficulty;
            let zero=builder.bit(false);builder.assert_zero(zero);
            let mut lower=last.iter().skip(1).copied().collect::<Vec<_>>();lower.push(zero);lower.push(zero);
            let mut last_extended=last.clone();last_extended.push(zero);
            let upper=add_positive(builder,&last_extended,&lower,257);
            let limited=clamp(builder,&predictive,None,&lower,&upper);
            let classic=&regression.aliases[7];
            let sources=[(classic.magnitude.as_slice(),classic.negative),(limited.as_slice(),zero)];
            let (sum_magnitude,sum_negative,_,_)=daa_regression::emit_signed_sum(
                builder,&sources,&[1,1],epoch.numerator_bits()+1)?;
            let average_magnitude=sum_magnitude[1..].to_vec();
            let average_nonzero=builder.nonzero_unasserted(&average_magnitude);
            let average_negative=builder.and(sum_negative,average_nonzero);
            let precompact=clamp(builder,&average_magnitude,Some(average_negative),&lower,&upper);
            let numeric_result=compact_positive(builder,&precompact);
            (Some(lower),Some(upper),Some(limited),Some(average_magnitude),Some(average_negative),
                Some(precompact),numeric_result)
        };
    let after=Progress::from(builder.progress());
    let increment=Increment{before,after,added_live_bits:after.live_bits-before.live_bits,
        added_rows:after.rows-before.rows,added_terms:after.terms-before.terms};
    Ok((FinishOutput{use_prediction,predictive,lower,upper,limited,average_magnitude,
        average_negative,precompact,numeric_result},increment))
}
pub fn compile_finish(epoch:Epoch,q:&BigUint,input:PredictionInput,materialize:bool)
    ->Result<CompiledFinish,String>{
    compile_finish_inner(epoch,q,input,materialize,None)
}
pub fn compile_finish_with_child(epoch:Epoch,q:&BigUint,input:PredictionInput,child_nbits:u32,
    materialize:bool)->Result<CompiledFinish,String>{
    compile_finish_inner(epoch,q,input,materialize,Some(child_nbits))
}
fn compile_finish_inner(epoch:Epoch,q:&BigUint,input:PredictionInput,materialize:bool,
    child_nbits:Option<u32>)->Result<CompiledFinish,String>{
    let (joined,(output,increment,child_nbits))=daa_regression::compile_prediction_extended(
        epoch,q,input,materialize,|builder,a1,regression,prediction|{
            let (output,increment)=emit_finish(builder,a1,regression,prediction,epoch)?;
            let child_nbits=child_nbits.map(|raw|daa_integer::bind_child_nbits_to_result(
                builder,raw,q,&output.numeric_result)).transpose()?;
            Ok((output,increment,child_nbits))
        })?;
    Ok(CompiledFinish{joined,output,increment,child_nbits,
        #[cfg(test)] intercept_count_trace:None})
}
pub fn finish_residuals(compiled:&CompiledFinish)->Result<Vec<Fr>,String>{
    daa_regression::prediction_residuals(&compiled.joined)
}

/// Legacy child3073 numeric profile for increasing selected samples only.
/// Timestamp fallback and sparse sample ancestry require separate relations.
pub(crate) fn compile_two_finish_with_child(q:&BigUint,input:daa_integer::TwoRatioInputs,
    child_nbits:u32,materialize:bool)->Result<CompiledFinish,String>{
    if input.timestamps.windows(2).any(|pair| pair[0]>=pair[1]) {
        return Err("two-ratio local profile requires increasing sample timestamps".into());
    }
    let (joined,(output,increment,child_nbits))=daa_regression::two_ratio::compile_extended(
        q,input,materialize,|builder,a1,_,prediction|{
            if a1.len()!=2{return Err("Legacy two-ratio finish requires two A1 outputs".into());}
            let before=Progress::from(builder.progress());
            let (use_prediction,selected)=choose_fallback(builder,prediction);
            let predictive=compact_positive(builder,&selected);
            let output=FinishOutput{use_prediction,numeric_result:predictive.clone(),predictive,
                lower:None,upper:None,limited:None,average_magnitude:None,
                average_negative:None,precompact:None};
            let after=Progress::from(builder.progress());
            let increment=Increment{before,after,added_live_bits:after.live_bits-before.live_bits,
                added_rows:after.rows-before.rows,added_terms:after.terms-before.terms};
            let child_nbits=daa_integer::bind_child_nbits_to_result(builder,child_nbits,q,&output.numeric_result)?;
            Ok((output,increment,Some(child_nbits)))
        })?;
    Ok(CompiledFinish{joined,output,increment,child_nbits,
        #[cfg(test)] intercept_count_trace:None})
}

/// Legacy m=3..7 numeric finish for strictly increasing local sample times.
pub(crate) fn compile_short_legacy(q:&BigUint,input:daa_integer::ShortLegacyInputs,
    materialize:bool)->Result<CompiledFinish,String>{
    compile_short_inner(q,input,None,materialize)
}
pub(crate) fn compile_short_legacy_with_child(q:&BigUint,input:daa_integer::ShortLegacyInputs,
    child_nbits:u32,materialize:bool)->Result<CompiledFinish,String>{
    compile_short_inner(q,input,Some(child_nbits),materialize)
}
fn compile_short_inner(q:&BigUint,input:daa_integer::ShortLegacyInputs,child_nbits:Option<u32>,
    materialize:bool)->Result<CompiledFinish,String>{
    let m=input.profile.count();
    if input.nbits.len()!=m||input.timestamps.len()!=m+1{
        return Err("short Legacy input shape does not match profile".into());
    }
    if input.timestamps.windows(2).any(|pair|pair[0]>=pair[1]){
        return Err("short Legacy local profile requires increasing sample timestamps".into());
    }
    #[cfg(test)]
    let mut intercept_count_trace=None;
    let (joined,(output,increment,child_nbits))=daa_regression::short_legacy::compile_extended(
        q,input,materialize,|builder,a1,_,prediction,_intercept_count_division|{
            #[cfg(test)]
            { intercept_count_trace=Some(_intercept_count_division.clone()); }
            if a1.len()!=m{return Err("short Legacy finish profile count".into());}
            let before=Progress::from(builder.progress());
            let (use_prediction,selected)=choose_fallback(builder,prediction);
            let predictive=compact_positive(builder,&selected);
            let output=FinishOutput{use_prediction,numeric_result:predictive.clone(),predictive,
                lower:None,upper:None,limited:None,average_magnitude:None,
                average_negative:None,precompact:None};
            let after=Progress::from(builder.progress());
            let increment=Increment{before,after,added_live_bits:after.live_bits-before.live_bits,
                added_rows:after.rows-before.rows,added_terms:after.terms-before.terms};
            let child_nbits=child_nbits.map(|raw|daa_integer::bind_child_nbits_to_result(
                builder,raw,q,&output.numeric_result)).transpose()?;
            Ok((output,increment,child_nbits))
        })?;
    Ok(CompiledFinish{joined,output,increment,child_nbits,
        #[cfg(test)] intercept_count_trace})
}

#[cfg(test)]
mod two_ratio_tests {
    use super::*;
    #[test]
    fn two_ratio_legacy_finish_prediction_fallback_and_timestamp_domain() {
        for (deltas,expected_prediction) in [([1i64,1i64],true),([7,3],true),([1,100],false),([1,2],false)] {
            let input=daa_integer::TwoRatioInputs{nbits:[0x03000001;2],
                timestamps:[0,deltas[0],deltas[0]+deltas[1]]};
            let prediction=daa_regression::two_ratio::compile(&crate::daa_count::q(),input,true).unwrap();
            let p=daa_regression::signed_value(&prediction.joined.joined.witness,
                &prediction.output.prediction_magnitude,prediction.output.prediction_negative);
            let chosen=if p>=BigInt::from(1u8){p.to_biguint().unwrap()}else{initial()};
            let (raw,expected)=native_positive_compact_roundtrip(&chosen);
            let mut c=compile_two_finish_with_child(&crate::daa_count::q(),input,raw,true).unwrap();
            assert!(finish_residuals(&c).unwrap().iter().all(Zero::is_zero));
            let w=&c.joined.joined.joined.witness;
            let actual=c.output.numeric_result.iter().enumerate().fold(BigUint::zero(),|v,(i,&wire)|
                if w[wire].is_one(){v+(BigUint::one()<<i)}else{v});
            assert_eq!(actual,expected);
            assert_eq!(w[c.output.use_prediction],Fr::from(expected_prediction as u64));
            let flag=c.output.use_prediction;
            c.joined.joined.joined.witness[flag]=Fr::one()-c.joined.joined.joined.witness[flag];
            assert!(finish_residuals(&c).unwrap().iter().any(|r|!r.is_zero()));
        }
        for timestamps in [[0,0,1],[0,2,1],[2,1,0]] {
            let input=daa_integer::TwoRatioInputs{nbits:[0x03000001;2],timestamps};
            assert!(compile_two_finish_with_child(&crate::daa_count::q(),input,0x03000001,true)
                .err().unwrap().contains("requires increasing"));
        }
    }
}

/// Independent byte-oriented model of Scala's positive compact roundtrip.
pub fn native_positive_compact_roundtrip(value:&BigUint)->(u32,BigUint){
    let signed=BigInt::from_biguint(Sign::Plus,value.clone()).to_signed_bytes_be();
    let mut size=signed.len();
    let mut mantissa=if size<=3{(value<<(8*(3-size))).to_u64().unwrap()}
        else{(value>>(8*(size-3))).to_u64().unwrap()};
    if mantissa&0x0080_0000!=0{mantissa>>=8;size+=1;}
    assert!(size<=255 && mantissa<0x0080_0000);
    let compact=((size as u32)<<24)|(mantissa as u32);
    let decoded=if size<=3{BigUint::from(mantissa)>>(8*(3-size))}
        else{BigUint::from(mantissa)<<(8*(size-3))};
    (compact,decoded)
}
pub fn native_finish_oracle(epoch:Epoch,prediction:&BigInt,classic:&BigInt,last:&BigUint)
    ->Result<BigUint,String>{
    if last.is_zero(){return Err("last difficulty must be positive".into());}
    let selected=if prediction> &BigInt::zero(){prediction.to_biguint().unwrap()}else{initial()};
    let predictive=native_positive_compact_roundtrip(&selected).1;
    if epoch==Epoch::Legacy{return Ok(predictive);}
    let lower=last>>1usize;let upper=last+&lower;
    let limited=predictive.max(lower.clone()).min(upper.clone());
    let average=(classic+BigInt::from_biguint(Sign::Plus,limited))/BigInt::from(2u8);
    let clamped=average.max(BigInt::from_biguint(Sign::Plus,lower))
        .min(BigInt::from_biguint(Sign::Plus,upper));
    Ok(native_positive_compact_roundtrip(&clamped.to_biguint().unwrap()).1)
}

#[cfg(test)]
mod short_legacy_tests{
    use super::*;
    use crate::daa_integer::{ShortLegacyInputs,ShortLegacyProfile};
    fn fixture(profile:ShortLegacyProfile)->ShortLegacyInputs{
        crate::daa_integer::mainnet_short_legacy_test_inputs(profile)
    }
    fn values(compiled:&CompiledFinish)->Vec<BigInt>{
        compiled.joined.joined.joined.output.iter().map(|output|
            daa_regression::signed_value(&compiled.joined.joined.joined.witness,
                &output.quotient_magnitude,output.quotient_negative)).collect()
    }
    fn bits(witness:&[Fr],wires:&[usize])->BigUint{
        let mut bytes=vec![0u8;wires.len().div_ceil(8)];
        for (i,&wire) in wires.iter().enumerate(){if witness[wire]==Fr::one(){bytes[i/8]|=1<<(i%8);}}
        BigUint::from_bytes_le(&bytes)
    }
    fn set_bits(witness:&mut [Fr],wires:&[usize],value:&BigUint){
        for (i,&wire) in wires.iter().enumerate(){
            witness[wire]=Fr::from(((value>>(i as usize))&BigUint::one()).to_u64_digits().first().copied().unwrap_or(0));
        }
    }
    fn failures(compiled:&CompiledFinish)->Vec<usize>{
        daa_regression::prediction_residuals(&compiled.joined).unwrap().iter().enumerate()
            .filter_map(|(row,value)|if value.is_zero(){None}else{Some(row)}).collect()
    }
    fn flip_and_restore(compiled:&mut CompiledFinish,wire:usize)->Vec<usize>{
        let witness=&mut compiled.joined.joined.joined.witness;
        let old=witness[wire];witness[wire]=Fr::one()-old;let failed=failures(compiled);
        compiled.joined.joined.joined.witness[wire]=old;failed
    }
    #[test]
    fn short_legacy_real_prefixes_match_unsimplified_bigint_and_compacts(){
        let profiles=[ShortLegacyProfile::M3,ShortLegacyProfile::M4,ShortLegacyProfile::M5,
            ShortLegacyProfile::M6,ShortLegacyProfile::M7];
        let expected_prediction=["209121100561880","208128758099145","194856715501454",
            "188495223007494","178708529591783"];
        let expected_raw=[0x0700_be31,0x0700_bd4a,0x0700_b138,0x0700_ab6f,0x0700_a288];
        let q=crate::daa_count::q();
        for (index,profile) in profiles.into_iter().enumerate(){
            let input=fixture(profile);let compiled=compile_short_legacy(&q,input.clone(),true).unwrap();
            assert!(finish_residuals(&compiled).unwrap().iter().all(Zero::is_zero),"{profile:?}");
            let ys=values(&compiled);let (slope,intercept,prediction)
                =daa_regression::short_legacy::native_oracle(&ys).unwrap();
            let witness=&compiled.joined.joined.joined.witness;
            let regression=&compiled.joined.joined.output;
            let predicted=&compiled.joined.output;
            assert_eq!(daa_regression::signed_value(witness,&regression.slope_magnitude,
                regression.slope_negative),slope,"{profile:?} slope");
            assert_eq!(daa_regression::signed_value(witness,&predicted.a_magnitude,
                predicted.a_negative),intercept,"{profile:?} intercept");
            assert_eq!(daa_regression::signed_value(witness,&predicted.term_magnitude,
                predicted.term_negative),&slope*BigInt::from(2048+1024*profile.count())
                    /BigInt::from(daa_regression::PRECISION),"{profile:?} term");
            assert_eq!(daa_regression::signed_value(witness,&predicted.prediction_magnitude,
                predicted.prediction_negative),prediction,"{profile:?} prediction");
            assert_eq!(prediction.to_string(),expected_prediction[index],"{profile:?}");
            let (raw,decoded)=native_positive_compact_roundtrip(&prediction.to_biguint().unwrap());
            assert_eq!(raw,expected_raw[index],"{profile:?} compact");
            assert_eq!(bits(witness,&compiled.output.numeric_result),decoded,"{profile:?} compact roundtrip");
            let m=profile.count();
            let exact=compile_short_legacy_with_child(&q,input.clone(),raw,true).unwrap();
            assert!(finish_residuals(&exact).unwrap().iter().all(Zero::is_zero),"{profile:?} child compact");
            assert!(exact.child_nbits.is_some(),"{profile:?} child is bound");
            let count=&exact.joined.joined.joined.count;
            println!("short-legacy-child profile={profile:?} m={m} input_len={} row_count={} terms={} live_bits={}",
                count.padded_input_bits,count.padded_rows,count.terms,count.live_bits);
            if profile==ShortLegacyProfile::M7{
                let mismatch=compile_short_legacy_with_child(&q,fixture(profile),raw^1,true).unwrap();
                let failed=failures(&mismatch);
                assert_eq!(failed.len(),1,"child compact mismatch must isolate one decoded equality bit");
            }
        }
    }
    #[test]
    fn short_legacy_timestamp_admission_checks_each_edge_before_math(){
        let q=crate::daa_count::q();
        for profile in [ShortLegacyProfile::M3,ShortLegacyProfile::M4,ShortLegacyProfile::M5,
            ShortLegacyProfile::M6,ShortLegacyProfile::M7]{
            let m=profile.count();
            for edge in 0..m{
                for decreasing in [false,true]{
                    let mut input=fixture(profile);input.timestamps=(0..=m as i64).collect();
                    input.timestamps[edge+1]=input.timestamps[edge]+if decreasing{-1}else{0};
                    let error=compile_short_legacy_with_child(&q,input,0x0300_0001,false)
                        .err().expect("non-increasing timestamps rejected");
                    assert!(error.contains("requires increasing"),"profile={profile:?}, edge={edge}, {error}");
                }
            }
        }
    }
    #[test]
    fn short_legacy_negative_forecast_uses_legacy_fallback(){
        let q=crate::daa_count::q();let initial=initial();
        let input=ShortLegacyInputs{profile:ShortLegacyProfile::M3,
            nbits:vec![0x0300_0001;3],timestamps:vec![0,120_000,12_120_000,132_120_000]};
        let mut compiled=compile_short_legacy(&q,input,true).unwrap();
        assert!(failures(&compiled).is_empty());
        let w=&compiled.joined.joined.joined.witness;
        assert!(daa_regression::signed_value(w,&compiled.joined.output.prediction_magnitude,
            compiled.joined.output.prediction_negative)<BigInt::from(1u8));
        assert_eq!(w[compiled.output.use_prediction],Fr::zero());
        assert_eq!(bits(w,&compiled.output.numeric_result),native_positive_compact_roundtrip(&initial).1);
        let selector=compiled.output.use_prediction;
        assert!(!flip_and_restore(&mut compiled,selector).is_empty());
    }
    #[test]
    fn short_legacy_signed_nonexact_slope_and_strict_remainder_bound_each_profile(){
        let q=crate::daa_count::q();
        let profiles=[(ShortLegacyProfile::M3,2048u64),(ShortLegacyProfile::M4,10240),
            (ShortLegacyProfile::M5,10240),(ShortLegacyProfile::M6,35840),(ShortLegacyProfile::M7,28672)];
        let expected_remainders=[-1536i64,-7680,-5120,-23040,-27136];
        for (profile,denom) in profiles{
            let m=profile.count();let mut deltas=[1i64,-2,3,-4,5,-6,7];
            deltas[m-1]=if m%2==1{7}else{-7};let mut timestamps=vec![0i64];
            for delta in &deltas[..m]{timestamps.push(timestamps.last().unwrap()+delta);}
            let input=ShortLegacyInputs{profile,nbits:vec![0x0300_0001;m],timestamps};
            let mut compiled=daa_regression::short_legacy::compile(&q,input,true).unwrap();
            let residuals=daa_regression::prediction_residuals(&compiled).unwrap();
            assert!(residuals.iter().all(Zero::is_zero),"{profile:?}");
            let witness=&compiled.joined.joined.witness;
            let ys=compiled.joined.joined.output.iter().map(|output|
                daa_regression::signed_value(witness,&output.quotient_magnitude,output.quotient_negative))
                .collect::<Vec<_>>();
            assert!(ys.iter().any(|y|y.sign()==Sign::Minus),"{profile:?} signed A1 inputs");
            let (slope,_,prediction)=daa_regression::short_legacy::native_oracle(&ys).unwrap();
            assert_eq!(slope.sign(),Sign::Minus,"{profile:?} signed slope");
            assert_eq!(daa_regression::signed_value(witness,&compiled.joined.output.slope_magnitude,
                compiled.joined.output.slope_negative),slope,"{profile:?}");
            assert_eq!(daa_regression::signed_value(witness,&compiled.output.prediction_magnitude,
                compiled.output.prediction_negative),prediction,"{profile:?}");
            let remainder=daa_regression::signed_value(witness,&compiled.joined.output.remainder,
                compiled.joined.output.remainder_negative);
            assert_eq!(remainder,BigInt::from(expected_remainders[profile.count()-3]),
                "{profile:?} independent synthetic nonexact remainder");
            let wires=compiled.joined.output.remainder.clone();
            set_bits(&mut compiled.joined.joined.witness,&wires,&BigUint::from(denom));
            assert!(daa_regression::prediction_residuals(&compiled).unwrap().iter()
                .any(|row|!row.is_zero()),"{profile:?} remainder equal to denominator rejected");
        }
    }
    #[test]
    fn short_legacy_output_aliases_and_arithmetic_boundaries_have_causal_rows(){
        let q=crate::daa_count::q();let input=fixture(ShortLegacyProfile::M7);
        let base=compile_short_legacy(&q,input.clone(),true).unwrap();
        assert!(failures(&base).is_empty());
        let aliases=base.joined.joined.output.aliases.clone();
        for (index,alias) in aliases.iter().enumerate(){
            let original=bits(&base.joined.joined.joined.witness,&alias.magnitude);
            let sign=base.joined.joined.joined.witness[alias.negative]==Fr::one();
            let alternate=if original.bit(0){&original-BigUint::one()}else{&original+BigUint::one()};
            for (magnitude,negative,row) in [
                (alternate,sign,alias.magnitude_binding_rows[0]),
                (original,!sign,alias.sign_binding_row)]{
                let mut changed=daa_regression::short_legacy::compile_alias_override(&q,input.clone(),
                    true,index,magnitude,negative).unwrap();
                let failed=daa_regression::prediction_residuals(&changed).unwrap().iter().enumerate()
                    .filter_map(|(row,value)|if value.is_zero(){None}else{Some(row)}).collect::<Vec<_>>();
                assert_eq!(failed,vec![row],"alias={index}, binding row");
                changed.joined.joined.circuit.as_mut().unwrap().terms.retain(|term|term.row!=row);
                assert!(daa_regression::prediction_residuals(&changed).unwrap().iter().all(Zero::is_zero),
                    "omitting alias binding accepts the consistently recomputed alternate witness");
            }
        }

        let input=fixture(ShortLegacyProfile::M3);
        let mut compiled=compile_short_legacy(&q,input.clone(),true).unwrap();
        let aliases=compiled.joined.joined.output.aliases.clone();
        assert_eq!(aliases.len(),3);
        let slope_wire=compiled.joined.joined.output.slope_magnitude[0];
        let slope_remainder=compiled.joined.joined.output.remainder[0];
        let intercept_wire=compiled.joined.output.a_magnitude[0];
        let intercept_remainder=compiled.joined.output.a_remainder[0];
        let point_wire=compiled.joined.output.point_magnitude[0];
        let point_row=compiled.joined.output.point_binding_rows[0];
        let term_wire=compiled.joined.output.term_magnitude[0];
        let term_remainder=compiled.joined.output.term_remainder[0];
        let compact_wire=compiled.output.numeric_result[0];
        assert!(!flip_and_restore(&mut compiled,slope_wire).is_empty());
        assert!(!flip_and_restore(&mut compiled,slope_remainder).is_empty());
        assert!(!flip_and_restore(&mut compiled,intercept_wire).is_empty());
        assert!(!flip_and_restore(&mut compiled,intercept_remainder).is_empty());
        let point_failures=flip_and_restore(&mut compiled,point_wire);
        assert!(point_failures.contains(&point_row));
        assert!(point_failures.iter().any(|&row|row!=point_row),"raw point fault also reaches downstream product");
        let point_value=bits(&compiled.joined.joined.joined.witness,&compiled.joined.output.point_magnitude);
        let point_negative=compiled.joined.joined.joined.witness[compiled.joined.output.point_negative]==Fr::one();
        let alternate_point=if point_value.bit(0){&point_value-BigUint::one()}else{&point_value+BigUint::one()};
        let mut changed_point=daa_regression::short_legacy::compile_point_override(&q,input.clone(),true,
            alternate_point,point_negative).unwrap();
        let point_binding=changed_point.output.point_binding_rows[0];
        assert_eq!(daa_regression::prediction_residuals(&changed_point).unwrap().iter().enumerate()
            .filter_map(|(row,value)|if value.is_zero(){None}else{Some(row)}).collect::<Vec<_>>(),
            vec![point_binding],"coherent point magnitude override fails only its binding");
        changed_point.joined.joined.circuit.as_mut().unwrap().terms.retain(|term|term.row!=point_binding);
        assert!(daa_regression::prediction_residuals(&changed_point).unwrap().iter().all(Zero::is_zero),
            "omitting only point magnitude binding accepts the recomputed forecast");
        let mut changed_sign=daa_regression::short_legacy::compile_point_override(&q,input.clone(),true,
            point_value,!point_negative).unwrap();
        let sign_binding=*changed_sign.output.point_binding_rows.last().unwrap();
        assert_eq!(daa_regression::prediction_residuals(&changed_sign).unwrap().iter().enumerate()
            .filter_map(|(row,value)|if value.is_zero(){None}else{Some(row)}).collect::<Vec<_>>(),
            vec![sign_binding],"coherent point sign override fails only its binding");
        changed_sign.joined.joined.circuit.as_mut().unwrap().terms.retain(|term|term.row!=sign_binding);
        assert!(daa_regression::prediction_residuals(&changed_sign).unwrap().iter().all(Zero::is_zero),
            "omitting only point sign binding accepts the recomputed forecast");
        assert!(!flip_and_restore(&mut compiled,term_wire).is_empty());
        assert!(!flip_and_restore(&mut compiled,term_remainder).is_empty());
        assert!(!flip_and_restore(&mut compiled,compact_wire).is_empty());
        let (joined,trace)=daa_regression::short_legacy::compile_extended(&q,input,true,
            |_,_,_,_,trace|Ok(trace.clone())).unwrap();
        assert!(!daa_regression::prediction_residuals(&joined).unwrap().iter().any(|r|!r.is_zero()));
        let mut traced=joined;
        for wires in [&trace.quotient_magnitude,&trace.remainder_magnitude]{
            let witness=&mut traced.joined.joined.witness;let wire=wires[0];let old=witness[wire];
            witness[wire]=Fr::one()-old;
            assert!(daa_regression::prediction_residuals(&traced).unwrap().iter().any(|r|!r.is_zero()));
            traced.joined.joined.witness[wire]=old;
        }
        for wire in [trace.quotient_negative,trace.remainder_negative]{
            let witness=&mut traced.joined.joined.witness;let old=witness[wire];witness[wire]=Fr::one()-old;
            assert!(daa_regression::prediction_residuals(&traced).unwrap().iter().any(|r|!r.is_zero()));
            traced.joined.joined.witness[wire]=old;
        }
    }
}

#[cfg(test)]
mod tests{
    use super::*;
    use crate::{daa_count,daa_integer::WindowInputs};

    fn hex(bytes:&[u8])->String{bytes.iter().map(|b|format!("{b:02x}")).collect()}
    fn input(epoch:Epoch,deltas:[i64;8],last_nbits:u32,x0:u32)->PredictionInput{
        let mut timestamps=[0i64;9];
        for i in 0..8{timestamps[i+1]=timestamps[i].wrapping_add(deltas[i]);}
        let mut nbits=[0x03000001;8];nbits[7]=last_nbits;
        let _=epoch;
        PredictionInput{window:WindowInputs{nbits,timestamps},x0}
    }
    fn failed(compiled:&CompiledPrediction)->Vec<usize>{
        daa_regression::prediction_residuals(compiled).unwrap().iter().enumerate()
            .filter_map(|(i,value)|if value.is_zero(){None}else{Some(i)}).collect()
    }
    fn witness_big(witness:&[Fr],bits:&[usize])->BigUint{
        let mut bytes=vec![0u8;bits.len().div_ceil(8)];
        for (i,&wire) in bits.iter().enumerate(){if witness[wire]==Fr::one(){bytes[i/8]|=1<<(i%8);}}
        BigUint::from_bytes_le(&bytes)
    }
    fn set_bits(witness:&mut [Fr],bits:&[usize],value:&BigUint){
        for (i,&wire) in bits.iter().enumerate(){witness[wire]=Fr::from(bit_value(value,i) as u64);}
    }
    fn omit(compiled:&mut CompiledPrediction,rows:&[usize]){
        compiled.joined.joined.circuit.as_mut().unwrap().terms.retain(|term|!rows.contains(&term.row));
    }
    fn values(epoch:Epoch,input:PredictionInput)->([BigInt;8],BigUint){
        let multiplier=BigInt::from(120_000u64*epoch.length());
        let decoded=|nbits:u32|match nbits{0x03000001=>1u64,0x01030000=>3u64,_=>panic!("test nBits")};
        let y=std::array::from_fn(|j|{
            let d=decoded(input.window.nbits[j]);
            BigInt::from(d)*&multiplier
                /BigInt::from(input.window.timestamps[j+1]-input.window.timestamps[j])
        });
        (y,BigUint::from(decoded(input.window.nbits[7])))
    }
    #[test]
    fn a4_child_nbits_numeric_join_preserves_aliases_and_rejects_mismatch(){
        for epoch in [Epoch::Legacy,Epoch::Eip]{
            let spacing=i64::try_from(120_000*epoch.length()).unwrap();
            let fixture=input(epoch,[spacing;8],0x03000001,0);
            for raw in [0x03000001,0x01010000,0x0101ffff]{
                assert_eq!(crate::work_tree_work::native_decode(raw).unwrap(),BigUint::one());
                let compiled=compile_finish_with_child(epoch,&daa_count::q(),fixture,raw,true).unwrap();
                assert!(failed(&compiled.joined).is_empty(),"epoch={epoch:?}, child nBits={raw:08x}");
                let witness=&compiled.joined.joined.joined.witness;
                assert_eq!(witness_big(witness,&compiled.output.numeric_result),BigUint::one());
                assert_eq!(witness_big(witness,&compiled.child_nbits.unwrap()),BigUint::from(raw as u64));
                let count=&compiled.joined.joined.joined.count;
                assert_eq!(count.source_nbits_bits,8*32+32);
                assert_eq!(count.decoded_bits,9*256);
            }
            let mut mismatch=compile_finish_with_child(
                epoch,&daa_count::q(),fixture,0x03000003,true).unwrap();
            let failing=failed(&mismatch.joined);
            assert_eq!(failing.len(),1,"child target mismatch must isolate one equality bit");
            omit(&mut mismatch.joined,&failing);
            assert!(failed(&mismatch.joined).is_empty(),"omitting the new numeric equality must admit mismatch");
        }
    }
    #[test]
    fn a4_noop_bridge_and_native_branch_differential(){
        let expected_a3=["d7e6a03cd9ae082483fcfe74577009023b061b002438ee76782c38894083009d",
            "535d2258529ff950954df35d999c22132d9ad70f2d9c87214848500f884a20b6"];
        let expected_a4=["6a3c84f89e559bca9a0129cf71e335c24b99a72c96d80b317370a48fd0636185",
            "194acd29b2f14774e0dd80fe6b97b238698e4f51639cc3a861677c3b643bfb4c"];
        let mut saw_positive=false;let mut saw_zero=false;let mut saw_negative=false;
        let mut saw_negative_classic=false;let mut saw_zero_result=false;
        let mut saw_positive_odd_average=false;let mut saw_negative_odd_average=false;
        let mut saw_zero_average=false;
        for (epoch_index,epoch) in [Epoch::Legacy,Epoch::Eip].into_iter().enumerate(){
            let e=epoch.length() as i64;let c=120_000*e;
            let cases=[([1;8],0x03000001,0u32),([1,2,3,4,5,6,7,8],0x03000001,41),
                ([8,7,6,5,4,3,2,1],0x03000001,60),([2*c;8],0x03000001,0),
                ([c;8],0x03000001,0),([1,2,3,4,5,6,7,-8],0x03000001,0),
                ([c;8],0x01030000,0)];
            let mut first_topology=None;
            for (deltas,last_nbits,x0) in cases{
                let input=input(epoch,deltas,last_nbits,x0);
                let baseline=daa_regression::compile_prediction(epoch,&daa_count::q(),input,false).unwrap();
                assert_eq!(hex(&baseline.joined.joined.count.topology_blake2b256),expected_a3[epoch_index]);
                let (noop,())=daa_regression::compile_prediction_extended(epoch,&daa_count::q(),
                    input,false,|_,_,_,_|Ok(())).unwrap();
                assert_eq!(noop.joined.joined.count.topology_blake2b256,
                    baseline.joined.joined.count.topology_blake2b256);
                assert_eq!(noop.joined.joined.count.live_bits,baseline.joined.joined.count.live_bits);
                let compiled=compile_finish(epoch,&daa_count::q(),input,true).unwrap();
                assert!(failed(&compiled.joined).is_empty());
                let count=&compiled.joined.joined.joined.count;
                assert_eq!(hex(&count.topology_blake2b256),expected_a4[epoch_index]);
                if let Some(previous)=first_topology{assert_eq!(count.topology_blake2b256,previous);}
                first_topology=Some(count.topology_blake2b256);
                let (y,last)=values(epoch,input);
                let prediction=daa_regression::native_prediction_oracle(x0 as i64,epoch,&y).2;
                saw_positive|=prediction>BigInt::zero();saw_zero|=prediction.is_zero();
                saw_negative|=prediction<BigInt::zero();saw_negative_classic|=y[7]<BigInt::zero();
                let expected=native_finish_oracle(epoch,&prediction,&y[7],&last).unwrap();
                let witness=&compiled.joined.joined.joined.witness;
                let actual=witness_big(witness,&compiled.output.numeric_result);
                assert_eq!(actual,expected,"epoch={epoch:?}, deltas={deltas:?}");
                let selected=if prediction>BigInt::zero(){prediction.to_biguint().unwrap()}
                    else{initial()};
                let predictive=native_positive_compact_roundtrip(&selected).1;
                assert_eq!(witness[compiled.output.use_prediction],
                    Fr::from((prediction>BigInt::zero()) as u64));
                assert_eq!(witness_big(witness,&compiled.output.predictive),predictive);
                if epoch==Epoch::Legacy{
                    assert!(compiled.output.lower.is_none());
                    assert_eq!(actual,witness_big(witness,&compiled.output.predictive));
                }else{
                    assert!(compiled.output.lower.is_some());
                    let lower=witness_big(witness,compiled.output.lower.as_ref().unwrap());
                    let upper=witness_big(witness,compiled.output.upper.as_ref().unwrap());
                    assert_eq!(lower,&last>>1usize);
                    assert_eq!(upper,&last+(&last>>1usize));
                    let limited=predictive.max(lower.clone()).min(upper.clone());
                    assert_eq!(witness_big(witness,compiled.output.limited.as_ref().unwrap()),limited);
                    let numerator=&y[7]+BigInt::from_biguint(Sign::Plus,limited);
                    let average=&numerator/BigInt::from(2u8);
                    let odd=bit_value(numerator.magnitude(),0);
                    saw_positive_odd_average|=average>BigInt::zero() && odd;
                    saw_negative_odd_average|=average<BigInt::zero() && odd;
                    saw_zero_average|=average.is_zero();
                    assert_eq!(witness_big(witness,compiled.output.average_magnitude.as_ref().unwrap()),
                        average.magnitude().clone());
                    assert_eq!(witness[compiled.output.average_negative.unwrap()],
                        Fr::from((average.sign()==Sign::Minus) as u64));
                    let precompact=average.max(BigInt::from_biguint(Sign::Plus,lower))
                        .min(BigInt::from_biguint(Sign::Plus,upper)).to_biguint().unwrap();
                    assert_eq!(witness_big(witness,compiled.output.precompact.as_ref().unwrap()),
                        precompact);
                    saw_zero_result|=actual.is_zero();
                }
            }
        }
        assert!(saw_positive && saw_zero && saw_negative && saw_negative_classic && saw_zero_result);
        assert!(saw_positive_odd_average && saw_negative_odd_average && saw_zero_average);
    }
    #[test]
    fn a4_compact_byte_oracle_and_isolated_mask_mutants(){
        assert_eq!(native_positive_compact_roundtrip(&BigUint::zero()).0,0x01000000);
        let mut corpus=vec![BigUint::zero(),BigUint::one(),BigUint::from(127u8),BigUint::from(128u8)];
        for k in [7usize,8,15,16,22,23,24,30,31,32,39,40,254,255,256,330,331,332]{
            let center=BigUint::one()<<k;
            corpus.push(&center-BigUint::one());corpus.push(center.clone());
            if k<332{corpus.push(center+BigUint::one());}
        }
        for h in 0..333usize{
            let v=BigUint::one()<<h;
            let (_,decoded)=native_positive_compact_roundtrip(&v);
            let dropped=if h>=23{(h-23)/8+1}else{0};
            let expected=(&v>>(8*dropped))<<(8*dropped);
            assert_eq!(decoded,expected,"highest bit {h}");
        }
        let fixture=input(Epoch::Legacy,[1;8],0x03000001,0);
        let (compiled,outputs)=daa_regression::compile_prediction_extended(Epoch::Legacy,
            &daa_count::q(),fixture,true,|builder,_,_,_|{
                Ok(corpus.iter().map(|value|{
                    let bits=builder.bits_big(value,PREDICTION_BOUND_BITS);
                    compact_positive(builder,&bits)
                }).collect::<Vec<_>>())
            }).unwrap();
        assert!(failed(&compiled).is_empty());
        for (value,bits) in corpus.iter().zip(&outputs){
            let expected=native_positive_compact_roundtrip(value).1;
            assert_eq!(witness_big(&compiled.joined.joined.witness,bits),expected,"value={value}");
        }
        let value=(BigUint::one()<<23usize)+BigUint::one();
        let make=||daa_regression::compile_prediction_extended(Epoch::Legacy,&daa_count::q(),fixture,
            true,|builder,_,_,_|{
                let bits=builder.bits_big(&value,PREDICTION_BOUND_BITS);
                let mut suffix=Vec::new();
                let output=compact_positive_with_trace(builder,&bits,Some(&mut suffix));
                Ok((output,suffix))
            }).unwrap();
        let (mut output_fault,(output,_))=make();
        output_fault.joined.joined.witness[output[0]]=Fr::one();
        let failing=failed(&output_fault);assert_eq!(failing.len(),1);
        omit(&mut output_fault,&failing);assert!(failed(&output_fault).is_empty());
        let (mut suffix_fault,(output,suffix))=make();
        for i in 1..=23{suffix_fault.joined.joined.witness[suffix[i].unwrap()]=Fr::zero();}
        suffix_fault.joined.joined.witness[output[0]]=Fr::one();
        let failing=failed(&suffix_fault);assert_eq!(failing.len(),1);
        omit(&mut suffix_fault,&failing);assert!(failed(&suffix_fault).is_empty());
    }
    #[test]
    fn a4_fallback_and_prediction_width_single_faults(){
        let fixture=input(Epoch::Legacy,[1;8],0x03000001,0);
        let (mut fallback,(selector,selected))=daa_regression::compile_prediction_extended(
            Epoch::Legacy,&daa_count::q(),fixture,true,|builder,_,_,prediction|{
                Ok(choose_fallback(builder,prediction))
            }).unwrap();
        assert!(failed(&fallback).is_empty());
        assert_eq!(fallback.joined.joined.witness[selector],Fr::one());
        fallback.joined.joined.witness[selector]=Fr::zero();
        set_bits(&mut fallback.joined.joined.witness,&selected,&initial());
        let failing=failed(&fallback);assert_eq!(failing.len(),1);
        omit(&mut fallback,&failing);assert!(failed(&fallback).is_empty());
        let (mut width,bits)=daa_regression::compile_prediction_extended(Epoch::Legacy,
            &daa_count::q(),fixture,true,|builder,_,_,prediction|{
                let mut alternate=prediction.clone();
                alternate.prediction_magnitude=builder.bits_big(&BigUint::zero(),
                    daa_regression::PREDICTION_WIDTH);
                let _=choose_fallback(builder,&alternate);
                Ok(alternate.prediction_magnitude)
            }).unwrap();
        width.joined.joined.witness[bits[PREDICTION_BOUND_BITS]]=Fr::one();
        let failing=failed(&width);assert_eq!(failing.len(),1);
        omit(&mut width,&failing);assert!(failed(&width).is_empty());
    }
    #[test]
    fn a4_clamp_boundaries_and_limb_borrow_carry_mutants(){
        let fixture=input(Epoch::Legacy,[1;8],0x03000001,0);
        let cases=[(0u64,false,1u64,4u64,1u64),(1,false,1,4,1),(2,false,1,4,2),
            (4,false,1,4,4),(5,false,1,4,4),(3,true,1,4,1),
            (3,true,0,1,0),(0,false,0,1,0),(1,false,0,1,1),(2,false,0,1,1)];
        let (compiled,outputs)=daa_regression::compile_prediction_extended(Epoch::Legacy,
            &daa_count::q(),fixture,true,|builder,_,_,_|{
                Ok(cases.iter().map(|&(value,negative,low,high,_)|{
                    let v=builder.bits_u64(value,16);let l=builder.bits_u64(low,16);
                    let h=builder.bits_u64(high,16);
                    let sign=if negative{let s=builder.bit(true);builder.assert_one(s);Some(s)}else{None};
                    clamp(builder,&v,sign,&l,&h)
                }).collect::<Vec<_>>())
            }).unwrap();
        assert!(failed(&compiled).is_empty());
        for ((_,_,_,_,expected),output) in cases.iter().zip(&outputs){
            assert_eq!(witness_big(&compiled.joined.joined.witness,output),BigUint::from(*expected));
        }
        let (mut borrow,(start,result))=daa_regression::compile_prediction_extended(
            Epoch::Legacy,&daa_count::q(),fixture,true,|builder,_,_,_|{
                let a=builder.bits_u64(5,16);let b=builder.bits_u64(3,16);
                let start=Progress::from(builder.progress());let result=less(builder,&a,&b);
                Ok((start,result))
            }).unwrap();
        assert!(failed(&borrow).is_empty());
        assert_eq!(borrow.joined.joined.witness[result],Fr::zero());
        borrow.joined.joined.witness[start.live_bits]=Fr::one();
        let difference=(start.live_bits+1..start.live_bits+17).collect::<Vec<_>>();
        set_bits(&mut borrow.joined.joined.witness,&difference,&BigUint::one());
        let failing=failed(&borrow);assert_eq!(failing,vec![start.rows+1]);
        omit(&mut borrow,&failing);assert!(failed(&borrow).is_empty());
        let (mut carry,(start,out))=daa_regression::compile_prediction_extended(
            Epoch::Legacy,&daa_count::q(),fixture,true,|builder,_,_,_|{
                let a=builder.bits_u64(0xffff,32);let b=builder.bits_u64(1,32);
                let start=Progress::from(builder.progress());let out=add_positive(builder,&a,&b,32);
                Ok((start,out))
            }).unwrap();
        assert!(failed(&carry).is_empty());
        assert_eq!(witness_big(&carry.joined.joined.witness,&out),BigUint::from(0x10000u64));
        carry.joined.joined.witness[start.live_bits+32]=Fr::zero();
        carry.joined.joined.witness[out[16]]=Fr::zero();
        let failing=failed(&carry);assert_eq!(failing,vec![start.rows+33]);
        omit(&mut carry,&failing);assert!(failed(&carry).is_empty());
    }
}

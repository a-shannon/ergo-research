//! Fixed Mainnet header height and signed timestamp ordering relation.
//! The consumer must verify this local stage and both adjacency stages under
//! the same committed input; this module does not check PoW or native work.
use ark_bn254::Fr;
use ark_ff::{One, PrimeField, Zero};
use std::ops::Range;
use crate::{gkr::Gate, header_hash, packed::PackedFile, segment_adjacency,
    segment_points, segment_relation, serializer, sparse::{Circuit, Term}};

pub const ORDER_OFFSET: usize = 794624;
pub const ORDER_WIDTH: usize = 1024;
pub const MAINNET_GENESIS: [u8; 32] = [
    0xb0,0x24,0x4d,0xfc,0x26,0x7b,0xac,0xa9,0x74,0xa4,0xca,0xee,0x06,0x12,0x03,0x21,
    0x56,0x27,0x84,0x30,0x3a,0x8a,0x68,0x89,0x76,0xae,0x56,0x17,0x0e,0x4d,0x17,0x5b,
];

pub struct Compiled {
    pub circuit: Circuit,
    pub boolean_rows: Range<usize>,
    pub metadata_zero_rows: Range<usize>,
    pub dedicated_zero_row: usize,
    pub tail_zero_rows: Range<usize>,
    pub height_range_rows: Range<usize>,
    pub increment_row: usize,
    pub timestamp_row: usize,
    pub first_delta_rows: Range<usize>,
}

pub struct Joined {
    pub base: Box<segment_points::Joined>,
    pub order: Box<Compiled>,
    pub released_rows: Range<usize>,
    pub alias_rows: Range<usize>,
    pub genesis_rows: Range<usize>,
}

fn gate(left: usize, right: usize, c0: Fr, c1: Fr, c2: Fr, c3: Fr) -> Gate {
    Gate { left, right, c0, c1, c2, c3 }
}

pub(crate) fn local_order() -> Result<Compiled, String> {
    if Fr::MODULUS_BIT_SIZE <= 65 { return Err("order field modulus is too small".into()); }
    let z=Fr::zero(); let o=Fr::one();
    let mut terms=Vec::with_capacity(2081);
    let mut push=|row,left,right,c0,c1,c2,c3| terms.push(Term {row,gate:gate(left,right,c0,c1,c2,c3)});
    let boolean_rows=0..ORDER_WIDTH;
    for bit in 0..ORDER_WIDTH { push(bit,bit,bit,z,-o,z,o); }
    let metadata_zero_rows=1024..1343;
    for (row,wire) in metadata_zero_rows.clone().zip((97..256).chain(352..512)) {
        push(row,wire,0,z,o,z,z);
    }
    let dedicated_zero_row=1343;
    push(dedicated_zero_row,576,0,z,o,z,z);
    let tail_zero_rows=1344..1791;
    for (row,wire) in tail_zero_rows.clone().zip(577..1024) { push(row,wire,0,z,o,z,z); }
    let height_range_rows=1791..1793;
    push(1791,31,0,z,o,z,z);
    push(1792,287,0,z,o,z,z);
    let increment_row=1793;
    for bit in 0..32 {
        let weight=Fr::from(1u64<<bit);
        push(increment_row,256+bit,bit,if bit==0 {-o} else {z},weight,-weight,z);
    }
    let timestamp_row=1794;
    for part in 0..3 { for bit in 0..64 {
        let weight=if bit==63 && part<2 {-Fr::from(1u64<<63)} else {Fr::from(1u64<<bit)};
        let (wire,weight)=match part {
            0 => (288+bit,weight), 1 => (32+bit,-weight), _ => (512+bit,-weight),
        };
        let constant=if part==0 && bit==0 {-o} else {z};
        let selector_constant=if part==0 && bit==0 {o} else {z};
        push(timestamp_row,wire,96,constant,weight,selector_constant,-weight);
    }}
    let first_delta_rows=1795..1859;
    for (row,bit) in first_delta_rows.clone().zip(0..64) { push(row,512+bit,96,z,z,z,o); }
    if terms.len()!=2081 {return Err("order term schedule changed".into());}
    Ok(Compiled {circuit:Circuit {input_len:ORDER_WIDTH,row_count:2048,terms},
        boolean_rows,metadata_zero_rows,dedicated_zero_row,tail_zero_rows,
        height_range_rows,increment_row,timestamp_row,first_delta_rows})
}

/// Build the same descriptor for public and private paths. A private build
/// remains incomplete until assign_order installs the order bank.
pub fn build(fields: Option<&serializer::Fields>) -> Result<Joined,String> {
    let mut base=Box::new(segment_points::build(fields)?);
    let order=Box::new(local_order()?);
    let z=Fr::zero();let o=Fr::one();
    if base.base.boundary.terms.len()!=420489 || base.alias_rows!=(405784..405850)
        || base.base.remaining_padding_rows.end!=405784 {
        return Err("order adapter old boundary shape changed".into());
    }
    let padding_wire=segment_relation::DIGEST_OFFSET+256;
    let start=base.base.remaining_padding_rows.start+ORDER_OFFSET-padding_wire;
    let released_rows=start..start+ORDER_WIDTH;
    if released_rows!=(151832..152856) || released_rows.end>base.base.remaining_padding_rows.end {
        return Err("order bank outside exact padding".into());
    }
    let first=base.base.boundary.terms.partition_point(|t|t.row<released_rows.start);
    for bit in 0..ORDER_WIDTH {
        let expected=Term {row:start+bit,gate:gate(ORDER_OFFSET+bit,0,z,o,z,z)};
        if base.base.boundary.terms.get(first+bit)!=Some(&expected) {
            return Err("order adapter expected exact zero anchor".into());
        }
    }
    for term in &mut base.base.boundary.terms[first..first+ORDER_WIDTH] {
        term.gate=gate(0,0,z,z,z,z);
    }
    let alias_rows=405850..405862;
    let alias_term_start=base.base.boundary.terms.len();
    for (role,source) in [(&base.base.serializer.layout.fields.height[..],32usize,256usize),
        (&base.base.serializer.layout.fields.timestamp[..],64usize,288usize)].into_iter().enumerate() {
        let (source,bits,bank)=source;
        for byte in 0..bits/8 { for bit in 0..8 {
            let weight=Fr::from(1u64<<bit);
            base.base.boundary.terms.push(Term {row:alias_rows.start+if role==0 {byte} else {4+byte},
                gate:gate(ORDER_OFFSET+bank+8*byte+bit,
                    header_hash::SERIALIZER_OFFSET+source[8*byte+bit],z,weight,-weight,z)});
        }}
    }
    #[cfg(test)]
    crate::c425_span_census::append_source_span(
        "header_order.build.order_alias_terms", alias_term_start, base.base.boundary.terms.len());
    let genesis_rows=405862..405894;
    let genesis_term_start=base.base.boundary.terms.len();
    for byte in 0..32 { for bit in 0..8 {
        let first_bit=bit==0;
        base.base.boundary.terms.push(Term {row:genesis_rows.start+byte,
            gate:gate(segment_relation::DIGEST_OFFSET+8*byte+bit,ORDER_OFFSET+96,
                z,z,if first_bit {-Fr::from(MAINNET_GENESIS[byte] as u64)} else {z},
                Fr::from(1u64<<bit))});
    }}
    #[cfg(test)]
    crate::c425_span_census::append_source_span(
        "header_order.build.genesis_terms", genesis_term_start, base.base.boundary.terms.len());
    if base.base.boundary.terms.len()!=420841 || genesis_rows.end!=405894 {
        return Err("order adapter boundary count changed".into());
    }
    Ok(Joined {base,order,released_rows,alias_rows,genesis_rows})
}

/// The previous metadata is supplied as a witness; the second adjacency stage
/// authenticates it to the preceding committed header.
pub fn witness(current_height:u32,current_time:i64,previous_height:u32,previous_time:i64,
    first:bool)->Result<Vec<bool>,String> {
    let delta=if first {0u64} else {
        let difference=(current_time as i128)-(previous_time as i128)-1;
        if !(0..=u64::MAX as i128).contains(&difference) {
            return Err("nonfirst timestamp has no unsigned strict delta".into());
        }
        difference as u64
    };
    let mut bits=vec![false;ORDER_WIDTH];
    for bit in 0..32 {
        bits[bit]=(previous_height>>bit)&1!=0;
        bits[256+bit]=(current_height>>bit)&1!=0;
    }
    for bit in 0..64 {
        bits[32+bit]=((previous_time as u64)>>bit)&1!=0;
        bits[288+bit]=((current_time as u64)>>bit)&1!=0;
        bits[512+bit]=(delta>>bit)&1!=0;
    }
    bits[96]=first;
    Ok(bits)
}

/// Assign exactly the 1024-bit order bank of an existing private input.
pub fn assign_order(joined:&mut Joined,fields:&serializer::Fields,previous_height:u32,
    previous_time:i64,first:bool)->Result<(),String> {
    let bits=witness(fields.height,fields.timestamp,previous_height,previous_time,first)?;
    let input=joined.base.base.input.as_mut().ok_or("order assignment needs a private input")?;
    if input.len()!=segment_relation::HEADER_WIDTH {return Err("order input width mismatch".into());}
    for (out,bit) in input[ORDER_OFFSET..ORDER_OFFSET+ORDER_WIDTH].iter_mut().zip(bits) {
        *out=Fr::from(bit as u64);
    }
    Ok(())
}

pub fn metadata_relation(n:usize,tip_time:i64)->Result<segment_adjacency::Relation,String> {
    segment_relation::validate_n(n)?;
    let parent_wires=std::array::from_fn(|j|ORDER_OFFSET+j);
    let digest_wires=std::array::from_fn(|j|ORDER_OFFSET+256+j);
    let mut initial=[0u8;32];initial[12]=1;
    let mut terminal=[0u8;32];
    terminal[..4].copy_from_slice(&(n as u32).to_le_bytes());
    terminal[4..12].copy_from_slice(&tip_time.to_le_bytes());
    segment_adjacency::Relation::new(n,parent_wires,digest_wires,initial,terminal)
}

pub fn embed(stage:usize,h:usize,point:&[Fr])->Result<Vec<Fr>,String> {
    if stage<4 {return segment_points::embed(stage,h,point);}
    if stage!=4 || h>2 || point.len()!=10+h {return Err("order stage embedding dimensions invalid".into());}
    let mut out=point[..10].to_vec();
    out.extend([0u64,0,0,1,0,0,0,0,1,1].map(Fr::from));
    out.extend_from_slice(&point[10..]);Ok(out)
}

pub fn load_copy(source:&PackedFile,stage:usize,n:usize,copy:usize)->Result<Vec<Fr>,String> {
    if stage<4 {return segment_points::load_copy(source,stage,n,copy);}
    segment_relation::validate_n(n)?;
    if stage!=4 || copy>=n || source.input_len()!=n*segment_relation::HEADER_WIDTH {
        return Err("order stage packed source/copy dimensions invalid".into());
    }
    source.read_copy(ORDER_WIDTH,copy*1024+776)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ergo_header_core::{Header,PowSolution};
    use crate::transcript::Transcript;
    use std::{fs::OpenOptions,io::Write};

    fn failed(c:&Circuit,input:&[Fr],omit:Option<Range<usize>>)->Vec<usize> {
        assert_eq!(input.len(),c.input_len);
        let mut rows=vec![Fr::zero();c.row_count];
        for term in &c.terms {
            if !omit.as_ref().is_some_and(|range|range.contains(&term.row)) {
                rows[term.row]+=term.gate.evaluate(input);
            }
        }
        rows.into_iter().enumerate().filter_map(|(row,value)|(!value.is_zero()).then_some(row)).collect()
    }
    fn fr_bits(bits:&[bool])->Vec<Fr>{bits.iter().map(|bit|Fr::from(*bit as u64)).collect()}
    fn local(c:&Compiled,height:u32,time:i64,previous_height:u32,previous_time:i64,first:bool)->Vec<Fr>{
        let input=fr_bits(&witness(height,time,previous_height,previous_time,first).unwrap());
        assert!(failed(&c.circuit,&input,None).is_empty());input
    }
    fn put_raw_time(bits:&mut [Fr],start:usize,time:i64) {
        for bit in 0..64 {bits[start+bit]=Fr::from((((time as u64)>>bit)&1) as u64);}
    }
    fn mainnet_headers(n:usize)->Vec<Header> {
        let pack:serde_json::Value=serde_json::from_str(include_str!("../vendor/header-core/fixtures/governance-contiguous-header-packs-v1.json")).unwrap();
        (0..n).map(|i| {
            let text=pack["networks"]["mainnet"]["source_headers_hex"][i].as_str().unwrap();
            let raw:Vec<_>=text.as_bytes().chunks_exact(2).map(|pair|u8::from_str_radix(std::str::from_utf8(pair).unwrap(),16).unwrap()).collect();
            let digest=ergo_header_core::blake2b256(&raw);
            Header::decode(&raw,Some(&digest)).unwrap()
        }).collect()
    }
    fn fields(h:&Header)->serializer::Fields {
        let mut f=serializer::Fields {version:h.version,parent_id:h.parent_id,
            ad_proofs_root:h.ad_proofs_root,transactions_root:h.transactions_root,
            state_root:h.state_root,timestamp:h.timestamp,extension_root:h.extension_root,
            n_bits:h.n_bits,height:h.height,votes:h.votes,pk:[0;33],w:[0;33],
            nonce:[0;8],payload_len:0,payload:[0;255]};
        let payload=match &h.pow {
            PowSolution::V1 {pk,w,nonce,distance} => {
                f.pk=*pk.as_bytes();f.w=*w.as_bytes();f.nonce=*nonce;distance
            }
            PowSolution::V2 {pk,nonce} => {f.pk=*pk.as_bytes();f.nonce=*nonce;&h.unparsed_bytes}
        };
        f.payload_len=payload.len().try_into().unwrap();
        f.payload[..payload.len()].copy_from_slice(payload);f
    }
    fn all_old(j:&Joined) {
        let x=j.base.base.input.as_ref().unwrap();
        for half in x[..header_hash::SERIALIZER_OFFSET].chunks_exact(1<<18) {
            assert!(failed(&j.base.base.core4,half,None).is_empty());
        }
        assert!(failed(&j.base.base.serializer.circuit,
            &x[header_hash::SERIALIZER_OFFSET..header_hash::AUX_OFFSET],None).is_empty());
        assert!(failed(&j.base.points.circuit,
            &x[segment_points::POINT_OFFSET..segment_points::POINT_OFFSET+segment_points::POINT_WIDTH],None).is_empty());
    }
    fn joined(h:&Header,previous_height:u32,previous_time:i64,first:bool)->Joined {
        let f=fields(h);let mut j=build(Some(&f)).unwrap();
        assign_order(&mut j,&f,previous_height,previous_time,first).unwrap();j
    }

    #[test]
    fn exact_schedule_and_signed_integer_falsifiers() {
        let c=local_order().unwrap();
        assert_eq!((c.circuit.input_len,c.circuit.row_count,c.circuit.terms.len()),(1024,2048,2081));
        assert_eq!(c.boolean_rows,0..1024);assert_eq!(c.metadata_zero_rows,1024..1343);
        assert_eq!(c.dedicated_zero_row,1343);assert_eq!(c.tail_zero_rows,1344..1791);
        assert_eq!(c.height_range_rows,1791..1793);assert_eq!(c.increment_row,1793);
        assert_eq!(c.timestamp_row,1794);assert_eq!(c.first_delta_rows,1795..1859);
        for (previous,current) in [(i64::MIN,i64::MIN+1),(-1,0),(i64::MAX-1,i64::MAX),
            (i64::MIN,i64::MAX)] {
            let bits=local(&c,2,current,1,previous,false);
            let delta=bits[512..576].iter().enumerate().fold(0u64,|acc,(i,b)|acc|((*b==Fr::one()) as u64)<<i);
            assert_eq!(delta,(current as i128-previous as i128-1) as u64);
        }
        local(&c,1,i64::MIN,0,0,true);
        local(&c,i32::MAX as u32,10,(i32::MAX-1) as u32,9,false);
        assert!(witness(2,0,1,0,false).is_err());
        assert!(witness(2,-1,1,0,false).is_err());
        assert!(witness(2,i64::MIN,1,i64::MAX,false).is_err());
        let mut bits=fr_bits(&witness(0,1,u32::MAX,0,false).unwrap());
        assert!(failed(&c.circuit,&bits,None).contains(&c.height_range_rows.start));
        assert!(failed(&c.circuit,&bits,None).contains(&c.increment_row));
        bits=fr_bits(&witness(0,1,0,0,false).unwrap());
        assert_eq!(failed(&c.circuit,&bits,None),vec![c.increment_row]);
        bits=fr_bits(&witness(3,1,1,0,false).unwrap());
        assert_eq!(failed(&c.circuit,&bits,None),vec![c.increment_row]);
        bits=fr_bits(&witness(0,1,i32::MAX as u32,0,false).unwrap());
        assert_eq!(failed(&c.circuit,&bits,None),vec![c.increment_row]);
        bits=fr_bits(&witness(1u32<<31,1,(1u32<<31)-1,0,false).unwrap());
        assert_eq!(failed(&c.circuit,&bits,None),vec![c.height_range_rows.start+1]);
        bits=fr_bits(&witness(1,1,0,0,false).unwrap());
        bits[287]=Fr::one();
        assert!(failed(&c.circuit,&bits,None).contains(&(c.height_range_rows.start+1)));
        bits=local(&c,2,0,1,-1,false);bits[351]=Fr::one();
        assert_eq!(failed(&c.circuit,&bits,None),vec![c.timestamp_row]);
        for (previous,current) in [(0,0),(1,0),(i64::MAX,i64::MIN)] {
            bits=local(&c,2,1,1,0,false);
            put_raw_time(&mut bits,32,previous);
            put_raw_time(&mut bits,288,current);
            bits[512..576].fill(Fr::zero());
            assert_eq!(failed(&c.circuit,&bits,None),vec![c.timestamp_row]);
        }
        bits=local(&c,2,5,1,4,false);bits[96]=Fr::from(2u64);
        assert!(failed(&c.circuit,&bits,None).contains(&96));
        bits=local(&c,2,5,1,4,false);bits[512]=Fr::from(2u64);
        assert!(failed(&c.circuit,&bits,None).contains(&512));
        bits=local(&c,2,5,1,4,false);bits[577]=Fr::from(2u64);
        let bad=failed(&c.circuit,&bits,None);
        assert!(bad.contains(&577)&&bad.contains(&c.tail_zero_rows.start));
        bits=local(&c,1,i64::MIN,0,0,true);bits[512]=Fr::one();
        assert!(failed(&c.circuit,&bits,None).contains(&c.first_delta_rows.start));
        let mut invalid=fr_bits(&witness(2,10,1,9,false).unwrap());
        invalid[512..576].fill(Fr::one());
        assert_eq!(failed(&c.circuit,&invalid,None),vec![c.timestamp_row]);
    }

    #[test]
    fn exact_adapter_aliases_genesis_and_assignment_scope() {
        let h=mainnet_headers(1).remove(0);let raw=h.encode().unwrap();
        assert_eq!(ergo_header_core::blake2b256(&raw),MAINNET_GENESIS);
        assert_eq!((h.height,h.parent_id),(1,[0;32]));
        let f=fields(&h);let public=build(None).unwrap();let mut j=build(Some(&f)).unwrap();
        assert_eq!(public.order.circuit,j.order.circuit);
        assert_eq!(public.base.base.boundary,j.base.base.boundary);
        assert!(public.base.base.input.is_none());
        assert_eq!(j.released_rows,151832..152856);
        assert_eq!(j.alias_rows,405850..405862);
        assert_eq!(j.genesis_rows,405862..405894);
        assert_eq!(j.base.base.boundary.terms.len(),420841);
        let before=j.base.base.input.as_ref().unwrap().clone();
        assign_order(&mut j,&f,0,0,true).unwrap();
        let x=j.base.base.input.as_ref().unwrap();
        assert_eq!(&x[..ORDER_OFFSET],&before[..ORDER_OFFSET]);
        assert_eq!(&x[ORDER_OFFSET+ORDER_WIDTH..],&before[ORDER_OFFSET+ORDER_WIDTH..]);
        assert!(failed(&j.order.circuit,&x[ORDER_OFFSET..ORDER_OFFSET+ORDER_WIDTH],None).is_empty());
        all_old(&j);assert!(failed(&j.base.base.boundary,x,None).is_empty());
        assert!(assign_order(&mut build(None).unwrap(),&f,0,0,true).is_err());
        j.base.base.input.as_mut().unwrap().pop();
        assert!(assign_order(&mut j,&f,0,0,true).is_err());
        let mut altered=h.clone();
        match &mut altered.pow {
            PowSolution::V2 {nonce,..}|PowSolution::V1 {nonce,..} => nonce[0]^=1,
        }
        let mutant=joined(&altered,0,0,true);
        all_old(&mutant);
        let y=mutant.base.base.input.as_ref().unwrap();
        assert!(failed(&mutant.order.circuit,&y[ORDER_OFFSET..ORDER_OFFSET+ORDER_WIDTH],None).is_empty());
        let failures=failed(&mutant.base.base.boundary,y,None);
        assert!(!failures.is_empty()&&failures.iter().all(|row|mutant.genesis_rows.contains(row)));
        assert!(failed(&mutant.base.base.boundary,y,Some(mutant.genesis_rows.clone())).is_empty());
        let changed_tip=ergo_header_core::blake2b256(&altered.encode().unwrap());
        assert_ne!(changed_tip,MAINNET_GENESIS);
        let link=segment_adjacency::Relation::new(1,mutant.base.base.parent_wires,
            mutant.base.base.digest_wires,[0;32],changed_tip).unwrap();
        assert!(link.residuals(y).unwrap().iter().all(Zero::is_zero));
    }

    #[test]
    fn isolated_alias_and_metadata_endpoint_falsifiers() {
        let h=mainnet_headers(1).remove(0);let f=fields(&h);
        let j=joined(&h,0,0,true);let mut x=j.base.base.input.as_ref().unwrap().clone();
        let changed_time=h.timestamp^(1i64<<5);
        x[ORDER_OFFSET+288+5]=Fr::one()-x[ORDER_OFFSET+288+5];
        assert!(failed(&j.order.circuit,&x[ORDER_OFFSET..ORDER_OFFSET+ORDER_WIDTH],None).is_empty());
        let metadata=metadata_relation(1,changed_time).unwrap();
        assert!(metadata.residuals(&x).unwrap().iter().all(Zero::is_zero));
        assert_eq!(failed(&j.base.base.boundary,&x,None),vec![j.alias_rows.start+4]);
        assert!(failed(&j.base.base.boundary,&x,Some(j.alias_rows.start+4..j.alias_rows.start+5)).is_empty());
        x=j.base.base.input.as_ref().unwrap().clone();
        x[ORDER_OFFSET+256+8]=Fr::one()-x[ORDER_OFFSET+256+8];
        assert_eq!(failed(&j.base.base.boundary,&x,None),vec![j.alias_rows.start+1]);
        x=j.base.base.input.as_ref().unwrap().clone();
        x[ORDER_OFFSET+288+63]=Fr::one()-x[ORDER_OFFSET+288+63];
        assert_eq!(failed(&j.base.base.boundary,&x,None),vec![j.alias_rows.start+11]);
        let first_off=joined(&h,0,0,false);
        let first_off=first_off.base.base.input.as_ref().unwrap();
        assert!(failed(&j.order.circuit,&first_off[ORDER_OFFSET..ORDER_OFFSET+ORDER_WIDTH],None).is_empty());
        let endpoint=metadata_relation(1,h.timestamp).unwrap().residuals(&first_off).unwrap();
        assert!(!endpoint[96].is_zero());
        assert!(endpoint.iter().enumerate().all(|(row,value)|row==96||value.is_zero()));
        let mut wrong_tip=metadata_relation(1,h.timestamp^1).unwrap().residuals(j.base.base.input.as_ref().unwrap()).unwrap();
        assert!(!wrong_tip[256+32].is_zero());wrong_tip[256+32]=Fr::zero();
        assert!(wrong_tip.iter().all(Zero::is_zero));
        assert!(metadata_relation(3,h.timestamp).is_err());
        let repeated=std::array::from_fn(|_|ORDER_OFFSET);
        assert!(segment_adjacency::Relation::new(1,repeated,repeated,[0;32],[0;32]).is_err());
        assert_eq!(f.height,1);
    }

    #[test]
    fn metadata_shift_exact_single_bit_and_later_selector() {
        let mut hs=mainnet_headers(2);let genesis=hs.remove(0);let mut child=hs.remove(0);
        let genesis_id=ergo_header_core::blake2b256(&genesis.encode().unwrap());
        assert_eq!(genesis_id,MAINNET_GENESIS);
        child.parent_id=genesis_id;child.height=2;child.timestamp=genesis.timestamp;
        let first=joined(&genesis,0,0,true);
        let bit=(0..63).find(|bit|((genesis.timestamp as u64>>bit)&1)!=0).unwrap();
        let previous=genesis.timestamp & !(1i64<<bit);
        let second=joined(&child,1,previous,false);
        all_old(&first);all_old(&second);
        let a=first.base.base.input.as_ref().unwrap();let b=second.base.base.input.as_ref().unwrap();
        assert!(failed(&first.base.base.boundary,a,None).is_empty());
        assert!(failed(&second.base.base.boundary,b,None).is_empty());
        assert!(failed(&second.order.circuit,&b[ORDER_OFFSET..ORDER_OFFSET+ORDER_WIDTH],None).is_empty());
        let mut combined=a.clone();combined.extend_from_slice(b);
        let tip=ergo_header_core::blake2b256(&child.encode().unwrap());
        let old_link=segment_adjacency::Relation::new(2,first.base.base.parent_wires,
            first.base.base.digest_wires,[0;32],tip).unwrap();
        assert!(old_link.residuals(&combined).unwrap().iter().all(Zero::is_zero));
        let m=metadata_relation(2,child.timestamp).unwrap();
        let failed_rows:Vec<_>=m.residuals(&combined).unwrap().iter().enumerate()
            .filter_map(|(row,value)|(!value.is_zero()).then_some(row)).collect();
        assert_eq!(failed_rows,vec![512+32+bit]);
        let mut transcript=Transcript::new(b"order-metadata-fault");
        let counters=(transcript.bytes_absorbed(),transcript.challenges());
        assert!(m.prove(&combined,&mut transcript).unwrap_err().contains("nonzero adjacency residual"));
        assert_eq!((transcript.bytes_absorbed(),transcript.challenges()),counters);
        // Independent expanded byte/bit oracle: endpoints and all other links
        // match even if the single changed previous-time coordinate is omitted.
        let mut expanded=Vec::new();
        for row in 0..256 {
            let initial=if row==96 {Fr::one()} else {Fr::zero()};
            if combined[ORDER_OFFSET+row]!=initial {expanded.push(row);}
            let terminal=if row<32 {Fr::from((((2u32>>(row))&1)!=0) as u64)}
                else if row<96 {Fr::from(((((child.timestamp as u64)>>(row-32))&1)!=0) as u64)}
                else {Fr::zero()};
            if combined[segment_relation::HEADER_WIDTH+ORDER_OFFSET+256+row]!=terminal {
                expanded.push(512+256+row);
            }
            if combined[ORDER_OFFSET+256+row]!=combined[segment_relation::HEADER_WIDTH+ORDER_OFFSET+row] {
                expanded.push(512+row);
            }
        }
        expanded.sort_unstable();assert_eq!(expanded,failed_rows);
        assert!(expanded.iter().all(|row|*row==512+32+bit));
        assert!(m.residuals(&combined).unwrap().iter().enumerate()
            .all(|(row,value)|row==512+32+bit||value.is_zero()));
        let mut later_first=joined(&child,1,genesis.timestamp,true);
        let slot=later_first.base.base.input.as_mut().unwrap();
        let mut both=a.clone();both.extend_from_slice(slot);
        let failures:Vec<_>=m.residuals(&both).unwrap().iter().enumerate()
            .filter_map(|(row,value)|(!value.is_zero()).then_some(row)).collect();
        assert!(failures.contains(&(512+96)));
    }

    #[test]
    fn rebuilt_children_keep_old_families_valid_but_order_fails() {
        let mut hs=mainnet_headers(2);let genesis=hs.remove(0);let template=hs.remove(0);
        let genesis_id=ergo_header_core::blake2b256(&genesis.encode().unwrap());
        let first=joined(&genesis,0,0,true);
        let first_input=first.base.base.input.as_ref().unwrap();
        assert!(failed(&first.base.base.boundary,first_input,None).is_empty());
        for (child_time,child_height,expected_row) in [
            (genesis.timestamp,2usize,1794usize),
            (genesis.timestamp-1,2usize,1794usize),
            (genesis.timestamp+1,3usize,1793usize),
        ] {
            let mut child=template.clone();
            child.parent_id=genesis_id;child.timestamp=child_time;child.height=child_height as u32;
            let raw=child.encode().unwrap();
            let tip=ergo_header_core::blake2b256(&raw);
            assert_eq!(Header::decode(&raw,Some(&tip)).unwrap(),child);
            let f=fields(&child);let mut second=build(Some(&f)).unwrap();
            let provisional_previous=if expected_row==1794 {child_time-1} else {genesis.timestamp};
            assign_order(&mut second,&f,1,provisional_previous,false).unwrap();
            let bank=second.base.base.input.as_mut().unwrap();
            if expected_row==1794 {put_raw_time(&mut bank[ORDER_OFFSET..ORDER_OFFSET+ORDER_WIDTH],32,genesis.timestamp);}
            all_old(&second);
            let child_input=second.base.base.input.as_ref().unwrap();
            assert!(failed(&second.base.base.boundary,child_input,None).is_empty());
            let order_failures=failed(&second.order.circuit,
                &child_input[ORDER_OFFSET..ORDER_OFFSET+ORDER_WIDTH],None);
            assert_eq!(order_failures,vec![expected_row]);
            let mut combined=first_input.clone();combined.extend_from_slice(child_input);
            let old_link=segment_adjacency::Relation::new(2,first.base.base.parent_wires,
                first.base.base.digest_wires,[0;32],tip).unwrap();
            assert!(old_link.residuals(&combined).unwrap().iter().all(Zero::is_zero));
            if child_height==2 {
                assert!(metadata_relation(2,child_time).unwrap().residuals(&combined).unwrap().iter().all(Zero::is_zero));
            }
        }
    }

    #[test]
    fn metadata_map_and_packed_embedding_are_exact() {
        let c=local_order().unwrap();
        for wire in [97,255,352,511] {
            let mut bits=local(&c,1,0,0,0,true);bits[wire]=Fr::one();
            assert!(failed(&c.circuit,&bits,None).iter().any(|row|c.metadata_zero_rows.contains(row)));
        }
        for n in [1,2,4] {
            let h=segment_relation::validate_n(n).unwrap();
            let m=metadata_relation(n,-123).unwrap();
            assert_eq!(m.input_len(),n*segment_relation::HEADER_WIDTH);
            let point:Vec<_>=(0..10+h).map(|i|Fr::from((i+7) as u64)).collect();
            let embedded=embed(4,h,&point).unwrap();
            assert_eq!(&embedded[..10],&point[..10]);
            assert_eq!(&embedded[20..],&point[10..]);
            for bit in 0..10 {assert_eq!(embedded[10+bit],Fr::from(((776>>bit)&1) as u64));}
            let mut global:Vec<_>=(0..n*segment_relation::HEADER_WIDTH)
                .map(|index|Fr::from(((index.wrapping_mul(73)+19)%11<5) as u64)).collect();
            for copy in 0..n {for bit in 0..ORDER_WIDTH {
                global[copy*segment_relation::HEADER_WIDTH+ORDER_OFFSET+bit]=Fr::from(((bit+copy*19)%7==0) as u64);
            }}
            for copy in 0..n {
                global[copy*segment_relation::HEADER_WIDTH+ORDER_OFFSET-1]=Fr::one();
                global[copy*segment_relation::HEADER_WIDTH+ORDER_OFFSET+ORDER_WIDTH]=Fr::one();
            }
            let mut bytes=vec![0u8;global.len()/8];
            for (i,value) in global.iter().enumerate() {if value.is_one(){bytes[i/8]|=1<<(i%8);}}
            let path=std::env::temp_dir().join(format!("order-bank-{}-{}-{}.bits",std::process::id(),n,
                std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
            let mut file=OpenOptions::new().write(true).create_new(true).open(&path).unwrap();
            file.write_all(&bytes).unwrap();drop(file);
            let source=PackedFile::open(&path,20+h).unwrap();
            for copy in 0..n {
                let got=load_copy(&source,4,n,copy).unwrap();
                assert_eq!(got,&global[copy*segment_relation::HEADER_WIDTH+ORDER_OFFSET..
                    copy*segment_relation::HEADER_WIDTH+ORDER_OFFSET+ORDER_WIDTH]);
                let local_point:Vec<_>=(0..10).map(|bit|Fr::from(((17>>bit)&1) as u64)).collect();
                let copy_point:Vec<_>=(0..h).map(|bit|Fr::from(((copy>>bit)&1) as u64)).collect();
                let mut local_coordinates=local_point.clone();local_coordinates.extend_from_slice(&copy_point);
                let global_coordinates=embed(4,h,&local_coordinates).unwrap();
                let global_index=global_coordinates.iter().enumerate().fold(0usize,|index,(bit,value)|{
                    if value.is_one() {index|(1<<bit)} else {index}
                });
                assert_eq!(global_index,copy*segment_relation::HEADER_WIDTH+ORDER_OFFSET+17);
                assert_eq!(global[global_index],got[17]);
                assert_eq!(global[copy*segment_relation::HEADER_WIDTH+ORDER_OFFSET-1],Fr::one());
                let mut fractional=global_coordinates.clone();
                fractional[0]=Fr::from(3u64);fractional[1]=Fr::from(5u64);
                let anchor=global_index & !3;
                let x=Fr::from(3u64);let y=Fr::from(5u64);
                let expected=(Fr::one()-x)*(Fr::one()-y)*global[anchor]
                    +x*(Fr::one()-y)*global[anchor+1]
                    +(Fr::one()-x)*y*global[anchor+2]+x*y*global[anchor+3];
                let local_expected=(Fr::one()-x)*(Fr::one()-y)*got[16]
                    +x*(Fr::one()-y)*got[17]
                    +(Fr::one()-x)*y*got[18]+x*y*got[19];
                assert_eq!(expected,local_expected);
            }
            assert!(load_copy(&source,4,n,n).is_err());
            assert!(load_copy(&source,5,n,0).is_err());
            drop(source);
            std::fs::remove_file(path).unwrap();
        }
        assert!(embed(4,3,&[]).is_err());assert!(embed(5,0,&[]).is_err());
    }
}

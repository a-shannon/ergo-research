//! B1 diagnostic allocation. This does not replace the header profile or certify B2.
use ark_bn254::Fr;
use ark_ff::{BigInteger, One, PrimeField, Zero};
use blake2::{Blake2b, Digest, digest::consts::U32};
use serde::{Deserialize, Serialize};
use crate::{circuit::{self, CompressionLayout}, gkr::Gate, header_hash,
    header_compact_links, sparse::{Circuit, Term}};

pub const WIDTH: usize = 1 << 20;
pub const CORE: usize = 1 << 16;
pub const ENDPOINT_BASE: usize = 983040;
pub const ENDPOINT_WIDTH: usize = 8192;
pub const BASELINE_ID: &str = "work-tree-b1-header-baseline-v1";
pub const CONTRACT_SHA256: &str = "1D8D75A8C1980999036E4903E3BA79F225C6F7E106DF284327DD858DEB7C1633";
pub const CORE_OFFSETS: [usize; 11] = [0,65536,131072,196608,262144,
    327680,393216,458752,720896,851968,917504];
pub const PENDING: &[&str] = &[
    "B2 compact U224 decode, positivity, range and checked interval addition",
    "B2 work continuity, first zero and public total endpoints",
    "B2 L/P/N/profile preimages, BE encodings and serializer length attainability",
    "B2 five-block leaf selection and selected leaf output equality",
    "B2 complete 512-bit chaining, IV, counters, final flags and message tails",
    "B2 Booleanity of newly reserved endpoints and work helpers",
    "B2 full inactive header/tree compression and serializer execution",
    "B2 constraints for position/level/count bytes inside preimages",
    "integrated authentication of every new core/bank terminal opening",
    "complete DAA, historical imports and combined allocation",
];

pub fn hash_bytes(bytes: &[u8]) -> String {
    Blake2b::<U32>::digest(bytes).iter().map(|b|format!("{b:02x}")).collect()
}
pub fn hash_terms(terms: &[Term]) -> String {
    let mut h=Blake2b::<U32>::new();
    for t in terms {
        for n in [t.row,t.gate.left,t.gate.right] {h.update((n as u64).to_le_bytes());}
        for c in [t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3] {h.update(c.into_bigint().to_bytes_le());}
    }
    h.finalize().iter().map(|b|format!("{b:02x}")).collect()
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct Bank {
    pub role: String, pub start: usize, pub end: usize, pub live_bits: usize,
    pub alignment: usize, pub padding_bits: usize, pub last_coordinate: usize,
    pub opening: String,
}
impl Bank {
    fn new(role:&str,start:usize,width:usize,live:usize,alignment:usize)->Self {
        Self {role:role.into(),start,end:start+width,live_bits:live,alignment,
            padding_bits:width-live,last_coordinate:start+width-1,
            opening:if width.is_power_of_two() && start%width==0 {
                format!("LSB local coordinates then fixed bank bits then S-slot coordinates; width {width}")
            }else {"individual fixed-wire embeddings; no single aligned-bank opening claimed".into()}}
    }
}

#[derive(Clone, Debug)]
pub struct Endpoints {
    pub raw: Vec<usize>, pub length: Vec<usize>, pub n_bits: Vec<usize>, pub height: Vec<usize>,
    pub lower: Vec<usize>, pub upper: Vec<usize>, pub work: Vec<usize>,
    pub exponent: Vec<usize>, pub work_minus_one: Vec<usize>,
    pub leaf: Vec<usize>, pub node_left: Vec<usize>, pub node_right: Vec<usize>,
    pub node: Vec<usize>, pub profile: Vec<usize>, pub count: Vec<usize>,
    pub position: Vec<usize>, pub level: Vec<usize>, pub used: usize,
}
impl Endpoints {
    pub fn new()->Self {
        fn take(next:&mut usize,n:usize)->Vec<usize> {let first=*next;*next+=n;(first..*next).collect()}
        let mut n=ENDPOINT_BASE;
        let raw=take(&mut n,4112);let length=take(&mut n,10);
        let n_bits=take(&mut n,32);let height=take(&mut n,32);
        let lower=take(&mut n,224);let upper=take(&mut n,224);let work=take(&mut n,224);
        let exponent=take(&mut n,256);let work_minus_one=take(&mut n,224);
        let leaf=take(&mut n,256);let node_left=take(&mut n,256);let node_right=take(&mut n,256);
        let node=take(&mut n,256);let profile=take(&mut n,256);let count=take(&mut n,32);
        let position=take(&mut n,32);let level=take(&mut n,8);
        Self {raw,length,n_bits,height,lower,upper,work,exponent,work_minus_one,
            leaf,node_left,node_right,node,profile,count,position,level,used:n-ENDPOINT_BASE}
    }
    pub fn header_aliases(&self)->Vec<usize> {
        self.raw.iter().chain(&self.length).chain(&self.n_bits).chain(&self.height).copied().collect()
    }
    pub fn typed_ranges(&self)->Vec<Bank> {
        [("raw",&self.raw),("length",&self.length),("nBits",&self.n_bits),("height",&self.height),
         ("lower_work_pending",&self.lower),("upper_work_pending",&self.upper),("work_pending",&self.work),
         ("exponent_selectors_pending",&self.exponent),("work_minus_one_pending",&self.work_minus_one),
         ("leaf_digest",&self.leaf),("node_left_digest",&self.node_left),("node_right_digest",&self.node_right),
         ("node_digest",&self.node),("profile_digest",&self.profile),("count_pending",&self.count),
         ("position_pending",&self.position),("level_pending",&self.level)]
            .iter().map(|(name,v)|Bank::new(name,v[0],v.len(),v.len(),1)).collect()
    }
}
impl Default for Endpoints {fn default()->Self {Self::new()}}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CoreCounts {
    pub used_bits:usize,pub padded_bits:usize,pub residual_rows:usize,
    pub padded_rows:usize,pub terms:usize,pub maximum_degree:usize,
    pub internal_zero_bits:usize,pub terms_blake2b256:String,
    pub sparse_dimension24:bool,pub sparse_base_terms_2pow20:bool,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RetiredAnchors {
    pub role:String,pub rows:usize,pub terms:usize,pub first_row:usize,pub last_row:usize,
    pub replacement_obligation:String,pub replacement_fully_compiled:bool,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Inventory {
    pub schema:String,pub baseline_id:String,pub contract_sha256:String,
    pub source_sha256_pins_for_archive:Vec<(String,String)>,
    pub core:CoreCounts,pub banks:Vec<Bank>,pub endpoint_fields:Vec<Bank>,
    pub free_ranges:Vec<(usize,usize)>,pub remaining_bits:usize,
    pub retired:Vec<RetiredAnchors>,pub checked_retired_rows:usize,pub checked_retired_terms:usize,
    pub old_boundary_terms:usize,pub unrelated_terms_retained:usize,
    pub old_boundary_blake2b256:String,pub descriptor_blake2b256:String,
    pub partial_arithmetic_reservation_bits:usize,pub pending:Vec<String>,
    pub retained_capacity_bytes:usize,pub inspected_template_peak_capacity_bytes:usize,
}
pub struct Baseline {
    pub inventory:Inventory,pub compression:CompressionLayout,pub endpoints:Endpoints,
    pub header_alias_wires:Vec<usize>,
}

/// Tests share only the small frozen inventory, never the expanded templates.
pub fn shared_baseline()->Result<&'static Baseline,String> {
    static CACHE:std::sync::OnceLock<Result<Baseline,String>>=std::sync::OnceLock::new();
    CACHE.get_or_init(inspect_baseline).as_ref().map_err(Clone::clone)
}

pub fn validate_banks(banks:&[Bank])->Result<(),String> {
    let mut sorted=banks.to_vec();sorted.sort_by_key(|b|b.start);
    for b in &sorted {
        if b.start>=b.end || b.end>WIDTH || b.live_bits>b.end-b.start || b.alignment==0
            || b.start%b.alignment!=0 || b.last_coordinate!=b.end-1
            || b.padding_bits!=b.end-b.start-b.live_bits {return Err(format!("invalid bank {}",b.role));}
    }
    if sorted.windows(2).any(|p|p[0].end>p[1].start) {return Err("bank overlap".into());}
    Ok(())
}

fn anchor(row:usize,wire:usize,value:bool)->Term {
    Term {row,gate:Gate {left:wire,right:0,c0:-Fr::from(value as u64),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()}}
}
fn row_matches(c:&Circuit,row:usize,expected:&[Term])->Result<(),String> {
    let first=c.terms.partition_point(|t|t.row<row);
    let end=c.terms.partition_point(|t|t.row<=row);
    if &c.terms[first..end]!=expected {return Err(format!("baseline anchor mismatch at row {row}"));}
    Ok(())
}

/// Builds actual immutable templates sequentially, then checks every proposed retired gate.
pub fn inspect_baseline()->Result<Baseline,String> {
    let actual=circuit::build_compression(None)?;
    let compression=actual.layout.clone();
    let c=&actual.compiled.circuit;
    let core=CoreCounts {used_bits:compression.used_input_len,padded_bits:c.input_len,
        residual_rows:c.terms.iter().map(|t|t.row+1).max().unwrap_or(0),padded_rows:c.row_count,
        terms:c.terms.len(),maximum_degree:2,internal_zero_bits:c.input_len-compression.used_input_len,
        terms_blake2b256:hash_terms(&c.terms),sparse_dimension24:c.input_len<=1<<24 && c.row_count<=1<<24,
        sparse_base_terms_2pow20:c.terms.len()<=1<<20};
    if core.padded_bits!=CORE {return Err("compression width differs from candidate".into());}
    let core_capacity=c.terms.capacity()*std::mem::size_of::<Term>();
    drop(actual);
    let original=header_hash::build(None,[0;32])?;
    if original.compression_layout!=compression {return Err("compression layout drift".into());}
    let ranges=original.boundary_rows.clone();
    let original_capacity=original.core.terms.capacity()*std::mem::size_of::<Term>()
        +original.boundary.terms.capacity()*std::mem::size_of::<Term>()
        +original.serializer.circuit.terms.capacity()*std::mem::size_of::<Term>();
    drop(original);
    let current=header_compact_links::build(None)?;
    let old=&current.base.base.base;
    let c=&old.boundary;
    if c.input_len!=WIDTH || c.terms.windows(2).any(|p|p[0].row>p[1].row) {
        return Err("compact boundary dimensions/order drift".into());
    }
    let current_capacity=(c.terms.capacity()+old.core4.terms.capacity()+old.serializer.circuit.terms.capacity()
        +current.base.order.circuit.terms.capacity()+current.base.base.points.circuit.terms.capacity())
        *std::mem::size_of::<Term>();
    let mut retired=Vec::new();
    let iv=circuit::blake2b256_initial_state();
    for copy in 5..8 {
        let mut group=|name:&str,first:usize,last:usize,terms:usize,obligation:&str| {
            retired.push(RetiredAnchors {role:format!("core{copy}_{name}"),rows:last-first+1,terms,
                first_row:first,last_row:last,replacement_obligation:obligation.into(),replacement_fully_compiled:false});
        };
        let first=ranges.message_padding.start+(copy*128-514)*8;
        for bit in 0..1024 {
            row_matches(c,first+bit,&[anchor(first+bit,copy*CORE+compression.message[bit/64][bit%64],false)])?;
        }
        group("message",first,first+1023,1024,"B2 leaf message preimage and exact zero tail");
        let first=ranges.dummy_state.start+(copy-5)*512;
        for bit in 0..512 {
            row_matches(c,first+bit,&[anchor(first+bit,copy*CORE+compression.state[bit/64][bit%64],(iv[bit/64]>>(bit%64))&1!=0)])?;
        }
        group("state",first,first+511,512,"B2 leaf IV or full 512-bit prior-block state");
        let row=ranges.counters.start+copy;
        let expected:Vec<_>=compression.counter.iter().enumerate().map(|(bit,wire)|Term {row,gate:Gate {
            left:copy*CORE+wire,right:0,c0:Fr::zero(),c1:Fr::from(1u64<<bit),c2:Fr::zero(),c3:Fr::zero()}}).collect();
        row_matches(c,row,&expected)?;group("counter",row,row,64,"B2 selected cumulative byte counter");
        let row=ranges.flags.start+copy;
        let expected=[Term {row,gate:Gate {left:0,right:0,c0:-Fr::one(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}},
            Term {row,gate:Gate {left:copy*CORE+compression.final_flag,right:0,c0:Fr::zero(),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()}}];
        row_matches(c,row,&expected)?;group("final",row,row,2,"B2 final-block selector and inactive core flag");
    }
    for (name,start,len) in [("leaf_core3",720896,CORE),("leaf_core4",851968,CORE),
        ("node_core",917504,CORE),("typed_endpoints",ENDPOINT_BASE,ENDPOINT_WIDTH)] {
        let first=ranges.global_padding.start+start-(header_hash::AUX_OFFSET+12);
        for bit in 0..len {row_matches(c,first+bit,&[anchor(first+bit,start+bit,false)])?;}
        retired.push(RetiredAnchors {role:name.into(),rows:len,terms:len,first_row:first,last_row:first+len-1,
            replacement_obligation:if name=="typed_endpoints" {"B1 emitted aliases/topology plus pending B2 Booleanity/arithmetic/preimages"}
                else {"actual core template plus pending B2 preimage/chaining/dummy boundary"}.into(),replacement_fully_compiled:false});
    }
    let endpoints=Endpoints::new();
    let header_alias_wires=old.serializer.layout.bytes.iter().flatten().chain(&old.serializer.layout.length)
        .chain(&old.serializer.layout.fields.n_bits).chain(&old.serializer.layout.fields.height)
        .map(|w|header_hash::SERIALIZER_OFFSET+w).collect::<Vec<_>>();
    let mut banks:Vec<_>=CORE_OFFSETS.iter().enumerate().map(|(i,&start)|
        Bank::new(&format!("compression_{i}"),start,CORE,core.used_bits,CORE)).collect();
    banks.extend([Bank::new("serializer",524288,131072,old.serializer.stats.used_input_bits,131072),
        Bank::new("header_aux_and_digest",655360,268,268,1),
        Bank::new("points",786432,8192,8192,8192),Bank::new("order",794624,1024,1024,1024),
        Bank::new("hash_aliases",795648,512,512,512),
        Bank::new("tree_typed_endpoints",ENDPOINT_BASE,ENDPOINT_WIDTH,endpoints.used,ENDPOINT_WIDTH)]);
    validate_banks(&banks)?;
    let free_ranges=vec![(655628,720896),(796160,851968),(ENDPOINT_BASE+ENDPOINT_WIDTH,WIDTH)];
    let checked_retired_rows=retired.iter().map(|x|x.rows).sum();
    let checked_retired_terms=retired.iter().map(|x|x.terms).sum();
    let mut inventory=Inventory {schema:"work-tree-b1-inventory-v1".into(),baseline_id:BASELINE_ID.into(),
        contract_sha256:CONTRACT_SHA256.into(),source_sha256_pins_for_archive:vec![
            ("src/circuit.rs".into(),"AEE8392CC4DCD5E3CC732B2C0DAFDBE66A69A336BCF6698B94B03C710314FEF9".into()),
            ("src/header_compact_links.rs".into(),"83CAFF672EF1989CA65BA01B401FD7986C12FDCEA0D85B4432B4D6006DF495D3".into()),
            ("src/serializer.rs".into(),"CCAC89DD241169E3280546FC60834E94317857A93E2B756D16D76033CA7243E5".into())],
        core,banks,endpoint_fields:endpoints.typed_ranges(),remaining_bits:free_ranges.iter().map(|(a,b)|b-a).sum(),free_ranges,
        retired,checked_retired_rows,checked_retired_terms,old_boundary_terms:c.terms.len(),
        unrelated_terms_retained:c.terms.len()-checked_retired_terms,old_boundary_blake2b256:hash_terms(&c.terms),
        descriptor_blake2b256:String::new(),partial_arithmetic_reservation_bits:1152,
        pending:PENDING.iter().map(|s|s.to_string()).collect(),retained_capacity_bytes:0,
        inspected_template_peak_capacity_bytes:core_capacity.max(original_capacity).max(current_capacity)};
    inventory.retained_capacity_bytes=header_alias_wires.capacity()*std::mem::size_of::<usize>()
        +std::mem::size_of::<CompressionLayout>()+inventory.endpoint_fields.iter().map(|x|x.live_bits).sum::<usize>()*std::mem::size_of::<usize>();
    inventory.descriptor_blake2b256=hash_bytes(&serde_json::to_vec(&inventory).map_err(|e|e.to_string())?);
    Ok(Baseline {inventory,compression,endpoints,header_alias_wires})
}

pub fn embed_bank(start:usize,width:usize,slot_log:usize,point:&[Fr])->Result<Vec<Fr>,String> {
    if !width.is_power_of_two() || start%width!=0 || start+width>WIDTH || slot_log>31
        || point.len()!=width.trailing_zeros() as usize+slot_log {return Err("bank embedding shape".into());}
    let low=width.trailing_zeros() as usize;let mut out=point[..low].to_vec();
    out.extend((low..20).map(|bit|Fr::from(((start>>bit)&1) as u64)));
    out.extend_from_slice(&point[low..]);Ok(out)
}

pub fn leaf_compressions(raw_len:usize)->Result<usize,String> {
    if !(1..=514).contains(&raw_len) {return Err("raw byte envelope".into());}
    Ok((99+raw_len+127)/128)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test] fn work_tree_layout_actual_core_and_anchor_inventory() {
        let b=shared_baseline().unwrap();assert_eq!(b.inventory.core.padded_bits,65536);
        assert_eq!(b.inventory.core.terms,172480);assert_eq!(b.inventory.core.padded_rows,131072);
        assert_eq!(b.inventory.remaining_bits,186612-ENDPOINT_WIDTH);
        assert_eq!(b.inventory.retired.len(),16);assert!(!b.inventory.pending.is_empty());
        assert_eq!(b.header_alias_wires.len(),b.endpoints.header_aliases().len());
    }
    #[test] fn work_tree_layout_alignment_overlap_and_mle() {
        let a=Bank::new("a",720896,CORE,60000,CORE);let mut b=a.clone();b.role="b".into();
        assert!(validate_banks(&[a.clone(),b]).is_err());
        let mut bad=a;bad.start+=1;assert!(validate_banks(&[bad]).is_err());
        let mut banks=CORE_OFFSETS.into_iter().map(|start|(start,CORE)).collect::<Vec<_>>();
        banks.extend([(ENDPOINT_BASE,ENDPOINT_WIDTH),(524288,131072),(786432,8192),(794624,1024),(795648,512)]);
        for (start,width) in banks {
            for slot in [0usize,3,7] {for local in [0,width/2,width-1] {
                let point:Vec<_>=(0..width.trailing_zeros()).map(|b|Fr::from(((local>>b)&1) as u64))
                    .chain((0..3).map(|b|Fr::from(((slot>>b)&1) as u64))).collect();
                let out=embed_bank(start,width,3,&point).unwrap();
                let expected=start+local+slot*WIDTH;
                for (bit,value) in out.iter().enumerate() {assert_eq!(*value,Fr::from(((expected>>bit)&1) as u64));}
            }}
        }
        assert!(embed_bank(1,CORE,3,&vec![Fr::zero();19]).is_err());
    }
    #[test] fn work_tree_layout_byte_envelope_not_preimage_proof() {
        for (n,c) in [(1,1),(29,1),(30,2),(157,2),(158,3),(285,3),(286,4),(413,4),(414,5),(514,5)] {
            assert_eq!(leaf_compressions(n).unwrap(),c);
        }
        assert!(leaf_compressions(0).is_err());assert!(leaf_compressions(515).is_err());
        assert_eq!(b"nipopow-v2/work-profile/v1\0".len()+32,59);
        assert_eq!(1+32+4+4+56+2,99);assert_eq!(1+1+4+64,70);assert_eq!(1+32+4+4,41);
    }
}

//! Positive native compact difficulty and exact U224 intervals on existing B1/B3 wires.
use std::{collections::BTreeMap,ops::Range};
use ark_bn254::Fr;
use ark_ff::{BigInteger,One,PrimeField,Zero};
use num_bigint::BigUint;
use serde::{Serialize,Deserialize};
use serde_json::{json,Value};
use crate::{gkr::Gate,sparse::Term,wiring::{evaluate_shift,RightIndex},
    work_tree_layout::{self as layout,Baseline,WIDTH},work_tree_wiring::{self as topology,Descriptor,Family,Mapping},
    work_tree_fixed_hash::NATIVE_WORK_SHA256};

pub const LOCAL_ROW_WIDTH:usize=2048;
pub const PENDING:&[&str]=&["global GKR/PCS authentication and composition with frozen B1/B2/B3",
    "integrated retirement of old header anchors","full DAA and historical feasibility",
    "serializer attainability of raw byte-envelope fixtures"];
#[derive(Clone,Debug,Serialize,Deserialize,PartialEq,Eq)]
pub struct WorkProfile {
    pub schema:String,pub tree:Descriptor,pub total_be28:[u8;28],pub integer_encoding:String,
    pub native_work_sha256:String,pub canonical_nbits_required:bool,
}
impl WorkProfile {
    pub fn new(headers:usize,root:[u8;32],total_be28:[u8;28])->Result<Self,String> {
        Ok(Self {schema:"work-tree-positive-u224-v1".into(),tree:Descriptor::new(headers,root)?,total_be28,
            integer_encoding:"numeric bits LSB-first; same lower/upper wires serialized BE28 by B3".into(),
            native_work_sha256:NATIVE_WORK_SHA256.into(),canonical_nbits_required:false})
    }
    pub fn validate(&self)->Result<(),String> {
        if *self!=Self::new(self.tree.headers,self.tree.root,self.total_be28)?{return Err("work descriptor mismatch".into());}Ok(())
    }
}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
enum Mask {Genuine,Padding}
#[derive(Clone,Debug)]
struct Tagged {mask:Mask,term:Term}
#[derive(Clone,Debug,Serialize)]
pub struct Group {pub name:String,pub rows:Range<usize>,pub term_count:usize}
pub struct Boundary {profile:WorkProfile,terms:Vec<Tagged>,groups:Vec<Group>,links:[Family;3]}
impl Boundary {
    pub fn profile(&self)->&WorkProfile{&self.profile}
    pub fn links(&self)->&[Family;3]{&self.links}
    pub fn groups(&self)->&[Group]{&self.groups}
    pub fn group(&self,name:&str)->Result<Range<usize>,String>{self.groups.iter().find(|g|g.name==name).map(|g|g.rows.clone()).ok_or_else(||format!("missing work group {name}"))}
    pub fn emit_slot(&self,slot:usize,mut sink:impl FnMut(Term))->Result<(),String> {
        self.profile.validate()?;if slot>=self.profile.tree.slots{return Err("work slot outside S".into());}
        for t in &self.terms {if active(&self.profile,t.mask,slot){let mut term=t.term.clone();term.row+=slot*LOCAL_ROW_WIDTH;
            term.gate.left+=slot*WIDTH;term.gate.right+=slot*WIDTH;sink(term);}}Ok(())
    }
}
fn active(p:&WorkProfile,mask:Mask,slot:usize)->bool{match mask {
    Mask::Genuine=>slot<p.tree.genuine,Mask::Padding=>slot>=p.tree.genuine&&slot<p.tree.leaves,
}}
struct Rows {row:usize,terms:Vec<Tagged>,groups:Vec<Group>,mask:Mask}
impl Rows {
    fn gate(&mut self,left:usize,right:usize,c:[Fr;4]){self.terms.push(Tagged {mask:self.mask,term:Term {row:self.row,
        gate:Gate {left,right,c0:c[0],c1:c[1],c2:c[2],c3:c[3]}}});}
    fn linear(&mut self,w:usize,c:Fr){self.gate(w,0,[Fr::zero(),c,Fr::zero(),Fr::zero()]);}
    fn product(&mut self,a:usize,b:usize,c:Fr){self.gate(a,b,[Fr::zero(),Fr::zero(),Fr::zero(),c]);}
    fn constant(&mut self,c:Fr){self.gate(0,0,[c,Fr::zero(),Fr::zero(),Fr::zero()]);}
    fn boolean(&mut self,w:usize){self.gate(w,w,[Fr::zero(),-Fr::one(),Fr::zero(),Fr::one()]);self.row+=1;}
    fn zero(&mut self,w:usize){self.linear(w,Fr::one());self.row+=1;}
    fn group(&mut self,name:&str,f:impl FnOnce(&mut Self)){let start=self.row;let terms=self.terms.len();f(self);
        self.groups.push(Group {name:name.into(),rows:start..self.row,term_count:self.terms.len()-terms});}
}

/// This checks the actual BN254 scalar modulus, not only its advertised bit width.
pub fn integer_bound()->Result<Value,String> {
    let modulus=BigUint::from_bytes_le(&Fr::MODULUS.to_bytes_le());let bound=BigUint::one()<<225usize;
    if bound>=modulus{return Err("Fr modulus does not contain exact U224 addition interval".into());}
    Ok(json!({"field":"ark_bn254::Fr","modulus_decimal":modulus.to_str_radix(10),"sum_upper_exclusive":"2^225",
        "exact_reason":"Boolean lower/work/upper are below 2^224; lower+work is below 2^225, strictly below the actual modulus. Equality in Fr therefore implies integer equality and rejects U224 overflow. work-minus_one-1 also cannot wrap."}))
}
fn powers()->[Fr;224]{let mut out=[Fr::one();224];for bit in 1..224{out[bit]=out[bit-1]+out[bit-1];}out}
fn numeric_bits(bytes:&[u8;28])->Vec<u8>{(0..224).map(|bit|(bytes[27-bit/8]>>(bit%8))&1).collect()}

pub fn compile(base:&Baseline,p:WorkProfile)->Result<Boundary,String> {
    p.validate()?;integer_bound()?;let e=&base.endpoints;let one=Fr::one();let pow=powers();
    let mut r=Rows {row:0,terms:Vec::new(),groups:Vec::new(),mask:Mask::Genuine};
    for (name,wires) in [("nbits_boolean",&e.n_bits),("lower_boolean",&e.lower),("upper_boolean",&e.upper),
        ("work_boolean",&e.work),("minus_one_boolean",&e.work_minus_one)] {
        r.group(name,|r|{for &w in wires{r.boolean(w);}});
    }
    r.group("exponent_boolean",|r|{for exponent in 1..=30{r.boolean(e.exponent[exponent]);}});
    r.group("forbidden_exponents",|r|{for exponent in 0..256{if !(1..=30).contains(&exponent){r.zero(e.exponent[exponent]);}}});
    r.group("exponent_one_hot",|r|{r.constant(-one);for exponent in 1..=30{r.linear(e.exponent[exponent],one);}r.row+=1;});
    r.group("exponent_alias",|r|{
        for bit in 0..8{r.linear(e.n_bits[24+bit],Fr::from(1u64<<bit));}
        for exponent in 1..=30{r.linear(e.exponent[exponent],-Fr::from(exponent as u64));}r.row+=1;
    });
    r.group("nonnegative_sign",|r|{r.zero(e.n_bits[23]);});
    r.group("decoded_work",|r|{
        for bit in 0..224 {
            r.linear(e.work[bit],one);
            for exponent in 1..=30 {
                let source=if exponent<3 {bit as isize+8*(3-exponent) as isize}else {bit as isize-8*(exponent-3) as isize};
                if (0..23).contains(&source){r.product(e.exponent[exponent],e.n_bits[source as usize],-one);}
            }r.row+=1;
        }
    });
    r.group("overflow_exponent29",|r|{for bit in 16..23{r.product(e.exponent[29],e.n_bits[bit],one);r.row+=1;}});
    r.group("overflow_exponent30",|r|{for bit in 8..23{r.product(e.exponent[30],e.n_bits[bit],one);r.row+=1;}});
    r.group("positive_work",|r|{r.constant(-one);for bit in 0..224{r.linear(e.work[bit],pow[bit]);r.linear(e.work_minus_one[bit],-pow[bit]);}r.row+=1;});
    r.group("checked_interval_addition",|r|{for bit in 0..224{r.linear(e.lower[bit],pow[bit]);r.linear(e.work[bit],pow[bit]);r.linear(e.upper[bit],-pow[bit]);}r.row+=1;});
    if r.row>LOCAL_ROW_WIDTH{return Err("work local row allocation".into());}
    r.mask=Mask::Padding;r.row=0;
    r.group("padding_arithmetic_zero",|r|{for &w in e.lower.iter().chain(&e.upper).chain(&e.work).chain(&e.work_minus_one).chain(&e.exponent){r.zero(w);}});
    let first=Family {name:"work_first_lower_zero".into(),mapping:Mapping::FixedRight {lo:0,hi:1,target:0},
        left_wires:e.lower.clone(),right_wires:vec![0;224],constants:Some(vec![0;224])};
    let continuity=Family {name:"work_interval_continuity".into(),mapping:Mapping::HeaderSuccessor {lo:1,hi:p.tree.genuine},
        left_wires:e.lower.clone(),right_wires:e.upper.clone(),constants:None};
    let total=Family {name:"work_public_total".into(),mapping:Mapping::FixedRight {lo:p.tree.genuine-1,hi:p.tree.genuine,target:0},
        left_wires:e.upper.clone(),right_wires:vec![0;224],constants:Some(numeric_bits(&p.total_be28))};
    Ok(Boundary {profile:p,terms:r.terms,groups:r.groups,links:[first,continuity,total]})
}

/// Fixed local terms plus two constant-state interval automata, O(log H).
pub fn local_coefficients(b:&Boundary,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String> {
    b.profile.validate()?;let h=b.profile.tree.slot_log();if r.len()!=11+h||u.len()!=20+h||v.len()!=20+h{return Err("work wiring dimensions".into());}
    let g=b.profile.tree.genuine as u64;let n=b.profile.tree.leaves as u64;
    let weights=[evaluate_shift(&r[11..],&u[20..],&v[20..],0,0,g,0,RightIndex::SameRow)?,
        evaluate_shift(&r[11..],&u[20..],&v[20..],0,g,n,0,RightIndex::SameRow)?];
    let mut out=[Fr::zero();4];for t in &b.terms {
        let gate=&t.term.gate;let w=weights[if t.mask==Mask::Genuine{0}else{1}]*topology::eq_index(&r[..11],t.term.row)
            *topology::eq_index(&u[..20],gate.left)*topology::eq_index(&v[..20],gate.right);
        for (sum,c) in out.iter_mut().zip([gate.c0,gate.c1,gate.c2,gate.c3]){*sum+=w*c;}
    }Ok(out)
}
pub fn count(b:&Boundary)->Result<Value,String> {
    b.profile.validate()?;let d=&b.profile.tree;let g=d.genuine as u64;let padding=(d.leaves-d.genuine) as u64;
    let genuine_terms=b.terms.iter().filter(|t|t.mask==Mask::Genuine).count() as u64;
    let padding_terms=b.terms.iter().filter(|t|t.mask==Mask::Padding).count() as u64;
    let genuine_rows=b.groups.iter().filter(|g|g.name!="padding_arithmetic_zero").map(|g|g.rows.len() as u64).sum::<u64>();
    let padding_rows=b.group("padding_arithmetic_zero")?.len() as u64;
    let links=b.links.iter().map(|f|f.count(d)).collect::<Result<Vec<_>,_>>()?;
    let link_rows=links.iter().map(|f|f.live_rows).sum::<u64>();let link_terms=links.iter().map(|f|f.terms).sum::<u64>();
    let local_terms=g*genuine_terms+padding*padding_terms;let local_rows=g*genuine_rows+padding*padding_rows;
    Ok(json!({"headers":d.headers,"genuine_leaves":d.genuine,"tree_leaves":d.leaves,"global_slots":d.slots,
        "new_witness_bits":0,"new_core_banks":0,"new_auxiliary_bits":0,"reused_arithmetic_endpoint_bits_per_slot":1152,
        "new_local_rows":local_rows,"new_local_terms":local_terms,"padded_local_rows":LOCAL_ROW_WIDTH as u64*d.slots as u64,
        "new_link_rows":link_rows,"new_link_terms":link_terms,"new_total_rows":local_rows+link_rows,"new_total_terms":local_terms+link_terms,
        "local_literal_templates":{"genuine_rows":genuine_rows,"genuine_terms":genuine_terms,"padding_rows":padding_rows,"padding_terms":padding_terms},
        "links":links,"maximum_degree":2,"global_input_log":20+d.slot_log(),"local_row_log":11+d.slot_log(),
        "local_sparse_dimension_le24":20+d.slot_log()<=24,"local_sparse_base_terms_le2pow20":local_terms<=1<<20,
        "b1_terms_reemitted":0,"b3_terms_reemitted":0,
        "retained_b1_inactive_arithmetic_zero_terms":1152u64*(d.slots-d.leaves) as u64,
        "retained_header_to_nbits_alias_rows":32u64*g,
        "accounting":"All B4 rows are additive. No old anchor is retired and no B1 family is reemitted. Some explicit bit checks are logically implied by upstream B1/B3, but are counted as new B4 terms.",
        "retained_local_term_capacity_bytes":b.terms.capacity()*std::mem::size_of::<Tagged>(),
        "retained_link_wire_capacity_bytes":b.links.iter().map(|f|(f.left_wires.capacity()+f.right_wires.capacity())*std::mem::size_of::<usize>()).sum::<usize>(),
        "analytic_local_multiplication_upper":60*b.terms.len()+128*(d.slot_log()+1),"analytic_local_field_scratch_upper":40,
        "analytic_sequential_local_and_links_field_scratch_upper":40usize.max(32+3*d.slot_log()),
        "coefficient_complexity":"O(log H) for local interval masks and each reused adjacency/anchor family; fixed endpoint/term work",
        "topology_blake2b256":layout::hash_terms(&b.terms.iter().map(|t|t.term.clone()).collect::<Vec<_>>())}))
}

/// Independent integer oracle follows native acceptance, with no bit-selector mapping.
pub fn native_decode(nbits:u32)->Result<BigUint,String> {
    if nbits&0x0080_0000!=0{return Err("native negative difficulty".into());}
    let exponent=nbits>>24;let mantissa=nbits&0x007f_ffff;
    if mantissa==0{return Err("native zero difficulty".into());}
    let work=if exponent<3 {BigUint::from(mantissa>>(8*(3-exponent)))}else {BigUint::from(mantissa)<<(8*(exponent-3)) as usize};
    if work.is_zero(){return Err("native zero after truncation".into());}
    if work.bits()>224{return Err("native difficulty overflow".into());}Ok(work)
}
fn be28(n:&BigUint)->Result<[u8;28],String>{let bytes=n.to_bytes_be();if bytes.len()>28{return Err("U224 range".into());}
    let mut out=[0;28];out[28-bytes.len()..].copy_from_slice(&bytes);Ok(out)}
fn put(values:&mut BTreeMap<usize,Fr>,wires:&[usize],n:&BigUint){for (bit,&wire) in wires.iter().enumerate(){values.insert(wire,Fr::from(n.bit(bit as u64) as u64));}}
fn get(values:&BTreeMap<usize,Fr>,wire:usize)->Fr{values.get(&wire).copied().unwrap_or(Fr::zero())}
fn eval(t:&Term,values:&BTreeMap<usize,Fr>)->Fr{let g=&t.gate;let x=get(values,g.left);let y=get(values,g.right);g.c0+g.c1*x+g.c2*y+g.c3*x*y}
fn local_assignment(base:&Baseline,nbits:u32,lower:&BigUint,work:&BigUint,upper:&BigUint)->BTreeMap<usize,Fr> {
    let e=&base.endpoints;let mut out=BTreeMap::new();put(&mut out,&e.n_bits,&BigUint::from(nbits));
    put(&mut out,&e.lower,lower);put(&mut out,&e.work,work);put(&mut out,&e.upper,upper);
    put(&mut out,&e.work_minus_one,&if work.is_zero(){BigUint::zero()}else {work-BigUint::one()});
    out.insert(e.exponent[(nbits>>24) as usize],Fr::one());out
}
fn local_failures(b:&Boundary,slot:usize,values:&BTreeMap<usize,Fr>,omit:Option<Range<usize>>)->Result<Vec<usize>,String> {
    if slot>=b.profile.tree.slots{return Err("work slot outside S".into());}
    let mut rows=vec![Fr::zero();LOCAL_ROW_WIDTH];for t in &b.terms {if active(&b.profile,t.mask,slot)&&!omit.as_ref().is_some_and(|r|r.contains(&t.term.row)){
        rows[t.term.row]+=eval(&t.term,values);}}
    Ok(rows.iter().enumerate().filter_map(|(r,x)|(!x.is_zero()).then_some(r)).collect())
}
fn direct_local(b:&Boundary,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String> {
    if b.profile.tree.slots>16{return Err("work direct slot cap".into());}let mut out=[Fr::zero();4];
    for slot in 0..b.profile.tree.slots{b.emit_slot(slot,|t|{let g=&t.gate;
        let w=topology::eq_index(r,t.row)*topology::eq_index(u,g.left)*topology::eq_index(v,g.right);
        for (sum,c) in out.iter_mut().zip([g.c0,g.c1,g.c2,g.c3]){*sum+=w*c;}
    })?;}Ok(out)
}

#[derive(Debug,Serialize)]
pub struct TinyEvidence {
    pub headers:usize,pub genuine_records:usize,pub literal_local_rows:usize,pub literal_local_terms:usize,
    pub link_rows_checked:usize,pub b1_nbits_alias_rows_checked:usize,pub coefficient_challenges:usize,
    pub endpoint_coordinates:usize,pub maximum_enumerated_link_capacity_bytes:usize,
    pub raw_header_serializer_or_hash_proof_executed:bool,pub total_be28:[u8;28],
}
pub fn tiny_check(base:&Baseline,headers:usize)->Result<TinyEvidence,String> {
    let shape=Descriptor::new(headers,[0;32])?;if shape.slots>16{return Err("work tiny cap".into());}
    let aliases=[0x01010000u32,0x0101ffff,0x020001ff,0x03000001,0x02001001,0x03010001,0x1c000001,0x1d000001];
    let mut lower=BigUint::zero();let mut all=BTreeMap::new();let mut locals=Vec::new();
    for slot in 0..shape.genuine {
        let nbits=aliases[slot%aliases.len()];let work=native_decode(nbits)?;let upper=&lower+&work;
        be28(&upper)?;let local=local_assignment(base,nbits,&lower,&work,&upper);
        for (&wire,&value) in &local{all.insert(slot*WIDTH+wire,value);}
        // Reuse the actual B1 alias map rather than reconstructing serializer coordinates.
        let destination=base.endpoints.header_aliases();
        for (&source,&target) in base.header_alias_wires.iter().zip(&destination){all.insert((slot+1)*WIDTH+source,get(&local,target));}
        locals.push(local);lower=upper;
    }
    let total=be28(&lower)?;let b=compile(base,WorkProfile::new(headers,[0;32],total)?)?;let mut literal_rows=0;let mut literal_terms=0;
    for slot in 0..shape.slots {
        let empty=BTreeMap::new();let local=locals.get(slot).unwrap_or(&empty);
        if !local_failures(&b,slot,local,None)?.is_empty(){return Err(format!("native work residual H{headers} slot{slot}"));}
        let mut rows=std::collections::BTreeSet::new();b.emit_slot(slot,|t|{literal_terms+=1;rows.insert(t.row);})?;literal_rows+=rows.len();
    }
    let mut link_rows=0;let mut capacity=0;
    for f in &b.links {
        let c=f.enumerate(&shape,1<<20)?;capacity=capacity.max(c.terms.capacity()*std::mem::size_of::<Term>());
        for t in &c.terms {if !eval(t,&all).is_zero(){return Err(format!("work link residual {}",f.name));}}link_rows+=c.terms.len();
    }
    let existing=topology::Topology::new(base,headers,[0;32])?;let alias=existing.families.iter().find(|f|f.name=="header_to_leaf_raw_length_nbits_height").ok_or("B1 header alias missing")?;
    let c=alias.enumerate(&shape,1<<20)?;for t in &c.terms{if !eval(t,&all).is_zero(){return Err("B4 B1 source alias mismatch".into());}}
    let counts=count(&b)?;if counts["new_local_rows"].as_u64()!=Some(literal_rows as u64)||counts["new_local_terms"].as_u64()!=Some(literal_terms as u64){return Err("work literal count mismatch".into());}
    for seed in [3u64,101] {
        let point=|n:usize,offset:u64|(0..n).map(|i|Fr::from(seed+offset+29*(i as u64+1))).collect::<Vec<_>>();
        let h=shape.slot_log();let r=point(11+h,0);let u=point(20+h,11);let v=point(20+h,71);
        if local_coefficients(&b,&r,&u,&v)?!=direct_local(&b,&r,&u,&v)?{return Err("work analytic local differential".into());}
        for f in &b.links {let fc=f.count(&shape)?;let r=point(fc.row_log,7);let mut direct=[Fr::zero();4];let c=f.enumerate(&shape,1<<20)?;
            for t in &c.terms{let g=&t.gate;let w=topology::eq_index(&r,t.row)*topology::eq_index(&u,g.left)*topology::eq_index(&v,g.right);
                for (sum,c) in direct.iter_mut().zip([g.c0,g.c1,g.c2,g.c3]){*sum+=w*c;}}
            if f.coefficients(&shape,&r,&u,&v)?!=direct{return Err(format!("work analytic link differential {}",f.name));}
        }
    }
    Ok(TinyEvidence {headers,genuine_records:shape.genuine,literal_local_rows:literal_rows,literal_local_terms:literal_terms,
        link_rows_checked:link_rows,b1_nbits_alias_rows_checked:32*shape.genuine,coefficient_challenges:2,
        endpoint_coordinates:all.len(),maximum_enumerated_link_capacity_bytes:capacity,
        raw_header_serializer_or_hash_proof_executed:false,total_be28:total})
}

pub fn report()->Result<Value,String> {
    let base=layout::shared_baseline()?;let mut cases=Vec::new();for headers in [3,5,6,9]{
        let evidence=tiny_check(base,headers)?;let b=compile(base,WorkProfile::new(headers,[0;32],evidence.total_be28)?)?;
        cases.push(json!({"descriptor":b.profile,"count":count(&b)?,"evidence":evidence,"groups":b.groups}));
    }
    let historical=compile(base,WorkProfile::new(1827840,[0;32],[0;28])?)?;
    Ok(json!({"profile":"work-tree-positive-u224-b4-v1","contract_sha256":layout::CONTRACT_SHA256,
        "compiled_source_blake2b256":{"work_tree_work.rs":layout::hash_bytes(include_bytes!("work_tree_work.rs")),
            "work_tree_layout.rs":layout::hash_bytes(include_bytes!("work_tree_layout.rs")),"work_tree_wiring.rs":layout::hash_bytes(include_bytes!("work_tree_wiring.rs")),
            "work_tree_leaf_hash.rs":layout::hash_bytes(include_bytes!("work_tree_leaf_hash.rs")),"wiring.rs":layout::hash_bytes(include_bytes!("wiring.rs"))},
        "native_work_sha256":NATIVE_WORK_SHA256,"integer_bound":integer_bound()?,"cases":cases,
        "historical_symbolic_only":count(&historical)?,"historical_total_is_placeholder_not_a_witness":true,
        "pending":PENDING,"decision":"positive U224 and interval join only; no integrated global proof or fit claim",
        "observed_process_peak":"external bounded watchdog; allocation capacities do not claim RSS",
        "historical_witness_generated":false,"global_proof_generated":false}))
}

#[cfg(test)]
mod tests {
    use super::*;
    use blake2::{Blake2b,Digest,digest::consts::U32};
    fn projected(nbits:u32)->BigUint {
        let exponent=nbits>>24;let mantissa=nbits&0x007f_ffff;
        let wide=if exponent<3{BigUint::from(mantissa>>(8*(3-exponent)))}else {BigUint::from(mantissa)<<(8*(exponent-3)) as usize};
        wide&((BigUint::one()<<224usize)-BigUint::one())
    }
    fn isolated(b:&Boundary,slot:usize,values:&BTreeMap<usize,Fr>,name:&str) {
        let omitted=b.group(name).unwrap();let bad=local_failures(b,slot,values,None).unwrap();
        assert!(!bad.is_empty(),"{name}");assert!(bad.iter().all(|r|omitted.contains(r)),"{name}: {bad:?}");
        assert!(local_failures(b,slot,values,Some(omitted)).unwrap().is_empty(),"omission {name}");
    }
    #[test] fn work_tree_work_native_decode_all_exponents_and_noncanonical_aliases() {
        let base=layout::shared_baseline().unwrap();let b=compile(base,WorkProfile::new(3,[0;32],[0;28]).unwrap()).unwrap();
        let mantissas=[0u32,1,0x7f,0xff,0x100,0xffff,0x10000,0x10001,0x7fffff];
        for exponent in 0..=255u32 {for mantissa in mantissas {for sign in [0,0x00800000] {
            let nbits=(exponent<<24)|mantissa|sign;let work=projected(nbits);
            let assigned=local_assignment(base,nbits,&BigUint::zero(),&work,&work);
            let accepted=local_failures(&b,0,&assigned,None).unwrap().is_empty();
            assert_eq!(accepted,native_decode(nbits).is_ok(),"{nbits:08x}");
        }}}
        for alias in [0x01010000,0x0101ffff,0x02000100,0x020001ff,0x03000001] {
            assert_eq!(native_decode(alias).unwrap(),BigUint::one());
            let a=local_assignment(base,alias,&BigUint::zero(),&BigUint::one(),&BigUint::one());
            assert!(local_failures(&b,0,&a,None).unwrap().is_empty());
        }
        for good in [0x1c7fffff,0x1d00ffff,0x1e0000ff]{assert!(native_decode(good).is_ok());}
        for bad in [0x00010000,0x0100ffff,0x020000ff,0x1d010000,0x1e000100,0x1f000001]{assert!(native_decode(bad).is_err());}
    }
    #[test] fn work_tree_work_each_local_frontier_isolated_and_omission() {
        let base=layout::shared_baseline().unwrap();let ep=&base.endpoints;
        let b=compile(base,WorkProfile::new(6,[0;32],[0;28]).unwrap()).unwrap();
        let valid=||local_assignment(base,0x03000001,&BigUint::zero(),&BigUint::one(),&BigUint::one());
        assert!(local_failures(&b,0,&valid(),None).unwrap().is_empty());
        let mut a=local_assignment(base,0x01010000,&BigUint::zero(),&BigUint::one(),&BigUint::one());a.insert(ep.n_bits[0],Fr::from(2u64));isolated(&b,0,&a,"nbits_boolean");
        for (wires,name) in [(&ep.lower,"lower_boolean"),(&ep.upper,"upper_boolean"),(&ep.work_minus_one,"minus_one_boolean")] {
            let mut a=valid();let first=get(&a,wires[0]);let second=get(&a,wires[1]);a.insert(wires[0],first+Fr::from(2u64));a.insert(wires[1],second-Fr::one());
            isolated(&b,0,&a,name);
        }
        // Keep exponent alias, one-hot SUM, every decoded work bit and interval
        // valid: exponent2, mantissa1, selectors (e1,e2,e3)=(1,-1,1), work1.
        let mut a=local_assignment(base,0x02000001,&BigUint::zero(),&BigUint::one(),&BigUint::one());
        a.insert(ep.exponent[1],Fr::one());a.insert(ep.exponent[2],-Fr::one());a.insert(ep.exponent[3],Fr::one());isolated(&b,0,&a,"exponent_boolean");
        let mut a=valid();a.insert(ep.exponent[0],Fr::one());isolated(&b,0,&a,"forbidden_exponents");
        let mut a=local_assignment(base,0x04000001,&BigUint::zero(),&BigUint::one(),&BigUint::one());
        a.insert(ep.exponent[4],Fr::zero());a.insert(ep.exponent[1],Fr::one());a.insert(ep.exponent[3],Fr::one());isolated(&b,0,&a,"exponent_one_hot");
        let mut a=valid();a.insert(ep.n_bits[24],Fr::zero());isolated(&b,0,&a,"exponent_alias");
        let mut a=valid();a.insert(ep.n_bits[23],Fr::one());isolated(&b,0,&a,"nonnegative_sign");
        let a=local_assignment(base,0x03000001,&BigUint::zero(),&BigUint::from(2u64),&BigUint::from(2u64));isolated(&b,0,&a,"decoded_work");
        for (nbits,name) in [(0x1d010001,"overflow_exponent29"),(0x1e000101,"overflow_exponent30")] {
            let work=projected(nbits);let a=local_assignment(base,nbits,&BigUint::zero(),&work,&work);isolated(&b,0,&a,name);
        }
        let a=local_assignment(base,0x01000001,&BigUint::zero(),&BigUint::zero(),&BigUint::zero());isolated(&b,0,&a,"positive_work");
        let mut nonboolean_minus=a;nonboolean_minus.insert(ep.work_minus_one[0],-Fr::one());isolated(&b,0,&nonboolean_minus,"minus_one_boolean");
        let a=local_assignment(base,0x03000001,&BigUint::zero(),&BigUint::one(),&BigUint::from(2u64));isolated(&b,0,&a,"checked_interval_addition");
        let mut padding=BTreeMap::new();padding.insert(ep.work[0],Fr::one());isolated(&b,5,&padding,"padding_arithmetic_zero");
        // Explicit work Booleanity is redundant with Boolean source bits and the
        // one-hot decoder. Its removal must NOT allow this non-Boolean work.
        let mut a=valid();a.insert(ep.work[0],Fr::from(3u64));a.insert(ep.work[1],-Fr::one());
        let bad=local_failures(&b,0,&a,None).unwrap();let boolean=b.group("work_boolean").unwrap();let decode=b.group("decoded_work").unwrap();
        assert!(bad.iter().any(|r|boolean.contains(r)));assert!(bad.iter().any(|r|decode.contains(r)));
        assert!(!local_failures(&b,0,&a,Some(boolean)).unwrap().is_empty());
    }
    #[test] fn work_tree_work_exact_modulus_bound_and_224_bit_overflow() {
        integer_bound().unwrap();let base=layout::shared_baseline().unwrap();let b=compile(base,WorkProfile::new(3,[0;32],[0;28]).unwrap()).unwrap();
        let max=(BigUint::one()<<224usize)-BigUint::one();let overflow=&max+BigUint::one();assert!(be28(&overflow).is_err());
        let a=local_assignment(base,0x03000001,&max,&BigUint::one(),&BigUint::zero());isolated(&b,0,&a,"checked_interval_addition");
        let rows=b.group("checked_interval_addition").unwrap();let residue=b.terms.iter().filter(|t|t.mask==Mask::Genuine&&rows.contains(&t.term.row)).map(|t|eval(&t.term,&a)).sum::<Fr>();
        assert_eq!(residue,Fr::from_le_bytes_mod_order(&overflow.to_bytes_le()));assert!(!residue.is_zero());
        let almost=&max-BigUint::one();let a=local_assignment(base,0x03000001,&almost,&BigUint::one(),&max);
        assert!(local_failures(&b,0,&a,None).unwrap().is_empty());
    }
    fn hash(bytes:&[u8])->[u8;32]{Blake2b::<U32>::digest(bytes).into()}
    // Rebuild a native-format byte-envelope tree from independently computed
    // intervals. This authenticates no real header and executes no hash circuit.
    fn chain(base:&Baseline,nbits:&[u32],offset:u64,gap_before:Option<usize>)->(BTreeMap<usize,Fr>,[u8;28],[u8;32]) {
        let headers=nbits.len()+1;let mut lower=BigUint::from(offset);let mut all=BTreeMap::new();let mut leaves=Vec::new();
        let mut p=b"nipopow-v2/work-profile/v1\0".to_vec();p.extend_from_slice(&crate::header_order::MAINNET_GENESIS);let profile=hash(&p);
        for (slot,&nbits) in nbits.iter().enumerate(){if gap_before==Some(slot){lower+=BigUint::one();}
            let work=native_decode(nbits).unwrap();let upper=&lower+&work;let local=local_assignment(base,nbits,&lower,&work,&upper);
            for (wire,value) in local{all.insert(slot*WIDTH+wire,value);}
            let raw=[0x91,slot as u8,0x37];let mut preimage=vec![b'L'];preimage.extend_from_slice(&profile);
            preimage.extend_from_slice(&(headers as u32).to_be_bytes());preimage.extend_from_slice(&((slot+2) as u32).to_be_bytes());
            preimage.extend_from_slice(&be28(&lower).unwrap());preimage.extend_from_slice(&be28(&upper).unwrap());
            preimage.extend_from_slice(&3u16.to_be_bytes());preimage.extend_from_slice(&raw);leaves.push(hash(&preimage));lower=upper;
        }
        let padded=leaves.len().next_power_of_two();while leaves.len()<padded{let mut preimage=vec![b'P'];preimage.extend_from_slice(&profile);
            preimage.extend_from_slice(&(headers as u32).to_be_bytes());preimage.extend_from_slice(&(leaves.len() as u32).to_be_bytes());leaves.push(hash(&preimage));}
        let mut level=1u8;while leaves.len()>1{let mut next=Vec::new();for (position,pair) in leaves.chunks_exact(2).enumerate(){let mut preimage=vec![b'N',level];
            preimage.extend_from_slice(&(position as u32).to_be_bytes());preimage.extend_from_slice(&pair[0]);preimage.extend_from_slice(&pair[1]);next.push(hash(&preimage));}leaves=next;level+=1;}
        (all,be28(&lower).unwrap(),leaves[0])
    }
    fn link_failures(b:&Boundary,values:&BTreeMap<usize,Fr>)->Vec<usize>{b.links.iter().enumerate().filter_map(|(i,f)|{
        let c=f.enumerate(&b.profile.tree,1<<20).unwrap();c.terms.iter().any(|t|!eval(t,values).is_zero()).then_some(i)
    }).collect()}
    fn locals_pass(base:&Baseline,b:&Boundary,values:&BTreeMap<usize,Fr>){for slot in 0..b.profile.tree.genuine{
        let local=values.range(slot*WIDTH..(slot+1)*WIDTH).map(|(&wire,&value)|(wire-slot*WIDTH,value)).collect();
        assert!(local_failures(b,slot,&local,None).unwrap().is_empty());
    }assert_eq!(base.endpoints.lower.len(),224);}
    #[test] fn work_tree_work_initial_continuity_and_wrong_total_with_rebuilt_tree() {
        let base=layout::shared_baseline().unwrap();let samples=[0x03000001u32;4];
        let (_,correct_total,correct_root)=chain(base,&samples,0,None);
        for (offset,gap,expected) in [(1,None,0),(0,Some(2),1)] {
            let (values,total,root)=chain(base,&samples,offset,gap);assert_ne!(root,correct_root);
            let b=compile(base,WorkProfile::new(5,root,total).unwrap()).unwrap();locals_pass(base,&b,&values);
            assert_eq!(link_failures(&b,&values),vec![expected]);
            // Omitting that unique family accepts the rebuilt, otherwise coherent tree.
            for (i,f) in b.links.iter().enumerate(){if i!=expected{let c=f.enumerate(&b.profile.tree,1<<20).unwrap();assert!(c.terms.iter().all(|t|eval(t,&values).is_zero()));}}
        }
        let changed=[0x03000001u32,0x03000001,0x03000002,0x03000001];
        let (values,actual_total,root)=chain(base,&changed,0,None);assert_ne!(root,correct_root);assert_ne!(actual_total,correct_total);
        let b=compile(base,WorkProfile::new(5,root,correct_total).unwrap()).unwrap();locals_pass(base,&b,&values);
        assert_eq!(link_failures(&b,&values),vec![2]);
        let correct=compile(base,WorkProfile::new(5,root,actual_total).unwrap()).unwrap();assert!(link_failures(&correct,&values).is_empty());
    }
    #[test] fn work_tree_work_existing_nbits_source_and_inactive_b1_guard() {
        let base=layout::shared_baseline().unwrap();let shape=Descriptor::new(3,[0;32]).unwrap();let old=topology::Topology::new(base,3,[0;32]).unwrap();
        let b=compile(base,WorkProfile::new(3,[0;32],[0;28]).unwrap()).unwrap();
        let local=local_assignment(base,0x03000001,&BigUint::zero(),&BigUint::one(),&BigUint::one());let mut all=BTreeMap::new();
        for (&wire,&value) in &local{all.insert(wire,value);}let aliases=base.endpoints.header_aliases();
        for (&source,&destination) in base.header_alias_wires.iter().zip(&aliases){all.insert(WIDTH+source,get(&local,destination));}
        let source=old.families.iter().find(|f|f.name=="header_to_leaf_raw_length_nbits_height").unwrap();let c=source.enumerate(&shape,1<<20).unwrap();
        // Limit this isolated source fixture to the first actual header->leaf pair.
        let terms=c.terms.iter().filter(|t|t.gate.left/WIDTH==1).collect::<Vec<_>>();
        assert!(!terms.is_empty());assert!(terms.iter().all(|t|eval(t,&all).is_zero()));
        let bit=aliases.iter().position(|w|*w==base.endpoints.n_bits[0]).unwrap();let wire=WIDTH+base.header_alias_wires[bit];
        all.insert(wire,Fr::one()-get(&all,wire));assert!(terms.iter().any(|t|!eval(t,&all).is_zero()));
        assert!(local_failures(&b,0,&local,None).unwrap().is_empty());
        let mut inactive=BTreeMap::new();inactive.insert(base.endpoints.work[0],Fr::one());assert!(local_failures(&b,2,&inactive,None).unwrap().is_empty());
        let guard=old.families.iter().find(|f|f.name=="inactive_tree_endpoints").unwrap();let c=guard.enumerate(&shape,1<<20).unwrap();
        let values=BTreeMap::from([(2*WIDTH+base.endpoints.work[0],Fr::one())]);assert!(c.terms.iter().any(|t|!eval(t,&values).is_zero()));
    }
    #[test] fn work_tree_work_tiny_analytic_literal_counts_and_historical_no_enumeration() {
        let base=layout::shared_baseline().unwrap();for headers in [3,5,6,9]{let evidence=tiny_check(base,headers).unwrap();
            assert_eq!(evidence.genuine_records,headers-1);assert_eq!(evidence.b1_nbits_alias_rows_checked,32*(headers-1));
            assert!(!evidence.raw_header_serializer_or_hash_proof_executed);
        }
        for headers in [3,6,9]{let b=compile(base,WorkProfile::new(headers,[0;32],[0;28]).unwrap()).unwrap();let h=b.profile.tree.slot_log();
            for x in [0u64,1]{let r=vec![Fr::from(x);11+h];let u=vec![Fr::from(x);20+h];let v=vec![Fr::from(x);20+h];
                assert_eq!(local_coefficients(&b,&r,&u,&v).unwrap(),direct_local(&b,&r,&u,&v).unwrap());}
        }
        let b=compile(base,WorkProfile::new(1827840,[0;32],[0;28]).unwrap()).unwrap();let h=b.profile.tree.slot_log();
        assert!(local_coefficients(&b,&vec![Fr::from(3u64);11+h],&vec![Fr::from(7u64);20+h],&vec![Fr::from(13u64);20+h]).is_ok());
        assert_eq!(count(&b).unwrap()["new_witness_bits"],0);
        let mut altered=b.profile.clone();altered.canonical_nbits_required=true;assert!(altered.validate().is_err());
    }
}

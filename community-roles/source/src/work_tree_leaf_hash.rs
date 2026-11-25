//! Five-core leaf hash join. Serializer zero-tail is a required upstream relation.
use std::{collections::BTreeMap,ops::Range,sync::OnceLock};
use ark_bn254::Fr;
use ark_ff::{One,PrimeField,Zero};
use blake2::{Blake2b,Digest,digest::consts::U32};
use serde::{Serialize,Deserialize};
use serde_json::{json,Value};
use crate::{circuit::{self,CompressionInput},gkr::Gate,sparse::Term,
    work_tree_layout::{self as layout,WIDTH,CORE},work_tree_wiring::{self as topology,Descriptor},
    work_tree_fixed_hash::{self as fixed,Engine}};

pub const CORES:[usize;5]=[327680,393216,458752,720896,851968];
pub const AUX:usize=655628;
pub const AUX_BITS:usize=26;
pub const ROW_WIDTH:usize=16384;
pub const TRANSITIONS:[usize;10]=[1,29,30,157,158,285,286,413,414,514];
pub const PENDING:&[&str]=&["U224 positivity, decoding, checked addition, continuity and total",
    "serializer attainability of byte-envelope fixtures",
    "global GKR/PCS authentication and integrated header-boundary replacement",
    "complete DAA, historical imports and global feasibility"];

#[derive(Clone,Debug,Serialize,Deserialize,PartialEq,Eq)]
pub struct LeafProfile {
    pub schema:String,pub tree:Descriptor,pub cores:[usize;5],pub aux_start:usize,pub aux_bits:usize,
    pub lower_upper_encoding:String,pub raw_tail_producer:String,pub native_work_sha256:String,
}
impl LeafProfile {
    pub fn new(headers:usize,root:[u8;32])->Result<Self,String> {
        Ok(Self {schema:"work-tree-leaf-five-core-v1".into(),tree:Descriptor::new(headers,root)?,cores:CORES,
            aux_start:AUX,aux_bits:AUX_BITS,lower_upper_encoding:"224 numeric bits LSB-first, serialized BE28".into(),
            raw_tail_producer:"serializer::build less(length,j+1), not, zero_unless(bytes[j],live), then Booleanity; B1 header successor aliases".into(),
            native_work_sha256:fixed::NATIVE_WORK_SHA256.into()})
    }
    pub fn validate(&self)->Result<(),String> {
        if *self!=Self::new(self.tree.headers,self.tree.root)? {return Err("leaf descriptor mismatch".into());}Ok(())
    }
    pub fn role(&self,slot:usize)->Result<Role,String> {
        if slot>=self.tree.slots{return Err("leaf slot outside S".into());}
        Ok(if slot<self.tree.genuine {Role::Genuine}else if slot<self.tree.leaves {Role::Padding}else {Role::Dummy})
    }
}
#[derive(Clone,Copy,Debug,PartialEq,Eq,Serialize)]
pub enum Role {Genuine,Padding,Dummy}
#[derive(Clone,Copy,Debug)]
enum Mask {Genuine,Padding,Dummy,PaddingBit(usize)}
#[derive(Clone,Debug)]
struct Tagged {mask:Mask,term:Term}
#[derive(Clone,Debug,Serialize)]
pub struct Family {pub name:String,pub rows:Range<usize>}
pub struct Boundary {pub profile:LeafProfile,terms:Vec<Tagged>,pub families:Vec<Family>,pub live_local_rows:usize}

struct Rows {terms:Vec<Tagged>,row:usize,mask:Mask,families:Vec<Family>}
impl Rows {
    fn gate(&mut self,left:usize,right:usize,c:[Fr;4]) {
        self.terms.push(Tagged {mask:self.mask,term:Term {row:self.row,
            gate:Gate {left,right,c0:c[0],c1:c[1],c2:c[2],c3:c[3]}}});
    }
    fn linear(&mut self,wire:usize,c:Fr){self.gate(wire,0,[Fr::zero(),c,Fr::zero(),Fr::zero()]);}
    fn constant(&mut self,c:Fr){if !c.is_zero(){self.gate(0,0,[c,Fr::zero(),Fr::zero(),Fr::zero()]);}}
    fn product(&mut self,a:usize,b:usize,c:Fr){self.gate(a,b,[Fr::zero(),Fr::zero(),Fr::zero(),c]);}
    fn anchor(&mut self,w:usize,v:bool){self.gate(w,0,[-Fr::from(v as u64),Fr::one(),Fr::zero(),Fr::zero()]);self.row+=1;}
    fn boolean(&mut self,w:usize){self.gate(w,w,[Fr::zero(),-Fr::one(),Fr::zero(),Fr::one()]);self.row+=1;}
    fn equal(&mut self,a:usize,b:usize){self.gate(a,b,[Fr::zero(),Fr::one(),-Fr::one(),Fr::zero()]);self.row+=1;}
    fn group(&mut self,name:&str,f:impl FnOnce(&mut Self)) {
        let first=self.row;f(self);self.families.push(Family {name:name.into(),rows:first..self.row});
    }
}
fn selector(j:usize)->usize{AUX+j}
fn remainder(k:usize)->usize{AUX+5+k}
fn low_slack(k:usize)->usize{AUX+12+k}
fn high_slack(k:usize)->usize{AUX+19+k}
fn msg(e:&Engine,copy:usize,byte:usize,bit:usize)->usize {CORES[copy]+e.base.compression.message[byte/8][byte%8*8+bit]}
fn output(e:&Engine,copy:usize,bit:usize)->usize {CORES[copy]+e.base.compression.output[bit/64][bit%64]}
fn encoded_bit(wires:&[usize],byte:usize,bit:usize)->usize {wires[(wires.len()/8-1-byte)*8+bit]}

/// Compile three fixed local templates, never a historical slot roster.
pub fn compile(e:&Engine,p:LeafProfile)->Result<Boundary,String> {
    p.validate()?;let mut r=Rows {terms:Vec::new(),row:0,mask:Mask::Genuine,families:Vec::new()};
    let ep=&e.base.endpoints;let l=&e.base.compression;let one=Fr::one();
    for (role,mask) in [(Role::Genuine,Mask::Genuine),(Role::Padding,Mask::Padding),(Role::Dummy,Mask::Dummy)] {
        r.mask=mask;r.row=0;
        let label=match role {Role::Genuine=>"genuine",Role::Padding=>"padding",Role::Dummy=>"dummy"};
        r.group(&format!("{label}_auxiliary"),|r| {
            for w in AUX..AUX+AUX_BITS {if role==Role::Genuine {r.boolean(w);}else {r.anchor(w,false);}}
        });
        if role==Role::Genuine {
            r.group("genuine_length_boolean",|r|{for &w in &ep.length {r.boolean(w);}});
            r.group("genuine_last_one_hot",|r|{r.constant(-one);for j in 0..5 {r.linear(selector(j),one);}r.row+=1;});
            r.group("genuine_length",|r|{
                r.constant(Fr::from(98u64));for (bit,&w) in ep.length.iter().enumerate(){r.linear(w,Fr::from(1u64<<bit));}
                for j in 1..5 {r.linear(selector(j),-Fr::from((128*j) as u64));}
                for bit in 0..7 {r.linear(remainder(bit),-Fr::from(1u64<<bit));}r.row+=1;
            });
            r.group("genuine_lower_length_bound",|r|{
                r.linear(selector(0),-Fr::from(99u64));
                for bit in 0..7 {r.product(selector(0),remainder(bit),Fr::from(1u64<<bit));r.product(selector(0),low_slack(bit),-Fr::from(1u64<<bit));}r.row+=1;
            });
            r.group("genuine_upper_length_bound",|r|{
                r.linear(selector(4),Fr::from(100u64));
                for bit in 0..7 {r.product(selector(4),remainder(bit),-Fr::from(1u64<<bit));r.product(selector(4),high_slack(bit),-Fr::from(1u64<<bit));}r.row+=1;
            });
            r.group("genuine_inactive_slacks",|r|{
                for bit in 0..7 {for (s,w) in [(selector(0),low_slack(bit)),(selector(4),high_slack(bit))] {
                    r.linear(w,one);r.product(s,w,-one);r.row+=1;
                }}
            });
        }
        // A shared fixed local start leaves explicit zero rows in simpler public roles.
        r.row=64;
        for copy in 0..5 {
            r.group(&format!("{label}_state_{copy}"),|r|{
                let iv=circuit::blake2b256_initial_state();
                for bit in 0..512 {
                    let v=Fr::from((iv[bit/64]>>(bit%64))&1);r.linear(CORES[copy]+l.state[bit/64][bit%64],one);r.constant(-v);
                    if role==Role::Genuine && copy>0 {for j in copy..5 {r.linear(selector(j),v);r.product(selector(j),output(e,copy-1,bit),-one);}}
                    r.row+=1;
                }
            });
            r.group(&format!("{label}_message_{copy}"),|r|{
                for byte in 0..128 {for bit in 0..8 {
                    let absolute=copy*128+byte;let wire=msg(e,copy,byte,bit);
                    if role==Role::Dummy {r.anchor(wire,false);continue;}
                    let source=match absolute {
                        1..=32=>Some(ep.profile[(absolute-1)*8+bit]),
                        37..=40 if role==Role::Genuine=>Some(encoded_bit(&ep.height,absolute-37,bit)),
                        41..=68 if role==Role::Genuine=>Some(encoded_bit(&ep.lower,absolute-41,bit)),
                        69..=96 if role==Role::Genuine=>Some(encoded_bit(&ep.upper,absolute-69,bit)),
                        97..=98 if role==Role::Genuine=>{let k=(98-absolute)*8+bit;ep.length.get(k).copied()},
                        99..=612 if role==Role::Genuine=>Some(ep.raw[(absolute-99)*8+bit]),_=>None,
                    };
                    if let Some(source)=source {r.equal(wire,source);continue;}
                    let value=match absolute {
                        0=>((if role==Role::Genuine {b'L'}else {b'P'})>>bit)&1,
                        33..=36=>((p.tree.headers as u32).to_be_bytes()[absolute-33]>>bit)&1,_=>0,
                    };
                    r.linear(wire,one);r.constant(-Fr::from(value as u64));
                    if role==Role::Padding && (37..41).contains(&absolute) {
                        r.mask=Mask::PaddingBit((40-absolute)*8+bit);r.constant(-one);r.mask=mask;
                    }
                    r.row+=1;
                }}
            });
            r.group(&format!("{label}_counter_{copy}"),|r|{
                for (bit,&w) in l.counter.iter().enumerate(){r.linear(CORES[copy]+w,Fr::from(1u64<<bit));}
                if role==Role::Genuine {
                    for j in copy+1..5 {r.linear(selector(j),-Fr::from((128*(copy+1)) as u64));}
                    r.linear(selector(copy),-Fr::from(99u64));
                    for (bit,&w) in ep.length.iter().enumerate(){r.product(selector(copy),w,-Fr::from(1u64<<bit));}
                }else if role==Role::Padding && copy==0 {r.constant(-Fr::from(41u64));}
                r.row+=1;
            });
            r.group(&format!("{label}_final_{copy}"),|r|{
                r.linear(CORES[copy]+l.final_flag,one);r.constant(-one);
                if role==Role::Genuine {for j in copy+1..5 {r.linear(selector(j),one);}}r.row+=1;
            });
        }
        r.group(&format!("{label}_digest"),|r|{
            if role!=Role::Dummy {for bit in 0..256 {
                r.linear(ep.leaf[bit],-one);
                if role==Role::Genuine {for j in 0..5 {r.product(selector(j),output(e,j,bit),one);}}
                else {r.linear(output(e,0,bit),one);}r.row+=1;
            }}
        });
    }
    let live_local_rows=r.families.iter().map(|f|f.rows.end).max().unwrap_or(0);
    if live_local_rows>ROW_WIDTH || r.terms.iter().any(|t|t.term.gate.left>=WIDTH||t.term.gate.right>=WIDTH) {return Err("leaf local shape overflow".into());}
    Ok(Boundary {profile:p,terms:r.terms,families:r.families,live_local_rows})
}
fn selected(p:&LeafProfile,mask:Mask,slot:usize)->bool {
    match mask {Mask::Genuine=>slot<p.tree.genuine,Mask::Padding=>slot>=p.tree.genuine&&slot<p.tree.leaves,
        Mask::Dummy=>slot>=p.tree.leaves&&slot<p.tree.slots,
        Mask::PaddingBit(bit)=>slot>=p.tree.genuine&&slot<p.tree.leaves&&(slot>>bit)&1!=0}
}
impl Boundary {
    pub fn emit_slot(&self,slot:usize,mut sink:impl FnMut(Term))->Result<(),String> {
        self.profile.validate()?;self.profile.role(slot)?;
        for t in &self.terms {if selected(&self.profile,t.mask,slot) {
            let mut term=t.term.clone();term.row+=slot*ROW_WIDTH;term.gate.left+=slot*WIDTH;term.gate.right+=slot*WIDTH;sink(term);
        }}Ok(())
    }
    pub fn family(&self,name:&str)->Result<Range<usize>,String>{self.families.iter().find(|f|f.name==name).map(|f|f.rows.clone()).ok_or_else(||format!("missing boundary family {name}"))}
}

// Sum product(eq(point,slot)) over [0,n), optionally forcing one public slot bit.
fn weighted_prefix(n:usize,z:&[Fr],o:&[Fr],forced:Option<usize>)->Fr {
    let h=z.len();if forced.is_some_and(|b|b>=h){return Fr::zero();}
    let mut free=vec![Fr::one();h+1];
    for b in 0..h {free[b+1]=free[b]*(if forced==Some(b){o[b]}else {z[b]+o[b]});}
    if n==1usize<<h{return free[h];}
    let mut prefix=Fr::one();let mut sum=Fr::zero();
    for b in (0..h).rev() {if (n>>b)&1!=0 {
        if forced!=Some(b){sum+=prefix*z[b]*free[b];}prefix*=o[b];
    }else {prefix*=if forced==Some(b){Fr::zero()}else {z[b]};}}
    sum
}
fn masks(p:&LeafProfile,r:&[Fr],u:&[Fr],v:&[Fr])->[Fr;35] {
    let h=p.tree.slot_log();let mut z=vec![Fr::one();h];let mut o=z.clone();
    for b in 0..h {z[b]=(Fr::one()-r[b])*(Fr::one()-u[b])*(Fr::one()-v[b]);o[b]=r[b]*u[b]*v[b];}
    let mut out=[Fr::zero();35];let g=weighted_prefix(p.tree.genuine,&z,&o,None);let b=weighted_prefix(p.tree.leaves,&z,&o,None);
    out[0]=g;out[1]=b-g;out[2]=weighted_prefix(p.tree.slots,&z,&o,None)-b;
    for bit in 0..32 {out[3+bit]=weighted_prefix(p.tree.leaves,&z,&o,Some(bit))-weighted_prefix(p.tree.genuine,&z,&o,Some(bit));}out
}
fn mask_index(mask:Mask)->usize {match mask {Mask::Genuine=>0,Mask::Padding=>1,Mask::Dummy=>2,Mask::PaddingBit(bit)=>3+bit}}
/// Fixed local work plus O(log^2 H), using dyadic masks; no iteration over global slots.
pub fn coefficients(b:&Boundary,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String> {
    b.profile.validate()?;let h=b.profile.tree.slot_log();
    if r.len()!=14+h||u.len()!=20+h||v.len()!=20+h{return Err("leaf wiring dimension".into());}
    let weights=masks(&b.profile,&r[14..],&u[20..],&v[20..]);let mut out=[Fr::zero();4];
    for t in &b.terms {
        let g=&t.term.gate;let weight=weights[mask_index(t.mask)]*topology::eq_index(&r[..14],t.term.row)
            *topology::eq_index(&u[..20],g.left)*topology::eq_index(&v[..20],g.right);
        for (sum,c) in out.iter_mut().zip([g.c0,g.c1,g.c2,g.c3]){*sum+=weight*c;}
    }Ok(out)
}

fn bit_count_prefix(n:u64,bit:usize)->u64 {
    let period=1u64<<(bit+1);let half=1u64<<bit;(n/period)*half+(n%period).saturating_sub(half)
}
pub fn count(e:&Engine,b:&Boundary)->Result<Value,String> {
    b.profile.validate()?;let d=&b.profile.tree;let g=d.genuine as u64;let n=d.leaves as u64;let s=d.slots as u64;
    let mut counts=[0u64;35];counts[0]=g;counts[1]=n-g;counts[2]=s-n;
    for bit in 0..32 {counts[3+bit]=bit_count_prefix(n,bit)-bit_count_prefix(g,bit);}
    let terms:u64=b.terms.iter().map(|t|counts[mask_index(t.mask)]).sum();
    let rows_for=|role:Role|{let label=match role{Role::Genuine=>"genuine_",Role::Padding=>"padding_",Role::Dummy=>"dummy_"};b.families.iter().filter(|f|f.name.starts_with(label)).map(|f|f.rows.len() as u64).sum::<u64>()};
    let rows=g*rows_for(Role::Genuine)+(n-g)*rows_for(Role::Padding)+(s-n)*rows_for(Role::Dummy);
    Ok(json!({"headers":d.headers,"genuine_leaves":g,"tree_leaves":n,"global_slots":s,
        "new_auxiliary_bits_per_slot":AUX_BITS,"new_auxiliary_bits":AUX_BITS as u64*s,"auxiliary_interval":[AUX,AUX+AUX_BITS],
        "new_boundary_rows":rows,"new_boundary_terms":terms,"padded_boundary_rows":ROW_WIDTH as u64*s,
        "boundary_accounting":"Gross new B3 boundary emission. Old-anchor retirement is inventoried but not applied; this is not a net integrated boundary count.",
        "reused_b1_terms_reemitted":0,"reused_core_banks":CORES,"five_core_copies":5*s,
        "core_terms_per_copy":e.core.terms.len(),"core_rows_per_copy":e.core.row_count,
        "five_core_terms":5*s*e.core.terms.len() as u64,"five_core_rows":5*s*e.core.row_count as u64,
        "maximum_boundary_degree":2,"global_input_log":20+d.slot_log(),"boundary_row_log":14+d.slot_log(),
        "sparse_dimension_le24":20+d.slot_log()<=24,"sparse_base_terms_le2pow20":terms<=1<<20,
        "retained_local_boundary_capacity_bytes":b.terms.capacity()*std::mem::size_of::<Tagged>(),
        "retained_core_capacity_bytes":e.core.terms.capacity()*std::mem::size_of::<Term>(),
        "analytic_field_multiplication_upper":64*b.terms.len()+400*(d.slot_log()+1),
        "analytic_field_scratch_upper":8*(d.slot_log()+1)+64,
        "coefficient_complexity":"fixed local templates plus at most 67 dyadic prefix sums, O(log^2 H) with bounded 32-bit positions",
        "raw_zero_tail":"required serializer relation propagated by unchanged B1 header successor aliases; not established by these raw byte-envelope fixtures"}))
}

/// Check new auxiliary coordinates against the actual unchanged old boundary.
pub fn replacement_inventory(e:&Engine)->Result<Value,String> {
    static AUDIT:OnceLock<Result<Value,String>>=OnceLock::new();
    AUDIT.get_or_init(|| {
        if !e.base.inventory.free_ranges.iter().any(|&(a,z)|a<=AUX&&AUX+AUX_BITS<=z){return Err("leaf auxiliaries outside B1 free ranges".into());}
        let original=crate::header_compact_links::build(None)?;let boundary=&original.base.base.base.boundary;
        let typed=e.base.inventory.retired.iter().find(|r|r.role=="typed_endpoints").ok_or("missing B1 typed anchor inventory")?;
        let first=typed.first_row-(layout::ENDPOINT_BASE-AUX);
        let mut checked=Vec::new();
        for i in 0..AUX_BITS {
            let row=first+i;let a=boundary.terms.partition_point(|t|t.row<row);let z=boundary.terms.partition_point(|t|t.row<=row);
            let expected=Term {row,gate:Gate {left:AUX+i,right:0,c0:Fr::zero(),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()}};
            if boundary.terms[a..z]!=[expected.clone()]{return Err("leaf auxiliary old-zero anchor mismatch".into());}checked.push(expected);
        }
        let serializer=&original.base.base.base.serializer;
        let mut candidates=BTreeMap::<usize,Vec<usize>>::new();
        for (byte,wires) in serializer.layout.bytes.iter().enumerate(){candidates.entry(wires[0]).or_default().push(byte);}
        let mut tail_rows=vec![None;514];let mut i=0;
        while i<serializer.circuit.terms.len() {
            let first=i;let row=serializer.circuit.terms[i].row;while i<serializer.circuit.terms.len()&&serializer.circuit.terms[i].row==row{i+=1;}
            let terms=&serializer.circuit.terms[first..i];if terms.len()!=8{continue;}
            if let Some(bytes)=candidates.get(&terms[0].gate.left){for &byte in bytes {
                let active=terms[0].gate.right;
                if terms.iter().enumerate().all(|(bit,t)|t.gate==Gate {left:serializer.layout.bytes[byte][bit],right:active,
                    c0:Fr::zero(),c1:Fr::from(1u64<<bit),c2:Fr::zero(),c3:-Fr::from(1u64<<bit)}) {tail_rows[byte]=Some(row);}
            }}
        }
        if tail_rows.iter().any(Option::is_none){return Err("serializer output zero-tail row missing".into());}
        let tail_rows=tail_rows.into_iter().map(Option::unwrap).collect::<Vec<_>>();
        Ok(json!({"old_header_profile_unchanged":true,"candidate_replacement_required":true,
            "new_auxiliary_zero_anchors":{"first_row":first,"rows":AUX_BITS,"terms":AUX_BITS,"blake2b256":layout::hash_terms(&checked)},
            "checked_b1_core_anchor_groups":e.base.inventory.retired.iter().filter(|r|r.role.starts_with("core5_")||r.role.starts_with("core6_")||r.role.starts_with("core7_")||r.role=="leaf_core3"||r.role=="leaf_core4").collect::<Vec<_>>(),
            "serializer_zero_tail":{"matched_output_byte_rows":tail_rows.len(),"terms":8*tail_rows.len(),
                "row_numbers":tail_rows,"predicate":"packed_byte*(1-live)=0, live=not(less(length,byte+1)); all serializer coordinates Boolean",
                "producer_source_blake2b256":layout::hash_bytes(include_bytes!("serializer.rs")),
                "source_sha256":"CCAC89DD241169E3280546FC60834E94317857A93E2B756D16D76033CA7243E5",
                "length_comparator_connection":"source-verified in the pinned build loop; gate-shape inventory alone is not a comparator correctness proof"},
            "scope":"B3 supplies replacement leaf message/state/counter/final plus real cores; integrated removal from the old global boundary is still pending"}))
    }).clone()
}

fn hash(bytes:&[u8])->[u8;32]{Blake2b::<U32>::digest(bytes).into()}
fn put_numeric(values:&mut BTreeMap<usize,Fr>,wires:&[usize],n:u64) {
    for (bit,&w) in wires.iter().enumerate(){values.insert(w,Fr::from((n>>bit)&1));}
}
fn put_bytes(values:&mut BTreeMap<usize,Fr>,wires:&[usize],bytes:&[u8],numeric_be:bool) {
    for (j,&byte) in bytes.iter().enumerate(){for bit in 0..8 {
        let i=if numeric_be {(bytes.len()-1-j)*8+bit}else {j*8+bit};
        values.insert(wires[i],Fr::from(((byte>>bit)&1) as u64));
    }}
}
fn get(values:&BTreeMap<usize,Fr>,wire:usize)->Fr{values.get(&wire).copied().unwrap_or(Fr::zero())}
fn evaluate(term:&Term,values:&BTreeMap<usize,Fr>)->Fr {
    let g=&term.gate;let x=get(values,g.left);let y=get(values,g.right);g.c0+g.c1*x+g.c2*y+g.c3*x*y
}
fn verify_core(e:&Engine,input:&[Fr])->Result<(),String> {
    match checked_boolean_view(input) {
        Some(bits)=>verify_core_boolean(e,&bits),
        None=>verify_core_generic(e,input),
    }
}
// The complete original Fr slice, including unused padding, is checked before
// allocating or using a Boolean view. Any nonboolean value keeps the original
// field evaluator's exact verdict; it is never coerced into a bit.
fn checked_boolean_view(input:&[Fr])->Option<Vec<bool>> {
    if input.len()!=CORE || input.iter().any(|value|!value.is_zero()&&!value.is_one()) {return None;}
    Some(input.iter().map(|value|value.is_one()).collect())
}
fn verify_core_boolean(e:&Engine,input:&[bool])->Result<(),String> {
    if input.len()!=CORE{return Err("leaf compression witness width".into());}
    let mut row=None;let mut sum=Fr::zero();
    for t in &e.core.terms {
        if row!=Some(t.row){if row.is_some()&&!sum.is_zero(){return Err(format!("leaf core residual {row:?}"));}row=Some(t.row);sum=Fr::zero();}
        let g=&t.gate;let left=input[g.left];let right=input[g.right];
        let mut value=g.c0;
        if left {value+=g.c1;}
        if right {value+=g.c2;}
        if left&&right {value+=g.c3;}
        sum+=value;
    }if !sum.is_zero(){return Err("leaf core final residual".into());}Ok(())
}
// Retained unchanged as the arbitrary-Fr reference and fallback.
fn verify_core_generic(e:&Engine,input:&[Fr])->Result<(),String> {
    if input.len()!=CORE{return Err("leaf compression witness width".into());}
    let mut row=None;let mut sum=Fr::zero();
    for t in &e.core.terms {
        if row!=Some(t.row){if row.is_some()&&!sum.is_zero(){return Err(format!("leaf core residual {row:?}"));}row=Some(t.row);sum=Fr::zero();}
        sum+=t.gate.evaluate(input);
    }if !sum.is_zero(){return Err("leaf core final residual".into());}Ok(())
}
#[cfg(test)]
#[path="work_tree_boolean_residual_tests.rs"]
mod boolean_residual_tests;
fn compression(e:&Engine,input:&CompressionInput,offset:usize,values:&mut BTreeMap<usize,Fr>)->Result<([u64;8],usize,usize),String> {
    let assigned=circuit::assign_compression(input,&e.base.compression,e.core.input_len)?;
    if assigned.layout!=e.base.compression||assigned.input.len()!=e.core.input_len{return Err("leaf assigned core differs from template".into());}
    verify_core(e,&assigned.input)?;
    let l=&e.base.compression;
    // The global seven-claim roster opens every bit of each replacement core,
    // including private local-operation wires, not only its exposed boundary.
    for (wire,&value) in assigned.input.iter().enumerate(){if !value.is_zero(){values.insert(offset+wire,value);}}
    Ok((assigned.output,assigned.input.capacity()*std::mem::size_of::<Fr>(),0))
}
fn digest(output:[u64;8])->[u8;32]{let mut out=[0;32];for i in 0..4{out[i*8..i*8+8].copy_from_slice(&output[i].to_le_bytes());}out}

#[derive(Clone)]
pub(crate) struct Envelope {pub(crate) raw:Vec<u8>,pub(crate) height:u32,pub(crate) lower:[u8;28],pub(crate) upper:[u8;28],pub(crate) profile:[u8;32]}
impl Envelope {
    fn sample(slot:usize,len:usize,profile:[u8;32])->Self {
        Self {raw:(0..len).map(|i|(i as u8).wrapping_mul(17).wrapping_add((slot as u8).wrapping_mul(43)).wrapping_add(11)).collect(),
            height:(slot+2) as u32,lower:std::array::from_fn(|i|(i as u8).wrapping_mul(13).wrapping_add(slot as u8)),
            upper:std::array::from_fn(|i|(i as u8).wrapping_mul(7).wrapping_add(slot as u8).wrapping_add(1)),profile}
    }
}
// Independent byte-vector oracle; does not read emitted terms, row maps or encoded_bit().
pub(crate) fn preimage(p:&LeafProfile,slot:usize,x:&Envelope)->Result<Vec<u8>,String> {
    match p.role(slot)? {
        Role::Genuine=>{
            let mut bytes=vec![b'L'];bytes.extend_from_slice(&x.profile);bytes.extend_from_slice(&(p.tree.headers as u32).to_be_bytes());
            bytes.extend_from_slice(&x.height.to_be_bytes());bytes.extend_from_slice(&x.lower);bytes.extend_from_slice(&x.upper);
            bytes.extend_from_slice(&(x.raw.len() as u16).to_be_bytes());bytes.extend_from_slice(&x.raw);Ok(bytes)
        },Role::Padding=>{
            let mut bytes=vec![b'P'];bytes.extend_from_slice(&x.profile);bytes.extend_from_slice(&(p.tree.headers as u32).to_be_bytes());
            bytes.extend_from_slice(&(slot as u32).to_be_bytes());Ok(bytes)
        },Role::Dummy=>Ok(Vec::new()),
    }
}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
enum Mutation {None,Tag,Raw,LengthBytes,Profile,H,Height,Lower,Upper,PaddingPosition,Counter,Final,ChainLow,ChainHigh,
    SelectedDigest,LastBlock,NoSelector,DummyReactivated,UpperLength,LowerLength,RawTailSourceOmitted}
struct Assigned {
    values:BTreeMap<usize,Fr>,digest:[u8;32],native:[u8;32],witness_capacity:usize,core_capacity:usize,
}

/// Per-slot B3 witness produced from one decoded Ergo header. This is a
/// bounded local assignment; it does not validate PoW, DAA, or chain history.
pub struct HeaderLeafAssignment {
    pub values:BTreeMap<usize,Fr>,
    pub digest:[u8;32],
}

/// Compute the code-owned native B3 digest without allocating a circuit witness.
/// This is used only while deriving a bounded tree descriptor from native bytes.
pub(crate) fn native_digest(p:&LeafProfile,slot:usize,x:&Envelope)->Result<[u8;32],String>{
    p.validate()?;
    if p.role(slot)?==Role::Genuine {
        let expected=(slot as u32).checked_add(2).ok_or("native leaf height overflow")?;
        if x.height!=expected||x.raw.is_empty()||x.raw.len()>514{return Err("native genuine leaf identity or raw bound".into());}
        let decoded=ergo_header_core::Header::decode(&x.raw,None).map_err(|e|format!("native leaf header decode: {e:?}"))?;
        if decoded.height!=x.height||decoded.encode().map_err(|e|format!("native leaf header encode: {e:?}"))?!=x.raw {
            return Err("native genuine leaf raw is not canonical at its position".into());
        }
    } else if !x.raw.is_empty()||x.height!=0||x.lower!=[0;28]||x.upper!=[0;28] {
        return Err("native inactive leaf carries genuine-only values".into());
    }
    Ok(hash(&preimage(p,slot,x)?))
}

/// Typed native B3 hash path for canonical producer inputs. Unlike the local
/// assignment API, this hashes only the byte preimage and allocates no Fr
/// witness or compression trace.
pub(crate) fn native_leaf_preimage_hash(
    p:&LeafProfile,slot:usize,raw:&[u8],height:u32,lower:[u8;28],upper:[u8;28],profile:[u8;32],
)->Result<[u8;32],String>{
    native_digest(p,slot,&Envelope{raw:raw.to_vec(),height,lower,upper,profile})
}

/// Assign a role selected by the immutable leaf descriptor. Genuine slots must
/// use `assign_header_leaf`; padding and dummy roles cannot be caller-labelled.
pub(crate) fn assign_inactive_leaf(
    e:&Engine,b:&Boundary,slot:usize,profile:[u8;32],
)->Result<HeaderLeafAssignment,String>{
    b.profile.validate()?;
    let role=b.profile.role(slot)?;
    if role==Role::Genuine{return Err("inactive leaf assignment rejects a genuine role".into());}
    let envelope=Envelope{raw:Vec::new(),height:0,lower:[0;28],upper:[0;28],profile};
    let assigned=assign(e,b,slot,&envelope,Mutation::None)?;
    if role==Role::Padding&&assigned.digest!=native_digest(&b.profile,slot,&envelope)?{
        return Err("native padding leaf digest mismatch".into());
    }
    Ok(HeaderLeafAssignment{values:assigned.values,digest:assigned.digest})
}

/// Assign a fixed node/profile/dummy role from its canonical descriptor
/// preimage. Node children are kept as bytes and linked by the fixed consumer.
pub(crate) fn assign_fixed_slot_native(
    e:&Engine,p:&fixed::FixedProfile,slot:usize,bytes:&[u8],
)->Result<HeaderLeafAssignment,String>{
    let role=validate_fixed_preimage(p,slot,bytes)?;
    let mut values=BTreeMap::new();
    if matches!(role,fixed::Role::Node{..}) {
        let mut children=BTreeMap::new();
        put_bytes(&mut children,&e.base.endpoints.node_left,&bytes[6..38],false);
        put_bytes(&mut children,&e.base.endpoints.node_right,&bytes[38..70],false);
        for (wire,value) in children {values.insert(slot*WIDTH+wire,value);}
    }
    let digest=fixed_slot(e,p,slot,bytes,&mut values)?;
    let base=slot.checked_mul(WIDTH).ok_or("fixed assignment owner overflow")?;
    let mut local=BTreeMap::new();
    for (wire,value) in values {
        let local_wire=wire.checked_sub(base).filter(|w|*w<WIDTH).ok_or("fixed assignment wire outside owner")?;
        if local.insert(local_wire,value).is_some(){return Err("fixed assignment duplicate wire".into());}
    }
    Ok(HeaderLeafAssignment{values:local,digest})
}

/// Hash one descriptor-selected fixed preimage directly, without expanding a
/// compression witness. Node/profile/dummy roles and exact preimage bytes are
/// checked before hashing; profile bytes must be the 27-byte prefix + genesis.
pub(crate) fn native_fixed_preimage_hash(
    p:&fixed::FixedProfile,slot:usize,bytes:&[u8],
)->Result<[u8;32],String>{
    validate_fixed_preimage(p,slot,bytes)?;
    Ok(hash(bytes))
}

fn validate_fixed_preimage(
    p:&fixed::FixedProfile,slot:usize,bytes:&[u8],
)->Result<fixed::Role,String>{
    p.validate()?;
    let role=p.role(slot)?;
    match role {
        fixed::Role::Node{level,position}=>{
            if bytes.len()!=p.node_len||bytes[0]!=b'N'||bytes[1]!=level
                ||u32::from_be_bytes(bytes[2..6].try_into().map_err(|_|"fixed node position width")?)!=position {
                return Err("fixed node preimage differs from descriptor role".into());
            }
            let level=usize::from(level);let position=usize::try_from(position).map_err(|_|"fixed node position width")?;
            let (child_base,_) = if level==1{(0,p.tree.leaves)}else{p.tree.level(level-1)?};
            p.tree.validate_node(level,position,slot,child_base+2*position,child_base+2*position+1)?;
        },
        fixed::Role::Profile=>{
            let mut expected=fixed::PROFILE_PREFIX.to_vec();expected.extend_from_slice(&p.genesis);
            if expected.len()!=p.profile_len||bytes!=expected{return Err("fixed profile preimage differs from exact prefix/genesis".into());}
        },
        fixed::Role::Dummy=>if !bytes.is_empty(){return Err("fixed dummy preimage must be empty".into());},
    }
    Ok(role)
}

/// Produce the genuine-leaf witness for one already-decoded post-genesis
/// header. The caller supplies the cumulative-work interval and public work
/// profile; their consensus correctness is outside this producer's contract.
pub fn assign_header_leaf(
    e:&Engine,b:&Boundary,slot:usize,header:&ergo_header_core::Header,
    lower:[u8;28],upper:[u8;28],profile:[u8;32],
)->Result<HeaderLeafAssignment,String>{
    b.profile.validate()?;
    if b.profile.role(slot)?!=Role::Genuine{return Err("header leaf producer requires a genuine slot".into());}
    let expected_height=(slot as u32).checked_add(2).ok_or("header leaf height overflow")?;
    if header.height!=expected_height{return Err("header height does not match leaf position".into());}
    let raw=header.encode().map_err(|error|format!("header encoding failed: {error:?}"))?;
    if raw.is_empty()||raw.len()>514{return Err("canonical header exceeds B3 raw-byte bound".into());}
    let decoded=ergo_header_core::Header::decode(&raw,None)
        .map_err(|error|format!("header re-decode failed: {error:?}"))?;
    let canonical=decoded.encode().map_err(|error|format!("header re-encoding failed: {error:?}"))?;
    if canonical!=raw{return Err("header encoding is not canonical".into());}
    // Also exercise the exact runtime V1/V2 field adapter used by the
    // serializer boundary before constructing the B3 leaf witness.
    crate::serializer::Fields::from_header(&decoded)?;
    let envelope=Envelope {raw,height:header.height,lower,upper,profile};
    let assigned=assign(e,b,slot,&envelope,Mutation::None)?;
    if assigned.digest!=assigned.native{return Err("B3 native leaf digest mismatch".into());}
    Ok(HeaderLeafAssignment {values:assigned.values,digest:assigned.digest})
}

fn assign(e:&Engine,b:&Boundary,slot:usize,x:&Envelope,mutation:Mutation)->Result<Assigned,String> {
    let role=b.profile.role(slot)?;let ep=&e.base.endpoints;let bytes=preimage(&b.profile,slot,x)?;
    if bytes.len()>640{return Err("byte-envelope exceeds five cores".into());}
    let mut values=BTreeMap::new();let mut selectors=[false;5];
    if role==Role::Genuine {
        let len=x.raw.len();let last=(99+len-1)/128;let d=(99+len-1)%128;
        selectors[if mutation==Mutation::LastBlock {last+1}else {last}]=true;
        if mutation==Mutation::NoSelector{selectors=[false;5];}
        put_bytes(&mut values,&ep.raw,&x.raw[..len.min(514)],false);put_numeric(&mut values,&ep.length,len as u64);
        put_numeric(&mut values,&ep.height,x.height as u64);put_bytes(&mut values,&ep.lower,&x.lower,true);put_bytes(&mut values,&ep.upper,&x.upper,true);
        for j in 0..5{values.insert(selector(j),Fr::from(selectors[j] as u64));}
        for bit in 0..7 {
            values.insert(remainder(bit),Fr::from(((d>>bit)&1) as u64));
            let low=if selectors[0]&&d>=99 {d-99}else {0};let high=if selectors[4]&&d<=100 {100-d}else {0};
            values.insert(low_slack(bit),Fr::from(((low>>bit)&1) as u64));values.insert(high_slack(bit),Fr::from(((high>>bit)&1) as u64));
        }
    }
    if role!=Role::Dummy {put_bytes(&mut values,&ep.profile,&x.profile,false);}
    let mut previous=circuit::blake2b256_initial_state();let mut final_digest=[0;32];let mut witness_capacity=0;let mut core_capacity=0;
    for copy in 0..5 {
        let active=if role==Role::Genuine {selectors[copy..].iter().any(|x|*x)}else {role==Role::Padding&&copy==0};
        let later=role==Role::Genuine&&selectors[copy+1..].iter().any(|x|*x);
        let mut block=[0u8;128];let first=copy*128;
        if first<bytes.len(){let end=(first+128).min(bytes.len());block[..end-first].copy_from_slice(&bytes[first..end]);}
        let mut input=CompressionInput {
            state:if role==Role::Genuine&&copy>0&&active {previous}else {circuit::blake2b256_initial_state()},block,
            counter:if later {(128*(copy+1)) as u64}else if active {bytes.len() as u64}else {0},final_flag:!later,
        };
        if copy==0 {match mutation {
            Mutation::Tag=>input.block[0]^=1,Mutation::Raw=>input.block[99]^=1,Mutation::LengthBytes=>input.block[98]^=1,
            Mutation::Profile=>input.block[1]^=1,Mutation::H=>input.block[33]^=1,Mutation::PaddingPosition=>input.block[40]^=1,
            Mutation::Height=>input.block[37]^=1,Mutation::Lower=>input.block[41]^=1,Mutation::Upper=>input.block[69]^=1,
            Mutation::Counter=>input.counter^=1,Mutation::Final=>input.final_flag=!input.final_flag,
            Mutation::RawTailSourceOmitted=>{input.block[100]=1;values.insert(ep.raw[8],Fr::one());},_=>{}
        }}
        if copy==1 {match mutation {Mutation::ChainLow=>input.state[0]^=1,Mutation::ChainHigh=>input.state[6]^=1,_=>{}}}
        if copy==4&&mutation==Mutation::DummyReactivated {input.counter=1;}
        let (state,wc,cc)=compression(e,&input,CORES[copy],&mut values)?;previous=state;
        witness_capacity=witness_capacity.max(wc);core_capacity=core_capacity.max(cc);
        if role==Role::Genuine&&selectors[copy]||role==Role::Padding&&copy==0{final_digest=digest(state);}
    }
    if mutation==Mutation::SelectedDigest {final_digest[0]^=1;}
    if role!=Role::Dummy {put_bytes(&mut values,&ep.leaf,&final_digest,false);}
    Ok(Assigned {values,digest:final_digest,native:hash(&bytes),witness_capacity,core_capacity})
}
fn failures(b:&Boundary,slot:usize,values:&BTreeMap<usize,Fr>,omit:Option<Range<usize>>)->Result<Vec<usize>,String> {
    let mut rows=vec![Fr::zero();ROW_WIDTH];
    // Local templates and assignment use local wires; the public slot selects a role only.
    for t in &b.terms {if selected(&b.profile,t.mask,slot)&&!omit.as_ref().is_some_and(|r|r.contains(&t.term.row)){
        rows[t.term.row]+=evaluate(&t.term,values);
    }}
    Ok(rows.iter().enumerate().filter_map(|(r,x)|(!x.is_zero()).then_some(r)).collect())
}
fn direct_coefficients(b:&Boundary,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String> {
    if b.profile.tree.slots>16{return Err("leaf direct coefficient cap".into());}
    let mut out=[Fr::zero();4];
    for slot in 0..b.profile.tree.slots {b.emit_slot(slot,|t| {
        let g=&t.gate;let w=topology::eq_index(r,t.row)*topology::eq_index(u,g.left)*topology::eq_index(v,g.right);
        for (sum,c) in out.iter_mut().zip([g.c0,g.c1,g.c2,g.c3]){*sum+=w*c;}
    })?;}Ok(out)
}
fn fixed_slot(e:&Engine,p:&fixed::FixedProfile,slot:usize,bytes:&[u8],values:&mut BTreeMap<usize,Fr>)->Result<[u8;32],String> {
    let mut block=[0u8;128];block[..bytes.len()].copy_from_slice(bytes);
    let input=CompressionInput {state:circuit::blake2b256_initial_state(),block,counter:bytes.len() as u64,final_flag:true};
    let (state,_,_)=compression(e,&input,slot*WIDTH+fixed::NODE_CORE,values)?;let out=digest(state);
    if out!=hash(bytes){return Err("fixed native hash mismatch".into());}
    if slot<p.tree.leaves {let mut endpoint=BTreeMap::new();put_bytes(&mut endpoint,&e.base.endpoints.node,&out,false);
        for (wire,value) in endpoint {values.insert(slot*WIDTH+wire,value);}}
    let mut rows=vec![Fr::zero();fixed::ROW_WIDTH];
    fixed::emit_slot(e,p,slot,|t|{rows[t.row-slot*fixed::ROW_WIDTH]+=evaluate(&t,values);})?;
    if rows.iter().any(|x|!x.is_zero()){return Err(format!("leaf-to-fixed boundary residual slot{slot}"));}Ok(out)
}

#[derive(Debug,Serialize)]
pub struct TinyEvidence {
    pub headers:usize,pub slots:usize,pub genuine_lengths:Vec<usize>,pub leaf_core_witnesses:usize,
    pub fixed_core_witnesses:usize,pub native_leaf_matches:usize,pub b1_family_rows:usize,
    pub literal_boundary_terms:usize,pub literal_boundary_rows:usize,pub coefficient_challenges:usize,
    pub maximum_single_core_witness_capacity_bytes:usize,pub maximum_single_core_terms_capacity_bytes:usize,
    pub endpoint_coordinates:usize,pub raw_fixture_serializer_attainability:bool,pub root:[u8;32],
}
pub fn tiny_check(e:&Engine,headers:usize)->Result<TinyEvidence,String> {
    let p=LeafProfile::new(headers,[0;32])?;if p.tree.slots>16{return Err("leaf tiny cap".into());}
    let b=compile(e,p.clone())?;let mut all=BTreeMap::new();let mut native_profile=b"nipopow-v2/work-profile/v1\0".to_vec();
    native_profile.extend_from_slice(&crate::header_order::MAINNET_GENESIS);
    let fixed_profile=fixed::FixedProfile::new(headers,[0;32])?;
    let profile=fixed_slot(e,&fixed_profile,p.tree.profile_node_slot,&native_profile,&mut all)?;
    let mut leaves=Vec::new();let mut lengths=Vec::new();let mut wc=0;let mut cc=0;let mut literal_terms=0;let mut literal_rows=0;
    for slot in 0..p.tree.slots {
        let len=TRANSITIONS[(slot+headers)%TRANSITIONS.len()];let x=Envelope::sample(slot,len,profile);
        let assigned=assign(e,&b,slot,&x,Mutation::None)?;
        if !failures(&b,slot,&assigned.values,None)?.is_empty(){return Err(format!("leaf boundary residual H{headers} slot{slot}"));}
        if slot<p.tree.leaves {
            if assigned.digest!=assigned.native{return Err("leaf native hash differential".into());}leaves.push(assigned.digest);
        }
        if slot<p.tree.genuine {lengths.push(len);}
        wc=wc.max(assigned.witness_capacity);cc=cc.max(assigned.core_capacity);
        // Only endpoint/header aliases survive the sequential core check.
        for (&wire,&value) in &assigned.values {if (layout::ENDPOINT_BASE..layout::ENDPOINT_BASE+layout::ENDPOINT_WIDTH).contains(&wire){all.insert(slot*WIDTH+wire,value);}}
        if slot<p.tree.genuine {for (&source,destination) in e.base.header_alias_wires.iter().zip(e.base.endpoints.header_aliases()){
            all.insert((slot+1)*WIDTH+source,get(&assigned.values,destination));
        }}
        let mut rows=std::collections::BTreeSet::new();b.emit_slot(slot,|t|{literal_terms+=1;rows.insert(t.row);})?;literal_rows+=rows.len();
    }
    let mut node_slot=0;let mut level=1;let mut layer=leaves;
    while layer.len()>1 {
        let mut next=Vec::new();
        for (position,pair) in layer.chunks_exact(2).enumerate(){
            let mut bytes=vec![b'N',level as u8];bytes.extend_from_slice(&(position as u32).to_be_bytes());bytes.extend_from_slice(&pair[0]);bytes.extend_from_slice(&pair[1]);
            let mut children=BTreeMap::new();put_bytes(&mut children,&e.base.endpoints.node_left,&pair[0],false);put_bytes(&mut children,&e.base.endpoints.node_right,&pair[1],false);
            for (wire,value) in children {all.insert(node_slot*WIDTH+wire,value);}
            next.push(fixed_slot(e,&fixed_profile,node_slot,&bytes,&mut all)?);node_slot+=1;
        }layer=next;level+=1;
    }
    let root=layer[0];for slot in p.tree.leaves..p.tree.slots{fixed_slot(e,&fixed_profile,slot,&[],&mut all)?;}
    let topology=topology::Topology::new(e.base,headers,root)?;let mut b1_rows=0;
    for family in &topology.families {
        let c=family.enumerate(&topology.descriptor,1<<20)?;
        for t in &c.terms {if !evaluate(t,&all).is_zero(){return Err(format!("leaf B1 join {} row{}",family.name,t.row));}}
        b1_rows+=c.terms.len();
    }
    let counts=count(e,&b)?;
    if counts["new_boundary_terms"].as_u64()!=Some(literal_terms as u64)||counts["new_boundary_rows"].as_u64()!=Some(literal_rows as u64){return Err("leaf literal count mismatch".into());}
    for seed in [7u64,103] {
        let point=|n:usize,offset:u64|(0..n).map(|i|Fr::from(seed+offset+37*(i as u64+1))).collect::<Vec<_>>();
        let r=point(14+p.tree.slot_log(),0);let u=point(20+p.tree.slot_log(),11);let v=point(20+p.tree.slot_log(),73);
        if coefficients(&b,&r,&u,&v)?!=direct_coefficients(&b,&r,&u,&v)?{return Err("leaf dyadic wiring differential".into());}
    }
    Ok(TinyEvidence {headers,slots:p.tree.slots,genuine_lengths:lengths,leaf_core_witnesses:5*p.tree.slots,
        fixed_core_witnesses:p.tree.slots,native_leaf_matches:p.tree.leaves,b1_family_rows:b1_rows,
        literal_boundary_terms:literal_terms,literal_boundary_rows:literal_rows,coefficient_challenges:2,
        maximum_single_core_witness_capacity_bytes:wc,maximum_single_core_terms_capacity_bytes:cc,
        endpoint_coordinates:all.len(),raw_fixture_serializer_attainability:false,root})
}

pub fn report()->Result<Value,String> {
    let e=fixed::engine()?;let replacement=replacement_inventory(e)?;let mut cases=Vec::new();
    for headers in [3,5,6,9] {let b=compile(e,LeafProfile::new(headers,[0;32])?)?;
        cases.push(json!({"descriptor":b.profile,"counts":count(e,&b)?,"evidence":tiny_check(e,headers)?}));}
    let historical=compile(e,LeafProfile::new(1827840,[0;32])?)?;
    Ok(json!({"profile":"work-tree-leaf-five-core-b3-v1","contract_sha256":layout::CONTRACT_SHA256,
        "compiled_source_blake2b256":{
            "work_tree_leaf_hash.rs":layout::hash_bytes(include_bytes!("work_tree_leaf_hash.rs")),
            "work_tree_fixed_hash.rs":layout::hash_bytes(include_bytes!("work_tree_fixed_hash.rs")),
            "work_tree_layout.rs":layout::hash_bytes(include_bytes!("work_tree_layout.rs")),
            "work_tree_wiring.rs":layout::hash_bytes(include_bytes!("work_tree_wiring.rs")),
            "circuit.rs":layout::hash_bytes(include_bytes!("circuit.rs")),
            "serializer.rs":layout::hash_bytes(include_bytes!("serializer.rs")),
            "header_hash.rs":layout::hash_bytes(include_bytes!("header_hash.rs"))},
        "native_work_sha256":fixed::NATIVE_WORK_SHA256,"replacement_inventory":replacement,"cases":cases,
        "historical_symbolic_only":count(e,&historical)?,"pending":PENDING,
        "boundary_inputs":"B1 raw/length/height from header i+1 and B2 computed profile via B1 fanout; H and padding position are public descriptor/index values; lower/upper are numeric LSB bit aliases encoded BE28, with work semantics pending",
        "zero_tail_dependency":"The standalone B3 boundary assumes the actual serializer zero-tail relation. A deliberate producer-omission fixture shows B3 alone accepts a nonzero raw tail; restoring that exact upstream predicate rejects it.",
        "state_scope":"full512-bit IV/chaining and all five valid compression witnesses; selected first256 digest only, upper256 outputs remain real core outputs",
        "observed_process_peak":"external bounded watchdog; reported capacities are retained/scratch allocations, not RSS",
        "decision":"bounded leaf hash join only; no integrated global fit or proof claim","historical_witness_generated":false,"global_proof_generated":false}))
}


#[cfg(test)]
pub(crate) fn assign_inactive_leaf_for_prefix(
    e: &Engine, b: &Boundary, slot: usize, profile: [u8;32],
) -> Result<HeaderLeafAssignment,String> {
    b.profile.validate()?;
    if !matches!(b.profile.tree.headers, 3 | 4) || b.profile.role(slot)? == Role::Genuine {
        return Err("prefix inactive leaf requires N3/N4 and a non-genuine role".into());
    }
    assign_inactive_leaf(e,b,slot,profile)
}

#[cfg(test)]
pub(crate) fn assign_padding_position_fault_for_prefix(
    e: &Engine, b: &Boundary, slot: usize, profile: [u8;32],
) -> Result<HeaderLeafAssignment,String> {
    b.profile.validate()?;
    if b.profile.tree.headers != 4 || b.profile.role(slot)? != Role::Padding {
        return Err("prefix padding-position fault requires the N4 padding role".into());
    }
    let envelope = Envelope {raw:Vec::new(), height:0, lower:[0;28], upper:[0;28], profile};
    let assigned = assign(e,b,slot,&envelope,Mutation::PaddingPosition)?;
    if assigned.digest == assigned.native {
        return Err("prefix padding-position fault did not alter the leaf digest".into());
    }
    Ok(HeaderLeafAssignment {values:assigned.values,digest:assigned.digest})
}

#[cfg(test)]
pub(crate) fn assign_fixed_slot_for_prefix(
    e: &Engine, p: &fixed::FixedProfile, slot: usize, bytes: &[u8],
) -> Result<HeaderLeafAssignment,String> {
    p.validate()?;
    if !matches!(p.tree.headers, 3 | 4) {return Err("prefix fixed assignment requires N3/N4".into());}
    assign_fixed_slot_native(e,p,slot,bytes)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test] fn runtime_header_leaf_assignment_matches_fixture_oracle_and_fails_closed() {
        use ergo_header_core::Header;
        let pack:serde_json::Value=serde_json::from_str(include_str!("../vendor/header-core/fixtures/governance-contiguous-header-packs-v1.json")).unwrap();
        let raw=pack["networks"]["mainnet"]["source_headers_hex"][1].as_str().unwrap();
        let raw=raw.as_bytes().chunks_exact(2).map(|pair|u8::from_str_radix(std::str::from_utf8(pair).unwrap(),16).unwrap()).collect::<Vec<_>>();
        let header=Header::decode(&raw,None).unwrap();assert_eq!(header.height,2);assert_eq!(header.encode().unwrap(),raw);
        let engine=fixed::engine().unwrap();let boundary=compile(engine,LeafProfile::new(3,[0;32]).unwrap()).unwrap();
        let profile=[0x2a;32];let lower=[0;28];let mut upper=[0;28];upper[27]=1;
        let runtime=assign_header_leaf(engine,&boundary,0,&header,lower,upper,profile).unwrap();
        let legacy=assign(engine,&boundary,0,&Envelope{raw,height:header.height,lower,upper,profile},Mutation::None).unwrap();
        assert_eq!(runtime.values,legacy.values);assert_eq!(runtime.digest,legacy.digest);assert_eq!(runtime.digest,legacy.native);
        assert!(failures(&boundary,0,&runtime.values,None).unwrap().is_empty());
        assert!(assign_header_leaf(engine,&boundary,1,&header,lower,upper,profile).is_err());
        assert!(assign_header_leaf(engine,&boundary,2,&header,lower,upper,profile).is_err());
    }
    #[test] fn streamed_mainnet_h3_leaf_and_header_alias_claims_share_one_dory_commitment() {
        use std::io::{Read,Seek,SeekFrom,Write};
        use num_bigint::BigUint;
        #[derive(Clone,Copy,Default)]
        struct PhaseTime {calls:u64,nanos:u128,enabled:bool}
        #[derive(Clone,Copy,Default)]
        struct H3PhaseTimes {gkr_produce:PhaseTime,gkr_leaf_produce:PhaseTime,gkr_serializer_produce:PhaseTime,
            gkr_slot_local_produce:PhaseTime,gkr_work_link_produce:PhaseTime,gkr_header_alias_produce:PhaseTime,
            gkr_topology_link_produce:PhaseTime,gkr_verify:PhaseTime,dory_open:PhaseTime,dory_verify:PhaseTime,
            claim_evaluation:PhaseTime}
        #[derive(Default)]
        struct CoefficientProfile {calls:std::cell::Cell<u64>,nanos:std::cell::Cell<u128>,enabled:std::cell::Cell<bool>}
        #[derive(Default)]
        struct SerializerProfile {load_copy:PhaseTime,term_visit:PhaseTime,coefficient_eval:CoefficientProfile}
        fn enabled_serializer_profile()->SerializerProfile{
            let mut profile=SerializerProfile::default();profile.load_copy.enabled=true;profile.term_visit.enabled=true;
            profile.coefficient_eval.enabled.set(true);profile
        }
        #[derive(Clone,Copy)]
        enum GkrProducerKind {Leaf,Serializer,SlotLocal,WorkLink,HeaderAlias,TopologyLink}
        fn record_time(phase:&mut PhaseTime,nanos:u128){
            phase.calls=phase.calls.saturating_add(1);phase.nanos=phase.nanos.saturating_add(nanos);
        }
        fn measure<T>(phase:&mut PhaseTime,action:impl FnOnce()->T)->T{
            if !phase.enabled{return action();}
            let started=std::time::Instant::now();let result=action();
            record_time(phase,started.elapsed().as_nanos());result
        }
        fn measure_coefficient<T>(phase:&CoefficientProfile,action:impl FnOnce()->T)->T{
            if !phase.enabled.get(){return action();}
            let started=std::time::Instant::now();let result=action();let elapsed=started.elapsed().as_nanos();
            phase.calls.set(phase.calls.get().saturating_add(1));
            phase.nanos.set(phase.nanos.get().saturating_add(elapsed));result
        }
        fn measure_gkr_producer<T>(timings:&mut H3PhaseTimes,kind:GkrProducerKind,action:impl FnOnce()->T)->T{
            if !timings.gkr_produce.enabled{return action();}
            let started=std::time::Instant::now();let result=action();let elapsed=started.elapsed().as_nanos();
            record_time(&mut timings.gkr_produce,elapsed);
            let bucket=match kind{
                GkrProducerKind::Leaf=>&mut timings.gkr_leaf_produce,
                GkrProducerKind::Serializer=>&mut timings.gkr_serializer_produce,
                GkrProducerKind::SlotLocal=>&mut timings.gkr_slot_local_produce,
                GkrProducerKind::WorkLink=>&mut timings.gkr_work_link_produce,
                GkrProducerKind::HeaderAlias=>&mut timings.gkr_header_alias_produce,
                GkrProducerKind::TopologyLink=>&mut timings.gkr_topology_link_produce,
            };
            record_time(bucket,elapsed);result
        }
        let mut timings=H3PhaseTimes::default();
        let mut serializer_profile=enabled_serializer_profile();
        let mut serializer_cache_profile=enabled_serializer_profile();
        timings.gkr_produce.enabled=true;timings.gkr_verify.enabled=true;timings.dory_open.enabled=true;
        timings.dory_verify.enabled=true;timings.claim_evaluation.enabled=true;
        fn prove_leaf(boundary:&Boundary,source:&crate::packed::PackedFile,commitment:&[u8],timings:&mut H3PhaseTimes)
            ->Result<(crate::gkr::GkrProof,crate::gkr::InputClaim,crate::transcript::Transcript),String>{
            let mut transcript=crate::transcript::Transcript::new(b"nipopow-v2-h3-streamed-leaf-b3-v1");
            let profile=serde_json::to_vec(&boundary.profile).map_err(|e|e.to_string())?;
            let proof_result=measure_gkr_producer(timings,GkrProducerKind::Leaf,||crate::sparse_stream_roster::prove(20,2,14,0,&[14],|slot|read_slot(source,slot),&mut transcript,
                |t|{t.append_bytes(b"leaf-profile",&profile);t.append_bytes(b"input-commitment",commitment);},
                |slot,sink|{
                    let mut failure=None;boundary.emit_slot(slot,|mut term|{
                        if failure.is_none(){term.row-=slot*ROW_WIDTH;term.gate.left-=slot*WIDTH;term.gate.right-=slot*WIDTH;
                            if let Err(error)=sink(term){failure=Some(error);}}
                    })?;if let Some(error)=failure{return Err(error);}Ok(())
                },|r,u,v|coefficients(boundary,r,u,v)));
            proof_result.map_err(|e|e.to_string()).map(|(proof,claim)|(proof,claim,transcript))
        }
        fn bind_serializer_statement(t:&mut crate::transcript::Transcript,serializer:&crate::serializer::Compiled,
            nph2:&[u8],commitment:&[u8],row_count:usize){
            t.append_bytes(b"serializer-claim-version",b"mainnet-h3-canonical-header-output-v1");
            t.append_bytes(b"nph2-input",&hash(nph2));t.append_bytes(b"input-commitment",commitment);
            t.append_u64(b"serializer-circuit-rows",serializer.circuit.row_count as u64);
            t.append_u64(b"serializer-proof-rows",row_count as u64);
            t.append_u64(b"serializer-circuit-terms",serializer.circuit.terms.len() as u64);
        }
        fn public_header_raws(nph2:&[u8])->Result<Vec<Vec<u8>>,String>{
            let input=crate::nph2_header_source::MainnetH3Input::decode_nph2(nph2).map_err(|error|error.to_string())?;
            Ok(input.headers().iter().map(|header|header.raw_bytes().to_vec()).collect())
        }
        fn prove_serializer(serializer:&crate::serializer::Compiled,nph2:&[u8],
            commitment:&[u8],source:&crate::packed::PackedFile,timings:&mut H3PhaseTimes,profile:&mut SerializerProfile,
            cache_budget_bytes:Option<usize>)
            ->Result<(crate::gkr::GkrProof,crate::gkr::InputClaim,crate::transcript::Transcript,usize),String>{
            const PUBLIC_BITS:usize=514*8+10;
            let public_raws=public_header_raws(nph2)?;
            if public_raws.len()!=3{return Err("public serializer claim requires exact H3 input".into());}
            let row_count=serializer.circuit.row_count.checked_add(PUBLIC_BITS).ok_or("serializer row count overflow")?.next_power_of_two();
            let row_bits=row_count.trailing_zeros() as usize;
            let mut transcript=crate::transcript::Transcript::new(b"nipopow-v2-h3-streamed-public-serializer-v1");
            bind_serializer_statement(&mut transcript,serializer,nph2,commitment,row_count);
            let proof_result=measure_gkr_producer(timings,GkrProducerKind::Serializer,||crate::sparse_stream_roster::prove_with_cache_budget_for_test(20,2,row_bits,0,&[row_bits],cache_budget_bytes,
                |slot|measure(&mut profile.load_copy,||read_slot(source,slot)),&mut transcript,|_|{},
                |slot,sink|measure(&mut profile.term_visit,||{
                    let mut failure=None;
                    for original in &serializer.circuit.terms {
                        let mut term=original.clone();
                        term.gate.left=term.gate.left.checked_add(crate::header_hash::SERIALIZER_OFFSET).ok_or("serializer left wire overflow")?;
                        term.gate.right=term.gate.right.checked_add(crate::header_hash::SERIALIZER_OFFSET).ok_or("serializer right wire overflow")?;
                        if let Err(error)=sink(term){failure=Some(error);break;}
                    }
                    if let Some(error)=failure{return Err(error);}
                    let raw=&public_raws[slot.min(2)];
                    if raw.len()>514{return Err("public NPH2 header exceeds serializer bound".into());}
                    let mut row=serializer.circuit.row_count;
                    for (byte,wire_bits) in serializer.layout.bytes.iter().enumerate(){
                        let expected=raw.get(byte).copied().unwrap_or(0);
                        for (bit,&wire) in wire_bits.iter().enumerate(){
                            sink(crate::sparse::Term{row,gate:crate::gkr::Gate{left:crate::header_hash::SERIALIZER_OFFSET+wire,right:0,
                                c0:-Fr::from(((expected>>bit)&1) as u64),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()}})?;
                            row+=1;
                        }
                    }
                    for (bit,&wire) in serializer.layout.length.iter().enumerate(){
                        sink(crate::sparse::Term{row,gate:crate::gkr::Gate{left:crate::header_hash::SERIALIZER_OFFSET+wire,right:0,
                            c0:-Fr::from(((raw.len()>>bit)&1) as u64),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()}})?;
                        row+=1;
                    }
                    Ok(())
                }),|r,u,v|measure_coefficient(&profile.coefficient_eval,||{
                    let mut out=[Fr::zero();4];
                    for slot in 0usize..4{
                        let row_slot=slot.checked_mul(row_count).ok_or("serializer row slot overflow")?;
                        let input_slot=slot.checked_mul(WIDTH).ok_or("serializer input slot overflow")?;
                        let mut visit=|term:crate::sparse::Term|->Result<(),String>{
                            let weight=crate::work_tree_wiring::eq_index(r,row_slot+term.row)
                                *crate::work_tree_wiring::eq_index(u,input_slot+term.gate.left)
                                *crate::work_tree_wiring::eq_index(v,input_slot+term.gate.right);
                            for (sum,coefficient) in out.iter_mut().zip([term.gate.c0,term.gate.c1,term.gate.c2,term.gate.c3]){
                                *sum+=weight*coefficient;
                            }
                            Ok(())
                        };
                        for original in &serializer.circuit.terms{
                            let mut term=original.clone();term.gate.left+=crate::header_hash::SERIALIZER_OFFSET;
                            term.gate.right+=crate::header_hash::SERIALIZER_OFFSET;visit(term)?;
                        }
                        let raw=&public_raws[slot.min(2)];let mut row=serializer.circuit.row_count;
                        for (byte,wire_bits) in serializer.layout.bytes.iter().enumerate(){
                            let expected=raw.get(byte).copied().unwrap_or(0);
                            for (bit,&wire) in wire_bits.iter().enumerate(){
                                visit(crate::sparse::Term{row,gate:crate::gkr::Gate{left:crate::header_hash::SERIALIZER_OFFSET+wire,right:0,
                                    c0:-Fr::from(((expected>>bit)&1) as u64),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()}})?;row+=1;
                            }
                        }
                        for (bit,&wire) in serializer.layout.length.iter().enumerate(){
                            visit(crate::sparse::Term{row,gate:crate::gkr::Gate{left:crate::header_hash::SERIALIZER_OFFSET+wire,right:0,
                                c0:-Fr::from(((raw.len()>>bit)&1) as u64),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()}})?;row+=1;
                        }
                    }
                    Ok(out)
                })));
            let (proof,claim)=proof_result.map_err(|error|error.to_string())?;
            Ok((proof,claim,transcript,row_count))
        }
        fn read_slot(source:&crate::packed::PackedFile,slot:usize)->Result<Vec<Fr>,String>{
            let chunks=WIDTH/(1<<16);let first=slot.checked_mul(chunks).ok_or("slot chunk offset overflow")?;
            let mut values=Vec::with_capacity(WIDTH);
            for chunk in 0..chunks{values.extend(source.read_copy(1<<16,first+chunk)?);}Ok(values)
        }
        fn fixed_stream_coefficients(engine:&Engine,profile:&fixed::FixedProfile,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String>{
            if r.len()!=13||u.len()!=22||v.len()!=22{return Err("H3 fixed streamed dimensions".into());}
            let mut out=[Fr::zero();4];
            for slot in 0..profile.tree.slots{fixed::emit_slot(engine,profile,slot,|term|{
                let weight=crate::work_tree_wiring::eq_index(r,term.row)
                    *crate::work_tree_wiring::eq_index(u,term.gate.left)
                    *crate::work_tree_wiring::eq_index(v,term.gate.right);
                for (sum,coefficient) in out.iter_mut().zip([term.gate.c0,term.gate.c1,term.gate.c2,term.gate.c3]){
                    *sum+=weight*coefficient;
                }
            })?;}Ok(out)
        }
        fn prove_slot_claim(source:&crate::packed::PackedFile,committed:&crate::packed::PackedCommitted,timings:&mut H3PhaseTimes,
            setup:&crate::pcs::Setup,commitment:&[u8],domain:&[u8],row_bits:usize,
            bind:impl Fn(&mut crate::transcript::Transcript),
            visit:impl FnMut(usize,&mut dyn FnMut(crate::sparse::Term)->Result<(),String>)->Result<(),String>,
            wiring:impl Fn(&[Fr],&[Fr],&[Fr])->Result<[Fr;4],String>)->Result<(),String>{
            let mut prover=crate::transcript::Transcript::new(domain);
            let proof_result=measure_gkr_producer(timings,GkrProducerKind::SlotLocal,||crate::sparse_stream_roster::prove(20,2,row_bits,0,&[row_bits],
                |slot|read_slot(source,slot),&mut prover,|t|bind(t),visit,|r,u,v|wiring(r,u,v)));
            let (proof,claim)=proof_result?;
            let evaluated=measure(&mut timings.claim_evaluation,||source.evaluate(&claim.point))?;
            assert_eq!(evaluated,claim.value,"streamed local claim input evaluation");
            let opening=measure(&mut timings.dory_open,||crate::packed::open(committed,source,&claim.point,setup,&mut prover))?;
            let opening=crate::pcs::decode_proof(&crate::pcs::encode_proof(&opening)?,22)?;
            let rows=(1usize<<row_bits)*4;
            let mut verifier=crate::transcript::Transcript::new(domain);
            let verify_result=measure(&mut timings.gkr_verify,||crate::gkr::verify_with_wiring(&[22],rows,&proof,&mut verifier,|t|bind(t),
                |_,r,u,v|wiring(r,u,v).map_err(|_|crate::gkr::GkrError::PointDimension)));
            let verified=verify_result.map_err(|error|error.to_string())?;
            assert_eq!(verified,claim,"streamed local GKR claim");
            measure(&mut timings.dory_verify,||crate::pcs::verify(committed.commitment,verified.value,&verified.point,&opening,setup,&mut verifier))?;
            Ok(())
        }
        fn prove_work_link(source:&crate::packed::PackedFile,committed:&crate::packed::PackedCommitted,timings:&mut H3PhaseTimes,
            setup:&crate::pcs::Setup,commitment:&[u8],boundary:&crate::work_tree_work::Boundary,
            family:&crate::work_tree_wiring::Family)->Result<(),String>{
            let descriptor=&boundary.profile().tree;let slot_bits=descriptor.slot_log();
            let count=family.count(descriptor)?;let row_bits=count.row_log;
            let base_row_bits=row_bits.checked_sub(slot_bits).ok_or("work link row width underflow")?;
            let domain=b"nipopow-v2-h3-streamed-b4-link-v1";
            let mut prover=crate::transcript::Transcript::new(domain);
            let work_profile=serde_json::to_vec(boundary.profile()).map_err(|e|e.to_string())?;
            let proof_result=measure_gkr_producer(timings,GkrProducerKind::WorkLink,||crate::sparse_stream_roster::prove_edge_terms(20,slot_bits,base_row_bits,0,&[base_row_bits],
                |left_endpoint,slot,sink|family.emit_endpoint_terms(descriptor,left_endpoint,slot,|source_slot,family_row,term|
                    sink(crate::sparse_stream_roster::EdgeTerm{source_slot,family_row,term})),
                |slot|read_slot(source,slot),&mut prover,|t|{
                    t.append_bytes(b"work-profile",&work_profile);t.append_bytes(b"work-link-name",family.name.as_bytes());
                    t.append_bytes(b"setup-id",&setup.id);
                    t.append_bytes(b"input-commitment",commitment);
                },|r,u,v|family.coefficients(descriptor,r,u,v)));
            let (proof,claim,left,right)=proof_result?;
            assert!(left&&right,"B4 link must cover both endpoints: {}",family.name);
            let evaluated=measure(&mut timings.claim_evaluation,||source.evaluate(&claim.point))?;
            assert_eq!(evaluated,claim.value,"streamed B4 link input evaluation");
            let opening=measure(&mut timings.dory_open,||crate::packed::open(committed,source,&claim.point,setup,&mut prover))?;
            let opening=crate::pcs::decode_proof(&crate::pcs::encode_proof(&opening)?,22)?;
            let mut verifier=crate::transcript::Transcript::new(domain);
            let verify_result=measure(&mut timings.gkr_verify,||crate::gkr::verify_with_wiring(&[22],1usize<<row_bits,&proof,&mut verifier,|t|{
                t.append_bytes(b"work-profile",&work_profile);t.append_bytes(b"work-link-name",family.name.as_bytes());
                t.append_bytes(b"setup-id",&setup.id);
                t.append_bytes(b"input-commitment",commitment);
            },|_,r,u,v|family.coefficients(descriptor,r,u,v).map_err(|_|crate::gkr::GkrError::PointDimension)));
            let verified=verify_result.map_err(|error|error.to_string())?;
            assert_eq!(verified,claim,"streamed B4 link GKR claim {}",family.name);
            measure(&mut timings.dory_verify,||crate::pcs::verify(committed.commitment,verified.value,&verified.point,&opening,setup,&mut verifier))?;
            Ok(())
        }
        fn prove_topology_link(source:&crate::packed::PackedFile,committed:&crate::packed::PackedCommitted,timings:&mut H3PhaseTimes,
            setup:&crate::pcs::Setup,commitment:&[u8],nph2:&[u8],topology:&crate::work_tree_wiring::Topology,
            family:&crate::work_tree_wiring::Family)->Result<(),String>{
            let descriptor=&topology.descriptor;let slot_bits=descriptor.slot_log();let count=family.count(descriptor)?;
            let row_bits=count.row_log;let base_row_bits=row_bits.checked_sub(slot_bits).ok_or("B1 link row width underflow")?;
            let topology_report=topology.report()?;
            let mut prover=crate::transcript::Transcript::new(b"nipopow-v2-h3-streamed-b1-root-link-v1");
            let proof_result=measure_gkr_producer(timings,GkrProducerKind::TopologyLink,||crate::sparse_stream_roster::prove_edge_terms(20,slot_bits,base_row_bits,0,&[base_row_bits],
                |left_endpoint,slot,sink|family.emit_endpoint_terms(descriptor,left_endpoint,slot,|source_slot,family_row,term|
                    sink(crate::sparse_stream_roster::EdgeTerm{source_slot,family_row,term})),
                |slot|read_slot(source,slot),&mut prover,|t|{
                    t.append_bytes(b"nph2-input",&hash(nph2));
                    t.append_bytes(b"descriptor",topology_report.descriptor_blake2b256.as_bytes());
                    t.append_bytes(b"topology",topology_report.topology_blake2b256.as_bytes());
                    t.append_bytes(b"b1-family",family.name.as_bytes());t.append_bytes(b"setup-id",&setup.id);
                    t.append_bytes(b"input-commitment",commitment);
                },|r,u,v|family.coefficients(descriptor,r,u,v)));
            let (proof,claim,left,right)=proof_result?;
            assert!(left&&right,"B1 relation must cover both endpoints: {}",family.name);
            let evaluated=measure(&mut timings.claim_evaluation,||source.evaluate(&claim.point))?;
            assert_eq!(evaluated,claim.value,"streamed B1 claim input evaluation {}",family.name);
            let opening=measure(&mut timings.dory_open,||crate::packed::open(committed,source,&claim.point,setup,&mut prover))?;
            let opening=crate::pcs::decode_proof(&crate::pcs::encode_proof(&opening)?,22)?;
            let mut verifier=crate::transcript::Transcript::new(b"nipopow-v2-h3-streamed-b1-root-link-v1");
            let verify_result=measure(&mut timings.gkr_verify,||crate::gkr::verify_with_wiring(&[22],1usize<<row_bits,&proof,&mut verifier,|t|{
                t.append_bytes(b"nph2-input",&hash(nph2));
                t.append_bytes(b"descriptor",topology_report.descriptor_blake2b256.as_bytes());
                t.append_bytes(b"topology",topology_report.topology_blake2b256.as_bytes());
                t.append_bytes(b"b1-family",family.name.as_bytes());t.append_bytes(b"setup-id",&setup.id);
                t.append_bytes(b"input-commitment",commitment);
            },|_,r,u,v|family.coefficients(descriptor,r,u,v).map_err(|_|crate::gkr::GkrError::PointDimension)));
            let verified=verify_result.map_err(|error|error.to_string())?;
            assert_eq!(verified,claim,"streamed B1 GKR claim {}",family.name);
            measure(&mut timings.dory_verify,||crate::pcs::verify(committed.commitment,verified.value,&verified.point,&opening,setup,&mut verifier))?;
            Ok(())
        }
        let pack:serde_json::Value=serde_json::from_str(include_str!("../vendor/header-core/fixtures/governance-contiguous-header-packs-v1.json")).unwrap();
        let raws=pack["networks"]["mainnet"]["source_headers_hex"].as_array().unwrap().iter().take(3)
            .map(|item|item.as_str().unwrap().as_bytes().chunks_exact(2).map(|pair|u8::from_str_radix(std::str::from_utf8(pair).unwrap(),16).unwrap()).collect::<Vec<_>>()).collect::<Vec<_>>();
        let mut nph2=b"NPH2".to_vec();nph2.extend_from_slice(&3u32.to_be_bytes());
        for raw in &raws{nph2.extend_from_slice(&(raw.len() as u32).to_be_bytes());nph2.extend_from_slice(raw);}
        let input=crate::nph2_header_source::MainnetH3Input::decode_nph2(&nph2).unwrap();
        let headers=input.headers().iter().map(|record|record.decoded().clone()).collect::<Vec<_>>();
        assert_eq!(headers.iter().map(|h|h.height).collect::<Vec<_>>(),[1,2,3]);
        let engine=fixed::engine().unwrap();let serializer=crate::serializer::build(None).unwrap();let endpoints=&engine.base.endpoints;
        let mut profile_bytes=b"nipopow-v2/work-profile/v1\0".to_vec();profile_bytes.extend_from_slice(&crate::header_order::MAINNET_GENESIS);
        let profile=hash(&profile_bytes);
        let provisional=compile(engine,LeafProfile::new(3,[0;32]).unwrap()).unwrap();
        let mut work_cases=Vec::with_capacity(2);let mut cumulative=BigUint::from(0u8);
        for slot in 0..2 {
            let nbits=headers[slot+1].n_bits;let work=crate::work_tree_work::native_decode(nbits).unwrap();
            let upper=&cumulative+&work;work_cases.push((nbits,cumulative.clone(),work,upper.clone()));cumulative=upper;
        }
        let mut total=[0u8;28];let total_bytes=cumulative.to_bytes_be();assert!(total_bytes.len()<=28);
        total[28-total_bytes.len()..].copy_from_slice(&total_bytes);
        let mut leaf_assignments=Vec::with_capacity(2);let mut leaf_digests=Vec::with_capacity(2);
        for (slot,(nbits,lower,_,upper)) in work_cases.iter().enumerate(){
            let mut lower_be=[0u8;28];let lower_bytes=lower.to_bytes_be();assert!(lower_bytes.len()<=28);
            lower_be[28-lower_bytes.len()..].copy_from_slice(&lower_bytes);
            let mut upper_be=[0u8;28];let upper_bytes=upper.to_bytes_be();assert!(upper_bytes.len()<=28);
            upper_be[28-upper_bytes.len()..].copy_from_slice(&upper_bytes);
            assert_eq!(*nbits,headers[slot+1].n_bits);
            let assignment=assign_header_leaf(engine,&provisional,slot,&headers[slot+1],lower_be,upper_be,profile).unwrap();
            leaf_digests.push(assignment.digest);leaf_assignments.push(assignment);
        }
        let mut node=b"N\x01\x00\x00\x00\x00".to_vec();node.extend_from_slice(&leaf_digests[0]);node.extend_from_slice(&leaf_digests[1]);
        let root=hash(&node);let boundary=compile(engine,LeafProfile::new(3,root).unwrap()).unwrap();
        let fixed_profile=fixed::FixedProfile::new(3,root).unwrap();
        let work_profile=crate::work_tree_work::WorkProfile::new(3,root,total).unwrap();
        let work_boundary=crate::work_tree_work::compile(engine.base,work_profile.clone()).unwrap();
        fn put_slot_bytes(values:&mut BTreeMap<usize,Fr>,slot:usize,wires:&[usize],bytes:&[u8]){
            let mut local=BTreeMap::new();put_bytes(&mut local,wires,bytes,false);
            for (wire,value) in local{values.insert(slot*WIDTH+wire,value);}
        }
        fn put_uint(values:&mut BTreeMap<usize,Fr>,wires:&[usize],number:&BigUint){
            for (bit,&wire) in wires.iter().enumerate(){values.insert(wire,Fr::from(number.bit(bit as u64) as u64));}
        }
        let mut fixed_slots=Vec::with_capacity(4);
        for slot in 0..4 {
            let mut values=BTreeMap::new();
            let preimage=match slot{0=>Some(node.as_slice()),1=>Some(profile_bytes.as_slice()),_=>None};
            if slot==0{
                put_slot_bytes(&mut values,slot,&endpoints.node_left,&leaf_digests[0]);
                put_slot_bytes(&mut values,slot,&endpoints.node_right,&leaf_digests[1]);
            }
            fixed_slot(engine,&fixed_profile,slot,preimage.unwrap_or(&[]),&mut values).unwrap();
            fixed_slots.push(values);
        }
        let mut work_slots=vec![BTreeMap::new();4];
        for (slot,(nbits,lower,work,upper)) in work_cases.iter().enumerate(){
            let values=&mut work_slots[slot];put_uint(values,&endpoints.n_bits,&BigUint::from(*nbits));
            put_uint(values,&endpoints.lower,lower);put_uint(values,&endpoints.work,work);put_uint(values,&endpoints.upper,upper);
            let minus=if work==&BigUint::from(0u8){BigUint::from(0u8)}else{work-BigUint::from(1u8)};
            put_uint(values,&endpoints.work_minus_one,&minus);
            values.insert(endpoints.exponent[(nbits>>24) as usize],Fr::one());
        }
        let packed_path=std::env::temp_dir().join(format!("nipopow-h3-streamed-{}.bits",std::process::id()));
        let bad_path=std::env::temp_dir().join(format!("nipopow-h3-streamed-mutant-{}.bits",std::process::id()));
        let witness_started=std::time::Instant::now();
        let mut writer=crate::packed::PackedFileWriter::create_new(&packed_path,22).unwrap();
        for slot in 0..4 {
            let header_index=slot.min(2);let header=&headers[header_index];
            let fields=crate::serializer::Fields::from_header(header).unwrap();
            let serialized=serializer.assign(&fields);
            let mut joined=crate::header_compact_links::build(Some(&fields)).unwrap();
            let (previous_height,previous_time,first)=if header_index==0{(0,0,true)}else{(headers[header_index-1].height,headers[header_index-1].timestamp,false)};
            crate::header_compact_links::assign_order(&mut joined,&fields,previous_height,previous_time,first).unwrap();
            let mut slot_values=joined.base.base.base.input.as_ref().unwrap().clone();assert_eq!(slot_values.len(),WIDTH);
            assert_eq!(&slot_values[crate::header_hash::SERIALIZER_OFFSET..crate::header_hash::AUX_OFFSET],serialized.as_slice(),
                "joined header witness must contain the compiled serializer assignment");
            let mut released=CORES.iter().chain(std::iter::once(&fixed::NODE_CORE)).map(|start|*start..*start+CORE).collect::<Vec<_>>();
            released.push(AUX..AUX+AUX_BITS);released.push(layout::ENDPOINT_BASE..layout::ENDPOINT_BASE+layout::ENDPOINT_WIDTH);
            for range in released{slot_values[range].fill(Fr::zero());}
            let assignment=if slot<2 {
                leaf_assignments.remove(0)
            }else{
                let leaf_slot=slot.min(2);let envelope=Envelope::sample(leaf_slot,100,profile);
                let assigned=assign(engine,&boundary,leaf_slot,&envelope,Mutation::None).unwrap();
                HeaderLeafAssignment{values:assigned.values,digest:assigned.digest}
            };
            for (wire,value) in assignment.values{slot_values[wire]=value;}
            for (global_wire,value) in &fixed_slots[slot]{slot_values[global_wire-slot*WIDTH]=*value;}
            for (&wire,&source_wire) in endpoints.n_bits.iter().zip(&serializer.layout.fields.n_bits){slot_values[wire]=serialized[source_wire];}
            for (&wire,&value) in &work_slots[slot]{
                if endpoints.n_bits.contains(&wire){assert_eq!(slot_values[wire],value,"B4 nBits must equal serialized header field, slot {slot}");}
                if endpoints.lower.contains(&wire)||endpoints.upper.contains(&wire){
                    assert_eq!(slot_values[wire],value,"B4 interval must equal B3 leaf envelope, slot {slot}");
                }
                slot_values[wire]=value;
            }
            assert!(slot_values.iter().all(|value|value.is_zero()||value.is_one()),"slot {slot} witness must be Boolean");
            let mut bytes=vec![0u8;WIDTH/8];
            for (index,value) in slot_values.iter().enumerate(){if value.is_one(){bytes[index/8]|=1<<(index%8);}}
            writer.write_bytes(&bytes).unwrap();
        }
        let source=writer.finish().unwrap();let witness_wall_ns=witness_started.elapsed().as_nanos();
        assert_eq!(source.input_len(),1<<22);
        let witness_io=source.io_metrics_snapshot();
        let setup_started=std::time::Instant::now();
        let setup=crate::pcs::generate_setup(22).unwrap();let setup_wall_ns=setup_started.elapsed().as_nanos();
        source.reset_io_metrics();
        let commit_started=std::time::Instant::now();
        let committed=crate::packed::commit(&source,&setup).unwrap();let commit_wall_ns=commit_started.elapsed().as_nanos();
        let commit_io=source.io_metrics_snapshot();source.reset_io_metrics();
        let commitment=crate::pcs::encode_commitment(&committed.commitment).unwrap();
        let (leaf_proof,leaf_claim,mut leaf_transcript)=prove_leaf(&boundary,&source,&commitment,&mut timings).unwrap();
        assert_eq!(measure(&mut timings.claim_evaluation,||source.evaluate(&leaf_claim.point)).unwrap(),leaf_claim.value);
        let leaf_open=measure(&mut timings.dory_open,||crate::packed::open(&committed,&source,&leaf_claim.point,&setup,&mut leaf_transcript)).unwrap();
        let leaf_open_bytes=crate::pcs::encode_proof(&leaf_open).unwrap();
        let mut leaf_verifier=crate::transcript::Transcript::new(b"nipopow-v2-h3-streamed-leaf-b3-v1");
        let leaf_verify_result=measure(&mut timings.gkr_verify,||crate::gkr::verify_with_wiring(&[22],1<<16,&leaf_proof,&mut leaf_verifier,
            |t|{t.append_bytes(b"leaf-profile",&serde_json::to_vec(&boundary.profile).unwrap());t.append_bytes(b"input-commitment",&commitment);},
            |_,r,u,v|coefficients(&boundary,r,u,v).map_err(|_|crate::gkr::GkrError::PointDimension)));
        let leaf_verified=leaf_verify_result.unwrap();
        assert_eq!(leaf_verified,leaf_claim);
        let leaf_open=crate::pcs::decode_proof(&leaf_open_bytes,22).unwrap();
        measure(&mut timings.dory_verify,||crate::pcs::verify(committed.commitment,leaf_verified.value,&leaf_verified.point,&leaf_open,&setup,&mut leaf_verifier)).unwrap();

        let public_raws=public_header_raws(&nph2).unwrap();
        const SERIALIZER_CACHE_BASELINE_BYTES:usize=320*1024*1024;
        // None routes through the same configured default as production prove().
        let serializer_baseline_started=std::time::Instant::now();
        let (serializer_baseline_proof,serializer_baseline_claim,serializer_baseline_transcript,serializer_baseline_rows)=
            prove_serializer(&serializer,&nph2,&commitment,&source,&mut timings,&mut serializer_profile,
                Some(SERIALIZER_CACHE_BASELINE_BYTES)).unwrap();
        let serializer_baseline_wall_ns=serializer_baseline_started.elapsed().as_nanos();
        let serializer_cache_started=std::time::Instant::now();
        let (serializer_proof,serializer_claim,mut serializer_transcript,serializer_rows)=
            prove_serializer(&serializer,&nph2,&commitment,&source,&mut timings,&mut serializer_cache_profile,
                None).unwrap();
        let serializer_cache_wall_ns=serializer_cache_started.elapsed().as_nanos();
        assert_eq!(serializer_proof,serializer_baseline_proof,"512 MiB cache-default GKR proof must match the 320 MiB baseline");
        assert_eq!(crate::gkr::encode_proof(&serializer_proof).unwrap(),crate::gkr::encode_proof(&serializer_baseline_proof).unwrap(),
            "512 MiB cache-default GKR proof bytes must match the 320 MiB baseline");
        assert_eq!(serializer_claim,serializer_baseline_claim,"cache-default input claim must match the 320 MiB baseline");
        assert_eq!(serializer_rows,serializer_baseline_rows,"cache-default serializer row count");
        let mut baseline_probe=serializer_baseline_transcript.clone();let mut cache_probe=serializer_transcript.clone();
        assert_eq!(baseline_probe.challenge_scalar(b"serializer-cache-budget-parity"),
            cache_probe.challenge_scalar(b"serializer-cache-budget-parity"),"cache-default transcript continuation");
        assert_eq!(measure(&mut timings.claim_evaluation,||source.evaluate(&serializer_claim.point)).unwrap(),serializer_claim.value);
        let serializer_open=measure(&mut timings.dory_open,||crate::packed::open(&committed,&source,&serializer_claim.point,&setup,&mut serializer_transcript)).unwrap();
        let serializer_open=crate::pcs::decode_proof(&crate::pcs::encode_proof(&serializer_open).unwrap(),22).unwrap();
        let mut serializer_verifier=crate::transcript::Transcript::new(b"nipopow-v2-h3-streamed-public-serializer-v1");
        let serializer_verify_result=measure(&mut timings.gkr_verify,||{
            bind_serializer_statement(&mut serializer_verifier,&serializer,&nph2,&commitment,serializer_rows);
            crate::gkr::verify_with_wiring(&[22],serializer_rows*4,&serializer_proof,&mut serializer_verifier,|_|{},
            |_,r,u,v|{
                let mut out=[Fr::zero();4];
                for slot in 0..4{
                    let row_slot=slot*serializer_rows;let input_slot=slot*WIDTH;
                    let mut add=|term:&crate::sparse::Term|{
                        let weight=crate::work_tree_wiring::eq_index(r,row_slot+term.row)
                            *crate::work_tree_wiring::eq_index(u,input_slot+term.gate.left)
                            *crate::work_tree_wiring::eq_index(v,input_slot+term.gate.right);
                        for (sum,coefficient) in out.iter_mut().zip([term.gate.c0,term.gate.c1,term.gate.c2,term.gate.c3]){*sum+=weight*coefficient;}
                    };
                    for original in &serializer.circuit.terms{
                        let mut term=original.clone();term.gate.left+=crate::header_hash::SERIALIZER_OFFSET;
                        term.gate.right+=crate::header_hash::SERIALIZER_OFFSET;add(&term);
                    }
                    let raw=&public_raws[slot.min(2)];let mut row=serializer.circuit.row_count;
                    for (byte,wire_bits) in serializer.layout.bytes.iter().enumerate(){
                        let expected=raw.get(byte).copied().unwrap_or(0);
                        for (bit,&wire) in wire_bits.iter().enumerate(){
                            add(&crate::sparse::Term{row,gate:crate::gkr::Gate{left:crate::header_hash::SERIALIZER_OFFSET+wire,right:0,
                                c0:-Fr::from(((expected>>bit)&1) as u64),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()}});row+=1;
                        }
                    }
                    for (bit,&wire) in serializer.layout.length.iter().enumerate(){
                        add(&crate::sparse::Term{row,gate:crate::gkr::Gate{left:crate::header_hash::SERIALIZER_OFFSET+wire,right:0,
                            c0:-Fr::from(((raw.len()>>bit)&1) as u64),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()}});row+=1;
                    }
                }
                Ok(out)
            })
        });
        let serializer_verified=serializer_verify_result.unwrap();
        assert_eq!(serializer_verified,serializer_claim);
        measure(&mut timings.dory_verify,||crate::pcs::verify(committed.commitment,serializer_verified.value,&serializer_verified.point,&serializer_open,&setup,&mut serializer_verifier)).unwrap();

        let fixed_profile_bytes=serde_json::to_vec(&fixed_profile).unwrap();
        prove_slot_claim(&source,&committed,&mut timings,&setup,&commitment,b"nipopow-v2-h3-streamed-b2-fixed-v1",11,
            |t|{t.append_bytes(b"fixed-profile",&fixed_profile_bytes);t.append_bytes(b"setup-id",&setup.id);
                t.append_bytes(b"input-commitment",&commitment);},
            |slot,sink|{
                let mut failure=None;fixed::emit_slot(engine,&fixed_profile,slot,|mut term|{
                    if failure.is_none(){term.row-=slot*fixed::ROW_WIDTH;
                        if term.gate.c1.is_zero()&&term.gate.c3.is_zero(){term.gate.left=WIDTH;}else{term.gate.left-=slot*WIDTH;}
                        if term.gate.c2.is_zero()&&term.gate.c3.is_zero(){term.gate.right=WIDTH;}else{term.gate.right-=slot*WIDTH;}
                        if let Err(error)=sink(term){failure=Some(error);}}
                })?;if let Some(error)=failure{return Err(error);}Ok(())
            },|r,u,v|fixed_stream_coefficients(engine,&fixed_profile,r,u,v)).unwrap();

        let work_profile_bytes=serde_json::to_vec(&work_profile).unwrap();
        prove_slot_claim(&source,&committed,&mut timings,&setup,&commitment,b"nipopow-v2-h3-streamed-b4-local-v1",11,
            |t|{t.append_bytes(b"work-profile",&work_profile_bytes);t.append_bytes(b"setup-id",&setup.id);
                t.append_bytes(b"input-commitment",&commitment);},
            |slot,sink|{
                let mut failure=None;work_boundary.emit_slot(slot,|mut term|{
                    if failure.is_none(){term.row-=slot*crate::work_tree_work::LOCAL_ROW_WIDTH;
                        if term.gate.c1.is_zero()&&term.gate.c3.is_zero(){term.gate.left=0;}else{term.gate.left-=slot*WIDTH;}
                        if term.gate.c2.is_zero()&&term.gate.c3.is_zero(){term.gate.right=0;}else{term.gate.right-=slot*WIDTH;}
                        if let Err(error)=sink(term){failure=Some(error);}}
                })?;if let Some(error)=failure{return Err(error);}Ok(())
            },|r,u,v|crate::work_tree_work::local_coefficients(&work_boundary,r,u,v)).unwrap();
        assert_eq!(work_boundary.links().len(),3,"B4 work-link roster");
        for family in work_boundary.links(){prove_work_link(&source,&committed,&mut timings,&setup,&commitment,&work_boundary,family).unwrap();}

        let topology=crate::work_tree_wiring::Topology::new(engine.base,3,root).unwrap();
        let alias=topology.families.iter().find(|family|family.name=="header_to_leaf_raw_length_nbits_height").unwrap();
        let family_count=alias.count(&topology.descriptor).unwrap();assert_eq!(family_count.terms,8372);
        let mut edge_transcript=crate::transcript::Transcript::new(b"nipopow-v2-h3-streamed-header-leaf-alias-v1");
        let edge_proof_result=measure_gkr_producer(&mut timings,GkrProducerKind::HeaderAlias,||crate::sparse_stream_roster::prove_edge_terms(20,2,13,0,&[13],
            |left,slot,sink|alias.emit_endpoint_terms(&topology.descriptor,left,slot,|source_slot,family_row,term|
                sink(crate::sparse_stream_roster::EdgeTerm{source_slot,family_row,term})),
            |slot|read_slot(&source,slot),&mut edge_transcript,|t|{
                t.append_bytes(b"nph2-input",&hash(&nph2));t.append_bytes(b"topology",topology.report().unwrap().topology_blake2b256.as_bytes());
                t.append_bytes(b"input-commitment",&commitment);
            },|r,u,v|alias.coefficients(&topology.descriptor,r,u,v)));
        let (edge_proof,edge_claim,edge_u,edge_v)=edge_proof_result.unwrap();
        assert!(edge_u&&edge_v);assert_eq!(measure(&mut timings.claim_evaluation,||source.evaluate(&edge_claim.point)).unwrap(),edge_claim.value);
        let edge_open=measure(&mut timings.dory_open,||crate::packed::open(&committed,&source,&edge_claim.point,&setup,&mut edge_transcript)).unwrap();
        let edge_open=crate::pcs::decode_proof(&crate::pcs::encode_proof(&edge_open).unwrap(),22).unwrap();
        let mut edge_verifier=crate::transcript::Transcript::new(b"nipopow-v2-h3-streamed-header-leaf-alias-v1");
        let topology_id=topology.report().unwrap().topology_blake2b256;
        let edge_verify_result=measure(&mut timings.gkr_verify,||crate::gkr::verify_with_wiring(&[22],1<<15,&edge_proof,&mut edge_verifier,|t|{
            t.append_bytes(b"nph2-input",&hash(&nph2));t.append_bytes(b"topology",topology_id.as_bytes());t.append_bytes(b"input-commitment",&commitment);
        },|_,r,u,v|alias.coefficients(&topology.descriptor,r,u,v).map_err(|_|crate::gkr::GkrError::PointDimension)));
        let edge_verified=edge_verify_result.unwrap();
        assert_eq!(edge_verified,edge_claim);
        measure(&mut timings.dory_verify,||crate::pcs::verify(committed.commitment,edge_verified.value,&edge_verified.point,&edge_open,&setup,&mut edge_verifier)).unwrap();

        for name in ["level_1_child_0","level_1_child_1","profile_digest_fanout","public_root"] {
            let family=topology.families.iter().find(|family|family.name==name).unwrap();
            prove_topology_link(&source,&committed,&mut timings,&setup,&commitment,&nph2,&topology,family).unwrap();
        }
        let proof_phase_times=timings;
        let proof_io=source.io_metrics_snapshot();
        timings.gkr_produce.enabled=false;timings.gkr_verify.enabled=false;timings.dory_open.enabled=false;
        timings.dory_verify.enabled=false;timings.claim_evaluation.enabled=false;
        serializer_profile.load_copy.enabled=false;serializer_profile.term_visit.enabled=false;
        serializer_profile.coefficient_eval.enabled.set(false);
        serializer_cache_profile.load_copy.enabled=false;serializer_cache_profile.term_visit.enabled=false;
        serializer_cache_profile.coefficient_eval.enabled.set(false);
        for (name,wire) in [("level_1_child_0",endpoints.node_left[0]),
            ("level_1_child_1",endpoints.node_right[0]),("profile_digest_fanout",endpoints.profile[0])] {
            let mutant_path=std::env::temp_dir().join(format!("nipopow-h3-b1-{name}-{}.bits",std::process::id()));
            std::fs::copy(&packed_path,&mutant_path).unwrap();
            let global_wire=wire;let mut file=std::fs::OpenOptions::new().read(true).write(true).open(&mutant_path).unwrap();
            file.seek(SeekFrom::Start((global_wire/8) as u64)).unwrap();let mut byte=[0];file.read_exact(&mut byte).unwrap();byte[0]^=1<<(global_wire%8);
            file.seek(SeekFrom::Start((global_wire/8) as u64)).unwrap();file.write_all(&byte).unwrap();file.sync_all().unwrap();drop(file);
            let mutant=crate::packed::PackedFile::open(&mutant_path,22).unwrap();
            let family=topology.families.iter().find(|family|family.name==name).unwrap();
            assert!(prove_topology_link(&mutant,&committed,&mut timings,&setup,&commitment,&nph2,&topology,family).is_err(),
                "single-field B1 mutant must fail: {name}");
            drop(mutant);std::fs::remove_file(&mutant_path).unwrap();
        }
        let mut wrong_root=root;wrong_root[0]^=1;
        let wrong_topology=crate::work_tree_wiring::Topology::new(engine.base,3,wrong_root).unwrap();
        let wrong_public_root=wrong_topology.families.iter().find(|family|family.name=="public_root").unwrap();
        assert!(prove_topology_link(&source,&committed,&mut timings,&setup,&commitment,&nph2,&wrong_topology,wrong_public_root).is_err(),
            "single-bit public root statement mutant must fail");

        std::fs::copy(&packed_path,&bad_path).unwrap();let mutant_wire=endpoints.raw[0];let mut file=std::fs::OpenOptions::new().read(true).write(true).open(&bad_path).unwrap();
        file.seek(SeekFrom::Start((mutant_wire/8) as u64)).unwrap();let mut byte=[0];file.read_exact(&mut byte).unwrap();byte[0]^=1<<(mutant_wire%8);
        file.seek(SeekFrom::Start((mutant_wire/8) as u64)).unwrap();file.write_all(&byte).unwrap();file.sync_all().unwrap();drop(file);
        let mutant=crate::packed::PackedFile::open(&bad_path,22).unwrap();assert!(prove_leaf(&boundary,&mutant,&commitment,&mut timings).is_err(),"linked raw-byte mutant must fail local B3 residuals");
        drop(mutant);
        let bad_serializer_path=std::env::temp_dir().join(format!("nipopow-h3-serializer-mutant-{}.bits",std::process::id()));
        std::fs::copy(&packed_path,&bad_serializer_path).unwrap();
        let serializer_wire=WIDTH+crate::header_hash::SERIALIZER_OFFSET+serializer.layout.bytes[0][0];
        let mut file=std::fs::OpenOptions::new().read(true).write(true).open(&bad_serializer_path).unwrap();
        file.seek(SeekFrom::Start((serializer_wire/8) as u64)).unwrap();let mut byte=[0];file.read_exact(&mut byte).unwrap();byte[0]^=1<<(serializer_wire%8);
        file.seek(SeekFrom::Start((serializer_wire/8) as u64)).unwrap();file.write_all(&byte).unwrap();file.sync_all().unwrap();drop(file);
        let serializer_mutant=crate::packed::PackedFile::open(&bad_serializer_path,22).unwrap();
        assert!(prove_serializer(&serializer,&nph2,&commitment,&serializer_mutant,&mut timings,&mut serializer_profile,None).is_err(),"public serializer byte mutant must fail exact NPH2 equalities");
        println!("streamed_h3_phases witness_build_ms={:.3} setup_ms={:.3} commit_ms={:.3} gkr_produce_calls={} gkr_produce_ms={:.3} gkr_leaf_calls={} gkr_leaf_ms={:.3} gkr_serializer_calls={} gkr_serializer_ms={:.3} serializer_baseline_320mib_ms={:.3} serializer_cache_budget_mib={} serializer_cache_candidate_ms={:.3} serializer_baseline_load_calls={} serializer_baseline_load_ms={:.3} serializer_baseline_term_calls={} serializer_baseline_term_ms={:.3} serializer_baseline_coeff_calls={} serializer_baseline_coeff_ms={:.3} serializer_cache_load_calls={} serializer_cache_load_ms={:.3} serializer_cache_term_calls={} serializer_cache_term_ms={:.3} serializer_cache_coeff_calls={} serializer_cache_coeff_ms={:.3} gkr_slot_local_calls={} gkr_slot_local_ms={:.3} gkr_work_link_calls={} gkr_work_link_ms={:.3} gkr_header_alias_calls={} gkr_header_alias_ms={:.3} gkr_topology_link_calls={} gkr_topology_link_ms={:.3} gkr_verify_calls={} gkr_verify_ms={:.3} dory_open_calls={} dory_open_ms={:.3} dory_verify_calls={} dory_verify_ms={:.3} claim_eval_calls={} claim_eval_ms={:.3} witness_write_calls={} witness_write_bytes={} witness_write_ms={:.3} witness_sync_calls={} witness_sync_ms={:.3} commit_read_calls={} commit_read_bytes={} commit_read_ms={:.3} proof_read_calls={} proof_read_bytes={} proof_read_ms={:.3}",
            witness_wall_ns as f64/1_000_000.0,setup_wall_ns as f64/1_000_000.0,commit_wall_ns as f64/1_000_000.0,
            proof_phase_times.gkr_produce.calls,proof_phase_times.gkr_produce.nanos as f64/1_000_000.0,
            proof_phase_times.gkr_leaf_produce.calls,proof_phase_times.gkr_leaf_produce.nanos as f64/1_000_000.0,
            proof_phase_times.gkr_serializer_produce.calls,proof_phase_times.gkr_serializer_produce.nanos as f64/1_000_000.0,
            serializer_baseline_wall_ns as f64/1_000_000.0,crate::sparse_stream_roster::MAX_INCREMENTAL_CACHE_STATE_BYTES/(1024*1024),
            serializer_cache_wall_ns as f64/1_000_000.0,
            serializer_profile.load_copy.calls,serializer_profile.load_copy.nanos as f64/1_000_000.0,
            serializer_profile.term_visit.calls,serializer_profile.term_visit.nanos as f64/1_000_000.0,
            serializer_profile.coefficient_eval.calls.get(),serializer_profile.coefficient_eval.nanos.get() as f64/1_000_000.0,
            serializer_cache_profile.load_copy.calls,serializer_cache_profile.load_copy.nanos as f64/1_000_000.0,
            serializer_cache_profile.term_visit.calls,serializer_cache_profile.term_visit.nanos as f64/1_000_000.0,
            serializer_cache_profile.coefficient_eval.calls.get(),serializer_cache_profile.coefficient_eval.nanos.get() as f64/1_000_000.0,
            proof_phase_times.gkr_slot_local_produce.calls,proof_phase_times.gkr_slot_local_produce.nanos as f64/1_000_000.0,
            proof_phase_times.gkr_work_link_produce.calls,proof_phase_times.gkr_work_link_produce.nanos as f64/1_000_000.0,
            proof_phase_times.gkr_header_alias_produce.calls,proof_phase_times.gkr_header_alias_produce.nanos as f64/1_000_000.0,
            proof_phase_times.gkr_topology_link_produce.calls,proof_phase_times.gkr_topology_link_produce.nanos as f64/1_000_000.0,
            proof_phase_times.gkr_verify.calls,proof_phase_times.gkr_verify.nanos as f64/1_000_000.0,
            proof_phase_times.dory_open.calls,proof_phase_times.dory_open.nanos as f64/1_000_000.0,
            proof_phase_times.dory_verify.calls,proof_phase_times.dory_verify.nanos as f64/1_000_000.0,
            proof_phase_times.claim_evaluation.calls,proof_phase_times.claim_evaluation.nanos as f64/1_000_000.0,
            witness_io.write_calls,witness_io.write_bytes,witness_io.write_ns as f64/1_000_000.0,
            witness_io.sync_calls,witness_io.sync_ns as f64/1_000_000.0,
            commit_io.read_calls,commit_io.read_bytes,commit_io.read_ns as f64/1_000_000.0,
            proof_io.read_calls,proof_io.read_bytes,proof_io.read_ns as f64/1_000_000.0);
        drop(serializer_mutant);drop(source);
        std::fs::remove_file(&bad_serializer_path).unwrap();
        std::fs::remove_file(&bad_path).unwrap();std::fs::remove_file(&packed_path).unwrap();
    }
    #[test] fn work_tree_leaf_hash_native_transitions_and_existing_b1_b2_join() {
        let e=fixed::engine().unwrap();let mut covered=std::collections::BTreeSet::new();
        for headers in [3,5,6,9] {let evidence=tiny_check(e,headers).unwrap();
            covered.extend(evidence.genuine_lengths);assert_eq!(evidence.leaf_core_witnesses,5*evidence.slots);
            assert_eq!(evidence.fixed_core_witnesses,evidence.slots);assert!(evidence.b1_family_rows>0);
            assert!(!evidence.raw_fixture_serializer_attainability);
        }
        assert!(TRANSITIONS.iter().all(|n|covered.contains(n)));
    }
    #[test] fn work_tree_leaf_hash_isolated_valid_core_mutants_and_omissions() {
        let e=fixed::engine().unwrap();let b=compile(e,LeafProfile::new(6,[0;32]).unwrap()).unwrap();
        let mut profile_bytes=b"nipopow-v2/work-profile/v1\0".to_vec();profile_bytes.extend_from_slice(&crate::header_order::MAINNET_GENESIS);let profile=hash(&profile_bytes);
        let cases=[(Mutation::Tag,0,30,"genuine_message_0"),(Mutation::Raw,0,30,"genuine_message_0"),
            (Mutation::LengthBytes,0,30,"genuine_message_0"),(Mutation::Profile,0,30,"genuine_message_0"),
            (Mutation::H,0,30,"genuine_message_0"),(Mutation::Counter,0,30,"genuine_counter_0"),
            (Mutation::Height,0,30,"genuine_message_0"),(Mutation::Lower,0,30,"genuine_message_0"),(Mutation::Upper,0,30,"genuine_message_0"),
            (Mutation::Final,0,30,"genuine_final_0"),(Mutation::ChainLow,0,30,"genuine_state_1"),
            (Mutation::ChainHigh,0,30,"genuine_state_1"),(Mutation::SelectedDigest,0,30,"genuine_digest"),
            (Mutation::LastBlock,0,30,"genuine_length"),(Mutation::NoSelector,0,1,"genuine_last_one_hot"),
            (Mutation::LowerLength,0,0,"genuine_lower_length_bound"),(Mutation::UpperLength,0,515,"genuine_upper_length_bound"),
            (Mutation::DummyReactivated,0,1,"genuine_counter_4"),(Mutation::PaddingPosition,5,1,"padding_message_0"),
            (Mutation::Profile,5,1,"padding_message_0"),(Mutation::H,5,1,"padding_message_0"),
            (Mutation::SelectedDigest,5,1,"padding_digest"),(Mutation::Counter,5,1,"padding_counter_0")];
        for (mutation,slot,len,family) in cases {
            let mut x=Envelope::sample(slot,len,profile);if mutation==Mutation::UpperLength{x.raw[514]=0;}
            let assigned=assign(e,&b,slot,&x,mutation).unwrap();let omitted=b.family(family).unwrap();
            let bad=failures(&b,slot,&assigned.values,None).unwrap();assert!(!bad.is_empty(),"{mutation:?}");
            assert!(bad.iter().all(|r|omitted.contains(r)),"{mutation:?}: {bad:?}");
            assert!(failures(&b,slot,&assigned.values,Some(omitted)).unwrap().is_empty(),"{mutation:?} omission");
        }
        let dummy=compile(e,LeafProfile::new(3,[0;32]).unwrap()).unwrap();let x=Envelope::sample(2,1,profile);
        let assigned=assign(e,&dummy,2,&x,Mutation::DummyReactivated).unwrap();let omitted=dummy.family("dummy_counter_4").unwrap();
        let bad=failures(&dummy,2,&assigned.values,None).unwrap();assert!(!bad.is_empty());assert!(bad.iter().all(|r|omitted.contains(r)));
        assert!(failures(&dummy,2,&assigned.values,Some(omitted)).unwrap().is_empty());
        let mut unchanged_core=assign(e,&b,0,&Envelope::sample(0,30,profile),Mutation::None).unwrap();
        // Value-preserving remainder mutation: +2 at bit0 and -1 at bit1.
        unchanged_core.values.insert(remainder(0),Fr::from(2u64));unchanged_core.values.insert(remainder(1),-Fr::one());
        let omitted=b.family("genuine_auxiliary").unwrap();let bad=failures(&b,0,&unchanged_core.values,None).unwrap();
        assert!(!bad.is_empty());assert!(bad.iter().all(|r|omitted.contains(r)));
        assert!(failures(&b,0,&unchanged_core.values,Some(omitted)).unwrap().is_empty());
    }
    #[test] fn work_tree_leaf_hash_auxiliary_boolean_and_length_exhaustion() {
        let e=fixed::engine().unwrap();let b=compile(e,LeafProfile::new(3,[0;32]).unwrap()).unwrap();let ep=&e.base.endpoints;
        for len in 1..=514 {let last=(len+98)/128;let d=(len+98)%128;let mut values=BTreeMap::new();put_numeric(&mut values,&ep.length,len as u64);
            values.insert(selector(last),Fr::one());for bit in 0..7{
                values.insert(remainder(bit),Fr::from(((d>>bit)&1) as u64));
                values.insert(low_slack(bit),Fr::from(((if last==0 {d-99}else {0}>>bit)&1) as u64));
                values.insert(high_slack(bit),Fr::from(((if last==4 {100-d}else {0}>>bit)&1) as u64));
            }
            let mut rows=[Fr::zero();64];for t in &b.terms {if matches!(t.mask,Mask::Genuine)&&t.term.row<64{rows[t.term.row]+=evaluate(&t.term,&values);}}
            assert!(rows.iter().all(|x|x.is_zero()),"length{len}");
        }
        // Auxiliary-only falsifier: fractional one-hot selectors satisfy the linear
        // length and slack equations, but must fail their Booleanity rows.
        let mut fractional=BTreeMap::new();put_numeric(&mut fractional,&ep.length,2);
        fractional.insert(selector(0),Fr::one()-Fr::one()/Fr::from(128u64));fractional.insert(selector(1),Fr::one()/Fr::from(128u64));
        for bit in 0..7{fractional.insert(remainder(bit),Fr::from(((99u64>>bit)&1) as u64));}
        let mut rows=[Fr::zero();64];for t in &b.terms {if matches!(t.mask,Mask::Genuine)&&t.term.row<64{rows[t.term.row]+=evaluate(&t.term,&fractional);}}
        let boolean=b.family("genuine_auxiliary").unwrap();assert!(rows.iter().any(|x|!x.is_zero()));
        assert!(rows.iter().enumerate().all(|(row,x)|boolean.contains(&row)||x.is_zero()));
        let p=b.profile.clone();let mut changed=p.clone();changed.aux_start+=1;assert!(changed.validate().is_err());
        changed=p.clone();changed.cores[4]=917504;assert!(changed.validate().is_err());
        changed=p;changed.lower_upper_encoding="byte-order unspecified".into();assert!(changed.validate().is_err());
    }
    #[test] fn work_tree_leaf_hash_dyadic_masks_zero_factors_and_historical_no_enumeration() {
        for h in [3,5,6,9] {let p=LeafProfile::new(h,[0;32]).unwrap();let log=p.tree.slot_log();
            for seed in [0u64,1,7] {let r=vec![Fr::from(seed);log];let u=vec![Fr::from(seed+1);log];let v=vec![Fr::from(seed+3);log];let analytic=masks(&p,&r,&u,&v);
                for index in 0..35 {let mask=match index {0=>Mask::Genuine,1=>Mask::Padding,2=>Mask::Dummy,_=>Mask::PaddingBit(index-3)};
                    let direct=(0..p.tree.slots).filter(|&s|selected(&p,mask,s)).map(|s|topology::eq_index(&r,s)*topology::eq_index(&u,s)*topology::eq_index(&v,s)).sum::<Fr>();
                    assert_eq!(analytic[index],direct,"H{h} mask{index}");
                }
            }
        }
        let e=fixed::engine().unwrap();let b=compile(e,LeafProfile::new(1827840,[0;32]).unwrap()).unwrap();let h=b.profile.tree.slot_log();
        assert!(coefficients(&b,&vec![Fr::from(3u64);14+h],&vec![Fr::from(11u64);20+h],&vec![Fr::from(17u64);20+h]).is_ok());
    }
    #[test] fn work_tree_leaf_hash_checked_old_anchors_and_upstream_tail_omission_boundary() {
        let e=fixed::engine().unwrap();let inventory=replacement_inventory(e).unwrap();
        assert_eq!(inventory["new_auxiliary_zero_anchors"]["rows"],AUX_BITS);assert_eq!(inventory["serializer_zero_tail"]["matched_output_byte_rows"],514);
        let b=compile(e,LeafProfile::new(3,[0;32]).unwrap()).unwrap();let x=Envelope::sample(0,1,[0x27;32]);
        let assigned=assign(e,&b,0,&x,Mutation::RawTailSourceOmitted).unwrap();
        assert!(failures(&b,0,&assigned.values,None).unwrap().is_empty());assert_ne!(assigned.digest,assigned.native);
        // Replay the actual inventoried producer row, with its comparator output
        // live=0 because byte1>=length1. This does not assert a valid serializer witness.
        let source=crate::serializer::build(None).unwrap();let row=inventory["serializer_zero_tail"]["row_numbers"][1].as_u64().unwrap() as usize;
        let terms=source.circuit.terms.iter().filter(|t|t.row==row).collect::<Vec<_>>();assert_eq!(terms.len(),8);
        let mut upstream_values=BTreeMap::new();for bit in 0..8 {upstream_values.insert(source.layout.bytes[1][bit],get(&assigned.values,e.base.endpoints.raw[8+bit]));}
        upstream_values.insert(terms[0].gate.right,Fr::zero());
        let upstream=terms.iter().map(|t|evaluate(t,&upstream_values)).sum::<Fr>();
        assert_eq!(upstream,Fr::one());
    }

    #[test] fn retained_mainnet_h3_serializer_to_real_leaves_and_parent_root() {
        std::thread::Builder::new().name("retained-h3-join".into()).stack_size(32*1024*1024)
            .spawn(||retained_mainnet_h3_join_inner(None)).unwrap().join().unwrap();
    }
    #[test] fn retained_mainnet_h4_serializer_to_real_leaves_and_parent_root() {
        std::thread::Builder::new().name("retained-h4-join".into()).stack_size(32*1024*1024)
            .spawn(||retained_mainnet_header_join_inner(None,4)).unwrap().join().unwrap();
    }
    #[test] fn retained_mainnet_h4_rebuilt_difficulty_isolates_genesis_and_each_inheritance_edge() {
        std::thread::Builder::new().name("retained-h4-daa-mutants".into()).stack_size(32*1024*1024)
            .spawn(||for mutation in 1..=3 {retained_mainnet_header_join_case(None,4,mutation);})
            .unwrap().join().unwrap();
    }
    #[test]
    #[ignore = "requires the exact three-header Mainnet export from ErgoHistory"]
    fn ergo_history_mainnet_h3_export_to_real_leaves_and_parent_root() {
        use std::{env,path::PathBuf};
        let path=PathBuf::from(env::var_os("NIPOPOW_V2_HEADER_EXPORT_PATH")
            .expect("set path to the Scala Mainnet ErgoHistory export"));
        std::thread::Builder::new().name("ergo-history-h3-join".into()).stack_size(32*1024*1024)
            .spawn(move||retained_mainnet_h3_join_inner(Some(path))).unwrap().join().unwrap();
    }
    fn retained_mainnet_h3_join_inner(export_path:Option<std::path::PathBuf>) {
        retained_mainnet_header_join_inner(export_path,3)
    }
    fn retained_mainnet_header_join_inner(export_path:Option<std::path::PathBuf>,header_count:usize) {
        retained_mainnet_header_join_case(export_path,header_count,0)
    }
    fn retained_mainnet_header_join_case(export_path:Option<std::path::PathBuf>,header_count:usize,daa_mutation:usize) {
        use ergo_header_core::Header;
        use num_bigint::BigUint;

        fn hex(s:&str)->Vec<u8>{s.as_bytes().chunks_exact(2).map(|p|u8::from_str_radix(std::str::from_utf8(p).unwrap(),16).unwrap()).collect()}
        fn output(c:&crate::serializer::Compiled,input:&[Fr])->(Vec<u8>,usize){
            let bytes=c.layout.bytes.iter().map(|byte|byte.iter().enumerate().map(|(bit,w)|
                if input[*w]==Fr::one(){1u8<<bit}else{0}).fold(0u8,|a,b|a|b)).collect();
            let length=c.layout.length.iter().enumerate().map(|(bit,w)|if input[*w]==Fr::one(){1usize<<bit}else{0}).sum();(bytes,length)
        }
        fn residuals(c:&crate::sparse::Circuit,input:&[Fr])->Vec<Fr>{
            let mut rows=vec![Fr::zero();c.row_count];for t in &c.terms{rows[t.row]+=t.gate.evaluate(input);}rows
        }
        fn set_uint(values:&mut BTreeMap<usize,Fr>,wires:&[usize],n:&BigUint){
            for (bit,&wire) in wires.iter().enumerate(){values.insert(wire,Fr::from(n.bit(bit as u64) as u64));}
        }
        fn read_packed_slot(source:&crate::packed::PackedFile,width:usize,slot:usize)->Result<Vec<Fr>,String>{
            const CHUNK:usize=1<<16;
            if width<CHUNK||!width.is_power_of_two()||width%CHUNK!=0||source.input_len()%width!=0
                ||slot>=source.input_len()/width{return Err("packed slot shape invalid".into());}
            let first=slot.checked_mul(width).ok_or("packed slot offset overflow")?/CHUNK;
            let mut values=Vec::with_capacity(width);
            for chunk in 0..width/CHUNK{values.extend(source.read_copy(CHUNK,first+chunk)?);}
            Ok(values)
        }
        fn put_digest(values:&mut BTreeMap<usize,Fr>,slot:usize,wires:&[usize],digest:&[u8;32]){
            for (i,byte) in digest.iter().enumerate(){for bit in 0..8{values.insert(slot*WIDTH+wires[i*8+bit],Fr::from(((byte>>bit)&1) as u64));}}
        }

        assert!(matches!(header_count,3|4));
        let mut nph2=if let Some(path)=export_path {
            std::fs::read(path).unwrap()
        } else {
            let pack:serde_json::Value=serde_json::from_str(include_str!("../vendor/header-core/fixtures/governance-contiguous-header-packs-v1.json")).unwrap();
            let raws=pack["networks"]["mainnet"]["source_headers_hex"].as_array().unwrap().iter().take(header_count)
                .map(|item|hex(item.as_str().unwrap())).collect::<Vec<_>>();
            let mut frame=b"NPH2".to_vec();frame.extend_from_slice(&(header_count as u32).to_be_bytes());
            for raw in raws {frame.extend_from_slice(&(raw.len() as u32).to_be_bytes());frame.extend_from_slice(&raw);}
            frame
        };
        if daa_mutation!=0 {
            assert_eq!(header_count,4);
            let source=crate::nph2_header_source::MainnetH4Input::decode_nph2(&nph2).unwrap();
            let mut rebuilt=source.headers().iter().map(|header|
                Header::decode(header.raw_bytes(),None).unwrap()).collect::<Vec<_>>();
            let first_changed=match daa_mutation {1=>3,2=>2,3=>1,_=>panic!("unknown DAA mutant")};
            for slot in first_changed..4 {
                assert_eq!(rebuilt[slot].n_bits,0x06011765);
                rebuilt[slot].n_bits^=1;
                rebuilt[slot].parent_id=Blake2b::<U32>::digest(rebuilt[slot-1].encode().unwrap()).into();
            }
            nph2=b"NPH2".to_vec();nph2.extend_from_slice(&4u32.to_be_bytes());
            for header in rebuilt {let raw=header.encode().unwrap();
                nph2.extend_from_slice(&(raw.len() as u32).to_be_bytes());nph2.extend_from_slice(&raw);}
        }
        let retained:Vec<Vec<u8>>=match header_count {
            3=>crate::nph2_header_source::MainnetH3Input::decode_nph2(&nph2).unwrap().headers()
                .iter().map(|header|header.raw_bytes().to_vec()).collect(),
            4=>crate::nph2_header_source::MainnetH4Input::decode_nph2(&nph2).unwrap().headers()
                .iter().map(|header|header.raw_bytes().to_vec()).collect(),
            _=>unreachable!(),
        };
        assert_eq!(retained.len(),header_count);
        let mut decoded:Vec<(Vec<u8>,Header)>=Vec::new();
        for (index,raw) in retained.into_iter().enumerate(){
            let header=Header::decode(&raw,None).unwrap();
            assert_eq!(header.height,index as u32+1);assert_eq!(header.encode().unwrap(),raw);
            if index>0 {let parent=Blake2b::<U32>::digest(&decoded[index-1].0);assert_eq!(header.parent_id.as_slice(),parent.as_slice());}
            decoded.push((raw,header));
        }
        assert_eq!(decoded[0].1.parent_id,[0;32]);
        assert_eq!(Blake2b::<U32>::digest(&decoded[0].0).as_slice(),crate::header_order::MAINNET_GENESIS);

        let serializer=crate::serializer::build(None).unwrap();
        let e=fixed::engine().unwrap();let leaf_profile=LeafProfile::new(header_count,[0;32]).unwrap();
        let boundary=compile(e,leaf_profile.clone()).unwrap();
        let mut profile_bytes=b"nipopow-v2/work-profile/v1\0".to_vec();profile_bytes.extend_from_slice(&crate::header_order::MAINNET_GENESIS);
        let profile=hash(&profile_bytes);let base=&e.base;let ep=&base.endpoints;
        let mut global=BTreeMap::new();let mut leaves=Vec::new();let mut work_cases=Vec::new();let mut lower=BigUint::from(0u8);
        for slot in 0..header_count-1 {
            let (raw,header)=&decoded[slot+1];let f=crate::serializer::Fields::from_header(header).unwrap();let serialized=serializer.assign(&f);
            assert!(serialized.iter().all(|x|x.is_zero()||x.is_one()));
            assert!(residuals(&serializer.circuit,&serialized).iter().all(|x|x.is_zero()),"serializer residual slot{slot}");
            let (bytes,length)=output(&serializer,&serialized);assert_eq!(length,raw.len());assert_eq!(&bytes[..length],raw.as_slice());
            assert!(bytes[length..].iter().all(|x|*x==0));
            let nbits=crate::work_tree_work::native_decode(header.n_bits).unwrap();assert!(!nbits.is_zero());
            let upper=&lower+&nbits;assert!(upper.bits()<=224);
            work_cases.push((header.n_bits,lower.clone(),nbits.clone(),upper.clone()));
            let be28=|n:&BigUint|{let mut out=[0u8;28];let b=n.to_bytes_be();out[28-b.len()..].copy_from_slice(&b);out};
            let mut assigned=assign_header_leaf(e,&boundary,slot,header,be28(&lower),be28(&upper),profile).unwrap();
            assert!(failures(&boundary,slot,&assigned.values,None).unwrap().is_empty(),"B3 residual slot{slot}");
            for (wire,source) in ep.n_bits.iter().zip(&serializer.layout.fields.n_bits){
                assigned.values.insert(*wire,serialized[*source]);
            }
            for (wire,source) in ep.height.iter().zip(&serializer.layout.fields.height){assert_eq!(assigned.values.get(wire).copied().unwrap_or(Fr::zero()),serialized[*source]);}
            for (wire,source) in ep.length.iter().zip(&serializer.layout.length){assert_eq!(assigned.values.get(wire).copied().unwrap_or(Fr::zero()),serialized[*source]);}
            leaves.push(assigned.digest);
            for (&wire,&value) in &assigned.values {if (layout::ENDPOINT_BASE..layout::ENDPOINT_BASE+layout::ENDPOINT_WIDTH).contains(&wire){global.insert(slot*WIDTH+wire,value);}}
            let aliases=ep.header_aliases();
            for (&source,&target) in base.header_alias_wires.iter().zip(&aliases){
                let serializer_wire=source-524288;let value=serialized[serializer_wire];
                assert_eq!(assigned.values.get(&target).copied().unwrap_or(Fr::zero()),value,"B1 alias slot{slot} wire{target}");
                global.insert((slot+1)*WIDTH+source,value);
            }
            // The serializer is the producer for the aliased raw/length/height coordinates.
            for (i,wire) in ep.raw.iter().enumerate(){let from=serializer.layout.bytes[i/8][i%8];assert_eq!(assigned.values.get(wire).copied().unwrap_or(Fr::zero()),serialized[from]);}
            for (&wire,&value) in &assigned.values {
                let global_wire=slot*WIDTH+wire;
                if let Some(previous)=global.insert(global_wire,value){assert_eq!(previous,value,"B3 witness merge slot{slot} wire{wire}");}
            }
            lower=upper;
        }

        // Fill the B3 padding/dummy-role core and auxiliary witnesses; these
        // occupy released core banks and are independent of header cores 0..4.
        for slot in header_count-1..leaf_profile.tree.slots {
            let envelope=Envelope::sample(slot,100,profile);
            let assigned=assign(e,&boundary,slot,&envelope,Mutation::None).unwrap();
            assert!(failures(&boundary,slot,&assigned.values,None).unwrap().is_empty());
            if leaf_profile.role(slot).unwrap()==Role::Padding {leaves.push(assigned.digest);}
            for (&wire,&value) in &assigned.values {global.insert(slot*WIDTH+wire,value);}
        }

        // Preserve the old header's still-live witness while allowing B1/B2/B3
        // to replace the retired core, auxiliary, and endpoint zero anchors.
        let mut released_ranges=CORES.iter().chain(std::iter::once(&fixed::NODE_CORE))
            .map(|start|*start..*start+CORE).collect::<Vec<_>>();
        released_ranges.push(AUX..AUX+AUX_BITS);
        released_ranges.push(layout::ENDPOINT_BASE..layout::ENDPOINT_BASE+layout::ENDPOINT_WIDTH);
        for slot in 0..leaf_profile.tree.slots {
            let header_index=slot.min(header_count-1);let (_raw,header)=&decoded[header_index];
            let f=crate::serializer::Fields::from_header(header).unwrap();
            let mut joined=crate::header_compact_links::build(Some(&f)).unwrap();
            let (previous_height,previous_time,first)=if header_index==0 {
                (0,0,true)
            } else {
                let previous=&decoded[header_index-1].1;
                (previous.height,previous.timestamp,false)
            };
            crate::header_compact_links::assign_order(&mut joined,&f,previous_height,previous_time,first).unwrap();
            let input=joined.base.base.base.input.as_ref().unwrap();
            assert!(residuals(&joined.base.base.base.boundary,input).iter().all(|value|value.is_zero()),"standalone adapted header boundary slot{slot}");
            for (wire,value) in input.into_iter().enumerate() {
                if released_ranges.iter().any(|range|range.contains(&wire)){continue;}
                let global_wire=slot*WIDTH+wire;
                if let Some(previous)=global.get(&global_wire){assert_eq!(*previous,*value,"header witness merge slot{slot} wire{wire}");}
                if !value.is_zero(){global.insert(global_wire,*value);}
            }
        }

        let fixed_profile=fixed::FixedProfile::new(header_count,[0;32]).unwrap();
        let root=if header_count==3 {
            let profile_hash=fixed_slot(e,&fixed_profile,1,&profile_bytes,&mut global).unwrap();
            assert_eq!(profile_hash,hash(&profile_bytes));
            put_digest(&mut global,0,&ep.node_left,&leaves[0]);put_digest(&mut global,0,&ep.node_right,&leaves[1]);
            let mut node=b"N\x01\x00\x00\x00\x00".to_vec();node.extend_from_slice(&leaves[0]);node.extend_from_slice(&leaves[1]);
            let root=fixed_slot(e,&fixed_profile,0,&node,&mut global).unwrap();assert_eq!(root,hash(&node));
            for slot in 2..leaf_profile.tree.slots{fixed_slot(e,&fixed_profile,slot,&[],&mut global).unwrap();}
            root
        }else{
            assert_eq!(leaves.len(),leaf_profile.tree.leaves);
            let mut level_digests=leaves.clone();
            for level in 1..=leaf_profile.tree.leaves.trailing_zeros() as usize {
                let (node_base,node_count)=fixed_profile.tree.level(level).unwrap();
                let child_base=if level==1 {0}else {fixed_profile.tree.level(level-1).unwrap().0};
                let mut next=Vec::with_capacity(node_count);
                for position in 0..node_count {
                    let left_index=if level==1 {2*position}else {child_base+2*position};
                    let right_index=left_index+1;
                    let left=level_digests[left_index-child_base];
                    let right=level_digests[right_index-child_base];
                    let slot=node_base+position;
                    put_digest(&mut global,slot,&ep.node_left,&left);
                    put_digest(&mut global,slot,&ep.node_right,&right);
                    let mut node=vec![b'N',level as u8];node.extend_from_slice(&(position as u32).to_be_bytes());
                    node.extend_from_slice(&left);node.extend_from_slice(&right);
                    next.push(fixed_slot(e,&fixed_profile,slot,&node,&mut global).unwrap());
                }
                level_digests=next;
            }
            assert_eq!(level_digests.len(),1);
            let profile_hash=fixed_slot(e,&fixed_profile,fixed_profile.tree.profile_node_slot,&profile_bytes,&mut global).unwrap();
            assert_eq!(profile_hash,hash(&profile_bytes));
            level_digests[0]
        };

        let mut total=[0u8;28];let total_be=lower.to_bytes_be();assert!(total_be.len()<=28);total[28-total_be.len()..].copy_from_slice(&total_be);
        let work_profile=crate::work_tree_work::WorkProfile::new(header_count,root,total).unwrap();
        let work_boundary=crate::work_tree_work::compile(base,work_profile.clone()).unwrap();
        for (slot,(nbits,lo,work,hi)) in work_cases.iter().enumerate(){
            let mut local=BTreeMap::new();set_uint(&mut local,&ep.n_bits,&BigUint::from(*nbits));
            set_uint(&mut local,&ep.lower,lo);set_uint(&mut local,&ep.work,work);set_uint(&mut local,&ep.upper,hi);
            let minus=if work.is_zero(){BigUint::from(0u8)}else{work-BigUint::from(1u8)};
            set_uint(&mut local,&ep.work_minus_one,&minus);local.insert(ep.exponent[(nbits>>24) as usize],Fr::one());
            for (&wire,&value) in &local{
                let global_wire=slot*WIDTH+wire;
                if ep.n_bits.contains(&wire)||ep.lower.contains(&wire)||ep.upper.contains(&wire){
                    assert_eq!(global.get(&global_wire).copied().unwrap_or(Fr::zero()),value,"B4 shared endpoint slot{slot} wire{wire}");
                }
                global.insert(global_wire,value);
            }
        }
        let mut work_rows=BTreeMap::<usize,Fr>::new();
        for slot in 0..work_profile.tree.slots{work_boundary.emit_slot(slot,|t|{
            *work_rows.entry(t.row).or_insert(Fr::zero())+=evaluate(&t,&global);
        }).unwrap();}
        assert!(work_rows.values().all(|x|x.is_zero()),"B4 local interval residual");
        for family in work_boundary.links(){let circuit=family.enumerate(&work_profile.tree,1<<20).unwrap();
            let mut rows=BTreeMap::<usize,Fr>::new();for t in &circuit.terms{*rows.entry(t.row).or_insert(Fr::zero())+=evaluate(t,&global);}
            assert!(rows.values().all(|x|x.is_zero()),"B4 interval link {}",family.name);}

        let topology=topology::Topology::new(base,header_count,root).unwrap();
        for family in &topology.families {let circuit=family.enumerate(&topology.descriptor,1<<20).unwrap();
            for term in &circuit.terms{assert!(evaluate(term,&global).is_zero(),"B1 family {} row{}",family.name,term.row);}}

        let previous_composed=if header_count==3 {crate::work_tree_composition::h3(root,total).unwrap()}
            else {crate::work_tree_composition::h4(root,total).unwrap()};
        let composed=if header_count==4 {crate::work_tree_composition::h4_early_daa(root,total).unwrap()}
            else {previous_composed.clone()};
        let mut witness=vec![Fr::zero();composed.circuit.input_len];
        for (&wire,&value) in &global {witness[wire]=value;}
        let mut rows=vec![Fr::zero();composed.circuit.row_count];
        for term in &composed.circuit.terms {rows[term.row]+=term.gate.evaluate(&witness);}
        let failed=rows.iter().enumerate().filter_map(|(row,value)|(!value.is_zero()).then_some((row,*value))).collect::<Vec<_>>();
        if daa_mutation!=0 {
            let group=match daa_mutation {1=>2,2=>1,3=>0,_=>unreachable!()};
            let expected_row=previous_composed.reserved_rows+group*224+24;
            assert_eq!(failed.iter().map(|(row,_)|*row).collect::<Vec<_>>(),vec![expected_row],
                "rebuilt DAA mutant must fail exactly its selected obligation");
            assert!(rows[..previous_composed.reserved_rows].iter().all(|value|value.is_zero()),
                "all previous tree/header/work constraints must stay satisfied");
            let joined=crate::header_compact_links::build(None).unwrap();
            for slot in 0..4 {
                let slot_input=&witness[slot*WIDTH..(slot+1)*WIDTH];
                for (relation,offset) in [
                    (&joined.base.base.base.serializer.circuit,crate::header_hash::SERIALIZER_OFFSET),
                    (&joined.base.base.points.circuit,crate::segment_points::POINT_OFFSET),
                    (&joined.base.order.circuit,crate::header_order::ORDER_OFFSET)] {
                    assert!(residuals(relation,&slot_input[offset..offset+relation.input_len])
                        .iter().all(|value|value.is_zero()),"rebuilt local relation slot{slot}");
                }
            }
            let tip=ergo_header_core::blake2b256(&decoded[3].0);
            let hash_link=crate::segment_adjacency::Relation::new(4,joined.base.base.base.parent_wires,
                joined.base.base.base.digest_wires,[0;32],tip).unwrap();
            assert!(hash_link.residuals(&witness).unwrap().iter().all(|value|value.is_zero()));
            assert!(crate::header_order::metadata_relation(4,decoded[3].1.timestamp).unwrap()
                .residuals(&witness).unwrap().iter().all(|value|value.is_zero()));
            let analytic=crate::h4_analytic::Plan::new(root,total).unwrap();
            let tagged=analytic.tree_circuit().unwrap();
            let tagged_rows=residuals(&tagged,&witness);
            let tagged_failed=tagged_rows.iter().enumerate().filter_map(|(row,value)|
                (!value.is_zero()).then_some(row)).collect::<Vec<_>>();
            assert_eq!(tagged_failed,vec![((20+group)<<16)+24],"DAA obligation moved to wrong v3 tag");
            println!("h4_rebuilt_daa_mutant kind={daa_mutation} old_structure=pass local_relations=pass adjacencies=pass failed_row={expected_row} result=rejected");
            return;
        }
        let details=failed.iter().take(12).map(|(row,residual)| {
            let gates=composed.circuit.terms.iter().filter(|t|t.row==*row).take(8).map(|t| {
                let g=&t.gate;(g.left,g.right,g.c0,g.c1,g.c2,g.c3,witness[g.left],witness[g.right])
            }).collect::<Vec<_>>();(*row,*residual,gates)
        }).collect::<Vec<_>>();
        assert!(failed.is_empty(),"composed Mainnet H{header_count} first residuals {details:?}");
        drop(rows);
        if header_count==4 {
            let link_wire=WIDTH+ep.node_left[0];
            let changed_value=Fr::one()-witness[link_wire];
            let mut affected_rows=std::collections::BTreeSet::new();
            for term in &composed.circuit.terms {
                if term.gate.left==link_wire||term.gate.right==link_wire {affected_rows.insert(term.row);}
            }
            assert!(!affected_rows.is_empty(),"H4 B2 child link has no composed rows");
            let mut link_residuals=BTreeMap::<usize,Fr>::new();
            for term in &composed.circuit.terms {
                if !affected_rows.contains(&term.row) {continue;}
                let gate=&term.gate;
                let left=if gate.left==link_wire {changed_value}else {witness[gate.left]};
                let right=if gate.right==link_wire {changed_value}else {witness[gate.right]};
                *link_residuals.entry(term.row).or_insert(Fr::zero())+=
                    gate.c0+gate.c1*left+gate.c2*right+gate.c3*left*right;
            }
            assert!(link_residuals.values().any(|value|!value.is_zero()),
                "H4 composed relation accepted a changed B2 child link");
        }
        drop(global);
        let setup_started=std::time::Instant::now();
        let setup=crate::pcs::generate_setup(22).unwrap();
        let setup_ms=setup_started.elapsed().as_millis();
        assert!(witness.iter().all(|x|x.is_zero()||x.is_one()),"packed GKR witness must be Boolean");
        let nonce=std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
        let packed_path=std::env::temp_dir().join(format!("nipopow-v2-composed-h{header_count}-witness-{}-{nonce}.bits",std::process::id()));
        let mut packed_bytes=vec![0u8;witness.len().div_ceil(8)];
        for (index,value) in witness.iter().enumerate(){if value.is_one(){packed_bytes[index/8]|=1<<(index%8);}}
        let mut packed_file=std::fs::OpenOptions::new().write(true).create_new(true).open(&packed_path).unwrap();
        std::io::Write::write_all(&mut packed_file,&packed_bytes).unwrap();drop(packed_file);drop(packed_bytes);
        let source=crate::packed::PackedFile::open(&packed_path,22).unwrap();
        let commitment_started=std::time::Instant::now();
        let committed=crate::packed::commit(&source,&setup).unwrap();
        let commitment_bytes=crate::pcs::encode_commitment(&committed.commitment).unwrap();
        let commitment_ms=commitment_started.elapsed().as_millis();
        let h4_expected=if header_count==4 {
            Some(crate::h4_packet::ExpectedStatement::new(root,total,
                ergo_header_core::blake2b256(&decoded[3].0),decoded[3].1.timestamp,&committed.commitment).unwrap())
        }else{None};
        let (core_domain,core_profile):(&[u8],&[u8])=if header_count==3 {
            (b"nipopow-v2-h3-core-gkr-measurement-v1",b"h3-composed-seven-core-roster-v1")
        }else{(b"nipopow-v2-h4-core-gkr-measurement-v1",b"h4-composed-seven-core-roster-v1")};
        let init_core_transcript=|index:usize,start:usize,copies:usize|{
            if let Some(expected)=&h4_expected {return crate::h4_packet::core_transcript(expected,index).unwrap();}
            let mut t=crate::transcript::Transcript::new(core_domain);
            t.append_bytes(b"profile",core_profile);
            t.append_bytes(b"root",&root);t.append_bytes(b"total-work-be28",&total);
            t.append_bytes(b"setup-id",&setup.id);t.append_bytes(b"input-commitment",&commitment_bytes);
            t.append_u64(b"core-claim-index",index as u64);t.append_u64(b"bank-start",start as u64);
            t.append_u64(b"repeated-core-copies",copies as u64);t
        };
        let engine=fixed::engine().unwrap();
        let mut core_claims=Vec::with_capacity(7);let mut core_proof_bytes=Vec::with_capacity(7);
        let mut core_packets=Vec::with_capacity(7);
        for slot in 0..leaf_profile.tree.slots {
            let input=witness[slot*WIDTH..slot*WIDTH+8*CORE].to_vec();
            let mut prover=init_core_transcript(slot,0,8);
            let (proof,claim)=crate::sparse::prove(&engine.core,&input,3,&mut prover).unwrap();
            let bytes=crate::gkr::encode_proof(&proof).unwrap();
            let decoded=crate::sparse::decode_proof(&engine.core,3,&bytes).unwrap();
            let mut verifier=init_core_transcript(slot,0,8);
            let checked=crate::sparse::verify(&engine.core,3,&decoded,&mut verifier).unwrap();
            assert_eq!(checked,claim,"legacy core slot {slot}");
            let mut point=checked.point.clone();
            point.push(Fr::zero()); // the upper half of each 1 MiB slot is fixed out
            point.extend((0..2).map(|bit|Fr::from(((slot>>bit)&1) as u64)));
            assert_eq!(point.len(),22);
            core_claims.push(crate::opening_batch::Claim{point,value:checked.value});
            core_proof_bytes.push(bytes.len());
            core_packets.push(bytes);
        }
        for (j,start) in [720896usize,851968, fixed::NODE_CORE].into_iter().enumerate() {
            let input=(0..leaf_profile.tree.slots).flat_map(|slot|
                witness[slot*WIDTH+start..slot*WIDTH+start+CORE].iter().copied()).collect::<Vec<_>>();
            let index=leaf_profile.tree.slots+j;
            let mut prover=init_core_transcript(index,start,leaf_profile.tree.slots);
            let (proof,claim)=crate::sparse::prove(&engine.core,&input,2,&mut prover).unwrap();
            let bytes=crate::gkr::encode_proof(&proof).unwrap();
            let decoded=crate::sparse::decode_proof(&engine.core,2,&bytes).unwrap();
            let mut verifier=init_core_transcript(index,start,leaf_profile.tree.slots);
            let checked=crate::sparse::verify(&engine.core,2,&decoded,&mut verifier).unwrap();
            assert_eq!(checked,claim,"tree core bank {start}");
            let point=layout::embed_bank(start,CORE,2,&checked.point).unwrap();
            core_claims.push(crate::opening_batch::Claim{point,value:checked.value});
            core_proof_bytes.push(bytes.len());
            core_packets.push(bytes);
        }
        let claims:[crate::opening_batch::Claim;crate::opening_batch::CLAIMS]=core_claims.try_into().unwrap();
        let batch_statement=if header_count==4 {
            crate::h4_packet::core_batch_statement(h4_expected.as_ref().unwrap(),&claims).unwrap()
        }else {
            let mut corpus=b"nipopow-v2/h3-mainnet-roster/v1\0".to_vec();
            corpus.extend_from_slice(&root);corpus.extend_from_slice(&total);
            crate::opening_batch::Statement{log_n:22,setup_id:setup.id,
                commitment:committed.commitment,corpus_id:Some(hash(&corpus)),claims}
        };
        let batch_started=std::time::Instant::now();
        let (batch_proof,batch_metrics,batch_prover_transcript)=crate::opening_batch::prove(&source,&committed,&setup,&batch_statement).unwrap();
        let batch_bytes=crate::opening_batch::encode_proof(&batch_proof,22).unwrap();
        let decoded_batch=crate::opening_batch::decode_proof(&batch_bytes,22).unwrap();
        let verifier_key=crate::verifier_key::admit(22,include_bytes!("../fixtures/verifier-keys-v1/log22.vk")).unwrap();
        let batch_verifier_transcript=crate::opening_batch::verify_admitted(&batch_statement,&verifier_key,&decoded_batch).unwrap();
        let transcript_ledger=|t:&crate::transcript::Transcript|(t.challenges(),t.raw_queries(),t.bytes_absorbed());
        assert_eq!(transcript_ledger(&batch_prover_transcript),transcript_ledger(&batch_verifier_transcript));
        let mut batch_prover_next=batch_prover_transcript.clone();let mut batch_verifier_next=batch_verifier_transcript.clone();
        assert_eq!(batch_prover_next.try_challenge_scalar(b"continuation").unwrap(),
            batch_verifier_next.try_challenge_scalar(b"continuation").unwrap());
        let mut wrong_statement=batch_statement.clone();wrong_statement.setup_id[0]^=1;
        assert!(crate::opening_batch::verify_admitted(&wrong_statement,&verifier_key,&decoded_batch).err().unwrap()
            .contains("verifier-key/dimension"));
        let mut wrong_statement=batch_statement.clone();wrong_statement.claims[0].point.pop();
        assert!(crate::opening_batch::verify_admitted(&wrong_statement,&verifier_key,&decoded_batch).err().unwrap()
            .contains("dimension rejected"));
        let mut wrong_statement=batch_statement.clone();wrong_statement.claims[0].value+=Fr::from(1u64);
        assert!(crate::opening_batch::verify_admitted(&wrong_statement,&verifier_key,&decoded_batch).err().unwrap()
            .contains("round sum rejected"));
        let batch_ms=batch_started.elapsed().as_millis();
        let (boundary_domain,boundary_profile):(&[u8],&[u8])=if header_count==3 {
            (b"nipopow-v2-composed-h3-gkr-dory-measurement-v1",b"h3-composed-boundary-mainnet-v1")
        }else{(b"nipopow-v2-composed-h4-gkr-dory-measurement-v1",b"h4-composed-boundary-mainnet-v1")};
        let init_transcript=||{
            if let Some(expected)=&h4_expected {return crate::h4_packet::boundary_transcript(expected).unwrap();}
            let mut t=crate::transcript::Transcript::new(boundary_domain);
            t.append_bytes(b"profile",boundary_profile);
            t.append_bytes(b"root",&root);t.append_bytes(b"total-work-be28",&total);
            t.append_bytes(b"setup-id",&setup.id);t.append_bytes(b"input-commitment",&commitment_bytes);t
        };
        let analytic=if header_count==4 {Some(crate::h4_analytic::Plan::new(root,total).unwrap())}else {None};
        let gkr_started=std::time::Instant::now();
        let mut prover_transcript=init_transcript();
        let (proof,claim)=if let Some(plan)=&analytic {plan.prove_headers(&witness,&mut prover_transcript).unwrap()}
            else {crate::sparse::prove(&composed.circuit,&witness,0,&mut prover_transcript).unwrap()};
        let proof_bytes=crate::gkr::encode_proof(&proof).unwrap();
        let gkr_ms=gkr_started.elapsed().as_millis();
        let decoded_gkr=if let Some(plan)=&analytic {plan.decode(&proof_bytes).unwrap()}
            else {crate::sparse::decode_proof(&composed.circuit,0,&proof_bytes).unwrap()};
        let mut verifier_transcript=init_transcript();
        let verified=if let Some(plan)=&analytic {plan.verify_headers(&decoded_gkr,&mut verifier_transcript).unwrap()}
            else {crate::sparse::verify(&composed.circuit,0,&decoded_gkr,&mut verifier_transcript).unwrap()};
        assert_eq!(verified,claim);
        assert_eq!(verified.value,crate::gkr::mle(&witness,&verified.point).unwrap());

        // H4's padded fourth leaf and all three internal B2 nodes are covered
        // by the tree relation. The seven required relation claims below are
        // opened together against this same packed commitment.
        if header_count==4 {
            use crate::{header_compact_links,header_order,segment_points,segment_relation};

            let mut relation_claims=Vec::with_capacity(7);
            assert_eq!(verified.point.len(),22);
            assert_eq!(source.evaluate(&verified.point).unwrap(),verified.value,
                "retained header claim must open in the common commitment");
            relation_claims.push(crate::opening_batch::Claim{point:verified.point.clone(),value:verified.value});
            let mut relation_gkr_bytes=proof_bytes.len();
            let mut semantic_packets=vec![proof_bytes.clone()];
            let roster_transcript=|role:&[u8]|{
                if let Some(index)=crate::h4_packet::SEMANTIC_ROLES.iter().position(|candidate|*candidate==role) {
                    return crate::h4_packet::semantic_transcript(h4_expected.as_ref().unwrap(),index).unwrap();
                }
                let mut t=crate::transcript::Transcript::new(b"nipopow-v2-h4-complete-header-relations-v1");
                t.append_bytes(b"roster-profile",b"mainnet-h4-header-and-tree-relations-v1");
                t.append_bytes(b"relation-role",role);t.append_u64(b"header-count",4);
                t.append_bytes(b"tree-root",&root);t.append_bytes(b"total-work-be28",&total);
                t.append_bytes(b"setup-id",&setup.id);t.append_bytes(b"input-commitment",&commitment_bytes);t
            };
            let plan=analytic.as_ref().unwrap();
            let tree_started=std::time::Instant::now();
            let mut tree_prover=roster_transcript(b"work-tree-early-daa");
            let (tree_proof,tree_claim)=plan.prove_tree(&witness,&mut tree_prover).unwrap();
            let tree_bytes=crate::gkr::encode_proof(&tree_proof).unwrap();
            let tree_decoded=plan.decode(&tree_bytes).unwrap();
            let mut tree_verifier=roster_transcript(b"work-tree-early-daa");
            let checked_tree=plan.verify_tree(&tree_decoded,&mut tree_verifier).unwrap();
            assert_eq!(checked_tree,tree_claim);
            for mutation in 0..3 {
                let mut bad_tree_verifier=roster_transcript(b"work-tree-early-daa");
                assert!(plan.verify_tree_mutant(&tree_decoded,&mut bad_tree_verifier,mutation)
                    .unwrap_err().contains("TerminalExpression"),"wiring mutant {mutation}");
            }
            assert_eq!(source.evaluate(&checked_tree.point).unwrap(),checked_tree.value);
            relation_claims.push(crate::opening_batch::Claim{point:checked_tree.point,value:checked_tree.value});
            relation_gkr_bytes+=tree_bytes.len();semantic_packets.push(tree_bytes);
            let tree_gkr_ms=tree_started.elapsed().as_millis();
            let header_relations=header_compact_links::build(None).unwrap();
            let serializer_relation=&header_relations.base.base.base.serializer.circuit;
            let point_relation=&header_relations.base.base.points.circuit;
            let order_relation=&header_relations.base.order.circuit;
            assert_eq!((serializer_relation.input_len,serializer_relation.row_count,serializer_relation.terms.len()),
                (131072,262144,315546));
            assert_eq!((point_relation.input_len,point_relation.row_count,point_relation.terms.len()),
                (8192,16384,288158));
            assert_eq!((order_relation.input_len,order_relation.row_count,order_relation.terms.len()),
                (1024,2048,2081));

            let gather_stage=|stage:usize,load:fn(&crate::packed::PackedFile,usize,usize,usize)->Result<Vec<Fr>,String>|{
                let mut input=Vec::new();
                for slot in 0..4 {input.extend(load(&source,stage,4,slot).unwrap());}
                input
            };
            let mut semantic_gkr_ms=tree_gkr_ms;
            let mut add_local_relation=|role:&[u8],stage:usize,circuit:&crate::sparse::Circuit,input:Vec<Fr>,
                embed:fn(usize,usize,&[Fr])->Result<Vec<Fr>,String>|{
                let started=std::time::Instant::now();
                let mut prover=roster_transcript(role);
                let (proof,claim)=crate::sparse::prove(circuit,&input,2,&mut prover).unwrap();
                let bytes=crate::gkr::encode_proof(&proof).unwrap();
                let decoded=crate::sparse::decode_proof(circuit,2,&bytes).unwrap();
                let mut verifier=roster_transcript(role);
                let checked=crate::sparse::verify(circuit,2,&decoded,&mut verifier).unwrap();
                assert_eq!(checked,claim,"repeated local relation {role:?}");
                let point=embed(stage,2,&checked.point).unwrap();
                assert_eq!(point.len(),22);
                assert_eq!(source.evaluate(&point).unwrap(),checked.value,
                    "local relation {role:?} must open in the common commitment");
                relation_claims.push(crate::opening_batch::Claim{point,value:checked.value});
                relation_gkr_bytes+=bytes.len();
                semantic_packets.push(bytes);
                semantic_gkr_ms+=started.elapsed().as_millis();
            };

            let serializer_input=gather_stage(1,segment_relation::load_copy);
            add_local_relation(b"header-serializer",1,serializer_relation,serializer_input,
                segment_relation::embed);
            let point_input=gather_stage(3,segment_points::load_copy);
            add_local_relation(b"header-point-membership",3,point_relation,point_input,
                segment_points::embed);

            // Audit mutant: this previous-timestamp bit is invisible to the
            // old H4 boundary. The repeated order proof must reject it.
            let mut order_input=gather_stage(4,header_order::load_copy);
            let order_mutant_index=header_order::ORDER_WIDTH+32;
            order_input[order_mutant_index]=if order_input[order_mutant_index].is_zero(){Fr::one()}else{Fr::zero()};
            let mut mutant_transcript=roster_transcript(b"header-order-mutant");
            assert_eq!(crate::sparse::prove(order_relation,&order_input,2,&mut mutant_transcript).unwrap_err(),
                crate::gkr::GkrError::NonzeroOutput);
            order_input=gather_stage(4,header_order::load_copy);
            add_local_relation(b"header-order",4,order_relation,order_input,header_order::embed);

            let tip=ergo_header_core::blake2b256(&decoded[header_count-1].0);
            let tip_time=decoded[header_count-1].1.timestamp;
            let mut add_adjacency_relation=|role:&[u8],link:&header_compact_links::Link|{
                let started=std::time::Instant::now();
                let mut prover=roster_transcript(role);
                let (proof,claim,_stats)=link.prove_streamed_boolean(&source,&mut prover).unwrap();
                let bytes=crate::gkr::encode_proof(&proof).unwrap();
                let decoded=link.decode_proof(&bytes).unwrap();
                let mut verifier=roster_transcript(role);
                let checked=link.verify(&decoded,&mut verifier).unwrap();
                assert_eq!(checked,claim,"adjacency relation {role:?}");
                assert_eq!(source.evaluate(&checked.point).unwrap(),checked.value,
                    "adjacency relation {role:?} must open in the common commitment");
                relation_claims.push(crate::opening_batch::Claim{point:checked.point,value:checked.value});
                relation_gkr_bytes+=bytes.len();
                semantic_packets.push(bytes);
                semantic_gkr_ms+=started.elapsed().as_millis();
            };
            let hash_link=header_compact_links::hash_relation(4,tip).unwrap();
            add_adjacency_relation(b"header-hash-adjacency",&hash_link);
            let metadata_link=header_compact_links::metadata_relation(4,tip_time).unwrap();
            add_adjacency_relation(b"header-metadata-adjacency",&metadata_link);
            assert_eq!(relation_claims.len(),7);

            // Isolate metadata authentication from local ordering: change the
            // imported previous timestamp and repair its unsigned delta. All
            // current fields, serialized bytes, hashes and tree cells stay fixed.
            let changed_previous=decoded[0].1.timestamp.checked_sub(1).unwrap();
            let repaired=header_order::witness(decoded[1].1.height,decoded[1].1.timestamp,
                decoded[0].1.height,changed_previous,false).unwrap();
            let mut repaired_order_input=gather_stage(4,header_order::load_copy);
            let mut changed_cells=BTreeMap::new();
            for (bit,value) in repaired.iter().enumerate() {
                let global_index=WIDTH+header_order::ORDER_OFFSET+bit;
                let value=Fr::from(*value as u64);
                if witness[global_index]!=value {
                    assert!((32..96).contains(&bit)||(512..576).contains(&bit));
                    changed_cells.insert(global_index,value);
                }
                repaired_order_input[header_order::ORDER_WIDTH+bit]=value;
            }
            assert!(!changed_cells.is_empty());
            assert!(composed.circuit.terms.iter().all(|term|
                !changed_cells.contains_key(&term.gate.left)&&!changed_cells.contains_key(&term.gate.right)),
                "the isolated metadata fault must leave the composed relation unchanged");
            for slot in 0..4 {
                let start=slot*header_order::ORDER_WIDTH;
                assert!(residuals(order_relation,&repaired_order_input[start..start+header_order::ORDER_WIDTH])
                    .iter().all(Zero::is_zero),"repaired order must pass for every header");
            }
            let mut repaired_order_transcript=roster_transcript(b"header-order");
            crate::sparse::prove(order_relation,&repaired_order_input,2,&mut repaired_order_transcript).unwrap();
            let mutant_path=std::env::temp_dir().join(format!("nipopow-v2-h4-metadata-mutant-{}-{nonce}.bits",std::process::id()));
            let mut mutant_bytes=std::fs::read(&packed_path).unwrap();
            for (&index,&value) in &changed_cells {
                let mask=1u8<<(index%8);
                if value.is_one(){mutant_bytes[index/8]|=mask;}else{mutant_bytes[index/8]&=!mask;}
            }
            let mut mutant_file=std::fs::OpenOptions::new().write(true).create_new(true).open(&mutant_path).unwrap();
            std::io::Write::write_all(&mut mutant_file,&mutant_bytes).unwrap();drop(mutant_file);drop(mutant_bytes);
            let mutant_source=crate::packed::PackedFile::open(&mutant_path,22).unwrap();
            let mut unchanged_hash_transcript=roster_transcript(b"header-hash-adjacency");
            let (unchanged_hash_proof,_,_)=hash_link.prove_streamed_boolean(&mutant_source,&mut unchanged_hash_transcript).unwrap();
            assert_eq!(crate::gkr::encode_proof(&unchanged_hash_proof).unwrap(),semantic_packets[5],
                "hash adjacency must remain byte-for-byte unchanged");
            let mut bad_metadata_transcript=roster_transcript(b"header-metadata-adjacency");
            assert_eq!(metadata_link.prove_streamed_boolean(&mutant_source,&mut bad_metadata_transcript).unwrap_err(),
                "nonzero adjacency residual");
            drop(mutant_source);std::fs::remove_file(&mutant_path).unwrap();

            let semantic_claims:[crate::opening_batch::Claim;7]=relation_claims.clone().try_into().unwrap();
            let complete_statement=crate::h4_packet::semantic_batch_statement(
                h4_expected.as_ref().unwrap(),&semantic_claims).unwrap();
            let complete_open_started=std::time::Instant::now();
            let (complete_opening,_complete_metrics,complete_prover_transcript)=crate::opening_batch::prove(
                &source,&committed,&setup,&complete_statement).unwrap();
            let complete_opening_bytes=crate::opening_batch::encode_proof(&complete_opening,22).unwrap();
            let decoded_complete_opening=crate::opening_batch::decode_proof(&complete_opening_bytes,22).unwrap();
            let complete_verifier_transcript=crate::opening_batch::verify_admitted(
                &complete_statement,&verifier_key,&decoded_complete_opening).unwrap();
            assert_eq!(transcript_ledger(&complete_prover_transcript),transcript_ledger(&complete_verifier_transcript));
            let mut producer_next=complete_prover_transcript.clone();let mut verifier_next=complete_verifier_transcript.clone();
            assert_eq!(producer_next.try_challenge_scalar(b"continuation").unwrap(),
                verifier_next.try_challenge_scalar(b"continuation").unwrap());
            let mut wrong_complete_statement=complete_statement.clone();
            wrong_complete_statement.claims[4].value+=Fr::from(1u64);
            assert!(crate::opening_batch::verify_admitted(&wrong_complete_statement,&verifier_key,
                &decoded_complete_opening).is_err(),"the mandatory order opening cannot be substituted");
            let complete_open_ms=complete_open_started.elapsed().as_millis();

            let expected=h4_expected.as_ref().unwrap();
            let packet=crate::h4_packet::Proof {
                core_gkr:core_packets.try_into().unwrap(),semantic_gkr:semantic_packets.try_into().unwrap(),
                opening_batches:[batch_bytes.clone(),complete_opening_bytes.clone()],
            };
            let statement_bytes=crate::h4_packet::encode_statement(expected).unwrap();
            assert_eq!(crate::h4_packet::decode_statement(&statement_bytes).unwrap(),*expected);
            let packet_bytes=crate::h4_packet::encode_proof(&packet).unwrap();
            assert_eq!(crate::h4_packet::decode_proof(&packet_bytes).unwrap(),packet);
            let client_metrics=crate::h4_packet::verify(expected,&packet).unwrap();
            println!("h4_autonomous_client {}",serde_json::to_string(&client_metrics).unwrap());

            // Every mandatory proof is independently load-bearing. Keep framing
            // and field encodings valid, and change one first-round scalar only.
            for section in 0..16 {
                use ark_serialize::CanonicalDeserialize;
                let mut wrong=packet.clone();
                let (part,offset,category)=if section<7 {
                    (&mut wrong.core_gkr[section],0,format!("H4 core GKR {section} rejected"))
                }else if section<14 {
                    (&mut wrong.semantic_gkr[section-7],0,format!("H4 semantic GKR {} rejected",section-7))
                }else {
                    (&mut wrong.opening_batches[section-14],12,format!("H4 opening batch {} rejected",section-14))
                };
                let mut cursor=&part[offset..offset+32];
                let changed=Fr::deserialize_compressed(&mut cursor).unwrap()+Fr::one();
                part[offset..offset+32].copy_from_slice(&crate::pcs::encode(&changed).unwrap());
                assert!(crate::h4_packet::encode_proof(&wrong).is_ok());
                let rejected=crate::h4_packet::verify(expected,&wrong).unwrap_err();
                assert!(rejected.contains(&category),"section {section}: {rejected}");
            }
            for mutation in 0..6 {
                let mut wrong=expected.clone();
                match mutation {
                    0=>wrong.root[0]^=1,1=>wrong.total_be28[27]^=1,2=>wrong.tip[0]^=1,
                    3=>wrong.tip_time=wrong.tip_time.checked_add(1).unwrap(),4=>wrong.setup_id[0]^=1,
                    5=>wrong.commitment=crate::pcs::encode_commitment(&dory_pcs::backends::arkworks::ArkGT::default()).unwrap(),
                    _=>unreachable!(),
                }
                assert!(crate::h4_packet::verify(&wrong,&packet).is_err(),"expected field {mutation}");
            }
            let mut swapped=packet.clone();swapped.core_gkr.swap(1,2);
            assert!(crate::h4_packet::verify(expected,&swapped).unwrap_err().contains("core GKR 1 rejected"));
            swapped=packet.clone();swapped.semantic_gkr.swap(5,6);
            assert!(crate::h4_packet::verify(expected,&swapped).unwrap_err().contains("semantic GKR 5 rejected"));
            swapped=packet.clone();swapped.semantic_gkr.swap(0,1);
            assert!(crate::h4_packet::verify(expected,&swapped).unwrap_err().contains("semantic GKR 0 rejected"));
            swapped=packet.clone();swapped.opening_batches.swap(0,1);
            assert!(crate::h4_packet::verify(expected,&swapped).unwrap_err().contains("opening batch 0 rejected"));
            println!("h4_consumer_negatives proof_sections=16 expected_fields=6 role_swaps=4 all_rejected=true");

            if let Some(directory)=std::env::var_os("NIPOPOW_V2_H4_EXPORT_DIR") {
                let directory=std::path::PathBuf::from(directory);
                assert!(directory.is_dir(),"export destination must already exist");
                for (name,bytes) in [("expected-statement.json",&statement_bytes),("proof.h4",&packet_bytes)] {
                    let mut file=std::fs::OpenOptions::new().write(true).create_new(true).open(directory.join(name)).unwrap();
                    std::io::Write::write_all(&mut file,bytes).unwrap();file.sync_all().unwrap();
                }
                println!("h4_export statement_bytes={} proof_bytes={} witness_exported=false",statement_bytes.len(),packet_bytes.len());
            }

            println!("complete_h4_mainnet roster_roles=7 shared_commitment_log_n=22 semantic_gkr_bytes={} opening_batch_bytes={} opening_batch_claims=7 exact_roster=true header_serializer_terms={} point_terms={} order_terms={} order_mutant=rejected hash_adjacency=verified metadata_adjacency=verified isolated_metadata_mutant=rejected v2_reference_terms={} v2_reference_rows={} v2_reference_reserved_rows={} setup_ms={} commitment_ms={} core_opening_ms={} core_opening_bytes={} relation_gkr_ms={} relation_opening_ms={} relation_gkr_verifier_checked=true relation_dory_admitted=true total_gkr_bytes={} total_opening_bytes={} result=pass",
                relation_gkr_bytes,complete_opening_bytes.len(),serializer_relation.terms.len(),point_relation.terms.len(),
                order_relation.terms.len(),composed.circuit.terms.len(),composed.circuit.row_count,composed.reserved_rows,
                setup_ms,commitment_ms,batch_ms,batch_bytes.len(),semantic_gkr_ms,complete_open_ms,
                relation_gkr_bytes+core_proof_bytes.iter().sum::<usize>(),
                complete_opening_bytes.len()+batch_bytes.len());
            drop(source);std::fs::remove_file(&packed_path).unwrap();
            return;
        }

        let opening_started=std::time::Instant::now();
        let dory=crate::packed::open(&committed,&source,&claim.point,&setup,&mut prover_transcript).unwrap();
        let dory_bytes=crate::pcs::encode_proof(&dory).unwrap();
        let opening_ms=opening_started.elapsed().as_millis();
        let decoded_dory=crate::pcs::decode_proof(&dory_bytes,22).unwrap();
        crate::pcs::verify(committed.commitment,verified.value,&verified.point,&decoded_dory,&setup,&mut verifier_transcript).unwrap();

        // Reuse this exact satisfying Mainnet witness to exercise the tagged
        // B1/B2/B3/B4 verifier. The separate legacy header boundary remains
        // covered by the composed proof above.
        let roster_fixed_profile=fixed::FixedProfile::new(3,root).unwrap();
        let roster_leaf_profile=LeafProfile::new(3,root).unwrap();
        let roster_boundary=compile(e,roster_leaf_profile.clone()).unwrap();
        assert_eq!(roster_fixed_profile.tree,topology.descriptor);
        assert_eq!(roster_leaf_profile.tree,topology.descriptor);
        assert_eq!(work_boundary.profile().tree,topology.descriptor);
        let roster=crate::work_tree_wiring::full_roster_circuit(&topology,e,&roster_fixed_profile,&roster_boundary,&work_boundary).unwrap();
        let (local_row_bits,family_bits,row_bits,input_bits)=crate::work_tree_wiring::full_roster_shape(&topology).unwrap();
        assert_eq!((local_row_bits,family_bits,row_bits,input_bits),(16,5,21,22));
        let roster_domain=b"nipopow-v2-h3-full-tagged-roster-gkr-test-v1";
        let roster_started=std::time::Instant::now();
        let mut roster_prover=crate::transcript::Transcript::new(roster_domain);
        let (roster_proof,roster_claim)=crate::sparse::prove_with_binding(&roster,&witness,0,&mut roster_prover,|t|
            {crate::work_tree_wiring::bind_full_roster(&topology,&roster_fixed_profile,&roster_leaf_profile,work_boundary.profile(),t);
                t.append_bytes(b"setup-id",&setup.id);t.append_bytes(b"input-commitment",&commitment_bytes);}).unwrap();
        let roster_gkr_ms=roster_started.elapsed().as_millis();
        assert_eq!(roster_claim.value,crate::gkr::mle(&witness,&roster_claim.point).unwrap());
        let roster_open_started=std::time::Instant::now();
        let roster_dory=crate::packed::open(&committed,&source,&roster_claim.point,&setup,&mut roster_prover).unwrap();
        let roster_open_ms=roster_open_started.elapsed().as_millis();
        let roster_dory_bytes=crate::pcs::encode_proof(&roster_dory).unwrap();
        let roster_dory=crate::pcs::decode_proof(&roster_dory_bytes,22).unwrap();
        let mut roster_verifier=crate::transcript::Transcript::new(roster_domain);
        let roster_verified=crate::gkr::verify_with_wiring(&[input_bits],roster.row_count,&roster_proof,&mut roster_verifier,
            |t|{crate::work_tree_wiring::bind_full_roster(&topology,&roster_fixed_profile,&roster_leaf_profile,work_boundary.profile(),t);
                t.append_bytes(b"setup-id",&setup.id);t.append_bytes(b"input-commitment",&commitment_bytes);},
            |_,r,u,v|crate::work_tree_wiring::full_roster_coefficients(
                &topology,e,&roster_fixed_profile,&roster_boundary,&work_boundary,r,u,v)
                .map_err(|error|{eprintln!("full roster callback rejected dimensions r={} u={} v={}: {error}",r.len(),u.len(),v.len());
                    crate::gkr::GkrError::PointDimension})).unwrap();
        assert_eq!(roster_verified,roster_claim);
        crate::pcs::verify(committed.commitment,roster_verified.value,&roster_verified.point,&roster_dory,&setup,&mut roster_verifier).unwrap();

        // Composition falsifier: split all B1/B2/B3/B4 roster families into
        // local and cross-slot claims, with one global witness commitment.
        let split_domain=b"nipopow-v2-h3-full-roster-two-claim-v1";
        let mut split_sizes=Vec::new();
        for local in [true,false]{
            let split=crate::work_tree_wiring::full_split_circuit(
                &topology,e,&roster_fixed_profile,&roster_boundary,&work_boundary,local).unwrap();
            let mut split_prover=crate::transcript::Transcript::new(split_domain);
            let resident_split_started=std::time::Instant::now();
            let (split_proof,split_claim)=crate::sparse::prove_with_binding(&split,&witness,0,&mut split_prover,|t|{
                crate::work_tree_wiring::bind_full_split(&topology,&roster_fixed_profile,&roster_leaf_profile,
                    work_boundary.profile(),&work_boundary,local,t);
                t.append_bytes(b"setup-id",&setup.id);t.append_bytes(b"input-commitment",&commitment_bytes);
            }).unwrap();
            let resident_split_ms=resident_split_started.elapsed().as_millis();
            assert_eq!(split_claim.value,crate::gkr::mle(&witness,&split_claim.point).unwrap());
            let mut streamed_term_visits=0usize;
            let mut streamed_transcript=crate::transcript::Transcript::new(split_domain);
            let (streamed_proof,streamed_claim)=crate::sparse_stream_terms::prove_with_term_source(
                split.input_len,split.row_count,split.terms.len(),&witness,&mut streamed_transcript,|t|{
                    crate::work_tree_wiring::bind_full_split(&topology,&roster_fixed_profile,&roster_leaf_profile,
                        work_boundary.profile(),&work_boundary,local,t);
                    t.append_bytes(b"setup-id",&setup.id);t.append_bytes(b"input-commitment",&commitment_bytes);
                },|visitor|crate::work_tree_wiring::full_split_visit_terms(
                    &topology,e,&roster_fixed_profile,&roster_boundary,&work_boundary,local,&mut |term|{
                        streamed_term_visits+=1;visitor(term)
                    }),|r,u,v|crate::work_tree_wiring::full_split_coefficients(
                    &topology,e,&roster_fixed_profile,&roster_boundary,&work_boundary,local,r,u,v)
                ).unwrap();
            assert_eq!(streamed_term_visits,3*split.terms.len(),"streamed producer must replay each term exactly three times");
            let streamed_proof_bytes=crate::gkr::encode_proof(&streamed_proof).unwrap();
            let split_proof_bytes=crate::gkr::encode_proof(&split_proof).unwrap();
            assert_eq!(streamed_proof_bytes,split_proof_bytes,"streamed GKR transcript differs from resident producer");
            assert_eq!(streamed_claim,split_claim,"streamed input claim differs from resident producer");
            let split_opening=crate::packed::open(&committed,&source,&split_claim.point,&setup,&mut split_prover).unwrap();
            let split_opening_bytes=crate::pcs::encode_proof(&split_opening).unwrap();
            let split_opening=crate::pcs::decode_proof(&split_opening_bytes,22).unwrap();
            if local{
                let (local_input_bits,slot_bits,base_row_bits,family_bits)=
                    crate::work_tree_wiring::full_split_local_tensor_dimensions(&topology,&work_boundary).unwrap();
                let member_row_bits=crate::work_tree_wiring::full_split_local_tensor_member_row_bits(&topology,&work_boundary).unwrap();
                let local_row_bits=base_row_bits+slot_bits;let local_mask=(1usize<<local_row_bits)-1;
                let b2_family=member_row_bits.len().checked_sub(3).expect("B2/B3/B4 families must be present");
                let key=|term:&Term,row:usize,slot:usize,family:usize,global:bool|{
                    let gate=&term.gate;let slot_wire=slot*WIDTH;
                    let left_global=family==b2_family&&gate.c1.is_zero()&&gate.c3.is_zero();
                    let right_global=family==b2_family&&gate.c2.is_zero()&&gate.c3.is_zero();
                    let zero=gate.c0.is_zero()&&gate.c1.is_zero()&&gate.c2.is_zero()&&gate.c3.is_zero();
                    (row,
                     if zero{0}else if global {gate.left} else if left_global {0}else{slot_wire+gate.left},
                     if zero{0}else if global {gate.right} else if right_global {0}else{slot_wire+gate.right},
                     gate.c0.into_bigint().0,gate.c1.into_bigint().0,gate.c2.into_bigint().0,gate.c3.into_bigint().0)
                };
                let mut resident_terms=BTreeMap::new();
                for term in &split.terms{
                    let member=term.row>>local_row_bits;let within=term.row&local_mask;
                    let low=member_row_bits[member];let slot=(within>>low)&((1usize<<slot_bits)-1);
                    let local_row=within&((1usize<<low)-1);let row=(member<<base_row_bits)|local_row;
                    *resident_terms.entry(key(term,row,slot,member,true)).or_insert(0usize)+=1;
                }
                let mut slot_terms=BTreeMap::new();
                for slot in 0..topology.descriptor.slots{
                    crate::work_tree_wiring::full_split_visit_local_slot_terms(
                        &topology,e,&roster_fixed_profile,&roster_boundary,&work_boundary,slot,&mut |term|{
                            let row=term.row;let family=row>>base_row_bits;
                            *slot_terms.entry(key(&term,row,slot,family,false)).or_insert(0usize)+=1;Ok(())
                        }).unwrap();
                }
                if slot_terms!=resident_terms{
                    let slot_only:Vec<_>=slot_terms.iter().filter(|(key,count)|resident_terms.get(*key).copied()!=Some(**count)).take(3).collect();
                    let resident_only:Vec<_>=resident_terms.iter().filter(|(key,count)|slot_terms.get(*key).copied()!=Some(**count)).take(3).collect();
                    panic!("per-slot term mismatch: slot keys={} resident keys={} slot-only={slot_only:?} resident-only={resident_only:?}",slot_terms.len(),resident_terms.len());
                }
                let mut anchor_transcript=crate::transcript::Transcript::new(split_domain);
                crate::work_tree_wiring::bind_full_split(&topology,&roster_fixed_profile,&roster_leaf_profile,
                    work_boundary.profile(),&work_boundary,true,&mut anchor_transcript);
                anchor_transcript.append_bytes(b"setup-id",&setup.id);
                anchor_transcript.append_bytes(b"input-commitment",&commitment_bytes);
                let anchor_r=crate::gkr::output_point(split.row_count,&mut anchor_transcript);
                crate::gkr::append_usize(&mut anchor_transcript,b"gkr-layer-index",0);
                let anchor_rows=crate::gkr::eq_weights(&anchor_r);
                let mut local_points=Vec::with_capacity(local_input_bits);
                for round in split_proof.layers[0].rounds.iter().take(local_input_bits){
                    crate::gkr::append_polynomial(&mut anchor_transcript,b"gkr-sumcheck-polynomial",round);
                    local_points.push(anchor_transcript.challenge_scalar(b"gkr-sumcheck-challenge"));
                }
                let local_weights=crate::gkr::eq_weights(&local_points);
                let mut resident_b=vec![Fr::zero();topology.descriptor.slots];
                for term in &split.terms{let gate=&term.gate;
                    let slot=gate.left/WIDTH;let local_wire=gate.left%WIDTH;
                    resident_b[slot]+=anchor_rows[term.row]*(gate.c0+gate.c2*witness[gate.right])*local_weights[local_wire];
                }
                let mut slot_b=vec![Fr::zero();topology.descriptor.slots];
                for slot in 0..topology.descriptor.slots{
                    crate::work_tree_wiring::full_split_visit_local_slot_terms(
                        &topology,e,&roster_fixed_profile,&roster_boundary,&work_boundary,slot,&mut |term|{
                            let family=term.row>>base_row_bits;let local=term.row&((1usize<<base_row_bits)-1);
                            let global_row=(family<<(base_row_bits+slot_bits))|(slot<<member_row_bits[family])|local;
                            let global_anchor=family==b2_family&&term.gate.c1.is_zero()&&term.gate.c3.is_zero();
                            let target_slot=if global_anchor{0}else{slot};
                            let local_wire=if global_anchor{0}else{term.gate.left};
                            let right=if term.gate.c2.is_zero(){Fr::zero()}else{witness[slot*WIDTH+term.gate.right]};
                            slot_b[target_slot]+=anchor_rows[global_row]*(term.gate.c0+term.gate.c2*right)*local_weights[local_wire];
                            Ok(())
                        }).unwrap();
                }
                assert_eq!(slot_b,resident_b,"slotwise B MLE after local challenges must match resident producer");
                let mut resident_a=vec![Fr::zero();topology.descriptor.slots];
                let mut resident_x=vec![Fr::zero();topology.descriptor.slots];
                for term in &split.terms{let gate=&term.gate;if !gate.c1.is_zero()||!gate.c3.is_zero(){
                    let slot=gate.left/WIDTH;let local_wire=gate.left%WIDTH;
                    resident_a[slot]+=anchor_rows[term.row]*(gate.c1+gate.c3*witness[gate.right])*local_weights[local_wire];
                }}
                for slot in 0..topology.descriptor.slots{
                    for wire in 0..WIDTH{resident_x[slot]+=witness[slot*WIDTH+wire]*local_weights[wire];}
                }
                let mut slot_a=vec![Fr::zero();topology.descriptor.slots];
                for slot in 0..topology.descriptor.slots{
                    crate::work_tree_wiring::full_split_visit_local_slot_terms(
                        &topology,e,&roster_fixed_profile,&roster_boundary,&work_boundary,slot,&mut |term|{
                            if !term.gate.c1.is_zero()||!term.gate.c3.is_zero(){
                                let family=term.row>>base_row_bits;let local=term.row&((1usize<<base_row_bits)-1);
                                let global_row=(family<<(base_row_bits+slot_bits))|(slot<<member_row_bits[family])|local;
                                let right=if term.gate.c3.is_zero(){Fr::zero()}else{witness[slot*WIDTH+term.gate.right]};
                                slot_a[slot]+=anchor_rows[global_row]*(term.gate.c1+term.gate.c3*right)*local_weights[term.gate.left];
                            }
                            Ok(())
                        }).unwrap();
                }
                assert_eq!(slot_a,resident_a,"slotwise A MLE after local challenges must match resident producer");
                let mut slot_x=vec![Fr::zero();topology.descriptor.slots];
                for slot in 0..topology.descriptor.slots{
                    for wire in 0..WIDTH{slot_x[slot]+=witness[slot*WIDTH+wire]*local_weights[wire];}
                }
                assert_eq!(slot_x,resident_x,"slotwise input MLE after local challenges must match resident producer");
                let mut tensor_transcript=crate::transcript::Transcript::new(split_domain);
                let mut tensor_term_visits=0usize;let tensor_started=std::time::Instant::now();
                let (tensor_proof,tensor_claim)=crate::sparse_stream_roster::prove_checked(
                    local_input_bits,slot_bits,base_row_bits,family_bits,&member_row_bits,
                    Some(&split_proof.layers[0].rounds),Some((&resident_a,&resident_b,&resident_x)),Some(&anchor_r),
                    |slot|read_packed_slot(&source,1usize<<local_input_bits,slot),&mut tensor_transcript,|t|{
                        crate::work_tree_wiring::bind_full_split(&topology,&roster_fixed_profile,&roster_leaf_profile,
                            work_boundary.profile(),&work_boundary,true,t);
                        t.append_bytes(b"setup-id",&setup.id);t.append_bytes(b"input-commitment",&commitment_bytes);
                    },|slot,visitor|crate::work_tree_wiring::full_split_visit_local_slot_terms(
                        &topology,e,&roster_fixed_profile,&roster_boundary,&work_boundary,slot,&mut |mut term|{
                            tensor_term_visits+=1;
                            let family=term.row>>base_row_bits;
                            if family==b2_family&&term.gate.c1.is_zero()&&term.gate.c3.is_zero(){term.gate.left=1usize<<local_input_bits;}
                            if family==b2_family&&term.gate.c2.is_zero()&&term.gate.c3.is_zero(){term.gate.right=1usize<<local_input_bits;}
                            visitor(term)
                        }),
                    |r,u,v|crate::work_tree_wiring::full_split_coefficients(
                        &topology,e,&roster_fixed_profile,&roster_boundary,&work_boundary,true,r,u,v)).unwrap();
                let tensor_ms=tensor_started.elapsed().as_millis();
                println!("local_tensor_h3 resident_gkr_ms={resident_split_ms} streamed_gkr_ms={tensor_ms} terms={} streamed_term_visits={tensor_term_visits}",split.terms.len());
                assert_eq!(tensor_proof.layers[0].rounds.len(),split_proof.layers[0].rounds.len());
                for (index,(tensor_round,resident_round)) in tensor_proof.layers[0].rounds.iter()
                    .zip(&split_proof.layers[0].rounds).enumerate(){
                    assert_eq!(tensor_round,resident_round,"slot-tensor GKR message differs at round {index}");
                }
                assert_eq!(tensor_proof.layers[0].left_value,split_proof.layers[0].left_value);
                assert_eq!(tensor_proof.layers[0].right_value,split_proof.layers[0].right_value);
                assert_eq!(tensor_proof.layers[0].line_coefficients,split_proof.layers[0].line_coefficients);
                assert_eq!(crate::gkr::encode_proof(&tensor_proof).unwrap(),split_proof_bytes,
                    "slot-tensor GKR proof differs from resident local claim");
                assert_eq!(tensor_claim,split_claim,"slot-tensor input claim differs from resident local claim");
                let tensor_opening=crate::packed::open(&committed,&source,&tensor_claim.point,&setup,&mut tensor_transcript).unwrap();
                assert_eq!(crate::pcs::encode_proof(&tensor_opening).unwrap(),split_opening_bytes,
                    "slot-tensor Dory opening differs from resident local claim");
                assert_eq!(tensor_transcript.challenges(),split_prover.challenges());
                assert_eq!(tensor_transcript.raw_queries(),split_prover.raw_queries());
                assert_eq!(tensor_transcript.bytes_absorbed(),split_prover.bytes_absorbed());
                let mut tensor_next=tensor_transcript.clone();let mut resident_next=split_prover.clone();
                assert_eq!(tensor_next.challenge_scalar(b"parity-next"),resident_next.challenge_scalar(b"parity-next"),
                    "slot-tensor transcript differs after Dory opening");
            }else{
                let (edge_input_bits,edge_slot_bits,edge_base_row_bits,edge_family_bits)=
                    crate::work_tree_wiring::full_split_cross_tensor_dimensions(&topology,&work_boundary).unwrap();
                let edge_member_row_bits=crate::work_tree_wiring::full_split_cross_tensor_member_row_bits(&topology,&work_boundary).unwrap();
                let mut edge_term_visits=0usize;let mut edge_transcript=crate::transcript::Transcript::new(split_domain);
                let edge_started=std::time::Instant::now();
                let (edge_proof,edge_claim,edge_incremental_u,edge_incremental_v)=crate::sparse_stream_roster::prove_edge_terms(
                    edge_input_bits,edge_slot_bits,edge_base_row_bits,edge_family_bits,&edge_member_row_bits,
                    |left,slot,sink|crate::work_tree_wiring::full_split_visit_cross_endpoint_terms(
                        &topology,&work_boundary,left,slot,&mut |source_slot,family_row,term|{
                            edge_term_visits+=1;sink(crate::sparse_stream_roster::EdgeTerm{source_slot,family_row,term})
                        }),
                    |slot|read_packed_slot(&source,1usize<<edge_input_bits,slot),&mut edge_transcript,|t|{
                        crate::work_tree_wiring::bind_full_split(&topology,&roster_fixed_profile,&roster_leaf_profile,
                            work_boundary.profile(),&work_boundary,false,t);
                        t.append_bytes(b"setup-id",&setup.id);t.append_bytes(b"input-commitment",&commitment_bytes);
                    },|r,u,v|crate::work_tree_wiring::full_split_coefficients(
                        &topology,e,&roster_fixed_profile,&roster_boundary,&work_boundary,false,r,u,v)).unwrap();
                assert!(edge_incremental_u&&edge_incremental_v,"H3 edge fixture must exercise both incremental phases");
                let edge_ms=edge_started.elapsed().as_millis();
                println!("cross_tensor_h3 resident_gkr_ms={resident_split_ms} streamed_gkr_ms={edge_ms} terms={} endpoint_term_visits={edge_term_visits}",split.terms.len());
                assert_eq!(crate::gkr::encode_proof(&edge_proof).unwrap(),split_proof_bytes,
                    "endpoint-tensor cross GKR proof differs from resident claim");
                assert_eq!(edge_claim,split_claim,"endpoint-tensor cross claim differs from resident");
                let edge_opening=crate::packed::open(&committed,&source,&edge_claim.point,&setup,&mut edge_transcript).unwrap();
                assert_eq!(crate::pcs::encode_proof(&edge_opening).unwrap(),split_opening_bytes,
                    "endpoint-tensor cross Dory opening differs from resident");
                assert_eq!(edge_transcript.challenges(),split_prover.challenges());
                assert_eq!(edge_transcript.raw_queries(),split_prover.raw_queries());
                assert_eq!(edge_transcript.bytes_absorbed(),split_prover.bytes_absorbed());
                let mut edge_next=edge_transcript.clone();let mut resident_next=split_prover.clone();
                assert_eq!(edge_next.challenge_scalar(b"parity-next"),resident_next.challenge_scalar(b"parity-next"),
                    "endpoint-tensor transcript differs after Dory opening");
                println!("cross_edge_tensor_h3 terms={} endpoint_term_visits={edge_term_visits}",split.terms.len());
            }
            let streamed_opening=crate::packed::open(&committed,&source,&streamed_claim.point,&setup,&mut streamed_transcript).unwrap();
            let streamed_opening_bytes=crate::pcs::encode_proof(&streamed_opening).unwrap();
            assert_eq!(streamed_opening_bytes,split_opening_bytes,"streamed Dory opening differs");
            assert_eq!(streamed_transcript.challenges(),split_prover.challenges());
            assert_eq!(streamed_transcript.raw_queries(),split_prover.raw_queries());
            assert_eq!(streamed_transcript.bytes_absorbed(),split_prover.bytes_absorbed());
            let mut split_next=split_prover.clone();let mut streamed_next=streamed_transcript.clone();
            assert_eq!(split_next.challenge_scalar(b"parity-next"),streamed_next.challenge_scalar(b"parity-next"),"transcript state differs after identical proofs and openings");
            let streamed_opening=crate::pcs::decode_proof(&streamed_opening_bytes,22).unwrap();
            let split_proof=crate::sparse::decode_proof(&split,0,&split_proof_bytes).unwrap();
            let mut split_verifier=crate::transcript::Transcript::new(split_domain);
            let split_verified=crate::gkr::verify_with_wiring(&[input_bits],split.row_count,&split_proof,&mut split_verifier,|t|{
                crate::work_tree_wiring::bind_full_split(&topology,&roster_fixed_profile,&roster_leaf_profile,
                    work_boundary.profile(),&work_boundary,local,t);
                t.append_bytes(b"setup-id",&setup.id);t.append_bytes(b"input-commitment",&commitment_bytes);
            },|_,r,u,v|crate::work_tree_wiring::full_split_coefficients(
                &topology,e,&roster_fixed_profile,&roster_boundary,&work_boundary,local,r,u,v)
                .map_err(|_|crate::gkr::GkrError::PointDimension)).unwrap();
            assert_eq!(split_verified,split_claim);
            crate::pcs::verify(committed.commitment,split_verified.value,&split_verified.point,&split_opening,&setup,&mut split_verifier).unwrap();
            let streamed_proof=crate::sparse::decode_proof(&split,0,&streamed_proof_bytes).unwrap();
            let mut streamed_verifier=crate::transcript::Transcript::new(split_domain);
            let streamed_verified=crate::gkr::verify_with_wiring(&[input_bits],split.row_count,&streamed_proof,&mut streamed_verifier,|t|{
                crate::work_tree_wiring::bind_full_split(&topology,&roster_fixed_profile,&roster_leaf_profile,
                    work_boundary.profile(),&work_boundary,local,t);
                t.append_bytes(b"setup-id",&setup.id);t.append_bytes(b"input-commitment",&commitment_bytes);
            },|_,r,u,v|crate::work_tree_wiring::full_split_coefficients(
                &topology,e,&roster_fixed_profile,&roster_boundary,&work_boundary,local,r,u,v)
                .map_err(|_|crate::gkr::GkrError::PointDimension)).unwrap();
            assert_eq!(streamed_verified,streamed_claim);
            crate::pcs::verify(committed.commitment,streamed_verified.value,&streamed_verified.point,&streamed_opening,&setup,&mut streamed_verifier).unwrap();
            if local{
                let mut omission_transcript=crate::transcript::Transcript::new(split_domain);
                let omitted=crate::gkr::verify_with_wiring(&[input_bits],split.row_count,&split_proof,&mut omission_transcript,|t|{
                    crate::work_tree_wiring::bind_full_split(&topology,&roster_fixed_profile,&roster_leaf_profile,
                        work_boundary.profile(),&work_boundary,local,t);
                    t.append_bytes(b"setup-id",&setup.id);t.append_bytes(b"input-commitment",&commitment_bytes);
                },|_,r,u,v|crate::work_tree_wiring::full_split_coefficients_omitting(
                    &topology,e,&roster_fixed_profile,&roster_boundary,&work_boundary,local,r,u,v,Some("B3_leaf_hash"))
                    .map_err(|_|crate::gkr::GkrError::PointDimension));
                assert!(omitted.is_err(),"local split accepted an omitted B3 leaf-hash family");
            }else{
                for omitted_name in ["level_1_child_0","work_interval_continuity"]{
                    let mut omission_transcript=crate::transcript::Transcript::new(split_domain);
                    let omitted=crate::gkr::verify_with_wiring(&[input_bits],split.row_count,&split_proof,&mut omission_transcript,|t|{
                        crate::work_tree_wiring::bind_full_split(&topology,&roster_fixed_profile,&roster_leaf_profile,
                            work_boundary.profile(),&work_boundary,local,t);
                        t.append_bytes(b"setup-id",&setup.id);t.append_bytes(b"input-commitment",&commitment_bytes);
                    },|_,r,u,v|crate::work_tree_wiring::full_split_coefficients_omitting(
                        &topology,e,&roster_fixed_profile,&roster_boundary,&work_boundary,local,r,u,v,Some(omitted_name))
                        .map_err(|_|crate::gkr::GkrError::PointDimension));
                    assert!(omitted.is_err(),"cross-slot split accepted an omitted family: {omitted_name}");
                }
                let mut changed_total=work_boundary.profile().clone();changed_total.total_be28[27]^=1;
                let changed_boundary=crate::work_tree_work::compile(base,changed_total.clone()).unwrap();
                let mut changed_transcript=crate::transcript::Transcript::new(split_domain);
                let changed_total_proof=crate::gkr::verify_with_wiring(&[input_bits],split.row_count,&split_proof,&mut changed_transcript,|t|{
                    crate::work_tree_wiring::bind_full_split(&topology,&roster_fixed_profile,&roster_leaf_profile,
                        &changed_total,&changed_boundary,local,t);
                    t.append_bytes(b"setup-id",&setup.id);t.append_bytes(b"input-commitment",&commitment_bytes);
                },|_,r,u,v|crate::work_tree_wiring::full_split_coefficients(
                    &topology,e,&roster_fixed_profile,&roster_boundary,&changed_boundary,local,r,u,v)
                    .map_err(|_|crate::gkr::GkrError::PointDimension));
                assert!(changed_total_proof.is_err(),"cross-slot split accepted a changed B4 public total");
            }
            split_sizes.push((split.terms.len(),split.row_count));
        }
        println!("full_roster_two_claim_h3 local_terms={} local_rows={} cross_terms={} cross_rows={} claims=2 commitment=single",
            split_sizes[0].0,split_sizes[0].1,split_sizes[1].0,split_sizes[1].1);

        let swapped_tag=|index|match index {0=>1,1=>0,_=>index};
        let mut tag_mutant_transcript=crate::transcript::Transcript::new(roster_domain);
        let tag_mutant=crate::gkr::verify_with_wiring(&[input_bits],roster.row_count,&roster_proof,&mut tag_mutant_transcript,
            |t|{crate::work_tree_wiring::bind_full_roster(&topology,&roster_fixed_profile,&roster_leaf_profile,work_boundary.profile(),t);
                t.append_bytes(b"setup-id",&setup.id);t.append_bytes(b"input-commitment",&commitment_bytes);},
            |_,r,u,v|crate::work_tree_wiring::full_roster_coefficients_with_tag(
                &topology,e,&roster_fixed_profile,&roster_boundary,&work_boundary,r,u,v,swapped_tag)
                .map_err(|_|crate::gkr::GkrError::PointDimension));
        assert!(tag_mutant.is_err(),"full-roster GKR accepted two swapped algebraic family tags");

        let mut changed_total=work_boundary.profile().clone();changed_total.total_be28[27]^=1;
        let mut total_mutant_transcript=crate::transcript::Transcript::new(b"nipopow-v2-h3-full-tagged-roster-gkr-test-v1");
        let total_mutant=crate::gkr::verify_with_wiring(&[input_bits],roster.row_count,&roster_proof,&mut total_mutant_transcript,
            |t|{crate::work_tree_wiring::bind_full_roster(&topology,&roster_fixed_profile,&roster_leaf_profile,&changed_total,t);
                t.append_bytes(b"setup-id",&setup.id);t.append_bytes(b"input-commitment",&commitment_bytes);},
            |_,r,u,v|crate::work_tree_wiring::full_roster_coefficients(
                &topology,e,&roster_fixed_profile,&roster_boundary,&work_boundary,r,u,v)
                .map_err(|_|crate::gkr::GkrError::PointDimension));
        assert!(total_mutant.is_err(),"full-roster GKR accepted a mutated public work total");

        let changed_work_boundary=crate::work_tree_work::compile(base,changed_total).unwrap();
        let mut total_relation_transcript=crate::transcript::Transcript::new(roster_domain);
        let total_relation_mutant=crate::gkr::verify_with_wiring(&[input_bits],roster.row_count,&roster_proof,&mut total_relation_transcript,
            |t|{crate::work_tree_wiring::bind_full_roster(&topology,&roster_fixed_profile,&roster_leaf_profile,work_boundary.profile(),t);
                t.append_bytes(b"setup-id",&setup.id);t.append_bytes(b"input-commitment",&commitment_bytes);},
            |_,r,u,v|crate::work_tree_wiring::full_roster_coefficients(
                &topology,e,&roster_fixed_profile,&roster_boundary,&changed_work_boundary,r,u,v)
                .map_err(|_|crate::gkr::GkrError::PointDimension));
        assert!(total_relation_mutant.is_err(),"full-roster GKR accepted the original binding with an altered B4 public-total relation");
        println!("full_tagged_h3_gkr_ms={roster_gkr_ms} dory_ms={roster_open_ms} families={} terms={} input_bits={} row_bits={} proof_layers={} dory_bytes={}",
            topology.families.len()+6,roster.terms.len(),input_bits,row_bits,roster_proof.layers.len(),roster_dory_bytes.len());
        println!("composed_h3_setup_ms={setup_ms} commitment_ms={commitment_ms} core_claims=7 core_gkr_bytes={} opening_batch_ms={batch_ms} opening_batch_bytes={} projection_ms={:.3} transition_ms={:.3} batch_pcs_ms={:.3} boundary_gkr_ms={gkr_ms} boundary_dory_ms={opening_ms} boundary_gkr_bytes={} boundary_dory_bytes={}",core_proof_bytes.iter().sum::<usize>(),batch_bytes.len(),batch_metrics.projection_seconds*1000.0,batch_metrics.transition_seconds*1000.0,batch_metrics.pcs_seconds*1000.0,proof_bytes.len(),dory_bytes.len());
    }
}

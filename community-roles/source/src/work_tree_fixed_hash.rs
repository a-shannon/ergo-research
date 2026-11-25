//! Fixed node/profile/dummy hash boundary. Leaves and U224 work remain uncertified.
use std::{collections::BTreeMap,sync::OnceLock};
use ark_bn254::Fr;
use ark_ff::{One,Zero};
use blake2::{Blake2b,Digest,digest::consts::U32};
use serde::{Serialize,Deserialize};
use serde_json::{Value,json};
use crate::{circuit::{self,CompressionInput},gkr::Gate,sparse::{Circuit,Term},header_order,
    work_tree_layout::{self as layout,Baseline,WIDTH,CORE},work_tree_wiring::{self as topology,Descriptor,Topology}};

pub const NODE_CORE:usize=917504;
pub const ROW_WIDTH:usize=2048;
pub const NEW_ROWS_PER_SLOT:usize=1601;
pub const DIGEST_ROW:usize=1601;
pub const PROFILE_PREFIX:&[u8;27]=b"nipopow-v2/work-profile/v1\0";
pub const NATIVE_WORK_SHA256:&str="C2C82ECBD554C8D3B2919A3815C4DE1DB6737C220FACE85781B2D3E63A9DDD41";
pub const PENDING:&[&str]=&[
    "variable-length leaf preimages, leaf compression chains and selected leaf digests",
    "positive U224 work decoding, interval addition, continuity and total",
    "retirement and replacement of old header dummy cores 5..7",
    "full inactive header/serializer execution outside the fixed node core",
    "global GKR/PCS authentication of the joined core, B1 topology and fixed boundary",
    "complete DAA and historical feasibility",
];

#[derive(Clone,Debug,Serialize,Deserialize,PartialEq,Eq)]
pub struct FixedProfile {
    pub schema:String,pub tree:Descriptor,pub genesis:[u8;32],pub prefix:Vec<u8>,
    pub node_core_offset:usize,pub node_len:usize,pub profile_len:usize,
    pub dummy_counter:u64,pub dummy_final:bool,pub native_work_sha256:String,
}
impl FixedProfile {
    pub fn new(headers:usize,root:[u8;32])->Result<Self,String> {
        Ok(Self {schema:"work-tree-fixed-node-profile-hash-v1".into(),tree:Descriptor::new(headers,root)?,
            genesis:header_order::MAINNET_GENESIS,prefix:PROFILE_PREFIX.to_vec(),node_core_offset:NODE_CORE,
            node_len:70,profile_len:59,dummy_counter:0,dummy_final:true,native_work_sha256:NATIVE_WORK_SHA256.into()})
    }
    pub fn validate(&self)->Result<(),String> {
        if *self!=Self::new(self.tree.headers,self.tree.root)? {return Err("fixed hash descriptor mismatch".into());}Ok(())
    }
    pub fn role(&self,slot:usize)->Result<Role,String> {
        if slot>=self.tree.slots {return Err("fixed hash slot outside S".into());}
        if slot>=self.tree.leaves {return Ok(Role::Dummy);}
        if slot==self.tree.profile_node_slot {return Ok(Role::Profile);}
        for level in 1..=self.tree.leaves.trailing_zeros() as usize {
            let (start,count)=self.tree.level(level)?;
            if (start..start+count).contains(&slot) {return Ok(Role::Node {level:level as u8,position:(slot-start) as u32});}
        }
        Err("node role not covered".into())
    }
    pub fn fingerprint(&self)->Result<String,String> {
        self.validate()?;Ok(layout::hash_bytes(&serde_json::to_vec(self).map_err(|e|e.to_string())?))
    }
}
#[derive(Clone,Copy,Debug,PartialEq,Eq,Serialize)]
pub enum Role {Node {level:u8,position:u32},Profile,Dummy}

pub struct Engine {pub base:&'static Baseline,pub core:Circuit}
pub fn engine()->Result<&'static Engine,String> {
    static VALUE:OnceLock<Result<Engine,String>>=OnceLock::new();
    VALUE.get_or_init(|| {
        let base=layout::shared_baseline()?;let core=circuit::build_compression(None)?;
        if core.layout!=base.compression || core.compiled.circuit.input_len!=CORE
            || core.compiled.circuit.terms.len()!=base.inventory.core.terms {
            return Err("fixed hash core/baseline mismatch".into());
        }
        Ok(Engine {base,core:core.compiled.circuit})
    }).as_ref().map_err(Clone::clone)
}

fn linear(row:usize,wire:usize,coefficient:Fr)->Term {
    Term {row,gate:Gate {left:wire,right:0,c0:Fr::zero(),c1:coefficient,c2:Fr::zero(),c3:Fr::zero()}}
}
fn constant(row:usize,value:bool)->Option<Term> {
    value.then_some(Term {row,gate:Gate {left:0,right:0,c0:-Fr::one(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}})
}
fn counter(role:Role)->u64 {match role {Role::Node {..}=>70,Role::Profile=>59,Role::Dummy=>0}}
fn message_wire(e:&Engine,byte:usize,bit:usize)->usize {
    NODE_CORE+e.base.compression.message[byte/8][(byte%8)*8+bit]
}
fn expected_constant(p:&FixedProfile,role:Role,byte:usize)->u8 {
    match role {
        Role::Node {level,position}=>match byte {0=>b'N',1=>level,2..=5=>position.to_be_bytes()[byte-2],_=>0},
        Role::Profile=>if byte<27 {p.prefix[byte]}else if byte<59 {p.genesis[byte-27]}else {0},
        Role::Dummy=>0,
    }
}

/// Emit one public slot; callers cannot supply a private role, length, IV or flag.
pub fn emit_slot(e:&Engine,p:&FixedProfile,slot:usize,mut sink:impl FnMut(Term))->Result<(),String> {
    p.validate()?;let role=p.role(slot)?;let global=slot*WIDTH;let row_base=slot*ROW_WIDTH;
    let iv=circuit::blake2b256_initial_state();let l=&e.base.compression;
    for bit in 0..512 {
        let row=row_base+bit;sink(linear(row,global+NODE_CORE+l.state[bit/64][bit%64],Fr::one()));
        if let Some(t)=constant(row,(iv[bit/64]>>(bit%64))&1!=0){sink(t);}
    }
    for byte in 0..128 {for bit in 0..8 {
        let row=row_base+512+byte*8+bit;sink(linear(row,global+message_wire(e,byte,bit),Fr::one()));
        if matches!(role,Role::Node {..}) && (6..70).contains(&byte) {
            let wire=if byte<38 {e.base.endpoints.node_left[(byte-6)*8+bit]}
                else {e.base.endpoints.node_right[(byte-38)*8+bit]};
            sink(linear(row,global+wire,-Fr::one()));
        }else if let Some(t)=constant(row,(expected_constant(p,role,byte)>>bit)&1!=0){sink(t);}
    }}
    for bit in 0..64 {
        let row=row_base+1536+bit;sink(linear(row,global+NODE_CORE+l.counter[bit],Fr::one()));
        if let Some(t)=constant(row,(counter(role)>>bit)&1!=0){sink(t);}
    }
    sink(linear(row_base+1600,global+NODE_CORE+l.final_flag,Fr::one()));
    sink(constant(row_base+1600,true).unwrap());
    // Same equality already emitted by B1 for [0,B). Never alias a dummy hash to zero endpoints.
    if !matches!(role,Role::Dummy) {for bit in 0..256 {
        let row=row_base+DIGEST_ROW+bit;
        sink(linear(row,global+NODE_CORE+l.output[bit/64][bit%64],Fr::one()));
        sink(linear(row,global+e.base.endpoints.node[bit],-Fr::one()));
    }}
    Ok(())
}

#[derive(Clone,Debug,Serialize)]
pub struct Counts {
    pub headers:usize,pub tree_leaves:usize,pub global_slots:usize,pub nodes:u64,pub profiles:u64,pub dummy_slots:u64,
    pub additional_witness_bits:u64,pub additional_core_banks:u64,pub consumed_existing_core_offset:usize,
    pub new_live_boundary_rows:u64,pub reused_b1_digest_alias_rows:u64,pub reused_b1_child_alias_rows:u64,
    pub materialized_live_rows:u64,pub padded_boundary_rows:u64,
    pub new_boundary_terms:u64,pub reused_b1_digest_alias_terms:u64,pub reused_b1_child_alias_terms:u64,
    pub standalone_reemitted_digest_alias_terms:u64,pub standalone_reemitted_child_alias_terms:u64,
    pub total_boundary_terms:u64,
    pub fixed_core_copies:u64,pub core_used_bits:usize,pub core_padded_bits:usize,pub core_rows_per_copy:usize,pub core_terms_per_copy:usize,
    pub fixed_core_rows:u64,pub fixed_core_terms:u64,pub active_native_compressions:u64,
    pub maximum_boundary_degree:usize,pub global_input_log:usize,pub boundary_row_log:usize,
    pub boundary_dimension_le24:bool,pub boundary_base_terms_le2pow20:bool,pub repeated_core_log_copies_le3:bool,
    pub role_kernel_multiplication_upper:usize,pub role_kernel_field_scratch_upper:usize,
    pub analytic_total_multiplication_upper:usize,pub retained_core_term_capacity_bytes:usize,
}
pub fn count(e:&Engine,p:&FixedProfile)->Result<Counts,String> {
    p.validate()?;let b=p.tree.leaves as u64;let s=p.tree.slots as u64;let nodes=b-1;
    let state_ones:u64=circuit::blake2b256_initial_state().iter().map(|w|w.count_ones() as u64).sum();
    let mut node_constants=nodes*b'N'.count_ones() as u64;
    for level in 1..=p.tree.leaves.trailing_zeros() {
        let n=b>>level;node_constants+=n*level.count_ones() as u64;
        // Each low position bit is one for half the complete dyadic interval.
        if n>1 {node_constants+=n*n.trailing_zeros() as u64/2;}
    }
    let profile_ones:u64=p.prefix.iter().chain(&p.genesis).map(|byte|byte.count_ones() as u64).sum();
    let new_terms=(NEW_ROWS_PER_SLOT as u64+state_ones+1)*s+512*nodes+node_constants+profile_ones
        +nodes*70u64.count_ones() as u64+59u64.count_ones() as u64;
    let reused=512*b;let total=new_terms+reused;let h=p.tree.slot_log();
    Ok(Counts {headers:p.tree.headers,tree_leaves:p.tree.leaves,global_slots:p.tree.slots,nodes,profiles:1,dummy_slots:s-b,
        additional_witness_bits:0,additional_core_banks:0,consumed_existing_core_offset:NODE_CORE,
        new_live_boundary_rows:NEW_ROWS_PER_SLOT as u64*s-512*nodes,reused_b1_digest_alias_rows:256*b,
        reused_b1_child_alias_rows:512*nodes,
        materialized_live_rows:NEW_ROWS_PER_SLOT as u64*s+256*b,padded_boundary_rows:ROW_WIDTH as u64*s,
        new_boundary_terms:new_terms-1024*nodes,reused_b1_digest_alias_terms:256*b,
        reused_b1_child_alias_terms:512*nodes,standalone_reemitted_digest_alias_terms:reused,
        standalone_reemitted_child_alias_terms:1024*nodes,total_boundary_terms:total,
        fixed_core_copies:s,core_used_bits:e.base.compression.used_input_len,core_padded_bits:e.core.input_len,
        core_rows_per_copy:e.core.row_count,core_terms_per_copy:e.core.terms.len(),
        fixed_core_rows:s*e.core.row_count as u64,fixed_core_terms:s*e.core.terms.len() as u64,active_native_compressions:b,
        maximum_boundary_degree:1,global_input_log:20+h,boundary_row_log:11+h,
        boundary_dimension_le24:20+h<=24,boundary_base_terms_le2pow20:total<=1<<20,repeated_core_log_copies_le3:h<=3,
        role_kernel_multiplication_upper:40*h+100,role_kernel_field_scratch_upper:8*(h+1)+128,
        analytic_total_multiplication_upper:100000+40*h,retained_core_term_capacity_bytes:e.core.terms.capacity()*std::mem::size_of::<Term>()})
}

struct RoleWeights {all:Fr,node:Fr,profile:Fr,active:Fr,level:[Fr;8],position:[Fr;32]}
/// Prefix/suffix products have no divisions; zero challenge factors are valid inputs.
fn role_weights(p:&FixedProfile,points:&[&[Fr]])->Result<RoleWeights,String> {
    let h=p.tree.slot_log();let b=p.tree.leaves.trailing_zeros() as usize;
    if points.is_empty() || points.len()>2 || points.iter().any(|v|v.len()!=h) {return Err("role point dimension".into());}
    let mut zero=vec![Fr::one();h];let mut one=zero.clone();
    for bit in 0..h {for v in points {zero[bit]*=Fr::one()-v[bit];one[bit]*=v[bit];}}
    let mut free=vec![Fr::one();h+1];
    for bit in 0..h {free[bit+1]=free[bit]*(zero[bit]+one[bit]);}
    let mut suffix=vec![Fr::one();b+1];let mut ones=suffix.clone();
    for bit in (0..b).rev() {suffix[bit]=suffix[bit+1]*(zero[bit]+one[bit]);ones[bit]=ones[bit+1]*one[bit];}
    let mut top=Fr::one();for value in &zero[b..] {top*=value;}
    let active=free[b]*top;let profile=ones[0]*top;let mut level=[Fr::zero();8];
    for m in 0..b {
        let weight=free[m]*zero[m]*ones[m+1]*top;let l=b-m;
        for (bit,value) in level.iter_mut().enumerate(){if (l>>bit)&1!=0 {*value+=weight;}}
    }
    let mut position=[Fr::zero();32];
    for q in 0..b {position[q]=free[q]*one[q]*(suffix[q+1]-ones[q+1])*top;}
    Ok(RoleWeights {all:free[h],node:active-profile,profile,active,level,position})
}

/// Coefficients for the exact emitted sparse gates. Cost is O(log H)+fixed local layout.
pub fn coefficients(e:&Engine,p:&FixedProfile,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String> {
    p.validate()?;let h=p.tree.slot_log();
    if r.len()!=11+h || u.len()!=20+h || v.len()!=20+h {return Err("fixed boundary wiring dimension".into());}
    let a=role_weights(p,&[&r[11..]])?;let pair=role_weights(p,&[&r[11..],&u[20..]])?;
    let u0=topology::eq_index(u,0);let v0=topology::eq_index(v,0);let mut out=[Fr::zero();4];
    let row=|i|topology::eq_index(&r[..11],i);let wire=|i|topology::eq_index(&u[..20],i);
    let iv=circuit::blake2b256_initial_state();let l=&e.base.compression;
    for bit in 0..512 {
        let w=row(bit);out[1]+=w*wire(NODE_CORE+l.state[bit/64][bit%64])*pair.all;
        if (iv[bit/64]>>(bit%64))&1!=0 {out[0]-=w*a.all*u0;}
    }
    for byte in 0..128 {for bit in 0..8 {
        let w=row(512+byte*8+bit);out[1]+=w*wire(message_wire(e,byte,bit))*pair.all;
        let mut expected=Fr::zero();
        match byte {
            0=>if (b'N'>>bit)&1!=0 {expected+=a.node;},
            1=>expected+=a.level[bit],
            2..=5=>expected+=a.position[(5-byte)*8+bit],
            6..=69=>{
                let source=if byte<38 {e.base.endpoints.node_left[(byte-6)*8+bit]}
                    else {e.base.endpoints.node_right[(byte-38)*8+bit]};
                out[1]-=w*wire(source)*pair.node;
            },_=>{}
        }
        if (expected_constant(p,Role::Profile,byte)>>bit)&1!=0 {expected+=a.profile;}
        out[0]-=w*expected*u0;
    }}
    for bit in 0..64 {
        let w=row(1536+bit);out[1]+=w*wire(NODE_CORE+l.counter[bit])*pair.all;
        let mut expected=Fr::zero();if (70u64>>bit)&1!=0{expected+=a.node;}if (59u64>>bit)&1!=0{expected+=a.profile;}
        out[0]-=w*expected*u0;
    }
    let w=row(1600);out[1]+=w*wire(NODE_CORE+l.final_flag)*pair.all;out[0]-=w*a.all*u0;
    for bit in 0..256 {
        let w=row(DIGEST_ROW+bit);
        out[1]+=w*(wire(NODE_CORE+l.output[bit/64][bit%64])-wire(e.base.endpoints.node[bit]))*pair.active;
    }
    out[0]*=v0;out[1]*=v0;Ok(out)
}

fn native_hash(bytes:&[u8])->[u8;32] {Blake2b::<U32>::digest(bytes).into()}
fn independent_node(level:u8,position:u32,left:[u8;32],right:[u8;32])->Vec<u8> {
    let mut bytes=vec![b'N',level];bytes.extend_from_slice(&position.to_be_bytes());
    bytes.extend_from_slice(&left);bytes.extend_from_slice(&right);bytes
}
fn independent_profile()->Vec<u8> {
    let mut bytes=b"nipopow-v2/work-profile/v1\0".to_vec();bytes.extend_from_slice(&header_order::MAINNET_GENESIS);bytes
}
fn compression_input(bytes:&[u8])->CompressionInput {
    let mut block=[0u8;128];block[..bytes.len()].copy_from_slice(bytes);
    CompressionInput {state:circuit::blake2b256_initial_state(),block,counter:bytes.len() as u64,final_flag:true}
}
fn core_output(input:&[Fr],e:&Engine)->Result<[u8;32],String> {
    let mut output=[0u8;32];
    for bit in 0..256 {
        let value=input[e.base.compression.output[bit/64][bit%64]];
        if value.is_one(){output[bit/8]|=1<<(bit%8);}else if !value.is_zero(){return Err("non-Boolean core digest".into());}
    }Ok(output)
}
fn verify_core(e:&Engine,input:&[Fr])->Result<(),String> {
    if input.len()!=CORE{return Err("core witness length".into());}
    let mut previous=None;let mut value=Fr::zero();
    for term in &e.core.terms {
        if previous!=Some(term.row) {
            if previous.is_some() && !value.is_zero(){return Err(format!("compression residual {:?}",previous));}
            previous=Some(term.row);value=Fr::zero();
        }
        value+=term.gate.evaluate(input);
    }
    if !value.is_zero(){return Err("last compression residual".into());}Ok(())
}
fn add_bytes(values:&mut BTreeMap<usize,Fr>,slot:usize,wires:&[usize],bytes:&[u8;32]) {
    for bit in 0..256 {values.insert(slot*WIDTH+wires[bit],Fr::from(((bytes[bit/8]>>(bit%8))&1) as u64));}
}
fn residuals(e:&Engine,p:&FixedProfile,slot:usize,input:&[Fr],endpoints:&BTreeMap<usize,Fr>,omit:Option<std::ops::Range<usize>>)->Result<Vec<usize>,String> {
    let mut rows=vec![Fr::zero();ROW_WIDTH];
    let get=|index:usize|if (slot*WIDTH+NODE_CORE..slot*WIDTH+NODE_CORE+CORE).contains(&index) {
        input[index-slot*WIDTH-NODE_CORE]
    }else {endpoints.get(&index).copied().unwrap_or(Fr::zero())};
    emit_slot(e,p,slot,|term| {
        let row=term.row-slot*ROW_WIDTH;
        if !omit.as_ref().is_some_and(|r|r.contains(&row)) {
            let x=get(term.gate.left);let y=get(term.gate.right);
            rows[row]+=term.gate.c0+term.gate.c1*x+term.gate.c2*y+term.gate.c3*x*y;
        }
    })?;
    Ok(rows.iter().enumerate().filter_map(|(i,x)|(!x.is_zero()).then_some(i)).collect())
}

#[derive(Clone,Debug,Serialize)]
pub struct TinyEvidence {
    pub headers:usize,pub core_witnesses_checked:usize,pub boundary_slots_checked:usize,
    pub digest_oracle_matches:usize,pub b1_family_rows_checked:usize,pub literal_boundary_terms:usize,
    pub literal_boundary_rows:usize,pub analytic_challenge_sets:usize,pub topology_blake2b256:String,
    pub max_core_witness_capacity_fields:usize,pub max_assigned_core_term_capacity:usize,
    pub max_boundary_slot_terms:usize,pub endpoint_map_entries:usize,pub leaf_hashes_certified:bool,
}

/// Independent bottom-up native preimages; genuine and padding leaf digests are arbitrary inputs.
pub fn tiny_check(e:&Engine,headers:usize)->Result<TinyEvidence,String> {
    let initial=FixedProfile::new(headers,[0;32])?;
    if initial.tree.slots>16{return Err("fixed hash tiny cap S<=16".into());}
    let leaves=(0..initial.tree.leaves).map(|i|std::array::from_fn(|j|((i*41+j*13+7)%256) as u8)).collect::<Vec<[u8;32]>>();
    let mut lower=leaves.clone();let mut native_messages=Vec::new();let mut children=Vec::new();let mut level=1u8;
    while lower.len()>1 {
        let mut upper=Vec::new();
        for (position,pair) in lower.chunks_exact(2).enumerate() {
            let bytes=independent_node(level,position as u32,pair[0],pair[1]);
            upper.push(native_hash(&bytes));native_messages.push(bytes);children.push((pair[0],pair[1]));
        }
        lower=upper;level+=1;
    }
    let p=FixedProfile::new(headers,lower[0])?;let profile_message=independent_profile();
    let profile_digest=native_hash(&profile_message);native_messages.push(profile_message);
    while native_messages.len()<p.tree.slots {native_messages.push(Vec::new());}
    let mut endpoints=BTreeMap::new();
    for (slot,leaf) in leaves.iter().enumerate() {
        add_bytes(&mut endpoints,slot,&e.base.endpoints.leaf,leaf);
        add_bytes(&mut endpoints,slot,&e.base.endpoints.profile,&profile_digest);
    }
    for (slot,(left,right)) in children.iter().enumerate() {
        add_bytes(&mut endpoints,slot,&e.base.endpoints.node_left,left);
        add_bytes(&mut endpoints,slot,&e.base.endpoints.node_right,right);
    }
    let mut evidence=TinyEvidence {headers,core_witnesses_checked:0,boundary_slots_checked:0,digest_oracle_matches:0,
        b1_family_rows_checked:0,literal_boundary_terms:0,literal_boundary_rows:0,analytic_challenge_sets:2,
        topology_blake2b256:String::new(),max_core_witness_capacity_fields:0,max_assigned_core_term_capacity:0,
        max_boundary_slot_terms:0,endpoint_map_entries:0,leaf_hashes_certified:false};
    let mut all_terms=Vec::new();
    for (slot,bytes) in native_messages.iter().enumerate() {
        let assigned=circuit::build_compression(Some(&compression_input(bytes)))?;
        if assigned.layout!=e.base.compression || assigned.compiled.circuit!=e.core {return Err("private compression topology changed".into());}
        let input=assigned.compiled.input.as_ref().ok_or("missing core witness")?;
        verify_core(e,input)?;evidence.core_witnesses_checked+=1;
        let output=core_output(input,e)?;
        if output!=native_hash(bytes){return Err("native BLAKE2b-256 differential mismatch".into());}evidence.digest_oracle_matches+=1;
        if slot<p.tree.leaves {add_bytes(&mut endpoints,slot,&e.base.endpoints.node,&output);}
        if matches!(p.role(slot)?,Role::Dummy) && input.iter().all(Zero::is_zero) {return Err("invalid all-zero dummy".into());}
        if !residuals(e,&p,slot,input,&endpoints,None)?.is_empty(){return Err("honest fixed boundary residual".into());}
        evidence.boundary_slots_checked+=1;
        // Preserve only core coordinates consumed by the unchanged B1 alias families.
        for word in &e.base.compression.message {for &wire in word {endpoints.insert(slot*WIDTH+NODE_CORE+wire,input[wire]);}}
        for word in &e.base.compression.output {for &wire in word {endpoints.insert(slot*WIDTH+NODE_CORE+wire,input[wire]);}}
        let before=all_terms.len();emit_slot(e,&p,slot,|term|all_terms.push(term))?;
        evidence.max_boundary_slot_terms=evidence.max_boundary_slot_terms.max(all_terms.len()-before);
        evidence.max_core_witness_capacity_fields=evidence.max_core_witness_capacity_fields.max(input.capacity());
        evidence.max_assigned_core_term_capacity=evidence.max_assigned_core_term_capacity.max(assigned.compiled.circuit.terms.capacity());
        // assigned template and witness drop here before the next slot.
    }
    evidence.literal_boundary_terms=all_terms.len();
    let mut last=None;for term in &all_terms {if last!=Some(term.row){evidence.literal_boundary_rows+=1;last=Some(term.row);}}
    let counts=count(e,&p)?;
    if counts.total_boundary_terms!=all_terms.len() as u64 || counts.materialized_live_rows!=evidence.literal_boundary_rows as u64 {
        return Err("literal/symbolic boundary count mismatch".into());
    }
    evidence.topology_blake2b256=layout::hash_terms(&all_terms);
    for seed in [3u64,103] {
        let point=|n,s|(0..n).map(|i|Fr::from(s+37*(i as u64+1))).collect::<Vec<_>>();
        let h=p.tree.slot_log();let r=point(11+h,seed);let u=point(20+h,seed+13);let v=point(20+h,seed+67);
        let mut direct=[Fr::zero();4];
        for term in &all_terms {
            let w=topology::eq_index(&r,term.row)*topology::eq_index(&u,term.gate.left)*topology::eq_index(&v,term.gate.right);
            for (out,c) in direct.iter_mut().zip([term.gate.c0,term.gate.c1,term.gate.c2,term.gate.c3]) {*out+=w*c;}
        }
        if coefficients(e,&p,&r,&u,&v)?!=direct {return Err("fixed analytic/enumerated wiring differential".into());}
    }
    let b1=Topology::new(e.base,headers,p.tree.root)?;
    for family in &b1.families {
        let c=family.enumerate(&b1.descriptor,1<<20)?;
        for term in &c.terms {
            let x=endpoints.get(&term.gate.left).copied().unwrap_or(Fr::zero());
            let y=endpoints.get(&term.gate.right).copied().unwrap_or(Fr::zero());
            if !(term.gate.c0+term.gate.c1*x+term.gate.c2*y+term.gate.c3*x*y).is_zero(){
                return Err(format!("B1 compatibility family {}",family.name));
            }
            evidence.b1_family_rows_checked+=1;
        }
    }
    evidence.endpoint_map_entries=endpoints.len();Ok(evidence)
}

pub fn report()->Result<Value,String> {
    let e=engine()?;let mut cases=Vec::new();
    for h in [3,5,6,9] {
        let evidence=tiny_check(e,h)?;let p=FixedProfile::new(h,[0;32])?;
        cases.push(json!({"counts":count(e,&p)?,"evidence":evidence,
            "shape_descriptor_fingerprint_root_zero":p.fingerprint()?}));
    }
    let scenario=FixedProfile::new(1827840,[0;32])?;
    Ok(json!({"profile":"work-tree-fixed-node-profile-hash-v1","scope":"fixed N/profile/dummy compression boundary and B1 endpoint join only",
        "decision":"compiled_fixed_hash_subset_pass","source_blake2b256":{
            "work_tree_fixed_hash.rs":layout::hash_bytes(include_bytes!("work_tree_fixed_hash.rs")),
            "work_tree_layout.rs":layout::hash_bytes(include_bytes!("work_tree_layout.rs")),
            "work_tree_wiring.rs":layout::hash_bytes(include_bytes!("work_tree_wiring.rs")),
            "circuit.rs":layout::hash_bytes(include_bytes!("circuit.rs"))},
        "native_work_sha256":NATIVE_WORK_SHA256,"mainnet_genesis":header_order::MAINNET_GENESIS,
        "cases":cases,"scenario_symbolic_only":count(e,&scenario)?,
        "existing_zero_anchors":"B1 inventory verifies the node bank's old global-zero anchors; this diagnostic emits replacements without mutating the old header boundary",
        "constraint_accounting":"Materialized: 1601*S+256*B rows. Reused B1: 512*(B-1) child aliases and 256*B digest aliases, each one actual retained B1 Term with c1=1,c2=-1. Net new: 1601*S-512*(B-1) rows. The standalone diagnostic reemits each alias as two split-linear Terms: these are separate standalone_reemitted fields. total_boundary_terms counts this standalone emission, not a retained-B1 join. Upper 256 output state bits remain computed by the compression core, with no boundary zero constraint.",
        "dummy_join":"B1 node endpoints remain zero in [B,S); the real empty-message compression output has no endpoint alias there",
        "pending":PENDING,"historical_witness_generated":false,"global_proof_generated":false,
        "observed_process_peak":"external bounded watchdog; in-file capacities are allocations, not RSS"}))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test] fn work_tree_fixed_hash_descriptor_roles_and_no_private_topology() {
        for h in [3,5,6,9] {
            let p=FixedProfile::new(h,[0;32]).unwrap();let b=p.tree.leaves;
            assert_eq!(p.role(b-1).unwrap(),Role::Profile);
            for slot in b..p.tree.slots {assert_eq!(p.role(slot).unwrap(),Role::Dummy);}
            let mut invalid=p.clone();invalid.genesis[0]^=1;assert!(invalid.validate().is_err());
            let mut invalid=p.clone();invalid.prefix[0]^=1;assert!(invalid.validate().is_err());
            let mut invalid=p.clone();invalid.dummy_final=false;assert!(invalid.validate().is_err());
            assert!(p.role(p.tree.slots).is_err());
        }
    }
    #[test] fn work_tree_fixed_hash_real_cores_native_oracle_and_b1_join() {
        let e=engine().unwrap();
        for h in [3,5,6,9] {
            let evidence=tiny_check(e,h).unwrap();
            assert_eq!(evidence.core_witnesses_checked,Descriptor::new(h,[0;32]).unwrap().slots);
            assert_eq!(evidence.core_witnesses_checked,evidence.digest_oracle_matches);
            assert!(evidence.b1_family_rows_checked>0);assert!(!evidence.leaf_hashes_certified);
        }
    }
    #[test] fn work_tree_fixed_hash_role_kernel_zero_factors_and_large_dimension() {
        for h in [3,5,6,9] {
            let p=FixedProfile::new(h,[0;32]).unwrap();let n=p.tree.slot_log();
            for point in [vec![Fr::zero();n],vec![Fr::one();n],vec![Fr::from(7u64);n]] {
                for two in [false,true] {
                    let points=if two {vec![point.as_slice(),point.as_slice()]}else {vec![point.as_slice()]};
                    let sums=role_weights(&p,&points).unwrap();let mut direct=[Fr::zero();3];
                    let mut levels=[Fr::zero();8];let mut positions=[Fr::zero();32];
                    for slot in 0..p.tree.slots {
                        let w=points.iter().map(|v|topology::eq_index(v,slot)).product::<Fr>();
                        match p.role(slot).unwrap() {
                            Role::Node {level,position}=>{direct[0]+=w;
                                for bit in 0..8 {if (level>>bit)&1!=0 {levels[bit]+=w;}}
                                for bit in 0..32 {if (position>>bit)&1!=0 {positions[bit]+=w;}}},
                            Role::Profile=>direct[1]+=w,Role::Dummy=>direct[2]+=w,
                        }
                    }
                    assert_eq!(sums.node,direct[0]);assert_eq!(sums.profile,direct[1]);assert_eq!(sums.all-sums.active,direct[2]);
                    assert_eq!(sums.level,levels);assert_eq!(sums.position,positions);
                }
            }
        }
        let e=engine().unwrap();let p=FixedProfile::new(1827840,[0;32]).unwrap();let h=p.tree.slot_log();
        assert!(coefficients(e,&p,&vec![Fr::from(3u64);11+h],&vec![Fr::from(11u64);20+h],&vec![Fr::from(7u64);20+h]).is_ok());
        assert_eq!(count(e,&p).unwrap().additional_witness_bits,0);
    }

    #[test] fn work_tree_fixed_hash_isolated_valid_core_boundary_mutants_and_omissions() {
        let e=engine().unwrap();let p=FixedProfile::new(3,[0;32]).unwrap();
        let left=[0x11;32];let right=[0x77;32];
        let cases=[("tag",0,512..520),("level",0,520..528),("position",0,528..560),
            ("child_order",0,560..1072),("iv",0,0..512),("counter",0,1536..1600),
            ("final",0,1600..1601),("tail",0,1072..1536),("genesis",1,728..984),
            ("profile_prefix",1,512..728),("digest",0,1601..1857),("profile_digest",1,1601..1857),
            ("profile_counter",1,1536..1600),("profile_tail",1,984..1536),
            ("dummy_counter",2,1536..1600),("dummy_tail",2,512..1536)];
        for (name,slot,omitted) in cases {
            let bytes=match slot {0=>independent_node(1,0,left,right),1=>independent_profile(),_=>Vec::new()};
            let mut input=compression_input(&bytes);
            match name {
                "tag"=>input.block[0]^=1,"level"=>input.block[1]^=1,"position"=>input.block[5]^=1,
                "child_order"=>{input.block[6..38].copy_from_slice(&right);input.block[38..70].copy_from_slice(&left);},
                "iv"=>input.state[0]^=1,"counter"|"profile_counter"|"dummy_counter"=>input.counter^=1,
                "final"=>input.final_flag=false,"tail"=>input.block[70]=1,"genesis"=>input.block[27]^=1,
                "profile_prefix"=>input.block[0]^=1,"profile_tail"=>input.block[59]=1,"dummy_tail"=>input.block[127]=1,_=>{}
            }
            let assigned=circuit::build_compression(Some(&input)).unwrap();
            assert_eq!(assigned.compiled.circuit,e.core);let witness=assigned.compiled.input.as_ref().unwrap();verify_core(e,witness).unwrap();
            let mut endpoints=BTreeMap::new();
            add_bytes(&mut endpoints,0,&e.base.endpoints.node_left,&left);add_bytes(&mut endpoints,0,&e.base.endpoints.node_right,&right);
            if slot<p.tree.leaves {
                let mut digest=core_output(witness,e).unwrap();if name=="digest"||name=="profile_digest" {digest[0]^=1;}
                add_bytes(&mut endpoints,slot,&e.base.endpoints.node,&digest);
            }
            let failed=residuals(e,&p,slot,witness,&endpoints,None).unwrap();
            assert!(!failed.is_empty(),"{name}");assert!(failed.iter().all(|r|omitted.contains(r)),"{name}: {failed:?}");
            assert!(residuals(e,&p,slot,witness,&endpoints,Some(omitted)).unwrap().is_empty(),"omission {name}");
        }
    }
    #[test] fn work_tree_fixed_hash_boundary_only_trace_corruption_is_not_core_acceptance() {
        let e=engine().unwrap();let p=FixedProfile::new(3,[0;32]).unwrap();
        let assigned=circuit::build_compression(Some(&compression_input(&[]))).unwrap();
        let mut witness=assigned.compiled.input.unwrap();
        assert!(residuals(e,&p,2,&witness,&BTreeMap::new(),None).unwrap().is_empty());
        let output=core_output(&witness,e).unwrap();assert_eq!(output,native_hash(&[]));assert_ne!(output,[0;32]);
        // A private intermediate absent from the boundary must still be checked by the core.
        let protected=e.base.compression.state.iter().flatten().chain(e.base.compression.message.iter().flatten())
            .chain(&e.base.compression.counter).chain(std::iter::once(&e.base.compression.final_flag))
            .chain(e.base.compression.output.iter().flatten()).copied().collect::<std::collections::BTreeSet<_>>();
        let intermediate=(e.base.compression.final_flag+1..e.base.compression.used_input_len).find(|w|!protected.contains(w)).unwrap();
        witness[intermediate]=Fr::one()-witness[intermediate];
        assert!(residuals(e,&p,2,&witness,&BTreeMap::new(),None).unwrap().is_empty());assert!(verify_core(e,&witness).is_err());
    }
}

//! Bounded tiny owner writer; the dense builder remains the independent oracle.
use super::{be28, S, WIDTH};
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use ergo_header_core::Header;
use num_bigint::BigUint;
use std::{collections::BTreeMap, path::Path};
use crate::{daa_history_layout::HeaderAssignmentTemplate, header_order::MAINNET_GENESIS,
    packed::{PackedFile, PackedFileWriter}, serializer::Fields, work_tree_fixed_hash as fixed,
    work_tree_history_plan::WorkTreeHistoryPlan, work_tree_leaf_hash as leaf, work_tree_work as work};

const BLOCK: usize = WIDTH / 8;
type Sink<'a> = dyn FnMut(usize, &[u8]) -> Result<(), String> + 'a;
fn require(ok: bool, error: &str) -> Result<(), String> { if ok {Ok(())} else {Err(error.into())} }
fn leaf_digest(role: leaf::Role, actual: [u8;32], native: [u8;32])->Result<(),String>{
    require(actual==if role==leaf::Role::Dummy {[0;32]}else{native},"stream40 assigned leaf digest")
}
fn fixed_digest(actual: [u8;32], native: [u8;32])->Result<(),String>{
    require(actual==native,"stream40 assigned fixed digest")
}
fn root_digest(owner:usize,root_owner:usize,actual:[u8;32],root:[u8;32])->Result<(),String>{
    require(owner!=root_owner||actual==root,"stream40 assigned root")
}
fn replacement_mask(mask:&Vec<bool>)->Result<(),String>{
    require(mask.len()==WIDTH && mask.capacity()<=WIDTH,"stream40 replacement mask capacity")?;
    require(mask.iter().filter(|v|**v).count()==401362 && !mask[991232..999424].iter().any(|v|*v),
        "stream40 replacement mask contract")
}
fn final_work(lower:&BigUint,total:[u8;28])->Result<(),String>{
    require(be28(lower)?==total,"stream40 final work")
}
// Admit the immutable plan tuple before allocating its local permission mask.
pub(crate) fn assignment_mask_profile(headers:u64,h:usize,slots:usize)->Result<(),String>{
    require(matches!((headers,h,slots),(3|4,2,4)|(5|8,3,8)),"scaling43 assignment mask profile")
}
pub(crate) fn assignment_mask(plan:&WorkTreeHistoryPlan)->Result<Vec<bool>,String>{
    assignment_mask_profile(plan.headers(),plan.slot_log(),plan.slots())?;
    if plan.slots()==4 {plan.assignment_replacement_mask()}
    else {plan.physical_assignment_replacement_mask(0)}
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct NativeSummary {
    pub headers: usize, pub root: [u8;32], pub total: [u8;28], pub tip: [u8;32], pub tip_time: i64,
}
#[derive(Default, Clone, Debug, serde::Serialize)]
pub(crate) struct WriterStats {
    pub sink_calls: usize, pub written_bytes: usize, pub finish_observed: bool,
    pub output_capacity_peak: usize, pub seen_capacity_peak: usize, pub mask_capacity: usize,
    pub header_capacity_peak: usize, pub local_map_peak: usize, pub frontier_peak: usize,
    pub native_scans: usize, pub scan_leaf_hashes: usize, pub scan_node_hashes: usize,
}
impl WriterStats {
    fn scan(&mut self, scan: &NativeScan<'_>) {
        self.native_scans+=1;self.scan_leaf_hashes+=scan.next;
        self.scan_node_hashes+=scan.nodes;self.frontier_peak=self.frontier_peak.max(scan.peak);
    }
}
#[derive(Clone, Copy)]
struct Node { start: usize, level: usize, digest: [u8;32] }
struct NativeScan<'a> {
    headers: &'a [Header], leaf: &'a leaf::LeafProfile, fixed: &'a fixed::FixedProfile,
    profile: [u8;32], next: usize, lower: BigUint,
    frontier: [Option<Node>;4], peak: usize, nodes: usize,
}
impl<'a> NativeScan<'a> {
    fn new(headers: &'a [Header], p: &'a leaf::LeafProfile, f: &'a fixed::FixedProfile, profile: [u8;32]) -> Self {
        Self {headers,leaf:p,fixed:f,profile,next:0,lower:BigUint::from(0u64),frontier:[None;4],peak:0,nodes:0}
    }
    fn next_node(&mut self, target: usize) -> Result<Option<(usize,Vec<u8>,[u8;32])>,String> {
        require((1..=self.leaf.tree.slot_log()).contains(&target) && target<=3,"stream40 target level")?;
        while self.next<self.leaf.tree.leaves {
            let slot=self.next;self.next+=1;
            let digest=if slot<self.leaf.tree.genuine {
                let header=&self.headers[slot+1];let difficulty=work::native_decode(header.n_bits)?;
                let upper=&self.lower+&difficulty;
                let digest=leaf::native_leaf_preimage_hash(self.leaf,slot,&header.encode().map_err(|e|format!("{e:?}"))?,
                    header.height,be28(&self.lower)?,be28(&upper)?,self.profile)?;
                self.lower=upper;digest
            }else{leaf::native_leaf_preimage_hash(self.leaf,slot,&[],0,[0;28],[0;28],self.profile)?};
            let mut node=Node{start:slot,level:0,digest};
            loop {
                require(node.level<self.frontier.len(),"stream40 frontier level")?;
                if let Some(left)=self.frontier[node.level].take() {
                    require(left.level==node.level && left.start+(1usize<<node.level)==node.start,"stream40 frontier siblings")?;
                    let level=node.level+1;let position=left.start>>level;
                    let (base,_)=self.leaf.tree.level(level)?;let owner=base+position;
                    let mut bytes=vec![b'N',level as u8];bytes.extend_from_slice(&(position as u32).to_be_bytes());
                    bytes.extend_from_slice(&left.digest);bytes.extend_from_slice(&node.digest);
                    let digest=leaf::native_fixed_preimage_hash(self.fixed,owner,&bytes)?;self.nodes+=1;
                    if level==target {return Ok(Some((owner,bytes,digest)));}
                    node=Node{start:left.start,level,digest};
                }else{
                    self.frontier[node.level]=Some(node);
                    self.peak=self.peak.max(self.frontier.iter().filter(|v|v.is_some()).count());break;
                }
            }
        }
        require(self.frontier.iter().all(Option::is_none),"stream40 incomplete frontier")?;
        Ok(None)
    }
}
struct Prepared {
    summary: NativeSummary, leaf: leaf::LeafProfile, fixed: fixed::FixedProfile,
    profile_bytes: Vec<u8>, profile: [u8;32], levels: usize, stats: WriterStats,
}
fn prepare(headers: &[Header]) -> Result<Prepared,String> {
    require(matches!(headers.len(),3|4),"stream40 header count")?;
    prepare_closed(headers,2)
}
fn prepare_closed(headers:&[Header],h:usize)->Result<Prepared,String>{
    require(matches!((headers.len(),h),(3|4,2)|(5|8,3)),"scaling41 writer profile")?;
    let mut previous=[0;32];
    for (i,header) in headers.iter().enumerate() {
        let raw=header.encode().map_err(|e|format!("{e:?}"))?;
        require(!raw.is_empty() && raw.len()<=514,"stream40 canonical raw extent")?;
        let decoded=Header::decode(&raw,None).map_err(|e|format!("{e:?}"))?;
        require(decoded.encode().map_err(|e|format!("{e:?}"))?==raw && header.height as usize==i+1
            && header.parent_id==previous,"stream40 canonical height/parent")?;
        previous=ergo_header_core::blake2b256(&raw);
        require(i!=0 || previous==MAINNET_GENESIS,"stream40 genesis")?;
    }
    let n=headers.len();let p=leaf::LeafProfile::new(n,[0;32])?;let f=fixed::FixedProfile::new(n,[0;32])?;
    require(p.tree.slots==1usize<<h && p.tree.slot_log()==h,"stream40 tiny geometry")?;
    let mut profile_bytes=fixed::PROFILE_PREFIX.to_vec();profile_bytes.extend_from_slice(&MAINNET_GENESIS);
    let profile=leaf::native_fixed_preimage_hash(&f,p.tree.profile_node_slot,&profile_bytes)?;
    let levels=p.tree.leaves.trailing_zeros() as usize;
    let (root,total,stats)={let mut scan=NativeScan::new(headers,&p,&f,profile);
        let (owner,_,root)=scan.next_node(levels)?.ok_or("stream40 root absent")?;
        require(owner==p.tree.root_node_slot && scan.next_node(levels)?.is_none(),"stream40 root descriptor")?;
        let total=be28(&scan.lower)?;let mut stats=WriterStats::default();stats.scan(&scan);(root,total,stats)};
    Ok(Prepared{summary:NativeSummary{headers:n,root,total,tip:previous,tip_time:headers[n-1].timestamp},
        leaf:p,fixed:f,profile_bytes,profile,levels,stats})
}
struct FixedCursor<'a> { prepared: &'a Prepared, headers: &'a [Header], level: usize, scan: NativeScan<'a>, done: WriterStats }
impl<'a> FixedCursor<'a> {
    fn new(p: &'a Prepared, headers: &'a [Header]) -> Self {
        Self{prepared:p,headers,level:1,scan:NativeScan::new(headers,&p.leaf,&p.fixed,p.profile),done:WriterStats::default()}
    }
    fn preimage(&mut self, owner: usize) -> Result<(Vec<u8>,[u8;32]),String> {
        let p=self.prepared;
        if owner>=p.leaf.tree.profile_node_slot {
            let bytes=if owner==p.leaf.tree.profile_node_slot {p.profile_bytes.clone()}else{Vec::new()};
            let digest=leaf::native_fixed_preimage_hash(&p.fixed,owner,&bytes)?;return Ok((bytes,digest));
        }
        loop {
            if let Some((actual,bytes,digest))=self.scan.next_node(self.level)? {
                require(actual==owner,"stream40 fixed owner order")?;return Ok((bytes,digest));
            }
            self.done.scan(&self.scan);self.level+=1;
            require(self.level<=p.levels,"stream40 fixed cursor exhausted")?;
            self.scan=NativeScan::new(self.headers,&p.leaf,&p.fixed,p.profile);
        }
    }
    fn stats(&self, stats: &mut WriterStats) {
        stats.native_scans+=self.done.native_scans;stats.scan_leaf_hashes+=self.done.scan_leaf_hashes;
        stats.scan_node_hashes+=self.done.scan_node_hashes;stats.frontier_peak=stats.frontier_peak.max(self.done.frontier_peak);
        stats.scan(&self.scan);
    }
}
struct OwnerBits { owner: usize, bits: Vec<u8>, seen: Vec<u8> }
impl OwnerBits {
    fn new(owner: usize) -> Result<Self,String> {
        Self::new_for(owner,S)
    }
    fn new_for(owner:usize,slots:usize)->Result<Self,String>{
        require(matches!(slots,4|8) && owner<slots,"stream40 owner")?;
        Ok(Self{owner,bits:vec![0;BLOCK],seen:vec![0;BLOCK]})
    }
    fn put(&mut self, wire: usize, value: Fr) -> Result<(),String> {
        require(self.owner<8 && wire<WIDTH,"stream40 local wire")?;
        require(value.is_zero()||value.is_one(),"stream40 non-Boolean")?;
        let byte=wire/8;let mask=1u8<<(wire%8);let one=value.is_one();
        require(self.seen[byte]&mask==0 || (self.bits[byte]&mask!=0)==one,"stream40 conflicting assignment")?;
        self.seen[byte]|=mask;if one {self.bits[byte]|=mask;}Ok(())
    }
    fn map(&mut self, values: BTreeMap<usize,Fr>, stats: &mut WriterStats) -> Result<(),String> {
        require(values.len()<=WIDTH,"stream40 local map extent")?;stats.local_map_peak=stats.local_map_peak.max(values.len());
        for (wire,value) in values {self.put(wire,value)?;}Ok(())
    }
    fn integer(&mut self, wires: &[usize], value: &BigUint) -> Result<(),String> {
        for (bit,wire) in wires.iter().enumerate(){self.put(*wire,Fr::from(value.bit(bit as u64) as u64))?;}Ok(())
    }
}
fn emit_owners(headers: &[Header], p: &Prepared, sink: &mut Sink<'_>) -> Result<(NativeSummary,WriterStats),String> {
    let engine=fixed::engine()?;let e=&engine.base.endpoints;
    let mask={let plan=WorkTreeHistoryPlan::compile(p.summary.headers as u64,p.leaf.tree.slot_log(),p.summary.root,p.summary.total)?;
        assignment_mask(&plan)?}; // Parent graph drops before template construction.
    replacement_mask(&mask)?;
    let template=HeaderAssignmentTemplate::new()?;
    let boundary=leaf::compile(engine,p.leaf.clone())?;
    let mut cursor=FixedCursor::new(p,headers);let mut stats=p.stats.clone();stats.mask_capacity=mask.capacity();
    let mut lower=BigUint::from(0u64);
    for owner in 0..p.leaf.tree.slots {
        let mut bits=OwnerBits::new_for(owner,p.leaf.tree.slots)?;
        stats.output_capacity_peak=stats.output_capacity_peak.max(bits.bits.capacity());
        stats.seen_capacity_peak=stats.seen_capacity_peak.max(bits.seen.capacity());
        require(bits.bits.capacity()==BLOCK && bits.seen.capacity()==BLOCK,"stream40 owner capacity")?;
        if owner<p.leaf.tree.genuine {
            let header=&headers[owner+1];let difficulty=work::native_decode(header.n_bits)?;
            require(difficulty!=BigUint::from(0u64),"stream40 zero difficulty")?;let upper=&lower+&difficulty;
            let assigned=leaf::assign_header_leaf(engine,&boundary,owner,header,be28(&lower)?,be28(&upper)?,p.profile)?;
            let digest=leaf::native_leaf_preimage_hash(&p.leaf,owner,&header.encode().map_err(|e|format!("{e:?}"))?,
                header.height,be28(&lower)?,be28(&upper)?,p.profile)?;
            leaf_digest(leaf::Role::Genuine,assigned.digest,digest)?;bits.map(assigned.values,&mut stats)?;
            bits.integer(&e.n_bits,&BigUint::from(header.n_bits))?;bits.integer(&e.lower,&lower)?;
            bits.integer(&e.upper,&upper)?;bits.integer(&e.work,&difficulty)?;
            bits.integer(&e.work_minus_one,&(&difficulty-BigUint::from(1u64)))?;
            bits.put(e.exponent[(header.n_bits>>24) as usize],Fr::one())?;lower=upper;
        }else{
            let assigned=if p.leaf.tree.slots==4{leaf::assign_inactive_leaf_for_prefix(engine,&boundary,owner,p.profile)?}
                else{leaf::assign_inactive_leaf(engine,&boundary,owner,p.profile)?};
            let expected=leaf::native_leaf_preimage_hash(&p.leaf,owner,&[],0,[0;28],[0;28],p.profile)?;
            leaf_digest(p.leaf.role(owner)?,assigned.digest,expected)?;bits.map(assigned.values,&mut stats)?;
        }
        let (preimage,digest)=cursor.preimage(owner)?;
        let assigned=if p.leaf.tree.slots==4{leaf::assign_fixed_slot_for_prefix(engine,&p.fixed,owner,&preimage)?}
            else{leaf::assign_fixed_slot_native(engine,&p.fixed,owner,&preimage)?};
        fixed_digest(assigned.digest,digest)?;
        root_digest(owner,p.leaf.tree.root_node_slot,assigned.digest,p.summary.root)?;
        bits.map(assigned.values,&mut stats)?;
        {let i=owner.min(headers.len()-1);let fields=Fields::from_header(&headers[i])?;
            let mut input=template.assign(&fields)?;
            let (height,time,first)=if i==0 {(0,0,true)}else{(headers[i-1].height,headers[i-1].timestamp,false)};
            template.assign_order(&mut input,&fields,height,time,first)?;
            require(input.len()==WIDTH && input.capacity()<=WIDTH,"stream40 header capacity")?;
            stats.header_capacity_peak=stats.header_capacity_peak.max(input.capacity()*32);
            for (wire,value) in input.into_iter().enumerate(){if !mask[wire]{bits.put(wire,value)?;}}
        } // No assignment map or header Vec remains during a sink call.
        sink(owner,&bits.bits)?;
    }
    final_work(&lower,p.summary.total)?;cursor.stats(&mut stats);
    require(stats.native_scans<=p.levels+1,"stream40 native scan bound")?;
    Ok((p.summary.clone(),stats))
}
fn owned_output(path: &Path, operation: impl FnOnce(&mut Sink<'_>)->Result<(NativeSummary,WriterStats),String>)
    ->Result<(PackedFile,NativeSummary,WriterStats),String>{
    owned_output_closed(path,2,operation)
}
fn owned_output_closed(path:&Path,h:usize,operation:impl FnOnce(&mut Sink<'_>)->Result<(NativeSummary,WriterStats),String>)
    ->Result<(PackedFile,NativeSummary,WriterStats),String>{
    require(matches!(h,2|3),"scaling41 writer dimension")?;let slots=1usize<<h;
    let mut writer=PackedFileWriter::create_new(path,20+h)?;let mut count=0usize;let mut bytes=0usize;
    let (summary,mut stats)=operation(&mut |owner,block| {
        require(owner==count && owner<slots,"stream40 sink owner order")?;
        require(block.len()==BLOCK,"stream40 sink block extent")?;
        writer.write_bytes(block)?;count+=1;bytes+=block.len();Ok(())
    })?;
    require(count==slots && bytes==slots*BLOCK,"stream40 sink completion")?;
    let source=writer.finish()?;stats.finish_observed=true;stats.sink_calls=count;stats.written_bytes=bytes;
    Ok((source,summary,stats))
}
pub(crate) fn write_packed(headers: &[Header], path: &Path)->Result<(PackedFile,NativeSummary,WriterStats),String>{
    let prepared=prepare(headers)?;
    owned_output(path,|sink|emit_owners(headers,&prepared,sink))
}

// Sealed N5/N8 TESTONLY entry. The old H2 entry never infers this policy.
pub(crate) fn write_h3_packed(headers:&[Header],path:&Path)->Result<(PackedFile,NativeSummary,WriterStats),String>{
    require(matches!(headers.len(),5|8),"scaling41 writer headers")?;
    let p=prepare_closed(headers,3)?;owned_output_closed(path,3,|sink|emit_owners(headers,&p,sink))
}
pub(crate) fn h3_writer_controls()->Result<usize,String>{
    require(prepare_closed(&[],3).err().as_deref()==Some("scaling41 writer profile"),"scaling41 writer guard attribution")?;
    require(OwnerBits::new_for(8,8).err().as_deref()==Some("stream40 owner"),"scaling41 owner guard attribution")?;
    let mut a=OwnerBits::new_for(4,8)?;a.put(0,Fr::zero())?;
    require(a.put(0,Fr::one()).err().as_deref()==Some("stream40 conflicting assignment"),"scaling41 owner4 conflict attribution")?;
    let path=std::env::temp_dir().join(format!("scaling41-sink-{}.bits",std::process::id()));
    require(!path.exists(),"scaling41 sink fixture exists")?;
    for fault in 0..3 {
        let result=owned_output_closed(&path,3,|sink|{
            let block=vec![0;BLOCK];
            if fault==0{sink(4,&block)?;}else if fault==1{sink(0,&block)?;sink(0,&block)?;}
            else{for owner in 0..8{sink(owner,&block)?;}return Err("scaling41 post-final sink".into());}
            Err("scaling41 sink unexpectedly reached".into())
        });
        require(result.err().as_deref()==Some(if fault==2{"scaling41 post-final sink"}else{"stream40 sink owner order"}),
            "scaling41 sink guard attribution")?;
        require(!path.exists(),"scaling41 failed sink retained finalizable file")?;
    }
    Ok(6)
}

// New-depth attribution uses valid H3 preparation, with one local mutation at
// a time. It runs in the full trial's writer phase, before the real writer.
pub(crate) fn h3_prepared_controls(headers:&[Header])->Result<usize,String>{
    fn rejected<T>(r:Result<T,String>,expected:&str)->Result<(),String>{
        require(r.err().as_deref()==Some(expected),"scaling41 prepared fault attribution")
    }
    require(matches!(headers.len(),5|8),"scaling41 writer headers")?;
    let p=prepare_closed(headers,3)?;let mut faults=0;
    {let mask={let plan=WorkTreeHistoryPlan::compile(headers.len() as u64,3,p.summary.root,p.summary.total)?;
            assignment_mask(&plan)?};replacement_mask(&mask)?;
        let mut bad=mask.clone();let active=bad.iter().position(|v|*v).ok_or("scaling41 missing replaced wire")?;
        require(!bad[991232],"scaling41 protected fixture")?;bad[active]=false;bad[991232]=true;
        require(bad.iter().filter(|v|**v).count()==401362,"scaling41 protected cardinality")?;
        rejected(replacement_mask(&bad),"stream40 replacement mask contract")?;faults+=1;}
    {let mut scan=NativeScan::new(headers,&p.leaf,&p.fixed,p.profile);scan.lower=BigUint::from(1u64);
        let(_,_,wrong)=scan.next_node(p.levels)?.ok_or("scaling41 shifted root")?;
        rejected(root_digest(p.leaf.tree.root_node_slot,p.leaf.tree.root_node_slot,wrong,p.summary.root),"stream40 assigned root")?;faults+=1;}
    {let mut total=p.summary.total;total[27]^=1;
        rejected(final_work(&BigUint::from_bytes_be(&p.summary.total),total),"stream40 final work")?;faults+=1;}
    {let mut cursor=FixedCursor::new(&p,headers);let(mut bytes,digest)=cursor.preimage(0)?;bytes[6]^=1;
        rejected(fixed_digest(digest,leaf::native_fixed_preimage_hash(&p.fixed,0,&bytes)?),"stream40 assigned fixed digest")?;faults+=1;}
    {let mut bytes=p.profile_bytes.clone();bytes[0]^=1;
        rejected(leaf::native_fixed_preimage_hash(&p.fixed,p.leaf.tree.profile_node_slot,&bytes),"fixed profile preimage differs from exact prefix/genesis")?;faults+=1;}
    {let engine=fixed::engine()?;let boundary=leaf::compile(engine,p.leaf.clone())?;
        rejected(leaf::assign_header_leaf(engine,&boundary,1,&headers[1],[0;28],[0;28],p.profile),"header height does not match leaf position")?;faults+=1;
        let upper=be28(&work::native_decode(headers[1].n_bits)?)?;
        let expected=leaf::native_leaf_preimage_hash(&p.leaf,0,&headers[1].encode().map_err(|e|format!("{e:?}"))?,2,[0;28],upper,p.profile)?;
        let wrong={let mut header=headers[1].clone();header.timestamp^=1;
            leaf::assign_header_leaf(engine,&boundary,0,&header,[0;28],upper,p.profile)?.digest};
        rejected(leaf_digest(leaf::Role::Genuine,wrong,expected),"stream40 assigned leaf digest")?;faults+=1;
        if headers.len()==8{
            rejected(leaf::assign_header_leaf(engine,&boundary,4,&headers[4],[0;28],[0;28],p.profile),"header height does not match leaf position")?;faults+=1;
            let expected=leaf::native_leaf_preimage_hash(&p.leaf,7,&[],0,[0;28],[0;28],p.profile)?;
            let mut bytes=vec![b'P'];bytes.extend(p.profile);bytes.extend(8u32.to_be_bytes());bytes.extend(6u32.to_be_bytes());
            let wrong=ergo_header_core::blake2b256(&bytes);
            rejected(leaf_digest(leaf::Role::Padding,wrong,expected),"stream40 assigned leaf digest")?;faults+=1;
        }else{
            require(p.leaf.role(4)?==leaf::Role::Dummy,"scaling41 dummy owner fixture")?;
            rejected(leaf_digest(leaf::Role::Dummy,[1;32],[0;32]),"stream40 assigned leaf digest")?;faults+=1;
        }
    }
    {let mask={let plan=WorkTreeHistoryPlan::compile(headers.len() as u64,3,p.summary.root,p.summary.total)?;
            assignment_mask(&plan)?};let template=HeaderAssignmentTemplate::new()?;
        let retained=|i:usize|->Result<Vec<u8>,String>{let fields=Fields::from_header(&headers[i])?;let mut input=template.assign(&fields)?;
            template.assign_order(&mut input,&fields,headers[i-1].height,headers[i-1].timestamp,false)?;
            require(input.len()==WIDTH&&input.capacity()<=WIDTH,"stream40 header capacity")?;
            let mut bits=OwnerBits::new_for(4,8)?;for(wire,value)in input.into_iter().enumerate(){if !mask[wire]{bits.put(wire,value)?;}}Ok(bits.bits)};
        let correct=retained(4)?;let wrong=retained(3)?;
        require(correct!=wrong,"scaling41 owner4 header/leaf index comparator")?;faults+=1;
    }
    require(faults==if headers.len()==5{9}else{10},"scaling41 prepared negative census")?;Ok(faults)
}

// Reached heavy controls run only in the isolated differential, after its
// dense oracle drops. Each faulty channel uses an unchanged prepared reference.
pub(crate) fn differential_controls(headers:&[Header])->Result<usize,String>{
    fn rejected<T>(result:Result<T,String>,error:&str)->Result<(),String>{
        require(result.err().as_deref()==Some(error),"stream40 negative attribution")
    }
    let p=prepare(headers)?;let mut faults=0;
    let mask={let plan=WorkTreeHistoryPlan::compile(p.summary.headers as u64,2,p.summary.root,p.summary.total)?;
        plan.assignment_replacement_mask()?};
    replacement_mask(&mask)?;
    {let mut changed=mask.clone();let active=mask.iter().position(|v|*v).ok_or("stream40 missing replaced wire")?;
        require(!changed[991232],"stream40 protected fixture")?;changed[active]=false;changed[991232]=true;
        require(changed.iter().filter(|v|**v).count()==401362,"stream40 protected cardinality")?;
        rejected(replacement_mask(&changed),"stream40 replacement mask contract")?;faults+=1;}
    {let mut shifted=NativeScan::new(headers,&p.leaf,&p.fixed,p.profile);shifted.lower=BigUint::from(1u64);
        let (_,_,wrong)=shifted.next_node(p.levels)?.ok_or("stream40 shifted root")?;
        rejected(root_digest(p.leaf.tree.root_node_slot,p.leaf.tree.root_node_slot,wrong,p.summary.root),"stream40 assigned root")?;faults+=1;}
    {let mut total=p.summary.total;total[27]^=1;
        rejected(final_work(&BigUint::from_bytes_be(&p.summary.total),total),"stream40 final work")?;faults+=1;}
    {let mut cursor=FixedCursor::new(&p,headers);let (mut bytes,digest)=cursor.preimage(0)?;bytes[6]^=1;
        let wrong=leaf::native_fixed_preimage_hash(&p.fixed,0,&bytes)?;
        rejected(fixed_digest(digest,wrong),"stream40 assigned fixed digest")?;faults+=1;}
    {let mut bytes=p.profile_bytes.clone();bytes[0]^=1;
        rejected(leaf::native_fixed_preimage_hash(&p.fixed,p.leaf.tree.profile_node_slot,&bytes),
            "fixed profile preimage differs from exact prefix/genesis")?;faults+=1;}
    {let engine=fixed::engine()?;let boundary=leaf::compile(engine,p.leaf.clone())?;
        rejected(leaf::assign_header_leaf(engine,&boundary,1,&headers[1],[0;28],[0;28],p.profile),
            "header height does not match leaf position")?;faults+=1;
        let upper=be28(&work::native_decode(headers[1].n_bits)?)?;
        let expected=leaf::native_leaf_preimage_hash(&p.leaf,0,&headers[1].encode().map_err(|e|format!("{e:?}"))?,
            2,[0;28],upper,p.profile)?;
        let wrong={let mut header=headers[1].clone();header.timestamp^=1;
            leaf::assign_header_leaf(engine,&boundary,0,&header,[0;28],upper,p.profile)?.digest};
        rejected(leaf_digest(leaf::Role::Genuine,wrong,expected),"stream40 assigned leaf digest")?;faults+=1;
        if headers.len()==4 {
            let expected=leaf::native_leaf_preimage_hash(&p.leaf,3,&[],0,[0;28],[0;28],p.profile)?;
            let wrong=leaf::assign_padding_position_fault_for_prefix(engine,&boundary,3,p.profile)?.digest;
            rejected(leaf_digest(leaf::Role::Padding,wrong,expected),"stream40 assigned leaf digest")?;faults+=1;
        }
    } // No local assignment map/boundary survives template construction.
    {let template=HeaderAssignmentTemplate::new()?;
        let retained=|i:usize|->Result<Vec<u8>,String>{
            let fields=Fields::from_header(&headers[i])?;let mut input=template.assign(&fields)?;
            let (height,time,first)=if i==0 {(0,0,true)}else{(headers[i-1].height,headers[i-1].timestamp,false)};
            template.assign_order(&mut input,&fields,height,time,first)?;
            require(input.len()==WIDTH && input.capacity()<=WIDTH,"stream40 header capacity")?;
            let mut bits=OwnerBits::new(1)?;for (wire,value) in input.into_iter().enumerate(){if !mask[wire]{bits.put(wire,value)?;}}
            Ok(bits.bits)
        };
        let correct=retained(1)?;let wrong=retained(0)?;
        require(correct!=wrong,"stream40 retained header-index comparator")?;faults+=1;
    }
    require(faults==if headers.len()==3{8}else{9},"stream40 negative census")?;Ok(faults)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn owner_boundaries(){
        assert_eq!(OwnerBits::new(S).err().unwrap(),"stream40 owner");
        let mut bits=OwnerBits::new(0).unwrap();
        for wire in [0,7,8,65535,65536,WIDTH-1]{bits.put(wire,Fr::zero()).unwrap();bits.put(wire,Fr::zero()).unwrap();
            assert_eq!(bits.put(wire,Fr::one()).err().unwrap(),"stream40 conflicting assignment");}
        let mut other=OwnerBits::new(3).unwrap();
        for wire in [0,7,8,65535,65536,WIDTH-1]{other.put(wire,Fr::one()).unwrap();
            assert_eq!(other.put(wire,Fr::zero()).err().unwrap(),"stream40 conflicting assignment");
            assert_ne!(other.bits[wire/8]&(1<<(wire%8)),0);}
        assert!(bits.bits.iter().all(|b|*b==0));
        assert_eq!(bits.put(WIDTH,Fr::zero()).err().unwrap(),"stream40 local wire");
        assert_eq!(bits.put(1,Fr::from(2u64)).err().unwrap(),"stream40 non-Boolean");
        let headers=super::super::retained_headers_n(4).unwrap();let prepared=prepare(&headers).unwrap();
        for n in [0usize,2,5] {let mut changed=headers.clone();if n<=4 {changed.truncate(n);}else{changed.push(headers[3].clone());}
            assert_eq!(prepare(&changed).err().unwrap(),"stream40 header count");}
        for fault in 0..2 {let mut changed=headers.clone();if fault==0 {changed[1].height+=1;}else{changed[1].parent_id[0]^=1;}
            assert_eq!(prepare(&changed).err().unwrap(),"stream40 canonical height/parent");}
        let p3=leaf::LeafProfile::new(3,[0;32]).unwrap();
        let dummy=leaf::native_leaf_preimage_hash(&p3,2,&[],0,[0;28],[0;28],prepared.profile).unwrap();
        let genuine=leaf::native_leaf_preimage_hash(&prepared.leaf,0,&headers[1].encode().unwrap(),2,[0;28],
            be28(&work::native_decode(headers[1].n_bits).unwrap()).unwrap(),prepared.profile).unwrap();
        let padding=leaf::native_leaf_preimage_hash(&prepared.leaf,3,&[],0,[0;28],[0;28],prepared.profile).unwrap();
        for (role,native) in [(leaf::Role::Genuine,genuine),(leaf::Role::Padding,padding)] {leaf_digest(role,native,native).unwrap();
            let mut corrupt=native;corrupt[0]^=1;
            assert_eq!(leaf_digest(role,corrupt,native).err().unwrap(),"stream40 assigned leaf digest");}
        leaf_digest(leaf::Role::Dummy,[0;32],dummy).unwrap();
        assert_eq!(leaf_digest(leaf::Role::Dummy,dummy,dummy).err().unwrap(),"stream40 assigned leaf digest");
        fixed_digest(dummy,dummy).unwrap();assert_eq!(fixed_digest([0;32],dummy).err().unwrap(),"stream40 assigned fixed digest");
        let root_owner=prepared.leaf.tree.root_node_slot;
        root_digest(root_owner,root_owner,prepared.summary.root,prepared.summary.root).unwrap();let mut wrong_root=prepared.summary.root;wrong_root[0]^=1;
        assert_eq!(root_digest(root_owner,root_owner,prepared.summary.root,wrong_root).err().unwrap(),"stream40 assigned root");
        let mut mask=vec![false;WIDTH];assert_eq!(replacement_mask(&mask).err().unwrap(),"stream40 replacement mask contract");
        mask.truncate(WIDTH-1);assert_eq!(replacement_mask(&mask).err().unwrap(),"stream40 replacement mask capacity");
        let mut bad_genesis=headers.clone();bad_genesis[0].timestamp^=1;
        assert_eq!(prepare(&bad_genesis).err().unwrap(),"stream40 genesis");
        let mut cursor=FixedCursor::new(&prepared,&headers);
        for owner in 0..S {let (bytes,digest)=cursor.preimage(owner).unwrap();
            assert_eq!(leaf::native_fixed_preimage_hash(&prepared.fixed,owner,&bytes).unwrap(),digest);}
        let mut stats=prepared.stats.clone();cursor.stats(&mut stats);assert_eq!(stats.native_scans,3);
        assert_eq!(stats.scan_leaf_hashes,12);assert!(stats.frontier_peak<=2);
        let mut wrong=FixedCursor::new(&prepared,&headers);
        assert_eq!(wrong.preimage(1).err().unwrap(),"stream40 fixed owner order");
        assert_eq!(NativeScan::new(&headers,&prepared.leaf,&prepared.fixed,prepared.profile).next_node(0).err().unwrap(),"stream40 target level");
        let mut overflow=NativeScan::new(&headers,&prepared.leaf,&prepared.fixed,prepared.profile);overflow.lower=BigUint::from(1u64)<<224usize;
        assert_eq!(overflow.next_node(1).err().unwrap(),"prefix work overflow");
        let mut node=vec![b'N',1,0,0,0,0];node.extend_from_slice(&genuine);node.extend_from_slice(&padding);
        for offset in [0usize,1,5] {let mut wrong=node.clone();wrong[offset]^=1;
            assert_eq!(leaf::native_fixed_preimage_hash(&prepared.fixed,0,&wrong).err().unwrap(),"fixed node preimage differs from descriptor role");}
        let temp=std::env::temp_dir().join(format!("stream40-control-{}.bits",std::process::id()));assert!(!temp.exists());
        for fail in [0usize,1,3] {
            let result=owned_output(&temp,|sink|{let block=vec![0;BLOCK];for owner in 0..S {
                sink(owner,&block)?;if owner==fail{return Err(format!("stream40 injected sink {fail}"));}}
                Ok((prepared.summary.clone(),WriterStats::default()))});
            assert_eq!(result.err().unwrap(),format!("stream40 injected sink {fail}"));assert!(!temp.exists());
        }
        for fault in 0..4 {let result=owned_output(&temp,|sink|{let block=vec![0;BLOCK];
            match fault {0=>sink(1,&block)?,1=>sink(0,&block[..BLOCK-1])?,2=>{sink(0,&block)?;sink(0,&block)?;},_=>{sink(0,&block)?;}}
            Ok((prepared.summary.clone(),WriterStats::default()))});
            assert_eq!(result.err().unwrap(),match fault {1=>"stream40 sink block extent",3=>"stream40 sink completion",_=>"stream40 sink owner order"});assert!(!temp.exists());}
        {use std::io::Write;let mut file=std::fs::OpenOptions::new().write(true).create_new(true).open(&temp).unwrap();file.write_all(b"owned-fixture").unwrap();}
        let before=std::fs::read(&temp).unwrap();
        assert!(owned_output(&temp,|_|panic!("existing target reached operation")).is_err());
        assert_eq!(std::fs::read(&temp).unwrap(),before);std::fs::remove_file(&temp).unwrap();
    }
}

//! Exact Eligible08 H21 D stream -> scheduled MAX -> Cap component.
//! Component row namespace only; no final ROW allocation, HEADER retirement,
//! DAA authentication, Score admission or PCS authority.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use num_bigint::BigUint;
use std::collections::BTreeMap;
use crate::{certified_modern_cap as cap,
    gkr::Gate, sparse::Term,
    wiring::{evaluate_residue_shift, RightIndex, SourceDelta}};
#[cfg(test)]
use crate::certified_modern_suffix as source;

const FIRST: usize = 844_672;
const LAST: usize = crate::h21_snapshot::N;
pub(super) use crate::bank53_map::CutDescriptor;
#[cfg(test)]
use crate::bank53_map::{CutProfile, MaturityMode};
const MAX_BASE: [usize; 2] = [999_424, 1_000_097];
const CAP_BASE: [usize; 2] = [1_000_770, 1_002_818];
const MAX_ROW: [usize; 2] = [356_632, 357_305];
const CAP_ROW: [usize; 2] = [357_978, 360_026];
const D_BASE: usize = 987_674;
const OWNERS: usize = 1 << 21;
fn x(o: usize, w: usize) -> usize { (o << 20) + w }
fn row(o: usize, q: usize) -> usize { (o << 19) + q }
fn cap_row(rows: ComponentRows, c: usize, q: usize) -> usize {
    if q < 2048 { CAP_ROW[c] + q } else { rows.cap_extra[c] + q - 2048 }
}
fn eq(p: &[Fr], n: usize) -> Fr {
    p.iter().enumerate().fold(Fr::one(), |a,(b,z)|
        a * if (n >> b) & 1 == 1 { *z } else { Fr::one() - z })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Writer { Max { context: usize, end: usize }, Cap { context: usize, origin: usize } }
#[derive(Clone, Copy, Debug)]
struct Epoch { start: usize, end: usize }
impl Epoch { fn owner(self) -> usize { self.end - 2 } }
#[derive(Clone, Copy, Debug)]
struct Guard { owner: usize, source: usize }

/// A candidate component placement, never an admission of the global merger.
#[derive(Clone, Copy)]
struct ComponentRows { max_extra:[usize;2], cap_extra:[usize;2] }
impl ComponentRows {
    fn checked(max_extra:[usize;2],cap_extra:[usize;2])->Result<Self,String> {
        let mut occupied=BTreeMap::new();
        for (start,len) in [(MAX_ROW[0],673),(MAX_ROW[1],673),(CAP_ROW[0],2048),(CAP_ROW[1],2048)] {
            for q in start..start+len {occupied.insert(q,());}
        }
        for (start,len) in [(max_extra[0],449),(max_extra[1],449),(cap_extra[0],520),(cap_extra[1],520)] {
            let end=start.checked_add(len).filter(|e|*e<=524288).ok_or("component extra ROW19 extent")?;
            // The pinned DAA zero_full lane is dense here and coactive with
            // scheduled MAX, e.g. Carry owner 844670. Never concatenate it.
            if start<475136 && end>393216 {return Err("component extras overlap DAA lane3".into());}
            if start<475136 {return Err("component extras precede high candidate band".into());}
            for q in start..end {if occupied.insert(q,()).is_some(){return Err("component extra row collision".into());}}
        }
        Ok(Self {max_extra,cap_extra})
    }
    fn high_candidate()->Self {
        Self::checked([475136,475585],[476034,476554]).expect("fixed component candidate rows")
    }
}

/// A code-owned fixed schedule, independent of any witness values.
pub(super) struct Plan { descriptor:CutDescriptor, epochs: [Vec<Epoch>; 2], caps: [Vec<Guard>; 2], rows:ComponentRows }
#[derive(Default, Debug, PartialEq, Eq)]
pub(super) struct Counts { pub max: [usize; 2], pub cap: [usize; 2] }

/// Fixed MAX-only calendar entry. Cap and HEADER ownership are not included.
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(super) struct MaxStep { pub end:usize, pub next:Option<usize> }
impl Plan {
    pub(super) fn descriptor(&self)->CutDescriptor {self.descriptor}
    pub(super) fn has_owner_writer(&self, owner: usize) -> Result<bool, String> {
        if owner >= OWNERS { return Err("scheduled owner outside H21".into()); }
        if self.descriptor != CutDescriptor::eligible08() {
            return Err("scheduled membership requires Eligible08".into());
        }
        Ok((0..2).any(|context| self.max_index(context, owner).is_some()
            || self.cap_index(context, owner).is_some()))
    }
    pub(super) fn max_calendar(&self)->Vec<(usize,[Option<MaxStep>;2])> {
        let mut owners:BTreeMap<usize,[Option<MaxStep>;2]>=BTreeMap::new();
        for context in 0..2 {
            for (j,epoch) in self.epochs[context].iter().enumerate() {
                owners.entry(epoch.owner()).or_insert([None;2])[context]=Some(MaxStep {
                    end:epoch.end,next:self.epochs[context].get(j+1).map(|e|e.owner()) });
            }
        }
        owners.into_iter().rev().collect()
    }
}

/// Lossless Boolean values, not a commitment or a substitute for source custody.
/// Coordinates and authors are reconstructed only from the fixed calendar.
#[derive(Clone,Debug,PartialEq,Eq)]
struct MaxRecord { owner:usize, d:[u8;28], max:[Option<[u8;85]>;2] }
impl MaxRecord {
    fn bit(bytes:&[u8],bit:usize)->Fr {Fr::from(((bytes[bit/8]>>(bit%8))&1)as u64)}
    fn set(bytes:&mut [u8],bit:usize,value:Fr)->Result<(),String> {
        if value!=Fr::zero() && value!=Fr::one() {return Err("streamed MAX nonboolean cell".into());}
        if value.is_one() {bytes[bit/8]|=1<<(bit%8);}Ok(())
    }
}

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(super) enum MaxReplayAuthor { NativeWorkD{height:usize}, Scheduled(Writer) }

/// Descending MAX-only successor closure. It retains exact bit values so a
/// later component can replay them; it stores no HEADER rows, Cap cells or X
/// ownership mask. Partial state has no replay interface. Full MAX closure is
/// neither a ROW merger nor an authenticated witness, PCS or proof.
pub(super) struct MaxStream<'a> {
    snapshot:&'a Eligible08NativeSnapshot,
    parent:NativeParent,
    calendar:Vec<(usize,[Option<MaxStep>;2])>,
    records:Vec<MaxRecord>,
    frontier:[Option<usize>;2],
    next:usize,
}
impl<'a> MaxStream<'a> {
    pub(super) fn new(plan:&crate::work_tree_history_plan::WorkTreeHistoryPlan,
        prefix:&crate::packed_owner_assembly::NativePrefix,snapshot:&'a Eligible08NativeSnapshot)
        ->Result<Self,String> {
        snapshot.require_native_parent(plan,prefix)?;
        snapshot.require_plan_parent(plan)?;
        Self::from_snapshot(snapshot)
    }
    fn from_snapshot(snapshot:&'a Eligible08NativeSnapshot)->Result<Self,String> {
        if snapshot.parent.cut!=CutDescriptor::eligible08()
            || snapshot.prepared.descriptor()!=CutDescriptor::eligible08() {
            return Err("streamed MAX exact Eligible08 cut".into());
        }
        let calendar=snapshot.scheduled_plan().max_calendar();
        let records=Vec::with_capacity(calendar.len());
        let out=Self{snapshot,parent:snapshot.parent(),calendar,records,frontier:[None;2],next:0};
        if out.retained_capacity_bytes()>2*1024*1024 {
            return Err("streamed MAX retained record/calendar cap".into());
        }
        Ok(out)
    }
    /// Capacity accounting includes all owned heap buffers and record slots.
    /// Borrowed native prefix/snapshot/plan and owner-local scratch are excluded.
    pub(super) fn retained_capacity_bytes(&self)->usize {
        self.records.capacity()*std::mem::size_of::<MaxRecord>()
            +self.calendar.capacity()*std::mem::size_of::<(usize,[Option<MaxStep>;2])>()
    }
    pub(super) fn remaining_owners(&self)->usize {self.calendar.len()-self.next}
    pub(super) fn push_native(&mut self,producer:&crate::packed_owner_assembly::NativeOwnerProducer<'_>,
        owner:usize)->Result<(),String> {
        let source=producer.native_work_d_lease(owner)?;
        producer.require_work_d_lease(owner,&source)?;
        let lease=self.snapshot.owner_lease(owner)?;
        self.append(&lease,&source)
    }
    fn append(&mut self,lease:&Eligible08OwnerLease,
        source:&crate::packed_owner_assembly::NativeWorkDLease)->Result<(),String> {
        if self.parent!=self.snapshot.parent() {return Err("streamed MAX immutable parent".into());}
        let &(owner,steps)=self.calendar.get(self.next).ok_or("streamed MAX surplus owner")?;
        if lease.owner()!=owner {return Err("streamed MAX exact descending owner".into());}
        lease.check_exact(self.snapshot)?;
        let actual=source.checked_cells(&self.parent,owner)?;
        let expected=lease.work_d().ok_or("streamed MAX missing Work-D expectation")?;
        if expected.owner()!=owner || expected.height()!=owner+2 || actual!=expected.cells() {
            return Err("streamed MAX exact native Work-D expectation".into());
        }
        let mut record=MaxRecord{owner,d:[0;28],max:[None;2]};
        for (bit,&(_,value)) in actual.iter().enumerate() {MaxRecord::set(&mut record.d,bit,value)?;}
        for context in 0..2 {
            let spans:Vec<_>=lease.patch.spans.iter().filter(|span|
                matches!(span.writer,Writer::Max{context:c,..} if c==context)).collect();
            match steps[context] {
                None if !spans.is_empty()=>return Err("streamed MAX inactive context".into()),
                None=>continue,
                Some(step)=> {
                    if spans.len()!=1 || spans[0].writer!=(Writer::Max{context,end:step.end})
                        || spans[0].start!=MAX_BASE[context] || spans[0].values.len()!=673 {
                        return Err("streamed MAX exact typed cell census".into());
                    }
                    let mut bits=[0u8;85];
                    for (bit,&value) in spans[0].values.iter().enumerate() {MaxRecord::set(&mut bits,bit,value)?;}
                    if bits[84]&0xfe!=0 {return Err("streamed MAX canonical padding".into());}
                    record.max[context]=Some(bits);
                    match (step.next,self.frontier[context]) {
                        (None,None)=> {
                            if (224..448).any(|bit|!MaxRecord::bit(&bits,bit).is_zero()) {
                                return Err("streamed MAX terminal T must be zero".into());
                            }
                        }
                        (Some(next),Some(index))=> {
                            let prior=self.records.get(index).ok_or("streamed MAX missing successor record")?;
                            if prior.owner!=next || prior.max[context].is_none() {
                                return Err("streamed MAX exact typed successor".into());
                            }
                            let prior_bits=prior.max[context].as_ref().unwrap();
                            for bit in 0..224 {
                                if MaxRecord::bit(&bits,224+bit)!=MaxRecord::bit(prior_bits,bit) {
                                    return Err("streamed MAX successor value".into());
                                }
                            }
                        }
                        _=>return Err("streamed MAX successor/terminal census".into()),
                    }
                }
            }
        }
        let read=|wire:usize|->Result<Fr,String> {
            let local=wire%(1<<20);let at=wire>>20;
            if at==owner && (D_BASE..D_BASE+224).contains(&local) {
                return Ok(MaxRecord::bit(&record.d,local-D_BASE));
            }
            for context in 0..2 {
                if let Some(step)=steps[context] {
                    if at==owner && (MAX_BASE[context]..MAX_BASE[context]+673).contains(&local) {
                        return Ok(MaxRecord::bit(record.max[context].as_ref().unwrap(),local-MAX_BASE[context]));
                    }
                    if step.next==Some(at) && (MAX_BASE[context]..MAX_BASE[context]+224).contains(&local) {
                        let prior=&self.records[self.frontier[context].ok_or("streamed MAX unresolved successor")?];
                        return Ok(MaxRecord::bit(prior.max[context].as_ref().ok_or("streamed MAX successor context")?,local-MAX_BASE[context]));
                    }
                }
            }
            Err("streamed MAX unclassified live read".into())
        };
        let mut residuals:BTreeMap<(usize,usize),Fr>=BTreeMap::new();
        lease.visit_rows(|writer,term| {
            let Writer::Max{context,end}=writer else {return Ok(());};
            if context>=2 || steps[context].map(|step|step.end)!=Some(end) {
                return Err("streamed MAX exact ROW writer".into());
            }
            let g=&term.gate;
            let left=if !g.c1.is_zero()||!g.c3.is_zero(){read(g.left)?}else{Fr::zero()};
            let right=if !g.c2.is_zero()||!g.c3.is_zero(){read(g.right)?}else{Fr::zero()};
            *residuals.entry((context,term.row)).or_insert(Fr::zero())+=g.c0+g.c1*left+g.c2*right+g.c3*left*right;
            Ok(())
        })?;
        if residuals.len()!=steps.iter().filter(|step|step.is_some()).count()*1122
            || residuals.values().any(|value|!value.is_zero()) {
            return Err("streamed MAX exact residual census/value".into());
        }
        // All validation precedes the sole state transition. No owner-local
        // rows, field buffers or native leases survive this append.
        let index=self.records.len();self.records.push(record);
        for context in 0..2 {if steps[context].is_some(){self.frontier[context]=Some(index);}}
        self.next+=1;Ok(())
    }
    /// Exact values for a future MAX-only consumer. Incomplete closure cannot
    /// export values; this grants no global X/ROW ownership or proof authority.
    pub(super) fn closed_owner_cells(&self,owner:usize)->Result<Vec<(usize,MaxReplayAuthor,Fr)>,String> {
        if self.next!=self.calendar.len() || self.records.len()!=self.calendar.len() {
            return Err("streamed MAX incomplete closure".into());
        }
        let record=self.records.iter().find(|record|record.owner==owner).ok_or("streamed MAX replay inactive owner")?;
        let mut cells=Vec::with_capacity(224+673*record.max.iter().filter(|bits|bits.is_some()).count());
        for bit in 0..224 {cells.push((x(owner,D_BASE+bit),MaxReplayAuthor::NativeWorkD{height:owner+2},MaxRecord::bit(&record.d,bit)));}
        for context in 0..2 {if let Some(bits)=&record.max[context] {
            for bit in 0..673 {cells.push((x(owner,MAX_BASE[context]+bit),MaxReplayAuthor::Scheduled(Writer::Max{context,end:owner+2}),MaxRecord::bit(bits,bit)));}
        }}Ok(cells)
    }

    /// A closed native MAX stream is the sole source of modern Score spans.
    /// This does not publish the corresponding X or ROW cells.
    pub(super) fn closed_native_snapshot(
        &self,plan:&crate::work_tree_history_plan::WorkTreeHistoryPlan,
        prefix:&crate::packed_owner_assembly::NativePrefix,
    )->Result<&Eligible08NativeSnapshot,String> {
        if self.next!=self.calendar.len() || self.records.len()!=self.calendar.len() {
            return Err("Score source requires closed native MAX".into());
        }
        if self.parent!=self.snapshot.parent() {
            return Err("Score source immutable MAX parent".into());
        }
        self.snapshot.require_native_parent(plan,prefix)?;
        self.snapshot.require_plan_parent(plan)?;
        Ok(self.snapshot)
    }

    /// Every interval has one physical Cap endpoint and one retained MAX R.
    /// The value is checked against both authors before any Score consumer can
    /// use it; the future circuit still has to authenticate their ROW aliases.
    pub(super) fn closed_score_endpoint_leases(
        &self,context:usize,
    )->Result<Vec<ScoreEndpointLease>,String> {
        if self.next!=self.calendar.len() || self.records.len()!=self.calendar.len() {
            return Err("Score endpoint source requires closed MAX".into());
        }
        if self.parent!=self.snapshot.parent()
            || self.parent.cut!=CutDescriptor::eligible08() || context>=2 {
            return Err("Score endpoint source parent/cut/context".into());
        }
        let spans=self.snapshot.prepared.score_spans(context)?;
        if spans.len()!=crate::h21_snapshot::SCORE_SPANS[context] {
            return Err("Score endpoint exact context census".into());
        }
        let mut leases=Vec::with_capacity(spans.len());
        for (span,epoch) in spans.into_iter()
            .zip(self.snapshot.prepared.plan.epochs[context].iter()) {
            let first=epoch.start+self.parent.cut.offset();
            let last=(epoch.end+self.parent.cut.offset())
                .min(self.parent.cut.guards()[context]);
            if span.first!=first || span.last!=last || first>last {
                return Err("Score endpoint exact epoch interval".into());
            }
            let max_owner=epoch.owner();
            let index=self.records.partition_point(|record|record.owner>max_owner);
            let record=self.records.get(index).filter(|record|record.owner==max_owner)
                .ok_or("Score endpoint closed MAX owner missing")?;
            let max_bits=record.max[context].as_ref()
                .ok_or("Score endpoint closed MAX context missing")?;
            if max_bits[84]&0xfe!=0 {
                return Err("Score endpoint MAX padding".into());
            }
            let maximum=BigUint::from_bytes_le(&max_bits[..28]);
            if cap::scalar(&maximum)?!=span.value {
                return Err("Score endpoint MAX scalar/source".into());
            }
            let cap_owner=last-1;
            if self.snapshot.prepared.owner_patch(cap_owner)?
                .cap_value_65(context)?!=span.value {
                return Err("Score endpoint physical Cap q/source".into());
            }
            leases.push(ScoreEndpointLease {parent:self.parent.clone(),context,
                first_origin:first,last_origin:last,max_owner,cap_owner,
                value:span.value});
        }
        if leases.first().map(|lease|(lease.first_origin,lease.last_origin))
                !=Some((845760,845760))
            || leases.last().map(|lease|lease.last_origin)
                !=Some(self.parent.cut.guards()[context])
            || leases.windows(2).any(|pair|
                pair[0].last_origin+1!=pair[1].first_origin) {
            return Err("Score endpoint exhaustive modern partition".into());
        }
        Ok(leases)
    }
}

#[cfg(test)]
#[path="h21_streamed_max_tests.rs"]
mod streamed_max_tests;
impl Plan {
    #[cfg(test)]
    pub(super) fn new() -> Self {
        Self::with_descriptor(CutDescriptor::diagnostic08())
    }
    pub(super) fn eligible08() -> Self {
        Self::with_descriptor(CutDescriptor::eligible08())
    }
    fn with_descriptor(descriptor:CutDescriptor) -> Self {
        let terminal=descriptor.terminals();let guard=descriptor.guards();
        let epochs = std::array::from_fn(|c| {
            let mut out = Vec::with_capacity(7682);
            out.push(Epoch { start: FIRST, end: FIRST });
            let mut start = FIRST + 1;
            while start <= terminal[c] {
                let end = (start + 127).min(terminal[c]);
                out.push(Epoch { start, end }); start = end + 1;
            }
            out
        });
        let caps = std::array::from_fn(|c| {
            let mut out = Vec::with_capacity(if c == 0 { 7674 } else { 7673 });
            for (j, e) in epochs[c].iter().enumerate() {
                let origin = e.end + descriptor.offset();
                if origin <= guard[c] { out.push(Guard { owner: origin - 1, source: j }); }
            }
            if out.last().map(|g| g.owner) != Some(guard[c] - 1) {
                let h = guard[c] - descriptor.offset();
                let source = epochs[c].iter().position(|e| e.start <= h && h <= e.end).expect("fixed clipped epoch");
                out.push(Guard { owner: guard[c] - 1, source });
            }
            out
        });
        Self { descriptor, epochs, caps, rows:ComponentRows::high_candidate() }
    }
    fn max_index(&self, c: usize, o: usize) -> Option<usize> {
        self.epochs[c].binary_search_by_key(&o, |e| e.owner()).ok()
    }
    fn cap_index(&self, c: usize, o: usize) -> Option<usize> {
        self.caps[c].binary_search_by_key(&o, |g| g.owner).ok()
    }
    /// Read-only writer membership. This does not emit/validate equations,
    /// reproduce sink errors, close a native source or qualify a proof.
    pub(super) fn owner_activity(&self,o:usize)->Result<([bool;2],[bool;2]),String> {
        if o>=OWNERS {return Err("scheduled owner outside H21".into());}
        Ok((std::array::from_fn(|c|self.max_index(c,o).is_some()),
            std::array::from_fn(|c|self.cap_index(c,o).is_some())))
    }
    pub(super) fn visit_owner(&self, o: usize,
        mut sink: impl FnMut(Writer, Term) -> Result<(), String>) -> Result<Counts, String> {
        if o >= OWNERS { return Err("scheduled owner outside H21".into()); }
        let mut count = Counts::default();
        for c in 0..2 {
            if let Some(j) = self.max_index(c,o) {
                let writer = Writer::Max { context: c, end: self.epochs[c][j].end };
                let next = self.epochs[c].get(j+1).map(|e| e.owner());
                self.emit_max(c,o,next, |t| { count.max[c] += 1; sink(writer,t) })?;
            }
            if let Some(j) = self.cap_index(c,o) {
                let writer = Writer::Cap { context: c, origin: o+1 };
                let import = self.epochs[c][self.caps[c][j].source].owner();
                self.emit_cap(c,o,import, |t| { count.cap[c] += 1; sink(writer,t) })?;
            }
        }
        Ok(count)
    }
    fn emit_max(&self,c:usize,o:usize,next:Option<usize>,
        mut sink:impl FnMut(Term)->Result<(),String>) -> Result<(),String> {
        let z=Fr::zero(); let one=Fr::one(); let b=MAX_BASE[c]; let e=self.rows.max_extra[c];
        for k in 0..673 { sink(Term { row:row(o,MAX_ROW[c]+k),gate:Gate {
            left:x(o,b+k),right:x(o,b+k),c0:z,c1:-one,c2:z,c3:one } })?; }
        let mut mono=|q,l,r,j,v| { let mut a=[z;4];a[j]=v;
            sink(Term {row:row(o,q),gate:Gate {left:l,right:r,c0:a[0],c1:a[1],c2:a[2],c3:a[3]}}) };
        let mut p=one;
        for k in 0..224 {
            for (local,sign) in [(D_BASE+k,one),(b+224+k,-one),(b+448+k,-one)] {
                mono(e,x(o,local),x(o,0),1,sign*p)?;
            } p+=p;
        }
        mono(e,x(o,b+672),x(o,0),1,p)?;
        for k in 0..224 {
            mono(e+1+k,x(o,b+k),x(o,0),1,one)?;
            mono(e+1+k,x(o,D_BASE+k),x(o,0),1,-one)?;
            mono(e+1+k,x(o,b+672),x(o,b+224+k),3,-one)?;
            mono(e+1+k,x(o,b+672),x(o,D_BASE+k),3,one)?;
            mono(e+225+k,x(o,b+224+k),x(o,0),1,one)?;
            if let Some(n)=next { mono(e+225+k,x(n,b+k),x(o,0),1,-one)?; }
        }
        Ok(())
    }
    fn emit_cap(&self,c:usize,o:usize,import:usize,
        mut sink:impl FnMut(Term)->Result<(),String>) -> Result<(),String> {
        let mut error=None;
        cap_literal(|q,l,r,imported,coefficients| {
            if error.is_some() { return; }
            let result=if q>=2568 || l>=2048 || r>=2048 || (imported && l>=224) {
                Err("scheduled Cap literal extent".into())
            } else {
                sink(Term {row:row(o,cap_row(self.rows,c,q)),gate:Gate {
                    left:if imported {x(import,MAX_BASE[c]+l)}else{x(o,CAP_BASE[c]+l)},
                    right:x(o,CAP_BASE[c]+r),
                    c0:coefficients[0],c1:coefficients[1],
                    c2:coefficients[2],c3:coefficients[3]}})
            };
            if let Err(e)=result {error=Some(e);}
        });
        error.map_or(Ok(()),Err)
    }
    pub(super) fn coefficients(&self,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String> {
        if (r.len(),u.len(),v.len())!=(40,41,41) {return Err("scheduled coefficient dimensions".into());}
        let mut out=[Fr::zero();4];
        for c in 0..2 {
            let max=self.max_coefficients(c,r,u,v)?;
            let capped=self.cap_coefficients(c,r,u,v)?;
            for j in 0..4 {out[j]+=max[j]+capped[j];}
        } Ok(out)
    }
    /// Same-owner weights for the four actual scheduled writer rosters. The
    /// HEADER retirement consumer uses this plan's cut, including clipped tails.
    pub(super) fn anchor_owner_weights(&self,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String> {
        if (r.len(),u.len(),v.len())!=(21,21,21) {return Err("scheduled owner coefficient dimensions".into());}
        let mut out=[Fr::zero();4];
        for c in 0..2 {
            out[c]=self.max_owner_weights(c,r,u,v)?.0;
            out[2+c]=self.cap_owner_weights(c,r,u,v)?.0;
        }
        Ok(out)
    }
    fn max_owner_weights(&self,c:usize,r:&[Fr],u:&[Fr],v:&[Fr])->Result<(Fr,Fr),String> {
        let coordinate=|n:usize|u64::try_from(n).map_err(|_|"scheduled analytic coordinate U64".to_string());
        let weight=|lo:usize,hi:usize,res:usize,delta:usize| evaluate_residue_shift(r,u,v,
            SourceDelta::Add(coordinate(delta)?),coordinate(lo)?,coordinate(hi)?,if res==126 {7}else{0},coordinate(res)?,RightIndex::SameRow);
        // Closed-form runs from the cuts, independently of emitted epoch lists.
        let terminal=self.descriptor.terminals()[c];
        let regular=FIRST+((terminal-FIRST)/128)*128;
        let mut self_weight=weight(FIRST-2,regular-1,126,0)?;
        let mut next_weight=weight(FIRST-2,regular-129,126,128)?;
        if terminal!=regular {
            self_weight+=weight(terminal-2,terminal-1,0,0)?;
            next_weight+=weight(regular-2,regular-1,0,terminal-regular)?;
        }
        Ok((self_weight,next_weight))
    }
    fn max_coefficients(&self,c:usize,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String> {
        let (self_weight,next_weight)=self.max_owner_weights(c,&r[19..],&u[20..],&v[20..])?;
        let er=|q|eq(&r[..19],q);let eu=|q|eq(&u[..20],q);let ev=|q|eq(&v[..20],q);
        let b=MAX_BASE[c];let a=MAX_ROW[c];let e=self.rows.max_extra[c];
        let mut local=[Fr::zero();4];let mut compare=Fr::zero();let mut link=Fr::zero();let mut p=Fr::one();
        for k in 0..673 {let z=er(a+k)*eu(b+k)*ev(b+k);local[1]-=z;local[3]+=z;}
        for k in 0..224 {
            compare+=p*(eu(D_BASE+k)-eu(b+224+k)-eu(b+448+k));p+=p;
            local[1]+=er(e+1+k)*ev(0)*(eu(b+k)-eu(D_BASE+k));
            local[3]+=er(e+1+k)*eu(b+672)*(ev(D_BASE+k)-ev(b+224+k));
            local[1]+=er(e+225+k)*eu(b+224+k)*ev(0);
            link-=er(e+225+k)*eu(b+k)*ev(0);
        }
        local[1]+=er(e)*ev(0)*(compare+p*eu(b+672));
        for a in &mut local {*a*=self_weight;}local[1]+=link*next_weight;Ok(local)
    }
    fn cap_owner_weights(&self,c:usize,r:&[Fr],u:&[Fr],v:&[Fr])->Result<(Fr,Fr),String> {
        let offset=self.descriptor.offset();let guard=self.descriptor.guards()[c];
        let first=FIRST+offset-1;
        let regular=first+((guard-1-first)/128)*128;
        let coordinate=|n:usize|u64::try_from(n).map_err(|_|"scheduled analytic coordinate U64".to_string());
        let k=|delta| evaluate_residue_shift(r,u,v,delta,coordinate(first)?,coordinate(regular+1)?,7,coordinate(first%128)?,RightIndex::SameRow);
        let mut self_weight=k(SourceDelta::Add(0))?;
        let mut import_weight=k(SourceDelta::Sub(coordinate(offset+1)?))?;
        if regular!=guard-1 {
            let dest=guard-1;let q=guard-offset;
            let src=(FIRST+(q-FIRST).div_ceil(128)*128).min(self.descriptor.terminals()[c])-2;
            self_weight+=eq(r,dest)*eq(u,dest)*eq(v,dest);
            import_weight+=eq(r,dest)*eq(u,src)*eq(v,dest);
        }
        Ok((self_weight,import_weight))
    }
    fn cap_coefficients(&self,c:usize,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String> {
        let (self_weight,import_weight)=self.cap_owner_weights(c,&r[19..],&u[20..],&v[20..])?;
        let rr:Vec<_>=(0..2568).map(|q|eq(&r[..19],cap_row(self.rows,c,q))).collect();
        let uu:Vec<_>=(0..2048).map(|w|eq(&u[..20],CAP_BASE[c]+w)).collect();
        let vv:Vec<_>=(0..2048).map(|w|eq(&v[..20],CAP_BASE[c]+w)).collect();
        let mm:Vec<_>=(0..224).map(|w|eq(&u[..20],MAX_BASE[c]+w)).collect();
        let mut out=[Fr::zero();4];
        cap_literal(|q,l,rt,import,a| {
            let left=if import {mm[l]}else{uu[l]};
            let w=rr[q]*left*vv[rt]*if import {import_weight}else{self_weight};
            for j in 0..4 {out[j]+=w*a[j];}
        });Ok(out)
    }
}

/// Independent list-membership oracle plus bounded real emitter differential.
/// Called by the existing selected MAX test; no new test/group or native source.
#[cfg(test)]
pub(super) fn c576_owner_activity_controls() {
    use std::collections::BTreeSet;
    for descriptor in [CutDescriptor::eligible08(),CutDescriptor::diagnostic08()] {
        let plan=Plan::with_descriptor(descriptor);
        let expected_max:[BTreeSet<usize>;2]=std::array::from_fn(|c|
            plan.epochs[c].iter().map(|epoch|epoch.owner()).collect());
        let expected_cap:[BTreeSet<usize>;2]=std::array::from_fn(|c|
            plan.caps[c].iter().map(|guard|guard.owner).collect());
        let expected=|owner:usize| -> ([bool;2],[bool;2]) { (std::array::from_fn(|c|expected_max[c].contains(&owner)),
            std::array::from_fn(|c|expected_cap[c].contains(&owner))) };
        let mut members=BTreeSet::new();
        for set in expected_max.iter().chain(&expected_cap) {members.extend(set.iter().copied());}
        // ALL metadata members, with the oracle built from the private lists
        // rather than from the query's four binary searches. No term emission.
        for &owner in &members {assert_eq!(plan.owner_activity(owner).unwrap(),expected(owner));}
        let mut bounded=BTreeSet::from([0,OWNERS-1]);
        for c in 0..2 {
            for index in [0,plan.epochs[c].len()/2,plan.epochs[c].len()-1] {
                let owner=plan.epochs[c][index].owner();
                for at in owner-1..=owner+1 {bounded.insert(at);}
            }
            for index in [0,plan.caps[c].len()/2,plan.caps[c].len()-1] {
                let owner=plan.caps[c][index].owner;
                for at in owner-1..=owner+1 {bounded.insert(at);}
            }
        }
        bounded.extend([844_670,844_798,845_759,846_015,1_810_840,1_810_841,1_810_904,1_827_838]);
        // Explicitly include every actual MAX/Cap MASK combination, not only
        // any-writer=true. The fixed profiles may have different clipped tails.
        let mut masks=BTreeSet::new();
        for &owner in &members {let mask=expected(owner);if masks.insert(mask){bounded.insert(owner);}}
        for owner in bounded {
            let query=plan.owner_activity(owner).unwrap();assert_eq!(query,expected(owner));
            let counts=plan.visit_owner(owner,|_,_|Ok(())).unwrap();
            assert_eq!(query,(counts.max.map(|n|n>0),counts.cap.map(|n|n>0)));
        }
        assert_eq!(plan.owner_activity(0).unwrap(),([false;2],[false;2]));
        assert_eq!(plan.owner_activity(OWNERS-1).unwrap(),([false;2],[false;2]));
        for owner in [OWNERS,usize::MAX] {
            assert_eq!(plan.owner_activity(owner).unwrap_err(),"scheduled owner outside H21");
            assert_eq!(plan.owner_activity(owner).unwrap_err(),plan.visit_owner(owner,|_,_|Ok(())).unwrap_err());
        }
    }
}

/// Independent local arithmetic roster transferred from the c111 literal oracle.
fn cap_literal(mut sink:impl FnMut(usize,usize,usize,bool,[Fr;4])) {
    fn rails(emit:&mut impl FnMut(usize,usize,usize,bool,usize,Fr),
        ranges:&[(usize,usize,usize,i64)]) {
        for &(q,lo,hi,scale) in ranges {
            let mut power=if scale<0 {-Fr::from((-scale)as u64)}else{Fr::from(scale as u64)};
            for w in lo..hi {emit(q,w,0,false,1,power);power+=power;}
        }
    }
    let one=Fr::one();let zero=Fr::zero();
    let mut emit=|q,l,r,import,j,v|{let mut a=[zero;4];a[j]=v;sink(q,l,r,import,a);};
    emit(0,0,0,false,1,one);
    for w in 1..1383 {emit(w,w,0,false,1,-one);emit(w,w,w,false,3,one);}
    for b in 0..224 {emit(1383+b,1+b,0,false,1,one);emit(1383+b,b,0,true,1,-one);}
    for b in 0..224 {emit(1607+b,225+b,0,false,1,one);emit(1607+b,1+b,0,false,1,-one);}
    emit(1831,0,0,false,0,-one);
    rails(&mut emit,&[(1831,225,449,1),(1831,1159,1383,-1)]);
    rails(&mut emit,&[(1832,225,449,3),(1832,449,674,-2)]);
    emit(1832,674,0,false,1,-one);
    emit(1833,0,0,false,0,-one);
    for w in 675..740 {emit(1833,w,0,false,1,one);}
    rails(&mut emit,&[(1834,740,805,1),(1834,675,740,-1),
        (1835,805,869,1),(1835,676,740,-1),
        (1836,740,805,1),(1836,449,674,-1),(1836,869,934,-1)]);
    emit(1837,0,0,false,0,-one);
    rails(&mut emit,&[(1837,449,674,1),(1837,805,869,-1),(1837,934,1159,-1)]);
    for w in 1383..2048 {emit(1903+w-1383,w,0,false,1,one);}
}

#[derive(Debug, PartialEq, Eq)]
struct MaxWitness { d:BigUint, r:BigUint, t:BigUint, delta:BigUint, less:bool }
pub(super) struct Prepared { plan:Plan, max:[Vec<MaxWitness>;2] }
/// Exhaustive modern Score partition. Every origin in a span imports the
/// same suffix MAX; the final span may end inside a difficulty epoch.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct ScoreSpan {
    pub first: usize,
    pub last: usize,
    pub value: BigUint,
}
/// A private source token, owned by one completed MAX/Cap/Eligible08 calendar.
/// The consumer receives read-only fields; there is no caller-supplied V.
#[derive(Clone, Debug)]
pub(super) struct ScoreEndpointLease {
    parent: NativeParent,
    context: usize,
    first_origin: usize,
    last_origin: usize,
    max_owner: usize,
    cap_owner: usize,
    value: BigUint,
}
impl ScoreEndpointLease {
    pub(super) fn parent(&self)->&NativeParent {&self.parent}
    pub(super) fn context(&self)->usize {self.context}
    pub(super) fn first_origin(&self)->usize {self.first_origin}
    pub(super) fn last_origin(&self)->usize {self.last_origin}
    pub(super) fn max_owner(&self)->usize {self.max_owner}
    pub(super) fn cap_owner(&self)->usize {self.cap_owner}
    pub(super) fn value(&self)->&BigUint {&self.value}

    #[cfg(test)]
    pub(super) fn c498_matches_parent(&self,root:[u8;32],total:[u8;28],
        profile:[u8;32],cut:&[u8])->bool {
        self.parent.root==root && self.parent.total==total && self.parent.profile==profile
            && self.parent.cut.canonical_identity()==cut
    }

    #[cfg(test)]
    pub(super) fn synthetic_for_test(context:usize,first_origin:usize,
        last_origin:usize,value:BigUint)->Self {
        Self {parent:NativeParent {root:[0x72;32],total:[0x73;28],
                profile:[0x74;32],cut:CutDescriptor::eligible08()},
            context,first_origin,last_origin,max_owner:first_origin-1090,
            cap_owner:last_origin-1,value}
    }
}

#[cfg(test)]
pub(super) fn c488_first_regular_score_leases()->Result<[ScoreEndpointLease;2],String>{
    let descriptor=CutDescriptor::eligible08();
    let prepared=Prepared::from_d_iter_eligible08((FIRST..=LAST).map(|height|(height,BigUint::from(1u8))))?;
    let snapshot=Eligible08NativeSnapshot{parent:NativeParent{root:[0x72;32],total:[0x73;28],profile:[0x74;32],cut:descriptor},prepared};
    let mut leases=Vec::with_capacity(2);
    for context in 0..2 {
        let spans=snapshot.prepared.score_spans(context)?;
        if spans.len()<2||(spans[0].first,spans[0].last)!=(845_760,845_760)
            ||(spans[1].first,spans[1].last)!=(845_761,845_888){return Err("c488 first regular Score span position".into());}
        let span=&spans[1];let epoch=*snapshot.prepared.plan.epochs[context].get(1)
            .ok_or("c488 first regular epoch position")?;
        if epoch.start+descriptor.offset()!=span.first||epoch.end+descriptor.offset()!=span.last
            ||epoch.owner()!=844_798{return Err("c488 exact scheduled MAX owner".into());}
        let patch=snapshot.prepared.owner_patch(845_887)?;
        let writer=Writer::Cap{context,origin:845_888};
        let selected_patch=patch.snapshot().into_iter().filter(|(owner,_,actual,_)|*owner==845_887&&*actual==writer).collect::<Vec<_>>();
        if selected_patch.len()!=1||patch.cap_value_65(context)?!=span.value{return Err("c488 exact scheduled Cap owner/value".into());}
        leases.push(ScoreEndpointLease{parent:snapshot.parent(),context,first_origin:span.first,last_origin:span.last,max_owner:epoch.owner(),cap_owner:845_887,value:span.value.clone()});
    }
    let pair:[ScoreEndpointLease;2]=leases.try_into().map_err(|_|"c488 scheduled lease pair")?;
    if pair[0].context!=0||pair[1].context!=1||pair[0].parent!=pair[1].parent
        ||pair[0].parent.cut!=descriptor{return Err("c488 lease pair context/parent/cut".into());}Ok(pair)
}
/// Conditional schedule-derived fixtures only; no native D authentication.
#[cfg(test)]
pub(super) fn c498_clipped_score_leases()->Result<[ScoreEndpointLease;2],String>{
    let prepared=Prepared::from_d_iter_eligible08(
        (FIRST..=LAST).map(|height|(height,BigUint::from(1u8))))?;
    c498_clipped_score_leases_from_prepared(&prepared)
}

#[cfg(test)]
fn c498_clipped_score_leases_from_prepared(prepared:&Prepared)
    ->Result<[ScoreEndpointLease;2],String>{
    let parent=NativeParent {root:[0x72;32],total:[0x73;28],
        profile:[0x74;32],cut:CutDescriptor::eligible08()};
    c498_select_clipped_score_leases(prepared,parent)
}

/// Conditional H21 identity is fixed before any endpoint lease is issued.
#[cfg(test)]
pub(super) fn c498_clipped_score_leases_for_h21_parent(
    root:[u8;32],total:[u8;28],profile:[u8;32])
    ->Result<[ScoreEndpointLease;2],String>{
    use blake2::{Blake2b, Digest, digest::consts::U32};
    let mut bytes=crate::work_tree_fixed_hash::PROFILE_PREFIX.to_vec();
    bytes.extend_from_slice(&crate::header_order::MAINNET_GENESIS);
    let expected:[u8;32]=Blake2b::<U32>::digest(bytes).into();
    if profile!=expected {return Err("c498 conditional fixed H21 profile".into());}
    let prepared=Prepared::from_d_iter_eligible08(
        (FIRST..=LAST).map(|height|(height,BigUint::from(1u8))))?;
    let parent=NativeParent {root,total,profile,cut:CutDescriptor::eligible08()};
    c498_select_clipped_score_leases(&prepared,parent)
}

#[cfg(test)]
fn c498_select_clipped_score_leases(prepared:&Prepared,parent:NativeParent)
    ->Result<[ScoreEndpointLease;2],String>{
    let descriptor=CutDescriptor::eligible08();
    if prepared.descriptor()!=descriptor || parent.cut!=descriptor {
        return Err("c498 conditional Eligible08 descriptor".into());
    }
    let mut leases=Vec::with_capacity(2);
    for (context,first,last,previous,max_owner) in [
        (0,1_810_881,1_810_905,1_810_879,1_809_918),
        (1,1_810_753,1_810_842,1_810_751,1_809_790),
    ] {
        let spans=prepared.score_spans(context)?;
        let index=spans.len().checked_sub(1).ok_or("c498 terminal Score span absent")?;
        let span=&spans[index];
        // The final Score span is clipped before the final MAX epoch.
        let epoch=*prepared.plan.epochs[context].get(index)
            .ok_or("c498 corresponding MAX epoch absent")?;
        if spans.len()!=[7_542,7_541][context]
            || (span.first,span.last)!=(first,last) || first.checked_sub(2)!=Some(previous)
            || epoch.start+descriptor.offset()!=first
            || (epoch.end+descriptor.offset()).min(descriptor.guards()[context])!=last
            || epoch.owner()!=max_owner || last!=descriptor.guards()[context]
            || index+1>=prepared.plan.epochs[context].len() {
            return Err("c498 clipped Score/MAX interval identity".into());
        }
        let owner=last-1;
        let guards:Vec<_>=prepared.plan.caps[context].iter()
            .filter(|guard|guard.owner==owner).collect();
        if guards.len()!=1 || guards[0].source!=index {
            return Err("c498 clipped Cap source epoch identity".into());
        }
        let patch=prepared.owner_patch(owner)?;
        let writer=Writer::Cap {context,origin:last};
        let selected:Vec<_>=patch.spans.iter().filter(|span|span.writer==writer).collect();
        if patch.owner!=owner || selected.len()!=1
            || selected[0].start!=CAP_BASE[context] || selected[0].values.len()!=2_048
            || patch.cap_value_65(context)?!=span.value
            || cap::scalar(&prepared.max[context][index].r)?!=span.value {
            return Err("c498 clipped Cap owner/domain/scalar".into());
        }
        leases.push(ScoreEndpointLease {parent:parent.clone(),context,
            first_origin:first,last_origin:last,max_owner:epoch.owner(),
            cap_owner:owner,value:span.value.clone()});
    }
    let pair:[ScoreEndpointLease;2]=leases.try_into().map_err(|_|"c498 lease pair census")?;
    if pair[0].context!=0 || pair[1].context!=1 || pair[0].parent!=pair[1].parent
        || pair[0].parent.cut!=descriptor || pair[0].cap_owner==pair[1].cap_owner {
        return Err("c498 clipped lease pair identity".into());
    }
    Ok(pair)
}

#[cfg(test)]
#[test]
fn c498_clipped_schedule_rejects_wrong_max_and_cap_source_with_same_scalar(){
    let mut prepared=Prepared::from_d_iter_eligible08(
        (FIRST..=LAST).map(|height|(height,BigUint::from(1u8)))).unwrap();
    let baseline=c498_clipped_score_leases_from_prepared(&prepared).unwrap();
    for context in 0..2 {
        let index=prepared.score_spans(context).unwrap().len()-1;
        let saved_epoch=prepared.plan.epochs[context][index];
        prepared.plan.epochs[context][index].end-=1;
        assert_eq!(cap::scalar(&prepared.max[context][index].r).unwrap(),
            *baseline[context].value(),"MAX identity fault preserves scalar");
        assert_eq!(c498_clipped_score_leases_from_prepared(&prepared).unwrap_err(),
            "c498 clipped Score/MAX interval identity");
        prepared.plan.epochs[context][index]=saved_epoch;

        let owner=baseline[context].cap_owner();
        let guard_index=prepared.plan.cap_index(context,owner).unwrap();
        let saved_source=prepared.plan.caps[context][guard_index].source;
        prepared.plan.caps[context][guard_index].source=index-1;
        assert_eq!(prepared.owner_patch(owner).unwrap().cap_value_65(context).unwrap(),
            *baseline[context].value(),"Cap source fault preserves scalar");
        assert_eq!(c498_clipped_score_leases_from_prepared(&prepared).unwrap_err(),
            "c498 clipped Cap source epoch identity");
        prepared.plan.caps[context][guard_index].source=saved_source;
    }
    let restored=c498_clipped_score_leases_from_prepared(&prepared).unwrap();
    for context in 0..2 {
        assert_eq!(restored[context].parent(),baseline[context].parent());
        assert_eq!(restored[context].max_owner(),baseline[context].max_owner());
        assert_eq!(restored[context].value(),baseline[context].value());
    }
}

impl Prepared {
    fn owner_work_d(&self,owner:usize)->Result<Option<WorkDExpectation>,String> {
        if owner>=OWNERS {return Err("scheduled Work-D owner outside H21".into());}
        let mut source:Option<&BigUint>=None;
        for context in 0..2 {
            if let Some(j)=self.plan.max_index(context,owner) {
                let d=&self.max[context][j].d;
                if source.is_some_and(|prior|prior!=d) {
                    return Err("scheduled Work-D contexts disagree".into());
                }
                source=Some(d);
            }
        }
        Ok(source.map(|d|WorkDExpectation {owner,height:owner+2,
            cells:(0..224).map(|bit|(x(owner,D_BASE+bit),Fr::from(d.bit(bit as u64)as u64))).collect()}))
    }
    /// Conditional source contract only. No provenance or DAA proof is inferred.
    #[cfg(test)]
    pub(super) fn from_d_iter(input:impl IntoIterator<Item=(usize,BigUint)>)->Result<Self,String> {
        Self::from_d_iter_with_descriptor(CutDescriptor::diagnostic08(),input)
    }
    pub(super) fn from_d_iter_eligible08(input:impl IntoIterator<Item=(usize,BigUint)>)->Result<Self,String> {
        Self::from_d_iter_checked(CutDescriptor::eligible08(),input)
    }
    #[cfg(test)]
    pub(super) fn from_d_iter_with_descriptor(descriptor:CutDescriptor,input:impl IntoIterator<Item=(usize,BigUint)>)->Result<Self,String> {
        Self::from_d_iter_checked(descriptor,input)
    }
    fn from_d_iter_checked(descriptor:CutDescriptor,input:impl IntoIterator<Item=(usize,BigUint)>)->Result<Self,String> {
        let plan=Plan::with_descriptor(descriptor);let mut input=input.into_iter();
        let mut ds:[Vec<BigUint>;2]=std::array::from_fn(|_|Vec::with_capacity(7682));
        let mut current:[Option<BigUint>;2]=[None,None];let mut index=[0usize;2];
        for height in FIRST..=descriptor.terminals()[0] {
            let (actual,d)=input.next().ok_or("scheduled D stream missing height")?;
            if actual!=height {return Err("scheduled D stream height/order".into());}
            if d.is_zero() || d.bits()>224 {return Err("scheduled D stream positive U224".into());}
            for c in 0..2 {
                if height>descriptor.terminals()[c] {continue;}
                let e=plan.epochs[c][index[c]];
                if height==e.start {current[c]=Some(d.clone());}
                if current[c].as_ref()!=Some(&d) {return Err("scheduled D changes within epoch".into());}
                if height==e.end {ds[c].push(current[c].take().ok_or("scheduled epoch missing D")?);index[c]+=1;}
            }
        }
        if input.next().is_some() {return Err("scheduled D stream surplus".into());}
        if index!=std::array::from_fn(|c|plan.epochs[c].len()) {return Err("scheduled D epoch census".into());}
        let mut max:[Vec<MaxWitness>;2]=std::array::from_fn(|_|Vec::with_capacity(7682));
        let modulus=BigUint::from(1u8)<<224usize;
        for c in 0..2 {
            let mut t=BigUint::zero();
            for d in ds[c].iter().rev() {
                let less=d<&t;let r=d.clone().max(t.clone());
                let delta=if less {d+&modulus-&t}else{d-&t};
                max[c].push(MaxWitness {d:d.clone(),r:r.clone(),t,delta,less});t=r;
            }
            max[c].reverse();
            for g in &plan.caps[c] {cap::admit(&max[c][g.source].r)?;}
        }
        Ok(Self {plan,max})
    }
    pub(super) fn plan(&self)->&Plan {&self.plan}
    pub(super) fn descriptor(&self)->CutDescriptor {self.plan.descriptor}
    pub(super) fn score_spans(&self, context:usize)->Result<Vec<ScoreSpan>,String> {
        if context>=2 {return Err("Score source context".into());}
        let mut spans=Vec::new();
        for (epoch,maximum) in self.plan.epochs[context].iter().zip(&self.max[context]) {
            let first=epoch.start+self.descriptor().offset();
            if first>self.descriptor().guards()[context] {break;}
            let last=(epoch.end+self.descriptor().offset()).min(self.descriptor().guards()[context]);
            spans.push(ScoreSpan {first,last,value:cap::scalar(&maximum.r)?});
        }
        if spans.first().map(|s|s.first)!=Some(845760)
            ||spans.last().map(|s|s.last)!=Some(self.descriptor().guards()[context])
            ||spans.windows(2).any(|w|w[0].last+1!=w[1].first||w[0].value<w[1].value) {
            return Err("Score source exhaustive partition/monotonicity".into());
        }
        // The retained physical Cap at every right endpoint must be exactly
        // the scalar projection of this same Prepared snapshot.
        for span in &spans {
            if self.owner_patch(span.last-1)?.cap_value_65(context)?!=span.value {
                return Err("Score source retained Cap projection".into());
            }
        }
        Ok(spans)
    }
    /// Compare the complete epoch projection after replaying its source stream.
    /// The Plan is code-owned and reconstructed from the same fixed schedule.
    pub(super) fn source_replay_matches(&self, other:&Self)->bool {
        self.descriptor()==other.descriptor() && self.max==other.max
    }
    pub(super) fn owner_patch(&self,o:usize)->Result<Patch,String> {
        if o>=OWNERS {return Err("scheduled patch owner outside H21".into());}
        let mut spans=Vec::with_capacity(4);
        for c in 0..2 {
            if let Some(j)=self.plan.max_index(c,o) {
                let m=&self.max[c][j];let mut values=vec![Fr::zero();673];
                for (start,n) in [(0,&m.r),(224,&m.t),(448,&m.delta)] {
                    for k in 0..224 {values[start+k]=Fr::from(n.bit(k as u64)as u64);}
                }values[672]=Fr::from(m.less as u64);
                spans.push(Span {writer:Writer::Max {context:c,end:self.plan.epochs[c][j].end},start:MAX_BASE[c],values});
            }
            if let Some(j)=self.plan.cap_index(c,o) {
                let g=self.plan.caps[c][j];
                let values=cap::producer(&self.max[c][g.source].r)?;
                spans.push(Span {writer:Writer::Cap {context:c,origin:o+1},start:CAP_BASE[c],values});
            }
        }Ok(Patch {owner:o,spans})
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct Span {writer:Writer,start:usize,values:Vec<Fr>}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Patch {owner:usize,spans:Vec<Span>}
impl Patch {
    pub(super) fn writers(&self)->Vec<Writer> {self.spans.iter().map(|s|s.writer).collect()}
    pub(super) fn source_replay_matches(&self,other:&Self)->bool {self==other}
    pub(super) fn cap_value_65(&self,context:usize)->Result<BigUint,String> {
        if context>=2 {return Err("scheduled Cap value context".into());}
        let origin=self.owner.checked_add(1).ok_or("scheduled Cap origin overflow")?;
        let writer=Writer::Cap {context,origin};
        let span=self.spans.iter().find(|s|s.writer==writer)
            .ok_or("scheduled Cap value writer missing")?;
        if span.start!=CAP_BASE[context] || span.values.len()!=2048 {
            return Err("scheduled Cap value writer domain".into());
        }
        let mut out=BigUint::zero();
        for bit in 0..65 {
            let value=span.values.get(740+bit).ok_or("scheduled Cap value bit missing")?;
            if *value!=Fr::zero() && *value!=Fr::one() {
                return Err("scheduled Cap value is nonboolean".into());
            }
            if value.is_one() {out|=BigUint::from(1u8)<<bit;}
        }
        Ok(out)
    }
    pub(super) fn snapshot(&self)->Vec<(usize,usize,Writer,Vec<Fr>)> {
        self.spans.iter().map(|s|(self.owner,s.start,s.writer,s.values.clone())).collect()
    }
    #[cfg(test)]
    pub(super) fn duplicate_first_span_for_test(&self)->Self {
        let mut duplicate=self.clone();
        if let Some(span)=duplicate.spans.first().cloned(){duplicate.spans.push(span);}
        duplicate
    }
    #[cfg(test)]
    pub(super) fn set_owner_for_test(&mut self,owner:usize) { self.owner=owner; }
    #[cfg(test)]
    pub(super) fn set_writer_for_test(&mut self,index:usize,writer:Writer)->Result<(),String> {
        self.spans.get_mut(index).ok_or("scheduled test writer index")?.writer=writer;
        Ok(())
    }
}

/// Identity of the one admitted native H21 source and its fixed Eligible08 cut.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct NativeParent {
    root: [u8; 32],
    total: [u8; 28],
    profile: [u8; 32],
    cut: CutDescriptor,
}
impl NativeParent {
    #[cfg(test)]
    pub(super) fn different_cut_for_test(&self)->Self {
        let mut different=self.clone();different.cut=CutDescriptor::diagnostic08();different
    }
    pub(super) fn checked(plan:&crate::work_tree_history_plan::WorkTreeHistoryPlan,
        prefix:&crate::packed_owner_assembly::NativePrefix)->Result<Self,String> {
        crate::packed_owner_assembly::validate_native_plan_input(plan,prefix)?;
        if plan.headers()!=LAST as u64 || plan.slot_log()!=21
            || plan.slots()!=OWNERS || prefix.header_count()!=LAST {
            return Err("Eligible08 MAX/Cap exact native H21 parent".into());
        }
        Ok(Self {root:plan.descriptor().root,total:plan.work_profile().total_be28,
            profile:prefix.profile(),cut:CutDescriptor::eligible08()})
    }
}

/// Replays D exactly once. Subsequent owner leases read only this immutable
/// snapshot and never ask NativePrefix to rescan the full difficulty range.
pub(super) struct Eligible08NativeSnapshot {
    parent: NativeParent,
    prepared: Prepared,
}

#[derive(Clone)]
pub(super) struct Eligible08OwnerLease {
    parent: NativeParent,
    owner: usize,
    patch: Patch,
    rows: Vec<(Writer,Term)>,
    work_d:Option<WorkDExpectation>,
}

/// Expected HEADER Work-D inputs, projected solely from Prepared's epoch D.
#[derive(Clone,Debug,PartialEq,Eq)]
pub(super) struct WorkDExpectation {owner:usize,height:usize,cells:Vec<(usize,Fr)>}
impl WorkDExpectation {
    pub(super) fn owner(&self)->usize {self.owner}
    pub(super) fn height(&self)->usize {self.height}
    pub(super) fn cells(&self)->&[(usize,Fr)] {&self.cells}
}

pub(super) struct FirstModernCapLease {
    source: Eligible08OwnerLease,
    destination: Eligible08OwnerLease,
}

impl Eligible08NativeSnapshot {
    pub(super) fn new(plan:&crate::work_tree_history_plan::WorkTreeHistoryPlan,
        prefix:&crate::packed_owner_assembly::NativePrefix)->Result<Self,String> {
        let parent=NativeParent::checked(plan,prefix)?;
        let mut first_error=None;
        let stream=(FIRST..=LAST).map_while(|height| {
            if first_error.is_some() {return None;}
            match prefix.compact_n_bits(height).and_then(crate::work_tree_work::native_decode) {
                Ok(d)=>Some((height,d)),
                Err(error)=>{
                    first_error=Some(format!("Eligible08 native D height={height}: {error}"));
                    None
                }
            }
        });
        let prepared_result=Prepared::from_d_iter_eligible08(stream);
        if let Some(error)=first_error {return Err(error);}
        let prepared=prepared_result?;
        if prepared.descriptor()!=parent.cut {
            return Err("Eligible08 MAX/Cap prepared cut".into());
        }
        Ok(Self {parent,prepared})
    }

    pub(super) fn require_native_parent(
        &self,plan:&crate::work_tree_history_plan::WorkTreeHistoryPlan,
        prefix:&crate::packed_owner_assembly::NativePrefix)->Result<(),String> {
        if self.parent!=NativeParent::checked(plan,prefix)? {
            return Err("Eligible08 MAX/Cap parent/root/total/profile/cut mismatch".into());
        }
        Ok(())
    }

    pub(super) fn owner_lease(&self,owner:usize)->Result<Eligible08OwnerLease,String> {
        if self.prepared.descriptor()!=self.parent.cut
            || self.parent.cut!=CutDescriptor::eligible08() {
            return Err("Eligible08 MAX/Cap snapshot cut".into());
        }
        let patch=self.prepared.owner_patch(owner)?;
        let mut received=OwnerCells::new(owner)?;
        patch.apply(&mut received)?;
        let mut rows=Vec::new();
        self.prepared.plan().visit_owner(owner,|writer,term| {
            rows.push((writer,term));Ok(())
        })?;
        let patch_writers=patch.writers().into_iter().collect::<std::collections::BTreeSet<_>>();
        let row_writers=rows.iter().map(|(writer,_)|*writer)
            .collect::<std::collections::BTreeSet<_>>();
        if patch_writers!=row_writers || patch_writers.len()!=patch.writers().len() {
            return Err("Eligible08 MAX/Cap writer/ROW census".into());
        }
        let work_d=self.prepared.owner_work_d(owner)?;
        Ok(Eligible08OwnerLease {parent:self.parent.clone(),owner,patch,rows,work_d})
    }

    pub(super) fn parent(&self)->NativeParent {self.parent.clone()}
    pub(super) fn scheduled_plan(&self)->&Plan {self.prepared.plan()}
    pub(super) fn require_plan_parent(&self,plan:&crate::work_tree_history_plan::WorkTreeHistoryPlan)
        ->Result<(),String> {
        use blake2::{digest::consts::U32,Blake2b,Digest};
        let mut bytes=crate::work_tree_fixed_hash::PROFILE_PREFIX.to_vec();
        bytes.extend_from_slice(&crate::header_order::MAINNET_GENESIS);
        let expected_profile:[u8;32]=Blake2b::<U32>::digest(bytes).into();
        if plan.headers()!=LAST as u64 || plan.slot_log()!=21 || plan.slots()!=OWNERS
            || self.parent.root!=plan.descriptor().root
            || self.parent.total!=plan.work_profile().total_be28
            || self.parent.profile!=expected_profile
            || plan.fixed_profile().genesis!=crate::header_order::MAINNET_GENESIS
            || plan.fixed_profile().prefix.as_slice()!=crate::work_tree_fixed_hash::PROFILE_PREFIX.as_slice()
            || plan.fixed_profile().native_work_sha256!=crate::work_tree_fixed_hash::NATIVE_WORK_SHA256
            || plan.leaf_profile().native_work_sha256!=crate::work_tree_fixed_hash::NATIVE_WORK_SHA256
            || plan.work_profile().native_work_sha256!=crate::work_tree_fixed_hash::NATIVE_WORK_SHA256
            || self.parent.cut!=CutDescriptor::eligible08()
            || self.prepared.descriptor()!=self.parent.cut {
            return Err("scheduled ledger exact plan/root/total/cut".into());
        }
        Ok(())
    }

    #[cfg(test)]
    pub(super) fn constant_d_for_test(root:[u8;32],total:[u8;28],profile:[u8;32],d:u8)
        ->Result<Self,String> {
        Self::constant_scalar_d_for_test(root,total,profile,BigUint::from(d))
    }
    #[cfg(test)]
    pub(super) fn constant_scalar_d_for_test(root:[u8;32],total:[u8;28],profile:[u8;32],d:BigUint)
        ->Result<Self,String> {
        let prepared=Prepared::from_d_iter_eligible08(
            (FIRST..=LAST).map(|height|(height,d.clone())))?;
        Ok(Self {parent:NativeParent {root,total,profile,cut:CutDescriptor::eligible08()},prepared})
    }

    /// The first modern Cap imports exactly the source MAX at owner 844670.
    pub(super) fn first_modern_cap_lease(
        &self,plan:&crate::work_tree_history_plan::WorkTreeHistoryPlan,
        prefix:&crate::packed_owner_assembly::NativePrefix)->Result<FirstModernCapLease,String> {
        self.require_native_parent(plan,prefix)?;
        self.first_modern_from_snapshot()
    }

    fn first_modern_from_snapshot(&self)->Result<FirstModernCapLease,String> {
        let lease=FirstModernCapLease {
            source:self.owner_lease(FIRST-2)?,
            destination:self.owner_lease(845_759)?,
        };
        lease.check_exact(self)?;
        Ok(lease)
    }

    #[cfg(test)]
    pub(super) fn first_modern_constant_d_for_test(
        root:[u8;32],total:[u8;28],profile:[u8;32],d:u8,
    )->Result<FirstModernCapLease,String> {
        let prepared=Prepared::from_d_iter_eligible08(
            (FIRST..=LAST).map(|height|(height,BigUint::from(d))))?;
        Self {parent:NativeParent {root,total,profile,cut:CutDescriptor::eligible08()},prepared}
            .first_modern_from_snapshot()
    }
}

impl Eligible08OwnerLease {
    pub(super) fn check_exact(&self,snapshot:&Eligible08NativeSnapshot)->Result<(),String> {
        if self.parent!=snapshot.parent
            || !self.patch.source_replay_matches(&snapshot.prepared.owner_patch(self.owner)?) {
            return Err("Eligible08 MAX/Cap owner patch parent/source".into());
        }
        let mut rows=Vec::new();
        snapshot.prepared.plan().visit_owner(self.owner,|writer,term| {
            rows.push((writer,term));Ok(())
        })?;
        if self.rows!=rows {return Err("Eligible08 MAX/Cap owner ROW source".into());}
        if self.work_d!=snapshot.prepared.owner_work_d(self.owner)? {
            return Err("Eligible08 MAX/Cap owner Work-D expectation source".into());
        }
        Ok(())
    }
    pub(super) fn work_d(&self)->Option<&WorkDExpectation> {self.work_d.as_ref()}
    #[cfg(test)]
    pub(super) fn flip_work_d_bit_for_test(&mut self) {
        let bit=&mut self.work_d.as_mut().unwrap().cells[0].1;*bit=Fr::one()-*bit;
    }
    pub(super) fn owner(&self)->usize {self.owner}
    pub(super) fn cells(&self)->Vec<(usize,Writer,Fr)> {
        self.patch.snapshot().into_iter().flat_map(|(owner,start,writer,values)|
            values.into_iter().enumerate().map(move |(k,value)|(x(owner,start+k),writer,value))).collect()
    }
    pub(super) fn apply(&self,target:&mut OwnerCells)->Result<(),String> {
        self.patch.apply(target)
    }
    pub(super) fn visit_rows(&self,mut sink:impl FnMut(Writer,&Term)->Result<(),String>)
        ->Result<(),String> {
        for (writer,term) in &self.rows {sink(*writer,term)?;}Ok(())
    }
}

impl FirstModernCapLease {
    /// Require the exact checked snapshot that minted this lease, not merely
    /// a matching parent identity. This catches same-parent test mutations of
    /// the sealed destination patch before downstream materialization.
    pub(super) fn require_exact_native_snapshot(
        &self,
        snapshot: &Eligible08NativeSnapshot,
        plan: &crate::work_tree_history_plan::WorkTreeHistoryPlan,
        prefix: &crate::packed_owner_assembly::NativePrefix,
    ) -> Result<(), String> {
        snapshot.require_native_parent(plan, prefix)?;
        snapshot.require_plan_parent(plan)?;
        self.require_native_parent(plan, prefix)?;
        self.check_exact(snapshot)
    }

    pub(super) fn require_native_parent(
        &self,plan:&crate::work_tree_history_plan::WorkTreeHistoryPlan,
        prefix:&crate::packed_owner_assembly::NativePrefix,
    )->Result<(),String> {
        let expected=NativeParent::checked(plan,prefix)?;
        if self.source.parent!=expected || self.destination.parent!=expected
            || self.source.owner!=FIRST-2 || self.destination.owner!=845_759 {
            return Err("Eligible08 first Cap lease parent/cut/source owners".into());
        }
        Ok(())
    }

    pub(super) fn require_stage_identity(
        &self,root:[u8;32],total:[u8;28],profile:[u8;32],cut_identity:&[u8],
    )->Result<(),String> {
        if self.source.parent!=self.destination.parent
            || self.source.parent.root!=root || self.source.parent.total!=total
            || self.source.parent.profile!=profile
            || self.source.parent.cut.canonical_identity()!=cut_identity {
            return Err("Eligible08 first Cap lease stage parent/cut identity".into());
        }
        Ok(())
    }

    fn cap_span(&self,context:usize)->Result<&Span,String> {
        if context>=2 {return Err("Eligible08 first Cap context".into());}
        let writer=Writer::Cap {context,origin:845_760};
        let span=self.destination.patch.spans.iter().find(|span|span.writer==writer)
            .ok_or("Eligible08 first Cap destination writer")?;
        if span.start!=CAP_BASE[context] || span.values.len()!=2048 {
            return Err("Eligible08 first Cap destination domain".into());
        }
        Ok(span)
    }

    /// All 2,048 physical Cap cells are authored by the checked patch, not
    /// just the 65 q bits subsequently read by modern Score.
    pub(super) fn cap_cells(&self,context:usize)->Result<Vec<(usize,bool)>,String> {
        let span=self.cap_span(context)?;
        span.values.iter().enumerate().map(|(local,value)| {
            if *value!=Fr::zero() && *value!=Fr::one() {
                return Err("Eligible08 first Cap nonboolean cell".into());
            }
            Ok((CAP_BASE[context]+local,value.is_one()))
        }).collect()
    }

    pub(super) fn cap_rows(&self,context:usize)->Result<Vec<Term>,String> {
        self.cap_span(context)?;
        let writer=Writer::Cap {context,origin:845_760};
        let rows=self.destination.rows.iter().filter(|(source,_)|*source==writer)
            .map(|(_,term)|term.clone()).collect::<Vec<_>>();
        if rows.len()!=6419 {return Err("Eligible08 first Cap ROW census".into());}
        Ok(rows)
    }

    fn check_imports(&self)->Result<(),String> {
        if self.source.parent!=self.destination.parent
            || self.source.owner!=FIRST-2 || self.destination.owner!=845_759 {
            return Err("Eligible08 first Cap parent/owner pair".into());
        }
        for context in 0..2 {
            let source_writer=Writer::Max {context,end:FIRST};
            let source_span=self.source.patch.spans.iter()
                .find(|span|span.writer==source_writer)
                .ok_or("Eligible08 first Cap source MAX writer")?;
            if source_span.start!=MAX_BASE[context] || source_span.values.len()!=673 {
                return Err("Eligible08 first Cap source MAX domain".into());
            }
            let mut maximum=BigUint::zero();
            for k in 0..224 {
                let bit=source_span.values[k];
                if bit!=Fr::zero() && bit!=Fr::one() {
                    return Err("Eligible08 first Cap source MAX nonboolean".into());
                }
                if bit.is_one() {maximum|=BigUint::from(1u8)<<k;}
            }
            let q=self.destination.patch.cap_value_65(context)?;
            if q!=cap::scalar(&maximum)? {
                return Err("Eligible08 first Cap q/MAX source".into());
            }
            let cap_writer=Writer::Cap {context,origin:845_760};
            for k in 0..224 {
                let wanted_row=row(845_759,cap_row(ComponentRows::high_candidate(),context,1383+k));
                let wanted_x=x(FIRST-2,MAX_BASE[context]+k);
                let hits=self.destination.rows.iter().filter(|(writer,term)| {
                    *writer==cap_writer && term.row==wanted_row
                        && term.gate.left==wanted_x && term.gate.c1==-Fr::one()
                        && term.gate.c0.is_zero() && term.gate.c2.is_zero()
                        && term.gate.c3.is_zero()
                }).count();
                if hits!=1 {return Err("Eligible08 first Cap physical MAX import".into());}
            }
        }
        Ok(())
    }
    fn check_exact(&self,snapshot:&Eligible08NativeSnapshot)->Result<(),String> {
        self.source.check_exact(snapshot)?;
        self.destination.check_exact(snapshot)?;
        self.check_imports()
    }
    pub(super) fn cap_cell(&self,context:usize,bit:usize)->Result<(usize,bool),String> {
        if context>=2 || bit>=65 {return Err("Eligible08 first Cap q context/bit".into());}
        let span=self.cap_span(context)?;
        let value=span.values[740+bit];
        if value!=Fr::zero() && value!=Fr::one() {
            return Err("Eligible08 first Cap q nonboolean".into());
        }
        Ok((x(self.destination.owner,CAP_BASE[context]+740+bit),value.is_one()))
    }
    #[cfg(test)]
    pub(super) fn flip_cap_q_bit_for_test(&mut self,context:usize,bit:usize)
        ->Result<(),String> {
        if context>=2 || bit>=65 {return Err("Eligible08 first Cap test q context/bit".into());}
        let writer=Writer::Cap {context,origin:845_760};
        let span=self.destination.patch.spans.iter_mut().find(|span|span.writer==writer)
            .ok_or("Eligible08 first Cap test destination writer")?;
        if span.start!=CAP_BASE[context] || span.values.len()!=2048 {
            return Err("Eligible08 first Cap test destination domain".into());
        }
        let value=&mut span.values[740+bit];
        if *value==Fr::zero(){*value=Fr::one();}
        else if *value==Fr::one(){*value=Fr::zero();}
        else {return Err("Eligible08 first Cap test nonboolean bit".into());}
        Ok(())
    }
}
/// A sparse owner-local receiving surface, with strict semantic writer exclusion.
pub(super) struct OwnerCells {owner:usize,cells:BTreeMap<usize,(Writer,Fr)>}
impl OwnerCells {
    pub(super) fn new(owner:usize)->Result<Self,String> {
        if owner>=OWNERS {return Err("scheduled cell owner outside H21".into());}
        Ok(Self {owner,cells:BTreeMap::new()})
    }
    pub(super) fn read(&self,local:usize)->Result<Fr,String> {
        self.cells.get(&local).map(|p|p.1).ok_or_else(||"missing scheduled cell".into())
    }
}
impl Patch {
    pub(super) fn apply(&self,target:&mut OwnerCells)->Result<(),String> {
        if self.owner!=target.owner {return Err("scheduled patch owner mismatch".into());}
        let mut staged=BTreeMap::new();
        for s in &self.spans {
            let (start,len)=match s.writer {
                Writer::Max {context,end} if context<2 && end.checked_sub(2)==Some(self.owner)=>(MAX_BASE[context],673),
                Writer::Cap {context,origin} if context<2 && origin.checked_sub(1)==Some(self.owner)=>(CAP_BASE[context],2048),
                _=>return Err("scheduled semantic writer identity".into()),
            };
            if s.start!=start || s.values.len()!=len {return Err("scheduled writer domain".into());}
            for (k,&v) in s.values.iter().enumerate() {
                if v!=Fr::zero() && v!=Fr::one() {return Err("scheduled nonboolean patch".into());}
                let w=start+k;
                if target.cells.contains_key(&w) || staged.insert(w,(s.writer,v)).is_some() {
                    return Err("scheduled duplicate semantic writer".into());
                }
            }
        }
        target.cells.extend(staged);Ok(())
    }
}

#[cfg(test)]
#[path="h21_scheduled_max_cap_tests.rs"]
mod tests;

#[cfg(test)]
mod scheduled_lease_tests {
    use super::*;
    fn profile()->[u8;32] {
        use blake2::{digest::consts::U32,Blake2b,Digest};
        let mut bytes=crate::work_tree_fixed_hash::PROFILE_PREFIX.to_vec();
        bytes.extend_from_slice(&crate::header_order::MAINNET_GENESIS);
        Blake2b::<U32>::digest(bytes).into()
    }
    #[test]
    fn c183_synthetic_exact_lease_parent_cut_owner_rows_and_source_mutants() {
        let snapshot=Eligible08NativeSnapshot::constant_d_for_test([17;32],[0;28],profile(),16).unwrap();
        let lease=snapshot.owner_lease(844670).unwrap();lease.check_exact(&snapshot).unwrap();
        for field in 0..10 {
            let mut wrong=lease.clone();
            match field {
                0=>wrong.parent.root[0]^=1,
                1=>wrong.parent.total[0]^=1,
                2=>wrong.parent.profile[0]^=1,
                3=>wrong.parent.cut=CutDescriptor::diagnostic08(),
                4=>wrong.owner=844798,
                5=>wrong.patch.owner=844798,
                6=>wrong.patch.spans[0].writer=Writer::Max{context:1,end:844672},
                7=>wrong.patch.spans[0].values[0]+=Fr::one(),
                8=>{wrong.patch.spans.pop();},
                9=>wrong.patch.spans.push(wrong.patch.spans[0].clone()),
                _=>unreachable!(),
            }
            assert_eq!(wrong.check_exact(&snapshot).unwrap_err(),"Eligible08 MAX/Cap owner patch parent/source","field {field}");
        }
        for field in 0..4 {
            let mut wrong=lease.clone();
            match field {
                0=>wrong.rows[0].1.gate.c0+=Fr::one(),
                1=>wrong.rows.swap(0,1),
                2=>{wrong.rows.pop();},
                _=>wrong.rows.push(wrong.rows[0].clone()),
            }
            assert_eq!(wrong.check_exact(&snapshot).unwrap_err(),"Eligible08 MAX/Cap owner ROW source");
        }
        let parent=crate::work_tree_history_plan::WorkTreeHistoryPlan::compile(1827840,21,[17;32],[0;28]).unwrap();
        snapshot.require_plan_parent(&parent).unwrap();
        let mut wrong=Eligible08NativeSnapshot::constant_d_for_test([17;32],[0;28],profile(),16).unwrap();
        wrong.parent.root[0]^=1;
        assert_eq!(wrong.require_plan_parent(&parent).unwrap_err(),"scheduled ledger exact plan/root/total/cut");
        let mut wrong=Eligible08NativeSnapshot::constant_d_for_test([17;32],[0;28],profile(),16).unwrap();
        wrong.parent.total[0]^=1;
        assert_eq!(wrong.require_plan_parent(&parent).unwrap_err(),"scheduled ledger exact plan/root/total/cut");
        let mut wrong=Eligible08NativeSnapshot::constant_d_for_test([17;32],[0;28],profile(),16).unwrap();
        wrong.parent.cut=CutDescriptor::diagnostic08();
        assert_eq!(wrong.require_plan_parent(&parent).unwrap_err(),"scheduled ledger exact plan/root/total/cut");
    }

    #[test]
    fn c184_prepared_d_expectation_differs_from_r_and_rejects_projection_mutants() {
        let prepared=Prepared::from_d_iter_eligible08((FIRST..=LAST).map(|height|
            (height,BigUint::from(if height==FIRST {16u8}else{32u8})))).unwrap();
        let mut snapshot=Eligible08NativeSnapshot{parent:NativeParent{root:[17;32],total:[0;28],
            profile:profile(),cut:CutDescriptor::eligible08()},prepared};
        let lease=snapshot.owner_lease(844670).unwrap();
        let expected=lease.work_d().unwrap();assert_eq!(expected.height(),844672);
        assert_eq!(expected.cells().len(),224);
        assert_eq!(expected.cells()[4].1,Fr::one());assert_eq!(expected.cells()[5].1,Fr::zero());
        // R is 32, whereas this epoch's HEADER D is 16.
        assert_eq!(lease.patch.spans[0].values[4],Fr::zero());
        assert_eq!(lease.patch.spans[0].values[5],Fr::one());
        for field in 0..7 {
            let mut wrong=lease.clone();
            match field {
                0=>wrong.flip_work_d_bit_for_test(),
                1=>wrong.work_d.as_mut().unwrap().owner+=1,
                2=>wrong.work_d.as_mut().unwrap().height+=1,
                3=>{wrong.work_d.as_mut().unwrap().cells.pop();},
                4=>{let cell=wrong.work_d.as_ref().unwrap().cells[0];wrong.work_d.as_mut().unwrap().cells.push(cell);},
                5=>wrong.work_d.as_mut().unwrap().cells[0].0+=1,
                _=>wrong.work_d=None,
            }
            assert_eq!(wrong.check_exact(&snapshot).unwrap_err(),"Eligible08 MAX/Cap owner Work-D expectation source");
        }
        snapshot.prepared.max[1][0].d+=BigUint::from(1u8);
        assert_eq!(snapshot.owner_lease(844670).err().unwrap(),"scheduled Work-D contexts disagree");
    }
}

#[cfg(test)]
mod eligible_calendar_tests {
    use super::*;
    #[test]
    fn c182_owner_kernels_match_exact_schedule_lists_for_both_cuts() {
        for p in [Plan::new(),Plan::eligible08()] {
            for seed in [3u64,109] {
                let point=|offset| (0..21).map(|b|Fr::from(seed+offset+37*b)).collect::<Vec<_>>();
                let r=point(0);let u=point(43);let v=point(113);
                let weight=|o|eq(&r,o)*eq(&u,o)*eq(&v,o);
                let mut exact=[Fr::zero();4];
                for c in 0..2 {
                    exact[c]=p.epochs[c].iter().map(|e|weight(e.owner())).sum();
                    exact[2+c]=p.caps[c].iter().map(|g|weight(g.owner)).sum();
                }
                assert_eq!(p.anchor_owner_weights(&r,&u,&v).unwrap(),exact,
                    "exact emitted schedule lists {:?} seed {seed}",p.descriptor);
                for bad in 0..3 {
                    let mut points=[r.clone(),u.clone(),v.clone()];points[bad].pop();
                    assert_eq!(p.anchor_owner_weights(&points[0],&points[1],&points[2]).unwrap_err(),
                        "scheduled owner coefficient dimensions");
                }
            }
        }
    }
    fn stream()->impl Iterator<Item=(usize,BigUint)> {
        (844672..=1827840).map(|h|(h,BigUint::from(5u8)))
    }
    fn bits(n:usize,len:usize)->Vec<Fr> {(0..len).map(|b|Fr::from(((n>>b)&1)as u64)).collect()}
    fn oracle_epochs(terminal:usize)->Vec<(usize,usize)> {
        let mut out=vec![(844672,844672)];
        for start in (844673..=terminal).step_by(128) {out.push((start,(start+127).min(terminal)));}
        out
    }
    fn oracle_caps(guard:usize,terminal:usize)->Vec<(usize,usize)> {
        let mut out=Vec::new();
        for origin in (845760..=guard).step_by(128) {out.push((origin-1,origin-1090));}
        if out.last().unwrap().0!=guard-1 {
            let q=guard-1088;
            let end=(844672+((q-844672+127)/128)*128).min(terminal);
            out.push((guard-1,end-2));
        }
        out
    }
    #[test]
    fn c164_eligible_descriptor_census_partition_and_clipped_sources() {
        let p=Plan::eligible08();
        assert_eq!(p.epochs.each_ref().map(|e|e.len()),[7682,7550]);
        assert_eq!(p.caps.each_ref().map(|g|g.len()),[7542,7541]);
        for (c,(terminal,guard)) in [(1827840,1810905),(1810842,1810842)].into_iter().enumerate() {
            let expected=oracle_epochs(terminal);
            assert_eq!(p.epochs[c].iter().map(|e|(e.start,e.end)).collect::<Vec<_>>(),expected);
            assert_eq!(expected[0],(844672,844672));
            assert!(expected.windows(2).all(|w|w[0].1+1==w[1].0));
            assert_eq!(p.caps[c].iter().map(|g|(g.owner,p.epochs[c][g.source].owner())).collect::<Vec<_>>(),oracle_caps(guard,terminal));
        }
        assert_eq!(p.epochs[1].last().unwrap().owner(),1810840);
        assert_eq!((p.epochs[1][7548].start,p.epochs[1][7548].end),(1810689,1810816));
        assert_eq!((p.epochs[1][7549].start,p.epochs[1][7549].end),(1810817,1810842));
        assert!(p.epochs[0].iter().any(|e|e.end==1827840),"c0 MAX extends past f through N");
        assert_eq!(p.epochs[1][7548].owner(),1810814);
        assert_eq!(p.epochs[1].last().unwrap().owner()-p.epochs[1][7548].owner(),26);
        for (c,dest,src) in [(0,1810904,1809918),(1,1810841,1809790)] {
            let g=p.caps[c].last().unwrap();assert_eq!((g.owner,p.epochs[c][g.source].owner()),(dest,src));
        }
        let diagnostic=CutDescriptor::diagnostic08();let eligible=CutDescriptor::eligible08();
        assert_ne!(diagnostic.canonical_identity(),eligible.canonical_identity());
        for (n,h,f,l,k0,modes) in [(LAST,1810843,1810905,1024,64,eligible.modes()),
            (LAST,1810842,1810906,1024,64,eligible.modes()),(LAST,1810842,1810905,1023,64,eligible.modes()),
            (LAST,1810842,1810905,1024,63,eligible.modes()),
            (LAST,1810842,1810905,1024,64,[MaturityMode::Exact,MaturityMode::Exact]),
            (LAST-1,1810842,1810905,1024,64,eligible.modes())] {
            assert!(CutDescriptor::checked(CutProfile::Eligible08,n,h,f,l,k0,modes).is_err());
        }
    }
    #[test]
    fn c164_eligible_score_endpoints_order_and_missing_clipped_cell() {
        let p=Prepared::from_d_iter_eligible08(stream()).unwrap();
        for (c,count,last) in [(0,7542,1810905),(1,7541,1810842)] {
            let spans=p.score_spans(c).unwrap();assert_eq!(spans.len(),count);
            assert_eq!((spans[0].first,spans[0].last),(845760,845760));
            assert_eq!(spans.last().unwrap().last,last);
            assert_eq!(spans.last().unwrap().first,if c==0 {1810881}else{1810753});
            assert_eq!(spans.last().unwrap().last-spans.last().unwrap().first+1,if c==0 {25}else{90});
            assert!(spans.windows(2).all(|w|w[0].last+1==w[1].first));
            let patch=p.owner_patch(last-1).unwrap();let mut cells=OwnerCells::new(last-1).unwrap();
            patch.apply(&mut cells).unwrap();assert_eq!(patch.cap_value_65(c).unwrap(),spans.last().unwrap().value);
            cells.cells.remove(&(CAP_BASE[c]+740));assert_eq!(cells.read(CAP_BASE[c]+740).unwrap_err(),"missing scheduled cell");
            let mut missing=patch.clone();missing.spans.iter_mut().find(|s|s.writer==Writer::Cap {context:c,origin:last}).unwrap().values.pop();
            assert!(missing.apply(&mut OwnerCells::new(last-1).unwrap()).is_err());
        }
        let mut missing=p;missing.plan.caps[0].pop();
        assert_eq!(missing.score_spans(0).unwrap_err(),"scheduled Cap value writer missing");
        assert!(Prepared::from_d_iter_eligible08(stream().filter(|(h,_)|*h!=1810904)).is_err());
        assert!(Prepared::from_d_iter_eligible08(stream().map(|(h,d)|(h,if h==900001 {BigUint::from(6u8)}else{d}))).is_err());
    }
    #[test]
    fn c164_diagnostic08_exact_calendar_and_source_parity() {
        let old=Prepared::from_d_iter(stream()).unwrap();
        let named=Prepared::from_d_iter_with_descriptor(CutDescriptor::diagnostic08(),stream()).unwrap();
        assert!(old.source_replay_matches(&named));
        assert_eq!(Plan::new().descriptor,CutDescriptor::diagnostic08());
        for (c,terminal,guard,count) in [(0,1827840,1827838,7674),(1,1827775,1827775,7673)] {
            assert_eq!(old.plan.epochs[c].iter().map(|e|(e.start,e.end)).collect::<Vec<_>>(),oracle_epochs(terminal));
            assert_eq!(old.plan.caps[c].iter().map(|g|(g.owner,old.plan.epochs[c][g.source].owner())).collect::<Vec<_>>(),oracle_caps(guard,terminal));
            assert_eq!(old.score_spans(c).unwrap().len(),count);
            assert_eq!(old.owner_patch(guard-1).unwrap(),named.owner_patch(guard-1).unwrap());
        }
        let eligible=Prepared::from_d_iter_eligible08(stream()).unwrap();
        assert!(!old.source_replay_matches(&eligible));
        assert_eq!(old.owner_patch(844670).unwrap(),eligible.owner_patch(844670).unwrap(),"shared patch does not identify profile");
    }
    fn tuple(p:&Plan,o:usize,q:usize,left:usize,right:usize)->[Fr;4] {
        let mut emitted=[Fr::zero();4];
        p.visit_owner(o,|_,t| {if (t.row,t.gate.left,t.gate.right)==(row(o,q),left,right) {
            for (a,b) in emitted.iter_mut().zip([t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3]) {*a+=b;}
        }Ok(())}).unwrap();
        let analytic=p.coefficients(&bits(row(o,q),40),&bits(left,41),&bits(right,41)).unwrap();
        assert_eq!(analytic,emitted,"emitter/analytic tuple owner={o} row={q}");analytic
    }
    #[test]
    fn c164_eligible_exact_analytic_boundaries_and_isolated_offsets() {
        let p=Plan::eligible08();let z=Fr::zero();let one=Fr::one();
        for (c,o) in [(0,844670),(0,844798),(0,1827710),(0,1827838),
            (1,844670),(1,844798),(1,1810686),(1,1810814),(1,1810840)] {
            assert_eq!(tuple(&p,o,MAX_ROW[c]+7,x(o,MAX_BASE[c]+7),x(o,MAX_BASE[c]+7)),[z,-one,z,one]);
        }
        for (c,o,next) in [(0,844670,844798),(0,1827710,1827838),(1,844670,844798),
            (1,1810686,1810814),(1,1810814,1810840)] {
            let q=p.rows.max_extra[c]+225+7;
            assert_eq!(tuple(&p,o,q,x(next,MAX_BASE[c]+7),x(o,0)),[z,-one,z,z]);
            for bad in [next-1,next+1,o+128] {if bad!=next {assert_eq!(tuple(&p,o,q,x(bad,MAX_BASE[c]+7),x(o,0)),[z;4]);}}
        }
        for (c,o,src) in [(0,845759,844670),(1,845759,844670),(0,1810879,1809790),
            (1,1810751,1809662),(0,1810904,1809918),(1,1810841,1809790)] {
            let q=CAP_ROW[c]+1383+7;
            assert_eq!(tuple(&p,o,q,x(src,MAX_BASE[c]+7),x(o,CAP_BASE[c])),[z,-one,z,z]);
            for bad in [src-1,src+1,o-1089] {if bad!=src {assert_eq!(tuple(&p,o,q,x(bad,MAX_BASE[c]+7),x(o,CAP_BASE[c])),[z;4]);}}
            assert_eq!(tuple(&p,o,q,x(src,MAX_BASE[c]+7),x(o+1,CAP_BASE[c])),[z;4]);
        }
        for (c,o) in [(0,1811007),(1,1810879)] {
            assert_eq!(tuple(&p,o,CAP_ROW[c]+1383+7,x(o-1089,MAX_BASE[c]+7),x(o,CAP_BASE[c])),[z;4]);
        }
        for (c,o) in [(0,1827838),(1,1810840)] {
            assert_eq!(tuple(&p,o,p.rows.max_extra[c]+232,x(o+128,MAX_BASE[c]+7),x(o,0)),[z;4]);
        }
        assert_eq!(tuple(&p,1827773,MAX_ROW[1]+7,x(1827773,MAX_BASE[1]+7),x(1827773,MAX_BASE[1]+7)),[z;4]);
    }

    // Independent height-space sums and literal local gate arithmetic. Neither
    // the production epoch/cap vectors nor visit_owner participate in this oracle.
    fn independent_coefficients(r:&[Fr],u:&[Fr],v:&[Fr])->[Fr;4] {
        let mut out=[Fr::zero();4];let one=Fr::one();
        for (c,terminal,guard) in [(0,1827840,1810905),(1,1810842,1810842)] {
            let owner_weight=|o,source|eq(&r[19..],o)*eq(&u[20..],source)*eq(&v[20..],o);
            let epochs=oracle_epochs(terminal);
            let self_weight:Fr=epochs.iter().map(|e|owner_weight(e.1-2,e.1-2)).sum();
            let next_weight:Fr=epochs.windows(2).map(|w|owner_weight(w[0].1-2,w[1].1-2)).sum();
            let guards=oracle_caps(guard,terminal);
            let cap_self:Fr=guards.iter().map(|(o,_)|owner_weight(*o,*o)).sum();
            let cap_import:Fr=guards.iter().map(|(o,s)|owner_weight(*o,*s)).sum();
            let mut add=|q:usize,l:usize,rt:usize,channel:usize,value:Fr,weight:Fr| {
                out[channel]+=eq(&r[..19],q)*eq(&u[..20],l)*eq(&v[..20],rt)*value*weight;
            };
            let b=MAX_BASE[c];let e=if c==0 {475136}else{475585};
            for k in 0..673 {add(MAX_ROW[c]+k,b+k,b+k,1,-one,self_weight);add(MAX_ROW[c]+k,b+k,b+k,3,one,self_weight);}
            let mut power=one;
            for k in 0..224 {
                for (local,sign) in [(987674+k,one),(b+224+k,-one),(b+448+k,-one)] {add(e,local,0,1,sign*power,self_weight);}
                power+=power;
                add(e+1+k,b+k,0,1,one,self_weight);add(e+1+k,987674+k,0,1,-one,self_weight);
                add(e+1+k,b+672,b+224+k,3,-one,self_weight);add(e+1+k,b+672,987674+k,3,one,self_weight);
                add(e+225+k,b+224+k,0,1,one,self_weight);add(e+225+k,b+k,0,1,-one,next_weight);
            }
            add(e,b+672,0,1,power,self_weight);
            cap_literal(|q,l,rt,import,a| {
                let physical_row=if q<2048 {CAP_ROW[c]+q}else{[476034,476554][c]+q-2048};
                let left=if import {MAX_BASE[c]+l}else{CAP_BASE[c]+l};
                for (j,value) in a.into_iter().enumerate() {add(physical_row,left,CAP_BASE[c]+rt,j,value,if import {cap_import}else{cap_self});}
            });
        }out
    }
    #[test]
    fn c164_eligible_off_cube_analytic_matches_independent_literal_calendar() {
        let p=Plan::eligible08();
        let r:Vec<_>=(0..40).map(|b|Fr::from(3+37*b)).collect();
        let u:Vec<_>=(0..41).map(|b|Fr::from(104+37*b)).collect();
        let v:Vec<_>=(0..41).map(|b|Fr::from(254+37*b)).collect();
        let expected=independent_coefficients(&r,&u,&v);
        assert_eq!(p.coefficients(&r,&u,&v).unwrap(),expected);
        let mut missing=Plan::eligible08();missing.epochs[1].pop();
        let mut emitted=Fr::zero();missing.visit_owner(1810840,|_,t| {if t.row==row(1810840,MAX_ROW[1]+7){emitted+=t.gate.c1;}Ok(())}).unwrap();
        assert_eq!(emitted,Fr::zero());
        assert_eq!(tuple(&p,1810840,MAX_ROW[1]+7,x(1810840,MAX_BASE[1]+7),x(1810840,MAX_BASE[1]+7))[1],-Fr::one());
    }

    #[test]
    fn c164_eligible_varied_d_tail_cut_oracle_and_post_f_mutant() {
        fn difficulty(height:usize,late_peak:u64)->u64 {
            match height {
                1810561..=1810688=>19,
                1810689..=1810816=>3,
                1810817..=1810944=>7,
                1810945..=1811072=>late_peak,
                _=>5,
            }
        }
        fn scalar(value:u64)->BigUint {
            let target=3*value/2;let mut rounded=1u64;
            while rounded<target {rounded*=2;}BigUint::from(rounded)
        }
        let prepare=|peak|Prepared::from_d_iter_eligible08((844672..=1827840)
            .map(|h|(h,BigUint::from(difficulty(h,peak))))).unwrap();
        let p=prepare(31);
        // Per-height integer suffixes, without the production epoch fold.
        for (c,terminal) in [(0,1827840),(1,1810842)] {
            let mut suffix=vec![0u64;terminal-844672+2];
            for height in (844672..=terminal).rev() {
                suffix[height-844672]=difficulty(height,31).max(suffix[height-844672+1]);
            }
            for ((start,end),witness) in oracle_epochs(terminal).into_iter().zip(&p.max[c]) {
                let d=BigUint::from(difficulty(end,31));
                let next=BigUint::from(suffix[end-844672+1]);
                assert_eq!(witness.d,d);assert_eq!(witness.r,BigUint::from(suffix[start-844672]));
                assert_eq!(witness.t,next);assert_eq!(witness.less,d<next);
                let delta=if d<next {(BigUint::from(1u8)<<224usize)+&d-&next}else{&d-&next};
                assert_eq!(witness.delta,delta);
            }
            for span in p.score_spans(c).unwrap() {
                assert_eq!(span.value,scalar(suffix[span.first-1088-844672]));
            }
        }
        let at=|owner|&p.max[1][p.plan.max_index(1,owner).unwrap()];
        assert_eq!((&at(1810686).d,&at(1810686).t,at(1810686).less),(&BigUint::from(19u8),&BigUint::from(7u8),false));
        assert_eq!((&at(1810814).d,&at(1810814).t,at(1810814).less),(&BigUint::from(3u8),&BigUint::from(7u8),true));
        assert_eq!((&at(1810840).d,&at(1810840).t,at(1810840).less),(&BigUint::from(7u8),&BigUint::zero(),false));
        // Exercise physical MAX arithmetic for both signed branches and terminal.
        for owner in [1810686,1810814,1810840] {
            let mut terms=Vec::new();p.plan.visit_owner(owner,|_,t|{terms.push(t);Ok(())}).unwrap();
            let mut needed=std::collections::BTreeSet::from([owner]);
            for t in &terms {needed.insert(t.gate.left>>20);needed.insert(t.gate.right>>20);}
            let mut values=BTreeMap::new();
            for o in needed {
                values.insert(x(o,0),Fr::zero());
                for s in p.owner_patch(o).unwrap().spans {
                    for (k,v) in s.values.into_iter().enumerate() {values.insert(x(o,s.start+k),v);}
                }
                let d=difficulty(o+2,31);
                for bit in 0..224 {values.insert(x(o,987674+bit),Fr::from(if bit<64 {(d>>bit)&1}else{0}));}
            }
            let mut residuals=BTreeMap::new();
            for t in terms {
                let g=t.gate;let l=values[&g.left];let r=values[&g.right];
                *residuals.entry(t.row).or_insert(Fr::zero())+=g.c0+g.c1*l+g.c2*r+g.c3*l*r;
            }
            assert!(residuals.values().all(Zero::is_zero),"MAX residual owner {owner}");
        }
        assert_eq!(p.owner_patch(1810904).unwrap().cap_value_65(0).unwrap(),BigUint::from(64u8));
        assert_eq!(p.owner_patch(1810841).unwrap().cap_value_65(1).unwrap(),BigUint::from(32u8));
        let changed=prepare(47);
        assert!(1810945>1810905 && 1810905>1810842);
        assert_eq!(p.max[1],changed.max[1],"D after f cannot enter cut h");
        assert_ne!(p.max[0],changed.max[0],"c0 MAX must include post-f D");
        assert!(!p.source_replay_matches(&changed));
        assert_eq!(changed.owner_patch(1810904).unwrap().cap_value_65(0).unwrap(),BigUint::from(128u8));
        assert_eq!(changed.owner_patch(1810841).unwrap().cap_value_65(1).unwrap(),BigUint::from(32u8));
    }
}

#[cfg(test)]
mod c172b1_snapshot_tests {
    use super::*;

    #[test]
    fn production_cap_literal_is_exact_old_template_at_first_modern_owner() {
        let plan=Plan::eligible08();
        let mut emitted=Vec::new();
        plan.visit_owner(845_759,|writer,term| {emitted.push((writer,term));Ok(())}).unwrap();
        for context in 0..2 {
            let writer=Writer::Cap {context,origin:845_760};
            let actual=emitted.iter().filter(|(w,_)|*w==writer)
                .map(|(_,term)|term.clone()).collect::<Vec<_>>();
            let mut reference=Vec::new();
            source::emit_cap(source::I0,|t| {
                assert_eq!((t.row.family,t.row.owner),(2,source::I0));
                let translate=|wire| match wire {
                    source::Wire::Cap {origin,local} if origin==source::I0 && local<2048 =>
                        x(845_759,CAP_BASE[context]+local as usize),
                    source::Wire::Native {owner,local} if owner==source::I0-1090
                        && (999424..999648).contains(&local) =>
                        x(FIRST-2,MAX_BASE[context]+local as usize-999424),
                    _=>panic!("old Cap template wire changed"),
                };
                reference.push(Term {row:row(845_759,cap_row(plan.rows,context,t.row.local as usize)),
                    gate:Gate {left:translate(t.left),right:translate(t.right),
                        c0:t.c[0],c1:t.c[1],c2:t.c[2],c3:t.c[3]}});
            });
            assert_eq!(actual.len(),6419);
            assert_eq!(actual.len(),reference.len());
            for (index,(got,want)) in actual.iter().zip(&reference).enumerate() {
                assert_eq!(got,want,"exact Cap tuple context {context} index {index}");
            }
        }
    }

    fn synthetic_snapshot()->Eligible08NativeSnapshot {
        // A bounded no-frame D stream tests the patch/lease join, not native
        // H21 custody or the runtime constructor.
        let prepared=Prepared::from_d_iter_eligible08(
            (FIRST..=LAST).map(|height|(height,BigUint::from(16u8)))).unwrap();
        Eligible08NativeSnapshot {parent:NativeParent {
            root:[0x81;32],total:[0x82;28],profile:[0x83;32],
            cut:CutDescriptor::eligible08()},prepared}
    }

    #[test]
    fn first_cap_lease_is_parent_cut_import_and_writer_bound() {
        let snapshot=synthetic_snapshot();
        let lease=snapshot.first_modern_from_snapshot().unwrap();
        for context in 0..2 {
            let (x_addr,bit)=lease.cap_cell(context,5).unwrap();
            assert_eq!(x_addr,x(845_759,CAP_BASE[context]+745));
            assert!(bit,"D16 has p24 and q32");
            assert!(!lease.cap_cell(context,4).unwrap().1);
        }
        assert!(lease.cap_cell(2,0).is_err());
        assert!(lease.cap_cell(0,65).is_err());
        let mut cells=OwnerCells::new(845_759).unwrap();
        lease.destination.apply(&mut cells).unwrap();
        assert_eq!(lease.destination.apply(&mut cells).unwrap_err(),
            "scheduled duplicate semantic writer");

        let mut bad=FirstModernCapLease {source:lease.source.clone(),
            destination:lease.destination.clone()};
        bad.source.parent.root[0]^=1;
        assert!(bad.check_exact(&snapshot).unwrap_err().contains("parent/source"));
        let mut bad=FirstModernCapLease {source:lease.source.clone(),
            destination:lease.destination.clone()};
        bad.destination.parent.cut=CutDescriptor::diagnostic08();
        assert!(bad.check_exact(&snapshot).unwrap_err().contains("parent/source"));
        let mut bad=FirstModernCapLease {source:lease.source.clone(),
            destination:lease.destination.clone()};
        let import=x(FIRST-2,MAX_BASE[0]);
        let term=bad.destination.rows.iter_mut().find(|(writer,term)|
            *writer==Writer::Cap {context:0,origin:845_760} && term.gate.left==import)
            .unwrap();
        term.1.gate.left^=1;
        assert_eq!(bad.check_imports().unwrap_err(),
            "Eligible08 first Cap physical MAX import");
        let mut bad=FirstModernCapLease {source:lease.source.clone(),
            destination:lease.destination.clone()};
        bad.source.patch.spans.iter_mut().find(|span|
            span.writer==Writer::Max {context:0,end:FIRST}).unwrap().values[6]=Fr::one();
        assert_eq!(bad.check_imports().unwrap_err(),"Eligible08 first Cap q/MAX source");
        let mut bad=FirstModernCapLease {source:lease.source.clone(),
            destination:lease.destination.clone()};
        bad.destination.patch.spans.iter_mut().find(|span|
            span.writer==Writer::Cap {context:0,origin:845_760}).unwrap().values[745]=Fr::zero();
        assert_eq!(bad.check_imports().unwrap_err(),"Eligible08 first Cap q/MAX source");
    }

    #[test]
    fn score_source_rejects_unclosed_max_before_any_endpoint_lease() {
        let snapshot=synthetic_snapshot();
        let stream=MaxStream::from_snapshot(&snapshot).unwrap();
        assert_eq!(stream.closed_score_endpoint_leases(0).unwrap_err(),
            "Score endpoint source requires closed MAX");
        assert_eq!(stream.closed_score_endpoint_leases(1).unwrap_err(),
            "Score endpoint source requires closed MAX");
        assert_eq!(stream.closed_score_endpoint_leases(2).unwrap_err(),
            "Score endpoint source requires closed MAX");
    }
}

//! Structural, conditional ROW relocation diagnostic only. No final merger,
//! witness/proof admission, analytic-kernel relocation or modern Score admission.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use num_bigint::BigUint;
use std::{collections::BTreeMap,ops::Range};
use crate::{bank53_map,bank53_map_score,legacy_envelope_map::{Map,LowerSelector,LowerSource,LowerBranch},
    origin_score_map::{Plan as ScorePlan,Profile,Mode,GuardPolicy},
    h21_scheduled_max_cap::{CutDescriptor,Plan as ScheduledPlan,Writer as ScheduledWriter},
    sparse::Term,gkr::Gate};

const WIDTH:usize=1<<20;
const ROWS:usize=1<<19;
const SLOTS:usize=1<<21;
const COUNT:[usize;2]=[1827838,1827775];
const SCORE_X:[usize;2]=[677501,685693];
const CAP_X:[usize;2]=[1000770,1002818];

#[derive(Clone,Copy,Debug,PartialEq,Eq,PartialOrd,Ord)]
pub(super) enum Family {Map(usize),Score(usize),V(usize),W(usize),Slack(usize)}
#[derive(Clone,Copy,Debug,PartialEq,Eq,PartialOrd,Ord)]
pub(super) enum Writer {Relocated(Family),Scheduled(ScheduledWriter),Daa}
#[derive(Clone,Debug)]
pub(super) struct Tagged {pub writer:Writer,pub term:Term}
#[derive(Clone,Debug)]
struct Reservation {writer:Writer,wires:Range<usize>}
#[derive(Clone,Debug)]
pub(super) struct Batch {owner:usize,terms:Vec<Tagged>,writes:Vec<Reservation>}
impl Batch {
    pub(super) fn owner(&self)->usize{self.owner}
    pub(super) fn terms(&self)->&[Tagged]{&self.terms}
    pub(super) fn reservations(&self)->impl Iterator<Item=(Writer,Range<usize>)>+'_ {
        self.writes.iter().map(|reservation|(reservation.writer,reservation.wires.clone()))
    }
}

// Preserve source spans and their holes; do not translate reserved 8192-row
// Score lanes as if all of them were emitted. This is one candidate layout.
fn placement(f:Family)->Result<(usize,usize,usize),String> {
    let (c,old,new,len)=match f {
        Family::Map(c)=>(c,409600,[477074,492305],10347),
        Family::Score(c)=>(c,425984,[487421,502652],4208),
        Family::V(c)=>(c,430192,[491629,506860],65),
        Family::W(c)=>(c,438272,[491694,506925],224),
        Family::Slack(c)=>(c,438496,[491918,507149],387),
    };
    if c>=2 {return Err("relocation context".into());}
    Ok((old+c*32768,new[c],len))
}
pub(super) fn relocate(f:Family,owner:usize,t:&Term)->Result<Term,String> {
    if owner>=SLOTS || t.gate.left>=WIDTH*SLOTS || t.gate.right>=WIDTH*SLOTS {
        return Err("relocation owner or X extent".into());
    }
    let (old,new,len)=placement(f)?;
    let local=t.row.checked_sub(owner*ROWS+old).filter(|q|*q<len)
        .ok_or("term is not an actually emitted source-family span")?;
    let mut out=t.clone();out.row=owner*ROWS+new+local;Ok(out)
}
fn check_relocation(f:Family,o:usize,before:&Term,after:&Term)->Result<(),String> {
    let expected=relocate(f,o,before)?;
    if expected!=*after {return Err("relocation changed X/gate fields or ROW address".into());}
    Ok(())
}

/// The exact e55/pivot54/source-height structural signature used by the H21
/// native Map experiment, without claiming its parent_root or native values.
pub(super) struct Sources {maps:[Map;2],score:[ScorePlan;2],scheduled:ScheduledPlan}
impl Sources {
    pub(super) fn new()->Result<Self,String> {
        let map=|n|Map::new_modern_global_u_selected_lower(n,21,55,LowerSelector {
            source:LowerSource::HeaderDifficulty {height:841729},branch:LowerBranch::Pivot(54)});
        Self::with_maps([map(1827840)?,map(1827775)?])
    }
    fn with_maps(maps:[Map;2])->Result<Self,String> {
        let score=|c|ScorePlan::new(1,COUNT[c],vec![Profile {mode:if c==0 {Mode::Sampled}else{Mode::Exact},
            prefix:COUNT[c],expected:BigUint::from(0u8),guard:GuardPolicy::Disabled}]);
        Ok(Self {maps,score:[score(0)?,score(1)?],scheduled:ScheduledPlan::new()})
    }
    fn score_terms(&self,c:usize,o:usize)->Result<Vec<Term>,String> {
        // This adapter is explicitly diagnostic. The existing production-facing
        // bank53 adapter still rejects active modern Score owners.
        let n=self.score[c].emit_owner(0,o,|_|{})?;
        if n>10000 {return Err("conditional Score owner cap".into());}
        let mut out=Vec::with_capacity(n);
        self.score[c].emit_owner(0,o,|mut t| {
            let local=t.row-o*8192;t.row=o*ROWS+425984+c*32768+local;
            let physical=|i:usize|(i/2048)*WIDTH+SCORE_X[c]+i%2048;
            t.gate.left=physical(t.gate.left);t.gate.right=physical(t.gate.right);out.push(t);
        })?;Ok(out)
    }
    fn w_terms(&self,c:usize,o:usize)->Result<Vec<Term>,String> {
        if !self.score[c].spec(0,o)?.active {return Ok(Vec::new());}
        let mut out=Vec::with_capacity(448);let z=Fr::zero();let one=Fr::one();
        for k in 0..224 {
            let row=o*ROWS+438272+c*32768+k;
            out.push(Term {row,gate:Gate {left:o*WIDTH+SCORE_X[c]+k,right:0,c0:z,c1:one,c2:z,c3:z}});
            if o>0 {out.push(Term {row,gate:Gate {left:(o-1)*WIDTH+987450+k,right:0,c0:z,c1:-one,c2:z,c3:z}});}
        }Ok(out)
    }
    fn v_terms(&self,c:usize,o:usize)->Vec<Term> {
        if !(845759..COUNT[c]).contains(&o) {return Vec::new();}
        let tail=if c==0 {1827776}else{1827648};
        let dest=if o==845759 {o}else if o>=tail {COUNT[c]-1}else{((o+64)/128)*128+63};
        (0..65).map(|k|Term {row:o*ROWS+430192+c*32768+k,gate:Gate {
            left:o*WIDTH+SCORE_X[c]+224+k,right:dest*WIDTH+CAP_X[c]+740+k,
            c0:Fr::zero(),c1:Fr::one(),c2:-Fr::one(),c3:Fr::zero()}}).collect()
    }
    fn source_owner(&self,o:usize)->Result<Batch,String> {self.source_owner_mode(o,false)}
    fn source_owner_mode(&self,o:usize,sparse_score:bool)->Result<Batch,String> {
        if o>=SLOTS {return Err("diagnostic owner outside H21".into());}
        let mut terms=Vec::new();let mut writes=Vec::new();
        for c in 0..2 {
            let emit_score=!sparse_score||is_sparse_score_endpoint(c,o);
            let score=if emit_score {self.score_terms(c,o)?}else{Vec::new()};
            let v=if emit_score {self.v_terms(c,o)}else{Vec::new()};
            let w=if emit_score {self.w_terms(c,o)?}else{Vec::new()};
            let families=[(Family::Map(c),bank53_map::map_owner_terms(&self.maps[c],o as u64,c)?),
                (Family::Score(c),score),(Family::V(c),v),(Family::W(c),w),
                (Family::Slack(c),bank53_map_score::slack_zero_terms(o,c)?)];
            for (f,ts) in families {for term in ts {terms.push(Tagged {writer:Writer::Relocated(f),term});}}
            // W/V are aliases and read existing cells, not additional X writers.
            for (f,wires) in [(Family::Map(c),671744+c*8192..677501+c*8192),
                (Family::Score(c),677501+c*8192..679549+c*8192),
                (Family::Slack(c),679549+c*8192..679936+c*8192)] {
                if sparse_score&&f==Family::Score(c)&&!emit_score {continue;}
                writes.push(Reservation {writer:Writer::Relocated(f),wires});
            }
        }
        let mut scheduled_writers=BTreeMap::new();
        self.scheduled.visit_owner(o,|writer,term| {
            scheduled_writers.insert(writer,());terms.push(Tagged {writer:Writer::Scheduled(writer),term});Ok(())
        })?;
        for (w,_) in scheduled_writers {
            let wires=match w {ScheduledWriter::Max {context,..}=>[999424,1000097][context]..[1000097,1000770][context],
                ScheduledWriter::Cap {context,..}=>[1000770,1002818][context]..[1002818,1004866][context]};
            writes.push(Reservation {writer:Writer::Scheduled(w),wires});
        }
        if terms.len()>500000 {return Err("diagnostic per-owner term cap".into());}
        Ok(Batch {owner:o,terms,writes})
    }
    pub(super) fn stage_owner(&self,o:usize)->Result<Batch,String> {
        let mut b=self.source_owner(o)?;
        for t in &mut b.terms {if let Writer::Relocated(f)=t.writer {
            let moved=relocate(f,o,&t.term)?;check_relocation(f,o,&t.term,&moved)?;t.term=moved;
        }}
        Ok(b)
    }

    /// Test-only sparse Score view. Map, Slack and scheduled MAX/Cap ownership
    /// keep their existing source roster; Score/W/V rows and Score X writes
    /// survive only at cap-cell endpoints. This does not change the legacy
    /// source_owner API or the production Score refusal.
    pub(super) fn sparse_score_owner(&self,o:usize)->Result<Batch,String> {
        let mut b=self.source_owner_mode(o,true)?;
        // The ordinary Score emitter uses owner-1 for every predecessor R.
        // Sparse rows must instead read the previous retained endpoint.
        for t in &mut b.terms {if let Writer::Relocated(Family::Score(c))=t.writer {
            if let Some(previous)=sparse_previous_endpoint(c,o) {
                let local=t.term.gate.left%WIDTH;
                if t.term.gate.left/WIDTH==o.saturating_sub(1)
                    && (SCORE_X[c]+1318..SCORE_X[c]+1543).contains(&local) {
                    t.term.gate.left=previous*WIDTH+local;
                }
            }
        }}
        Ok(b)
    }
    pub(super) fn stage_sparse_score_owner(&self,o:usize)->Result<Batch,String> {
        let mut b=self.sparse_score_owner(o)?;
        for t in &mut b.terms {if let Writer::Relocated(f)=t.writer {
            let moved=relocate(f,o,&t.term)?;check_relocation(f,o,&t.term,&moved)?;t.term=moved;
        }}
        Ok(b)
    }
}

/// Source/cut binding for this structural diagnostic. In particular, the cut
/// Map is not assigned a fabricated cut-tree root: both Maps remain symbolic,
/// while this wrapper records their full source parent's root and total.
#[derive(Clone,Debug,PartialEq,Eq)]
pub(super) struct ParentMapBinding {
    pub headers:u64,pub slot_log:usize,pub root:[u8;32],pub total:[u8;28],
    pub cut_identity:Vec<u8>,
    pub maps:[crate::legacy_envelope_map::Binding;2],
}
#[derive(Clone,Copy,Debug)]
pub(super) struct MapParameters {pub cut:u64,pub exponent:usize,pub lower:LowerSelector}

fn bound_maps(parent:&crate::work_tree_history_plan::WorkTreeHistoryPlan,
    descriptor:CutDescriptor,parameters:[MapParameters;2])
    ->Result<([Map;2],ParentMapBinding),String> {
    if parent.headers()!=bank53_map::BANK53_N||parent.slot_log()!=21||parent.slots()!=SLOTS
        ||parent.headers()!=descriptor.terminals()[0] as u64 {
        return Err("c168 source parent H21 geometry".into());
    }
    if parameters.iter().enumerate().any(|(c,p)|p.cut!=descriptor.terminals()[c] as u64) {
        return Err("c168 exact descriptor context cut".into());
    }
    parent.descriptor().validate()?;
    let map=|p:MapParameters|Map::new_modern_global_u_selected_lower(
        p.cut,parent.slot_log(),p.exponent,p.lower);
    let maps=[map(parameters[0])?,map(parameters[1])?];
    let binding=ParentMapBinding {headers:parent.headers(),slot_log:parent.slot_log(),
        root:parent.descriptor().root,total:parent.work_profile().total_be28,
        cut_identity:descriptor.canonical_identity(),maps:[maps[0].binding(),maps[1].binding()]};
    Ok((maps,binding))
}

pub(super) struct ParentMapSources {sources:Sources,binding:ParentMapBinding}
impl ParentMapSources {
    pub(super) fn new(parent:&crate::work_tree_history_plan::WorkTreeHistoryPlan,
        parameters:[MapParameters;2])->Result<Self,String> {
        if parent.headers()!=bank53_map::BANK53_N||parent.slot_log()!=21||parent.slots()!=SLOTS {
            return Err("c141 source parent H21 geometry".into());
        }
        let cuts=[bank53_map::BANK53_N,bank53_map::BANK53_H];
        if parameters.iter().enumerate().any(|(c,p)|p.cut!=cuts[c]) {
            return Err("c141 exact context cut".into());
        }
        let (maps,binding)=bound_maps(parent,CutDescriptor::diagnostic08(),parameters)?;
        Ok(Self {sources:Sources::with_maps(maps)?,binding})
    }
    pub(super) fn binding(&self)->&ParentMapBinding {&self.binding}
    pub(super) fn sources(&self)->&Sources {&self.sources}
    pub(super) fn validate(&self,parent:&crate::work_tree_history_plan::WorkTreeHistoryPlan,
        claimed:&ParentMapBinding)->Result<(),String> {
        if parent.headers()!=self.binding.headers||parent.slot_log()!=self.binding.slot_log
            ||parent.slots()!=SLOTS||parent.descriptor().root!=self.binding.root
            ||parent.work_profile().total_be28!=self.binding.total||claimed!=&self.binding
            ||self.binding.cut_identity!=CutDescriptor::diagnostic08().canonical_identity()
            ||self.sources.maps[0].binding()!=self.binding.maps[0]
            ||self.sources.maps[1].binding()!=self.binding.maps[1] {
            return Err("c141 complete parent/Map source binding".into());
        }
        Ok(())
    }
}

/// A Map-only source pair for the eligible draft-0.8 cut. The Diagnostic08
/// ledger is deliberately not reachable through this type.
pub(super) struct EligibleParentMapSources {
    descriptor:CutDescriptor,maps:[Map;2],binding:ParentMapBinding,
}
impl EligibleParentMapSources {
    pub(super) fn new(parent:&crate::work_tree_history_plan::WorkTreeHistoryPlan,
        parameters:[MapParameters;2])->Result<Self,String> {
        let descriptor=CutDescriptor::eligible08();
        let (maps,binding)=bound_maps(parent,descriptor,parameters)?;
        Ok(Self {descriptor,maps,binding})
    }
    pub(super) fn binding(&self)->&ParentMapBinding {&self.binding}
    fn validate(&self,parent:&crate::work_tree_history_plan::WorkTreeHistoryPlan,
        claimed:&ParentMapBinding)->Result<(),String> {
        if parent.headers()!=self.binding.headers||parent.slot_log()!=self.binding.slot_log
            ||parent.slots()!=SLOTS||parent.descriptor().root!=self.binding.root
            ||parent.work_profile().total_be28!=self.binding.total||claimed!=&self.binding
            ||self.binding.cut_identity!=self.descriptor.canonical_identity()
            ||self.maps[0].binding()!=self.binding.maps[0]
            ||self.maps[1].binding()!=self.binding.maps[1] {
            return Err("c168 eligible parent/Map/cut source binding".into());
        }
        Ok(())
    }
    pub(super) fn source_owner_terms(&self,owner:usize,context:usize)->Result<Vec<Term>,String> {
        let map=self.maps.get(context).ok_or("c168 Map context")?;
        bank53_map::map_owner_terms_for_descriptor(map,owner as u64,context,self.descriptor)
    }
    /// Re-emit the selected physical Map relation before accepting an owner
    /// claim. This does not publish or authenticate X, Score, MAX or ROW.
    pub(super) fn preflight_owner(&self,parent:&crate::work_tree_history_plan::WorkTreeHistoryPlan,
        claimed:&ParentMapBinding,owner:usize,context:usize,
        terms:&[Term],x:Range<usize>)->Result<(),String> {
        self.validate(parent,claimed)?;
        if context>=2 {return Err("c168 Map context".into());}
        let expected_x=(671744+context*8192)..(677501+context*8192);
        if x!=expected_x {return Err("c168 Map X source domain".into());}
        if terms!=self.source_owner_terms(owner,context)? {
            return Err("c168 emitted Map source tuples".into());
        }
        Ok(())
    }
}

/// Sparse modern Score owners, derived from the pinned cap schedule constants:
/// first singleton, each regular 128-height cell end, and the clipped guard.
/// Values are score-owner indices (logical origin minus one).
pub(super) fn sparse_score_endpoints(c:usize)->Result<Vec<usize>,String> {
    if c>=2{return Err("sparse Score context".into());}
    let (last_regular,guard,count)=match c {
        0=>(1_827_776,1_827_838,7_674),
        1=>(1_827_648,1_827_775,7_673),
        _=>unreachable!(),
    };
    let mut out=Vec::with_capacity(count);
    let mut origin=845_760usize;
    while origin<=last_regular {out.push(origin-1);origin+=128;}
    out.push(guard-1);
    if out.len()!=count || out.first()!=Some(&845_759) || out.last()!=Some(&(guard-1))
        || out.windows(2).any(|w|w[0]>=w[1]) {
        return Err("sparse Score endpoint census".into());
    }
    Ok(out)
}
fn is_sparse_score_endpoint(c:usize,o:usize)->bool {
    if c>=2{return false;}
    let (last_regular,guard)=if c==0 {(1_827_775usize,1_827_837usize)}else{(1_827_647,1_827_774)};
    o==845_759 || o==guard || (845_887..=last_regular).contains(&o) && (o-845_887)%128==0
}
pub(super) fn sparse_previous_endpoint(c:usize,o:usize)->Option<usize>{
    if !is_sparse_score_endpoint(c,o){return None;}
    let (guard,last_regular)=if c==0 {(1_827_837usize,1_827_775usize)}else{(1_827_774,1_827_647)};
    if o==845_759 {Some(845_758)}
    else if o==guard {Some(last_regular)}
    else {Some(o-128)}
}

/// ROW ownership and X write reservations are separate. This registry does not
/// authenticate source tuple multiplicity, assignments, or a final proof.
#[derive(Clone,Debug,PartialEq,Eq)]
pub(super) struct Registry {owner:usize,rows:BTreeMap<usize,Writer>,x:BTreeMap<usize,Writer>}
impl Registry {
    pub(super) fn new(owner:usize)->Result<Self,String> {
        if owner>=SLOTS {return Err("registry owner outside H21".into());}
        Ok(Self {owner,rows:BTreeMap::new(),x:BTreeMap::new()})
    }
    pub(super) fn commit(&mut self,b:&Batch)->Result<(),String> {
        if self.owner!=b.owner {return Err("batch/registry owner mismatch".into());}
        let mut rows=BTreeMap::new();let mut x=BTreeMap::new();
        for t in &b.terms {
            if t.term.row/ROWS!=self.owner || t.term.gate.left>=WIDTH*SLOTS || t.term.gate.right>=WIDTH*SLOTS {
                return Err("batch ROW or X extent".into());
            }
            if let Writer::Relocated(f)=t.writer {
                let (_,start,len)=placement(f)?;let q=t.term.row-self.owner*ROWS;
                if !(start..start+len).contains(&q) {return Err("relocated family ROW extent".into());}
            }
            for previous in [self.rows.get(&t.term.row),rows.get(&t.term.row)].into_iter().flatten() {
                if *previous!=t.writer {return Err("cross-writer ROW collision".into());}
            }rows.insert(t.term.row,t.writer);
        }
        for write in &b.writes {
            if write.wires.start>=write.wires.end || write.wires.end>WIDTH {return Err("X reservation extent".into());}
            for cell in write.wires.clone() {
                if self.x.contains_key(&cell) || x.insert(cell,write.writer).is_some() {
                    return Err("duplicate X write reservation".into());
                }
            }
        }
        self.rows.extend(rows);self.x.extend(x);Ok(())
    }
}

#[cfg(test)]
#[path="h21_row_support_tests.rs"]
mod tests;

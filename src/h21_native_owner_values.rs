//! Complete native owner values for the fixed Eligible08 history. This is a
//! witness candidate, not a checked ROW slice or a commitment admission.
use super::*;
use crate::{bank53_required_writer::{required_bank53_writer,RequiredWriter},
    h21_scheduled_family_ledger::scored_owner_cap_publication_from_native_roster,
    h21_scheduled_max_cap::MaxReplayAuthor};

const N:usize=1_827_840;
const SLOTS:usize=1<<21;
const WIDTH:usize=1<<20;
const BYTES:usize=WIDTH/8;
const MAP_BASE:[usize;2]=[671_744,679_936];
const MAX_BASE:[usize;2]=[999_424,1_000_097];
const CAP_BASE:[usize;2]=[1_000_770,1_002_818];

impl<'src> H21EligibleContext<'src> {
    #[cfg(test)]
    pub(crate) fn native_owner_values_producer(&self)->&NativeOwnerProducer<'src> {&self.producer}
}

#[derive(Clone,Debug,Default,PartialEq,Eq)]
pub(crate) struct H21ValueCensus {
    pub(crate) map:[usize;2],pub(crate) score:[usize;2],
    pub(crate) slack:[usize;2],pub(crate) max:[usize;2],pub(crate) cap:[usize;2],
}

/// Only the closed stream's constructor below can issue this immutable row.
/// It cannot be converted into any older custody or verifier-success token.
pub(crate) struct NativeH21OwnerValues<'context,'source> {
    context:&'context H21EligibleContext<'source>,
    binding:HeaderSourceBinding,
    class:crate::daa_history_roster::OwnerClass,
    bytes:Vec<u8>,
    census:H21ValueCensus,
}
impl NativeH21OwnerValues<'_,'_> {
    pub(crate) fn owner(&self)->usize {self.binding.owner()}
    pub(crate) fn binding(&self)->&HeaderSourceBinding {&self.binding}
    pub(crate) fn packed_bytes(&self)->&[u8] {&self.bytes}
    pub(crate) fn census(&self)->&H21ValueCensus {&self.census}
    pub(crate) fn require_context(&self,context:&H21EligibleContext<'_>)->Result<(),String> {
        if !std::ptr::eq(self.context,context) {return Err("C587 different native source context".into());}
        let expected=HeaderSourceBinding::for_plan(context.producer.plan,self.owner())?;
        if self.binding!=expected || self.class!=context.producer.roster.owner_class(self.owner()as u64)?
            || self.bytes.len()!=BYTES {return Err("C587 native owner identity/extent".into());}
        Ok(())
    }
}

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
enum Component {Map(usize),Score(usize),Slack(usize),Max(usize),Cap(usize)}

struct Overlay {
    owner:usize,base:Vec<u8>,bytes:Vec<u8>,written:Vec<u8>,
    tree_daa:Vec<bool>,score:[bool;2],max:[bool;2],cap:[bool;2],census:H21ValueCensus,
}

// Cache original source tuples, not derived bits. Each immutable source bank
// is loaded once per owner during one equation diagnostic. Score and MAX have
// separate typed banks even when their owner numbers coincide.
struct ForeignOwnerCells<A> {
    owners:std::collections::BTreeMap<usize,Vec<(usize,A,Fr)>>,
}
impl<A:Copy> ForeignOwnerCells<A> {
    fn new()->Self {Self {owners:std::collections::BTreeMap::new()}}
    fn cell(&mut self,owner:usize,wire:usize,
        load:impl FnOnce(usize)->Result<Vec<(usize,A,Fr)>,String>)
        ->Result<Option<(A,Fr)>,String> {
        if let std::collections::btree_map::Entry::Vacant(entry)=self.owners.entry(owner) {
            entry.insert(load(owner)?);
        }
        Ok(self.owners[&owner].iter().find(|(at,_,_)|*at==wire)
            .map(|(_,author,value)|(*author,*value)))
    }
}
struct ForeignValues {
    score:ForeignOwnerCells<ScoreReplayAuthor>,
    max:ForeignOwnerCells<MaxReplayAuthor>,
    exports:std::collections::BTreeMap<usize,Fr>,
}
impl ForeignValues {
    fn new()->Self {Self {score:ForeignOwnerCells::new(),max:ForeignOwnerCells::new(),
        exports:std::collections::BTreeMap::new()}}
}
fn boolean(value:Fr)->Result<bool,String> {
    if value==Fr::zero() {Ok(false)} else if value==Fr::one() {Ok(true)}
    else {Err("C587 non-Boolean original component Fr".into())}
}
fn bit(bytes:&[u8],local:usize)->bool {bytes[local/8]>>(local%8)&1!=0}
fn set(bytes:&mut[u8],local:usize,value:bool) {
    let mask=1u8<<(local%8);
    if value {bytes[local/8]|=mask;} else {bytes[local/8]&=!mask;}
}
fn score_activity(owner:usize)->Result<[bool;2],String> {
    let mut out=[false;2];
    for context in 0..2 {
        out[context]=match required_bank53_writer(owner,context,5_757)
            .map_err(|e|e.to_string())? {
            RequiredWriter::ScoreAnchor{context:c}|RequiredWriter::ScoreReplay{context:c,..} if c==context=>true,
            RequiredWriter::HeaderZero=>false,
            _=>return Err("C587 Score writer classification".into()),
        };
    }
    Ok(out)
}
impl Overlay {
    fn new(owner:usize,base:Vec<u8>,tree_daa:Vec<bool>,score:[bool;2],max:[bool;2],cap:[bool;2])
        ->Result<Self,String> {
        if owner>=SLOTS || base.len()!=BYTES || tree_daa.len()!=WIDTH {
            return Err("C587 base owner/extent".into());
        }
        Ok(Self {owner,bytes:base.clone(),base,written:vec![0;BYTES],tree_daa,score,max,cap,
            census:H21ValueCensus::default()})
    }
    fn claim(&mut self,component:Component,wire:usize,value:Fr)->Result<(),String> {
        // Check the ORIGINAL field value before conversion or any bit write.
        let value=boolean(value)?;
        let local=wire.checked_sub(self.owner.checked_mul(WIDTH).ok_or("C587 owner product")?)
            .filter(|local|*local<WIDTH).ok_or("C587 component outside owner")?;
        let (context,start,width,active)=match component {
            Component::Map(c) if c<2=>(c,MAP_BASE[c],5_757,true),
            Component::Score(c) if c<2=>(c,SCORE_X[c],2_048,self.score[c]),
            Component::Slack(c) if c<2=>(c,MAP_BASE[c]+7_805,387,true),
            Component::Max(c) if c<2=>(c,MAX_BASE[c],673,self.max[c]),
            Component::Cap(c) if c<2=>(c,CAP_BASE[c],2_048,self.cap[c]),
            _=>return Err("C587 component context".into()),
        };
        if !active || !(start..start+width).contains(&local) || self.tree_daa[local]
            || bit(&self.written,local) || bit(&self.base,local)
            || (matches!(component,Component::Slack(_)) && value)
            || (matches!(component,Component::Map(_))
                && self.owner>=crate::bank53_map::CutDescriptor::eligible08().terminals()[context]-1 && value) {
            return Err("C587 inactive/domain/conflict/base-zero replacement".into());
        }
        set(&mut self.written,local,true);set(&mut self.bytes,local,value);
        match component {
            Component::Map(_)=>self.census.map[context]+=1,
            Component::Score(_)=>self.census.score[context]+=1,
            Component::Slack(_)=>self.census.slack[context]+=1,
            Component::Max(_)=>self.census.max[context]+=1,
            Component::Cap(_)=>self.census.cap[context]+=1,
        }
        Ok(())
    }
    fn finish(self)->Result<(Vec<u8>,H21ValueCensus),String> {
        for c in 0..2 {
            if self.census.map[c]!=5_757 || self.census.slack[c]!=387
                || self.census.score[c]!=usize::from(self.score[c])*2_048
                || self.census.max[c]!=usize::from(self.max[c])*673
                || self.census.cap[c]!=usize::from(self.cap[c])*2_048 {
                return Err("C587 incomplete full-domain component census".into());
            }
            for (start,width,active) in [(SCORE_X[c],2_048,self.score[c]),
                (MAX_BASE[c],673,self.max[c]),(CAP_BASE[c],2_048,self.cap[c])] {
                if !active && (start..start+width).any(|local|bit(&self.bytes,local)) {
                    return Err("C587 nonzero inactive family".into());
                }
            }
        }
        // Every changed bit has one explicit replacement author. No source
        // component's default zero can erase another family's active cell.
        for local in 0..WIDTH {
            if !bit(&self.written,local) && bit(&self.bytes,local)!=bit(&self.base,local) {
                return Err("C587 changed value outside component union".into());
            }
        }
        Ok((self.bytes,self.census))
    }
}

impl<'ctx,'src,'max,'snapshot> H21ScoreEndpointStream<'ctx,'src,'max,'snapshot> {
    /// Build one complete X-owner candidate using this stream's OWN native
    /// context and MAX closure. Callers choose no masks, fields or components.
    pub(crate) fn native_owner_values(&self,owner:usize)->Result<NativeH21OwnerValues<'_,'src>,String> {
        self.terminal_r()?;
        let context=self.context;let producer=&context.producer;
        validate_native_plan_input(producer.plan,producer.input)?;
        if owner>=SLOTS || producer.plan.headers()!=N as u64 || producer.plan.slot_log()!=21
            || producer.plan.slots()!=SLOTS {return Err("C587 fixed native history domain".into());}
        let snapshot=self.closed_max.closed_native_snapshot(producer.plan,producer.input)?;
        let (max,cap)=snapshot.scheduled_plan().owner_activity(owner)?;
        let score=score_activity(owner)?;
        let binding=HeaderSourceBinding::for_plan(producer.plan,owner)?;
        let class=producer.roster.owner_class(owner as u64)?;
        // The unchanged native writer checks every original base Fr before
        // packing. It supplies HEADER, POINT, Tree and all DAA banks together.
        let base=producer.produce(owner)?;
        base.require_header_source_binding(&binding,owner,class)?;
        let tree_daa=producer.plan.physical_assignment_replacement_mask(owner as u64)?;
        let mut overlay=Overlay::new(owner,base.bytes,tree_daa,score,max,cap)?;
        let stage=context.stage_with_slack(owner)?;
        stage.map_stage.validate_identity_with_roster(producer.plan,producer.input.profile(),context.descriptor,&context.maps,&producer.roster)?;
        if stage.map_stage.owner!=owner || stage.map_stage.claims.len()!=2*5_757
            || stage.slack_cells().len()!=2*387 {
            return Err("C587 full Map/Slack native source census".into());
        }
        for (&local,&(author,value)) in &stage.map_stage.claims {
            let H21StageAuthor::Map(c)=author else {return Err("C587 non-Map source in Map stage".into());};
            overlay.claim(Component::Map(c),owner*WIDTH+local,Fr::from(value as u64))?;
        }
        for (&local,&(author,value)) in stage.slack_cells() {
            let H21StageAuthor::Slack(c)=author else {return Err("C587 non-Slack source".into());};
            overlay.claim(Component::Slack(c),owner*WIDTH+local,Fr::from(value as u64))?;
        }
        let relation=if ANCHOR_OWNERS.contains(&owner) {
            let source=if owner==ANCHOR_OWNERS[0] {&self.first_modern.anchors.first}
                else {&self.first_modern.anchors.second};
            source.validate_identity_with_roster(producer.plan,producer.input.profile(),context.descriptor,&context.maps,&producer.roster)?;
            if source.map_bindings!=stage.map_stage.map_bindings {return Err("C587 anchor Map binding".into());}
            for (&local,&(author,value)) in &source.claims {
                if let H21StageAuthor::ScoreAnchor(c)=author {
                    overlay.claim(Component::Score(c),owner*WIDTH+local,Fr::from(value as u64))?;
                }
            }
            None
        } else {
            let relation=self.closed_owner_relation_status(owner)?;
            if let Some(relation)=relation.as_ref() {
                relation.require_original_map_bindings([&stage.map_stage.map_bindings[0],&stage.map_stage.map_bindings[1]])?;
                if relation.authors().map(|author|author.is_some())!=score {
                    return Err("C587 Score source/calendar activity".into());
                }
                for &(wire,author,value) in relation.cells() {
                    overlay.claim(Component::Score(author.context),wire,value)?;
                }
            } else if score.contains(&true) {return Err("C587 missing active closed Score source".into());}
            relation
        };
        if cap.contains(&true) {
            let publication=scored_owner_cap_publication_from_native_roster(
                producer.plan,producer.input,snapshot,&producer.roster,owner)?;
            if publication.binding()!=&binding {return Err("C587 Cap parent binding".into());}
            let material=publication.checked_material()?;
            if material.active!=cap {return Err("C587 Cap source/calendar activity".into());}
            // All 2,048 helpers are installed, not only the 65 q aliases.
            for &(wire,c,value) in &material.cells {
                overlay.claim(Component::Cap(c),wire,Fr::from(value as u64))?;
            }
            let mut sources=std::collections::BTreeMap::new();
            for &(wire,writer,value) in &material.imports {
                let source_owner=wire/WIDTH;
                if !sources.contains_key(&source_owner) {
                    sources.insert(source_owner,self.closed_max.closed_owner_cells(source_owner)?);
                }
                let (_,author,original)=sources[&source_owner].iter().find(|(at,_,_)|*at==wire)
                    .ok_or("C587 Cap missing MAX import")?;
                if *author!=MaxReplayAuthor::Scheduled(writer) || boolean(*original)?!=value {
                    return Err("C587 Cap original MAX import mismatch".into());
                }
            }
            let relation=relation.as_ref().ok_or("C587 Cap without closed Score relation")?;
            for c in 0..2 {
                if material.q[c].len()!=usize::from(cap[c])*65 {return Err("C587 Cap q census".into());}
                for (k,&(_,value)) in material.q[c].iter().enumerate() {
                    if bit(&overlay.bytes,SCORE_X[c]+score::Layout::new().sv.start+k)!=value {
                        return Err("C587 complete Cap disagrees with Score q".into());
                    }
                }
            }
            if relation.authors().map(|author|author.is_some())!=cap {
                return Err("C587 Score/Cap active context mismatch".into());
            }
        }
        if max.contains(&true) {
            let cells=self.closed_max.closed_owner_cells(owner)?;
            if cells.len()!=224+673*max.iter().filter(|active|**active).count() {
                return Err("C587 full MAX source census".into());
            }
            let work=&crate::work_tree_layout::shared_baseline()?.endpoints.work;
            for (k,&(wire,author,value)) in cells[..224].iter().enumerate() {
                if wire!=owner*WIDTH+work[k] || author!=(MaxReplayAuthor::NativeWorkD{height:owner+2})
                    || boolean(value)?!=bit(&overlay.base,work[k]) {
                    return Err("C587 MAX original Work-D/base mismatch".into());
                }
            }
            for &(wire,author,value) in &cells[224..] {
                let MaxReplayAuthor::Scheduled(crate::h21_scheduled_max_cap::Writer::Max{context:c,end})=author
                    else {return Err("C587 non-MAX writer in MAX source".into());};
                if end!=owner+2 {return Err("C587 MAX source end".into());}
                overlay.claim(Component::Max(c),wire,value)?;
            }
        }
        let (bytes,census)=overlay.finish()?;
        let result=NativeH21OwnerValues {context,binding,class,bytes,census};
        result.require_context(context)?;Ok(result)
    }

    /// Bounded equation diagnostic for a produced owner. Foreign cells are
    /// independently recomputed from this same closed native source, not
    /// certified commitment openings. The later common-X proof remains due.
    pub(crate) fn check_native_role1_values(&self,row:&NativeH21OwnerValues<'_,'src>,
        roster:&structural_roster::H21StructuralRoster<'_>)->Result<(),String> {
        row.require_context(self.context)?;
        let owner=row.owner();let base=owner*WIDTH;
        let mut residuals=vec![Fr::zero();1<<19];
        let mut foreign=ForeignValues::new();
        let mut read=|wire|->Result<Fr,String> {
            if (base..base+WIDTH).contains(&wire) {return Ok(Fr::from(bit(row.packed_bytes(),wire-base)as u64));}
            self.native_foreign_value(wire,&mut foreign)
        };
        roster.visit_owner_terms(owner,|_,term| {
            let local=term.row.checked_sub(owner*(1<<19)).filter(|q|*q<1<<19)
                .ok_or("C587 literal ROW owner")?;
            let g=term.gate;
            let l=if !g.c1.is_zero()||!g.c3.is_zero() {read(g.left)?}else{Fr::zero()};
            let r=if !g.c2.is_zero()||!g.c3.is_zero() {read(g.right)?}else{Fr::zero()};
            residuals[local]+=g.c0+g.c1*l+g.c2*r+g.c3*l*r;Ok(())
        })?;
        if let Some(local)=residuals.iter().position(|value|!value.is_zero()) {
            return Err(format!("C587 native owner{owner} literal residual localROW{local}"));
        }
        Ok(())
    }

    fn native_foreign_value(&self,wire:usize,cache:&mut ForeignValues)->Result<Fr,String> {
        if wire>=SLOTS*WIDTH {return Err("C587 foreign coordinate outside X".into());}
        let owner=wire/WIDTH;let local=wire%WIDTH;
        for c in 0..2 {
            if (SCORE_X[c]..SCORE_X[c]+2_048).contains(&local) {
                if !score_activity(owner)?[c] {return Ok(Fr::zero());}
                if ANCHOR_OWNERS.contains(&owner) {
                    let source=if owner==ANCHOR_OWNERS[0] {&self.first_modern.anchors.first}
                        else {&self.first_modern.anchors.second};
                    let (author,value)=source.claims.get(&local).ok_or("C587 foreign anchor cell missing")?;
                    if *author!=H21StageAuthor::ScoreAnchor(c) {return Err("C587 foreign anchor author".into());}
                    return Ok(Fr::from(*value as u64));
                }
                let (author,value)=cache.score.cell(owner,wire,|owner|self.closed_owner_cells(owner))?
                    .ok_or("C587 foreign closed Score cell missing")?;
                if author.context!=c {return Err("C587 foreign Score context".into());}
                boolean(value)?;return Ok(value);
            }
            if (MAX_BASE[c]..MAX_BASE[c]+673).contains(&local) {
                let snapshot=self.closed_max.closed_native_snapshot(
                    self.context.producer.plan,self.context.producer.input)?;
                if !snapshot.scheduled_plan().owner_activity(owner)?.0[c] {return Ok(Fr::zero());}
                let (author,value)=cache.max.cell(owner,wire,|owner|self.closed_max.closed_owner_cells(owner))?
                    .ok_or("C587 foreign MAX cell missing")?;
                if author!=(MaxReplayAuthor::Scheduled(crate::h21_scheduled_max_cap::Writer::Max{context:c,end:owner+2})) {
                    return Err("C587 foreign MAX author".into());
                }
                boolean(value)?;return Ok(value);
            }
        }
        if let Some(value)=cache.exports.get(&wire) {return Ok(*value);}
        let value=Fr::from(self.context.producer.exports.bit(wire)?as u64);
        cache.exports.insert(wire,value);Ok(value)
    }
}

#[path="h21_native_owner_values_tests.rs"]
mod tests;

#[path="h21_native_packed_source.rs"]
mod packed_source;

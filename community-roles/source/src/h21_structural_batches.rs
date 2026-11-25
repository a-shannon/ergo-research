//! Endpoint replay for the full-history tree, height/DAA and metadata roles.
use super::*;
use super::h21_owner_batches::Side;

#[derive(Clone,Copy)]
pub(super) struct Pass<'a> {
    pub(super) side:Side<'a>,
    pub(super) start:usize,
    pub(super) counts:&'a [usize],
    pub(super) prefix:&'a [Fr],
    pub(super) projection:&'a EdgePrefixPlan,
    pub(super) rows:&'a EqWeightLookup,
}

pub(super) trait Factory {
    fn logical_census(&self,physical_left:u64,physical_right:u64)->Result<(),String>;
    fn after_row_point(&self,r:&[Fr])->Result<Box<dyn Rounds+'_>,String>;
}
pub(super) trait Rounds {
    fn caches_extremes(&self)->bool;
    fn run(&mut self,pass:Pass<'_>,stats:&mut EdgeFullStats,
        sink:&mut dyn FnMut(usize,[Fr;3])->Result<(),String>)->Result<(),String>;
}

#[cfg(test)]
use crate::daa_history_roster::{DaaHistoryRoster,h21_zero};
#[cfg(test)]
use h21_owner_batches::{ContributionGroup,GROUP,RowLoader};
#[cfg(test)]
const WIDTH:usize=1<<20;
#[cfg(test)]
const OWNERS:usize=1<<21;

#[cfg(test)]
pub(super) fn resources(role:H21CandidateRole,required:usize,resource:&H21Role1ResourcePlan,
    budget:&H21Role1Budget,requested:usize)->Result<(usize,bool),String>{
    let family=match role {
        H21CandidateRole::HeightDaa=>256usize<<20,
        H21CandidateRole::Tree|H21CandidateRole::Metadata=>0,
        H21CandidateRole::Point=>return Err("POINT has a separate H21 producer".into()),
    };
    let base=required.checked_add(family).and_then(|v|v.checked_add(1<<20))
        .ok_or("H21 shared structural capacity overflow")?;
    let mut free=budget.limit_bytes.checked_sub(base).ok_or("H21 structural family exceeds role budget")?;
    // Only one axis is resident. Each extreme may keep two full coefficient
    // vectors, a full X, a packed row and the short prefix. Reserve another
    // full pair of coefficient vectors for sparse-to-sparse folding.
    let pair=resource.replay_banks_bytes.checked_mul(2).and_then(|v|v.checked_add(resource.expanded_owner_bytes))
        .and_then(|v|v.checked_add(WIDTH/8+65536)).and_then(|v|v.checked_mul(2))
        .ok_or("H21 retained owner capacity overflow")?;
    let retain=role!=H21CandidateRole::Metadata && free>=pair;
    if retain{free-=pair;}
    // Preserve the existing serial peak and allow a whole replay, visitor,
    // cache, stack and bounded 16-triple result window for every extra lane.
    let lane=[resource.cache_bytes,resource.replay_banks_bytes,resource.expanded_owner_bytes,
        budget.visitor_scratch_bytes,65usize<<20].into_iter().try_fold(0usize,|total,n|total.checked_add(n))
        .ok_or("H21 structural lane capacity overflow")?;
    Ok((requested.clamp(1,8).min((free/lane).max(1)),retain))
}

/// The same production bounds at equality, just below it and at overflow.
#[cfg(test)]
pub(crate) fn check_resource_bounds()->Result<(),String>{
    let mut budget=H21Role1Budget{limit_bytes:22usize<<30,caller_context_bytes:3usize<<30,
        visitor_scratch_bytes:512usize<<20,unmeasured_bytes:2usize<<30};
    let r=h21_role1_resource_preflight(20,21,19,0,&[19],512,budget)?;
    let required=1usize<<30;
    let lane=r.cache_bytes+r.replay_banks_bytes+r.expanded_owner_bytes+budget.visitor_scratch_bytes+(65<<20);
    let pair=2*(2*r.replay_banks_bytes+r.expanded_owner_bytes+WIDTH/8+65536);
    for role in [H21CandidateRole::Tree,H21CandidateRole::HeightDaa,H21CandidateRole::Metadata] {
        let shared=required+(1<<20)+if role==H21CandidateRole::HeightDaa{256<<20}else{0};
        budget.limit_bytes=shared-1;
        if resources(role,required,&r,&budget,8).is_ok(){return Err("short structural budget accepted".into());}
        budget.limit_bytes=shared;
        if resources(role,required,&r,&budget,8)?!=(1,false){return Err("invalid serial fallback".into());}
        let retained=role!=H21CandidateRole::Metadata;
        let kept=if retained{pair}else{0};
        if retained{
            budget.limit_bytes=shared+pair-1;
            if resources(role,required,&r,&budget,8)?.1{return Err("under-reserved retained owner".into());}
        }
        for (extra,requested,expected) in [(0,8,1),(2*lane-1,8,1),(2*lane,8,2),(8*lane,4,4),(12*lane,16,8)]{
            budget.limit_bytes=shared+kept+extra;
            if resources(role,required,&r,&budget,requested)?!=(expected,retained){
                return Err("H21 structural lane/retention budget boundary".into());
            }
        }
    }
    if resources(H21CandidateRole::Point,required,&r,&budget,8).is_ok()
        || resources(H21CandidateRole::Tree,usize::MAX,&r,&budget,8).is_ok(){
        return Err("unsupported structural role or budget overflow".into());
    }
    Ok(())
}
#[cfg(test)]
pub(super) type Visit<'a>=dyn Fn(bool,usize,&mut dyn FnMut(EdgeTerm)->Result<(),String>)->Result<(),String>+Sync+'a;

#[cfg(test)]
#[derive(Clone,Copy)]
pub(super) struct Config<'a,'p> {
    pub(super) shape:&'a H21CandidateShape,
    pub(super) daa:Option<&'a DaaHistoryRoster<'p>>,
    pub(super) load:&'a RowLoader<'a>,
    pub(super) visit:&'a Visit<'a>,
    pub(super) workers:usize,
    pub(super) retain_hot:bool,
}

#[cfg(test)]
impl<'a,'p> Config<'a,'p> {
    pub(super) fn prepare(&self,r:&[Fr])->Result<Prepared<'a,'p>,String>{
        if self.shape.input_log()!=41 || self.shape.input_bits()!=20 || self.shape.row_log()!=r.len()
            || !(1..=8).contains(&self.workers) || self.workers>rayon::current_num_threads()
            || self.daa.is_some()!=(self.shape.role()==H21CandidateRole::HeightDaa)
            || !matches!(self.shape.role(),H21CandidateRole::Tree|H21CandidateRole::HeightDaa|H21CandidateRole::Metadata)
            || self.retain_hot && self.shape.role()==H21CandidateRole::Metadata {
            return Err("invalid H21 structural replay profile".into());
        }
        let family=self.daa.map(|daa|h21_zero::Family::new(daa,r)).transpose()?;
        Ok(Prepared{config:*self,family,axis:None,hot:[None,None],finished:[false;2]})
    }
}

#[cfg(test)]
impl Factory for Config<'_,'_> {
    fn logical_census(&self,physical_left:u64,physical_right:u64)->Result<(),String>{
        let mut omitted=0u64;
        if let Some(daa)=self.daa {
            for owner in 0..OWNERS {
                omitted=EdgeFullStats::add(omitted,daa.h21_zero_logical_count(owner)? as u64)?;
            }
            if omitted!=daa.h21_zero_logical_total()? as u64 {
                return Err("H21 DAA zero-row class census differs".into());
            }
        }
        let left=EdgeFullStats::add(physical_left,omitted)?;
        if left!=EdgeFullStats::add(physical_right,omitted)? {
            return Err("H21 structural logical endpoint census differs".into());
        }
        println!("H21_STRUCTURAL_CENSUS {}",serde_json::json!({"role":self.shape.role().index(),
            "physical_left":physical_left,"physical_right":physical_right,"omitted_per_side":omitted,
            "logical_per_side":left,"workers":self.workers,"retained_extremes":self.retain_hot}));
        Ok(())
    }
    fn after_row_point(&self,r:&[Fr])->Result<Box<dyn Rounds+'_>,String>{Ok(Box::new(self.prepare(r)?))}
}

#[cfg(test)]
struct Hot {
    count:usize,
    prefix:Vec<Fr>,
    state:EdgeReplayState,
    raw:Option<Vec<u8>>,
}
#[cfg(test)]
pub(super) struct Prepared<'a,'p>{
    config:Config<'a,'p>,
    family:Option<h21_zero::Family<'a,'p>>,
    axis:Option<bool>,
    hot:[Option<Hot>;2],
    finished:[bool;2],
}

#[cfg(test)]
fn physical(cfg:&Config<'_,'_>,pass:Pass<'_>,owner:usize,count:usize,input:&mut impl EdgeInput)
    ->Result<EdgeReplayState,String> {
    let weight=|e:&EdgeTerm|Ok(pass.rows.at(e.term.row));
    let mut visit=cfg.visit;
    let bits=cfg.shape.base_row_bits();
    let members=cfg.shape.member_row_bits();
    match pass.side {
        Side::U=>edge_replay_u(&mut visit,input,owner,WIDTH,OWNERS,bits,members,
            count,&weight,pass.prefix,Some(pass.projection)),
        Side::V{local,owners,value,zero:None}=>edge_replay_v(&mut visit,input,owner,WIDTH,OWNERS,bits,members,
            count,&weight,owners,local,value,pass.prefix,Some(pass.projection)),
        Side::V{zero:Some(_),..}=>Err("role-1 right-zero injection on another H21 role".into()),
    }
}

#[cfg(test)]
fn contribution(family:Option<&h21_zero::Family<'_,'_>>,round:Option<&h21_zero::Round>,pass:Pass<'_>,
    owner:usize,state:&EdgeReplayState,raw:Option<&[u8]>)->Result<[Fr;3],String>{
    let terminal=pass.prefix.len()==20;
    let mut values=if terminal{
        let(a,b)=state.banks.terminal();[a,b,state.x[0]]
    }else{
        state.banks.message(&state.x).try_into().map_err(|_|"H21 structural quadratic degree")?
    };
    if let (Some(f),Some(q))=(family,round){
        let high=match pass.side{Side::U=>None,Side::V{owners,..}=>Some(owners)};
        let adjustment=q.contribution(f,owner,&state.x,raw,high)?;
        if terminal && !adjustment[2].is_zero(){return Err("DAA terminal contribution changed X".into());}
        for (total,value) in values.iter_mut().zip(adjustment){*total+=value;}
    }
    Ok(values)
}

#[cfg(test)]
impl Prepared<'_,'_>{
    fn ordinary(&self,pass:Pass<'_>,round:Option<&h21_zero::Round>,start:usize,counts:&[usize],
        stats:&mut EdgeFullStats,sink:&mut dyn FnMut(usize,[Fr;3])->Result<(),String>)->Result<(),String>{
        if counts.is_empty(){return Ok(());}
        let raw=self.family.is_some() && matches!(pass.side,Side::U);
        h21_owner_batches::indexed_groups(self.config.workers,self.config.load,start,counts,stats,sink,
            |begin,segment,input|{
                let mut output=ContributionGroup{start:begin,len:segment.len(),values:[[Fr::zero();3];GROUP],
                    stats:EdgeFullStats::default()};
                for (i,&count) in segment.iter().enumerate(){
                    let owner=begin+i;
                    let state=physical(&self.config,pass,owner,count,input)?;
                    output.stats.state(&state,count,false,pass.prefix.len(),input)?;
                    let began=std::time::Instant::now();
                    let row=if raw{Some(input.header_bits(owner)?)}else{None};
                    output.values[i]=contribution(self.family.as_ref(),round,pass,owner,&state,row)?;
                    if pass.prefix.len()<20 {
                        output.stats.message_ns=EdgeFullStats::add(output.stats.message_ns,EdgeFullStats::ns(began)?)?;
                    }
                }
                Ok(output)
            })
    }

    fn extreme(&mut self,pass:Pass<'_>,round:Option<&h21_zero::Round>,index:usize,owner:usize,
        count:usize,stats:&mut EdgeFullStats)->Result<[Fr;3],String>{
        if self.finished[index]{return Err("H21 retained owner already handed off".into());}
        if let Some(hot)=self.hot[index].as_mut(){
            let (last,before)=pass.prefix.split_last().ok_or("repeated structural hot setup")?;
            if hot.count!=count || hot.prefix!=before{return Err("non-consecutive retained H21 owner fold".into());}
            hot.state.banks.fold(*last);
            gkr::fold(&mut hot.state.x,*last);
            hot.prefix.push(*last);
            stats.sequential_bank_folds=EdgeFullStats::add(stats.sequential_bank_folds,1)?;
            stats.sequential_x_folds=EdgeFullStats::add(stats.sequential_x_folds,1)?;
            stats.banks=stats.banks.max(hot.state.banks.direct_bound()?);
        }else{
            if !pass.prefix.is_empty(){return Err("retained H21 owner must begin at the empty prefix".into());}
            let mut input=h21_role1_input(self.config.load)?;
            let state=physical(&self.config,pass,owner,count,&mut input)?;
            stats.state(&state,count,false,0,&input)?;
            let raw=if self.family.is_some() && matches!(pass.side,Side::U) {
                Some(input.header_bits(owner)?.to_vec())
            }else{None};
            self.hot[index]=Some(Hot{count,prefix:Vec::with_capacity(20),state,raw});
        }
        let hot=self.hot[index].as_ref().ok_or("missing retained H21 state")?;
        let began=std::time::Instant::now();
        let values=contribution(self.family.as_ref(),round,pass,owner,&hot.state,hot.raw.as_deref())?;
        if pass.prefix.len()<20 {
            stats.message_ns=EdgeFullStats::add(stats.message_ns,EdgeFullStats::ns(began)?)?;
        }else{
            self.hot[index]=None;
            self.finished[index]=true;
        }
        Ok(values)
    }
}

#[cfg(test)]
impl Rounds for Prepared<'_,'_>{
    fn caches_extremes(&self)->bool{self.config.retain_hot}
    fn run(&mut self,pass:Pass<'_>,stats:&mut EdgeFullStats,
        sink:&mut dyn FnMut(usize,[Fr;3])->Result<(),String>)->Result<(),String>{
        let end=pass.start.checked_add(pass.counts.len()).ok_or("H21 structural owner range overflow")?;
        if pass.counts.is_empty() || end>OWNERS || pass.prefix.len()>20 || pass.projection.k!=pass.prefix.len()
            || pass.projection.width!=WIDTH{return Err("H21 structural batch geometry".into());}
        let left=matches!(pass.side,Side::U);
        let v=match pass.side{
            Side::U=>None,
            Side::V{local,owners,value,zero:None} if local.len()==WIDTH && owners.len()==OWNERS=>Some((local,value)),
            _=>return Err("H21 structural V weights or role selection".into()),
        };
        if self.axis!=Some(left){
            if self.axis.is_some() && (left || self.hot.iter().flatten().any(|h|h.prefix.len()!=20)){
                return Err("retained H21 owners changed axis before terminal handoff".into());
            }
            self.hot=[None,None];
            self.finished=[false;2];
            self.axis=Some(left);
        }
        let round=self.family.as_ref().map(|f|f.round(pass.prefix,v)).transpose()?;
        let mut cursor=pass.start;
        if self.config.retain_hot {
            for (index,owner) in [0usize,OWNERS-1].into_iter().enumerate(){
                if !(cursor..end).contains(&owner){continue;}
                let offset=owner-pass.start;
                self.ordinary(pass,round.as_ref(),cursor,&pass.counts[cursor-pass.start..offset],stats,sink)?;
                let output=self.extreme(pass,round.as_ref(),index,owner,pass.counts[offset],stats)?;
                sink(owner,output)?;
                cursor=owner+1;
            }
        }
        self.ordinary(pass,round.as_ref(),cursor,&pass.counts[cursor-pass.start..],stats,sink)
    }
}

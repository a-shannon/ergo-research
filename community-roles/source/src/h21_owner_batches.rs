//! Bounded owner-parallel replay of one role-1 sumcheck pass.
use super::*;

#[derive(Clone,Copy)]
pub(super) enum Side<'a> {
    U,
    V { local:&'a [Fr], owners:&'a [Fr], value:Fr, zero:Option<Fr> },
}

#[derive(Clone,Copy)]
pub(super) struct Pass<'a> {
    pub(super) side:Side<'a>,
    pub(super) start:usize,
    pub(super) counts:&'a [usize],
    pub(super) prefix:&'a [Fr],
    pub(super) projection:&'a EdgePrefixPlan,
    pub(super) header:&'a h21_weighted_header::Header<'a>,
    pub(super) round:&'a h21_weighted_header::Round,
    pub(super) rows:&'a EqWeightLookup,
}

pub(super) trait Runner {
    fn run(&self, pass:Pass<'_>, stats:&mut EdgeFullStats,
        sink:&mut dyn FnMut(usize,[Fr;3])->Result<(),String>) -> Result<(),String>;
}

#[cfg(test)]
pub(super) struct Lanes<'a> {
    pub(super) workers:usize,
    pub(super) load:&'a (dyn Fn(usize)->Result<Vec<u8>,String>+Sync),
    pub(super) visit:&'a (dyn Fn(bool,usize,&mut dyn FnMut(EdgeTerm)->Result<(),String>)->Result<(),String>+Sync),
}

#[cfg(test)]
pub(super) const GROUP:usize=16;
#[cfg(test)]
const WIDTH:usize=1<<20;
#[cfg(test)]
const OWNERS:usize=1<<21;

#[cfg(test)]
pub(super) struct ContributionGroup {
    pub(super) start:usize,
    pub(super) len:usize,
    pub(super) values:[[Fr;3];GROUP],
    pub(super) stats:EdgeFullStats,
}

#[cfg(test)]
impl Lanes<'_> {
    fn evaluate(&self,pass:&Pass<'_>,start:usize,counts:&[usize],input:&mut impl EdgeInput)
        ->Result<ContributionGroup,String> {
        let mut group=ContributionGroup{start,len:counts.len(),values:[[Fr::zero();3];GROUP],
            stats:EdgeFullStats::default()};
        let terminal=pass.prefix.len()==20;
        let row_weight=|edge:&EdgeTerm|Ok(pass.rows.at(edge.term.row));
        let mut visit=self.visit;
        for (i,&count) in counts.iter().enumerate() {
            let owner=start+i;
            let (state,high)=match pass.side {
                Side::U=>(edge_replay_u(&mut visit,input,owner,WIDTH,OWNERS,19,&[19],
                    count,&row_weight,pass.prefix,Some(pass.projection))?,None),
                Side::V{local,owners,value,zero}=>(edge_replay_v_with_zero(&mut visit,input,
                    owner,WIDTH,OWNERS,19,&[19],count,&row_weight,owners,local,value,
                    pass.prefix,Some(pass.projection),zero)?,Some(owners)),
            };
            group.stats.state(&state,count,false,pass.prefix.len(),input)?;
            let started=std::time::Instant::now();
            let mut result=h21_weighted_header::combine(Some(pass.header),Some(pass.round),
                input,owner,&state,high)?;
            if terminal {
                if state.x.len()!=1{return Err("H21 terminal projected X extent".into());}
                result[2]=state.x[0];
            } else {
                group.stats.message_ns=EdgeFullStats::add(group.stats.message_ns,EdgeFullStats::ns(started)?)?;
            }
            group.values[i]=result;
        }
        Ok(group)
    }
}

#[cfg(test)]
fn merge_stats(total:&mut EdgeFullStats,local:&EdgeFullStats)->Result<(),String>{
    // Only state() and the local-message timer are updated on a worker.
    // Durations below are summed owner work; the coordinator times the pass.
    total.term_callbacks=EdgeFullStats::add(total.term_callbacks,local.term_callbacks)?;
    total.owner_requests=EdgeFullStats::add(total.owner_requests,local.owner_requests)?;
    total.emitted_fields=EdgeFullStats::add(total.emitted_fields,local.emitted_fields)?;
    total.sequential_x_folds=EdgeFullStats::add(total.sequential_x_folds,local.sequential_x_folds)?;
    total.sequential_bank_folds=EdgeFullStats::add(total.sequential_bank_folds,local.sequential_bank_folds)?;
    total.input_vector_clones=EdgeFullStats::add(total.input_vector_clones,local.input_vector_clones)?;
    total.message_ns=EdgeFullStats::add(total.message_ns,local.message_ns)?;
    total.x=total.x.max(local.x);
    total.banks=total.banks.max(local.banks);
    Ok(())
}

#[cfg(test)]
impl Runner for Lanes<'_> {
    fn run(&self,pass:Pass<'_>,stats:&mut EdgeFullStats,
        sink:&mut dyn FnMut(usize,[Fr;3])->Result<(),String>)->Result<(),String> {
        if !(2..=8).contains(&self.workers) || self.workers>rayon::current_num_threads()
            || pass.counts.is_empty() || pass.start.checked_add(pass.counts.len()).is_none_or(|n|n>OWNERS)
            || pass.prefix.len()>20 || pass.projection.width!=WIDTH || pass.projection.k!=pass.prefix.len() {
            return Err("invalid H21 owner batch geometry, pool or projection".into());
        }
        if let Side::V{local,owners,..}=pass.side {
            if local.len()!=WIDTH || owners.len()!=OWNERS {return Err("H21 V weight dimensions".into());}
        }
        indexed_groups(self.workers,self.load,pass.start,pass.counts,stats,sink,
            |start,counts,input|self.evaluate(&pass,start,counts,input))
    }
}

#[cfg(test)]
pub(super) type RowLoader<'a>=dyn Fn(usize)->Result<Vec<u8>,String>+Sync+'a;

/// Disjoint owner ranges share immutable round data. Cache lifetime is a pass;
/// only the coordinator can emit results or advance the transcript.
#[cfg(test)]
pub(super) fn indexed_groups<'a>(workers:usize,load:&'a RowLoader<'a>,start:usize,counts:&[usize],
    stats:&mut EdgeFullStats,sink:&mut dyn FnMut(usize,[Fr;3])->Result<(),String>,
    evaluate:impl Fn(usize,&[usize],&mut H21Role1PackedInput<&'a RowLoader<'a>>)->Result<ContributionGroup,String>+Sync
) -> Result<(),String>{
    use rayon::prelude::*;
    if !(1..=8).contains(&workers) || workers>rayon::current_num_threads() ||
        start.checked_add(counts.len()).is_none_or(|end|end>OWNERS){
        return Err("invalid indexed H21 owner range or worker budget".into());
    }
    if counts.is_empty(){return Ok(());}
    let active=workers.min(counts.len());
    let mut inputs=(0..active).map(|_|h21_role1_input(load)).collect::<Result<Vec<_>,_>>()?;
    let mut next=start;
    for batch in counts.chunks(active*GROUP) {
        let chunk=batch.len().div_ceil(active);
        let groups=batch.len().div_ceil(chunk);
        let result:Vec<_>=if groups==1 {
            vec![evaluate(next,batch,&mut inputs[0])]
        }else{
            inputs[..groups].par_iter_mut().zip(batch.par_chunks(chunk))
                .enumerate().map(|(i,(input,counts))|evaluate(next+i*chunk,counts,input)).collect()
        };
        // No part of this batch reaches the coordinator after a lane error.
        for r in &result {if let Err(e)=r{return Err(e.clone());}}
        for r in result {
            let group=r?;
            if group.start!=next || group.len==0 || group.len>GROUP {
                return Err("H21 owner batch handoff order or extent".into());
            }
            merge_stats(stats,&group.stats)?;
            for &values in &group.values[..group.len] {sink(next,values)?;next+=1;}
        }
    }
    if next!=start+counts.len(){return Err("incomplete H21 owner batch".into());}
    Ok(())
}

#[cfg(all(test,windows,feature="h21-snapshot-n0"))]
#[path="h21_owner_batch_tests.rs"]
mod tests;
#[cfg(all(test,windows,feature="h21-snapshot-n0"))]
pub(crate) use tests::check_h21_owner_batches;

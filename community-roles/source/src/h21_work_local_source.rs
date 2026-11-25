//! Source-owned Work LOCAL publication. This namespace is owner*2048,
//! tagged independently of ROW19. No Map read, shared X commitment, cumulative
//! Work, cross-slot link, global coverage or proof is admitted here.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use std::collections::{BTreeMap, BTreeSet};
use crate::{packed_owner_assembly::{NativeOwnerProducer, WorkLocalLease, NativeWorkLocalLease},
    sparse::Term, work_tree_history_plan::WorkTreeHistoryPlan, work_tree_layout::{self, WIDTH}};

pub(crate) const H21_OWNER: usize = 845_759;
pub(crate) const LOCAL_STRIDE: usize = 2048;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Parent {
    pub root: [u8;32], pub total: [u8;28], pub profile: [u8;32],
    pub headers: u64, pub slots: usize, pub cut: Vec<u8>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Role { WorkLocal { owner: usize, height: usize } }
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct TaggedTerm { pub role: Role, pub term: Term }

/// Ordered, exhaustive active endpoint domain, including zero-valued bits.
pub(crate) fn operand_domain(owner: usize) -> Result<Vec<usize>, String> {
    let e=&work_tree_layout::shared_baseline()?.endpoints;
    let mut domain=Vec::with_capacity(1184);
    for wires in [&e.n_bits,&e.lower,&e.upper,&e.work,&e.work_minus_one,&e.exponent] {
        for &wire in wires { domain.push(owner.checked_mul(WIDTH).and_then(|x|x.checked_add(wire))
            .ok_or("Work LOCAL wire overflow")?); }
    }
    if domain.len()!=1184 || domain.iter().copied().collect::<BTreeSet<_>>().len()!=1184 {
        return Err("Work LOCAL exact active operand domain".into());
    }
    Ok(domain)
}
pub(crate) fn canonical_terms(plan:&WorkTreeHistoryPlan,owner:usize)->Result<Vec<TaggedTerm>,String> {
    if LOCAL_STRIDE!=crate::work_tree_work::LOCAL_ROW_WIDTH || owner>=plan.descriptor().genuine {
        return Err("Work LOCAL requires genuine owner/geometry".into());
    }
    let height=owner.checked_add(2).ok_or("Work LOCAL height overflow")?;
    let mut terms=Vec::new();
    plan.work_boundary().emit_slot(owner,|term|terms.push(TaggedTerm {
        role:Role::WorkLocal{owner,height},term }))?;
    if terms.len()!=3265 || terms.iter().any(|t|t.term.row/LOCAL_STRIDE!=owner
        || t.term.gate.left/WIDTH!=owner || t.term.gate.right/WIDTH!=owner) {
        return Err("Work LOCAL canonical role geometry/census".into());
    }
    Ok(terms)
}
/// No absent active input is interpreted as zero. Zero-coefficient operands
/// remain in canonical term identity but need no assignment outside this role.
pub(crate) fn require_zero_residual(terms:&[TaggedTerm],operands:&[(usize,Fr)])
    ->Result<usize,String> {
    let mut cells=BTreeMap::new();
    for &(wire,value) in operands {
        if !(value.is_zero()||value.is_one()) || cells.insert(wire,value).is_some() {
            return Err("Work LOCAL duplicate/nonboolean operand".into());
        }
    }
    let read=|wire|cells.get(&wire).copied().ok_or("Work LOCAL missing active operand");
    let mut residuals=BTreeMap::<usize,Fr>::new();
    for tagged in terms {
        let g=&tagged.term.gate;
        let x=if !g.c1.is_zero()||!g.c3.is_zero(){read(g.left)?}else{Fr::zero()};
        let y=if !g.c2.is_zero()||!g.c3.is_zero(){read(g.right)?}else{Fr::zero()};
        *residuals.entry(tagged.term.row).or_default()+=g.c0+g.c1*x+g.c2*y+g.c3*x*y;
    }
    if residuals.is_empty() || residuals.values().any(|r|!r.is_zero()) {
        return Err("Work LOCAL nonzero per-row residual".into());
    }
    Ok(residuals.len())
}

/// Generic, in-process local custody core. It grants no H21 admission.
pub(crate) struct LocalPublisher<'a> {
    producer:&'a NativeOwnerProducer<'a>, owner:usize, published:bool,
    terms:Vec<TaggedTerm>, operands:Vec<(usize,Fr)>,
}
impl<'a> LocalPublisher<'a> {
    pub(crate) fn new(producer:&'a NativeOwnerProducer<'a>,owner:usize)->Result<Self,String> {
        producer.work_local_parent(owner)?;
        Ok(Self{producer,owner,published:false,terms:Vec::new(),operands:Vec::new()})
    }
    pub(crate) fn publish(&mut self,lease:&WorkLocalLease<'_>)->Result<(usize,usize),String> {
        if self.published {return Err("Work LOCAL publication replay".into());}
        self.producer.require_work_local_lease(self.owner,lease)?;
        // Build all fallible state before installing the single publication.
        let terms=lease.terms().to_vec();let operands=lease.operands().to_vec();
        let rows=require_zero_residual(&terms,&operands)?;
        self.terms=terms;self.operands=operands;self.published=true;
        Ok((self.terms.len(),rows))
    }
    #[cfg(test)]
    pub(crate) fn state_counts(&self)->(bool,usize,usize){(self.published,self.terms.len(),self.operands.len())}
}

/// Strict H21 wrapper accepts only the separately typed native lease.
pub(crate) struct NativeWorkLocalPublisher<'a> {
    local:LocalPublisher<'a>, parent:crate::h21_scheduled_max_cap::NativeParent,
}
impl<'a> NativeWorkLocalPublisher<'a> {
    pub(crate) fn new(producer:&'a NativeOwnerProducer<'a>)->Result<Self,String> {
        let parent=producer.work_local_native_parent()?;
        Ok(Self{local:LocalPublisher::new(producer,H21_OWNER)?,parent})
    }
    pub(crate) fn publish(&mut self,lease:&NativeWorkLocalLease<'_>)->Result<(usize,usize),String> {
        self.local.producer.require_native_work_local_lease(&self.parent,lease)?;
        self.local.publish(lease.local())
    }
}

//! HEADER view over the frozen DAA roster and scheduled MAX/Cap.
//! Retires only exact active helper anchors. No DAA arithmetic merger, native
//! witness authority, Map/Score admission, ROW allocation or PCS claim.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use crate::{daa_history_roster::{DaaHistoryRoster, HeaderCounts},
    h21_scheduled_max_cap::{Plan as Scheduled, Writer}, sparse::Term,
    wiring::{evaluate_shift, RightIndex}};

const WIDTH:usize=1<<20;
const ROWS:usize=1<<19;
const FIRST_ROW:usize=356632;
const FIRST_WIRE:usize=999424;
const END_WIRE:usize=1004866;
const RANGES:[(usize,usize,usize);4]=[
    (356632,999424,673),(357305,1000097,673),
    (357978,1000770,2048),(360026,1002818,2048),
];

fn eq(p:&[Fr],n:usize)->Fr {
    p.iter().enumerate().fold(Fr::one(),|a,(b,z)|
        a*if n>>b&1==1 {*z}else{Fr::one()-z})
}

#[derive(Debug)]
pub(super) struct RetainedHeader {
    pub terms:Vec<Term>,
    pub roster:HeaderCounts,
    pub retired:[usize;4],
}

pub(super) struct Merge<'r,'p> {
    roster:&'r DaaHistoryRoster<'p>,
    scheduled:&'r Scheduled,
}
impl<'r,'p> Merge<'r,'p> {
    pub(super) fn new(roster:&'r DaaHistoryRoster<'p>,scheduled:&'r Scheduled)->Result<Self,String> {
        if roster.headers()!=scheduled.descriptor().terminals()[0] as u64 || roster.slot_log()!=21
            || roster.row_log()!=40 || roster.input_log()!=41 {
            return Err("HEADER/scheduled fixed H21 geometry".into());
        }
        Ok(Self{roster,scheduled})
    }

    fn active(&self,owner:usize)->Result<[bool;4],String> {
        active(self.scheduled,owner)
    }

    /// Collect one bounded owner before returning anything to a consumer.
    /// The roster is the sole HEADER producer, retaining short and mature A4
    /// release as well as the parent's work-tree retirement.
    pub(super) fn header_terms(&self,owner:usize)->Result<RetainedHeader,String> {
        let active=self.active(owner)?;
        let (terms,retired,roster)=if self.roster.cached_header() {
            // Publish the single resulting Vec only after the scheduled-anchor
            // identity, uniqueness and full count checks have all completed.
            filter_stream(owner,active,396_561,|sink|self.roster.visit_header_terms(owner as u64,sink))?
        } else {
            let mut source=Vec::new();
            let roster=self.roster.visit_header_terms(owner as u64,|t|{source.push(t);Ok(())})?;
            let (terms,retired)=filter(owner,active,source)?;
            (terms,retired,roster)
        };
        if roster.emitted!=terms.len()+retired.iter().sum::<usize>() {
            return Err("HEADER/scheduled emission count".into());
        }
        Ok(RetainedHeader{terms,roster,retired})
    }

    /// Global coefficients: the retirement factor includes every scheduled
    /// owner through fixed interval/residue kernels, not the selected test set.
    pub(super) fn coefficients(&self,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String> {
        dimensions(r,u,v)?;
        let mut out=self.roster.header_coefficients(r,u,v)?;
        out[1]-=retired_coefficient(self.scheduled,r,u,v)?;
        let added=self.scheduled.coefficients(r,u,v)?;
        for (a,b) in out.iter_mut().zip(added){*a+=b;}
        Ok(out)
    }

    /// Global slot0 HEADER coefficients after the fixed ROW19 placement.
    /// F and scheduled retirement already contain their owner masks. Only the
    /// canonical tail's row-relocation correction receives the same-slot factor.
    pub(super) fn placed_header_coefficients(&self,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String> {
        dimensions(r,u,v)?;
        if self.scheduled.descriptor()!=crate::bank53_map::CutDescriptor::eligible08() {
            return Err("placed HEADER requires exact Eligible08 cut".into());
        }
        let tail=self.roster.canonical_header_tail()?;
        let mut out=self.roster.header_coefficients(r,u,v)?;
        out[1]-=retired_coefficient(self.scheduled,r,u,v)?;
        let mut delta=[Fr::zero();4];
        for t in tail {
            if !(393216..406406).contains(&t.row)
                || t.gate.left>=WIDTH || t.gate.right>=WIDTH {
                return Err("placed HEADER canonical tail term range".into());
            }
            let moved=t.row.checked_add(114320).filter(|q|*q<ROWS)
                .ok_or("placed HEADER tail row overflow")?;
            let weight=(eq(&r[..19],moved)-eq(&r[..19],t.row))
                *eq(&u[..20],t.gate.left)*eq(&v[..20],t.gate.right);
            for (sum,c) in delta.iter_mut().zip([t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3]) {
                *sum+=weight*c;
            }
        }
        // The placement applies to every owner, including padding beyond N.
        let same_slot=r[19..].iter().zip(&u[20..]).zip(&v[20..])
            .fold(Fr::one(),|a,((r,u),v)|
                a*((Fr::one()-r)*(Fr::one()-u)*(Fr::one()-v)+*r**u**v));
        for (value,correction) in out.iter_mut().zip(delta) {
            *value+=same_slot*correction;
        }
        Ok(out)
    }
}

fn active(plan:&Scheduled,owner:usize)->Result<[bool;4],String> {
    let mut roles=[false;4];
    plan.visit_owner(owner,|writer,_|{
        let index=match writer {
            Writer::Max{context,..} if context<2=>context,
            Writer::Cap{context,..} if context<2=>2+context,
            _=>return Err("HEADER/scheduled writer context".into()),
        };
        roles[index]=true;Ok(())
    })?;
    Ok(roles)
}

/// Identity and complete census precede publication of the returned vector.
fn filter(owner:usize,active:[bool;4],source:Vec<Term>)->Result<(Vec<Term>,[usize;4]),String> {
    if owner>=1<<21{return Err("HEADER/scheduled owner".into());}
    let rb=owner.checked_mul(ROWS).ok_or("HEADER row overflow")?;
    let xb=owner.checked_mul(WIDTH).ok_or("HEADER input overflow")?;
    let mut seen=vec![false;END_WIRE-FIRST_WIRE];
    let mut retired=[0;4];let mut out=Vec::with_capacity(source.len());
    for t in source {
        let q=t.row.checked_sub(rb).filter(|q|*q<ROWS).ok_or("HEADER row owner mismatch")?;
        if (FIRST_ROW..FIRST_ROW+seen.len()).contains(&q) {
            let k=q-FIRST_ROW;
            if seen[k]{return Err("duplicate scheduled HEADER anchor".into());}
            if t.gate.left!=xb+FIRST_WIRE+k || t.gate.right!=xb
                || [t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3]
                    !=[Fr::zero(),Fr::one(),Fr::zero(),Fr::zero()] {
                return Err("scheduled HEADER anchor identity".into());
            }
            seen[k]=true;
            let role=RANGES.iter().position(|&(a,_,n)|(a..a+n).contains(&q))
                .ok_or("scheduled HEADER anchor partition")?;
            if active[role]{retired[role]+=1;continue;}
        } else if (FIRST_WIRE..END_WIRE).contains(&(t.gate.left%WIDTH))
            || (FIRST_WIRE..END_WIRE).contains(&(t.gate.right%WIDTH)) {
            return Err("additional scheduled helper HEADER consumer".into());
        }
        out.push(t);
    }
    if seen.iter().any(|b|!*b){return Err("missing scheduled HEADER anchor".into());}
    for j in 0..4 {
        if retired[j]!=if active[j]{RANGES[j].2}else{0}{return Err("scheduled retirement count".into());}
    }
    Ok((out,retired))
}

fn filter_stream<T>(owner:usize,active:[bool;4],capacity:usize,
    emit:impl FnOnce(&mut dyn FnMut(Term)->Result<(),String>)->Result<T,String>)->Result<(Vec<Term>,[usize;4],T),String> {
    if owner>=1<<21{return Err("HEADER/scheduled owner".into());}
    let rb=owner.checked_mul(ROWS).ok_or("HEADER row overflow")?;
    let xb=owner.checked_mul(WIDTH).ok_or("HEADER input overflow")?;
    let mut seen=vec![false;END_WIRE-FIRST_WIRE];
    let mut retired=[0;4];let mut out=Vec::with_capacity(capacity);
    let result=emit(&mut |t| {
        let q=t.row.checked_sub(rb).filter(|q|*q<ROWS).ok_or("HEADER row owner mismatch")?;
        if (FIRST_ROW..FIRST_ROW+seen.len()).contains(&q) {
            let k=q-FIRST_ROW;
            if seen[k]{return Err("duplicate scheduled HEADER anchor".into());}
            if t.gate.left!=xb+FIRST_WIRE+k || t.gate.right!=xb
                || [t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3]
                    !=[Fr::zero(),Fr::one(),Fr::zero(),Fr::zero()] {
                return Err("scheduled HEADER anchor identity".into());
            }
            seen[k]=true;
            let role=RANGES.iter().position(|&(a,_,n)|(a..a+n).contains(&q))
                .ok_or("scheduled HEADER anchor partition")?;
            if active[role]{retired[role]+=1;return Ok(());}
        } else if (FIRST_WIRE..END_WIRE).contains(&(t.gate.left%WIDTH))
            || (FIRST_WIRE..END_WIRE).contains(&(t.gate.right%WIDTH)) {
            return Err("additional scheduled helper HEADER consumer".into());
        }
        out.push(t);Ok(())
    })?;
    if seen.iter().any(|b|!*b){return Err("missing scheduled HEADER anchor".into());}
    for j in 0..4 {
        if retired[j]!=if active[j]{RANGES[j].2}else{0}{return Err("scheduled retirement count".into());}
    }
    Ok((out,retired,result))
}

fn dimensions(r:&[Fr],u:&[Fr],v:&[Fr])->Result<(),String> {
    if (r.len(),u.len(),v.len())!=(40,41,41){return Err("HEADER/scheduled coefficient dimensions".into());}
    Ok(())
}

fn retired_coefficient(plan:&Scheduled,r:&[Fr],u:&[Fr],v:&[Fr])->Result<Fr,String> {
    dimensions(r,u,v)?;
    let owner=plan.anchor_owner_weights(&r[19..],&u[20..],&v[20..])?;
    let mut row_point=r[..19].to_vec();row_point.push(Fr::zero());
    let zero=[Fr::zero();20];let mut out=Fr::zero();
    for (j,&(a,b,n)) in RANGES.iter().enumerate() {
        // Iterate local wire i, map it to row i-(b-a); pad ROW19 with a fixed
        // zero high bit. The right placeholder remains owner-local X(o,0).
        let local=evaluate_shift(&u[..20],&row_point,&zero,(b-a)as u64,
            b as u64,(b+n)as u64,0,RightIndex::GlobalZero)?*eq(&v[..20],0);
        out+=owner[j]*local;
    }
    Ok(out)
}

#[cfg(test)]
#[path="header_scheduled_retirement_tests.rs"]
mod tests;

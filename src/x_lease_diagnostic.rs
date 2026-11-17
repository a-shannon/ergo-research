//! Test-only X-domain and atomic-publication diagnostic, independent of ROW layout.
//! Native producers supply values; this does not certify RAW custody, D provenance,
//! incident relations, a common transcript, or a proof. WorkTree cells are untouched.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use ergo_header_core::Header;
use crate::{daa_history_layout::HeaderAssignmentTemplate,
    daa_history_producer::{self, RawWindow, PACKED_OWNER_BYTES},
    daa_history_roster::{DaaHistoryRoster, OwnerClass, BANKS, WIDTH},
    h21_scheduled_max_cap::{Plan as Scheduled, Prepared, OwnerCells, Writer as ScheduledWriter},
    serializer, work_tree_history_plan::WorkTreeHistoryPlan};

const OWNERS:usize=1<<21;
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
#[repr(u8)]
pub(super) enum Writer { Header=1, DaaRetarget=2, AssemblyInactiveZero=3, Max0=4, Max1=5, Cap0=6, Cap1=7 }
fn retarget(class:OwnerClass)->bool {
    matches!(class,OwnerClass::M1|OwnerClass::Short(_)|OwnerClass::Mature(_))
}
fn validate_replacement_mask(mask:&[bool])->Result<(),String> {
    if mask.len()!=WIDTH || mask.iter().filter(|&&x|x).count()!=401362 {
        return Err("X lease parent mask shape/count".into());
    }
    if mask[989658..989730].iter().any(|&x|x){return Err("X lease protected endpoint release".into());}
    if mask[991232..999424].iter().any(|&x|x){return Err("X lease A4 parent release".into());}
    Ok(())
}

/// Code-owned immutable domain table. Zero means reserved for WorkTree, not zero-valued.
pub(super) struct Policy {owner:usize,class:OwnerClass,leases:Vec<u8>}
impl Policy {
    pub(super) fn lease_at(&self,owner:usize,class:OwnerClass,cell:usize)->Result<Option<Writer>,String> {
        if owner!=self.owner || class!=self.class {return Err("X lease owner/class".into());}
        let tag=*self.leases.get(cell).ok_or("X lease cell outside owner width")?;
        Ok(match tag {
            0=>None,
            value=>Some(match value {
                x if x==Writer::Header as u8=>Writer::Header,
                x if x==Writer::DaaRetarget as u8=>Writer::DaaRetarget,
                x if x==Writer::AssemblyInactiveZero as u8=>Writer::AssemblyInactiveZero,
                x if x==Writer::Max0 as u8=>Writer::Max0,
                x if x==Writer::Max1 as u8=>Writer::Max1,
                x if x==Writer::Cap0 as u8=>Writer::Cap0,
                x if x==Writer::Cap1 as u8=>Writer::Cap1,
                _=>return Err("X lease writer tag".into()),
            }),
        })
    }
    pub(super) fn new(parent:&WorkTreeHistoryPlan,roster:&DaaHistoryRoster<'_>,owner:usize)
        ->Result<Self,String> {
        if owner>=OWNERS || parent.headers()!=1827840 || parent.slot_log()!=21
            || roster.headers()!=parent.headers() || roster.slot_log()!=21 {
            return Err("X lease fixed H21 owner/geometry".into());
        }
        let class=roster.owner_class(owner as u64)?;
        let mask=parent.physical_assignment_replacement_mask(owner as u64)?;
        validate_replacement_mask(&mask)?;
        let mut p=Self{owner,class,leases:mask.iter().map(|&x|if x{0}else{Writer::Header as u8}).collect()};
        let bank_writer=if retarget(class){Writer::DaaRetarget}else{Writer::AssemblyInactiveZero};
        for (a,b) in BANKS {p.replace_header(a,b,bank_writer)?;}
        let mut active=[false;4];
        Scheduled::new().visit_owner(owner,|w,_|{
            let i=match w {ScheduledWriter::Max{context,..}if context<2=>context,
                ScheduledWriter::Cap{context,..}if context<2=>2+context,
                _=>return Err("X lease scheduled identity".into())};
            active[i]=true;Ok(())
        })?;
        for (i,(a,b,w)) in [(999424,1000097,Writer::Max0),(1000097,1000770,Writer::Max1),
            (1000770,1002818,Writer::Cap0),(1002818,1004866,Writer::Cap1)].into_iter().enumerate() {
            if active[i]{p.replace_header(a,b,w)?;}
        }
        Ok(p)
    }
    fn replace_header(&mut self,a:usize,b:usize,w:Writer)->Result<(),String> {
        if a>=b || b>WIDTH || self.leases[a..b].iter().any(|&x|x!=Writer::Header as u8) {
            return Err("X lease overlaps existing owner".into());
        }
        self.leases[a..b].fill(w as u8);Ok(())
    }
}

/// No public arbitrary-claim or caller-selected lease API exists.
pub(super) struct Scratch<'a> {policy:&'a Policy,packed:Vec<u8>,claimed:Vec<bool>}
impl<'a> Scratch<'a> {
    pub(super) fn new(policy:&'a Policy)->Self {
        Self{policy,packed:vec![0;PACKED_OWNER_BYTES],claimed:vec![false;WIDTH]}
    }
    fn stage_values(&mut self,w:Writer,owner:usize,class:OwnerClass,
        values:impl IntoIterator<Item=(usize,Fr)>)->Result<(),String> {
        if owner!=self.policy.owner || class!=self.policy.class {return Err("X stage owner/class".into());}
        let values:Vec<_>=values.into_iter().collect();
        let mut seen=std::collections::BTreeSet::new();
        for &(cell,value) in &values {
            if value!=Fr::zero() && value!=Fr::one(){return Err("X stage nonboolean".into());}
            if cell>=WIDTH || self.policy.leases[cell]!=w as u8{return Err("X stage outside lease".into());}
            if self.claimed[cell] || !seen.insert(cell){return Err("X stage duplicate claim".into());}
        }
        for (cell,value) in values {
            let mask=1u8<<(cell%8);
            if value.is_one(){self.packed[cell/8]|=mask;}else{self.packed[cell/8]&=!mask;}
            self.claimed[cell]=true;
        }
        Ok(())
    }
    pub(super) fn stage_header(&mut self,template:&HeaderAssignmentTemplate,raw:&[u8],previous:Option<&[u8]>)
        ->Result<(),String> {
        let decode=|bytes:&[u8]|->Result<Header,String>{
            let h=Header::decode(bytes,None).map_err(|e|format!("X HEADER RAW: {e:?}"))?;
            if h.encode().map_err(|e|format!("X HEADER encode: {e:?}"))?!=bytes {
                return Err("X HEADER canonical RAW".into());
            }Ok(h)
        };
        let h=decode(raw)?;let height=(self.policy.owner+1).min(1827840);
        if h.height as usize!=height{return Err("X HEADER height".into());}
        let prev=previous.map(decode).transpose()?;
        if height==1 {
            if prev.is_some(){return Err("X HEADER genesis predecessor".into());}
        }else if prev.as_ref().and_then(|p|p.height.checked_add(1))!=Some(h.height)
            || previous.map(ergo_header_core::blake2b256)!=Some(h.parent_id) {
            return Err("X HEADER predecessor identity".into());
        }
        let fields=serializer::Fields::from_header(&h)?;
        let mut native=template.assign(&fields)?;
        template.assign_order(&mut native,&fields,prev.as_ref().map_or(0,|p|p.height),
            prev.as_ref().map_or(0,|p|p.timestamp),height==1)?;
        if native.len()!=WIDTH || native.iter().any(|v|*v!=Fr::zero()&&*v!=Fr::one()) {
            return Err("X HEADER native shape/boolean".into());
        }
        let values=native.into_iter().enumerate()
            .filter(|(cell,_)|self.policy.leases[*cell]==Writer::Header as u8).collect::<Vec<_>>();
        self.stage_values(Writer::Header,self.policy.owner,self.policy.class,values)
    }
    /// Preserve the current assembler's explicit default-zero policy; not a DAA producer.
    pub(super) fn stage_assembly_inactive_zero(&mut self)->Result<(),String> {
        if retarget(self.policy.class){return Err("X inactive zero on retarget class".into());}
        self.stage_values(Writer::AssemblyInactiveZero,self.policy.owner,self.policy.class,
            BANKS.into_iter().flat_map(|(a,b)|(a..b).map(|cell|(cell,Fr::zero()))))
    }
    pub(super) fn stage_retarget(&mut self,roster:&DaaHistoryRoster<'_>,raw:RawWindow<'_>,
        outside:impl FnMut(usize)->Result<bool,String>)->Result<(),String> {
        if roster.headers()!=1827840 || roster.slot_log()!=21
            || roster.owner_class(self.policy.owner as u64)?!=self.policy.class || !retarget(self.policy.class) {
            return Err("X retarget class/roster".into());
        }
        if self.policy.leases.iter().zip(&self.claimed)
            .any(|(&tag,&done)|tag==Writer::Header as u8&&!done) {
            return Err("X retarget requires staged HEADER".into());
        }
        // Existing writer performs all fallible native validation on a private clone.
        let mut native=self.packed.clone();
        daa_history_producer::write_retarget(roster,self.policy.owner as u64,raw,&mut native,outside)?;
        self.stage_values(Writer::DaaRetarget,self.policy.owner,self.policy.class,
            BANKS.into_iter().flat_map(|(a,b)|a..b).map(|cell|
                (cell,Fr::from(((native[cell/8]>>(cell%8))&1)as u64))))
    }
    /// Values retain Prepared::from_d_iter's conditional D-source contract.
    pub(super) fn stage_scheduled(&mut self,prepared:&Prepared)->Result<(),String> {
        let owner=self.policy.owner;let class=self.policy.class;
        let mut native=OwnerCells::new(owner)?;
        prepared.owner_patch(owner)?.apply(&mut native)?;
        let mut pending=Self{policy:self.policy,packed:self.packed.clone(),claimed:self.claimed.clone()};
        for w in [Writer::Max0,Writer::Max1,Writer::Cap0,Writer::Cap1] {
            let cells=self.policy.leases.iter().enumerate().filter(|(_,tag)|**tag==w as u8)
                .map(|(cell,_)|Ok((cell,native.read(cell)?))).collect::<Result<Vec<_>,String>>()?;
            pending.stage_values(w,owner,class,cells)?;
        }
        self.packed=pending.packed;self.claimed=pending.claimed;Ok(())
    }
    /// Publication covers only participating leases. Reserved WorkTree bits survive unchanged.
    pub(super) fn publish(&self,owner:usize,class:OwnerClass,destination:&mut[u8])->Result<(),String> {
        if owner!=self.policy.owner || class!=self.policy.class || destination.len()!=PACKED_OWNER_BYTES {
            return Err("X publish owner/class/width".into());
        }
        if self.policy.leases.iter().zip(&self.claimed).any(|(&tag,&done)|tag!=0&&!done) {
            return Err("X publish incomplete claims".into());
        }
        let mut next=destination.to_vec();
        for cell in 0..WIDTH {if self.claimed[cell] {
            let mask=1u8<<(cell%8);next[cell/8]=(next[cell/8]&!mask)|(self.packed[cell/8]&mask);
        }}
        destination.copy_from_slice(&next);Ok(())
    }
}

#[cfg(test)]
#[path="x_lease_diagnostic_tests.rs"]
mod tests;

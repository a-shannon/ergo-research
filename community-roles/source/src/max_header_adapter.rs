//! Bounded retained-header / weighted suffix-MAX join. No global proof admission.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use ark_serialize::CanonicalSerialize;
use num_bigint::BigUint;
use crate::{daa_history_roster::{DaaHistoryRoster, HeaderCounts},
    native_owner_exports::NativeExports, packed_owner_assembly::{NativePrefix, validate_native_plan_input},
    sparse::Term, suffix_max::{self, Layout}, transcript::Transcript,
    wiring::{evaluate_shift, RightIndex}, work_tree_history_plan::WorkTreeHistoryPlan};

pub(crate) const BASE: usize = 999424;
const ANCHOR: usize = 356632;
const HEADER_ROWS: usize = 1 << 19;
const RULE: &[u8] = b"retained-header-weighted673-max-v1;active-work-owner=[0,n-1);header-row-log19;max-row-log11";

pub(crate) struct MaxHeaderAdapter<'a> {
    parent: &'a WorkTreeHistoryPlan,
    roster: DaaHistoryRoster<'a>,
    max: Layout,
    anchor_hash: String,
    binding: [u8; 32],
}
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Counts {
    pub(crate) parent: HeaderCounts,
    pub(crate) emitted: usize,
    pub(crate) omitted_max: usize,
}

fn eq(p: &[Fr], index: usize) -> Fr {
    p.iter().enumerate().fold(Fr::one(), |a, (bit, x)| a *
        if index & (1 << bit) == 0 { Fr::one() - x } else { *x })
}
fn certify(terms: &[Term]) -> Result<String, String> {
    let mut anchors = Vec::with_capacity(suffix_max::HELPERS);
    for term in terms.iter().filter(|t| (ANCHOR..ANCHOR + suffix_max::HELPERS).contains(&t.row)) {
        let offset = term.row - ANCHOR;
        let g = &term.gate;
        if g.left != BASE + offset || g.right != 0 ||
            [g.c0, g.c1, g.c2, g.c3] != [Fr::zero(), Fr::one(), Fr::zero(), Fr::zero()] {
            return Err("MAX canonical anchor identity".into());
        }
        anchors.push(term.clone());
    }
    anchors.sort_unstable_by_key(|t| t.row);
    if anchors.len() != suffix_max::HELPERS || anchors.iter().enumerate().any(|(i,t)| t.row != ANCHOR+i) {
        return Err("MAX missing or duplicate canonical anchor".into());
    }
    Ok(crate::work_tree_layout::hash_terms(&anchors))
}
impl<'a> MaxHeaderAdapter<'a> {
    pub(crate) fn compile(parent: &'a WorkTreeHistoryPlan) -> Result<Self, String> {
        Self::diagnostic_domain(parent)?;
        Self::with_layout(parent, Layout::new(parent.headers() as usize, parent.slots(), BASE)?)
    }
    fn diagnostic_domain(parent: &WorkTreeHistoryPlan) -> Result<(),String> {
        if parent.headers() != 3 || parent.slots() != 4 || parent.slot_log() != 2 {
            return Err("MAX adapter diagnostic admission requires N3/C4/S2".into());
        }
        Ok(())
    }
    fn with_layout(parent: &'a WorkTreeHistoryPlan, max: Layout) -> Result<Self, String> {
        Self::diagnostic_domain(parent)?;
        let n = parent.headers() as usize;
        let source = parent.header_boundary().canonical_circuit();
        let endpoints = &crate::work_tree_layout::shared_baseline()?.endpoints;
        if n < 3 || max.n() != n || max.c() != parent.slots() || max.base() != BASE ||
            parent.slots() != 1usize << parent.slot_log() ||
            parent.descriptor().genuine != n - 1 || source.input_len != suffix_max::WIDTH ||
            source.row_count != HEADER_ROWS ||
            endpoints.work != (suffix_max::D_BASE..suffix_max::D_BASE+suffix_max::BITS).collect::<Vec<_>>() ||
            max.input_log() != 20 + parent.slot_log() || max.row_log() != 11 + parent.slot_log() {
            return Err("MAX parent/descriptor/endpoint geometry mismatch".into());
        }
        let anchor_hash = certify(&source.terms)?;
        let roster = DaaHistoryRoster::compile(parent)?;
        let mut result = Self {parent, roster, max, anchor_hash, binding: [0;32]};
        let mut transcript = Transcript::new(b"max-header-adapter-binding");
        result.bind(&mut transcript);
        let mut bytes = Vec::new();
        transcript.challenge_scalar(b"binding").serialize_compressed(&mut bytes)
            .map_err(|e| format!("MAX binding serialization: {e}"))?;
        result.binding.copy_from_slice(&bytes);
        Ok(result)
    }
    pub(crate) fn check_parent(&self, parent: &WorkTreeHistoryPlan) -> Result<(),String> {
        if !std::ptr::eq(self.parent, parent) {return Err("MAX adapter parent identity mismatch".into());}
        Ok(())
    }
    pub(crate) fn parent(&self) -> &'a WorkTreeHistoryPlan { self.parent }
    pub(crate) fn roster(&self) -> &DaaHistoryRoster<'a> { &self.roster }
    pub(crate) fn max(&self) -> &Layout { &self.max }
    pub(crate) fn binding(&self) -> [u8;32] { self.binding }
    pub(crate) fn bind(&self, t: &mut Transcript) {
        self.roster.bind(t);
        self.max.bind(t);
        t.append_bytes(b"max-header-rule", RULE);
        t.append_bytes(b"max-header-anchor-identity", self.anchor_hash.as_bytes());
        for (label, value) in [(b"max-header-anchor-start".as_slice(), ANCHOR),
            (b"max-header-anchor-count", suffix_max::HELPERS),
            (b"max-header-row-width", HEADER_ROWS), (b"max-header-active-end", self.max.n()-1),
            (b"max-header-emitted-max-terms", self.max.term_count()),
            (b"max-header-max-rows", self.max.row_count()), (b"max-header-max-edges", self.max.edge_count())] {
            t.append_u64(label, value as u64);
        }
    }
    pub(crate) fn physical_assignment_replacement_mask(&self, owner: usize) -> Result<Vec<bool>,String> {
        let mut mask = self.parent.physical_assignment_replacement_mask(owner as u64)?;
        if mask[BASE..BASE+suffix_max::HELPERS].iter().any(|b| *b) {
            return Err("MAX helper overlaps parent permission".into());
        }
        if owner < self.max.n()-1 { mask[BASE..BASE+suffix_max::HELPERS].fill(true); }
        Ok(mask)
    }
    pub(crate) fn visit_header_terms(&self, owner: usize, mut sink: impl FnMut(Term)->Result<(),String>) -> Result<Counts,String> {
        if owner >= self.max.c() {return Err("MAX header owner outside domain".into());}
        let active = owner < self.max.n()-1;
        let mut seen = vec![false; suffix_max::HELPERS];
        let mut removed = 0;
        let counts = self.roster.visit_header_terms(owner as u64, |term| {
            let local = term.row.checked_sub(owner*HEADER_ROWS).ok_or("MAX header row precedes owner")?;
            if (ANCHOR..ANCHOR+suffix_max::HELPERS).contains(&local) {
                let i = local-ANCHOR;
                let g = &term.gate;
                if seen[i] || g.left != owner*suffix_max::WIDTH+BASE+i || g.right != owner*suffix_max::WIDTH ||
                    [g.c0,g.c1,g.c2,g.c3] != [Fr::zero(),Fr::one(),Fr::zero(),Fr::zero()] {
                    return Err("MAX translated anchor identity".into());
                }
                seen[i] = true;
                if active {removed += 1; return Ok(());}
            }
            sink(term)
        })?;
        if seen.iter().any(|v| !*v) || removed != if active {suffix_max::HELPERS} else {0} {
            return Err("MAX header visitor census mismatch".into());
        }
        Ok(Counts {emitted:counts.emitted-removed,parent:counts,omitted_max:removed})
    }
    pub(crate) fn header_coefficients(&self, r:&[Fr], u:&[Fr], v:&[Fr]) -> Result<[Fr;4],String> {
        let mut out = self.roster.header_coefficients(r,u,v)?;
        let selector = evaluate_shift(&r[19..],&u[20..],&v[20..],0,0,(self.max.n()-1) as u64,0,RightIndex::SameRow)?;
        let mut local = Fr::zero();
        for bit in 0..suffix_max::HELPERS { local += eq(&r[..19],ANCHOR+bit)*eq(&u[..20],BASE+bit)*eq(&v[..20],0); }
        out[1] -= selector*local;
        Ok(out)
    }
    /// Only immutable native input exports supply D. No helper/mask/D callback is accepted.
    pub(crate) fn helpers(&self, input:&NativePrefix, owner:usize) -> Result<Vec<Fr>,String> {
        validate_native_plan_input(self.parent,input)?;
        if owner >= self.max.c() {return Err("MAX helper owner outside domain".into());}
        let mut out = vec![Fr::zero();suffix_max::HELPERS];
        if owner >= self.max.n()-1 { return Ok(out); }
        let exports = NativeExports::new_for_history(self.parent,input)?;
        let mut next = BigUint::from(0u8);
        let mut current = BigUint::from(0u8);
        for work_owner in owner..self.max.n()-1 {
            let mut d = BigUint::from(0u8);
            for bit in 0..suffix_max::BITS {
                if exports.bit(work_owner*suffix_max::WIDTH+suffix_max::D_BASE+bit)? {d += BigUint::from(1u8)<<bit;}
            }
            if work_owner == owner {current = d;} else {next = next.max(d);}
        }
        let selected = current.clone().max(next.clone());
        let selector = current < next;
        let delta = &current + (BigUint::from(selector as u8)<<224usize) - &next;
        for (offset,value) in [(0,selected),(224,next),(448,delta)] {
            for bit in 0..224 {out[offset+bit] = Fr::from(value.bit(bit as u64) as u64);}
        }
        out[672] = Fr::from(selector as u64);
        Ok(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{gkr::Gate, work_tree_history_plan::WorkTreeHistoryPlan};
    fn anchors()->Vec<Term> {(0..673).map(|i|Term{row:ANCHOR+i,gate:Gate{left:BASE+i,right:0,c0:Fr::zero(),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()}}).collect()}
    #[test]
    fn isolated_anchor_identity_faults() {
        let terms=anchors(); assert!(certify(&terms).is_ok());
        for field in 0..6 {let mut t=terms.clone();let g=&mut t[1].gate;
            match field {0=>g.left+=1,1=>g.right=1,2=>g.c0=Fr::one(),3=>g.c1=Fr::zero(),4=>g.c2=Fr::one(),_=>g.c3=Fr::one()}
            assert!(certify(&t).is_err(),"field{field}");}
        let mut missing=terms.clone();missing.remove(1);assert!(certify(&missing).is_err());
        let mut duplicate=terms.clone();duplicate.push(terms[1].clone());assert!(certify(&duplicate).is_err());
        let mut replaced=terms.clone();replaced[1]=terms[0].clone();assert!(certify(&replaced).is_err());
    }
    #[test]
    fn n3_adapter_permissions_visitor_and_analytic_delta() {
        let plan=WorkTreeHistoryPlan::compile(3,2,[7;32],[0x35;28]).unwrap();
        let a=MaxHeaderAdapter::compile(&plan).unwrap();
        let different=WorkTreeHistoryPlan::compile(3,2,[8;32],[0x35;28]).unwrap();
        assert!(a.check_parent(&different).is_err());
        let n4=WorkTreeHistoryPlan::compile(4,2,[7;32],[0x35;28]).unwrap();
        assert!(MaxHeaderAdapter::compile(&n4).err().unwrap().contains("diagnostic admission"));
        for bad in [Layout::new(3,4,BASE+1).unwrap(),Layout::new(4,4,BASE).unwrap()] {assert!(MaxHeaderAdapter::with_layout(&plan,bad).is_err());}
        let r=(0..21).map(|i|Fr::from((3*i+2) as u64)).collect::<Vec<_>>();
        let u=(0..22).map(|i|Fr::from((5*i+7) as u64)).collect::<Vec<_>>();
        let v=(0..22).map(|i|Fr::from((7*i+11) as u64)).collect::<Vec<_>>();
        let mut direct=Fr::zero();
        for owner in 0..4 {
            let parent_mask=plan.physical_assignment_replacement_mask(owner as u64).unwrap();
            let mask=a.physical_assignment_replacement_mask(owner).unwrap();
            for wire in 0..suffix_max::WIDTH {assert_eq!(mask[wire],parent_mask[wire] || (owner<2 && (BASE..BASE+673).contains(&wire)));}
            assert!(!mask[BASE-1]);assert!(!mask[BASE+673]);
            let mut parent=Vec::new();a.roster.visit_header_terms(owner as u64,|t|{parent.push(t);Ok(())}).unwrap();
            let mut actual=Vec::new();let counts=a.visit_header_terms(owner,|t|{actual.push(t);Ok(())}).unwrap();
            assert_eq!(counts.omitted_max,if owner<2 {673}else{0});
            let expected=parent.iter().filter(|t|owner>=2 || !(owner*HEADER_ROWS+ANCHOR..owner*HEADER_ROWS+ANCHOR+673).contains(&t.row)).cloned().collect::<Vec<_>>();
            assert_eq!(actual,expected);
            for t in parent.iter().filter(|t|owner<2 && (owner*HEADER_ROWS+ANCHOR..owner*HEADER_ROWS+ANCHOR+673).contains(&t.row)) {
                assert_eq!(t.gate.right,owner*suffix_max::WIDTH);
                direct+=eq(&r,t.row)*eq(&u,t.gate.left)*eq(&v,t.gate.right);
            }
            a.max.emit_owner(owner,|t|{if owner>=2 && t.row%2048<673 {assert_eq!(t.gate.right,owner*suffix_max::WIDTH);}Ok(())}).unwrap();
        }
        let parent=a.roster.header_coefficients(&r,&u,&v).unwrap();
        let actual=a.header_coefficients(&r,&u,&v).unwrap();
        assert_eq!(actual,[parent[0],parent[1]-direct,parent[2],parent[3]]);
        assert!(a.physical_assignment_replacement_mask(4).is_err());
    }
}

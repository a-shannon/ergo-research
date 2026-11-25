//! Remaining complete H21 role producers for the shared full-X pipeline.
//! These return unverified GKR bytes, never PCS or history authority.
use super::*;
pub(crate) use crate::sparse_stream_roster::{H21CandidateRole,H21CandidateBudget,H21CandidateShape};
use crate::sparse_stream_roster::{self as edge,EdgeTerm};

pub(super) fn h21_point_scratch(budget:H21CandidateBudget)->Result<usize,String>{
    if budget.caller_context_bytes==0 || budget.visitor_scratch_bytes==0 || budget.unmeasured_bytes==0 {
        return Err("invalid grouped POINT resource reservations".into());
    }
    let scratch=budget.limit_bytes.checked_sub(budget.caller_context_bytes)
        .and_then(|n|n.checked_sub(budget.visitor_scratch_bytes))
        .and_then(|n|n.checked_sub(budget.unmeasured_bytes)).ok_or("insufficient grouped POINT budget")?;
    crate::sparse_stream_boolean::point_grouped_producer::check_resources(21,scratch)?;
    Ok(scratch)
}

fn canonical_edge(shape:&H21CandidateShape,term:Term)->Result<EdgeTerm,String>{
    let (source_slot,family_row)=shape.edge_metadata(term.row)?;
    let result=EdgeTerm {source_slot,family_row,term};shape.check_edge(&result)?;Ok(result)
}
fn admit_remaining_public_inputs(requested:&[u8],expected:&[u8],key_bytes:&[u8],commitment:&[u8])
    ->Result<verifier_key::AdmittedVerifierKey,String>{
    with_matching_h21_requested_identity(requested,expected,|| {
        let key=verifier_key::admit(41,key_bytes)?;require_h21_role0_diagnostic_key(&key)?;
        let c=pcs::decode_commitment(commitment)?;
        if pcs::encode_commitment(&c)?!=commitment{return Err("H21 candidate noncanonical C".into());}
        Ok(key)
    })
}
impl H21StructuralDiagnosticContext<'_> {
    pub(crate) fn candidate_role_shape(&self,role:H21CandidateRole)->Result<H21CandidateShape,String>{
        let shape=H21CandidateShape::for_parent(role,self.layouts.parent)?;
        let index=role.index();
        if self.geometry.input_bits[index]!=shape.input_log()||self.geometry.row_bits[index]!=shape.row_log() {
            return Err("H21 candidate geometry differs from canonical consumer".into());
        }
        if role==H21CandidateRole::Point {
            let c=&self.layouts.points.circuit;
            if c.input_len!=8192||c.row_count!=16384||c.terms.len()!=288_158 {
                return Err("H21 POINT canonical local circuit".into());
            }
            H21CandidateShape::physical_point_row((1<<21)-1)?;
        }
        if role==H21CandidateRole::HeightDaa {
            self.height.check_history_endpoint_scope()?;
            if !std::ptr::eq(self.height.endpoint_parent(),self.layouts.parent)
                ||!std::ptr::eq(self.roster.daa().endpoint_parent(),self.layouts.parent)
                ||self.height.row_log()!=27||self.roster.daa().row_log()!=40 {
                return Err("H21 height/DAA canonical parent and row allocation".into());
            }
        }
        Ok(shape)
    }

    pub(crate) fn visit_remaining_endpoint(&self,shape:&H21CandidateShape,left:bool,owner:usize,
        sink:&mut dyn FnMut(EdgeTerm)->Result<(),String>)->Result<(),String>{
        self.visit_remaining_selected_endpoint(shape,left,owner,false,sink)
    }

    pub(crate) fn visit_remaining_physical_endpoint(&self,shape:&H21CandidateShape,left:bool,owner:usize,
        sink:&mut dyn FnMut(EdgeTerm)->Result<(),String>)->Result<(),String>{
        self.visit_remaining_selected_endpoint(shape,left,owner,true,sink)
    }

    fn visit_remaining_selected_endpoint(&self,shape:&H21CandidateShape,left:bool,owner:usize,contract_zero:bool,
        sink:&mut dyn FnMut(EdgeTerm)->Result<(),String>)->Result<(),String>{
        if owner>=1<<21{return Err("H21 candidate endpoint owner".into());}
        match shape.role() {
            H21CandidateRole::Tree=>work_tree_wiring::h21_full_roster_endpoint(
                self.layouts.parent.topology(),fixed::engine()?,self.layouts.parent.fixed_profile(),
                self.layouts.parent.leaf_boundary(),self.layouts.parent.work_boundary(),left,owner,sink),
            H21CandidateRole::Point=>{
                let row_base=owner.checked_mul(1<<14).ok_or("H21 POINT row overflow")?;
                let input_base=owner.checked_mul(8192).ok_or("H21 POINT input overflow")?;
                for base in &self.layouts.points.circuit.terms {
                    let mut term=base.clone();
                    term.row=term.row.checked_add(row_base).ok_or("H21 POINT row translation")?;
                    term.gate.left=term.gate.left.checked_add(input_base).ok_or("H21 POINT left translation")?;
                    term.gate.right=term.gate.right.checked_add(input_base).ok_or("H21 POINT right translation")?;
                    let endpoint=if left{term.gate.left}else{term.gate.right};
                    if endpoint/8192!=owner{return Err("H21 POINT source is not owner-local".into());}
                    sink(canonical_edge(shape,term)?)?;
                }
                Ok(())
            },
            H21CandidateRole::HeightDaa=>{
                // HeightWork's already-tagged 27-bit namespace stays intact
                // in member0, zero-extended to the DAA 40-bit namespace.
                self.height.visit_history_endpoint_terms(left,owner,|term| {
                    if term.row>=1usize<<27{return Err("H21 height ROW extent".into());}
                    sink(canonical_edge(shape,term)?)
                })?;
                let append=|mut term:Term| {
                    if term.row>=1usize<<40{return Err("H21 DAA ROW extent".into());}
                    term.row=term.row.checked_add(1usize<<40).ok_or("H21 DAA composite ROW overflow")?;
                    sink(canonical_edge(shape,term)?)
                };
                if contract_zero{self.roster.daa().visit_h21_endpoint_without_zero(left,owner,append)?;}
                else{self.roster.daa().visit_history_endpoint_terms(left,owner,append)?;}
                Ok(())
            },
            H21CandidateRole::Metadata=>self.layouts.metadata.visit_h21_endpoint(left,owner,sink),
        }
    }

    /// The only outward producer seam accepts a sealed role and the same
    /// held full-log41 witness. Public identity/key/C are checked before any
    /// source read or census. Root re-derives claims from the exported bytes.
    pub(crate) fn prove_remaining_untrusted_candidate(&self,role:H21CandidateRole,key_bytes:&[u8],
        commitment:&[u8],candidate:&packed::UntrustedH21CandidateFile,budget:H21CandidateBudget)
        ->Result<(Vec<u8>,InputClaim),String>{
        let key=admit_remaining_public_inputs(candidate.requested_logical_public_identity(),self.native_witness_identity,key_bytes,commitment)?;
        let shape=self.candidate_role_shape(role)?;
        let index=role.index();
        let mut t=fresh_h21_role_prefix(self.public_bytes,&key,commitment,index)?;
        let (proof,claim) = if role == H21CandidateRole::Point {
            let source = candidate.untrusted_polynomial();
            if source.input_len()!=1usize<<41{return Err("invalid grouped POINT source".into());}
            let scratch=h21_point_scratch(budget)?;
            bind_h21_role(self, index, &mut t)?;
            if t.challenges() != 0 || t.raw_queries() != 0 { return Err("unexpected POINT challenge".into()); }
            crate::sparse_stream_boolean::point_grouped_producer::prove(
                &self.layouts.points.circuit, 21, scratch,
                |owner| source.read_row_bits(8192, H21CandidateShape::physical_point_row(owner)?), &mut t)?
        } else {
            let daa=(role==H21CandidateRole::HeightDaa).then_some(self.roster.daa());
            let (proof,claim,_) = edge::prove_h21_candidate(&shape,candidate,budget,&mut t,daa,
                |left,owner,sink|self.visit_remaining_physical_endpoint(&shape,left,owner,sink),
                |t|bind_h21_role(self,index,t),|r,u,v|self.coefficients(index,r,u,v))?;
            (proof,claim)
        };
        let bytes=gkr::encode_proof(&proof)?;
        let expected=if role==H21CandidateRole::Point {7_712}else{9_280};
        if bytes.len()!=expected||claim.point.len()!=shape.input_log(){return Err("H21 candidate role proof extent".into());}
        let projected=if role==H21CandidateRole::Point {InputClaim {point:self.point_role.project(&claim.point)?,value:claim.value}}else{claim};
        if projected.point.len()!=41{return Err("H21 candidate common input claim extent".into());}
        Ok((bytes,projected))
    }
}

#[path="h21_candidate_roles_tests.rs"]
mod tests;

#[path="point_grouped_native_tests.rs"]
mod grouped_native_tests;

//! Bounded test producer for a replayable sparse-term source.
//!
//! This preserves the one-layer sparse GKR transcript while asking the caller
//! to regenerate terms for each phase instead of retaining one global
//! `Vec<Term>`. Input/coefficient vectors remain global; this module makes no
//! historical-memory or streaming-I/O claim.
use ark_bn254::Fr;
use ark_ff::Zero;
use crate::{gkr::{self,GkrError,GkrProof,InputClaim,LayerProof},sparse::{self,Circuit,Term},transcript::Transcript};

pub(crate) fn prove_with_term_source(
    input_len:usize,row_count:usize,expected_terms:usize,input:&[Fr],transcript:&mut Transcript,
    bind:impl FnOnce(&mut Transcript),
    mut visit_terms:impl FnMut(&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String>,
    wiring:impl Fn(&[Fr],&[Fr],&[Fr])->Result<[Fr;4],String>,
)->Result<(GkrProof,InputClaim),String>{
    let shape=sparse::validate(&Circuit{input_len,row_count,terms:Vec::new()},0).map_err(|e|e.to_string())?;
    if input.len()!=shape.input_len{return Err(GkrError::InvalidInputWidth.to_string());}
    let mut residuals=vec![Fr::zero();row_count];let mut seen=0usize;
    visit_terms(&mut |term|{
        seen=seen.checked_add(1).ok_or("term count overflow")?;
        if seen>expected_terms{return Err("term source exceeded expected count".into());}
        if term.row>=row_count||term.gate.left>=input_len||term.gate.right>=input_len{return Err(GkrError::InvalidWireIndex.to_string());}
        residuals[term.row]+=term.gate.evaluate(input);Ok(())
    })?;
    if seen!=expected_terms{return Err("term source count mismatch in residual pass".into());}
    if residuals.iter().any(|value|!value.is_zero()){return Err(GkrError::NonzeroOutput.to_string());}
    drop(residuals);bind(transcript);
    let output_point=gkr::output_point(shape.row_count,transcript);
    gkr::append_usize(transcript,b"gkr-layer-index",0);
    let row_weights=gkr::eq_weights(&output_point[..shape.row_bits]);
    let mut claim=Fr::zero();let mut a=vec![Fr::zero();input_len];let mut b=vec![Fr::zero();input_len];
    seen=0;visit_terms(&mut |term|{
        seen=seen.checked_add(1).ok_or("term count overflow")?;
        if seen>expected_terms{return Err("term source exceeded expected count".into());}
        if term.row>=row_count||term.gate.left>=input_len||term.gate.right>=input_len{return Err(GkrError::InvalidWireIndex.to_string());}
        let gate=&term.gate;let weight=row_weights[term.row];let right=input[gate.right];
        a[gate.left]+=weight*(gate.c1+gate.c3*right);b[gate.left]+=weight*(gate.c0+gate.c2*right);Ok(())
    })?;
    if seen!=expected_terms{return Err("term source count mismatch in left-coefficient pass".into());}
    let mut rounds=Vec::new();drop(row_weights);
    let (u,left_value)=gkr::prove_phase(a,b,input,&mut claim,&mut rounds,transcript).map_err(|e|e.to_string())?;
    let row_weights=gkr::eq_weights(&output_point[..shape.row_bits]);let left_weights=gkr::eq_weights(&u);
    let mut c=vec![Fr::zero();input_len];let mut d=vec![Fr::zero();input_len];
    seen=0;visit_terms(&mut |term|{
        seen=seen.checked_add(1).ok_or("term count overflow")?;
        if seen>expected_terms{return Err("term source exceeded expected count".into());}
        if term.row>=row_count||term.gate.left>=input_len||term.gate.right>=input_len{return Err(GkrError::InvalidWireIndex.to_string());}
        let gate=&term.gate;let weight=row_weights[term.row]*left_weights[gate.left];
        c[gate.right]+=weight*(gate.c2+gate.c3*left_value);d[gate.right]+=weight*(gate.c0+gate.c1*left_value);Ok(())
    })?;
    if seen!=expected_terms{return Err("term source count mismatch in right-coefficient pass".into());}
    let (v,right_value)=gkr::prove_phase(c,d,input,&mut claim,&mut rounds,transcript).map_err(|e|e.to_string())?;
    let coefficients=wiring(&output_point,&u,&v)?;
    if coefficients[0]+coefficients[1]*left_value+coefficients[2]*right_value
        +coefficients[3]*left_value*right_value!=claim{return Err(GkrError::TerminalExpression.to_string());}
    let line_coefficients=gkr::line_polynomial(input,&u,&v);
    transcript.append_scalar(b"gkr-left-value",&left_value);transcript.append_scalar(b"gkr-right-value",&right_value);
    gkr::append_polynomial(transcript,b"gkr-line-polynomial",&line_coefficients);
    let challenge=transcript.challenge_scalar(b"gkr-line-challenge");
    let point=gkr::line_point(&u,&v,challenge);let value=gkr::eval_polynomial(&line_coefficients,challenge);
    Ok((GkrProof{layers:vec![LayerProof{rounds,left_value,right_value,line_coefficients}]},InputClaim{point,value}))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gkr::Gate;

    #[test]
    fn rejects_term_source_count_drift() {
        for (expected, emitted) in [(1usize, 0usize), (0, 1)] {
            let terms = vec![Term { row: 0, gate: Gate {
                left: 0, right: 0, c0: Fr::zero(), c1: Fr::zero(),
                c2: Fr::zero(), c3: Fr::zero(),
            }}; emitted];
            let mut transcript = Transcript::new(b"term-count-negative-test");
            let result = prove_with_term_source(1, 1, expected, &[Fr::zero()], &mut transcript,
                |_| {}, |visitor| { for term in &terms { visitor(term.clone())?; } Ok(()) },
                |_, _, _| Ok([Fr::zero(); 4]));
            assert!(result.is_err(), "expected {expected} terms but emitted {emitted}");
        }
    }
}

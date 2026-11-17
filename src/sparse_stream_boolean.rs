//! Boolean-source optimization of the unchanged sparse streaming proof.
//!
//! The callback must read the same immutable snapshot used for PCS commitment
//! and opening. Every read checks every coordinate, including unused ones, for
//! Boolean values. These checks do not detect arbitrary Boolean-to-Boolean
//! changes by a mutable callback. PackedFile supplies the existing locked-file
//! snapshot boundary; this module neither changes nor replaces that boundary.
//!
//! Copy coordinates remain high bits. There are b+5 complete copy passes:
//! validation, b+1 first-phase passes, two second-phase passes, and one line
//! pass. Width one intentionally retains all five passes. No full-history field
//! table is allocated; scratch space is O(base width + rows + terms + copies).
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use crate::{gkr::{self, GkrError, GkrProof, InputClaim, LayerProof},
    point_membership, sparse::{self, Circuit}, transcript::Transcript};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    Gkr(GkrError),
    NonBoolean { copy: usize, index: usize },
}

impl From<GkrError> for Error {
    fn from(error: GkrError) -> Self { Self::Gkr(error) }
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Gkr(error) => write!(f,"{error}"),
            Self::NonBoolean {copy,index} => write!(f,"non-Boolean input at copy {copy}, coordinate {index}"),
        }
    }
}
impl std::error::Error for Error {}

fn read_copy(load: &mut impl FnMut(usize)->Result<Vec<Fr>,GkrError>, copy: usize, width: usize)
    -> Result<Vec<Fr>,Error>
{
    let input=load(copy)?;
    if input.len()!=width { return Err(GkrError::InvalidInputWidth.into()); }
    if let Some(index)=input.iter().position(|x|!x.is_zero() && !x.is_one()) {
        return Err(Error::NonBoolean {copy,index});
    }
    Ok(input)
}

fn eq_index(point:&[Fr], index:usize)->Fr {
    point.iter().enumerate().fold(Fr::one(),|acc,(bit,x)| {
        acc * if (index>>bit)&1==1 {*x} else {Fr::one()-x}
    })
}

fn send_round(polynomial:Vec<Fr>, claim:&mut Fr, rounds:&mut Vec<Vec<Fr>>, transcript:&mut Transcript)
    -> Result<Fr,Error>
{
    if polynomial[0]+gkr::eval_polynomial(&polynomial,Fr::one())!=*claim {
        return Err(GkrError::SumcheckIdentity.into());
    }
    gkr::append_polynomial(transcript,b"gkr-sumcheck-polynomial",&polynomial);
    let challenge=transcript.challenge_scalar(b"gkr-sumcheck-challenge");
    *claim=gkr::eval_polynomial(&polynomial,challenge);
    rounds.push(polynomial); Ok(challenge)
}

fn finish_high(mut a:Vec<Fr>,mut b:Vec<Fr>,mut x:Vec<Fr>,point:&mut Vec<Fr>,
    claim:&mut Fr,rounds:&mut Vec<Vec<Fr>>,transcript:&mut Transcript)->Result<Fr,Error>
{
    while x.len()>1 {
        let polynomial=gkr::quadratic_message(&a,&b,&x);
        let challenge=send_round(polynomial,claim,rounds,transcript)?;
        gkr::fold(&mut a,challenge);gkr::fold(&mut b,challenge);gkr::fold(&mut x,challenge);
        point.push(challenge);
    }
    Ok(x[0])
}

struct Edge { left:usize, right:usize, coefficient:Fr }
// Only constructed behind validate_h21_point_window's exact circuit equality.
// The square and x*u rows are the fixed point-membership emitter's c3 terms.
struct PointFactor {
    layout:point_membership::Layout,
    row_weights:[[[Fr;7];3];2],
    powers:[Fr;64],
    low_weights:Vec<Fr>,
}
impl PointFactor {
    fn new(layout:point_membership::Layout,rows:&[Fr])->Self {
        let row_weights=std::array::from_fn(|point|std::array::from_fn(|identity| {
            std::array::from_fn(|limb|rows[layout.points[point].rows.arithmetic[identity].start+limb])
        }));
        let mut powers=[Fr::one();64];
        for i in 1..64 {powers[i]=powers[i-1]+powers[i-1];}
        Self {layout,row_weights,powers,low_weights:vec![Fr::one()]}
    }
    fn bind_low(&mut self,challenge:Fr) {
        let old=self.low_weights.len();self.low_weights.resize(2*old,Fr::zero());
        for i in 0..old {
            let weight=self.low_weights[i];
            self.low_weights[i]=weight*(Fr::one()-challenge);
            self.low_weights[i+old]=weight*challenge;
        }
    }
    fn add(&self,a:&mut[Fr],wire:usize,value:Fr) {
        let mask=self.low_weights.len()-1;
        let shift=self.low_weights.len().trailing_zeros() as usize;
        a[wire>>shift]+=self.low_weights[wire&mask]*value;
    }
    fn limbs(&self,input:&[Fr],wires:&[usize;256])->[Fr;4] {
        let mut sums=[Fr::zero();4];
        for i in 0..256 {if input[wires[i]].is_one() {sums[i/64]+=self.powers[i%64];}}
        sums
    }
    fn add_square(&self,a:&mut[Fr],input:&[Fr],wires:&[usize;256],rho:&[Fr;7]) {
        let limbs=self.limbs(input,wires);
        let mut higher=[Fr::zero();4];
        for limb in 0..4 {for above in limb+1..4 {higher[limb]+=rho[limb+above]*limbs[above];}}
        let mut tail=[Fr::zero();4];
        let two=Fr::from(2u64);
        for i in (0..256).rev() {
            let limb=i/64;let power=self.powers[i%64];
            let self_bit=if input[wires[i]].is_one() {power} else {Fr::zero()};
            let value=power*(rho[2*limb]*(self_bit+two*tail[limb])+two*higher[limb]);
            self.add(a,wires[i],value);
            tail[limb]+=self_bit;
        }
    }
    fn add_cross(&self,a:&mut[Fr],input:&[Fr],x:&[usize;256],u:&[usize;256],rho:&[Fr;7]) {
        let limbs=self.limbs(input,u);
        let mut mixed=[Fr::zero();4];
        for limb in 0..4 {for other in 0..4 {mixed[limb]+=rho[limb+other]*limbs[other];}}
        for i in 0..256 {self.add(a,x[i],self.powers[i%64]*mixed[i/64]);}
    }
    fn add_arithmetic(&self,a:&mut[Fr],input:&[Fr]) {
        for point in 0..2 {
            let p=&self.layout.points[point];let rho=&self.row_weights[point];
            self.add_square(a,input,p.x.as_ref(),&rho[0]);
            self.add_square(a,input,p.y.as_ref(),&rho[1]);
            self.add_cross(a,input,p.x.as_ref(),p.u.as_ref(),&rho[2]);
        }
    }
}
struct FirstPhase {
    a_constant:Vec<Fr>, b_constant:Vec<Fr>, a_edges:Vec<Edge>, b_edges:Vec<Edge>,
    point:Option<PointFactor>,
}

impl FirstPhase {
    fn new(circuit:&Circuit,rows:&[Fr])->Self {Self::new_with_point(circuit,rows,None)}
    // This private constructor is used only after exact canonical admission.
    fn new_point(circuit:&Circuit,rows:&[Fr])->Self {
        // emit fills the arithmetic row ranges; the bare layout allocator leaves
        // them empty. The sink discards terms, so no second circuit is allocated.
        let (layout,_)=point_membership::emit::<Fr>(|_,_,_,_|{})
            .expect("canonical point emitter must support Fr");
        Self::new_with_point(circuit,rows,Some(layout))
    }
    fn new_with_point(circuit:&Circuit,rows:&[Fr],layout:Option<point_membership::Layout>)->Self {
        let mut factorized_rows=vec![false;circuit.row_count];
        if let Some(layout)=&layout {for point in &layout.points {for range in &point.rows.arithmetic {
            factorized_rows[range.clone()].fill(true);
        }}}
        let mut result=Self {a_constant:vec![Fr::zero();circuit.input_len],
            b_constant:vec![Fr::zero();circuit.input_len],a_edges:Vec::new(),b_edges:Vec::new(),
            point:layout.map(|layout|PointFactor::new(layout,rows))};
        for term in &circuit.terms {
            let g=&term.gate;let rho=rows[term.row];
            if !g.c1.is_zero() {result.a_constant[g.left]+=rho*g.c1;}
            if !g.c0.is_zero() {result.b_constant[g.left]+=rho*g.c0;}
            if !g.c3.is_zero() && !factorized_rows[term.row] {
                result.a_edges.push(Edge {left:g.left,right:g.right,coefficient:rho*g.c3});
            }
            if !g.c2.is_zero() {result.b_edges.push(Edge {left:g.left,right:g.right,coefficient:rho*g.c2});}
        }
        result
    }
    // Only called after read_copy validated the entire input as Boolean.
    fn vectors(&self,input:&[Fr])->(Vec<Fr>,Vec<Fr>) {
        let mut a=self.a_constant.clone();let mut b=self.b_constant.clone();
        for edge in &self.a_edges {if input[edge.right].is_one() {a[edge.left]+=edge.coefficient;}}
        for edge in &self.b_edges {if input[edge.right].is_one() {b[edge.left]+=edge.coefficient;}}
        if let Some(point)=&self.point {point.add_arithmetic(&mut a,input);}
        (a,b)
    }
    // Bind the next low LEFT coordinate once for every copy. Right indices
    // still address the raw Boolean witness; they must never be folded here.
    fn bind_low(&mut self,challenge:Fr) {
        gkr::fold(&mut self.a_constant,challenge);
        gkr::fold(&mut self.b_constant,challenge);
        let complement=Fr::one()-challenge;
        for edge in self.a_edges.iter_mut().chain(&mut self.b_edges) {
            edge.coefficient*=if edge.left&1==1 {challenge} else {complement};
            edge.left>>=1;
        }
        if let Some(point)=&mut self.point {point.bind_low(challenge);}
    }
}

fn first_phase(circuit:&Circuit,shape:&sparse::Shape,
    load:&mut impl FnMut(usize)->Result<Vec<Fr>,GkrError>,rows:&[Fr],omega:&[Fr],
    point_factorized:bool,claim:&mut Fr,rounds:&mut Vec<Vec<Fr>>,transcript:&mut Transcript)
    ->Result<(Vec<Fr>,Fr),Error>
{
    let mut tables=if point_factorized {FirstPhase::new_point(circuit,rows)}
        else {FirstPhase::new(circuit,rows)};
    let mut point=Vec::with_capacity(shape.input_bits+shape.copies.trailing_zeros() as usize);
    for _ in 0..shape.input_bits {
        let mut polynomial=vec![Fr::zero();3];
        for copy in 0..shape.copies {
            let mut x=read_copy(load,copy,circuit.input_len)?;
            let (a,b)=tables.vectors(&x);
            for coordinate in &point {gkr::fold(&mut x,*coordinate);}
            for (sum,coefficient) in polynomial.iter_mut().zip(gkr::quadratic_message(&a,&b,&x)) {
                *sum+=omega[copy]*coefficient;
            }
        }
        let challenge=send_round(polynomial,claim,rounds,transcript)?;
        tables.bind_low(challenge);
        point.push(challenge);
    }
    let mut high_a=Vec::with_capacity(shape.copies);
    let mut high_b=Vec::with_capacity(shape.copies);
    let mut high_x=Vec::with_capacity(shape.copies);
    for copy in 0..shape.copies {
        let mut x=read_copy(load,copy,circuit.input_len)?;
        let (a,b)=tables.vectors(&x);
        for coordinate in &point {gkr::fold(&mut x,*coordinate);}
        high_a.push(omega[copy]*a[0]);high_b.push(omega[copy]*b[0]);high_x.push(x[0]);
    }
    // Free the term-weight tables before the second phase.
    drop(tables);
    let value=finish_high(high_a,high_b,high_x,&mut point,claim,rounds,transcript)?;
    Ok((point,value))
}

/// Quadratic message for A*X + sigma*D. D stays unscaled so its terminal
/// value remains available even when sigma=0. No division is used.
fn quadratic_scaled_d(a:&[Fr],d:&[Fr],x:&[Fr],sigma:Fr)->Vec<Fr> {
    let mut polynomial=vec![Fr::zero();3];
    let mut d_constant=Fr::zero();let mut d_linear=Fr::zero();
    for pair in 0..a.len()/2 {
        let lo=2*pair;let da=a[lo+1]-a[lo];let dx=x[lo+1]-x[lo];
        polynomial[0]+=a[lo]*x[lo];
        polynomial[1]+=a[lo]*dx+da*x[lo];
        polynomial[2]+=da*dx;
        d_constant+=d[lo];d_linear+=d[lo+1]-d[lo];
    }
    polynomial[0]+=sigma*d_constant;polynomial[1]+=sigma*d_linear;
    polynomial
}

fn second_phase(circuit:&Circuit,shape:&sparse::Shape,
    load:&mut impl FnMut(usize)->Result<Vec<Fr>,GkrError>,mut c:Vec<Fr>,mut d:Vec<Fr>,tau:&[Fr],
    claim:&mut Fr,rounds:&mut Vec<Vec<Fr>>,transcript:&mut Transcript)
    ->Result<(Vec<Fr>,Fr),Error>
{
    let sigma:Fr=tau.iter().copied().sum();
    let mut x_bar=vec![Fr::zero();circuit.input_len];
    for copy in 0..shape.copies {
        let input=read_copy(load,copy,circuit.input_len)?;
        for (out,bit) in x_bar.iter_mut().zip(input) {if bit.is_one() {*out+=tau[copy];}}
    }
    let mut point=Vec::with_capacity(shape.input_bits+shape.copies.trailing_zeros() as usize);
    for _ in 0..shape.input_bits {
        let polynomial=quadratic_scaled_d(&c,&d,&x_bar,sigma);
        let challenge=send_round(polynomial,claim,rounds,transcript)?;
        gkr::fold(&mut c,challenge);gkr::fold(&mut d,challenge);gkr::fold(&mut x_bar,challenge);
        point.push(challenge);
    }
    let c_value=c[0];let d_value=d[0];drop(c);drop(d);drop(x_bar);
    let mut high_a=Vec::with_capacity(shape.copies);
    let mut high_b=Vec::with_capacity(shape.copies);
    let mut high_x=Vec::with_capacity(shape.copies);
    for copy in 0..shape.copies {
        let mut input=read_copy(load,copy,circuit.input_len)?;
        for coordinate in &point {gkr::fold(&mut input,*coordinate);}
        high_a.push(tau[copy]*c_value);high_b.push(tau[copy]*d_value);high_x.push(input[0]);
    }
    let value=finish_high(high_a,high_b,high_x,&mut point,claim,rounds,transcript)?;
    Ok((point,value))
}

fn multiply_polynomials(a:&[Fr],b:&[Fr])->Vec<Fr> {
    let mut out=vec![Fr::zero();a.len()+b.len()-1];
    for (i,x) in a.iter().enumerate() {for (j,y) in b.iter().enumerate() {out[i+j]+=*x*y;}}
    out
}
fn copy_line_selector(copy:usize,u:&[Fr],v:&[Fr])->Vec<Fr> {
    let mut polynomial=vec![Fr::one()];
    for (bit,(a,b)) in u.iter().zip(v).enumerate() {
        let linear=if (copy>>bit)&1==1 {[*a,*b-a]} else {[Fr::one()-a,*a-b]};
        polynomial=multiply_polynomials(&polynomial,&linear);
    }
    polynomial
}

/// Same circuit/profile/transcript as sparse_stream::prove; only the producer
/// is specialized. Non-Boolean input is an error, never an implicit fallback.
pub fn prove(circuit:&Circuit,log_copies:usize,
    load_copy:impl FnMut(usize)->Result<Vec<Fr>,GkrError>,transcript:&mut Transcript)
    ->Result<(GkrProof,InputClaim),Error>
{
    let shape=sparse::validate(circuit,log_copies)?;
    prove_with_shape(circuit,log_copies,shape,false,load_copy,transcript)
}

/// Exact canonical point relation on one aligned 16-owner H21 window. This
/// does not admit the 2^21-copy role or a common-X/PCS proof.
pub(crate) fn prove_h21_point_window(circuit:&Circuit,
    load_copy:impl FnMut(usize)->Result<Vec<Fr>,GkrError>,transcript:&mut Transcript)
    ->Result<(GkrProof,InputClaim),Error>
{
    let shape=sparse::validate_h21_point_window(circuit)?;
    prove_with_shape(circuit,sparse::H21_POINT_WINDOW_LOG_COPIES,shape,true,load_copy,transcript)
}

fn prove_with_shape(circuit:&Circuit,log_copies:usize,shape:sparse::Shape,
    point_factorized:bool,mut load_copy:impl FnMut(usize)->Result<Vec<Fr>,GkrError>,transcript:&mut Transcript)
    ->Result<(GkrProof,InputClaim),Error>
{
    let mut residuals=vec![Fr::zero();circuit.row_count];
    for copy in 0..shape.copies {
        let input=read_copy(&mut load_copy,copy,circuit.input_len)?;
        residuals.fill(Fr::zero());
        for term in &circuit.terms {
            let g=&term.gate;let left=input[g.left].is_one();let right=input[g.right].is_one();
            let mut value=g.c0;
            if left {value+=g.c1;} if right {value+=g.c2;} if left && right {value+=g.c3;}
            residuals[term.row]+=value;
        }
        if residuals.iter().any(|x|!x.is_zero()) {return Err(GkrError::NonzeroOutput.into());}
    }
    drop(residuals);
    // No challenge or binding append precedes the complete Boolean/residual scan.
    sparse::bind(circuit,log_copies,transcript);
    let r=gkr::output_point(shape.row_count,transcript);
    gkr::append_usize(transcript,b"gkr-layer-index",0);
    let row_weights=gkr::eq_weights(&r[..shape.row_bits]);
    let r_high=&r[shape.row_bits..];
    let omega:Vec<_>=(0..shape.copies).map(|copy|eq_index(r_high,copy)).collect();
    let mut claim=Fr::zero();let mut rounds=Vec::new();
    let (u,left_value)=first_phase(circuit,&shape,&mut load_copy,&row_weights,&omega,point_factorized,
        &mut claim,&mut rounds,transcript)?;
    let u_low=gkr::eq_weights(&u[..shape.input_bits]);let u_high=&u[shape.input_bits..];
    let mut c=vec![Fr::zero();circuit.input_len];let mut d=vec![Fr::zero();circuit.input_len];
    for term in &circuit.terms {
        let g=&term.gate;let weight=row_weights[term.row]*u_low[g.left];
        c[g.right]+=weight*(g.c2+g.c3*left_value);
        d[g.right]+=weight*(g.c0+g.c1*left_value);
    }
    drop(u_low);drop(row_weights);
    let tau:Vec<_>=(0..shape.copies).map(|copy|omega[copy]*eq_index(u_high,copy)).collect();
    drop(omega);
    let (v,right_value)=second_phase(circuit,&shape,&mut load_copy,c,d,&tau,
        &mut claim,&mut rounds,transcript)?;
    let coefficients=sparse::wiring(circuit,&shape,&r,&u,&v)?;
    if coefficients[0]+coefficients[1]*left_value+coefficients[2]*right_value
        +coefficients[3]*left_value*right_value!=claim {return Err(GkrError::TerminalExpression.into());}
    let mut line=vec![Fr::zero();shape.input_bits+log_copies+1];
    for copy in 0..shape.copies {
        let input=read_copy(&mut load_copy,copy,circuit.input_len)?;
        let local=gkr::line_polynomial(&input,&u[..shape.input_bits],&v[..shape.input_bits]);
        let selector=copy_line_selector(copy,u_high,&v[shape.input_bits..]);
        for (sum,coefficient) in line.iter_mut().zip(multiply_polynomials(&local,&selector)) {*sum+=coefficient;}
    }
    if line[0]!=left_value || gkr::eval_polynomial(&line,Fr::one())!=right_value {
        return Err(GkrError::LineEndpoints.into());
    }
    transcript.append_scalar(b"gkr-left-value",&left_value);
    transcript.append_scalar(b"gkr-right-value",&right_value);
    gkr::append_polynomial(transcript,b"gkr-line-polynomial",&line);
    let challenge=transcript.challenge_scalar(b"gkr-line-challenge");
    let point=gkr::line_point(&u,&v,challenge);let value=gkr::eval_polynomial(&line,challenge);
    let proof=GkrProof {layers:vec![LayerProof {rounds,left_value,right_value,line_coefficients:line}]};
    Ok((proof,InputClaim {point,value}))
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::Field;
    use crate::{gkr::Gate,sparse::Term,sparse_stream};
    fn transcript()->Transcript {Transcript::new(b"boolean-stream-exact-parity")}
    fn fixture(width:usize,copies:usize)->(Circuit,Vec<Vec<Fr>>) {
        let input=(0..copies).map(|copy|(0..width).map(|bit| {
            if bit==width-1 {Fr::one()} else {Fr::from(((copy>>bit)&1) as u64)}
        }).collect()).collect();
        // (x+1)(y-1)=0, all coefficients nonzero. y is one. Duplicate terms
        // cancel in another row. Width8 has eight distinct valid copies;
        // width1 cannot contain eight distinct Boolean vectors.
        let g=Gate {left:0,right:width-1,c0:-Fr::one(),c1:-Fr::one(),c2:Fr::one(),c3:Fr::one()};
        let opposite=Gate {c0:-g.c0,c1:-g.c1,c2:-g.c2,c3:-g.c3,..g.clone()};
        // Unlike the y=1 relation, x*x-x has nonzero first-phase polynomials
        // when interpolating between different Boolean input coordinates.
        let booleanity=Gate {left:0,right:0,c0:Fr::zero(),c1:-Fr::one(),c2:Fr::zero(),c3:Fr::one()};
        (Circuit {input_len:width,row_count:4,terms:vec![Term {row:0,gate:g.clone()},
            Term {row:1,gate:g},Term {row:1,gate:opposite},Term {row:2,gate:booleanity}]},input)
    }
    #[test]
    fn exact_proof_claim_transcript_and_reads_match_both_references() {
        for width in [1usize,2,8] {for h in 0..=3 {
            let (c,inputs)=fixture(width,1<<h);let flat:Vec<_>=inputs.iter().flatten().copied().collect();
            if width==8 {for i in 0..inputs.len() {for j in 0..i {assert_ne!(inputs[i],inputs[j]);}}}
            let mut resident_t=transcript();let resident=sparse::prove(&c,&flat,h,&mut resident_t).unwrap();
            let mut generic_t=transcript();let generic=sparse_stream::prove(&c,h,|i|Ok(inputs[i].clone()),&mut generic_t).unwrap();
            let mut boolean_t=transcript();let mut reads=0;
            let boolean=prove(&c,h,|i|{reads+=1;Ok(inputs[i].clone())},&mut boolean_t).unwrap();
            assert_eq!(boolean,resident);assert_eq!(boolean,generic);
            if width>=2 && h>0 {
                let first_phase_rounds=width.trailing_zeros() as usize+h;
                assert!(boolean.0.layers[0].rounds[..first_phase_rounds].iter().flatten().any(|x|!x.is_zero()),
                    "first phase must be nonvacuous: width={width}, h={h}");
            }
            assert_eq!(gkr::encode_proof(&boolean.0).unwrap(),gkr::encode_proof(&resident.0).unwrap());
            assert_eq!(gkr::encode_proof(&boolean.0).unwrap(),gkr::encode_proof(&generic.0).unwrap());
            assert_eq!(reads,(width.trailing_zeros() as usize+5)*(1<<h));
            for t in [&generic_t,&boolean_t] {
                assert_eq!(t.raw_queries(),resident_t.raw_queries());
                assert_eq!(t.challenges(),resident_t.challenges());
                assert_eq!(t.bytes_absorbed(),resident_t.bytes_absorbed());
            }
            let next=resident_t.challenge_scalar(b"after-proof");
            assert_eq!(next,generic_t.challenge_scalar(b"after-proof"));
            assert_eq!(next,boolean_t.challenge_scalar(b"after-proof"));
            assert_eq!(sparse::verify(&c,h,&boolean.0,&mut transcript()).unwrap(),boolean.1);
            assert_eq!(gkr::mle(&flat,&boolean.1.point).unwrap(),boolean.1.value);
        }}
    }
    #[test]
    fn first_phase_vectors_match_direct_formula_with_collisions_and_zero_weights() {
        let gate=|left,right,c0:i64,c1:i64,c2:i64,c3:i64|Gate {
            left,right,c0:Fr::from(c0),c1:Fr::from(c1),c2:Fr::from(c2),c3:Fr::from(c3),
        };
        let c=Circuit {input_len:8,row_count:4,terms:vec![
            Term {row:0,gate:gate(1,2,2,3,5,7)},
            Term {row:0,gate:gate(1,2,2,3,5,7)},
            Term {row:1,gate:gate(1,3,-11,-13,-17,-19)},
            Term {row:2,gate:gate(4,2,23,0,0,29)},
            Term {row:3,gate:gate(4,2,31,37,41,43)},
            Term {row:3,gate:gate(4,2,-31,-37,-41,-43)},
            Term {row:3,gate:gate(4,5,0,47,53,0)},
        ]};
        let rho=[Fr::from(2),Fr::from(3),Fr::zero(),-Fr::from(5)];
        let precomputed=FirstPhase::new(&c,&rho);
        for mask in [0u8,255,0b01010101,0b10100110] {
            let input:Vec<_>=(0..8).map(|i|Fr::from(((mask>>i)&1) as u64)).collect();
            let mut a=vec![Fr::zero();8];let mut b=vec![Fr::zero();8];
            for term in &c.terms {
                let g=&term.gate;
                a[g.left]+=rho[term.row]*(g.c1+g.c3*input[g.right]);
                b[g.left]+=rho[term.row]*(g.c0+g.c2*input[g.right]);
            }
            assert!(a.iter().chain(&b).any(|x|!x.is_zero()));
            assert_eq!(precomputed.vectors(&input),(a,b),"mask {mask}");
        }
    }
    #[test]
    fn every_prefix_vectors_match_explicit_folding_through_scalar_handoff() {
        let gate=|left,right,c0:i64,c1:i64,c2:i64,c3:i64|Gate {
            left,right,c0:Fr::from(c0),c1:Fr::from(c1),c2:Fr::from(c2),c3:Fr::from(c3),
        };
        for width in [8usize,16] {
            let c=Circuit {input_len:width,row_count:4,terms:vec![
                Term {row:0,gate:gate(1,width-1,2,3,5,7)},
                Term {row:1,gate:gate(1,width-2,11,13,17,19)},
                Term {row:1,gate:gate(1,width-2,-11,-13,-17,-19)},
                Term {row:2,gate:gate(width-1,0,23,29,31,37)},
                Term {row:3,gate:gate(width-2,width-1,41,43,47,53)},
                Term {row:3,gate:gate(0,width-2,-59,61,67,-71)},
                Term {row:2,gate:gate(2,3,0,73,79,0)},
            ]};
            let rho=[Fr::zero(),Fr::from(2),-Fr::from(3),Fr::from(7)];
            let original=FirstPhase::new(&c,&rho);
            let dimensions=width.trailing_zeros() as usize;
            for coordinates in [[Fr::zero(),Fr::one(),Fr::from(5),-Fr::from(7)],
                [Fr::one(),Fr::zero(),Fr::from(3).inverse().unwrap(),Fr::from(11)]] {
                let mut current=FirstPhase::new(&c,&rho);
                let right_indices:Vec<_>=current.a_edges.iter().chain(&current.b_edges).map(|e|e.right).collect();
                for prefix in 0..=dimensions {
                    assert_eq!(current.a_constant.len(),width>>prefix);
                    assert_eq!(current.b_constant.len(),width>>prefix);
                    assert_eq!(current.a_edges.iter().chain(&current.b_edges).map(|e|e.right).collect::<Vec<_>>(),right_indices);
                    for mask in [0u16,u16::MAX,0x5555,0xa6b9] {
                        let input:Vec<_>=(0..width).map(|i|Fr::from(((mask>>i)&1) as u64)).collect();
                        let (mut a,mut b)=original.vectors(&input);
                        for z in &coordinates[..prefix] {gkr::fold(&mut a,*z);gkr::fold(&mut b,*z);}
                        assert_eq!(current.vectors(&input),(a,b),"width={width}, prefix={prefix}, mask={mask}");
                    }
                    if prefix<dimensions {current.bind_low(coordinates[prefix]);}
                }
                assert!(current.a_edges.iter().chain(&current.b_edges).all(|e|e.left==0));
            }
        }
    }
    #[test]
    fn canonical_point_factor_matches_generic_without_a_proof_frame() {
        let compiled=point_membership::build().unwrap();let c=&compiled.circuit;
        let mut seed=0x78c2_9413_a0d5_8e61u64;
        let mut next=||{seed=seed.wrapping_mul(6364136223846793005).wrapping_add(1);seed};
        let owners:Vec<Vec<Fr>>=(0..2).map(|_|(0..point_membership::POINT_WIDTH)
            .map(|_|Fr::from(next()>>63)).collect()).collect();
        for weight_case in 0..2 {
            let rho:Vec<_>=(0..c.row_count).map(|_|Fr::from(next())).collect();
            let coordinates:Vec<_>=(0..13).map(|_|Fr::from(next())).collect();
            let mut generic=FirstPhase::new(c,&rho);
            let mut factored=FirstPhase::new_point(c,&rho);
            assert_eq!(generic.a_edges.len()-factored.a_edges.len(),262_656);
            assert_eq!(generic.b_edges.len(),factored.b_edges.len());
            for prefix in 0..=13 {
                for (owner,input) in owners.iter().enumerate() {
                    let (a,b)=generic.vectors(input);let (a_factor,b_factor)=factored.vectors(input);
                    assert_eq!(a_factor,a,"rho={weight_case}, owner={owner}, prefix={prefix}, A");
                    assert_eq!(b_factor,b,"rho={weight_case}, owner={owner}, prefix={prefix}, B");
                    let mut x=input.clone();for challenge in &coordinates[..prefix] {gkr::fold(&mut x,*challenge);}
                    assert_eq!(gkr::quadratic_message(&a_factor,&b_factor,&x),
                        gkr::quadratic_message(&a,&b,&x),
                        "rho={weight_case}, owner={owner}, prefix={prefix}, message");
                    if prefix==13 {assert_eq!(a_factor[0]*x[0]+b_factor[0],a[0]*x[0]+b[0]);}
                }
                if prefix<13 {generic.bind_low(coordinates[prefix]);factored.bind_low(coordinates[prefix]);}
            }
        }
    }
    #[test]
    #[ignore = "bounded two-owner canonical point proof differential"]
    fn canonical_point_factor_matches_honest_two_owner_encoded_proof_and_transcript() {
        let compiled=point_membership::build().unwrap();let c=&compiled.circuit;
        let generator=||{
            let hex="79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798";
            let mut point=[0u8;33];point[0]=2;
            for i in 0..32 {point[i+1]=u8::from_str_radix(&hex[2*i..2*i+2],16).unwrap();}
            point
        };
        let owners:Vec<Vec<Fr>>=[([0;33],[0;33]),(generator(),generator())]
            .into_iter().map(|(pk,w)|point_membership::witness(pk,w).unwrap().into_iter()
                .map(|bit|Fr::from(bit as u64)).collect()).collect();
        let shape=sparse::validate(c,1).unwrap();
        let mut generic_t=Transcript::new(b"point-factor-two-owner-parity");
        let generic=prove_with_shape(c,1,shape,false,|copy|Ok(owners[copy].clone()),&mut generic_t).unwrap();
        let shape=sparse::validate(c,1).unwrap();
        let mut factored_t=Transcript::new(b"point-factor-two-owner-parity");
        let factored=prove_with_shape(c,1,shape,true,|copy|Ok(owners[copy].clone()),&mut factored_t).unwrap();
        assert_eq!(factored,generic);
        assert_eq!(gkr::encode_proof(&factored.0).unwrap(),gkr::encode_proof(&generic.0).unwrap());
        assert_eq!(factored_t.raw_queries(),generic_t.raw_queries());
        assert_eq!(factored_t.challenges(),generic_t.challenges());
        assert_eq!(factored_t.bytes_absorbed(),generic_t.bytes_absorbed());
        assert_eq!(factored_t.challenge_scalar(b"after-proof"),generic_t.challenge_scalar(b"after-proof"));
        assert_eq!(sparse::verify(c,1,&factored.0,&mut Transcript::new(b"point-factor-two-owner-parity")).unwrap(),factored.1);
    }
    #[test]
    fn generic_compression_weighted_edge_and_storage_counts() {
        let compiled=crate::circuit::build_compression(None).unwrap();
        let c=&compiled.compiled.circuit;
        let tables=FirstPhase::new(c,&vec![Fr::one();c.row_count]);
        let a_edges=c.terms.iter().filter(|t|!t.gate.c3.is_zero()).count();
        let b_edges=c.terms.iter().filter(|t|!t.gate.c2.is_zero()).count();
        assert_eq!(tables.a_edges.len(),a_edges);assert_eq!(tables.b_edges.len(),b_edges);
        eprintln!("generic compression phase1: width={}, terms={}, Aedges={}, Bedges={}, EdgeBytes={}, edge_record_bytes={}, allocated_edge_bytes={}, constant_bytes={}",
            c.input_len,c.terms.len(),a_edges,b_edges,std::mem::size_of::<Edge>(),
            (a_edges+b_edges)*std::mem::size_of::<Edge>(),
            (tables.a_edges.capacity()+tables.b_edges.capacity())*std::mem::size_of::<Edge>(),
            (tables.a_constant.capacity()+tables.b_constant.capacity())*std::mem::size_of::<Fr>());
    }
    #[test]
    fn factor_helpers_preserve_zero_omega_zero_sigma_and_nonunit_sigma() {
        let a=vec![Fr::from(3),Fr::from(5),Fr::from(7),Fr::from(11)];
        let d=vec![Fr::from(13),Fr::from(17),Fr::from(19),Fr::from(23)];
        let xs=[vec![Fr::zero(),Fr::one(),Fr::one(),Fr::zero()],
            vec![Fr::one(),Fr::zero(),Fr::one(),Fr::one()]];
        for omega in [Fr::zero(),Fr::one(),Fr::from(9)] {
            let aw:Vec<_>=a.iter().map(|x|*x*omega).collect();
            let dw:Vec<_>=d.iter().map(|x|*x*omega).collect();
            let expected:Vec<_>=gkr::quadratic_message(&a,&d,&xs[0]).iter().map(|x|*x*omega).collect();
            assert_eq!(gkr::quadratic_message(&aw,&dw,&xs[0]),expected);
        }
        let r=Fr::from(2);
        for u in [Fr::from(3).inverse().unwrap(),Fr::from(2)] {
            let tau=[(Fr::one()-r)*(Fr::one()-u),r*u];let sigma=tau[0]+tau[1];
            assert!(tau.iter().all(|x|!x.is_zero()));assert_ne!(sigma,Fr::one());
            if u==Fr::from(3).inverse().unwrap() {assert_eq!(sigma,Fr::zero());}
            else {assert!(!sigma.is_zero());}
            let mut x_bar=vec![Fr::zero();4];
            for copy in 0..2 {for j in 0..4 {x_bar[j]+=tau[copy]*xs[copy][j];}}
            let mut ac=a.clone();let mut dc=d.clone();let mut copies=xs.clone();
            for challenge in [Fr::from(29),Fr::from(31)] {
                let mut expected=vec![Fr::zero();3];
                for copy in 0..2 {
                    for (out,value) in expected.iter_mut().zip(gkr::quadratic_message(&ac,&dc,&copies[copy])) {*out+=tau[copy]*value;}
                }
                assert_eq!(quadratic_scaled_d(&ac,&dc,&x_bar,sigma),expected);
                gkr::fold(&mut ac,challenge);gkr::fold(&mut dc,challenge);gkr::fold(&mut x_bar,challenge);
                for x in &mut copies {gkr::fold(x,challenge);}
            }
            let sum:Fr=(0..2).map(|copy|tau[copy]*(ac[0]*copies[copy][0]+dc[0])).sum();
            assert_eq!(sum,ac[0]*x_bar[0]+sigma*dc[0]);
            assert!(!dc[0].is_zero()); // Unscaled D survives the zero-sigma case.
        }
        assert_eq!(eq_index(&[Fr::one()],0),Fr::zero());
    }
    #[test]
    fn nonbinary_unused_coordinate_rejected_before_transcript_changes() {
        let(c,mut inputs)=fixture(8,2);inputs[1][3]=Fr::from(2);
        let mut t=transcript();let mut untouched=transcript();
        assert_eq!(prove(&c,1,|i|Ok(inputs[i].clone()),&mut t),Err(Error::NonBoolean {copy:1,index:3}));
        assert_eq!(t.challenges(),0);assert_eq!(t.raw_queries(),0);
        assert_eq!(t.bytes_absorbed(),untouched.bytes_absorbed());
        assert_eq!(t.challenge_scalar(b"after-error"),untouched.challenge_scalar(b"after-error"));
    }
    #[test]
    fn every_read_rechecks_boolean_width_and_reader_errors() {
        let(c,inputs)=fixture(8,2);let total=(3+5)*2;
        // Inject into each read in turn: validation, both sumcheck phases,
        // handoffs and line. The unchanged valid prefix always reaches it.
        for bad_read in 1..=total {
            for fault in 0..3 {
                let mut reads=0;let mut failed_copy=0;
                let result=prove(&c,1,|copy| {
                    reads+=1;let mut x=inputs[copy].clone();
                    if reads==bad_read {
                        failed_copy=copy;
                        match fault {0=>x[3]=Fr::from(2),1=>{x.pop();},_=>return Err(GkrError::InvalidInputWidth)}
                    }
                    Ok(x)
                },&mut transcript());
                let expected=if fault==0 {Error::NonBoolean {copy:failed_copy,index:3}}
                    else {Error::Gkr(GkrError::InvalidInputWidth)};
                assert_eq!(result,Err(expected),"read {bad_read}, fault {fault}");assert_eq!(reads,bad_read);
            }
        }
    }
    #[test]
    fn nonzero_rows_and_existing_shape_limits_rejected() {
        let(mut c,mut input)=fixture(8,2);input[1][7]=Fr::zero();
        assert_eq!(prove(&c,1,|i|Ok(input[i].clone()),&mut transcript()),Err(Error::Gkr(GkrError::NonzeroOutput)));
        assert_eq!(prove(&c,4,|_|panic!("shape must reject before read"),&mut transcript()),Err(Error::Gkr(GkrError::RepetitionLimit)));
        c.input_len=3;
        assert_eq!(prove(&c,0,|_|panic!("shape must reject before read"),&mut transcript()),Err(Error::Gkr(GkrError::InvalidInputWidth)));
    }
}

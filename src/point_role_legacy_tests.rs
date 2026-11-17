use super::*;

// Literal retained pre-delegation algorithm. This is a compatibility oracle,
// not an alternative public producer, topology or acceptance path.
fn original_coefficients(base:&Circuit,g:usize,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],GkrError> {
    if (r.len(),u.len(),v.len())!=(14+g,13+g,13+g){return Err(GkrError::PointDimension);}
    let shape=sparse::validate(base,0)?;
    let mut coefficients=sparse::wiring(base,&shape,&r[..14],&u[..13],&v[..13])?;
    let high=r[14..].iter().zip(&u[13..]).zip(&v[13..]).fold(Fr::one(),|a,((r,u),v)|
        a*((Fr::one()-r)*(Fr::one()-u)*(Fr::one()-v)+*r**u**v));
    for c in &mut coefficients{*c*=high;}Ok(coefficients)
}
fn same(a:&Transcript,b:&Transcript){
    assert_eq!((a.bytes_absorbed(),a.challenges(),a.raw_queries()),(b.bytes_absorbed(),b.challenges(),b.raw_queries()));
    assert_eq!(a.clone().try_challenge_scalar(b"c568-legacy-probe").unwrap(),b.clone().try_challenge_scalar(b"c568-legacy-probe").unwrap());
}

#[test]
fn c568_fast_legacy_delegate_shape_pointer_math_projection_and_framing() {
    let canonical=point_membership::build().unwrap();let base=&canonical.circuit;
    for g in [2,21] {
        let role=PointRole::dimensions(base,g,13+g,14+g,20+g).unwrap();
        assert!(std::ptr::eq(role.base,base));
        let point=|n,start| (0..n).map(|i|Fr::from((start+i)as u64)).collect::<Vec<_>>();
        let(r,u,v)=(point(14+g,2),point(13+g,43),point(13+g,87));
        assert_eq!(role.coefficients(&r,&u,&v),original_coefficients(base,g,&r,&u,&v));
        let mut expected=u[..13].to_vec();expected.extend([0u64,0,0,0,0,1,1].map(Fr::from));expected.extend_from_slice(&u[13..]);
        assert_eq!(role.project(&u).unwrap(),expected);
        assert!(role.project(&u[..u.len()-1]).is_err());
        assert!(PointRole::dimensions(base,g,12+g,14+g,20+g).is_err());
        // A syntactically shaped negative verifier probe reaches the bind and
        // wiring path. Both results and literal transcript continuations must
        // match; it is not a generated or authenticated positive proof.
        let d=13+g;
        let probe=GkrProof{layers:vec![gkr::LayerProof{rounds:vec![vec![Fr::zero();3];2*d],
            left_value:Fr::zero(),right_value:Fr::zero(),line_coefficients:vec![Fr::zero();d+1]}]};
        let mut delegated=Transcript::new(b"c568-legacy-math");let mut original=delegated.clone();
        let got=role.verify(&probe,&mut delegated);
        let reference=gkr::verify_with_wiring(&[d],1usize<<(14+g),&probe,&mut original,
            |t|sparse::bind(base,g,t),|layer,r,u,v|if layer==0{original_coefficients(base,g,r,u,v)}else{Err(GkrError::PointDimension)});
        assert_eq!(got,reference);same(&delegated,&original);
    }
    assert!(PointRole::dimensions(base,22,35,36,42).is_err());
    let mut wrong=base.clone();wrong.terms.pop();
    assert!(PointRole::dimensions(&wrong,2,15,16,22).is_err());
}

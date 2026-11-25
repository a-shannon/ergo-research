//! Whole-function equivalence, not a proof or commitment adapter.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use num_bigint::BigUint;
use crate::{gkr, implicit_witness::{Witness, MAX_EXTENT}, certified_legacy_bound as legacy,
    envelope_score_join::{Declaration, Plan}, origin_score_map::{Mode, GuardPolicy}};

fn scalar(value: u64) -> Fr { Fr::from(value) }
fn integer(text: &str) -> BigUint { BigUint::parse_bytes(text.as_bytes(), 10).unwrap() }
fn weight(index: usize, point: &[Fr]) -> Fr {
    let mut result = Fr::one();
    for (bit, coordinate) in point.iter().enumerate() {
        result *= if index >> bit & 1 == 1 { *coordinate } else { Fr::one() - coordinate };
    }
    result
}
fn literal_mle(dense: &[Fr], point: &[Fr]) -> Fr {
    dense.iter().enumerate().map(|(index, value)| *value * weight(index, point)).sum()
}
fn literal_line(dense: &[Fr], u: &[Fr], v: &[Fr]) -> Vec<Fr> {
    let mut result = vec![Fr::zero(); u.len()+1];
    // Dense literal oracle: fresh convolution at each dimension, independently
    // of the owned-support/in-place production path.
    for (index, value) in dense.iter().enumerate() {
        let mut polynomial = vec![*value];
        for bit in 0..u.len() {
            let a = if index >> bit & 1 == 1 { u[bit] } else { Fr::one()-u[bit] };
            let b = if index >> bit & 1 == 1 { v[bit]-u[bit] } else { u[bit]-v[bit] };
            let mut next = vec![Fr::zero(); polynomial.len()+1];
            for (degree, coefficient) in polynomial.iter().enumerate() {
                next[degree] += a * coefficient;
                next[degree+1] += b * coefficient;
            }
            polynomial = next;
        }
        for (sum, coefficient) in result.iter_mut().zip(&polynomial) { *sum += coefficient; }
    }
    result
}
fn evaluate_polynomial(coefficients: &[Fr], point: Fr) -> Fr {
    let mut result = Fr::zero();
    for coefficient in coefficients.iter().rev() { result = result * point + coefficient; }
    result
}
fn dense_entries(dense: &[Fr]) -> Vec<(usize, Fr)> {
    dense.iter().enumerate().filter_map(|(index, value)|
        if value.is_zero() { None } else { Some((index, *value)) }).collect()
}
fn check_function(name: &str, dense: &[Fr], full_literal_line: bool) {
    let d = dense.len().trailing_zeros() as usize;
    let expected_entries = dense_entries(dense);
    let expected_k = expected_entries.len();
    let witness = Witness::from_dense(dense, dense.len()).unwrap();
    assert_eq!(witness.entries(), expected_entries, "{name}: complete support");
    assert_eq!((witness.extent(), witness.dimensions(), witness.retained_capacity()),
        (dense.len(), d, expected_k), "{name}: retained storage");
    assert_eq!(witness.declared_cap(), dense.len());
    for (index, expected) in dense.iter().enumerate() {
        assert_eq!(witness.value(index).unwrap(), *expected, "{name}: lookup {index}");
    }
    // Three fixed point families. Every prefix means j=0..d, not all field points.
    let points = [vec![scalar(2);d], (0..d).map(|bit| scalar((bit % 2) as u64)).collect(),
        (0..d).map(|bit| scalar((bit % 4+3) as u64)).collect()];
    for (family, point) in points.iter().enumerate() {
        let mut dense_fold = dense.to_vec();
        let mut sequential = witness.clone();
        for j in 0..=d {
            let (folded, work) = witness.fold_counted(&point[..j]).unwrap();
            assert_eq!(work.entry_visits, expected_k, "{name}: prefix {j} visits");
            assert_eq!(work.weight_factors, expected_k*j);
            assert_eq!(work.aggregation_capacity, expected_k);
            assert_eq!(work.retained_entries, folded.entries().len());
            assert_eq!(folded.retained_capacity(), folded.entries().len());
            assert_eq!(folded.declared_cap(), dense.len().min(dense.len() >> j));
            assert_eq!(folded, sequential, "{name}: successive prefix {j}");
            assert_eq!(folded.extent(), dense_fold.len());
            for (index, expected) in dense_fold.iter().enumerate() {
                assert_eq!(folded.value(index).unwrap(), *expected,
                    "{name}: family {family} prefix {j} index {index}");
            }
            if j < d {
                gkr::fold(&mut dense_fold, point[j]);
                sequential = sequential.fold(&point[j..j+1]).unwrap();
            }
        }
        let expected = literal_mle(dense, point);
        assert_eq!(witness.mle(point).unwrap(), expected, "{name}: literal MLE");
        assert_eq!(gkr::mle(dense, point).unwrap(), expected, "{name}: dense MLE");
    }
    let u = (0..d).map(|bit| scalar((bit % 3 + 2) as u64)).collect::<Vec<_>>();
    let v = (0..d).map(|bit| scalar((bit % 5 + 5) as u64)).collect::<Vec<_>>();
    let (line, work) = witness.line_counted(&u, &v).unwrap();
    assert_eq!(line.len(), d+1, "{name}: exact line framing");
    assert_eq!(work.entry_visits, expected_k);
    assert_eq!(work.coefficient_updates, expected_k*d*(d+3)/2);
    assert_eq!((work.output_scalars, work.scratch_scalars), (d+1,d+1));
    assert_eq!(line, gkr::line_polynomial(dense, &u, &v), "{name}: dense line coefficients");
    if full_literal_line { assert_eq!(line, literal_line(dense, &u, &v), "{name}: literal convolution"); }
    for t in [Fr::zero(), Fr::one(), scalar(2), scalar(3)] {
        let point = u.iter().zip(&v).map(|(a,b)| *a+t*(*b-*a)).collect::<Vec<_>>();
        assert_eq!(evaluate_polynomial(&line,t), literal_mle(dense,&point), "{name}: line point");
    }
    let stationary = witness.line(&u,&u).unwrap();
    assert_eq!(stationary.len(),d+1);
    assert_eq!(stationary[0],literal_mle(dense,&u));
    assert!(stationary[1..].iter().all(|c|c.is_zero()), "{name}: leading zero padding");
}

fn malformed_admission_and_callbacks() {
    let cases = vec![
        ("extent-zero",0,0,Vec::new(),"whole witness extent"),
        ("extent-nonpower",3,3,vec![(0,scalar(2))],"whole witness extent"),
        ("extent-over",32768,0,Vec::new(),"whole witness extent"),
        ("declared-cap",4,5,vec![(0,scalar(2))],"whole witness declared cap"),
        ("entry-count",4,1,vec![(0,scalar(2)),(1,scalar(3))],"whole witness entry count"),
        ("duplicate",4,4,vec![(1,scalar(2)),(1,scalar(3))],"whole witness duplicate"),
        ("disorder",4,4,vec![(2,scalar(2)),(1,scalar(3))],"whole witness disorder"),
        ("index",4,4,vec![(4,scalar(2))],"whole witness index"),
        ("explicit-zero",4,4,vec![(1,Fr::zero())],"whole witness explicit zero"),
    ];
    for (name,n,cap,entries,error) in cases {
        let mut calls = 0;
        assert_eq!(Witness::with_admitted(n,cap,entries,|_|{calls+=1;}),Err(error.into()),"{name}");
        assert_eq!(calls,0,"{name}: consumer before admission");
    }
    let mut over = Vec::with_capacity(5); over.push((0,scalar(2)));
    assert!(over.capacity()>4);
    let mut calls=0;
    assert_eq!(Witness::with_admitted(4,4,over,|_|{calls+=1;}),Err("whole witness incoming capacity".into()));
    assert_eq!(calls,0);
    let witness=Witness::new(4,4,vec![(1,scalar(2))]).unwrap();
    assert_eq!(witness.query_with(4,|_|{calls+=1;}),Err("whole witness query index".into()));
    assert_eq!(calls,0);
    assert_eq!(witness.fold(&[Fr::one();3]).unwrap_err(),"whole witness prefix dimensions");
    assert_eq!(witness.mle(&[Fr::one()]).unwrap_err(),"whole witness point dimensions");
    assert_eq!(witness.mle(&[Fr::one();3]).unwrap_err(),"whole witness point dimensions");
    assert_eq!(witness.line(&[Fr::one()],&[Fr::one();2]).unwrap_err(),"whole witness line dimensions");
    assert_eq!(witness.line(&[Fr::one();2],&[Fr::one()]).unwrap_err(),"whole witness line dimensions");
    assert_eq!(witness.line(&[Fr::one();3],&[Fr::one();2]).unwrap_err(),"whole witness line dimensions");
    assert_eq!(witness.line(&[Fr::one();2],&[Fr::one();3]).unwrap_err(),"whole witness line dimensions");
    assert!(Witness::from_dense(&[],0).is_err());
    assert!(Witness::from_dense(&[Fr::one();4],3).is_err());
    assert!(Witness::from_dense(&[Fr::one();4],5).is_err());
    let mut valid_calls=0;
    Witness::with_admitted(4,4,vec![(1,scalar(2))],|w|{valid_calls+=1;assert_eq!(w.value(1).unwrap(),scalar(2));}).unwrap();
    assert_eq!(valid_calls,1);
    assert_eq!(witness.query_with(0,|v|v).unwrap(),Fr::zero());
}

fn exact_storage_and_cancellation() {
    let mut entries=Vec::with_capacity(MAX_EXTENT); entries.push((7,scalar(2)));
    let witness=Witness::new(MAX_EXTENT,MAX_EXTENT,entries).unwrap();
    assert_eq!(witness.retained_capacity(),1,"declared cap cannot retain spare entries");
    let empty=Witness::new(MAX_EXTENT,MAX_EXTENT,Vec::with_capacity(MAX_EXTENT)).unwrap();
    assert_eq!(empty.retained_capacity(),0);
    let cancelled=Witness::new(2,2,vec![(0,scalar(2)),(1,Fr::one())]).unwrap().fold(&[scalar(2)]).unwrap();
    assert_eq!((cancelled.extent(),cancelled.declared_cap(),cancelled.retained_capacity()),(1,1,0));
    assert_eq!(cancelled.value(0).unwrap(),Fr::zero());
    let dense=vec![scalar(2);MAX_EXTENT];
    let full=Witness::from_dense(&dense,MAX_EXTENT).unwrap();
    assert_eq!(full.retained_capacity(),MAX_EXTENT,"adversarial dense support retained");
    drop(full);drop(witness);drop(empty);drop(cancelled);
    check_function("dense-max",&dense,false);
}

fn small_whole_functions() {
    for (name,dense) in [
        ("width0-zero",vec![Fr::zero()]),("width0-nonBoolean",vec![scalar(7)]),
        ("zero",vec![Fr::zero();8]),("sparse",vec![Fr::zero(),scalar(2),Fr::zero(),-scalar(3),Fr::zero(),Fr::zero(),scalar(5),Fr::zero()]),
        ("dense-small",(0..16).map(|i|scalar(i+2)).collect()),
        ("cancellation",vec![scalar(2),Fr::one()]),
    ] { check_function(name,&dense,true); }
}

fn source2_join_and_padding() {
    let d=Declaration {legacy:legacy::Inputs {d:[integer("1000000000"),integer("100000000000")],t:[1,2,3]},
        bound:integer("255212307692307695"),modern_d:BigUint::from(5u8),modern_q:BigUint::from(8u8),
        work:[BigUint::from(0u8),BigUint::from(7u8)],mode:Mode::Exact,prefix:2,
        expected:integer("5149812130702633730055"),guard:GuardPolicy::Disabled};
    let plan=Plan::new(d).unwrap();
    let dense=plan.produce().unwrap();
    assert_eq!(dense.len(),MAX_EXTENT);
    // Independent BigInt/popcount hypothesis, to be closed by actual execution.
    let component_counts=[0..8192,8192..10240,10240..12288,12288..14336,14336..16384]
        .map(|range|dense[range].iter().filter(|value|!value.is_zero()).count());
    assert_eq!(component_counts,[384,14,412,99,59]);
    assert_eq!(dense.iter().filter(|value|!value.is_zero()).count(),968);
    assert_eq!(std::mem::size_of::<Fr>(),32);
    assert_eq!(std::mem::size_of::<(usize,Fr)>(),40);
    let terms=plan.terms().unwrap(); assert_eq!(terms.len(),93441);
    plan.verify(&terms,|index|dense[index]).unwrap();
    let witness=Witness::from_dense(&dense,MAX_EXTENT).unwrap();
    assert_eq!(witness.entries().len(),968);
    assert_eq!(witness.retained_capacity(),968);
    assert_eq!(witness.retained_capacity()*std::mem::size_of::<(usize,Fr)>(),38720);
    assert_eq!(dense.len()*std::mem::size_of::<Fr>(),524288);
    plan.verify(&terms,|index|witness.value(index).unwrap()).unwrap();
    drop(witness);
    // Last cell is padding in the existing all-cell constrained local profile.
    assert_eq!(dense[MAX_EXTENT-1],Fr::zero());
    let mut changed=dense.clone(); changed[MAX_EXTENT-1]=Fr::one();
    // Second score owner's local cell2047: padding row3478+(2047-1994),
    // shifted by SCORE_ROWS24576 plus owner stride8192 gives literal row36299.
    let mut residuals=vec![Fr::zero();65536];
    for term in &terms {
        let g=&term.gate;
        residuals[term.row]+=g.c0+g.c1*changed[g.left]+g.c2*changed[g.right]+g.c3*changed[g.left]*changed[g.right];
    }
    let bad=residuals.iter().enumerate().filter_map(|(row,value)|
        if value.is_zero(){None}else{Some((row,*value))}).collect::<Vec<_>>();
    assert_eq!(bad,vec![(36299,Fr::one())],"isolated padding row, all other rows valid");
    assert_eq!(plan.row_label(36299),"padding");drop(residuals);
    assert_eq!(plan.verify(&terms,|index|changed[index]).unwrap_err(),"padding row 36299");
    drop(changed); drop(terms);
    check_function("source2-16384",&dense,true);
}

fn actual_unused_nonboolean_cell() {
    // A separate admitted tiny circuit: only wire0 is read. It is not the join.
    let input=vec![Fr::one(),scalar(4),scalar(5),scalar(2)];
    let layer=vec![gkr::Gate{left:0,right:0,c0:-Fr::one(),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()}];
    let values=gkr::evaluate(&input,&[layer.clone()]).unwrap();
    assert_eq!(values[1],vec![Fr::zero()]);
    let mut other=input.clone();other[3]=scalar(3);
    assert_eq!(gkr::evaluate(&other,&[layer]).unwrap()[1],values[1]);
    let a=Witness::from_dense(&input,4).unwrap();let b=Witness::from_dense(&other,4).unwrap();
    assert_eq!(a.value(3).unwrap(),scalar(2));assert_eq!(b.value(3).unwrap(),scalar(3));
    let u=[scalar(2),scalar(3)];let v=[scalar(5),scalar(7)];
    let partial_a=a.fold(&u[..1]).unwrap();let partial_b=b.fold(&u[..1]).unwrap();
    assert_eq!(partial_b.value(1).unwrap()-partial_a.value(1).unwrap(),scalar(2),
        "unused wire3 contributes its nonzero low-bit weight to remaining cell1");
    assert_eq!(partial_b.value(0).unwrap(),partial_a.value(0).unwrap());
    assert_eq!(weight(3,&u),scalar(6));assert!(!weight(3,&u).is_zero());
    assert_eq!(b.mle(&u).unwrap()-a.mle(&u).unwrap(),scalar(6));
    assert_eq!(gkr::mle(&other,&u).unwrap()-gkr::mle(&input,&u).unwrap(),scalar(6));
    let la=a.line(&u,&v).unwrap();let lb=b.line(&u,&v).unwrap();
    // (2+3t)*(3+4t)=6+17t+12t^2, independent of the production helpers.
    assert_eq!(lb.iter().zip(&la).map(|(x,y)|*x-*y).collect::<Vec<_>>(),vec![scalar(6),scalar(17),scalar(12)]);
    assert_eq!(la,gkr::line_polynomial(&input,&u,&v));assert_eq!(lb,literal_line(&other,&u,&v));
}

#[test]
fn whole_witness_fold_mle_and_line() {
    malformed_admission_and_callbacks();exact_storage_and_cancellation();small_whole_functions();
    source2_join_and_padding();actual_unused_nonboolean_cell();
}

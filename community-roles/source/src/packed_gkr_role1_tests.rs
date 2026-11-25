use super::*;
use crate::packed_gkr_role1 as engine;
use ark_ff::Field;
use std::{cell::Cell, mem::size_of};

const BUFFER: usize = 1 << 20;
const WITNESS_BLAKE: &str = "9D45000DD13F371AE2E740993346617B65C0C782B7867D6F6A0F7B01ADE24F30";
fn us(start: Instant) -> u64 { u64::try_from(start.elapsed().as_micros()).unwrap() }
fn counters(t: &Transcript) -> [u64; 3] { [t.challenges(), t.raw_queries(), t.bytes_absorbed()] }
fn continuation(t: &Transcript) -> Fr { t.clone().challenge_scalar(b"role1-window-continuation") }
fn eq(point: &[Fr], index: usize) -> Fr {
    point.iter().enumerate().fold(Fr::one(), |w, (b, x)| w * if index >> b & 1 == 0 { Fr::one() - x } else { *x })
}
fn literal(term: &Term, r: &[Fr], u: &[Fr], v: &[Fr]) -> [Fr; 4] {
    let g = &term.gate; let w = eq(r, term.row) * eq(u, g.left) * eq(v, g.right);
    [g.c0 * w, g.c1 * w, g.c2 * w, g.c3 * w]
}
fn boolean_point(bits: usize, index: usize) -> Vec<Fr> {
    (0..bits).map(|b| Fr::from(((index >> b) & 1) as u64)).collect()
}

#[derive(Debug, PartialEq, Eq)]
struct Trace { r: Vec<Fr>, u: Vec<Fr>, v: Vec<Fr>, counters: [u64; 3], continuation: Fr }
fn verify_trace(context: &ProofContext<'_>, artifact: &Artifact,
    key: &verifier_key::AdmittedVerifierKey, proof: &GkrProof) -> Result<(InputClaim, Trace), GkrError> {
    let mut t = context.transcript(1, key, &artifact.commitment);
    let initial = t.challenges(); let points = RefCell::new(None);
    let claim = gkr::verify_with_wiring(&[22], 1 << 21, proof, &mut t,
        |t| context.bind_role(1, t), |_, r, u, v| {
            *points.borrow_mut() = Some((r.to_vec(), u.to_vec(), v.to_vec()));
            context.coefficients(1, r, u, v).map_err(|_| GkrError::InvalidWireIndex)
        })?;
    assert_eq!(t.challenges() - initial, 66);
    let (r, u, v) = points.into_inner().unwrap();
    Ok((claim, Trace { r, u, v, counters: counters(&t), continuation: continuation(&t) }))
}

fn admit_snapshot(actual: &[u8], expected: &[u8]) -> Result<(), engine::Error> {
    if actual.len() != engine::BYTES || expected.len() != engine::BYTES { return Err(engine::Error::Framing); }
    if actual != expected { return Err(engine::Error::Binding); }
    if Blake2b::<U32>::digest(actual).iter().map(|b| format!("{b:02X}")).collect::<String>() != WITNESS_BLAKE { return Err(engine::Error::Binding); }
    Ok(())
}
fn snapshot(source: &PackedFile, expected: &[u8]) -> engine::Bits {
    assert_eq!(source.input_len(), engine::INPUTS); assert_eq!(expected.len(), engine::BYTES);
    let mut bytes = vec![0u8; engine::BYTES]; assert_eq!(bytes.capacity(), engine::BYTES);
    for copy in 0..64 {
        let chunk = source.read_copy(65536, copy).unwrap();
        assert_eq!(chunk.len(), 65536); assert!(chunk.capacity() <= 65536);
        for (j, bit) in chunk.iter().enumerate() {
            assert!(bit.is_zero() || bit.is_one());
            if bit.is_one() { let i = copy * 65536 + j; bytes[i >> 3] |= 1 << (i & 7); }
        }
        drop(chunk);
    }
    admit_snapshot(&bytes, expected).unwrap();
    engine::Bits::new(bytes.into_boxed_slice()).unwrap()
}

fn cache_and_algebra_controls() -> usize {
    let mut negatives = 0;
    for len in [0usize, 1, 8, 9, 10, 18, 19, 21, 22] {
        let point = (0..len).map(|j| Fr::from((2 * j + 3) as u64) / Fr::from((2 * j + 5) as u64)).collect::<Vec<_>>();
        let mut w = engine::Work::default(); let cache = engine::Cache::new(&point, &mut w).unwrap();
        for index in [0, (1usize << len) - 1, (1usize << len) / 2] { assert_eq!(cache.checked_at(index).unwrap(), eq(&point, index)); }
        if len <= 9 { for (i, value) in gkr::eq_weights(&point).iter().enumerate() { assert_eq!(cache.checked_at(i).unwrap(), *value); } }
        assert_eq!(cache.checked_at(1usize << len), Err(engine::Error::Point)); negatives += 1;
        assert!(cache.bytes() < 40000);
    }
    assert!(matches!(engine::Cache::new(&[Fr::one(); 23], &mut engine::Work::default()), Err(engine::Error::Point))); negatives += 1;
    let point = (2u64..24).map(Fr::from).collect::<Vec<_>>();
    let cache = engine::Cache::new(&point, &mut engine::Work::default()).unwrap();
    assert_ne!(cache.checked_at(1).unwrap(), cache.checked_at(2).unwrap()); negatives += 1;
    let mut bytes = vec![0u8; engine::BYTES]; bytes[0] = 2;
    let bits = engine::Bits::new(bytes.into_boxed_slice()).unwrap();
    let p = [Fr::from(2u64), Fr::from(3u64), Fr::from(5u64)];
    assert_eq!(engine::folded(&bits, 0, &p, &mut engine::Work::default()).unwrap(), Fr::from(16u64));
    let mut wrong = [Fr::zero(); 8]; wrong[1] = Fr::one(); let mut n = 8;
    for challenge in p { for j in 0..n/2 { wrong[j] += (wrong[j+n/2] - wrong[j]) * challenge; } n /= 2; }
    assert_eq!(wrong[0], Fr::from(10u64)); negatives += 1;
    assert_eq!(engine::folded(&bits, engine::INPUTS, &[], &mut engine::Work::default()), Err(engine::Error::Point)); negatives += 1;
    assert!(matches!(engine::Bits::new(Box::new([])), Err(engine::Error::Framing))); negatives += 1;
    let mut w = engine::Work::default(); let u = vec![Fr::from(2u64); 22]; let v = vec![Fr::from(3u64); 22];
    assert_eq!(engine::line(&bits, &u[..21], &v, &mut w), Err(engine::Error::Point)); negatives += 1;
    assert_eq!(engine::line(&bits, &u, &v[..21], &mut w), Err(engine::Error::Point)); negatives += 1;
    // Complete boundary pairs: endpoint contributions sit on opposite window sides.
    let mut a = [Fr::zero(); 8]; let mut x = [Fr::zero(); 8]; let b = [Fr::zero(); 8];
    a[3] = Fr::from(2u64); a[4] = Fr::from(3u64); x[3] = Fr::from(5u64); x[4] = Fr::from(7u64);
    let total = crate::packed_gkr_window::quadratic(&a, &b, &x);
    let lo = crate::packed_gkr_window::quadratic(&a[..4], &b[..4], &x[..4]);
    let hi = crate::packed_gkr_window::quadratic(&a[4..], &b[4..], &x[4..]);
    assert_eq!(total, std::array::from_fn(|j| lo[j] + hi[j]));
    let pair = crate::packed_gkr_window::quadratic(&[Fr::from(2u64), Fr::from(3u64)], &[Fr::zero();2], &[Fr::from(5u64),Fr::from(7u64)]);
    let l = crate::packed_gkr_window::quadratic(&[Fr::from(2u64),Fr::zero()], &[Fr::zero();2], &[Fr::from(5u64),Fr::zero()]);
    let r = crate::packed_gkr_window::quadratic(&[Fr::zero(),Fr::from(3u64)], &[Fr::zero();2], &[Fr::zero(),Fr::from(7u64)]);
    assert_eq!(pair, [Fr::from(10u64),Fr::from(9u64),Fr::from(2u64)]);
    assert_ne!(pair, std::array::from_fn(|j| l[j]+r[j])); negatives += 1;
    // Phase2 must restart with the original bytes, rather than a phase1 scalar.
    let a = engine::folded(&bits, 0, &[Fr::from(2u64)], &mut engine::Work::default()).unwrap();
    let b = engine::folded(&bits, 0, &[Fr::from(3u64)], &mut engine::Work::default()).unwrap();
    assert_eq!((a,b), (Fr::from(2u64),Fr::from(3u64))); assert_ne!(a,b); negatives += 1;
    negatives
}

fn admission_controls(source: &engine::Source<'_, '_>, oracle: &[Term]) -> usize {
    let mut n = 0; let frame = source.frame(); let t = Transcript::new(b"role1-admission");
    for field in 0..10 {
        let mut bad = frame;
        match field { 0 => bad.headers += 1, 1 => bad.owners += 1, 2 => bad.owner_bits += 1,
            3 => bad.input_bits -= 1, 4 => bad.row_bits -= 1,
            5..=8 => bad.counts[field-5] -= 1, _ => bad.binding[0] ^= 1 }
        let calls = Cell::new(0); let before = counters(&t);
        let result = source.admit_frame(bad).map(|()| calls.set(calls.get()+1));
        assert_eq!(result, Err(if field==9 {engine::Error::Binding} else {engine::Error::Scope}), "frame{field}");
        assert_eq!(calls.get(),0); assert_eq!(counters(&t),before); n += 1;
    }
    let original = oracle.iter().find(|term| term.row >> 19 == 1 && term.gate.left % (1<<20) == 999423).unwrap();
    for field in 0..4 {
        let mut bad = original.clone();
        match field { 0 => bad.row = 0, 1 => bad.gate.left -= 1<<20, 2 => bad.gate.right -= 1<<20, _ => bad.row += 1<<19 }
        assert_eq!(engine::term_shape(&bad,1,None),Err(engine::Error::Coordinate(1)),"axis{field}"); n += 1;
    }
    assert_eq!(engine::term_shape(original,4,None),Err(engine::Error::Coordinate(4))); n += 1;
    assert_eq!(engine::term_shape(original,usize::MAX,None),Err(engine::Error::Coordinate(usize::MAX))); n += 1;
    assert_eq!(engine::term_shape(original,1,Some(original.row+1)),Err(engine::Error::Order(original.row))); n += 1;
    let mut rows = engine::RowCheck::default(); rows.push(1,Fr::one()).unwrap();
    assert_eq!(rows.push(2,-Fr::one()),Err(engine::Error::Residual(1))); n += 1;
    let mut rows = engine::RowCheck::default(); rows.push(1,Fr::one()).unwrap(); rows.push(1,-Fr::one()).unwrap(); rows.finish().unwrap();
    let mut rows = engine::RowCheck::default(); rows.push(1,Fr::one()).unwrap(); assert_eq!(rows.finish(),Err(engine::Error::Residual(1))); n += 1;
    let mut rows = engine::RowCheck::default(); rows.push(3,Fr::zero()).unwrap(); assert_eq!(rows.push(2,Fr::zero()),Err(engine::Error::Order(2))); n += 1;
    n
}

fn source_controls(source: &engine::Source<'_, '_>, bits: &engine::Bits, context: &ProofContext<'_>) -> usize {
    let mut n=0; let mut oracle=Vec::with_capacity(64); let mut census=[0usize;4]; let mut helpers=[0usize;4]; let mut c0=false;
    source.visit(|term| {
        let owner=term.row>>19; census[owner]+=1; let local=term.gate.left % (1<<20);
        if (356632..357305).contains(&(term.row % (1<<19))) {helpers[owner]+=1;}
        if matches!(local,999423|1000097) || matches!(local,999424|1000096) && owner>=2 || !c0 && !term.gate.c0.is_zero() {
            if !term.gate.c0.is_zero(){c0=true;} assert!(oracle.len()<64); oracle.push(term.clone());
        }
        Ok(())
    }).unwrap();
    assert_eq!(census,engine::CENSUS); assert_eq!(helpers,[0,0,673,673]); assert!(c0);
    assert_eq!(oracle.capacity(),64); assert_eq!(oracle.capacity()*size_of::<Term>(),9728);
    n+=admission_controls(source,&oracle);
    let before=oracle.iter().find(|t|t.gate.left==999423).unwrap();
    let after=oracle.iter().find(|t|t.gate.left==1000097).unwrap();
    for term in [before, oracle.iter().find(|t|t.gate.left==3*(1<<20)+1000097).unwrap()] {
        assert!(bits.bit(term.gate.left).is_zero());
        let mut bytes=bits.bytes().to_vec(); assert_eq!(bytes.capacity(),engine::BYTES);
        bytes[term.gate.left>>3]^=1<<(term.gate.left&7); let changed=engine::Bits::new(bytes.into_boxed_slice()).unwrap();
        let mut t=Transcript::new(b"role1-keeper-admission");let old=counters(&t);let probe=continuation(&t);let calls=Cell::new(0);
        let result=source.check(&changed,&mut engine::Work::default()).map(|()|{calls.set(1);t.append_bytes(b"must-not-bind",b"bad");});
        assert_eq!(result,Err(engine::Error::Residual(term.row)));assert_eq!(calls.get(),0);assert_eq!(counters(&t),old);assert_eq!(continuation(&t),probe);n+=1;
        drop(changed);
    }
    // Two actual zero-anchor rows, both changed to1; choose a nonBoolean output point that cancels them.
    assert!(bits.bit(before.gate.left).is_zero()&&bits.bit(after.gate.left).is_zero());
    let mut r=vec![Fr::from(2u64);21]; let differing=(0..21).find(|b|(before.row>>b)&1!=(after.row>>b)&1).unwrap();
    r[differing]=Fr::zero();let constant=eq(&r,before.row)+eq(&r,after.row);
    r[differing]=Fr::one();let endpoint=eq(&r,before.row)+eq(&r,after.row);
    r[differing]=-constant*(endpoint-constant).inverse().unwrap();
    assert!(!r[differing].is_zero()&&!r[differing].is_one());assert!(!eq(&r,before.row).is_zero());
    assert_eq!(eq(&r,before.row)+eq(&r,after.row),Fr::zero());
    let mut bytes=bits.bytes().to_vec();for term in [before,after]{bytes[term.gate.left>>3]^=1<<(term.gate.left&7);}
    let changed=engine::Bits::new(bytes.into_boxed_slice()).unwrap();
    assert_eq!(source.check(&changed,&mut engine::Work::default()),Err(engine::Error::Residual(before.row)));n+=1;drop(changed);
    // Actual owner1 formal right-zero: residue unchanged, polynomial C1 is2 versus-1.
    let term=oracle.iter().find(|t|t.gate.left==(1<<20)+999423).unwrap();let mut wrong=term.clone();wrong.gate.right-=1<<20;
    let r=boolean_point(21,term.row);let u=boolean_point(22,term.gate.left);let mut v=vec![Fr::zero();22];v[20]=Fr::from(2u64);
    assert!(bits.bit(term.gate.left).is_zero());assert_eq!(literal(term,&r,&u,&v)[1],Fr::from(2u64));assert_eq!(literal(&wrong,&r,&u,&v)[1],-Fr::one());n+=1;
    let term=oracle.iter().find(|t|!t.gate.c0.is_zero()).unwrap();let mut wrong=term.clone();wrong.gate.left^=1;
    let r=boolean_point(21,term.row);let u=boolean_point(22,term.gate.left);let v=boolean_point(22,term.gate.right);
    assert_eq!(literal(term,&r,&u,&v)[0],term.gate.c0);assert_eq!(literal(&wrong,&r,&u,&v)[0],Fr::zero());n+=1;
    let r=(2u64..23).map(Fr::from).collect::<Vec<_>>();let u=(29u64..51).map(Fr::from).collect::<Vec<_>>();let v=(61u64..83).map(Fr::from).collect::<Vec<_>>();
    let mut work=engine::Work::default();let rc=engine::Cache::new(&r,&mut work).unwrap();let uc=engine::Cache::new(&u,&mut work).unwrap();let vc=engine::Cache::new(&v,&mut work).unwrap();
    let actual=engine::terminal(source,&rc,&uc,&vc,&mut work).unwrap();assert_eq!(actual,context.coefficients(1,&r,&u,&v).unwrap());assert_eq!(work.terminal_terms,engine::TERMS as u64);
    let short=engine::Cache::new(&u[..21],&mut engine::Work::default()).unwrap();assert_eq!(engine::terminal(source,&rc,&short,&vc,&mut work),Err(engine::Error::Point));n+=1;
    assert_eq!(engine::terminal(source,&rc,&uc,&short,&mut work),Err(engine::Error::Point));n+=1;
    // Isolated omission/duplicate/sign and field placement over actual selected tuples.
    for term in &oracle {
        let coefficients=literal(term,&r,&u,&v);assert!(coefficients.iter().any(|x|!x.is_zero()));
        assert_ne!(std::array::from_fn::<_,4,_>(|j|actual[j]-coefficients[j]),actual,"omission");n+=1;
        assert_ne!(std::array::from_fn::<_,4,_>(|j|actual[j]+coefficients[j]),actual,"duplicate");n+=1;
        let mut wrong=term.clone();wrong.row^=1;assert_ne!(literal(&wrong,&r,&u,&v),coefficients,"row");n+=1;
        let mut wrong=term.clone();wrong.gate.left^=1;assert_ne!(literal(&wrong,&r,&u,&v),coefficients,"left");n+=1;
        let mut wrong=term.clone();wrong.gate.right^=1;assert_ne!(literal(&wrong,&r,&u,&v),coefficients,"right");n+=1;
        let neg=coefficients.map(|x|-x);assert_ne!(neg,coefficients,"sign");n+=1;
    }
    drop(short);drop(rc);drop(uc);drop(vc);drop(oracle);n
}

fn proof_controls(context:&ProofContext<'_>,artifact:&Artifact,key:&verifier_key::AdmittedVerifierKey,proof:&GkrProof)->usize {
    let verify=|p:&GkrProof|{let mut t=context.transcript(1,key,&artifact.commitment);gkr::verify_with_wiring(&[22],1<<21,p,&mut t,|t|context.bind_role(1,t),|_,r,u,v|context.coefficients(1,r,u,v).map_err(|_|GkrError::InvalidWireIndex))};
    let mut changed=proof.clone();changed.layers[0].rounds[0][0]+=Fr::one();assert_eq!(verify(&changed),Err(GkrError::SumcheckIdentity));drop(changed);
    let mut changed=proof.clone();changed.layers[0].right_value+=Fr::one();assert_eq!(verify(&changed),Err(GkrError::TerminalExpression));drop(changed);
    let mut changed=proof.clone();changed.layers[0].line_coefficients[1]+=Fr::one();assert_eq!(verify(&changed),Err(GkrError::LineEndpoints));drop(changed);
    let encoded=gkr::encode_proof(proof).unwrap();assert!(encoded.capacity()<=BUFFER);
    assert!(gkr::decode_dimensions(&[22],&encoded[..encoded.len()-1]).is_err());
    let mut extra=encoded;extra.push(0);assert!(extra.capacity()<=BUFFER);assert!(gkr::decode_dimensions(&[22],&extra).is_err());
    let mut t=context.transcript(0,key,&artifact.commitment);
    assert_eq!(gkr::verify_with_wiring(&[22],1<<21,proof,&mut t,|t|context.bind_role(1,t),|_,r,u,v|context.coefficients(1,r,u,v).map_err(|_|GkrError::InvalidWireIndex)),Err(GkrError::SumcheckIdentity),"wrong role transcript");
    let mut t=context.transcript(1,key,&artifact.commitment);
    assert_eq!(gkr::verify_with_wiring(&[22],1<<21,proof,&mut t,|t|context.bind_role(0,t),|_,r,u,v|context.coefficients(1,r,u,v).map_err(|_|GkrError::InvalidWireIndex)),Err(GkrError::SumcheckIdentity),"wrong role binder");7
}

fn coefficient_consumer_controls(context:&ProofContext<'_>,artifact:&Artifact,key:&verifier_key::AdmittedVerifierKey,proof:&GkrProof)->usize {
    // Borrow one genuine native anchor at a time; never collect the canonical circuit.
    let canonical=context.consumer.parent.header_boundary().canonical_circuit();
    for fault in 0..4 {
        // Fault3 removes the genuine retained last A4 row348440..356632, rather than changing MAX masking.
        let (local_row,local_wire,owner)=if fault==0 || fault==3 {(356631,999423,1)} else if fault==1 {(356632,999424,0)} else {(356632,999424,2)};
        let native=canonical.terms.iter().find(|term|term.row==local_row&&term.gate.left==local_wire).unwrap();
        assert_eq!((native.gate.right,native.gate.c0,native.gate.c1,native.gate.c2,native.gate.c3),(0,Fr::zero(),Fr::one(),Fr::zero(),Fr::zero()));
        let mut correct=native.clone();correct.row+=owner<<19;correct.gate.left+=owner<<20;correct.gate.right+=owner<<20;
        let mut wrong=correct.clone();if fault==0 {wrong.gate.right=0;}
        let mut t=context.transcript(1,key,&artifact.commitment);let calls=Cell::new(0);
        let result=gkr::verify_with_wiring(&[22],1<<21,proof,&mut t,|t|context.bind_role(1,t),|_,r,u,v|{
            let old=literal(&correct,r,u,v);
            let delta=if fault==0 {let changed=literal(&wrong,r,u,v);std::array::from_fn(|j|changed[j]-old[j])} else if fault==1 {old} else {old.map(|x|-x)};
            let layer=&proof.layers[0];
            assert!(!(delta[0]+delta[1]*layer.left_value+delta[2]*layer.right_value+delta[3]*layer.left_value*layer.right_value).is_zero(),"nonvacuous coefficient consumer fault{fault}");
            let coefficients=context.coefficients(1,r,u,v).map_err(|_|GkrError::InvalidWireIndex)?;calls.set(calls.get()+1);
            Ok(std::array::from_fn(|j|coefficients[j]+delta[j]))
        });
        assert_eq!(calls.get(),1);assert_eq!(result,Err(GkrError::TerminalExpression),"formalright / retained active MAX / retired helper / A4 mask omission fault{fault}");
    }4
}

#[derive(serde::Serialize)]
struct Diagnostic {
    schema:u64,input_bits:u64,row_bits:u64,owners:u64,owner0_terms:u64,owner1_terms:u64,owner2_terms:u64,owner3_terms:u64,
    source_terms:u64,packed_bytes:u64,window_bytes:u64,cache_modeled_peak_bytes:u64,line_stack_bytes:u64,
    validation_terms:u64,residual_terms:u64,fill_term_visits:u64,weighted_terms:u64,terminal_terms:u64,
    fold_leaves:u64,fold_muls:u64,line_bits:u64,line_ones:u64,line_updates:u64,cache_muls:u64,
    gkr_bytes:u64,gkr_scalars:u64,gkr_challenges:u64,negative_cases:u64,snapshot_reads:u64,snapshot_read_bytes:u64,
    consumer_us:u64,golden_verify_us:u64,snapshot_us:u64,controls_us:u64,candidate_us:u64,verify_us:u64,shared_pcs_verify_us:u64,
    witness_blake2b256:&'static str,proof_equal:bool,claim_equal:bool,trace_equal:bool,continuation_equal:bool,shared_pcs_pass:bool,
}

#[test]
#[ignore = "root-controlled N3 MAX packet; 2GiB group and120s capture required"]
fn retained_header_windows_match_accepted_max_packet() {
    check_native_bundle().unwrap();let dir=baseline_directory().unwrap();let public=Public::native(3).unwrap();
    let artifact=baseline_packet(&dir,&public).unwrap();let start=Instant::now();
    let consumer=Consumer::new(&public).unwrap();let context=ProofContext::new(&consumer).unwrap();
    let key=verifier_key::admit(22,include_bytes!("../fixtures/verifier-keys-v1/log22.vk")).unwrap();let consumer_us=us(start);
    let start=Instant::now();let original_claims=context.verify(&artifact,&key).unwrap();
    let golden=gkr::decode_dimensions(&[22],&artifact.roles[1].bytes).unwrap();
    let (golden_claim,golden_trace)=verify_trace(&context,&artifact,&key,&golden).unwrap();
    assert_eq!(golden_claim.point,original_claims[1].point);assert_eq!(golden_claim.value,original_claims[1].value);
    let golden_verify_us=us(start);let source=engine::Source::new(&context.adapter,&consumer.parent).unwrap();
    let packed=PackedFile::open(dir.join("witness.bits"),22).unwrap();let expected=pinned_bytes(&dir.join("witness.bits"),engine::BYTES,WITNESS_BLAKE).unwrap();
    let start=Instant::now();packed.reset_io_metrics();let bits=snapshot(&packed,&expected);drop(expected);let io=packed.io_metrics_snapshot();let snapshot_us=us(start);
    assert_eq!((io.read_calls,io.read_bytes,io.write_calls,io.sync_calls),(64,524288,0,0));
    let start=Instant::now();let mut negatives=cache_and_algebra_controls()+source_controls(&source,&bits,&context);
    let mut mismatch=bits.bytes().to_vec();assert_eq!(mismatch.capacity(),engine::BYTES);mismatch[0]^=1;
    assert_eq!(admit_snapshot(&mismatch,bits.bytes()),Err(engine::Error::Binding));negatives+=1;
    assert_eq!(admit_snapshot(&mismatch,&mismatch),Err(engine::Error::Binding));negatives+=1;drop(mismatch);
    assert_eq!(admit_snapshot(&bits.bytes()[..engine::BYTES-1],bits.bytes()),Err(engine::Error::Framing));negatives+=1;
    let controls_us=us(start);
    let start=Instant::now();let mut transcript=context.transcript(1,&key,&artifact.commitment);
    let (proof,claim,work)=engine::prove(&source,&bits,&mut transcript,|t|context.bind_role(1,t)).unwrap();let candidate_us=us(start);
    assert_eq!(work.window_bytes,25165824);assert!(work.cache_modeled_peak_bytes<=108016);
    assert_eq!((work.validation_terms,work.residual_terms,work.terminal_terms),(1584898,1584898,1584898));
    assert_eq!((work.fill_term_visits,work.weighted_terms),(152150208,69735512));
    assert_eq!((work.fold_leaves,work.fold_muls),(184549376,167772164));
    assert_eq!(work.line_bits,4194304);assert_eq!(work.line_updates,275*work.line_ones);
    assert_eq!(proof.layers[0].line_coefficients.len()*size_of::<Fr>(),736);
    let encoded=gkr::encode_proof(&proof).unwrap();assert!(encoded.capacity()<=BUFFER);assert_eq!(encoded.len(),5024);assert_eq!(encoded,artifact.roles[1].bytes);
    assert_eq!(proof,golden);assert_eq!(claim,golden_claim);assert_eq!(counters(&transcript),golden_trace.counters);assert_eq!(continuation(&transcript),golden_trace.continuation);
    let start=Instant::now();let (verified,trace)=verify_trace(&context,&artifact,&key,&proof).unwrap();assert_eq!(verified,claim);assert_eq!(trace,golden_trace);let verify_us=us(start);
    negatives+=proof_controls(&context,&artifact,&key,&proof);
    negatives+=coefficient_consumer_controls(&context,&artifact,&key,&proof);
    let mut joined=artifact.clone();joined.roles[1].bytes=encoded;let start=Instant::now();assert_eq!(context.verify(&joined,&key).unwrap(),original_claims);let shared_pcs_verify_us=us(start);
    let mut wrong=original_claims.clone();wrong[1].value+=Fr::one();let statement=consumer.statement(&artifact,&key,wrong).unwrap();
    let batch=opening_batch::decode_proof(&artifact.batch,22).unwrap();assert!(opening_batch::verify_admitted(&statement,&key,&batch).is_err());negatives+=1;
    drop(batch);drop(statement);drop(joined);drop(packed);drop(bits);drop(proof);drop(golden);
    let diagnostic=Diagnostic {schema:1,input_bits:22,row_bits:21,owners:4,owner0_terms:395888,owner1_terms:395888,owner2_terms:396561,owner3_terms:396561,
        source_terms:1584898,packed_bytes:524288,window_bytes:work.window_bytes,cache_modeled_peak_bytes:work.cache_modeled_peak_bytes,line_stack_bytes:1472,
        validation_terms:work.validation_terms,residual_terms:work.residual_terms,fill_term_visits:work.fill_term_visits,weighted_terms:work.weighted_terms,terminal_terms:work.terminal_terms,
        fold_leaves:work.fold_leaves,fold_muls:work.fold_muls,line_bits:work.line_bits,line_ones:work.line_ones,line_updates:work.line_updates,cache_muls:work.cache_muls,
        gkr_bytes:5024,gkr_scalars:157,gkr_challenges:66,negative_cases:negatives as u64,snapshot_reads:io.read_calls,snapshot_read_bytes:io.read_bytes,
        consumer_us,golden_verify_us,snapshot_us,controls_us,candidate_us,verify_us,shared_pcs_verify_us,witness_blake2b256:WITNESS_BLAKE,
        proof_equal:true,claim_equal:true,trace_equal:true,continuation_equal:true,shared_pcs_pass:true};
    let json=serde_json::to_string(&diagnostic).unwrap();assert!(json.len()<8192);
    print!("\nNIPOPOW_ROLE1_WINDOW_DIAG {json}\n");std::io::stdout().flush().unwrap();
}

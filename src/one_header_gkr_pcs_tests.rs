use crate::{one_header_gkr_pcs::*, gkr::{self, Gate, GkrError}, pcs,
    projection_aux_retirement::Authority, serializer, sparse::{self,Circuit,Term},
    transcript::Transcript, verifier_key};
use ark_bn254::{Bn254,Fr};
use ark_ec::{CurveGroup,pairing::Pairing};
use ark_ff::{Field,One,Zero};
use dory_pcs::backends::arkworks::{ArkG1,ArkG2,ArkGT,ArkworksVerifierSetup};
use ergo_header_core::{GroupElement,Header,PowSolution};
use std::{cell::Cell,io::{self,Write},mem::{size_of,size_of_val},time::Instant};

fn micros(t:Instant)->u64 { t.elapsed().as_micros().try_into().expect("u64 duration") }
fn fields()->serializer::Fields { serializer::Fields { version:4,parent_id:[0x11;32],
    ad_proofs_root:[0x22;32],transactions_root:[0x33;32],state_root:[0x44;33],timestamp:0,
    extension_root:[0x55;32],n_bits:0x043B9ACA,height:844672,votes:[0x66,0x77,0x88],
    pk:[0;33],w:[0;33],nonce:[1,2,3,4,5,6,7,8],payload_len:0,payload:[0;255] } }
fn native(f:&serializer::Fields)->Vec<u8> { Header{version:f.version,parent_id:f.parent_id,
    ad_proofs_root:f.ad_proofs_root,transactions_root:f.transactions_root,state_root:f.state_root,
    timestamp:f.timestamp,extension_root:f.extension_root,n_bits:f.n_bits,height:f.height,votes:f.votes,
    unparsed_bytes:vec![],pow:PowSolution::V2{pk:GroupElement::from_bytes(f.pk).unwrap(),nonce:f.nonce}}
    .encode().unwrap() }
fn word(x:&[Fr],rails:&[usize])->usize { rails.iter().enumerate().fold(0,|n,(b,w)|{
    assert!(x[*w].is_zero() || x[*w].is_one());n|((x[*w].is_one() as usize)<<b)}) }
fn codec_fixture(a:&Authority,x:&[Fr],f:&serializer::Fields) {
    assert_eq!(f.height as u64,OWNER+1,"fixture equality, not height authentication");
    let raw=native(f);let l=&a.serializer().layout;
    let len=word(x,&l.length);assert_eq!(len,raw.len());
    for i in 0..len { assert_eq!(word(x,&l.bytes[i]),raw[i] as usize); }
    assert!(x[a.used()..131072].iter().all(Fr::is_zero));
}

fn reject(a:&Authority,d:&Descriptor,p:&[usize],r:&[usize],id:&[u8;32],e:Error) {
    let calls=Cell::new(0);
    let result=with_input(a,d,p,r,id,&[],||calls.set(calls.get()+1));
    assert_eq!(result,Err(e));assert_eq!(calls.get(),0,"before framing/callback/challenge");
}
fn metadata(a:&Authority)->(usize,usize) {
    let d=Descriptor::canonical(a);let p=placements();let r=rows();let mut count=0;
    for i in 0..36 { let mut bad=d.clone();bad.words[i]+=1;
        reject(a,&bad,&p,&r,&SETUP_ID,Error::Word(i));count+=1; }
    for i in 0..8 { for b in 0..32 { let mut bad=d.clone();bad.pins[i][b]^=1;
        reject(a,&bad,&p,&r,&SETUP_ID,Error::Pin(i));count+=1; } }
    for b in 0..32 { let mut bad=SETUP_ID;bad[b]^=1;
        reject(a,&d,&p,&r,&bad,Error::Setup(b));count+=1; }
    assert_eq!(count,324);
    for i in 0..419 { let mut bad=p;bad[i]+=1;
        reject(a,&d,&bad,&r,&SETUP_ID,Error::Placement(i)); }
    for i in [0,383,384,415,416,417,418] {
        let missing:[usize;418]=std::array::from_fn(|j|p[j+usize::from(j>=i)]);
        reject(a,&d,&missing,&r,&SETUP_ID,Error::PlacementLength);
        let mut duplicate=p;duplicate[i]=p[usize::from(i==0)];
        reject(a,&d,&duplicate,&r,&SETUP_ID,Error::Placement(i));
    }
    for i in 0..9 { let mut bad=r;bad[i]+=1;reject(a,&d,&p,&bad,&SETUP_ID,Error::Rows(i)); }
    let mut interchange=r;interchange.swap(2,4);
    reject(a,&d,&p,&interchange,&SETUP_ID,Error::Rows(2));
    reject(a,&d,&p,&r[..8],&SETUP_ID,Error::RowLength);
    reject(a,&d,&p,&r,&SETUP_ID,Error::Framing);
    assert!(p.windows(2).all(|w|w[0]<w[1]));assert_eq!((p[0],p[418]),(131072,131490));
    let bytes=d.bytes();assert_eq!(bytes.len(),584);
    for i in 0..36 { assert_eq!(&bytes[8*i..8*i+8],&d.words[i].to_le_bytes()); }
    for i in 0..8 { assert_eq!(&bytes[288+32*i..320+32*i],&d.pins[i]); }
    assert_eq!(&bytes[544..],pcs::VENDOR_PIN);(count,419)
}

/// Independent literal coordinate contract, not a call to the production mapper.
fn literal_terms(a:&Authority,mut emit:impl FnMut(Term)) {
    for t in &a.serializer().circuit.terms { emit(t.clone()); }
    let axis=|w:usize| { if w<a.used() {w} else {
        assert!((a.used()..a.used()+384).contains(&w));131072+w-a.used() } };
    for t in &a.projection().circuit.terms { emit(Term{row:262144+t.row,gate:Gate{
        left:axis(t.gate.left),right:axis(t.gate.right),
        c0:t.gate.c0,c1:t.gate.c1,c2:t.gate.c2,c3:t.gate.c3}}); }
    for b in 0..32 { emit(Term{row:263319+b,gate:Gate{left:1362+b,right:131490,
        c0:Fr::zero(),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()}});
        emit(Term{row:263319+b,gate:Gate{left:131456+b,right:131490,
        c0:Fr::zero(),c1:-Fr::one(),c2:Fr::zero(),c3:Fr::zero()}}); }
    for (i,j) in [0,385].into_iter().enumerate() {
        let g=&a.certificate()[j].gate;
        assert_eq!((a.certificate()[j].row,g.left,g.right),(12835+j,655627+j,0));
        emit(Term{row:263351+i,gate:Gate{left:131488+i,right:131490,
            c0:g.c0,c1:g.c1,c2:g.c2,c3:g.c3}});
    }
}
fn source_oracle(a:&Authority,c:&Compact) {
    let mut cursor=0;let mut channels=[0usize;4];let mut serializer_channels=[0usize;4];
    literal_terms(a,|t| {
        assert_eq!(c.circuit().terms[cursor],t,"source ordered tuple {cursor}");
        for (j,x) in [t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3].iter().enumerate() {
            channels[j]+=usize::from(!x.is_zero());
            if cursor<315546 {serializer_channels[j]+=usize::from(!x.is_zero());}
        }cursor+=1;
    });
    assert_eq!(cursor,317991);
    assert_eq!(channels,std::array::from_fn(|j|serializer_channels[j]+[1,1485,302,1897][j]));
    let actual_serializer: [usize;4]=std::array::from_fn(|j|a.serializer().circuit.terms.iter()
        .filter(|t|![t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3][j].is_zero()).count());
    assert_eq!(serializer_channels,actual_serializer);
    assert!(c.circuit().terms.windows(2).all(|t|t[0].row<=t[1].row));
    assert_eq!(c.circuit().terms.last().unwrap().row,263352);
    assert!(!c.circuit().terms.iter().any(|t|t.row>=263353));
}
fn eq(p:&[Fr],index:usize)->Fr { p.iter().enumerate().fold(Fr::one(),|w,(b,t)|
    w*if (index>>b)&1==1 {*t} else {Fr::one()-t}) }
fn weights(p:&[Fr])->Vec<Fr> {
    // Direct Boolean-index definition, independent of the production doubling loop.
    let mut out=Vec::with_capacity(1<<p.len());
    for i in 0..1<<p.len() {out.push(eq(p,i));}out
}
fn bits(i:usize,n:usize)->Vec<Fr> {(0..n).map(|b|Fr::from(((i>>b)&1) as u64)).collect()}
fn wiring(a:&Authority,c:&Compact) {
    let shape=sparse::validate(c.circuit(),0).unwrap();
    for seed in [2u64,5] {
        let r:Vec<_>=(0..19).map(|b|Fr::from(seed+b as u64)).collect();
        let u:Vec<_>=(0..18).map(|b|Fr::from(seed+2*b as u64)/Fr::from(3)).collect();
        let v:Vec<_>=(0..18).map(|b|Fr::from(seed+3*b as u64)/Fr::from(5)).collect();
        let wr=weights(&r);let wu=weights(&u);let wv=weights(&v);
        assert_eq!((wr.capacity(),wu.capacity(),wv.capacity()),(R,N,N));
        let mut expected=[Fr::zero();4];literal_terms(a,|t|{
            let w=wr[t.row]*wu[t.gate.left]*wv[t.gate.right];
            for (j,x)in [t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3].iter().enumerate(){expected[j]+=w*x;}
        });
        drop(wr);drop(wu);drop(wv);
        assert_eq!(sparse::wiring(c.circuit(),&shape,&r,&u,&v).unwrap(),expected);
        assert!(!expected[2].is_zero(),"c2 survives nonBoolean wiring");
    }
    // Exactly one formal right-axis substitution. Ordinary residues cannot see it.
    let original=c.circuit().terms[315546+2379].clone();
    assert_eq!((original.row,original.gate.left,original.gate.right),(ALIASES,1362,FORMAL));
    let mut collapsed=original.clone();collapsed.gate.right=0;
    let r=bits(ALIASES,19);let u=bits(1362,18);let v=bits(FORMAL,18);
    assert_eq!(eq(&r,original.row)*eq(&u,original.gate.left)*eq(&v,original.gate.right),Fr::one());
    assert_eq!(eq(&v,collapsed.gate.right),Fr::zero());
    let tiny=Circuit{input_len:N,row_count:R,terms:vec![original]};
    let s=sparse::validate(&tiny,0).unwrap();
    assert_eq!(sparse::wiring(&tiny,&s,&r,&u,&v).unwrap(),[Fr::zero(),Fr::one(),Fr::zero(),Fr::zero()]);
    let changed=Circuit{input_len:N,row_count:R,terms:vec![collapsed]};
    assert_eq!(sparse::wiring(&changed,&s,&r,&u,&v).unwrap(),[Fr::zero();4]);
}
fn ordinary_faults(a:&Authority,c:&Compact,x:&mut [Fr]) {
    c.check(x).unwrap();
    // Fr2 auxiliary, first/final decoder, two retained neighbors, serialized RAW bit.
    let aux=(AUX..DECODER).find(|w|x[*w].is_one()).expect("nonzero genuine projection aux");
    let raw=a.serializer().layout.bytes[0][0];
    for (wire,expected) in [(aux,None),(DECODER,Some(ALIASES)),(DECODER+31,Some(ALIASES+31)),
        (NEIGHBOR_INPUT,Some(NEIGHBORS)),(NEIGHBOR_INPUT+1,Some(NEIGHBORS+1)),(raw,None)] {
        let old=x[wire];x[wire]=if wire==aux {Fr::from(2)} else {Fr::one()-old};
        if let Some(row)=expected {assert_eq!(c.check(x),Err(Error::Residual(row)));}
        else {assert!(matches!(c.check(x),Err(Error::Residual(_))));}
        let mut t=Transcript::new(DOMAIN);
        assert_eq!(sparse::prove(c.circuit(),x,0,&mut t).err(),Some(GkrError::NonzeroOutput));
        assert_eq!(t.challenges(),0,"ordinary reject before aggregation challenge");x[wire]=old;
    }
    let alias=&c.circuit().terms[315546+2379];let mut collapsed=alias.gate.clone();collapsed.right=0;
    assert_eq!(alias.gate.evaluate(x),collapsed.evaluate(x));
    assert_eq!(c.check(&x[..N-1]),Err(Error::Framing));
    let first=&a.projection().circuit.terms[0];let second=&a.projection().circuit.terms[1];
    assert_eq!((first.row,second.row),(0,1));
    let mut gates=vec![first.clone(),second.clone()];
    for t in &mut gates {t.row+=PROJECTION;}
    let tiny=Circuit{input_len:4,row_count:R,terms:gates};let invalid=[Fr::from(2),Fr::from(2),Fr::zero(),Fr::zero()];
    assert_eq!(tiny.terms[0].gate.evaluate(&invalid),Fr::from(2));
    assert_eq!(tiny.terms[1].gate.evaluate(&invalid),Fr::one());
    let mut r=bits(PROJECTION,19);r[0]=Fr::from(2);
    let add0=eq(&r,PROJECTION)*Fr::from(2);let add1=eq(&r,PROJECTION+1);
    assert_eq!((add0,add1),(-Fr::from(2),Fr::from(2)));assert_eq!(add0+add1,Fr::zero());
    let mut t=Transcript::new(DOMAIN);
    assert_eq!(sparse::prove(&tiny,&invalid,0,&mut t).err(),Some(GkrError::NonzeroOutput));
    assert_eq!(t.challenges(),0);c.check(x).unwrap();
}
fn resources(a:&Authority,c:&Compact,x:&Vec<Fr>) {
    assert_eq!((size_of::<Fr>(),size_of::<Term>(),size_of::<ArkG1>(),size_of::<ArkG2>(),size_of::<ArkGT>()),(32,152,96,192,384));
    let r=a.resources();assert!(r.core_terms<=172864);
    assert_eq!((r.serializer_terms,r.boundary_terms),(315546,419961));
    assert!(r.core_capacity<=262144 && r.serializer_capacity<=524288 && r.boundary_capacity<=524288);
    assert!(r.projection_capacity<=4096);assert_eq!(r.certificate_capacity,386);
    assert_eq!((c.circuit().terms.len(),c.circuit().terms.capacity()),(TERMS,TERMS));
    assert_eq!((x.len(),x.capacity()),(N,N));assert_eq!(TERMS*size_of::<Term>(),48334632);
    // Models are logical payload bounds, not sampled process RSS.
    assert!(372usize*1024*1024<512usize*1024*1024);
    assert!(94221696usize+48334632+68*1024*1024+3*8*1024*1024+32*1024*1024+5*1024*1024<512*1024*1024);
}

fn gkr_controls(c:&Compact,statement:&Statement,p:&gkr::GkrProof,bytes:&[u8]) {
    for which in 0..6 {let mut bad=p.clone();let l=&mut bad.layers[0];match which {
        0=>l.rounds[0][0]+=Fr::one(),1=>l.rounds[35][0]+=Fr::one(),
        2=>l.left_value+=Fr::one(),3=>l.line_coefficients[0]+=Fr::one(),
        4=>{l.rounds.pop();},_=>{l.line_coefficients.pop();},
    }
    assert!(sparse::verify(c.circuit(),0,&bad,&mut statement.transcript()).is_err());}
    let mut bad=p.clone();bad.layers[0].right_value+=Fr::one();
    assert!(sparse::verify(c.circuit(),0,&bad,&mut statement.transcript()).is_err());drop(bad);
    let mut bad=p.clone();bad.layers[0].line_coefficients[1]+=Fr::one();
    assert_eq!(sparse::verify(c.circuit(),0,&bad,&mut statement.transcript()).err(),Some(GkrError::LineEndpoints));drop(bad);
    let mut bad=p.clone();bad.layers[0].rounds[0].push(Fr::zero());
    assert!(sparse::verify(c.circuit(),0,&bad,&mut statement.transcript()).is_err());drop(bad);
    let empty=gkr::GkrProof{layers:vec![]};
    assert!(sparse::verify(c.circuit(),0,&empty,&mut statement.transcript()).is_err());
    assert!(sparse::decode_proof(c.circuit(),0,&bytes[..bytes.len()-1]).is_err());
    let mut trailing=Vec::with_capacity(bytes.len()+1);trailing.extend_from_slice(bytes);trailing.push(0);
    assert!(sparse::decode_proof(c.circuit(),0,&trailing).is_err());drop(trailing);
    assert!(sparse::decode_proof(c.circuit(),1,bytes).is_err());
    let mut t=statement.transcript();t.append_bytes(b"compact-descriptor",b"wrong canonical statement");
    assert!(sparse::verify(c.circuit(),0,p,&mut t).is_err());
}
fn key_controls(key:&verifier_key::AdmittedVerifierKey) {
    assert!(verifier_key::admit(17,KEY).is_err());
    assert!(verifier_key::admit(18,&KEY[..KEY.len()-1]).is_err());
    let mut trailing=Vec::with_capacity(KEY.len()+1);trailing.extend_from_slice(KEY);trailing.push(0);
    assert!(verifier_key::admit(18,&trailing).is_err());drop(trailing);
    let mut wrong=key.verifier().clone();wrong.chi[0]=wrong.chi[1];
    let bytes=pcs::encode(&ArkworksVerifierSetup(wrong)).unwrap();
    assert_eq!(bytes.len(),KEY.len());assert_ne!(bytes,KEY);
    assert!(verifier_key::admit(18,&bytes).is_err());
}

#[test]
fn serializer_projection_claim_opens_same_compact_witness() {
    let a=Authority::build().unwrap();let (metadata_count,mapping_count)=metadata(&a);
    assert_eq!((metadata_count,mapping_count),(324,419));
    let c=Compact::build(&a,&Descriptor::canonical(&a),&placements(),&rows(),&SETUP_ID).unwrap();
    source_oracle(&a,&c);wiring(&a,&c);
    let f=fields();let mut x=assign(&a,&f).unwrap();codec_fixture(&a,&x,&f);
    with_input(&a,c.descriptor(),&placements(),&rows(),&SETUP_ID,&x,||()).unwrap();
    resources(&a,&c,&x);ordinary_faults(&a,&c,&mut x);
    // Coherent fields/RAW/projection/decoder changes remain valid in this local relation.
    let mut variant=fields();variant.n_bits=0x05174876;
    let alternative=assign(&a,&variant).unwrap();assert_ne!(native(&variant),native(&f));
    codec_fixture(&a,&alternative,&variant);c.check(&alternative).unwrap();drop(alternative);
    let source_capacities=(a.serializer().circuit.terms.capacity(),a.projection().circuit.terms.capacity(),a.resources().certificate_capacity);
    drop(a); // no assignments or recipe/compiler buffers retained into cryptographic stages
    let mut times=Timings{setup:0,commit:0,gkr_prove:0,gkr_codec:0,gkr_verify:0,
        pcs_open:0,pcs_codec:0,key_admit:0,pcs_verify:0,snapshot_commit:0,snapshot_open:0};
    let now=Instant::now();let setup=pcs::generate_setup(18).unwrap();times.setup=micros(now);
    assert_eq!(setup.id,SETUP_ID);assert_eq!(setup.log_n,18);
    assert_eq!((setup.prover.g1_vec.len(),setup.prover.g2_vec.len()),(512,512));
    let prepared:<Bn254 as Pairing>::G2Prepared=setup.prover.g2_vec[0].0.into_affine().into();
    assert_eq!(prepared.ell_coeffs.len(),87);assert!(prepared.ell_coeffs.capacity()<=128);
    assert_eq!(size_of_val(&prepared.ell_coeffs[0]),192);drop(prepared);
    let now=Instant::now();let key=verifier_key::admit(18,KEY).unwrap();let preliminary_key_us=micros(now);
    assert_eq!(key.id(),&setup.id);assert_eq!(key.log_n(),18);assert_eq!(KEY.len(),19824);
    assert_eq!(pcs::encode(&ArkworksVerifierSetup(setup.verifier.clone())).unwrap(),KEY);
    key_controls(&key);
    let now=Instant::now();let committed=pcs::commit(&x,&setup).unwrap();times.commit=micros(now);
    assert_eq!((committed.rows.len(),committed.rows.capacity()),(512,512));
    let row_capacity=committed.rows.capacity();let commitment_bytes=pcs::encode_commitment(&committed.commitment).unwrap();
    assert_eq!(commitment_bytes.len(),384);
    let statement=c.statement(setup.id,&commitment_bytes,&commitment_bytes).unwrap();
    let mut producer=statement.transcript();let mut preliminary=statement.transcript();
    let now=Instant::now();let (proof,claim)=sparse::prove(c.circuit(),&x,0,&mut producer).unwrap();times.gkr_prove=micros(now);
    assert_eq!(producer.challenges(),56);assert_eq!(claim.point.len(),18);
    assert_eq!(proof.layers.len(),1);assert_eq!(proof.layers[0].rounds.len(),36);
    assert_eq!(proof.layers[0].line_coefficients.len(),19);
    assert_eq!(gkr::mle(&x,&claim.point).unwrap(),claim.value);
    let now=Instant::now();let gkr_bytes=gkr::encode_proof(&proof).unwrap();
    let decoded=sparse::decode_proof(c.circuit(),0,&gkr_bytes).unwrap();
    assert_eq!(decoded,proof);assert_eq!(gkr::encode_proof(&decoded).unwrap(),gkr_bytes);times.gkr_codec=micros(now);
    assert_eq!(gkr_bytes.len(),4128);assert_eq!(gkr_bytes.len()/32,129);
    let verified=sparse::verify(c.circuit(),0,&decoded,&mut preliminary).unwrap();
    assert_eq!(verified,claim);assert_eq!(preliminary.challenges(),56);
    let continuation=preliminary.clone();
    let mut prefix1=producer.clone();let mut prefix2=continuation.clone();
    assert_eq!(prefix1.challenge_scalar(b"same-post-gkr-prefix"),prefix2.challenge_scalar(b"same-post-gkr-prefix"));
    gkr_controls(&c,&statement,&decoded,&gkr_bytes);drop(proof);drop(decoded);
    let now=Instant::now();let opening=pcs::open(&committed,&claim.point,&setup,&mut producer).unwrap();times.pcs_open=micros(now);
    assert_eq!((opening.nu,opening.sigma,opening.first_messages.len(),opening.second_messages.len()),(9,9,9,9));
    let now=Instant::now();let pcs_bytes=pcs::encode_proof(&opening).unwrap();
    let decoded_opening=pcs::decode_proof(&pcs_bytes,18).unwrap();
    assert_eq!(pcs::encode_proof(&decoded_opening).unwrap(),pcs_bytes);times.pcs_codec=micros(now);
    assert_eq!(pcs_bytes.len(),24237);assert_eq!(pcs_bytes.len()+gkr_bytes.len(),28365);
    pcs::verify_admitted(statement.commitment(),verified.value,&verified.point,&decoded_opening,&key,&mut continuation.clone()).unwrap();
    // Three independent actual consumer faults; reuse the same honest continuation.
    assert!(pcs::verify_admitted(statement.commitment(),verified.value+Fr::one(),&verified.point,
        &decoded_opening,&key,&mut continuation.clone()).is_err());
    let mut wrong_point=verified.point.clone();wrong_point[0]+=Fr::one();
    assert!(pcs::verify_admitted(statement.commitment(),verified.value,&wrong_point,
        &decoded_opening,&key,&mut continuation.clone()).is_err());drop(wrong_point);
    let wrong_commitment=ArkGT::default();assert_ne!(wrong_commitment,statement.commitment());
    assert!(pcs::verify_admitted(wrong_commitment,verified.value,&verified.point,
        &decoded_opening,&key,&mut continuation.clone()).is_err());
    assert!(pcs::decode_proof(&pcs_bytes[..pcs_bytes.len()-1],18).is_err());
    let mut trailing=Vec::with_capacity(pcs_bytes.len()+1);trailing.extend_from_slice(&pcs_bytes);trailing.push(0);
    assert!(pcs::decode_proof(&trailing,18).is_err());drop(trailing);
    assert!(pcs::decode_proof(&pcs_bytes,17).is_err());
    let mut bad_rounds=pcs_bytes.clone();bad_rounds[800..804].copy_from_slice(&u32::MAX.to_le_bytes());
    assert!(pcs::decode_proof(&bad_rounds,18).is_err());drop(bad_rounds);
    assert!(pcs::decode_commitment(&commitment_bytes[..383]).is_err());
    drop(opening);drop(decoded_opening);drop(committed); // one dense committed polynomial at a time
    let mut changed=x.clone();assert_eq!(changed.capacity(),N);changed[INPUT_USED]=Fr::one();c.check(&changed).unwrap();
    let changed_value=gkr::mle(&changed,&verified.point).unwrap();
    assert_ne!(changed_value,verified.value,"snapshot mutant must be decisive");
    let now=Instant::now();let snapshot=pcs::commit(&changed,&setup).unwrap();times.snapshot_commit=micros(now);
    assert_ne!(snapshot.commitment,statement.commitment());
    let changed_bytes=pcs::encode_commitment(&snapshot.commitment).unwrap();
    assert_eq!(c.statement(SETUP_ID,&changed_bytes,&commitment_bytes).err(),Some(Error::Commitment));
    let now=Instant::now();let snapshot_proof=pcs::open(&snapshot,&verified.point,&setup,&mut continuation.clone()).unwrap();
    times.snapshot_open=micros(now);
    let snapshot_bytes=pcs::encode_proof(&snapshot_proof).unwrap();
    let snapshot_decoded=pcs::decode_proof(&snapshot_bytes,18).unwrap();
    pcs::verify_admitted(snapshot.commitment,changed_value,&verified.point,&snapshot_decoded,&key,&mut continuation.clone()).unwrap();
    // ONLY value is changed here: C', point, proof, key and transcript are identical.
    assert!(pcs::verify_admitted(snapshot.commitment,verified.value,&verified.point,
        &snapshot_decoded,&key,&mut continuation.clone()).is_err());
    drop(snapshot_decoded);drop(snapshot_bytes);drop(snapshot_proof);drop(snapshot);
    drop(setup);drop(changed);let input_capacity=x.capacity();drop(x);drop(key);
    // Final measured consumer has no witness, polynomial, recipe or prover setup.
    let now=Instant::now();let decoded=sparse::decode_proof(c.circuit(),0,&gkr_bytes).unwrap();
    let mut consumer=statement.transcript();
    let final_claim=sparse::verify(c.circuit(),0,&decoded,&mut consumer).unwrap();times.gkr_verify=micros(now);
    assert_eq!(final_claim,verified);assert_eq!(consumer.challenges(),56);
    let now=Instant::now();let final_key=verifier_key::admit(18,KEY).unwrap();times.key_admit=micros(now);
    let final_opening=pcs::decode_proof(&pcs_bytes,18).unwrap();
    let now=Instant::now();pcs::verify_admitted(statement.commitment(),final_claim.value,
        &final_claim.point,&final_opening,&final_key,&mut consumer).unwrap();times.pcs_verify=micros(now);
    // Preliminary key duration is deliberately excluded from final key_admit.
    let _=preliminary_key_us;
    let diagnostic=Diagnostic{schema:"one-header-gkr-pcs-v1".into(),status:"PASS".into(),proof:true,pcs:true,setup:true,
        log_n:18,row_log:19,log_copies:0,terms:TERMS,input_used:INPUT_USED,input_extent:N,
        rows_used:ROWS_USED,row_extent:R,gkr_challenges:56,gkr_scalars:129,gkr_bytes:gkr_bytes.len(),
        dory_rounds:9,dory_bytes:pcs_bytes.len(),commitment_bytes:commitment_bytes.len(),key_bytes:KEY.len(),descriptor_bytes:584,
        setup_id:SETUP_ID.iter().map(|b|format!("{b:02x}")).collect(),timings_us:times,
        capacities:Capacities{compact_input:input_capacity,compact_terms:c.circuit().terms.capacity(),
            serializer_terms:source_capacities.0,projection_terms:source_capacities.1,certificate_terms:source_capacities.2,
            committed_rows:row_capacity,fr_size:size_of::<Fr>(),term_size:size_of::<Term>(),
            g1_size:size_of::<ArkG1>(),g2_size:size_of::<ArkG2>(),gt_size:size_of::<ArkGT>()},
        modeled_bytes:Modeled{source_compile_peak:372*1024*1024,source_retained:94221696,
            sparse_fr_peak:68*1024*1024,pairing_scratch:32*1024*1024,msm_scratch:2*1024*1024,
            dory_state:2*1024*1024,codec_setup_scratch:1024*1024,payload_ceiling:512*1024*1024},
        verdicts:Verdicts{ordinary:true,pipeline:true,snapshot_reject:true,metadata:true,compact_mapping:true,wiring:true,codec:true}};
    let json=serde_json::to_string(&diagnostic).unwrap();assert!(json.len()<=8192);
    let roundtrip:Diagnostic=serde_json::from_str(&json).unwrap();assert_eq!(serde_json::to_string(&roundtrip).unwrap(),json);
    let mut extra:serde_json::Value=serde_json::from_str(&json).unwrap();extra["unexpected"]=true.into();
    assert!(serde_json::from_value::<Diagnostic>(extra).is_err());
    // One stdout operation starts a fresh line under libtest's pending test header.
    let line=format!("\nONE_HEADER_GKR_PCS_DIAGNOSTIC_V1 {json}\n");
    let mut stdout=io::stdout().lock();stdout.write_all(line.as_bytes()).unwrap();stdout.flush().unwrap();
}

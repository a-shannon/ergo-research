use super::*;
use ark_ff::Zero;
use crate::gkr::LayerProof;

fn generator(prefix:u8)->[u8;33] {
    let hex="79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798";
    let mut out=[0;33];out[0]=prefix;
    for i in 0..32 {out[i+1]=u8::from_str_radix(&hex[2*i..2*i+2],16).unwrap();}out
}
fn same_transcript(a:&Transcript,b:&Transcript) {
    assert_eq!((a.challenges(),a.raw_queries(),a.bytes_absorbed()),(b.challenges(),b.raw_queries(),b.bytes_absorbed()));
    assert_eq!(a.clone().try_challenge_scalar(b"c568-continuation").unwrap(),
        b.clone().try_challenge_scalar(b"c568-continuation").unwrap());
}
fn residuals(c:&Circuit,x:&[Fr])->Vec<Fr> {
    let mut rows=vec![Fr::zero();c.row_count];
    for t in &c.terms {rows[t.row]+=t.gate.evaluate(x);}rows
}
fn admitted_key(log:usize)->AdmittedVerifierKey {verifier_key::admit(log,pinned_bytes(log).unwrap()).unwrap()}
fn commitment()->Vec<u8> {
    pcs::encode_commitment(&ArkGT(ark_ec::pairing::PairingOutput::<ark_bn254::Bn254>::zero())).unwrap()
}
fn eq_literal(point:&[Fr],mut index:usize)->Fr {
    let mut out=Fr::one();
    for z in point {out*=if index%2==0 {Fr::one()-z}else{*z};index/=2;}
    assert_eq!(index,0);out
}
fn low_fold(c:&Circuit,r:&[Fr],u:&[Fr],v:&[Fr])->[Fr;4] {
    let mut out=[Fr::zero();4];
    for t in &c.terms {
        let g=&t.gate;let w=eq_literal(r,t.row)*eq_literal(u,g.left)*eq_literal(v,g.right);
        for (sum,c) in out.iter_mut().zip([g.c0,g.c1,g.c2,g.c3]) {*sum+=w*c;}
    }out
}
fn low_point(n:usize,start:u64)->Vec<Fr> {(0..n).map(|i|Fr::from(start+i as u64)).collect()}
fn high_point(g:usize,base:usize,free:&[usize],start:u64)->Vec<Fr> {
    (0..g).map(|bit|if free.contains(&bit){Fr::from(start+bit as u64)}else{Fr::from(((base>>bit)&1)as u64)}).collect()
}
fn support(base:usize,free:&[usize])->Vec<usize> {
    (0..1usize<<free.len()).map(|mask|free.iter().enumerate().fold(base,|owner,(i,bit)|
        if mask>>i&1==1{owner|1<<bit}else{owner&!(1<<bit)})).collect()
}

#[test]
fn c568_fast_native_codec_membership_infinity_and_single_cell_controls() {
    let c=point_membership::build().unwrap();
    for (pk,w) in [(generator(2),generator(3)),([0;33],generator(2)),(generator(3),[0;33]),([0;33],[0;33])] {
        ergo_header_core::GroupElement::from_bytes(pk).unwrap();
        ergo_header_core::GroupElement::from_bytes(w).unwrap();
        let bits=point_membership::witness(pk,w).unwrap();
        let values:Vec<_>=bits.iter().map(|b|Fr::from(*b as u64)).collect();
        assert!(residuals(&c.circuit,&values).iter().all(Zero::is_zero));
        for wire in [c.layout.points[0].y[0],c.layout.points[0].quotients[0][0],point_membership::USED_BITS] {
            let mut bad=values.clone();bad[wire]=Fr::one()-bad[wire];
            assert!(residuals(&c.circuit,&bad).iter().any(|z|!z.is_zero()),"wire {wire}");
        }
        let mut non_boolean=values.clone();non_boolean[point_membership::USED_BITS]=Fr::from(2u8);
        assert!(!residuals(&c.circuit,&non_boolean)[c.layout.boolean_rows.start+point_membership::USED_BITS].is_zero());
        let mut parity=values.clone();let y=c.layout.points[0].y[0];parity[y]=Fr::one()-parity[y];
        assert!(!residuals(&c.circuit,&parity)[c.layout.points[0].rows.parity].is_zero());
    }
    let mut malformed=[0;33];malformed[32]=1;
    let mut nonresidue=[0;33];nonresidue[0]=2;
    let mut modulus=[0;33];modulus[0]=2;modulus[1..].copy_from_slice(&point_membership::modulus().to_bytes_be());
    for pk in [malformed,nonresidue,modulus] {
        assert!(ergo_header_core::GroupElement::from_bytes(pk).is_err());
        assert!(point_membership::witness(pk,[0;33]).is_err());
    }
}

#[test]
fn c568_fast_arbitrary_field_sparse_high_wiring_and_original_x_projection() {
    let c=point_membership::build().unwrap();
    for (g,n,free) in [(2,3,vec![0,1]),(21,1_827_840,vec![0,10,20])] {
        let math=PointMath::dimensions(&c.circuit,g,13+g,14+g,20+g).unwrap();
        let base=n-1;let owners=support(base,&free);
        assert_eq!(owners.len(),if g==2{4}else{8});
        let (rh,uh,vh)=(high_point(g,base,&free,2),high_point(g,base,&free,31),high_point(g,base,&free,71));
        let (rl,ul,vl)=(low_point(14,3),low_point(13,29),low_point(13,61));
        let high=owners.iter().fold(Fr::zero(),|sum,o|sum+eq_literal(&rh,*o)*eq_literal(&uh,*o)*eq_literal(&vh,*o));
        let mut expected=low_fold(&c.circuit,&rl,&ul,&vl);for value in &mut expected {*value*=high;}
        let r=[rl.clone(),rh].concat();let u=[ul.clone(),uh].concat();let v=[vl.clone(),vh].concat();
        assert_eq!(math.coefficients(&r,&u,&v).unwrap(),expected);
        assert!(math.coefficients(&r[..r.len()-1],&u,&v).is_err());
        let term=&c.circuit.terms[0];let w=eq_literal(&rl,term.row)*eq_literal(&ul,term.gate.left)*eq_literal(&vl,term.gate.right)*high;
        let cs=[term.gate.c0,term.gate.c1,term.gate.c2,term.gate.c3];
        let mut omitted=expected;for(j,c)in cs.into_iter().enumerate(){omitted[j]-=w*c;}assert_ne!(omitted,expected);
        let mut repeated=expected;for(j,c)in cs.into_iter().enumerate(){repeated[j]+=w*c;}assert_ne!(repeated,expected);
        let wrong=eq_literal(&rl,term.row)*eq_literal(&ul,term.gate.left)*eq_literal(&vl,term.gate.right+1)*high;
        let mut dummy=expected;for(j,c)in cs.into_iter().enumerate(){dummy[j]+=(wrong-w)*c;}assert_ne!(dummy,expected);
        let linear=c.circuit.terms.iter().find(|t|t.gate.right==0&&!t.gate.c1.is_zero()
            &&t.gate.c0.is_zero()&&t.gate.c2.is_zero()&&t.gate.c3.is_zero()).unwrap();
        let changed=eq_literal(&rl,linear.row)*eq_literal(&ul,linear.gate.left)
            *(eq_literal(&vl,1)-eq_literal(&vl,0))*high*linear.gate.c1;
        assert!(!changed.is_zero(),"owner-local dummy-right weight must survive");
        let q=[low_point(13,5),high_point(g,base,&free,101)].concat();let phi=math.project(&q).unwrap();
        assert_eq!(&phi[13..20],&[Fr::zero(),Fr::zero(),Fr::zero(),Fr::zero(),Fr::zero(),Fr::one(),Fr::one()]);
        let mut local=Fr::zero();let mut global=Fr::zero();let mut bad_bank=Fr::zero();let mut changed=phi.clone();changed[13]=Fr::one();
        for owner in &owners {for bit in 0..8192 {if bit%17==0 {
            local+=eq_literal(&q,owner*8192+bit);
            global+=eq_literal(&phi,owner*(1<<20)+786432+bit);
            bad_bank+=eq_literal(&changed,owner*(1<<20)+786432+bit);
        }}}
        assert_ne!(local,Fr::zero());assert_eq!(local,global);assert_ne!(global,bad_bank);
        let mut wrong_high=phi.clone();wrong_high[20+g-1]+=Fr::one();
        assert_ne!(eq_literal(&phi,base*(1<<20)+786432),eq_literal(&wrong_high,base*(1<<20)+786432));
        for owner in [0,n-1,n,(1usize<<g)-1] {
            let boolean:Vec<_>=(0..13+g).map(|b|Fr::from((((owner*8192+8191)>>b)&1)as u64)).collect();
            let mapped=math.project(&boolean).unwrap();
            for(bit,z)in mapped.iter().enumerate(){assert_eq!(*z,Fr::from((((owner*(1<<20)+786432+8191)>>bit)&1)as u64));}
        }
    }
}

#[test]
fn c568_fast_public_expected_context_fields_and_prechallenge_framing() {
    let parent=WorkTreeHistoryPlan::compile(3,2,[7;32],[9;28]).unwrap();let key=admitted_key(22);
    let good=PointPublicStatement::new(&parent,&key,&commitment()).unwrap();
    let mut bound=Transcript::new(b"c568-public-context");good.bind(&key,&mut bound).unwrap();assert_eq!(bound.challenges(),0);
    let warm_statement=good.clone();assert!(Arc::ptr_eq(&good.expected,&warm_statement.expected));
    let mut warm=Transcript::new(b"c568-public-context");warm_statement.bind(&key,&mut warm).unwrap();same_transcript(&bound,&warm);
    assert_eq!(pinned_expected_id(22).unwrap(),*key.id());
    assert_eq!(pinned_expected_id(22).unwrap(),*key.id());
    let mut literal=Transcript::new(b"c568-public-context");
    literal.append_bytes(b"point-role",b"point-same-x-v1");parent.bind(&mut literal);
    for n in [3,2,4,15,16,22,786432,8192]{literal.append_u64(b"point-shape",n);}
    literal.append_bytes(b"point-native-profile",&good.context.native_profile);
    literal.append_bytes(b"point-codec",b"ergo-header-core-canonical-v1-v2-max514");
    literal.append_bytes(b"point-template",good.context.template.as_bytes());
    literal.append_bytes(b"point-header-aliases",good.context.aliases.as_bytes());
    literal.append_bytes(b"point-owner-policy",b"all-physical-owners-canonical-membership-v1");
    literal.append_bytes(b"point-key",key.id());literal.append_bytes(b"point-C",&commitment());same_transcript(&bound,&literal);
    for field in 0..14 {
        let mut bad=good.clone();let expected=match field {
            0..=7=>{bad.context.numbers[field]+=1;format!("POINT context number {field}")},
            8=>{bad.context.native_profile[0]^=1;"POINT context native profile".into()},
            9=>{bad.context.codec.push(0);"POINT context codec".into()},
            10=>{bad.context.template.push('0');"POINT context template".into()},
            11=>{bad.context.aliases.push('0');"POINT context aliases".into()},
            12=>{bad.context.policy.push(0);"POINT context policy".into()},
            _=>{bad.key_id[0]^=1;"POINT statement key ID".into()},
        };
        let mut t=Transcript::new(b"c568-public-context");let before=t.clone();
        assert_eq!(bad.bind(&key,&mut t),Err(Error::Statement(expected)));same_transcript(&t,&before);
    }
    // The constant-owned ID cache must not admit a foreign supplied key even
    // with the SAME dimension and ID. These are valid canonical group bytes.
    let mut foreign=key.verifier().clone();foreign.chi.swap(0,1);
    let foreign_bytes=pcs::encode(&ArkworksVerifierSetup(foreign)).unwrap();
    assert_ne!(foreign_bytes.as_slice(),pinned_bytes(22).unwrap());
    let foreign=verifier_key::admit_generated_test_key(22,&foreign_bytes,*key.id()).unwrap();
    assert_eq!(foreign.log_n(),key.log_n());assert_eq!(foreign.id(),key.id());
    assert_eq!(pcs::encode(&ArkworksVerifierSetup(foreign.verifier().clone())).unwrap(),foreign_bytes);
    let mut t=Transcript::new(b"c568-public-context");let before=t.clone();
    assert_eq!(good.bind(&foreign,&mut t),Err(Error::Statement("POINT expected admitted key identity".into())));same_transcript(&t,&before);
    assert!(matches!(PointPublicVerifier::new(good.clone(),&foreign),Err(Error::Statement(message))if message=="POINT expected admitted key identity"));
    let mut bad=good.clone();bad.commitment_bytes.push(0);
    assert!(matches!(PointPublicVerifier::new(bad,&key),Err(Error::Statement(_))));
    let other=admitted_key(41);assert!(matches!(PointPublicStatement::new(&parent,&other,&commitment()),Err(Error::Statement(_))));
    let key18=verifier_key::admit(18,include_bytes!("../fixtures/verifier-keys-v1/log18.vk")).unwrap();
    assert!(matches!(PointPublicStatement::new(&parent,&key18,&commitment()),Err(Error::Statement(_))));
    let large=WorkTreeHistoryPlan::compile(1_827_840,21,[7;32],[9;28]).unwrap();
    let large_statement=PointPublicStatement::new(&large,&other,&commitment()).unwrap();
    for fault in 0..3 {
        let mut bad=good.clone();let expected=match fault {
            0=>{bad.parent=&large;"POINT expected parent identity"},
            1=>{bad.expected=Arc::clone(&large_statement.expected);"POINT expected parent identity"},
            _=>{bad.canonical=Arc::clone(&large_statement.canonical);"POINT expected canonical identity"},
        };
        let mut t=Transcript::new(b"c568-public-context");let before=t.clone();
        assert_eq!(bad.bind(&key,&mut t),Err(Error::Statement(expected.into())));same_transcript(&t,&before);
    }
    let mut challenged=Transcript::new(b"c568-public-context");challenged.try_challenge_scalar(b"early").unwrap();let before=challenged.clone();
    assert_eq!(good.bind(&key,&mut challenged),Err(Error::Statement("POINT prefix already challenged".into())));same_transcript(&challenged,&before);
}

#[test]
fn c568_fast_factory_h21_rejects_before_poison_path_setup_and_commit() {
    let parent=WorkTreeHistoryPlan::compile(1_827_840,21,[7;32],[9;28]).unwrap();
    let poison=Path::new("c568-poison-source-must-never-be-opened");let mut audit=PreparationAudit::default();
    let expected=Error::Producer("GKR error: RepetitionLimit".into());
    assert_eq!(PointProducer::create(&parent,poison,Some(&mut audit)).err().unwrap(),expected);
    assert_eq!(audit,PreparationAudit::default());
    assert_eq!(PointProducer::new(&parent,poison).err().unwrap(),expected);
}

#[test]
fn c568_fast_public_malformed_proof_decoders_are_atomic() {
    let parent=WorkTreeHistoryPlan::compile(3,2,[7;32],[9;28]).unwrap();let key=admitted_key(22);
    let verifier=PointPublicVerifier::new(PointPublicStatement::new(&parent,&key,&commitment()).unwrap(),&key).unwrap();
    let mut t=Transcript::new(b"c568-atomicity");let before=t.clone();
    assert!(matches!(verifier.verify_encoded_on(&[],&[],&mut t),Err(Error::GkrEncoding(_))));same_transcript(&t,&before);
    let zero=GkrProof{layers:vec![LayerProof{rounds:vec![vec![Fr::zero();3];30],left_value:Fr::zero(),right_value:Fr::zero(),line_coefficients:vec![Fr::zero();16]}]};
    let encoded=gkr::encode_proof(&zero).unwrap();
    assert!(matches!(verifier.verify_encoded_on(&encoded,&[],&mut t),Err(Error::PcsEncoding(_))));same_transcript(&t,&before);
    let mut trailing=encoded.clone();trailing.push(0);
    assert!(matches!(verifier.verify_encoded_on(&trailing,&[],&mut t),Err(Error::GkrEncoding(_))));same_transcript(&t,&before);
}

/// Genuine same-C semantic join; deliberately absent from default fast tests.
#[test]
#[ignore="actual retained-key22 POINT+HEADER GKR/PCS; requires a separately admitted controller and C568_POINT_SOURCE"]
fn c568_real_retained_key22_same_x_point_header_semantic_join() {
    use crate::packed_owner_assembly::{NativePrefix,NativeOwnerProducer,NativePcsSource};
    use crate::global_producer_endpoint_plan::{GlobalProducerEndpointPlan,NativeReleasedHeaderAdmission,NativeHeaderPublicStatement,NativeHeaderPublicVerifier};
    let path=std::path::PathBuf::from(std::env::var_os("C568_POINT_SOURCE").expect("controller supplies a new dedicated source path"));
    assert!(path.is_absolute()&&path.parent().unwrap().is_dir()&&!path.exists());
    let headers=crate::historical_prefix_witness::retained_headers().unwrap();
    let native=NativePrefix::from_raw_iter(3,headers.iter().map(|h|Ok(h.encode().unwrap()))).unwrap();
    let parent=WorkTreeHistoryPlan::compile(3,2,native.root(),native.total_be28()).unwrap();
    let large=WorkTreeHistoryPlan::compile(1_827_840,21,[7;32],[9;28]).unwrap();
    let native_producer=NativeOwnerProducer::new_for_history(&parent,&native).unwrap();
    let native_source=NativePcsSource::new(&native_producer).unwrap();
    let mut writer=packed::PackedFileWriter::create_new(&path,22).unwrap();
    for owner in 0..4 {writer.write_bytes(native_source.read_owner(owner).unwrap().packed_bytes()).unwrap();}
    drop(writer.finish().unwrap());
    let mut factory=PointProducer::new(&parent,&path).unwrap();
    let statement=factory.statement();let key=admitted_key(22);let verifier=PointPublicVerifier::new(statement.clone(),&key).unwrap();
    let mut prover=Transcript::new(b"c568-POINT-semantic");let proof=factory.prove_on(&mut prover).unwrap();
    let mut consumer=Transcript::new(b"c568-POINT-semantic");let claim=verifier.verify_on(&proof.gkr,&proof.opening,&mut consumer).unwrap();same_transcript(&prover,&consumer);
    let (gkr_bytes,pcs_bytes)=(gkr::encode_proof(&proof.gkr).unwrap(),pcs::encode_proof(&proof.opening).unwrap());
    let mut encoded=Transcript::new(b"c568-POINT-semantic");assert_eq!(verifier.verify_encoded_on(&gkr_bytes,&pcs_bytes,&mut encoded).unwrap(),claim);same_transcript(&encoded,&consumer);
    let mut trailing=pcs_bytes.clone();trailing.push(0);let mut t=Transcript::new(b"c568-POINT-semantic");let before=t.clone();
    assert!(matches!(verifier.verify_encoded_on(&gkr_bytes,&trailing,&mut t),Err(Error::PcsEncoding(_))));same_transcript(&t,&before);
    let mut challenged=Transcript::new(b"c568-POINT-semantic");challenged.try_challenge_scalar(b"early").unwrap();let before=challenged.clone();
    assert_eq!(verifier.verify_on(&proof.gkr,&proof.opening,&mut challenged),Err(Error::Statement("POINT prefix already challenged".into())));same_transcript(&challenged,&before);
    assert_eq!(verifier.verify_encoded_on(&gkr_bytes,&pcs_bytes,&mut challenged),Err(Error::Statement("POINT prefix already challenged".into())));same_transcript(&challenged,&before);
    let mut interior=proof.gkr.clone();interior.layers[0].line_coefficients[1]+=Fr::one();interior.layers[0].line_coefficients[2]-=Fr::one();
    for bad in [&interior] {let mut t=Transcript::new(b"c568-POINT-semantic");let before=t.clone();assert!(matches!(verifier.verify_on(bad,&proof.opening,&mut t),Err(Error::Pcs(_))));same_transcript(&t,&before);}
    let mut bad_round=proof.gkr.clone();bad_round.layers[0].rounds[0][0]+=Fr::one();
    let mut t=Transcript::new(b"c568-POINT-semantic");let before=t.clone();assert_eq!(verifier.verify_on(&bad_round,&proof.opening,&mut t),Err(Error::Gkr(GkrError::SumcheckIdentity)));same_transcript(&t,&before);
    let mut local_tx=Transcript::new(b"c568-POINT-semantic");statement.bind(&key,&mut local_tx).unwrap();
    let local=statement.math().unwrap().verify(&proof.gkr,&mut local_tx).unwrap();
    for field in 0..3 {
        let mut point=claim.point.clone();let mut value=claim.value;
        let last=point.len()-1;
        match field {0=>point[13]=Fr::one(),1=>point[last]+=Fr::one(),_=>value+=Fr::one()}
        assert!(pcs::verify_admitted(factory.committed.commitment,value,&point,&proof.opening,&key,&mut local_tx.clone()).is_err());
    }
    let mut wrong_phi=claim.point.clone();wrong_phi[13]=Fr::one();
    let wrong_opening=packed::open(&factory.committed,&factory.source,&wrong_phi,&factory.setup,&mut local_tx.clone()).unwrap();
    let mut t=Transcript::new(b"c568-POINT-semantic");let before=t.clone();assert!(matches!(verifier.verify_on(&proof.gkr,&wrong_opening,&mut t),Err(Error::Pcs(_))));same_transcript(&t,&before);
    let mut wrong_c=statement.clone();wrong_c.commitment_bytes=commitment();let other=PointPublicVerifier::new(wrong_c,&key).unwrap();
    let mut t=Transcript::new(b"c568-POINT-semantic");let before=t.clone();
    assert!(matches!(other.verify_on(&proof.gkr,&proof.opening,&mut t),Err(Error::Gkr(_))|Err(Error::Pcs(_))));same_transcript(&t,&before);
    // Coherent alternative expected parents isolate fields bound by parent.bind.
    // Reuse this proof/C/key and the code-owned canonical POINT template.
    for field in 0..3 {
        let (mut root,mut total,mut n)=(native.root(),native.total_be28(),3);
        match field {0=>root[0]^=1,1=>total[0]^=1,_=>n=4}
        let alternative=WorkTreeHistoryPlan::compile(n,2,root,total).unwrap();
        let changed=PointPublicStatement::from_canonical(&alternative,Arc::clone(&statement.canonical),
            &key,&statement.commitment_bytes).unwrap();
        // At the SAME geometry a different valid parent still requires its
        // own seal; neither a parent swap nor an expectation swap is reusable.
        for swap in 0..2 {
            let mut stale=statement.clone();
            if swap==0{stale.parent=&alternative;}else{stale.expected=Arc::clone(&changed.expected);}
            let mut t=Transcript::new(b"c568-POINT-semantic");let before=t.clone();
            assert_eq!(stale.bind(&key,&mut t),Err(Error::Statement("POINT expected parent identity".into())));same_transcript(&t,&before);
        }
        let changed=PointPublicVerifier::new(changed,&key).unwrap();
        let mut t=Transcript::new(b"c568-POINT-semantic");let before=t.clone();
        assert!(matches!(changed.verify_on(&proof.gkr,&proof.opening,&mut t),
            Err(Error::Gkr(_))|Err(Error::Pcs(_))),"coherent expected parent field {field}");
        same_transcript(&t,&before);
    }
    let plan=GlobalProducerEndpointPlan::new(&parent).unwrap();let header=NativeReleasedHeaderAdmission::new(&plan,&native_source).unwrap();
    let context=header.prepare_context(&factory.setup,&key).unwrap();assert_eq!(context.commitment_bytes(),statement.commitment_bytes);
    let mut ht=Transcript::new(b"c568-HEADER-semantic");let(hp,hclaim,_,_)=header.prove_on(&context,&mut ht).unwrap();
    let ho=packed::open_native(&native_source,context.committed(),&factory.setup,&hclaim.point,&mut ht).unwrap();
    let hs=NativeHeaderPublicStatement::new(native.root(),native.total_be28(),&key,&statement.commitment_bytes).unwrap();
    let hv=NativeHeaderPublicVerifier::new(&parent,hs,&key).unwrap();let mut ht_verify=Transcript::new(b"c568-HEADER-semantic");assert_eq!(hv.verify_on(&hp,&ho,&mut ht_verify).unwrap(),hclaim);same_transcript(&ht,&ht_verify);
    // Detached serializer bytes fail the actual retained HEADER alias rows;
    // a valid unchanged POINT bank alone has no such cross-family predicate.
    let row=native_source.read_owner(0).unwrap();let mut x:Vec<_>=row.packed_bytes().iter().flat_map(|byte|(0..8).map(move|b|Fr::from(((byte>>b)&1)as u64))).collect();
    let aliases:Vec<_>=parent.header_boundary().canonical_circuit().terms.iter().filter(|t|(405784..405850).contains(&t.row)).collect();
    let wire=aliases[0].gate.right;x[wire]=Fr::one()-x[wire];
    let residual=aliases.iter().filter(|t|t.row==405784).fold(Fr::zero(),|sum,t|sum+t.gate.evaluate(&x));assert!(!residual.is_zero());
    assert!(residuals(&statement.canonical.circuit,&x[786432..794624]).iter().all(Zero::is_zero));
    let io=factory.source.io_metrics_snapshot();factory.parent=&large;let mut t=Transcript::new(b"c568-POINT-semantic");let before=t.clone();
    assert_eq!(factory.prove_on(&mut t).err().unwrap(),Error::Producer("GKR error: RepetitionLimit".into()));same_transcript(&t,&before);
    assert_eq!(factory.source.io_metrics_snapshot().read_calls,io.read_calls);
    assert_eq!(factory.source.io_metrics_snapshot().read_bytes,io.read_bytes);
    assert_eq!(local.point.len(),15);
}

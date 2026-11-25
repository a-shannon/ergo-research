//! Bounded source-family/reference/proof join. No PCS or native authentication.
use ark_bn254::Fr;
use ark_ff::{Field, One, PrimeField, Zero};
use num_bigint::BigUint;
use crate::{gkr::{self,Gate,GkrError,GkrProof},implicit_witness::Witness,
    legacy_envelope_map::Map,sparse::{self,Circuit,Term},transcript::Transcript,
    ratio_contraction::{self as ratio,AdmittedFamily,AdmissionError,Descriptor,Fixture,Order,Role,RoundRecord}};

fn f(n:u64)->Fr{Fr::from(n)}
fn power(n:usize)->Fr{let v=BigUint::from(1u8)<<n;Fr::from_le_bytes_mod_order(&v.to_bytes_le())}
fn weight(index:usize,point:&[Fr])->Fr{
    let mut value=Fr::one();for(bit,z)in point.iter().enumerate(){value*=if index>>bit&1==1{*z}else{Fr::one()-z};}value
}
fn literal_mle(x:&[Fr],point:&[Fr])->Fr{x.iter().enumerate().map(|(i,v)|*v*weight(i,point)).sum()}
fn independent_line(x:&[Fr],u:&[Fr],v:&[Fr])->Vec<Fr>{
    let mut output=vec![Fr::zero();u.len()+1];
    for(index,value)in x.iter().enumerate(){let mut p=vec![*value];
        for bit in 0..u.len(){let(a,b)=if index>>bit&1==1{(u[bit],v[bit]-u[bit])}else{(Fr::one()-u[bit],u[bit]-v[bit])};
            let mut next=vec![Fr::zero();p.len()+1];for(degree,c)in p.iter().enumerate(){next[degree]+=a*c;next[degree+1]+=b*c;}p=next;}
        for(a,b)in output.iter_mut().zip(p){*a+=b;}}
    output
}
fn fixture(id:Fixture)->(Vec<Fr>,Fr,usize){
    let mut x=vec![Fr::zero();512];let(q,d)=(power(91)-Fr::one(),power(64)-Fr::one());
    let(e,k)=match id{
        Fixture::Main=>{for p in[0,2,3]{x[156+p]=Fr::one();}for b in[0,6]{x[92+b]=Fr::one();}x[400]=f(2);(f(845),6)},
        Fixture::Zero=>(Fr::zero(),0),
        Fixture::Nonboolean=>{x[156]=-f(3);x[92]=f(2);x[400]=f(5);(-f(6),3)},
        Fixture::AllOneRails=>{x[156..247].fill(Fr::one());x[92..156].fill(Fr::one());x[400]=f(2);(q*d,156)},
        Fixture::Full512=>{x.fill(f(2));(f(4)*q*d,512)},
    };assert_eq!(x.iter().filter(|v|!v.is_zero()).count(),k);(x,e,k)
}
fn term(left:usize,right:usize,c:[Fr;4])->Term{Term{row:0,gate:Gate{left,right,c0:c[0],c1:c[1],c2:c[2],c3:c[3]}}}
fn reference(e:Fr)->Circuit{
    let mut terms=Vec::with_capacity(5825);
    // Literal oracle only. No contraction/producer helper supplies expected Terms.
    for p in 0..91{for q in 0..64{terms.push(term(156+p,92+q,[Fr::zero(),Fr::zero(),Fr::zero(),-power(p+q)]));}}
    terms.push(term(0,0,[e,Fr::zero(),Fr::zero(),Fr::zero()]));
    assert_eq!((terms.len(),terms.capacity()),(5825,5825));Circuit{input_len:512,row_count:1,terms}
}
// Reference-only exact-program boundary; the structured producer never calls it.
fn check_reference<R>(supplied:&[Term],e:Fr,consumer:impl FnOnce()->R)->Result<R,&'static str>{
    let expected=reference(e);
    if supplied!=expected.terms{return Err("reference tuple fields/order/count");}Ok(consumer())
}
fn source_family_and_tuple_controls(){
    let map=Map::new(2048,11,64).unwrap();assert_eq!(map.tier(1983).unwrap(),Some(1));
    let owner=map.terms(1983).unwrap();assert_eq!((owner.len(),owner.capacity()),(17341,32768));
    let products=owner.iter().filter(|t|t.row==32497824&&!t.gate.c3.is_zero()).collect::<Vec<_>>();
    assert_eq!((products.len(),products.capacity()),(5824,8192));
    let compact=reference(f(845));
    for p in 0..91{for q in 0..64{let index=64*p+q;let actual=products[index];
        let expected=Term{row:32497824,gate:Gate{left:2079982690+p,right:2079982626+q,
            c0:Fr::zero(),c1:Fr::zero(),c2:Fr::zero(),c3:-power(p+q)}};
        assert_eq!(*actual,expected,"source product {p}/{q}");
        let mut mapped=(*actual).clone();mapped.row=0;
        mapped.gate.left=actual.gate.left.checked_sub(2079982535).unwrap()+1;
        mapped.gate.right=actual.gate.right.checked_sub(2079982535).unwrap()+1;
        assert_eq!(mapped,compact.terms[index],"mapped product {p}/{q}");}}
    let mut callbacks=0;check_reference(&compact.terms,f(845),||{callbacks+=1;}).unwrap();assert_eq!(callbacks,1);callbacks=0;
    let mut omission=compact.terms.clone();omission.remove(1700);
    assert_eq!(check_reference(&omission,f(845),||{callbacks+=1;}),Err("reference tuple fields/order/count"));
    assert_eq!(callbacks,0);drop(omission);
    for field in 0..9{let mut changed=compact.terms.clone();let t=&mut changed[1700];match field{
        0=>t.row=1,1=>t.gate.left+=1,2=>t.gate.right+=1,
        3=>t.gate.c0=Fr::one(),4=>t.gate.c1=Fr::one(),5=>t.gate.c2=Fr::one(),
        6=>t.gate.c3=-t.gate.c3,7=>t.gate.c3*=f(2),_=>changed.swap(1700,1701)};
        assert_eq!(check_reference(&changed,f(845),||{callbacks+=1;}),Err("reference tuple fields/order/count"),"tuple field/order {field}");
        assert_eq!(callbacks,0);}
    assert_eq!(std::mem::size_of::<Term>(),152);
    assert_eq!(compact.terms.len()*std::mem::size_of::<Term>(),885400);
    // Fixed capacity hypotheses above become evidence only if this selector passes.
}

fn binding_bytes(family:&AdmittedFamily,id:Fixture){
    let text=String::from_utf8(family.descriptor_bytes()).unwrap();
    assert!(text.ends_with('\n')&&!text.contains('\r')&&!text.contains('\0'));
    let expected=concat!(
        "version=ratio-contraction-local-family-v1\n",
        "source-map-sha256=AFEA8F2B7B54302FB75C7613ACA87E05AA02FAE842AF92DB38CB2B66DC0F23D9\n",
        "source-n=2048\nsource-h=11\nsource-e=64\nsource-owner=1983\nsource-tier=1\nsource-ratio-index=0\n",
        "source-width=1048576\nsource-row-stride=16384\nsource-owner-base=2079326208\nsource-row=32497824\n",
        "source-window-base=2079982535\nsource-window-width=503\nsource-Q-base=2079982690\nsource-Q-width=91\n",
        "source-D-base=2079982626\nsource-D-width=64\nsource-placeholder=2079326208\n",
        "import-D=Difficulty,1982,987674,224\nimport-end=Timestamp,1983,525330,64\nimport-start=Timestamp,1023,525330,64\nimport-offset=64\n",
        "mapping=window-to-one-plus-offset-placeholder-to-zero-v1\n",
        "local-input-width=512\nlocal-input-log=9\nlocal-row-count=1\nlocal-row-log=0\nlocal-row=0\n",
        "local-window-base=1\nlocal-window-width=503\nlocal-Q=Quotient91,156,91\nlocal-D=Delta64,92,64\nlocal-placeholder=0\n",
        "log-copies=0\nproduct-channel=c3\nproduct-scale=-1\nproduct-coefficient=scale-times-2-power-p-plus-q\n",
        "product-order=quotient-p-outer-denominator-q-inner\nproduct-term-count=5824\n",
        "constant-channel=c0\nconstant-order=after-products\nterm-count=5825\nfixture=FIXTURE_ID\nE-encoding=existing-canonical-Fr-scalar-event\n");
    assert_eq!(text,expected.replace("FIXTURE_ID",id.id()));
}
fn sparse_metadata_admission(){
    let cases=[(0,1,0,GkrError::InvalidInputWidth),(3,1,0,GkrError::InvalidInputWidth),
        (512,0,0,GkrError::InvalidLayerWidth),(512,3,0,GkrError::InvalidLayerWidth),
        (512,1,4,GkrError::RepetitionLimit),(1<<25,1,0,GkrError::RepeatedSizeLimit),
        (512,1<<25,0,GkrError::RepeatedSizeLimit),(1<<24,1,1,GkrError::RepeatedSizeLimit)];
    for(input_len,row_count,copies,error)in cases{let empty=Circuit{input_len,row_count,terms:Vec::new()};
        assert_eq!(sparse::validate(&empty,copies).err(),Some(error));}
    let empty=Circuit{input_len:512,row_count:1,terms:Vec::new()};let shape=sparse::validate(&empty,0).unwrap();
    assert_eq!((shape.input_bits,shape.row_bits,shape.copies,shape.input_len,shape.row_count),(9,0,1,512,1));
}
fn typed_admission_before_callbacks(){
    use AdmissionError::{Descriptor as D,Protocol as P};
    let mut cases=Vec::new();let canonical=Descriptor::canonical(Fixture::Main);
    macro_rules! bad{($name:expr,$field:ident,$value:expr,$error:expr)=>{{let mut d=canonical.clone();d.$field=$value;cases.push(($name,d,$error));}}}
    bad!("input-width",input_len,256,D("fixed dimensions"));bad!("input-log",input_log,8,D("fixed dimensions"));
    bad!("row-count",row_count,2,D("fixed dimensions"));bad!("row-log",row_log,1,D("fixed dimensions"));
    bad!("copies-one",log_copies,1,D("fixed dimensions"));bad!("copies-limit",log_copies,4,P(GkrError::RepetitionLimit));
    bad!("products",product_count,5823,D("term count"));bad!("terms",term_count,5824,D("term count"));
    // Actual cap branch precedes interval/canonical rejection; no term allocation occurs.
    bad!("term-cap",d_width,11523,D("term cap"));
    bad!("Q-end",q_width,90,D("mapping intervals"));bad!("D-end",d_width,63,D("mapping intervals"));
    bad!("Q-role",q_role,Role::Delta64,D("canonical descriptor"));bad!("D-role",d_role,Role::Quotient91,D("canonical descriptor"));
    bad!("constant-role",constant_role,Role::Delta64,D("canonical descriptor"));
    bad!("order",order,Order::DenominatorOuter,D("canonical descriptor"));bad!("constant-order",order,Order::ConstantBefore,D("canonical descriptor"));
    bad!("sign",sign,1,D("canonical descriptor"));bad!("collision",placeholder,1,D("mapping intervals"));
    bad!("window",local_window,2,D("mapping intervals"));bad!("raw-row",raw_row,32497825,D("mapping intervals"));
    bad!("raw-Q",raw_q,2079982691,D("mapping intervals"));bad!("raw-D",raw_d,2079982627,D("mapping intervals"));
    bad!("source-width",width,1048577,D("mapping intervals"));
    bad!("row-stride",row_stride,16385,D("mapping intervals"));
    bad!("owner-base",owner_base,2079326209,D("mapping intervals"));
    bad!("window-base",window_base,2079982536,D("mapping intervals"));
    bad!("raw-placeholder",raw_placeholder,2079326209,D("mapping intervals"));
    bad!("local-Q",local_q,157,D("mapping intervals"));bad!("local-D",local_d,93,D("mapping intervals"));
    bad!("window-width-short",window_width,502,D("mapping intervals"));
    bad!("owner-1959",owner,1959,D("mapping intervals"));
    bad!("owner-overflow",owner,usize::MAX,D("overflow"));bad!("window-overflow",window_width,usize::MAX,D("overflow"));
    bad!("n",n,2049,D("canonical descriptor"));bad!("h",h,10,D("canonical descriptor"));bad!("e",e,63,D("canonical descriptor"));
    bad!("tier",tier,2,D("canonical descriptor"));bad!("ratio",ratio,1,D("canonical descriptor"));
    bad!("local-row",local_row,1,D("canonical descriptor"));bad!("offset",offset,63,D("canonical descriptor"));
    for(import,name)in [(0,"D"),(1,"end"),(2,"start")]{for coordinate in 0..3{
        let mut wrong_import=canonical.clone();match coordinate{
            0=>wrong_import.imports[import].0-=1,
            1=>wrong_import.imports[import].1+=1,
            _=>wrong_import.imports[import].2-=1,
        }
        cases.push((match(name,coordinate){
            ("D",0)=>"D-origin",("D",1)=>"D-local",("D",_)=>"D-width",
            ("end",0)=>"end-origin",("end",1)=>"end-local",("end",_)=>"end-width",
            (_,0)=>"start-origin",(_,1)=>"start-local",(_,_)=>"start-width",
        },wrong_import,D("canonical descriptor")));
    }}
    let(x,e,_)=fixture(Fixture::Main);let witness=Witness::from_dense(&x,512).unwrap();
    for(name,descriptor,error)in cases{let mut callbacks=0;let mut transcript=Transcript::new(ratio::DOMAIN);let before=transcript.bytes_absorbed();
        let result=AdmittedFamily::with_admitted(descriptor,e,witness.clone(),|family|{callbacks+=1;family.bind(&mut transcript);});
        assert_eq!(result,Err(error),"{name}: exact rejection boundary");assert_eq!(callbacks,0,"{name}: callback");
        assert_eq!(transcript.bytes_absorbed(),before);assert_eq!(transcript.challenges(),0);}
    let small=Witness::from_dense(&x[..256],256).unwrap();let mut callbacks=0;
    assert_eq!(AdmittedFamily::with_admitted(canonical.clone(),e,small,|_|{callbacks+=1;}),Err(P(GkrError::InvalidInputWidth)));
    assert_eq!(callbacks,0);
    for fault in 0..2{let mut changed=x.clone();let wrong_e=if fault==0{e+Fr::one()}else{changed[156]+=Fr::one();e};
        let w=Witness::from_dense(&changed,512).unwrap();
        assert_eq!(AdmittedFamily::with_admitted(canonical.clone(),wrong_e,w,|_|{callbacks+=1;}),Err(P(GkrError::NonzeroOutput)));
        assert_eq!(callbacks,0);
        let circuit=reference(wrong_e);let mut t=Transcript::new(ratio::DOMAIN);
        assert_eq!(sparse::prove_with_binding(&circuit,&changed,0,&mut t,|_|{callbacks+=1;}).err(),Some(GkrError::NonzeroOutput));
        assert_eq!(callbacks,0);}
}

fn dense_coefficients(circuit:&Circuit,x:&[Fr])->(Vec<Fr>,Vec<Fr>){
    let(mut a,mut b)=(vec![Fr::zero();512],vec![Fr::zero();512]);
    for t in &circuit.terms{let g=&t.gate;a[g.left]+=g.c1+g.c3*x[g.right];b[g.left]+=g.c0+g.c2*x[g.right];}(a,b)
}
fn dense_second(circuit:&Circuit,u:&[Fr],left:Fr)->(Vec<Fr>,Vec<Fr>){
    let(mut c,mut d)=(vec![Fr::zero();512],vec![Fr::zero();512]);
    for t in &circuit.terms{let g=&t.gate;let w=weight(g.left,u);c[g.right]+=w*(g.c2+g.c3*left);d[g.right]+=w*(g.c0+g.c1*left);}(c,d)
}
fn compare_word(w:&Witness,dense:&[Fr],label:&str){assert_eq!(w.extent(),dense.len());
    for(i,v)in dense.iter().enumerate(){assert_eq!(w.value(i).unwrap(),*v,"{label}:{i}");}}
fn replay(family:&AdmittedFamily,proof:&GkrProof)->(Vec<Fr>,Fr,Transcript){
    let mut t=Transcript::new(ratio::DOMAIN);family.bind(&mut t);gkr::append_usize(&mut t,b"gkr-layer-index",0);
    let mut challenges=Vec::with_capacity(18);for p in &proof.layers[0].rounds{
        gkr::append_polynomial(&mut t,b"gkr-sumcheck-polynomial",p);challenges.push(t.challenge_scalar(b"gkr-sumcheck-challenge"));}
    let l=&proof.layers[0];t.append_scalar(b"gkr-left-value",&l.left_value);t.append_scalar(b"gkr-right-value",&l.right_value);
    gkr::append_polynomial(&mut t,b"gkr-line-polynomial",&l.line_coefficients);let lambda=t.challenge_scalar(b"gkr-line-challenge");
    (challenges,lambda,t)
}
fn proof_differentials(){
    for id in[Fixture::Main,Fixture::Zero,Fixture::Nonboolean,Fixture::AllOneRails,Fixture::Full512]{
        let(x,e,k)=fixture(id);let witness=Witness::from_dense(&x,512).unwrap();assert_eq!(witness.retained_capacity(),k);
        let family=AdmittedFamily::new(Descriptor::canonical(id),e,witness).unwrap();binding_bytes(&family,id);
        let circuit=reference(e);let shape=sparse::validate(&circuit,0).unwrap();assert_eq!(shape.input_bits,9);
        let mut literal_t=Transcript::new(ratio::DOMAIN);
        let(expected,expected_claim)=sparse::prove_with_binding(&circuit,&x,0,&mut literal_t,|t|family.bind(t)).unwrap();
        let mut structured_t=Transcript::new(ratio::DOMAIN);let mut records=Vec::with_capacity(18);
        let(actual,claim)=family.prove(&mut structured_t,|r|records.push(r.clone())).unwrap();
        assert_eq!(records.len(),18);assert_eq!(actual,expected,"{}: full proof",id.id());assert_eq!(claim,expected_claim);
        assert_eq!((structured_t.challenges(),structured_t.raw_queries(),structured_t.bytes_absorbed()),
            (literal_t.challenges(),literal_t.raw_queries(),literal_t.bytes_absorbed()));assert_eq!(structured_t.challenges(),19);
        assert_eq!(structured_t.challenge_scalar(b"ratio-test-continuation"),literal_t.challenge_scalar(b"ratio-test-continuation"));
        let bytes=gkr::encode_proof(&actual).unwrap();assert_eq!(bytes,gkr::encode_proof(&expected).unwrap());assert_eq!(bytes.len(),2112);
        assert_eq!(sparse::decode_proof(&circuit,0,&bytes).unwrap(),actual);
        let mut verified_t=Transcript::new(ratio::DOMAIN);assert_eq!(family.verify(&actual,&mut verified_t).unwrap(),claim);
        let mut reference_t=Transcript::new(ratio::DOMAIN);
        let reference_claim=gkr::verify_with_wiring(&[shape.input_bits],shape.row_count,&expected,&mut reference_t,
            |t|family.bind(t),|_,r,u,v|sparse::wiring(&circuit,&shape,r,u,v)).unwrap();assert_eq!(reference_claim,claim);
        assert_eq!(literal_mle(&x,&claim.point),claim.value);
        let(challenges,_,_)=replay(&family,&expected);let(u,v)=challenges.split_at(9);
        assert_eq!(actual.layers[0].line_coefficients,independent_line(&x,u,v));
        let(a,b)=family.first_coefficients().unwrap();let(da,db)=dense_coefficients(&circuit,&x);compare_word(&a,&da,"A");compare_word(&b,&db,"B");
        let(c,d)=family.second_coefficients(u,expected.layers[0].left_value).unwrap();
        let(dc,dd)=dense_second(&circuit,u,expected.layers[0].left_value);compare_word(&c,&dc,"C");compare_word(&d,&dd,"D");
        for phase in 0..2{let(mut aa,mut bb)=if phase==0{(da.clone(),db.clone())}else{(dc.clone(),dd.clone())};let mut xx=x.clone();
            for round in 0..9{let r:&RoundRecord=&records[phase*9+round];assert_eq!((r.phase,r.round,r.extent),(phase,round,xx.len()));
                assert_eq!(r.polynomial.to_vec(),gkr::quadratic_message(&aa,&bb,&xx));assert_eq!(r.challenge,challenges[phase*9+round]);
                assert_eq!(r.work.value_queries,6*r.work.pair_count);assert!(r.work.pair_capacity<=if phase==0{92}else{65});
                assert_eq!(r.support[2],xx.iter().filter(|x|!x.is_zero()).count());
                gkr::fold(&mut aa,r.challenge);gkr::fold(&mut bb,r.challenge);gkr::fold(&mut xx,r.challenge);}}
        let(line,work)=family.witness().line_counted(u,v).unwrap();assert_eq!(line,actual.layers[0].line_coefficients);
        assert_eq!((work.entry_visits,work.coefficient_updates,work.output_scalars,work.scratch_scalars),(k,k*54,10,10));
        assert_eq!(std::mem::size_of::<Fr>(),32);assert_eq!(std::mem::size_of::<(usize,Fr)>(),40);
    }
}

fn message_state_and_factor_controls(){
    let(x,e,_)=fixture(Fixture::Main);let family=AdmittedFamily::new(Descriptor::canonical(Fixture::Main),e,Witness::from_dense(&x,512).unwrap()).unwrap();
    let circuit=reference(e);let(mut da,mut db)=dense_coefficients(&circuit,&x);let(mut a,mut b)=family.first_coefficients().unwrap();
    let mut full=family.witness().clone();let mut rail_only=x.clone();rail_only[400]=Fr::zero();
    let mut truncated=Witness::from_dense(&rail_only,512).unwrap();let mut differences=Vec::new();let mut dense=x.clone();
    for j in 0..9{let(p,_)=ratio::quadratic(&a,&b,&full).unwrap();let(bad,_)=ratio::quadratic(&a,&b,&truncated).unwrap();
        assert_eq!(p.to_vec(),gkr::quadratic_message(&da,&db,&dense));if p!=bad{differences.push(j);}
        let z=f(2);a=a.fold(&[z]).unwrap();b=b.fold(&[z]).unwrap();full=full.fold(&[z]).unwrap();truncated=truncated.fold(&[z]).unwrap();
        gkr::fold(&mut da,z);gkr::fold(&mut db,z);gkr::fold(&mut dense,z);}
    assert_eq!(differences,vec![8],"off-rail cell participates in final paired message");
    let reversed=family.witness().fold(&[f(3),f(2)]).unwrap();let correct=family.witness().fold(&[f(2),f(3)]).unwrap();
    assert_ne!(correct,reversed,"coordinate order cannot be reversed");
    let(u,v)=(vec![f(2);9],vec![f(3);9]);let changed_x={let mut y=x.clone();y[400]=f(3);y};
    assert_eq!(literal_mle(&changed_x,&u)-literal_mle(&x,&u),f(8));
    let before=independent_line(&x,&u,&v);let after=independent_line(&changed_x,&u,&v);
    assert_eq!(after.iter().zip(&before).map(|(a,b)|*a-*b).collect::<Vec<_>>(),
        [8,60,198,377,456,363,190,63,12,1].map(f).to_vec());
    let changed_family=AdmittedFamily::new(Descriptor::canonical(Fixture::Main),e,Witness::from_dense(&changed_x,512).unwrap()).unwrap();
    assert_eq!(family.values(),changed_family.values());
    let left=literal_mle(&x,&u);let(c,d)=family.second_coefficients(&u,left).unwrap();let stale=family.witness().fold(&u).unwrap();
    let mut callbacks=0;let result=ratio::quadratic(&c,&d,&stale).map(|_|{callbacks+=1;});
    assert_eq!(result,Err(GkrError::PointDimension));assert_eq!(callbacks,0);
    let(mut dc,dd)=dense_second(&circuit,&u,left);let expected=gkr::quadratic_message(&dc,&dd,&x);
    let qweight=(0..91).map(|p|power(p)*weight(156+p,&u)).sum::<Fr>();assert!(!qweight.is_zero()&&left!=Fr::one());
    for fault in 0..3{let scale=match fault{0=>-left,1=>-qweight,_=>-qweight*left};
        for q in 0..64{dc[92+q]=power(q)*scale;}
        let mut bad_d=dd.clone();if fault==2{bad_d[0]=e;assert_ne!(weight(0,&u),Fr::one());}
        let cw=Witness::from_dense(&dc,512).unwrap();let dw=Witness::from_dense(&bad_d,512).unwrap();
        assert_ne!(ratio::quadratic(&cw,&dw,family.witness()).unwrap().0.to_vec(),expected,"missing factor {fault}");}
    // Small functional pair cancellation, independently dense and non-Boolean.
    let aa=vec![Fr::one(),-Fr::one(),Fr::zero(),Fr::zero(),f(2),Fr::zero(),Fr::zero(),Fr::zero()];
    let bb=vec![Fr::zero(),Fr::zero(),f(3),-f(3),Fr::zero(),Fr::zero(),Fr::zero(),Fr::zero()];let xx=vec![f(2);8];
    let mut aw=Witness::from_dense(&aa,8).unwrap();let mut bw=Witness::from_dense(&bb,8).unwrap();let mut xw=Witness::from_dense(&xx,8).unwrap();
    assert_eq!(ratio::quadratic(&aw,&bw,&xw).unwrap().0.to_vec(),gkr::quadratic_message(&aa,&bb,&xx));
    let half=Fr::from(2u8).inverse().unwrap();aw=aw.fold(&[half]).unwrap();bw=bw.fold(&[half]).unwrap();xw=xw.fold(&[half]).unwrap();
    assert_eq!(aw.entries().len(),1);assert_eq!(bw.entries().len(),0);assert_eq!(xw.entries().len(),4);
}

fn actual_consumer_mutants(){
    let(x,e,_)=fixture(Fixture::Main);let family=AdmittedFamily::new(Descriptor::canonical(Fixture::Main),e,Witness::from_dense(&x,512).unwrap()).unwrap();
    let mut t=Transcript::new(ratio::DOMAIN);let(proof,_)=family.prove(&mut t,|_|{}).unwrap();
    for fault in 0..4{let mut p=proof.clone();let expected=match fault{
        0=>{p.layers[0].rounds.pop();GkrError::SumcheckRoundCount},1=>{p.layers[0].rounds[0].push(Fr::zero());GkrError::SumcheckDegree},
        2=>{p.layers[0].line_coefficients.pop();GkrError::LineDegree},_=>{p.layers[0].left_value+=Fr::one();GkrError::TerminalExpression}};
        assert_eq!(family.verify(&p,&mut Transcript::new(ratio::DOMAIN)),Err(expected),"proof field {fault}");}
    let mut round=proof.clone();round.layers[0].rounds[0][1]-=Fr::one();round.layers[0].rounds[0][2]+=Fr::one();
    let original=&proof.layers[0].rounds[0];let changed=&round.layers[0].rounds[0];
    assert_eq!(changed[0],original[0]);assert_eq!(gkr::eval_polynomial(changed,Fr::one()),gkr::eval_polynomial(original,Fr::one()));
    assert_eq!(changed[1]-original[1],-Fr::one());assert_eq!(changed[2]-original[2],Fr::one());
    let mut rt=Transcript::new(ratio::DOMAIN);family.bind(&mut rt);gkr::append_usize(&mut rt,b"gkr-layer-index",0);
    gkr::append_polynomial(&mut rt,b"gkr-sumcheck-polynomial",changed);let z=rt.challenge_scalar(b"gkr-sumcheck-challenge");
    let claim=gkr::eval_polynomial(changed,z);let next=&proof.layers[0].rounds[1];
    assert_ne!(next[0]+gkr::eval_polynomial(next,Fr::one()),claim,"actual mutated challenge/next claim");
    assert_eq!(family.verify(&round,&mut Transcript::new(ratio::DOMAIN)),Err(GkrError::SumcheckIdentity));
    let mut line=proof.clone();line.layers[0].line_coefficients[1]-=Fr::one();line.layers[0].line_coefficients[2]+=Fr::one();
    assert_eq!(line.layers[0].line_coefficients[0],proof.layers[0].line_coefficients[0]);
    assert_eq!(gkr::eval_polynomial(&line.layers[0].line_coefficients,Fr::one()),proof.layers[0].right_value);
    let mutated=family.verify(&line,&mut Transcript::new(ratio::DOMAIN)).unwrap();
    let(challenges,lambda,_)=replay(&family,&line);assert!(lambda!=Fr::zero()&&lambda!=Fr::one(),"fixed line-mutant fixture must be decisive");
    assert_eq!(mutated.point,gkr::line_point(&challenges[..9],&challenges[9..],lambda));
    let difference=mutated.value-literal_mle(&x,&mutated.point);
    assert_eq!(difference,lambda*(lambda-Fr::one()));assert!(!difference.is_zero(),"missing PCS opening is visible");
    // Label/order faults consume the admitted geometry through the unchanged verifier.
    for fault in 0..2{let mut wrong=Transcript::new(ratio::DOMAIN);
        let result=gkr::verify_with_wiring(&[family.witness().dimensions()],1,&proof,&mut wrong,|transcript|{
            if fault==0{transcript.append_bytes(b"ratio-family-descriptor-wrong",&family.descriptor_bytes());transcript.append_scalar(b"ratio-fixed-E",&e);}
            else{transcript.append_scalar(b"ratio-fixed-E",&e);transcript.append_bytes(b"ratio-family-descriptor",&family.descriptor_bytes());}
        },|i,r,u,v|family.wiring(i,r,u,v));assert!(result.is_err(),"binding fault {fault}");}
    assert_eq!(family.wiring(1,&[],&[f(2);9],&[f(3);9]),Err(GkrError::PointDimension));
    assert_eq!(family.wiring(0,&[Fr::one()],&[f(2);9],&[f(3);9]),Err(GkrError::PointDimension));
    assert_eq!(family.wiring(0,&[],&[f(2);8],&[f(3);9]),Err(GkrError::PointDimension));
    assert_eq!(family.wiring(0,&[],&[f(2);9],&[f(3);8]),Err(GkrError::PointDimension));
}

#[test]
fn one_ratio_matches_bounded_sparse_proof(){
    source_family_and_tuple_controls();sparse_metadata_admission();typed_admission_before_callbacks();
    proof_differentials();message_state_and_factor_controls();actual_consumer_mutants();
}

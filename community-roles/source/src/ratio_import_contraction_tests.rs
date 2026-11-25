//! Ordered source tuples through whole-X producer, old proof consumer and codec.
use ark_bn254::Fr;
use ark_ff::{One, PrimeField, Zero};
use num_bigint::BigUint;
use crate::{gkr::{self, Gate, GkrError, GkrProof}, implicit_witness::Witness,
    legacy_envelope_map::Map, ratio_contraction::{self as ratio, RoundRecord},
    ratio_import_contraction::{self as join, AdmittedJoin, AdmissionError, Descriptor,
        Order, Padding, Role}, sparse::{self, Circuit, Term}, transcript::Transcript};

fn f(n:u64)->Fr{Fr::from(n)}
fn power(n:usize)->Fr{
    let value=BigUint::from(1u8)<<n;Fr::from_le_bytes_mod_order(&value.to_bytes_le())
}
fn decimal(text:&str)->Fr{
    let value=BigUint::parse_bytes(text.as_bytes(),10).unwrap();
    Fr::from_le_bytes_mod_order(&value.to_bytes_le())
}
fn weight(index:usize,point:&[Fr])->Fr{
    let mut value=Fr::one();
    for(bit,z)in point.iter().enumerate(){value*=if index>>bit&1==1{*z}else{Fr::one()-z};}value
}
fn word(x:&[Fr],start:usize,width:usize)->Fr{
    (0..width).map(|b|power(b)*x[start+b]).sum()
}
fn literal_mle(x:&[Fr],point:&[Fr])->Fr{
    x.iter().enumerate().map(|(i,v)|*v*weight(i,point)).sum()
}
fn independent_line(x:&[Fr],u:&[Fr],v:&[Fr])->Vec<Fr>{
    let mut output=vec![Fr::zero();u.len()+1];
    for(index,value)in x.iter().enumerate(){let mut polynomial=vec![*value];
        for bit in 0..u.len(){
            let(a,b)=if index>>bit&1==1{(u[bit],v[bit]-u[bit])}
                else{(Fr::one()-u[bit],u[bit]-v[bit])};
            let mut next=vec![Fr::zero();polynomial.len()+1];
            for(degree,c)in polynomial.iter().enumerate(){next[degree]+=a*c;next[degree+1]+=b*c;}
            polynomial=next;
        }
        for(a,b)in output.iter_mut().zip(polynomial){*a+=b;}
    }output
}
#[derive(Clone,Copy,Debug)]
enum Fixture{Main,ZeroProduct,Nonboolean,Full}
fn put_word(x:&mut[Fr],start:usize,width:usize,value:u64){
    for bit in 0..width{x[start+bit]=if bit<64&&value>>bit&1==1{Fr::one()}else{Fr::zero()};}
}
fn fixture(id:Fixture)->(Vec<Fr>,usize){
    let mut x=vec![Fr::zero();1024];
    let k=match id{
        Fixture::Main=>{
            for(start,width,value)in [(1,91,122880000),(92,64,65),(156,91,1890461),(247,64,35),
                (504,224,1),(728,64,2),(792,64,1)]{put_word(&mut x,start,width,value);}
            x[900]=f(2);28
        },
        Fixture::ZeroProduct=>{put_word(&mut x,92,64,64);1},
        Fixture::Nonboolean=>{
            for(index,value)in [(504,1),(1,122880000),(92,2),(728,1),(792,63),(156,3),
                (247,122879994),(0,7),(900,5)]{x[index]=f(value);}9
        },
        Fixture::Full=>{
            x.fill(f(2));
            let d=word(&x,504,224);let a=word(&x,1,91);
            x[1]+=f(122880000)*d-a;
            let end=word(&x,728,64);let start=word(&x,792,64);let delta=word(&x,92,64);
            x[92]+=end-start+f(64)-delta;
            let a=word(&x,1,91);let q=word(&x,156,91);let delta=word(&x,92,64);let r=word(&x,247,64);
            x[247]+=a-q*delta-r;
            // Independent pinned-modulus fixture identities; not producer outputs.
            assert_eq!(x[1],decimal("6625676492918941235937365627785944434353064613278619332798881733747481903108"));
            assert_eq!(x[92],decimal("21888242871839275222246405745257275088548364400416034343661310698428389392453"));
            assert_eq!(x[247],decimal("6625676492918941235937365627785944434353064612966658442862072416325483495556"));
            assert_eq!(word(&x,92,64),f(64));
            assert_eq!(word(&x,156,91),decimal("4951760157141521099596496894"));
            assert!(x.iter().all(|v|!v.is_zero()));1024
        },
    };
    assert_eq!(x.iter().filter(|v|!v.is_zero()).count(),k,"{id:?}: fixed K");
    assert_eq!(residuals(&x),[Fr::zero();4],"{id:?}: independent residuals");(x,k)
}
fn residuals(x:&[Fr])->[Fr;4]{
    let a=word(x,1,91);let delta=word(x,92,64);let q=word(x,156,91);let rem=word(x,247,64);
    [a-f(122880000)*word(x,504,224),delta-word(x,728,64)+word(x,792,64)-f(64),
        a-q*delta-rem,Fr::zero()]
}
fn term(row:usize,left:usize,right:usize,c:[Fr;4])->Term{
    Term{row,gate:Gate{left,right,c0:c[0],c1:c[1],c2:c[2],c3:c[3]}}
}
fn push_linear(terms:&mut Vec<Term>,row:usize,base:usize,width:usize,scale:Fr,placeholder:usize){
    for bit in 0..width{terms.push(term(row,base+bit,placeholder,
        [Fr::zero(),scale*power(bit),Fr::zero(),Fr::zero()]));}
}
fn reference()->Circuit{
    let mut terms=Vec::with_capacity(6487);
    push_linear(&mut terms,0,1,91,Fr::one(),0);
    push_linear(&mut terms,0,504,224,-f(122880000),0);
    push_linear(&mut terms,1,92,64,Fr::one(),0);
    push_linear(&mut terms,1,728,64,-Fr::one(),0);
    push_linear(&mut terms,1,792,64,Fr::one(),0);
    terms.push(term(1,0,0,[-f(64),Fr::zero(),Fr::zero(),Fr::zero()]));
    push_linear(&mut terms,2,1,91,Fr::one(),0);
    for p in 0..91{for q in 0..64{
        terms.push(term(2,156+p,92+q,[Fr::zero(),Fr::zero(),Fr::zero(),-power(p+q)]));
    }}
    push_linear(&mut terms,2,247,64,-Fr::one(),0);
    assert_eq!((terms.len(),terms.capacity()),(6487,6487));
    Circuit{input_len:1024,row_count:4,terms}
}
fn raw_reference()->Vec<Term>{
    let mut terms=Vec::with_capacity(6487);let placeholder=2079326208;
    push_linear(&mut terms,32497822,2079982535,91,Fr::one(),placeholder);
    push_linear(&mut terms,32497822,2079265306,224,-f(122880000),placeholder);
    push_linear(&mut terms,32497823,2079982626,64,Fr::one(),placeholder);
    push_linear(&mut terms,32497823,2079851538,64,-Fr::one(),placeholder);
    push_linear(&mut terms,32497823,1073218578,64,Fr::one(),placeholder);
    terms.push(term(32497823,placeholder,placeholder,[-f(64),Fr::zero(),Fr::zero(),Fr::zero()]));
    push_linear(&mut terms,32497824,2079982535,91,Fr::one(),placeholder);
    for p in 0..91{for q in 0..64{
        terms.push(term(32497824,2079982690+p,2079982626+q,
            [Fr::zero(),Fr::zero(),Fr::zero(),-power(p+q)]));
    }}
    push_linear(&mut terms,32497824,2079982781,64,-Fr::one(),placeholder);
    assert_eq!((terms.len(),terms.capacity()),(6487,6487));terms
}
fn map_index(index:usize)->Result<usize,&'static str>{
    if index==2079326208{return Ok(0);}
    let intervals=[(2079982535,503,1),(2079265306,224,504),(2079851538,64,728),(1073218578,64,792)];
    let mut mapped=None;
    for(raw,width,local)in intervals{if let Some(offset)=index.checked_sub(raw){
        if offset<width{if mapped.is_some(){return Err("raw alias");}mapped=Some(local+offset);}
    }}mapped.ok_or("raw wire")
}
fn map_term(t:&Term)->Result<Term,&'static str>{
    let row=match t.row{32497822=>0,32497823=>1,32497824=>2,_=>return Err("raw row")};
    Ok(term(row,map_index(t.gate.left)?,map_index(t.gate.right)?,[t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3]))
}
fn check_reference<R>(circuit:&Circuit,expected:&Circuit,consumer:impl FnOnce()->R)->Result<R,&'static str>{
    if circuit!=expected{return Err("reference tuple fields/order/count");}Ok(consumer())
}
fn source_tuple_controls(){
    let map=Map::new(2048,11,64).unwrap();assert_eq!(map.tier(1983).unwrap(),Some(1));
    let owner=map.terms(1983).unwrap();assert_eq!((owner.len(),owner.capacity()),(17341,32768));
    let mut selected=Vec::with_capacity(6487);
    for t in &owner{if (32497822..=32497824).contains(&t.row){selected.push(t.clone());}}
    assert_eq!((selected.len(),selected.capacity()),(6487,6487));
    let expected=raw_reference();assert_eq!(selected,expected,"every ordered raw tuple");drop(expected);
    let mut mapped=Vec::with_capacity(6487);
    for t in &selected{mapped.push(map_term(t).unwrap());}
    let circuit=reference();assert_eq!(mapped,circuit.terms,"every ordered mapped tuple");
    assert_eq!((0..4).map(|r|mapped.iter().filter(|t|t.row==r).count()).collect::<Vec<_>>(),vec![315,193,5979,0]);
    assert_eq!(mapped.iter().filter(|t|!t.gate.c3.is_zero()).count(),5824);
    assert_eq!(mapped.iter().filter(|t|!t.gate.c1.is_zero()).count(),662);
    assert_eq!(mapped.iter().filter(|t|!t.gate.c0.is_zero()).count(),1);
    assert!(mapped.iter().all(|t|t.gate.c2.is_zero()));
    assert_eq!(map_index(2079982535),Ok(1));assert_eq!(map_index(2079983037),Ok(503));
    assert_eq!(map_index(2079265529),Ok(727));assert_eq!(map_index(2079851601),Ok(791));
    assert_eq!(map_index(1073218641),Ok(855));
    assert_eq!(map_index(2079983038),Err("raw wire"));
    assert_eq!(map_index(2079326209),Err("raw wire"));
    let mut wrong=selected[0].clone();wrong.row+=3;assert_eq!(map_term(&wrong),Err("raw row"));
    for index in[91,379,443]{let mut t=selected[index].clone();t.gate.left-=1048576;
        assert_eq!(map_term(&t),Err("raw wire"),"wrong source import owner {index}");}
    drop(selected);drop(mapped);drop(owner);
    let mut callbacks=0;check_reference(&circuit,&circuit,||{callbacks+=1;}).unwrap();assert_eq!(callbacks,1);
    for fault in 0..15{
        let mut changed=circuit.clone();match fault{
            0=>{changed.terms.remove(1200);},1=>{changed.terms.push(changed.terms[1200].clone());},
            2=>changed.terms[1200].row=3,3=>changed.terms[1200].gate.left+=1,
            4=>changed.terms[1200].gate.right+=1,5=>changed.terms[1200].gate.c0=Fr::one(),
            6=>changed.terms[1200].gate.c1=Fr::one(),7=>changed.terms[1200].gate.c2=Fr::one(),
            8=>changed.terms[1200].gate.c3=-changed.terms[1200].gate.c3,
            9=>changed.terms[1200].gate.c3*=f(2),10=>changed.terms.swap(1200,1201),
            11=>changed.terms[91].gate.c1=-f(122879999),12=>changed.terms[507].gate.c0=-f(63),
            13=>changed.input_len=512,_=>changed.row_count=8,
        }
        assert_eq!(changed.terms.capacity(),if fault==1{12974}else{6487});
        assert!(circuit.terms.capacity()+changed.terms.capacity()<=3*6487);
        callbacks=0;
        assert_eq!(check_reference(&changed,&circuit,||{callbacks+=1;}),Err("reference tuple fields/order/count"));
        assert_eq!(callbacks,0,"reference tuple fault {fault}");
    }
    assert_eq!(std::mem::size_of::<Term>(),152);
    assert_eq!(circuit.terms.capacity()*std::mem::size_of::<Term>(),986024);
    let shape=sparse::validate(&circuit,0).unwrap();
    assert_eq!((shape.input_bits,shape.row_bits,shape.copies,shape.input_len,shape.row_count),(10,2,1,1024,4));
    for field in 0..3{let mut bad=circuit.clone();match field{
        0=>bad.terms[0].row=4,1=>bad.terms[0].gate.left=1024,_=>bad.terms[0].gate.right=1024,
    }assert_eq!(sparse::validate(&bad,0).err(),Some(GkrError::InvalidWireIndex));}
}
fn sparse_geometry_controls(){
    let cases=[(0,4,0,GkrError::InvalidInputWidth),(3,4,0,GkrError::InvalidInputWidth),
        (1024,0,0,GkrError::InvalidLayerWidth),(1024,3,0,GkrError::InvalidLayerWidth),
        (1024,4,4,GkrError::RepetitionLimit),(1<<25,4,0,GkrError::RepeatedSizeLimit),
        (1024,1<<25,0,GkrError::RepeatedSizeLimit),(1<<24,4,1,GkrError::RepeatedSizeLimit)];
    for(input_len,row_count,copies,error)in cases{let empty=Circuit{input_len,row_count,terms:Vec::new()};
        assert_eq!(sparse::validate(&empty,copies).err(),Some(error));}
}
fn typed_admission_controls(){
    use AdmissionError::{Descriptor as D,Protocol as P};
    let canonical=Descriptor::canonical();let mut cases=Vec::new();
    macro_rules! bad{($name:expr,$field:ident,$value:expr,$error:expr)=>{{let mut d=canonical.clone();d.$field=$value;cases.push(($name,d,$error));}}}
    bad!("input-width",input_len,512,D("fixed dimensions"));bad!("input-log",input_log,9,D("fixed dimensions"));
    bad!("input-zero",input_len,0,P(GkrError::InvalidInputWidth));bad!("input-nonpower",input_len,1023,P(GkrError::InvalidInputWidth));
    bad!("row-count",row_count,2,D("fixed dimensions"));bad!("row-log",row_log,1,D("fixed dimensions"));
    bad!("rows-zero",row_count,0,P(GkrError::InvalidLayerWidth));bad!("rows-nonpower",row_count,3,P(GkrError::InvalidLayerWidth));
    bad!("copies",log_copies,1,D("fixed dimensions"));bad!("copies-limit",log_copies,4,P(GkrError::RepetitionLimit));
    bad!("input-limit",input_len,1<<25,P(GkrError::RepeatedSizeLimit));bad!("row-limit",row_count,1<<25,P(GkrError::RepeatedSizeLimit));
    bad!("products",product_count,5823,D("term count"));bad!("terms",term_count,6486,D("term count"));
    bad!("row-terms",row_terms,[315,192,5979],D("term count"));
    bad!("source-pin",source_sha,"different-source",D("canonical descriptor"));
    bad!("n",n,2049,D("canonical descriptor"));bad!("h",h,10,D("canonical descriptor"));bad!("e",e,63,D("canonical descriptor"));
    bad!("tier",tier,2,D("canonical descriptor"));bad!("ratio",ratio,1,D("canonical descriptor"));
    bad!("owner",owner,1959,D("mapping intervals"));bad!("width",width,1048577,D("mapping intervals"));
    bad!("stride",row_stride,16385,D("mapping intervals"));bad!("owner-base",owner_base,2079326209,D("mapping intervals"));
    bad!("window-base",window_base,2079982536,D("mapping intervals"));bad!("window-width",window_width,502,D("mapping intervals"));
    bad!("local-window",local_window,2,D("mapping intervals"));bad!("placeholder",placeholder,1,D("mapping intervals"));
    bad!("raw-placeholder",raw_placeholder,2079326209,D("mapping intervals"));
    bad!("local-row-order",local_rows,[1,0,2],D("canonical descriptor"));
    bad!("TE",te,122879999,D("canonical descriptor"));bad!("offset",offset,63,D("canonical descriptor"));
    bad!("sign",product_sign,1,D("canonical descriptor"));bad!("order",order,Order::DenominatorOuter,D("canonical descriptor"));
    bad!("constant-order",order,Order::ConstantFirst,D("canonical descriptor"));
    bad!("padding",padding,Padding::ExternalOutput,D("canonical descriptor"));
    bad!("owner-overflow",owner,usize::MAX,D("overflow"));bad!("stride-overflow",row_stride,usize::MAX,D("overflow"));
    bad!("window-overflow",window_width,usize::MAX,D("overflow"));
    for index in 0..3{let mut d=canonical.clone();d.raw_rows[index]+=1;cases.push(("raw-row",d,D("mapping intervals")));}
    for rail in 0..7{for coordinate in 0..6{
        let mut d=canonical.clone();let entry=&mut d.rails[rail];
        let error=match coordinate{
            0=>{entry.owner-=1;D("mapping intervals")},
            1=>{entry.source_local+=1;D("mapping intervals")},
            2=>{entry.raw_base+=1;D("mapping intervals")},
            3=>{entry.local+=1;D("mapping intervals")},
            4=>{entry.width-=1;if rail==3||rail==6{D("term count")}else{D("mapping intervals")}},
            _=>{entry.role=if rail==0{Role::Quotient91}else{Role::Numerator91};D("canonical descriptor")},
        };cases.push(("rail-role-origin-range",d,error));
    }}
    let mut cap=canonical.clone();cap.rails[1].width=11523;
    assert_eq!(91*11523+(2*91+224+11523+64+64+64)+1,1060715);
    cases.push(("term-cap",cap,D("term cap")));
    for fault in 0..3{let mut d=canonical.clone();match fault{
        0=>d.rails[2].width=usize::MAX,1=>d.rails[4].raw_base=usize::MAX,_=>d.rails[4].source_local=usize::MAX,
    }cases.push(("rail-overflow",d,D("overflow")));}
    let(x,_)=fixture(Fixture::Main);let witness=Witness::from_dense(&x,1024).unwrap();
    for(name,descriptor,error)in &cases{
        for w in [witness.clone(),Witness::from_dense(&[Fr::zero()],1).unwrap()]{
            let mut callbacks=0;let mut t=Transcript::new(join::DOMAIN);let before=t.bytes_absorbed();
            let result=AdmittedJoin::with_admitted(descriptor.clone(),w,|family|{callbacks+=1;family.bind(&mut t);});
            assert_eq!(result,Err(error.clone()),"{name}: descriptor before witness extent");
            assert_eq!(callbacks,0);assert_eq!(t.bytes_absorbed(),before);assert_eq!(t.challenges(),0);
        }
    }
    let mut callbacks=0;
    let small=Witness::from_dense(&x[..512],512).unwrap();
    assert_eq!(AdmittedJoin::with_admitted(canonical,small,|_|{callbacks+=1;}),Err(P(GkrError::InvalidInputWidth)));
    assert_eq!(callbacks,0);
}
fn residual_admission_controls(){
    let(x,_)=fixture(Fixture::Main);let circuit=reference();
    for(index,change,expected,row)in [
        (504,-Fr::one(),[f(122880000),Fr::zero(),Fr::zero(),Fr::zero()],0),
        (728,Fr::one(),[Fr::zero(),-Fr::one(),Fr::zero(),Fr::zero()],1),
        (792,-Fr::one(),[Fr::zero(),-Fr::one(),Fr::zero(),Fr::zero()],1),
        (156,-Fr::one(),[Fr::zero(),Fr::zero(),f(65),Fr::zero()],2),
        (247,-Fr::one(),[Fr::zero(),Fr::zero(),Fr::one(),Fr::zero()],2),
        (1,Fr::one(),[Fr::one(),Fr::zero(),Fr::one(),Fr::zero()],0),
        (92,-Fr::one(),[Fr::zero(),-Fr::one(),f(1890461),Fr::zero()],1),
    ]{
        let mut changed=x.clone();changed[index]+=change;assert_eq!(residuals(&changed),expected);
        reject_residual(&circuit,&changed,row);
    }
    let allzero=vec![Fr::zero();1024];
    assert_eq!(residuals(&allzero),[Fr::zero(),-f(64),Fr::zero(),Fr::zero()]);reject_residual(&circuit,&allzero,1);
    let mut cancellation=x.clone();cancellation[1]+=f(4);cancellation[728]+=Fr::one();
    let residual=residuals(&cancellation);assert_eq!(residual,[f(4),-Fr::one(),f(4),Fr::zero()]);
    let r=[f(2),f(3)];let weights:[Fr;4]=std::array::from_fn(|row|weight(row,&r));
    assert_eq!(weights,[f(2),-f(4),-f(3),f(6)]);
    assert_eq!(weights.iter().zip(residual).map(|(a,b)|*a*b).sum::<Fr>(),Fr::zero());
    reject_residual(&circuit,&cancellation,0);
}
fn reject_residual(circuit:&Circuit,x:&[Fr],row:usize){
    let mut callbacks=0;let mut t=Transcript::new(join::DOMAIN);let before=t.bytes_absorbed();
    let w=Witness::from_dense(x,1024).unwrap();
    assert_eq!(AdmittedJoin::with_admitted(Descriptor::canonical(),w,|family|{callbacks+=1;family.bind(&mut t);}),
        Err(AdmissionError::Residual(row)));
    assert_eq!(callbacks,0);assert_eq!(t.bytes_absorbed(),before);assert_eq!(t.challenges(),0);
    let mut old=Transcript::new(join::DOMAIN);let old_before=old.bytes_absorbed();
    assert_eq!(sparse::prove_with_binding(circuit,x,0,&mut old,|_|{callbacks+=1;}).err(),Some(GkrError::NonzeroOutput));
    assert_eq!(callbacks,0);assert_eq!(old.bytes_absorbed(),old_before);assert_eq!(old.challenges(),0);
}
fn binding_bytes(family:&AdmittedJoin){
    let text=String::from_utf8(family.descriptor_bytes()).unwrap();
    assert!(text.ends_with('\n')&&!text.contains('\r')&&!text.contains('\0'));
    let expected=concat!(
        "version=ratio-import-contraction-three-rows-v1\n",
        "source-map-sha256=AFEA8F2B7B54302FB75C7613ACA87E05AA02FAE842AF92DB38CB2B66DC0F23D9\n",
        "source-n=2048\nsource-h=11\nsource-e=64\nsource-owner=1983\nsource-tier=1\nsource-ratio-index=0\n",
        "source-width=1048576\nsource-row-stride=16384\nsource-owner-base=2079326208\nsource-rows=32497822,32497823,32497824\n",
        "source-window=2079982535,503\nsource-placeholder=2079326208\n",
        "source-A=Numerator91,1983,656327,2079982535,91\n",
        "source-Delta=Delta64,1983,656418,2079982626,64\n",
        "source-Q=Quotient91,1983,656482,2079982690,91\n",
        "source-R=Remainder64,1983,656573,2079982781,64\n",
        "import-D=Difficulty224,1982,987674,2079265306,224\n",
        "import-end=TimestampEnd64,1983,525330,2079851538,64\n",
        "import-start=TimestampStart64,1023,525330,1073218578,64\n",
        "mapping=window-to-one-plus-offset-imports-to-504-728-792-placeholder-zero-v1\n",
        "local-input-width=1024\nlocal-input-log=10\nlocal-row-count=4\nlocal-row-log=2\nlocal-rows=0,1,2\n",
        "local-window=1,503\nlocal-placeholder=0\n",
        "local-A=1,91\nlocal-Delta=92,64\nlocal-Q=156,91\nlocal-R=247,64\n",
        "local-import-D=504,224\nlocal-import-end=728,64\nlocal-import-start=792,64\n",
        "log-copies=0\nrow0=A-122880000*D\nrow1=Delta-end+start-64\nrow2=A-Q*Delta-R\nrow3=zero-polynomial-no-output\n",
        "linear-channel=c1\nlinear-coefficient=signed-public-scale-times-2-power-bit\nlinear-right=placeholder\n",
        "constant-channel=c0\nconstant=-64\nconstant-left-right=placeholder\n",
        "product-channel=c3\nproduct-scale=-1\nproduct-coefficient=-2-power-p-plus-q\n",
        "order=source-rows-quotient-p-outer-delta-q-inner\nrow-term-counts=315,193,5979\nproduct-term-count=5824\nterm-count=6487\n",
    );assert_eq!(text,expected);assert!(!text.contains("fixture=")&&!text.contains("fixed-E"));
    assert_eq!(family.descriptor(),&Descriptor::canonical());
}
fn dense_first(circuit:&Circuit,x:&[Fr],r:&[Fr])->(Vec<Fr>,Vec<Fr>){
    let(mut a,mut b)=(vec![Fr::zero();1024],vec![Fr::zero();1024]);
    for t in &circuit.terms{let g=&t.gate;let rho=weight(t.row,r);
        a[g.left]+=rho*(g.c1+g.c3*x[g.right]);b[g.left]+=rho*(g.c0+g.c2*x[g.right]);}(a,b)
}
fn dense_second(circuit:&Circuit,r:&[Fr],u:&[Fr],left:Fr)->(Vec<Fr>,Vec<Fr>){
    let(mut c,mut d)=(vec![Fr::zero();1024],vec![Fr::zero();1024]);
    for t in &circuit.terms{let g=&t.gate;let coefficient=weight(t.row,r)*weight(g.left,u);
        c[g.right]+=coefficient*(g.c2+g.c3*left);d[g.right]+=coefficient*(g.c0+g.c1*left);}(c,d)
}
fn compare_word(w:&Witness,dense:&[Fr],label:&str){
    assert_eq!(w.extent(),dense.len());
    for(i,value)in dense.iter().enumerate(){assert_eq!(w.value(i).unwrap(),*value,"{label} cell{i}");}
}
fn replay(family:&AdmittedJoin,proof:&GkrProof)->(Vec<Fr>,Vec<Fr>,Fr,Transcript){
    let mut t=Transcript::new(join::DOMAIN);family.bind(&mut t);
    let output=gkr::output_point(4,&mut t);gkr::append_usize(&mut t,b"gkr-layer-index",0);
    let mut challenges=Vec::with_capacity(20);
    for polynomial in &proof.layers[0].rounds{
        gkr::append_polynomial(&mut t,b"gkr-sumcheck-polynomial",polynomial);
        challenges.push(t.challenge_scalar(b"gkr-sumcheck-challenge"));
    }
    let layer=&proof.layers[0];t.append_scalar(b"gkr-left-value",&layer.left_value);
    t.append_scalar(b"gkr-right-value",&layer.right_value);
    gkr::append_polynomial(&mut t,b"gkr-line-polynomial",&layer.line_coefficients);
    let lambda=t.challenge_scalar(b"gkr-line-challenge");(output,challenges,lambda,t)
}
fn proof_differentials(){
    let circuit=reference();let shape=sparse::validate(&circuit,0).unwrap();
    let mut frozen_binding=None;
    for id in[Fixture::Main,Fixture::ZeroProduct,Fixture::Nonboolean,Fixture::Full]{
        let(x,k)=fixture(id);let w=Witness::from_dense(&x,1024).unwrap();assert_eq!(w.retained_capacity(),k);
        let family=AdmittedJoin::new(Descriptor::canonical(),w).unwrap();binding_bytes(&family);
        let binding=family.descriptor_bytes();
        if let Some(bytes)=&frozen_binding{assert_eq!(&binding,bytes,"same statement across variable fixtures");}
        else{frozen_binding=Some(binding);}
        let mut old_t=Transcript::new(join::DOMAIN);
        let(expected,expected_claim)=sparse::prove_with_binding(&circuit,&x,0,&mut old_t,|t|family.bind(t)).unwrap();
        let mut actual_t=Transcript::new(join::DOMAIN);let mut records=Vec::with_capacity(20);
        let(actual,claim)=family.prove(&mut actual_t,|r|records.push(r.clone())).unwrap();
        assert_eq!(actual,expected,"{id:?}: full proof");assert_eq!(claim,expected_claim);assert_eq!(records.len(),20);
        assert_eq!((actual_t.challenges(),actual_t.raw_queries(),actual_t.bytes_absorbed()),
            (old_t.challenges(),old_t.raw_queries(),old_t.bytes_absorbed()));assert_eq!(actual_t.challenges(),23);
        let continuation=actual_t.challenge_scalar(b"ratio-import-test-continuation");
        assert_eq!(continuation,old_t.challenge_scalar(b"ratio-import-test-continuation"));
        let bytes=gkr::encode_proof(&actual).unwrap();assert_eq!(bytes.len(),2336);
        assert_eq!(bytes,gkr::encode_proof(&expected).unwrap());
        assert_eq!(sparse::decode_proof(&circuit,0,&bytes).unwrap(),actual);
        let mut checked_t=Transcript::new(join::DOMAIN);
        assert_eq!(family.verify(&actual,&mut checked_t).unwrap(),claim);
        let mut old_checked=Transcript::new(join::DOMAIN);
        assert_eq!(gkr::verify_with_wiring(&[shape.input_bits],shape.row_count,&expected,&mut old_checked,
            |t|family.bind(t),|_,r,u,v|sparse::wiring(&circuit,&shape,r,u,v)).unwrap(),claim);
        assert_eq!((checked_t.challenges(),checked_t.raw_queries(),checked_t.bytes_absorbed()),
            (old_checked.challenges(),old_checked.raw_queries(),old_checked.bytes_absorbed()));
        let(output,challenges,_,mut replayed)=replay(&family,&actual);assert_eq!(replayed.challenges(),23);
        assert_eq!(replayed.challenge_scalar(b"ratio-import-test-continuation"),continuation);
        assert_eq!(literal_mle(&x,&claim.point),claim.value);let(u,v)=challenges.split_at(10);
        assert_eq!(actual.layers[0].line_coefficients,independent_line(&x,u,v));
        let(a,b)=family.first_coefficients(&output).unwrap();let(da,db)=dense_first(&circuit,&x,&output);
        compare_word(&a,&da,"A");compare_word(&b,&db,"B");
        let(c,d)=family.second_coefficients(&output,u,expected.layers[0].left_value).unwrap();
        let(dc,dd)=dense_second(&circuit,&output,u,expected.layers[0].left_value);
        compare_word(&c,&dc,"C");compare_word(&d,&dd,"D");
        assert!(a.entries().len()<=662&&b.entries().len()<=1&&c.entries().len()<=64&&d.entries().len()<=1);
        let mut witness_visits=0;let mut coefficient_visits=0;let mut queries=0;
        for phase in 0..2{
            let(mut aa,mut bb)=if phase==0{(da.clone(),db.clone())}else{(dc.clone(),dd.clone())};let mut xx=x.clone();
            for round in 0..10{let record:&RoundRecord=&records[phase*10+round];
                assert_eq!((record.phase,record.round,record.extent),(phase,round,xx.len()));
                assert_eq!(record.polynomial.to_vec(),gkr::quadratic_message(&aa,&bb,&xx));
                assert_eq!(record.challenge,challenges[phase*10+round]);
                assert_eq!(record.support,[aa.iter().filter(|v|!v.is_zero()).count(),
                    bb.iter().filter(|v|!v.is_zero()).count(),xx.iter().filter(|v|!v.is_zero()).count()]);
                assert_eq!(record.work.value_queries,6*record.work.pair_count);
                assert!(record.work.pair_count<=if phase==0{332}else{33});
                assert!(record.work.pair_capacity<=if phase==0{663}else{65});
                witness_visits+=record.support[2];coefficient_visits+=record.support[0]+record.support[1];queries+=record.work.value_queries;
                gkr::fold(&mut aa,record.challenge);gkr::fold(&mut bb,record.challenge);gkr::fold(&mut xx,record.challenge);
            }
        }
        assert!(witness_visits<=20*k&&coefficient_visits<=7280&&queries<=21900);
        let(line,work)=family.witness().line_counted(u,v).unwrap();assert_eq!(line,actual.layers[0].line_coefficients);
        assert_eq!((work.entry_visits,work.coefficient_updates,work.output_scalars,work.scratch_scalars),(k,65*k,11,11));
        assert_eq!(std::mem::size_of::<Fr>(),32);assert_eq!(std::mem::size_of::<(usize,Fr)>(),40);
        assert_eq!(family.witness().retained_capacity()*40,k*40);assert!(k*40<=40960);
    }
}
fn phase_and_weight_controls(){
    let(x,_)=fixture(Fixture::Main);let family=AdmittedJoin::new(Descriptor::canonical(),Witness::from_dense(&x,1024).unwrap()).unwrap();
    let circuit=reference();let(u,v)=(vec![f(2);10],vec![f(3);10]);let left=literal_mle(&x,&u);
    for r in[vec![f(2),f(3)],vec![Fr::one(),f(2)],vec![Fr::zero(),Fr::zero()],
        vec![Fr::one(),Fr::zero()],vec![Fr::zero(),Fr::one()],vec![Fr::one(),Fr::one()]]{
        let(a,b)=family.first_coefficients(&r).unwrap();let(da,db)=dense_first(&circuit,&x,&r);
        let(c,d)=family.second_coefficients(&r,&u,left).unwrap();let(dc,dd)=dense_second(&circuit,&r,&u,left);
        compare_word(&a,&da,"fixed r A");compare_word(&b,&db,"fixed r B");
        compare_word(&c,&dc,"fixed r C");compare_word(&d,&dd,"fixed r D");
        assert_eq!(family.wiring(0,&r,&u,&v).unwrap(),sparse::wiring(&circuit,&sparse::validate(&circuit,0).unwrap(),&r,&u,&v).unwrap());
        if r==vec![Fr::one(),f(2)]{assert!(da[1..92].iter().all(|v|v.is_zero()));}
        if r==vec![Fr::one(),Fr::one()]{assert!(a.entries().is_empty()&&b.entries().is_empty()&&c.entries().is_empty()&&d.entries().is_empty());}
        for phase in 0..2{
            let(mut aw,mut bw)=if phase==0{(a.clone(),b.clone())}else{(c.clone(),d.clone())};
            let(mut aa,mut bb)=if phase==0{(da.clone(),db.clone())}else{(dc.clone(),dd.clone())};
            let mut ww=family.witness().clone();let mut xx=x.clone();
            for _ in 0..10{
                assert_eq!(ratio::quadratic(&aw,&bw,&ww).unwrap().0.to_vec(),gkr::quadratic_message(&aa,&bb,&xx));
                aw=aw.fold(&[f(2)]).unwrap();bw=bw.fold(&[f(2)]).unwrap();ww=ww.fold(&[f(2)]).unwrap();
                gkr::fold(&mut aa,f(2));gkr::fold(&mut bb,f(2));gkr::fold(&mut xx,f(2));
            }
        }
    }
    // r=[1,2] above masks the A rail. Here nonzero dyadic coefficients cancel.
    {
        let(nx,_)=fixture(Fixture::Nonboolean);
        let nf=AdmittedJoin::new(Descriptor::canonical(),Witness::from_dense(&nx,1024).unwrap()).unwrap();
        let nr=[f(2),f(3)];let nl=literal_mle(&nx,&u);
        assert_eq!(nl,decimal("21888242871839275222246405745257275088548364400416034343698204186559834097592"));
        let nq=(0..91).map(|p|power(p)*weight(156+p,&u)).sum::<Fr>();
        assert_eq!(nq,decimal("114652423099798554354414575248"));assert!(!nq.is_zero()&&!nl.is_zero());
        let(na,nb)=nf.first_coefficients(&nr).unwrap();
        let(nc,nd)=nf.second_coefficients(&nr,&u,nl).unwrap();
        assert_eq!((na.entries().len(),nb.entries().len(),nc.entries().len(),nd.entries().len()),(662,1,64,1));
        let(af,aw)=na.fold_counted(&[-Fr::one()]).unwrap();
        let bf=nb.fold(&[-Fr::one()]).unwrap();let cf=nc.fold(&[-Fr::one()]).unwrap();let df=nd.fold(&[-Fr::one()]).unwrap();
        assert_eq!(af.entries().iter().map(|v|v.0).collect::<Vec<_>>(),vec![0,123,155]);
        assert_eq!(af.entries(),&[(0,Fr::one()),(123,decimal("14855280471424563298789490685")),(155,decimal("55340232221128654848"))]);
        assert_eq!(nb.entries(),&[(0,f(256))]);assert_eq!(bf.entries(),&[(0,f(512))]);
        assert_eq!((af.entries().len(),bf.entries().len(),cf.entries().len(),df.entries().len()),(3,1,0,1));
        assert_eq!((aw.entry_visits,aw.aggregation_capacity,aw.retained_entries),(662,662,3));
        let(mut aa,mut bb)=dense_first(&circuit,&nx,&nr);
        let(mut cc,mut dd)=dense_second(&circuit,&nr,&u,nl);
        let mut xx=nx.clone();for values in [&mut aa,&mut bb,&mut cc,&mut dd,&mut xx]{gkr::fold(values,-Fr::one());}
        compare_word(&af,&aa,"cancelled A");compare_word(&bf,&bb,"cancelled B");
        compare_word(&cf,&cc,"cancelled C");compare_word(&df,&dd,"cancelled D");
        let xf=nf.witness().fold(&[-Fr::one()]).unwrap();
        assert_eq!(ratio::quadratic(&af,&bf,&xf).unwrap().0.to_vec(),gkr::quadratic_message(&aa,&bb,&xx));
        assert_eq!(ratio::quadratic(&cf,&df,&xf).unwrap().0.to_vec(),gkr::quadratic_message(&cc,&dd,&xx));
    }
    let r=[f(2),f(3)];let(c,d)=family.second_coefficients(&r,&u,left).unwrap();
    let(dc,dd)=dense_second(&circuit,&r,&u,left);let expected=gkr::quadratic_message(&dc,&dd,&x);
    let mut missing_linear=dd.clone();missing_linear[0]=-f(64)*weight(1,&r)*weight(0,&u);
    assert!(!(dd[0]-missing_linear[0]).is_zero(),"fixed missing-c1 fixture decisive");
    assert_ne!(ratio::quadratic(&c,&Witness::from_dense(&missing_linear,1024).unwrap(),family.witness()).unwrap().0.to_vec(),expected);
    let qweight=(0..91).map(|p|power(p)*weight(156+p,&u)).sum::<Fr>();
    assert!(!qweight.is_zero()&&!left.is_zero()&&left!=Fr::one());
    for fault in 0..3{
        let scale=match fault{0=>-weight(2,&r)*left,1=>-weight(2,&r)*qweight,_=>-qweight*left};
        let mut bad_c=dc.clone();for bit in 0..64{bad_c[92+bit]=scale*power(bit);}
        assert_ne!(ratio::quadratic(&Witness::from_dense(&bad_c,1024).unwrap(),&d,family.witness()).unwrap().0.to_vec(),expected,"missing product factor{fault}");
    }
    let stale=family.witness().fold(&u).unwrap();let mut callbacks=0;
    assert_eq!(ratio::quadratic(&c,&d,&stale).map(|_|{callbacks+=1;}),Err(GkrError::PointDimension));assert_eq!(callbacks,0);
    let mut changed=x.clone();changed[900]+=Fr::one();assert_eq!(residuals(&changed),[Fr::zero();4]);
    let other=AdmittedJoin::new(Descriptor::canonical(),Witness::from_dense(&changed,1024).unwrap()).unwrap();
    assert_eq!(other.descriptor_bytes(),family.descriptor_bytes());
    assert_eq!(literal_mle(&changed,&u)-literal_mle(&x,&u),f(16));
    assert_eq!(literal_mle(&changed,&v)-literal_mle(&x,&v),f(5184));
    let before=independent_line(&x,&u,&v);let after=independent_line(&changed,&u,&v);
    let delta=[16,128,456,952,1289,1182,743,316,87,14,1].map(f).to_vec();
    assert_eq!(after.iter().zip(&before).map(|(a,b)|*a-*b).collect::<Vec<_>>(),delta);
    assert_eq!(family.witness().line(&u,&v).unwrap(),before);assert_eq!(other.witness().line(&u,&v).unwrap(),after);
    let mut truncated=x.clone();truncated[900]=Fr::zero();
    let mut whole=family.witness().clone();let mut cut=Witness::from_dense(&truncated,1024).unwrap();
    let(mut a,mut b)=family.first_coefficients(&r).unwrap();let mut difference=false;
    for _ in 0..10{
        if ratio::quadratic(&a,&b,&whole).unwrap().0!=ratio::quadratic(&a,&b,&cut).unwrap().0{difference=true;}
        a=a.fold(&[f(2)]).unwrap();b=b.fold(&[f(2)]).unwrap();whole=whole.fold(&[f(2)]).unwrap();cut=cut.fold(&[f(2)]).unwrap();
    }assert!(difference,"complete-X off-rail mutation reaches actual message");
    assert_ne!(family.witness().fold(&[f(2),f(3)]).unwrap(),family.witness().fold(&[f(3),f(2)]).unwrap());
    // Each output component has its own nonzero coefficient at this point.
    let shape=sparse::validate(&circuit,0).unwrap();let actual=family.wiring(0,&r,&u,&v).unwrap();
    for row in 0..3{
        let mut changed=circuit.clone();for t in &mut changed.terms{if t.row==row{t.row=3;}}
        assert_ne!(sparse::wiring(&changed,&shape,&r,&u,&v).unwrap(),actual,"displaced row{row}");
        changed.terms.retain(|t|t.row!=3);
        assert_ne!(sparse::wiring(&changed,&shape,&r,&u,&v).unwrap(),actual,"dropped row weight{row}");
    }
    let mut swapped=circuit.clone();for t in &mut swapped.terms{
        t.row=match t.row{0=>1,1=>0,row=>row};
    }
    assert_ne!(sparse::wiring(&swapped,&shape,&r,&u,&v).unwrap(),actual,"swapped row weights");
    drop(swapped);
    let mut pad=circuit.clone();pad.terms.push(term(3,0,0,[Fr::one(),Fr::zero(),Fr::zero(),Fr::zero()]));
    assert_eq!(pad.terms.capacity(),12974);
    assert!(circuit.terms.capacity()+pad.terms.capacity()<=3*6487);
    assert_ne!(sparse::wiring(&pad,&shape,&r,&u,&v).unwrap(),actual,"nonzero padding polynomial");
    assert_eq!(family.first_coefficients(&[f(2)]).err(),Some(GkrError::PointDimension));
    assert_eq!(family.second_coefficients(&r,&u[..9],left).err(),Some(GkrError::PointDimension));
}
fn actual_consumer_controls(){
    let(x,_)=fixture(Fixture::Main);let family=AdmittedJoin::new(Descriptor::canonical(),Witness::from_dense(&x,1024).unwrap()).unwrap();
    let mut t=Transcript::new(join::DOMAIN);let(proof,_)=family.prove(&mut t,|_|{}).unwrap();
    for fault in 0..12{
        let mut p=proof.clone();let expected=match fault{
            0=>{p.layers.clear();GkrError::ProofLayerCount},
            1=>{p.layers[0].rounds.pop();GkrError::SumcheckRoundCount},
            2=>{p.layers[0].rounds[0].push(Fr::zero());GkrError::SumcheckDegree},
            3=>{p.layers[0].line_coefficients.pop();GkrError::LineDegree},
            4=>{p.layers[0].left_value+=Fr::one();GkrError::TerminalExpression},
            5=>{p.layers[0].right_value+=Fr::one();GkrError::TerminalExpression},
            6=>{p.layers[0].line_coefficients[0]+=Fr::one();GkrError::LineEndpoints},
            7=>{p.layers[0].line_coefficients[1]+=Fr::one();GkrError::LineEndpoints},
            8=>{p.layers.push(p.layers[0].clone());GkrError::ProofLayerCount},
            9=>{p.layers[0].rounds.push(vec![Fr::zero();3]);GkrError::SumcheckRoundCount},
            10=>{p.layers[0].rounds[0].pop();GkrError::SumcheckDegree},
            _=>{p.layers[0].line_coefficients.push(Fr::zero());GkrError::LineDegree},
        };
        assert_eq!(family.verify(&p,&mut Transcript::new(join::DOMAIN)),Err(expected),"proof fault{fault}");
    }
    let mut initial=proof.clone();initial.layers[0].rounds[0][0]+=Fr::one();
    assert_eq!(family.verify(&initial,&mut Transcript::new(join::DOMAIN)),Err(GkrError::SumcheckIdentity));
    let mut round=proof.clone();round.layers[0].rounds[0][1]-=Fr::one();round.layers[0].rounds[0][2]+=Fr::one();
    let original=&proof.layers[0].rounds[0];let changed=&round.layers[0].rounds[0];
    assert_eq!(changed[0],original[0]);assert_eq!(gkr::eval_polynomial(changed,Fr::one()),gkr::eval_polynomial(original,Fr::one()));
    let mut rt=Transcript::new(join::DOMAIN);family.bind(&mut rt);gkr::output_point(4,&mut rt);
    gkr::append_usize(&mut rt,b"gkr-layer-index",0);gkr::append_polynomial(&mut rt,b"gkr-sumcheck-polynomial",changed);
    let z=rt.challenge_scalar(b"gkr-sumcheck-challenge");let claim=gkr::eval_polynomial(changed,z);
    let next=&proof.layers[0].rounds[1];assert_ne!(next[0]+gkr::eval_polynomial(next,Fr::one()),claim);
    assert_eq!(family.verify(&round,&mut Transcript::new(join::DOMAIN)),Err(GkrError::SumcheckIdentity));
    let mut line=proof.clone();line.layers[0].line_coefficients[1]-=Fr::one();line.layers[0].line_coefficients[2]+=Fr::one();
    assert_eq!(line.layers[0].line_coefficients[0],proof.layers[0].left_value);
    assert_eq!(gkr::eval_polynomial(&line.layers[0].line_coefficients,Fr::one()),proof.layers[0].right_value);
    let mutated=family.verify(&line,&mut Transcript::new(join::DOMAIN)).unwrap();
    let(_,challenges,lambda,_)=replay(&family,&line);assert!(lambda!=Fr::zero()&&lambda!=Fr::one());
    assert_eq!(mutated.point,gkr::line_point(&challenges[..10],&challenges[10..],lambda));
    assert_eq!(mutated.value-literal_mle(&x,&mutated.point),lambda*(lambda-Fr::one()));
    assert!(!(mutated.value-literal_mle(&x,&mutated.point)).is_zero());
    for fault in 0..3{
        let mut wrong=Transcript::new(join::DOMAIN);
        let result=gkr::verify_with_wiring(&[10],4,&proof,&mut wrong,|transcript|{
            if fault==0{transcript.append_bytes(b"ratio-import-descriptor-wrong",&family.descriptor_bytes());}
            else if fault==1{transcript.append_scalar(b"unbound-host-A",&word(&x,1,91));family.bind(transcript);}
            else{family.bind(transcript);gkr::output_point(4,transcript);}
        },|i,r,u,v|family.wiring(i,r,u,v));assert!(result.is_err(),"statement/challenge ordering fault{fault}");
    }
    assert_eq!(family.wiring(1,&[f(2);2],&[f(2);10],&[f(3);10]),Err(GkrError::PointDimension));
    assert_eq!(family.wiring(0,&[f(2);1],&[f(2);10],&[f(3);10]),Err(GkrError::PointDimension));
    assert_eq!(family.wiring(0,&[f(2);2],&[f(2);9],&[f(3);10]),Err(GkrError::PointDimension));
    assert_eq!(family.wiring(0,&[f(2);2],&[f(2);10],&[f(3);9]),Err(GkrError::PointDimension));
    let circuit=reference();let bytes=gkr::encode_proof(&proof).unwrap();
    assert!(sparse::decode_proof(&circuit,0,&bytes[..bytes.len()-1]).is_err());
    let mut extra=bytes.clone();extra.push(0);assert!(sparse::decode_proof(&circuit,0,&extra).is_err());
    let mut invalid=bytes.clone();invalid[..32].fill(255);assert!(sparse::decode_proof(&circuit,0,&invalid).is_err());
    assert!(gkr::decode_dimensions(&[9],&bytes).is_err());assert!(gkr::decode_dimensions(&[11],&bytes).is_err());
}

#[test]
fn three_rows_match_bounded_sparse_proof(){
    source_tuple_controls();sparse_geometry_controls();typed_admission_controls();residual_admission_controls();
    proof_differentials();phase_and_weight_controls();actual_consumer_controls();
}

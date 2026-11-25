//! One complete packet: literal source, whole-X producer, old consumer and codec.
use ark_bn254::Fr;
use ark_ff::{BigInteger,Field,One,PrimeField,Zero};
use num_bigint::{BigInt,BigUint};
use crate::{gkr::{self,Gate,GkrError,GkrProof},implicit_witness::Witness,
    legacy_envelope_map::{Map,Inputs,Kind,BANK,RATIO},ratio_contraction::{self as ratio,RoundRecord},
    ratio_packet_contraction::{self as packet,AdmittedPacket,AdmissionError,Descriptor,Order,Padding,AuxRole},
    ratio_import_contraction::{Role,Order as SourceOrder,Padding as SourcePadding},
    sparse::{self,Circuit,Term},transcript::Transcript};

fn f(n:u64)->Fr{Fr::from(n)}
fn pow(n:usize)->Fr{Fr::from_le_bytes_mod_order(&(BigUint::from(1u8)<<n).to_bytes_le())}
fn weight(index:usize,p:&[Fr])->Fr{p.iter().enumerate().fold(Fr::one(),|a,(b,z)|
    a*if index>>b&1==1{*z}else{Fr::one()-z})}
fn word(x:&[Fr],start:usize,width:usize)->Fr{(0..width).map(|b|pow(b)*x[start+b]).sum()}
fn mle(x:&[Fr],p:&[Fr])->Fr{x.iter().enumerate().map(|(i,v)|*v*weight(i,p)).sum()}
fn independent_line(x:&[Fr],u:&[Fr],v:&[Fr])->Vec<Fr>{
    let mut out=vec![Fr::zero();11];
    for(i,value)in x.iter().enumerate(){let mut polynomial=vec![*value];
        for b in 0..10{let(a,s)=if i>>b&1==1{(u[b],v[b]-u[b])}else{(Fr::one()-u[b],u[b]-v[b])};
            let mut next=vec![Fr::zero();polynomial.len()+1];
            for(d,c)in polynomial.iter().enumerate(){next[d]+=a*c;next[d+1]+=s*c;}polynomial=next;
        }for(a,b)in out.iter_mut().zip(polynomial){*a+=b;}
    }out
}
fn put(x:&mut[Fr],start:usize,width:usize,n:u64){
    for b in 0..width{x[start+b]=if b<64&&n>>b&1==1{Fr::one()}else{Fr::zero()};}
}
fn auxiliary(x:&mut[Fr]){
    let mut nz=false;
    for b in 0..64{assert!(x[92+b]==Fr::zero()||x[92+b]==Fr::one());
        nz|=x[92+b]==Fr::one();x[311+b]=if nz{Fr::one()}else{Fr::zero()};}
    x[439]=Fr::zero();let mut borrow=0i8;
    for b in 0..64{assert!(x[247+b]==Fr::zero()||x[247+b]==Fr::one());
        let raw=i8::from(x[247+b]==Fr::one())-i8::from(x[92+b]==Fr::one())-borrow;
        x[375+b]=if raw.rem_euclid(2)==1{Fr::one()}else{Fr::zero()};
        borrow=i8::from(raw<0);x[440+b]=f(borrow as u64);
    }
}
#[derive(Clone,Copy,Debug)]
enum Fixture{Main,ZeroQ,Spare}
fn fixture(id:Fixture)->(Vec<Fr>,usize){
    let mut x=vec![Fr::zero();1024];let zero=matches!(id,Fixture::ZeroQ);
    let words=if zero{[(1,91,0),(92,64,64),(156,91,0),(247,64,0),(504,224,0),(728,64,0),(792,64,0)]}
        else{[(1,91,122880000),(92,64,65),(156,91,1890461),(247,64,35),(504,224,1),(728,64,2),(792,64,1)]};
    for(start,width,n)in words{put(&mut x,start,width,n);}auxiliary(&mut x);x[900]=f(2);
    if matches!(id,Fixture::Spare){x[0]=f(2);x[856..].fill(f(2));}
    let k=match id{Fixture::Main=>210,Fixture::ZeroQ=>176,Fixture::Spare=>378};
    assert_eq!(x.iter().filter(|v|!v.is_zero()).count(),k);
    assert!(residuals(&x).iter().all(Zero::is_zero));
    if !zero{
        assert!(x[311..375].iter().all(|v|*v==Fr::one()));
        for b in 0..64{assert_eq!(x[375+b],if b==1||b>=5{Fr::one()}else{Fr::zero()});}
        assert!(x[439..446].iter().all(Zero::is_zero));assert!(x[446..504].iter().all(|v|*v==Fr::one()));
        assert_eq!((x[311..375].iter().filter(|v|!v.is_zero()).count(),
            x[375..439].iter().filter(|v|!v.is_zero()).count(),x[439..504].iter().filter(|v|!v.is_zero()).count()),(64,60,58));
    }
    let map=Map::new(2048,11,64).unwrap();let imports=map.imports(1983).unwrap();
    assert_eq!((imports.len(),imports.capacity()),(4,4));
    let mut inputs=Inputs::default();let mut import_bits=0;
    for imp in &imports{
        let n=match(imp.kind,imp.owner){
            (Kind::Difficulty,1983)=>1,(Kind::Difficulty,1982)=>u64::from(!zero),
            (Kind::Timestamp,1983)=>if zero{0}else{2},(Kind::Timestamp,1023)=>u64::from(!zero),
            _=>panic!("unexpected source fixture import"),
        };inputs.put(&map,*imp,&BigInt::from(n)).unwrap();import_bits+=imp.width;
    }
    // Reference only: one BANK Vec<bool> plus four typed input words,576 bools.
    assert_eq!(import_bits,576);assert_eq!(std::mem::size_of::<bool>(),1);
    let row=map.generate(1983,&inputs).unwrap();assert_eq!((row.bits.len(),row.bits.capacity()),(BANK,BANK));
    assert_eq!(BANK,7898);
    for b in 0..503{assert_eq!(row.bit(RATIO+b).unwrap(),x[1+b]==Fr::one());}
    let selected=raw_reference();assert!(map.failures_with(&row,&inputs,&selected).unwrap().is_empty());
    (x,k)
}
fn residuals(x:&[Fr])->Vec<Fr>{
    let mut out=vec![Fr::zero();1024];
    for k in 0..503{out[k]=x[1+k]*(x[1+k]-Fr::one());}
    let(a,delta,q,r)=(word(x,1,91),word(x,92,64),word(x,156,91),word(x,247,64));
    out[503]=a-f(122880000)*word(x,504,224);out[504]=delta-word(x,728,64)+word(x,792,64)-f(64);
    out[505]=a-q*delta-r;out[506]=x[311]-x[92];
    for b in 1..64{out[506+b]=x[311+b]-x[92+b]-x[310+b]+x[92+b]*x[310+b];}
    out[570]=x[374]-Fr::one();out[571]=x[439];
    for b in 0..64{out[572+b]=x[247+b]-x[92+b]-x[439+b]-x[375+b]+f(2)*x[440+b];}
    out[636]=x[503]-Fr::one();out
}
fn term(row:usize,l:usize,h:usize,c:[Fr;4])->Term{Term{row,gate:Gate{left:l,right:h,c0:c[0],c1:c[1],c2:c[2],c3:c[3]}}}
fn linear(out:&mut Vec<Term>,row:usize,start:usize,width:usize,scale:Fr,zero:usize){
    for b in 0..width{out.push(term(row,start+b,zero,[Fr::zero(),scale*pow(b),Fr::zero(),Fr::zero()]));}
}
// Literal roster independent of producer callbacks. Raw and local addresses
// are supplied separately; raw conversion never calls the new descriptor.
fn literal(raw:bool)->Vec<Term>{
    let(bank,tier,z,a,delta,q,r,d,end,start,orz,diff,borrow)=if raw{
        (32489472+673,32497822,2079326208,2079982535,2079982626,2079982690,
            2079982781,2079265306,2079851538,1073218578,2079982845,2079982909,2079982973)
    }else{(0,503,0,1,92,156,247,504,728,792,311,375,439)};
    let mut out=Vec::with_capacity(7569);
    for k in 0..503{out.push(term(bank+k,a+k,a+k,[Fr::zero(),-Fr::one(),Fr::zero(),Fr::one()]));}
    linear(&mut out,tier,a,91,Fr::one(),z);linear(&mut out,tier,d,224,-f(122880000),z);
    linear(&mut out,tier+1,delta,64,Fr::one(),z);linear(&mut out,tier+1,end,64,-Fr::one(),z);
    linear(&mut out,tier+1,start,64,Fr::one(),z);out.push(term(tier+1,z,z,[-f(64),Fr::zero(),Fr::zero(),Fr::zero()]));
    linear(&mut out,tier+2,a,91,Fr::one(),z);
    for p in 0..91{for b in 0..64{out.push(term(tier+2,q+p,delta+b,[Fr::zero(),Fr::zero(),Fr::zero(),-pow(p+b)]));}}
    linear(&mut out,tier+2,r,64,-Fr::one(),z);
    linear(&mut out,tier+3,orz,1,Fr::one(),z);linear(&mut out,tier+3,delta,1,-Fr::one(),z);
    for b in 1..64{
        linear(&mut out,tier+3+b,orz+b,1,Fr::one(),z);linear(&mut out,tier+3+b,delta+b,1,-Fr::one(),z);
        linear(&mut out,tier+3+b,orz+b-1,1,-Fr::one(),z);
        out.push(term(tier+3+b,delta+b,orz+b-1,[Fr::zero(),Fr::zero(),Fr::zero(),Fr::one()]));
    }
    linear(&mut out,tier+67,orz+63,1,Fr::one(),z);out.push(term(tier+67,z,z,[-Fr::one(),Fr::zero(),Fr::zero(),Fr::zero()]));
    linear(&mut out,tier+68,borrow,1,Fr::one(),z);
    for b in 0..64{for(base,scale)in[(r,Fr::one()),(delta,-Fr::one()),(borrow,-Fr::one()),(diff,-Fr::one()),(borrow+1,f(2))]{
        linear(&mut out,tier+69+b,base+b,1,scale,z);
    }}
    linear(&mut out,tier+133,borrow+64,1,Fr::one(),z);out.push(term(tier+133,z,z,[-Fr::one(),Fr::zero(),Fr::zero(),Fr::zero()]));
    assert_eq!((out.len(),out.capacity()),(7569,7569));out
}
fn raw_reference()->Vec<Term>{literal(true)}
fn reference()->Circuit{Circuit{input_len:1024,row_count:1024,terms:literal(false)}}
fn map_wire(raw:usize)->Result<usize,&'static str>{
    if raw==2079326208{return Ok(0);}
    for(start,width,local)in[(2079982535,503,1),(2079265306,224,504),(2079851538,64,728),(1073218578,64,792)]{
        if let Some(offset)=raw.checked_sub(start){if offset<width{return Ok(local+offset);}}
    }Err("raw wire")
}
fn map_term(t:&Term)->Result<Term,&'static str>{
    let row=if(32490145..32490648).contains(&t.row){t.row-32490145}
        else if(32497822..32497956).contains(&t.row){503+t.row-32497822}else{return Err("raw row")};
    Ok(term(row,map_wire(t.gate.left)?,map_wire(t.gate.right)?,[t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3]))
}
fn checked_reference<R>(c:&Circuit,expected:&Circuit,consumer:impl FnOnce()->R)->Result<R,&'static str>{
    if c!=expected{return Err("tuple/order/schema");}Ok(consumer())
}
fn source_tuple_controls(){
    let map=Map::new(2048,11,64).unwrap();assert_eq!(map.tier(1983).unwrap(),Some(1));
    let owner=map.terms(1983).unwrap();assert_eq!((owner.len(),owner.capacity()),(17341,32768));
    let mut selected=Vec::with_capacity(7569);
    for t in &owner{if(32490145..32490648).contains(&t.row)||(32497822..32497956).contains(&t.row){selected.push(t.clone());}}
    assert_eq!((selected.len(),selected.capacity()),(7569,7569));
    let expected=raw_reference();assert_eq!(selected,expected);drop(expected);
    let mut mapped=Vec::with_capacity(7569);for t in &selected{mapped.push(map_term(t).unwrap());}
    let circuit=reference();assert_eq!(mapped,circuit.terms);
    assert_eq!([mapped.iter().filter(|t|!t.gate.c0.is_zero()).count(),mapped.iter().filter(|t|!t.gate.c1.is_zero()).count(),
        mapped.iter().filter(|t|!t.gate.c2.is_zero()).count(),mapped.iter().filter(|t|!t.gate.c3.is_zero()).count()],[3,1679,0,6390]);
    assert_eq!(mapped.iter().filter(|t|t.row<503).count(),503);
    assert_eq!(mapped.iter().filter(|t|(503..506).contains(&t.row)).count(),6487);
    assert_eq!(mapped.iter().filter(|t|(506..570).contains(&t.row)).count(),254);
    assert_eq!(mapped.iter().filter(|t|(571..636).contains(&t.row)).count(),321);
    assert!(mapped.iter().all(|t|t.row<637));
    assert_eq!(mapped.iter().filter(|t|t.row<503&&t.gate.left==t.gate.right).count(),503);
    let mut small_count=0;packet::small(|_,_,_,_|{small_count+=1;Ok(())}).unwrap();assert_eq!(small_count,1745);
    for raw in[2079982535,2079983037,2079265306,2079265529,2079851538,2079851601,1073218578,1073218641]{assert!(map_wire(raw).is_ok());}
    for raw in[2079983038,2079326209,2079265529+1,1073218641+1]{assert_eq!(map_wire(raw),Err("raw wire"));}
    let mut badrow=selected[0].clone();badrow.row=32490648;assert_eq!(map_term(&badrow),Err("raw row"));
    drop(owner);drop(selected);drop(mapped);
    let mut calls=0;checked_reference(&circuit,&circuit,||{calls+=1;}).unwrap();assert_eq!(calls,1);
    for fault in 0..20{let mut c=circuit.clone();match fault{
        0=>{c.terms.remove(503);},1=>c.terms.push(c.terms[503].clone()),
        2=>c.terms[503].row=637,3=>c.terms[503].gate.left+=1,4=>c.terms[503].gate.right+=1,
        5=>c.terms[503].gate.c0=Fr::one(),6=>c.terms[503].gate.c2=Fr::one(),
        7=>c.terms[503].gate.c1*=f(2),8=>c.terms[1300].gate.c3=-c.terms[1300].gate.c3,
        9=>c.terms.swap(1300,1301),10=>c.terms[0].gate.right=0,11=>c.terms[0].gate.c1=Fr::one(),
        12=>c.terms[0].gate.c3=-Fr::one(),13=>c.terms[594].gate.c1=-f(122879999),
        14=>c.terms[1010].gate.c0=-f(63),15=>c.terms[7568].gate.c0=Fr::one(),
        16=>c.terms[7567].gate.left=502,17=>c.terms[7200].gate.c1=-c.terms[7200].gate.c1,
        18=>c.input_len=512,_=>c.row_count=512,
    }
        assert_eq!(c.terms.capacity(),if fault==1{15138}else{7569});
        assert!(c.terms.capacity()+circuit.terms.capacity()<=3*7569);calls=0;
        assert_eq!(checked_reference(&c,&circuit,||{calls+=1;}),Err("tuple/order/schema"));assert_eq!(calls,0);
    }
    assert_eq!(std::mem::size_of::<Term>(),152);assert_eq!(7569*std::mem::size_of::<Term>(),1150488);
    let shape=sparse::validate(&circuit,0).unwrap();assert_eq!((shape.input_bits,shape.row_bits,shape.copies),(10,10,1));
    for fault in 0..3{let mut c=circuit.clone();match fault{0=>c.terms[0].row=1024,1=>c.terms[0].gate.left=1024,_=>c.terms[0].gate.right=1024}
        assert_eq!(sparse::validate(&c,0).err(),Some(GkrError::InvalidWireIndex));}
}

fn admission_controls(){
    use AdmissionError::{Descriptor as D,Protocol as P};
    let canonical=Descriptor::canonical();let mut cases=Vec::with_capacity(121);
    macro_rules! bad{($field:ident,$value:expr,$error:expr)=>{{let mut d=canonical.clone();d.$field=$value;cases.push((stringify!($field),d,$error));}}}
    bad!(input_len,0,P(GkrError::InvalidInputWidth));bad!(input_len,1023,P(GkrError::InvalidInputWidth));
    bad!(row_count,0,P(GkrError::InvalidLayerWidth));bad!(row_count,1023,P(GkrError::InvalidLayerWidth));
    bad!(log_copies,4,P(GkrError::RepetitionLimit));bad!(input_len,1<<25,P(GkrError::RepeatedSizeLimit));
    bad!(row_count,1<<25,P(GkrError::RepeatedSizeLimit));
    bad!(input_len,512,D("fixed dimensions"));bad!(input_log,9,D("fixed dimensions"));
    bad!(row_count,512,D("fixed dimensions"));bad!(row_log,9,D("fixed dimensions"));bad!(log_copies,1,D("fixed dimensions"));
    bad!(row_base,32489473,D("mapping intervals"));bad!(bank_start,674,D("mapping intervals"));
    bad!(bank_len,502,D("mapping intervals"));bad!(tier_start,8351,D("mapping intervals"));
    bad!(tier_len,133,D("mapping intervals"));bad!(local_tier,504,D("mapping intervals"));
    bad!(local_bank,1,D("canonical descriptor"));bad!(pad_start,638,D("canonical descriptor"));
    bad!(product_count,5823,D("term count"));bad!(small_count,1744,D("term count"));bad!(term_count,7568,D("term count"));
    bad!(order,Order::TierThenBank,D("canonical descriptor"));bad!(padding,Padding::ExternalOutput,D("canonical descriptor"));
    bad!(bank_len,1<<20,D("term cap"));bad!(bank_start,usize::MAX,D("overflow"));
    macro_rules! source_bad{($field:ident,$value:expr,$error:expr)=>{{let mut d=canonical.clone();d.source.$field=$value;cases.push((concat!("source.",stringify!($field)),d,$error));}}}
    source_bad!(source_sha,"different-source",D("source descriptor"));source_bad!(n,2049,D("source descriptor"));
    source_bad!(h,10,D("source descriptor"));source_bad!(e,63,D("source descriptor"));source_bad!(tier,2,D("source descriptor"));
    source_bad!(ratio,1,D("source descriptor"));source_bad!(owner,1959,D("mapping intervals"));
    source_bad!(width,1048577,D("mapping intervals"));source_bad!(row_stride,16385,D("mapping intervals"));
    source_bad!(owner_base,2079326209,D("source descriptor"));source_bad!(window_base,2079982536,D("mapping intervals"));
    source_bad!(window_width,502,D("mapping intervals"));source_bad!(local_window,2,D("source descriptor"));
    source_bad!(raw_placeholder,2079326209,D("source descriptor"));source_bad!(placeholder,1,D("source descriptor"));
    source_bad!(input_len,512,D("source descriptor"));source_bad!(input_log,9,D("source descriptor"));
    source_bad!(row_count,2,D("source descriptor"));source_bad!(row_log,1,D("source descriptor"));source_bad!(log_copies,1,D("source descriptor"));
    source_bad!(local_rows,[1,0,2],D("source descriptor"));source_bad!(row_terms,[315,192,5979],D("source descriptor"));
    source_bad!(product_count,5823,D("source descriptor"));source_bad!(term_count,6486,D("source descriptor"));
    source_bad!(te,122879999,D("source descriptor"));source_bad!(offset,63,D("source descriptor"));source_bad!(product_sign,1,D("source descriptor"));
    source_bad!(order,SourceOrder::DenominatorOuter,D("source descriptor"));source_bad!(order,SourceOrder::ConstantFirst,D("source descriptor"));
    source_bad!(padding,SourcePadding::ExternalOutput,D("source descriptor"));source_bad!(owner,usize::MAX,D("overflow"));
    source_bad!(window_width,usize::MAX,D("overflow"));source_bad!(row_stride,usize::MAX,D("overflow"));
    for i in 0..3{let mut d=canonical.clone();d.source.raw_rows[i]+=1;cases.push(("source row",d,D("source descriptor")));}
    for rail in 0..7{for field in 0..6{let mut d=canonical.clone();let entry=&mut d.source.rails[rail];
        let error=match field{
            0=>{entry.owner-=1;D("mapping intervals")},1=>{entry.source_local+=1;D("mapping intervals")},
            2=>{entry.raw_base+=1;D("mapping intervals")},3=>{entry.local+=1;D("source descriptor")},
            4=>{entry.width-=1;D("source descriptor")},
            _=>{entry.role=if rail==0{Role::Quotient91}else{Role::Numerator91};D("source descriptor")},
        };cases.push(("source rail",d,error));
    }}
    for i in 0..3{for field in 0..4{let mut d=canonical.clone();let entry=&mut d.aux[i];
        let error=match field{
            0=>{entry.role=if i==0{AuxRole::Diff64}else{AuxRole::Or64};D("canonical descriptor")},
            1=>{entry.raw+=1;D("mapping intervals")},2=>{entry.local+=1;D("mapping intervals")},
            _=>{entry.width-=1;if i<2{D("term count")}else{D("canonical descriptor")}},
        };cases.push(("aux",d,error));
    }}
    let mut d=canonical.clone();d.aux[0].width=0;cases.push(("aux zero",d,D("aux width")));
    for i in 0..3{let mut d=canonical.clone();match i{0=>d.source.rails[2].width=usize::MAX,
        1=>d.source.rails[4].raw_base=usize::MAX,_=>d.source.rails[4].source_local=usize::MAX}
        cases.push(("rail overflow",d,D("overflow")));}
    let(x,_)=fixture(Fixture::Main);let witness=Witness::from_dense(&x,1024).unwrap();
    // Exact metadata case count is kept next to the roster rather than inferred from a previous batch.
    assert_eq!((cases.len(),cases.capacity()),(121,121));
    for(name,d,error)in cases{for w in[witness.clone(),Witness::from_dense(&[Fr::zero()],1).unwrap()]{
        let mut calls=0;let mut t=Transcript::new(packet::DOMAIN);let before=t.bytes_absorbed();
        assert_eq!(AdmittedPacket::with_admitted(d.clone(),w,|p|{calls+=1;p.bind(&mut t);}),Err(error.clone()),"{name}");
        assert_eq!((calls,t.bytes_absorbed(),t.challenges()),(0,before,0));
    }}
    let mut calls=0;assert_eq!(AdmittedPacket::with_admitted(canonical,Witness::from_dense(&x[..512],512).unwrap(),|_|{calls+=1;}),
        Err(P(GkrError::InvalidInputWidth)));assert_eq!(calls,0);
}

fn reject_residual(c:&Circuit,x:&[Fr],expected:&[(usize,Fr)]){
    let actual:Vec<_>=residuals(x).into_iter().enumerate().filter(|(_,v)|!v.is_zero()).collect();assert_eq!(actual,expected);
    let mut calls=0;let mut t=Transcript::new(packet::DOMAIN);let before=t.bytes_absorbed();
    assert_eq!(AdmittedPacket::with_admitted(Descriptor::canonical(),Witness::from_dense(x,1024).unwrap(),|p|{calls+=1;p.bind(&mut t);}),
        Err(AdmissionError::Residual(expected[0].0)));
    assert_eq!((calls,t.bytes_absorbed(),t.challenges()),(0,before,0));
    let mut old=Transcript::new(packet::DOMAIN);let before=old.bytes_absorbed();
    assert_eq!(sparse::prove_with_binding(c,x,0,&mut old,|_|{calls+=1;}).err(),Some(GkrError::NonzeroOutput));
    assert_eq!((calls,old.bytes_absorbed(),old.challenges()),(0,before,0));
}
fn residual_controls(){
    let(x,_)=fixture(Fixture::Main);let c=reference();
    let modulus=BigUint::from_bytes_le(&Fr::MODULUS.to_bytes_le());
    assert!((BigUint::from(1u8)<<251)<modulus);assert!((BigUint::from(1u8)<<155)<modulus);
    assert_eq!(122880000u64,1890461*65+35);assert!(35<65&&65>0);
    // Isolated bank equation controls accompany the whole-packet owning-row faults below.
    for value in[Fr::zero(),Fr::one(),f(2),-Fr::one()]{
        let bank=term(0,1,1,[Fr::zero(),-Fr::one(),Fr::zero(),Fr::one()]);
        assert_eq!(bank.gate.c1*value+bank.gate.c3*value*value,value*(value-Fr::one()));
        assert_eq!((value*(value-Fr::one())).is_zero(),value==Fr::zero()||value==Fr::one());
    }
    for(index,change,expected)in[
        (504,-Fr::one(),vec![(503,f(122880000))]),(728,Fr::one(),vec![(504,-Fr::one())]),
        (792,-Fr::one(),vec![(504,-Fr::one())]),(156,-Fr::one(),vec![(505,f(65))]),
        (247,-Fr::one(),vec![(505,Fr::one()),(572,-Fr::one())]),
        (1,Fr::one(),vec![(503,Fr::one()),(505,Fr::one())]),
        (92,-Fr::one(),vec![(504,-Fr::one()),(505,f(1890461)),(506,Fr::one()),(572,Fr::one())]),
        (1,f(2),vec![(0,f(2)),(503,f(2)),(505,f(2))]),
    ]{let mut z=x.clone();z[index]+=change;reject_residual(&c,&z,&expected);}
    for bit in[0,5,63]{let mut z=x.clone();z[311+bit]=Fr::zero();let mut expected=vec![(506+bit,-Fr::one())];
        if bit<63&&x[93+bit].is_zero(){expected.push((507+bit,Fr::one()));}
        if bit==63{expected.push((570,-Fr::one()));}reject_residual(&c,&z,&expected);
    }
    for bit in[0,1,63]{let mut z=x.clone();let change=Fr::one()-f(2)*z[375+bit];z[375+bit]+=change;
        reject_residual(&c,&z,&[(572+bit,-change)]);}
    for bit in[0,1,6,7,63,64]{let mut z=x.clone();let change=Fr::one()-f(2)*z[439+bit];z[439+bit]+=change;
        let expected=if bit==0{vec![(571,change),(572,-change)]}else if bit==64{vec![(635,f(2)*change),(636,change)]}
            else{vec![(571+bit,f(2)*change),(572+bit,-change)]};reject_residual(&c,&z,&expected);
    }
    let allzero=vec![Fr::zero();1024];reject_residual(&c,&allzero,&[(504,-f(64)),(570,-Fr::one()),(636,-Fr::one())]);
    let mut strict=x.clone();put(&mut strict,156,91,1890460);put(&mut strict,247,64,100);auxiliary(&mut strict);
    assert_eq!(word(&strict,1,91)-word(&strict,156,91)*word(&strict,92,64)-word(&strict,247,64),Fr::zero());
    reject_residual(&c,&strict,&[(636,-Fr::one())]);
    // Actual native source encoder and selected raw consumer see the same strict-comparison fault.
    let map=Map::new(2048,11,64).unwrap();let mut inputs=Inputs::default();
    for imp in map.imports(1983).unwrap(){let n=match(imp.kind,imp.owner){(Kind::Difficulty,_)=>1,
        (Kind::Timestamp,1983)=>2,(Kind::Timestamp,1023)=>1,_=>unreachable!()};inputs.put(&map,imp,&BigInt::from(n)).unwrap();}
    let mut row=map.generate(1983,&inputs).unwrap();
    for bit in 0..503{row.set_bit(RATIO+bit,strict[1+bit]==Fr::one()).unwrap();}
    let failures=map.failures_with(&row,&inputs,&raw_reference()).unwrap();
    assert_eq!(failures,vec![(32497955,-Fr::one())]);
    let mut positive=vec![Fr::zero();1024];put(&mut positive,792,64,64);auxiliary(&mut positive);
    reject_residual(&c,&positive,&[(570,-Fr::one()),(636,-Fr::one())]);
    let mut cancel=x.clone();cancel[504]+=Fr::one();cancel[728]-=f(491520000);
    let rows=residuals(&cancel);assert_eq!(weight(503,&[f(2);10]),f(256));assert_eq!(weight(504,&[f(2);10]),f(64));
    assert_eq!(rows.iter().enumerate().map(|(i,v)|weight(i,&[f(2);10])*v).sum::<Fr>(),Fr::zero());
    reject_residual(&c,&cancel,&[(503,-f(122880000)),(504,f(491520000))]);
}

fn dense_first(c:&Circuit,x:&[Fr],r:&[Fr])->(Vec<Fr>,Vec<Fr>){
    let(mut a,mut b)=(vec![Fr::zero();1024],vec![Fr::zero();1024]);
    for t in &c.terms{let g=&t.gate;let rho=weight(t.row,r);
        a[g.left]+=rho*(g.c1+g.c3*x[g.right]);b[g.left]+=rho*(g.c0+g.c2*x[g.right]);}(a,b)
}
fn dense_second(circuit:&Circuit,r:&[Fr],u:&[Fr],left:Fr)->(Vec<Fr>,Vec<Fr>){
    let(mut c,mut d)=(vec![Fr::zero();1024],vec![Fr::zero();1024]);
    for t in &circuit.terms{let g=&t.gate;let k=weight(t.row,r)*weight(g.left,u);
        c[g.right]+=k*(g.c2+g.c3*left);d[g.right]+=k*(g.c0+g.c1*left);}(c,d)
}
fn compare(w:&Witness,x:&[Fr]){
    assert_eq!(w.extent(),x.len());for(i,v)in x.iter().enumerate(){assert_eq!(w.value(i).unwrap(),*v,"cell{i}");}
    assert_eq!(w.retained_capacity(),x.iter().filter(|v|!v.is_zero()).count());
}
fn c1_right_mutant(circuit:&Circuit)->Circuit{
    let mut wrong=circuit.clone();let index=wrong.terms.iter().position(|t|t.row==1&&t.gate.left==2&&t.gate.right==2).unwrap();
    assert_eq!((wrong.terms[index].gate.c1,wrong.terms[index].gate.c3),(-Fr::one(),Fr::one()));
    // Keep the original c3 diagonal and move only its separate c1 contribution.
    wrong.terms[index].gate.c1=Fr::zero();
    wrong.terms.push(term(1,2,0,[Fr::zero(),-Fr::one(),Fr::zero(),Fr::zero()]));
    assert_eq!(wrong.terms.capacity(),15138);assert!(wrong.terms.capacity()+circuit.terms.capacity()<=3*7569);wrong
}
fn replay(p:&AdmittedPacket,proof:&GkrProof)->(Vec<Fr>,Vec<Fr>,Fr,Transcript){
    let mut t=Transcript::new(packet::DOMAIN);p.bind(&mut t);let r=gkr::output_point(1024,&mut t);
    gkr::append_usize(&mut t,b"gkr-layer-index",0);let mut challenges=Vec::with_capacity(20);
    for polynomial in &proof.layers[0].rounds{gkr::append_polynomial(&mut t,b"gkr-sumcheck-polynomial",polynomial);
        challenges.push(t.challenge_scalar(b"gkr-sumcheck-challenge"));}
    let layer=&proof.layers[0];t.append_scalar(b"gkr-left-value",&layer.left_value);t.append_scalar(b"gkr-right-value",&layer.right_value);
    gkr::append_polynomial(&mut t,b"gkr-line-polynomial",&layer.line_coefficients);
    let lambda=t.challenge_scalar(b"gkr-line-challenge");(r,challenges,lambda,t)
}
fn binding_controls(){
    let expected=concat!(
        "version=ratio-packet-contraction-v1\n",
        "source-sha256=AFEA8F2B7B54302FB75C7613ACA87E05AA02FAE842AF92DB38CB2B66DC0F23D9\n",
        "source-n-h-e-owner-tier-index=2048,11,64,1983,1,0\n",
        "source-width-rowstride-wirebase-rowbase=1048576,16384,2079326208,32489472\n",
        "bank-source-rows=673,503\ntier-source-rows=8350,134\nrow-map=bank-first-0-tier-503-v1\n",
        "source-window=2079982535,503\nsource-placeholder=2079326208\n",
        "source-A=Numerator91,1983,656327,2079982535,91\nsource-Delta=Delta64,1983,656418,2079982626,64\n",
        "source-Q=Quotient91,1983,656482,2079982690,91\nsource-R=Remainder64,1983,656573,2079982781,64\n",
        "import-D=Difficulty224,1982,987674,2079265306,224\nimport-end=TimestampEnd64,1983,525330,2079851538,64\n",
        "import-start=TimestampStart64,1023,525330,1073218578,64\n",
        "aux-OR=2079982845,311,64\naux-diff=2079982909,375,64\naux-borrow=2079982973,439,65\n",
        "wire-map=window-one-imports-504-728-792-placeholder-zero-v1\n",
        "input-output-log-copies=1024,1024,10,10,0\npad=637,387,zero-polynomial\n",
        "bank=x*x-x,left-right-self\narithmetic=A-122880000*D;Delta-end+start-64;A-Q*Delta-R\n",
        "or=z0-Delta0;zi-Deltai-zprev+Deltai*zprev;z63-1\ncmp=b0;Ri-Deltai-bi-di+2*bnext;b64-1\n",
        "channels=c0,c1,c3;c2zero\nlinear-right=placeholder-except-bank-self\n",
        "product=-2-power-p-plus-q,Q-outer-Delta-inner\n",
        "family-terms=503,6487,254,2,321,2\nterm-count=7569\nbulk=5824\nsmall=1745\n",
    );
    for id in[Fixture::Main,Fixture::ZeroQ,Fixture::Spare]{let(x,_)=fixture(id);
        let p=AdmittedPacket::new(Descriptor::canonical(),Witness::from_dense(&x,1024).unwrap()).unwrap();
        assert_eq!(p.descriptor(),&Descriptor::canonical());assert_eq!(p.descriptor_bytes(),expected.as_bytes());
        assert!(!expected.contains("fixture=")&&!expected.contains("fixed-E")&&!expected.contains('\r'));
        let mut actual=Transcript::new(packet::DOMAIN);p.bind(&mut actual);
        let mut literal=Transcript::new(packet::DOMAIN);literal.append_bytes(b"ratio-packet-descriptor",expected.as_bytes());
        assert_eq!(actual.bytes_absorbed(),literal.bytes_absorbed());assert_eq!(actual.challenges(),0);
        assert_eq!(actual.challenge_scalar(b"binding-probe"),literal.challenge_scalar(b"binding-probe"));
    }
}
fn proof_differentials(){
    let circuit=reference();let shape=sparse::validate(&circuit,0).unwrap();
    for id in[Fixture::Main,Fixture::ZeroQ,Fixture::Spare]{
        let(x,k)=fixture(id);let p=AdmittedPacket::new(Descriptor::canonical(),Witness::from_dense(&x,1024).unwrap()).unwrap();
        let mut old_t=Transcript::new(packet::DOMAIN);
        let(expected,old_claim)=sparse::prove_with_binding(&circuit,&x,0,&mut old_t,|t|p.bind(t)).unwrap();
        let mut t=Transcript::new(packet::DOMAIN);let mut records=Vec::with_capacity(20);
        let(proof,claim)=p.prove(&mut t,|r|records.push(r.clone())).unwrap();
        assert_eq!(proof,expected);assert_eq!(claim,old_claim);assert_eq!(records.len(),20);
        assert_eq!((t.challenges(),t.raw_queries(),t.bytes_absorbed()),(old_t.challenges(),old_t.raw_queries(),old_t.bytes_absorbed()));
        assert_eq!(t.challenges(),31);let continuation=t.challenge_scalar(b"packet-continuation");
        assert_eq!(continuation,old_t.challenge_scalar(b"packet-continuation"));
        let bytes=gkr::encode_proof(&proof).unwrap();assert_eq!(bytes.len(),73*32);assert_eq!(bytes.len(),2336);
        assert_eq!(bytes,gkr::encode_proof(&expected).unwrap());assert_eq!(sparse::decode_proof(&circuit,0,&bytes).unwrap(),proof);
        assert_eq!(gkr::decode_dimensions(&[10],&bytes).unwrap(),proof);
        let mut verified=Transcript::new(packet::DOMAIN);assert_eq!(p.verify(&proof,&mut verified).unwrap(),claim);
        let mut old_verified=Transcript::new(packet::DOMAIN);
        assert_eq!(gkr::verify_with_wiring(&[10],1024,&expected,&mut old_verified,|t|p.bind(t),
            |_,r,u,v|sparse::wiring(&circuit,&shape,r,u,v)).unwrap(),claim);
        assert_eq!((verified.challenges(),verified.raw_queries(),verified.bytes_absorbed()),
            (old_verified.challenges(),old_verified.raw_queries(),old_verified.bytes_absorbed()));
        let(r,challenges,_,mut replayed)=replay(&p,&proof);assert_eq!(replayed.challenges(),31);
        assert_eq!(replayed.challenge_scalar(b"packet-continuation"),continuation);
        assert_eq!(mle(&x,&claim.point),claim.value);let(u,v)=challenges.split_at(10);
        assert_eq!(proof.layers[0].line_coefficients,independent_line(&x,u,v));
        let(a,b,aw)=p.first_counted(&r).unwrap();let(da,db)=dense_first(&circuit,&x,&r);compare(&a,&da);compare(&b,&db);
        let(c,d,cw)=p.second_counted(&r,u,proof.layers[0].left_value).unwrap();
        let(dc,dd)=dense_second(&circuit,&r,u,proof.layers[0].left_value);compare(&c,&dc);compare(&d,&dd);
        assert_eq!([aw[0].scratch_capacity,aw[1].scratch_capacity,cw[0].scratch_capacity,cw[1].scratch_capacity],[1833,3,630,1682]);
        for(work,limit)in aw.iter().chain(cw.iter()).zip([1833,3,630,1682]){assert!(work.updates<=limit);assert!(work.retained<=work.updates);}
        assert!(a.entries().len()<=855&&b.entries().len()<=1&&c.entries().len()<=503&&d.entries().len()<=504);
        assert!(a.entries().iter().all(|(i,_)|(1..856).contains(i)));assert!(b.entries().iter().all(|(i,_)|*i==0));
        assert!(c.entries().iter().all(|(i,_)|(1..504).contains(i)));assert!(d.entries().iter().all(|(i,_)|*i<504));
        let mut visits=0;let mut coefficient_visits=0;let mut queries=0;
        for phase in 0..2{let(mut aa,mut bb)=if phase==0{(da.clone(),db.clone())}else{(dc.clone(),dd.clone())};let mut xx=x.clone();
            let limits=if phase==0{[428,214,107,54,27,14,7,4,2,1]}else{[252,126,63,32,16,8,4,2,1,1]};
            for round in 0..10{let record:&RoundRecord=&records[phase*10+round];
                assert_eq!((record.phase,record.round,record.extent),(phase,round,xx.len()));
                assert_eq!(record.polynomial.to_vec(),gkr::quadratic_message(&aa,&bb,&xx));assert_eq!(record.challenge,challenges[phase*10+round]);
                assert_eq!(record.support,[aa.iter().filter(|v|!v.is_zero()).count(),bb.iter().filter(|v|!v.is_zero()).count(),xx.iter().filter(|v|!v.is_zero()).count()]);
                assert_eq!(record.work.value_queries,6*record.work.pair_count);assert!(record.work.pair_count<=limits[round]);
                assert!(record.work.pair_capacity<=if phase==0{856}else{1007});
                visits+=record.support[2];coefficient_visits+=record.support[0]+record.support[1];queries+=record.work.value_queries;
                gkr::fold(&mut aa,record.challenge);gkr::fold(&mut bb,record.challenge);gkr::fold(&mut xx,record.challenge);
            }
        }
        assert!(visits<=20*k&&coefficient_visits<=3737&&queries<=8178);
        let(line,lw)=p.witness().line_counted(u,v).unwrap();assert_eq!(line,proof.layers[0].line_coefficients);
        assert_eq!((lw.entry_visits,lw.coefficient_updates,lw.output_scalars,lw.scratch_scalars),(k,65*k,11,11));
        assert_eq!(std::mem::size_of::<Fr>(),32);assert_eq!(std::mem::size_of::<(usize,Fr)>(),40);
        assert_eq!((1836*40,856*40,2312*40,1007*40),(73440,34240,92480,40280));
        assert_eq!(p.witness().retained_capacity(),k);assert!(k*40<=40960);
    }
}

fn phase_and_factor_controls(){
    let(x,_)=fixture(Fixture::Main);let p=AdmittedPacket::new(Descriptor::canonical(),Witness::from_dense(&x,1024).unwrap()).unwrap();
    let circuit=reference();let shape=sparse::validate(&circuit,0).unwrap();let(u,v)=(vec![f(2);10],vec![f(3);10]);
    let left=mle(&x,&u);assert_eq!(left,f(604));
    let mut points=vec![vec![f(2);10],vec![f(3);10]];
    for row in[0,502,503,504,505,506,569,570,571,635,636,637,1023]{points.push((0..10).map(|b|f((row>>b&1)as u64)).collect());}
    for r in points{
        let(a,b)=p.first_coefficients(&r).unwrap();let(da,db)=dense_first(&circuit,&x,&r);compare(&a,&da);compare(&b,&db);
        let(c,d)=p.second_coefficients(&r,&u,left).unwrap();let(dc,dd)=dense_second(&circuit,&r,&u,left);compare(&c,&dc);compare(&d,&dd);
        assert_eq!(p.wiring(0,&r,&u,&v).unwrap(),sparse::wiring(&circuit,&shape,&r,&u,&v).unwrap());
        if weight(637,&r)==Fr::one()||weight(1023,&r)==Fr::one(){
            assert!(a.entries().is_empty()&&b.entries().is_empty()&&c.entries().is_empty()&&d.entries().is_empty());
            assert_eq!(p.wiring(0,&r,&u,&v).unwrap(),[Fr::zero();4]);
        }
        for phase in 0..2{let(mut aw,mut bw)=if phase==0{(a.clone(),b.clone())}else{(c.clone(),d.clone())};
            let(mut aa,mut bb)=if phase==0{(da.clone(),db.clone())}else{(dc.clone(),dd.clone())};
            let mut ww=p.witness().clone();let mut xx=x.clone();
            for _ in 0..10{
                assert_eq!(ratio::quadratic(&aw,&bw,&ww).unwrap().0.to_vec(),gkr::quadratic_message(&aa,&bb,&xx));
                aw=aw.fold(&[f(2)]).unwrap();bw=bw.fold(&[f(2)]).unwrap();ww=ww.fold(&[f(2)]).unwrap();
                gkr::fold(&mut aa,f(2));gkr::fold(&mut bb,f(2));gkr::fold(&mut xx,f(2));
            }
        }
    }
    let r=vec![f(2);10];let(c,d)=p.second_coefficients(&r,&u,left).unwrap();
    // Both rails have actual nonzero addends which disappear at t=1/3.
    assert_eq!((c.value(2).unwrap(),c.value(3).unwrap()),(f(2416),-f(4832)));
    assert_eq!((d.value(2).unwrap(),d.value(3).unwrap()),(-f(2416),f(4832)));
    let z=f(3).inverse().unwrap();let cf=c.fold(&[z]).unwrap();let df=d.fold(&[z]).unwrap();
    assert_eq!((cf.value(1).unwrap(),df.value(1).unwrap()),(Fr::zero(),Fr::zero()));
    assert!(!cf.entries().iter().any(|(i,_)|*i==1)&&!df.entries().iter().any(|(i,_)|*i==1));
    let(mut dc,mut dd)=dense_second(&circuit,&r,&u,left);gkr::fold(&mut dc,z);gkr::fold(&mut dd,z);compare(&cf,&dc);compare(&df,&dd);
    let wf=p.witness().fold(&[z]).unwrap();let mut xx=x.clone();gkr::fold(&mut xx,z);
    assert_eq!(ratio::quadratic(&cf,&df,&wf).unwrap().0.to_vec(),gkr::quadratic_message(&dc,&dd,&xx));
    // Only c1's right coordinate moves; c3 remains the unchanged diagonal.
    let wrong=c1_right_mutant(&circuit);
    assert_eq!(dense_first(&wrong,&x,&r),dense_first(&circuit,&x,&r));
    let(correct_c,correct_d)=dense_second(&circuit,&r,&u,left);let(wrong_c,wrong_d)=dense_second(&wrong,&r,&u,left);
    assert_eq!(wrong_c,correct_c);assert_ne!(wrong_d,correct_d);
    // Indices2 and0 share the first bit; compare actual messages through all LSB folds.
    assert_eq!(gkr::quadratic_message(&wrong_c,&wrong_d,&x),gkr::quadratic_message(&correct_c,&correct_d,&x));
    let(mut next_c,mut next_d,mut wrong_next_c,mut wrong_next_d,mut next_x)=
        (correct_c.clone(),correct_d.clone(),wrong_c.clone(),wrong_d.clone(),x.clone());
    let mut changed_message=false;
    for _ in 0..10{
        changed_message|=gkr::quadratic_message(&wrong_next_c,&wrong_next_d,&next_x)!=gkr::quadratic_message(&next_c,&next_d,&next_x);
        gkr::fold(&mut next_c,f(2));gkr::fold(&mut next_d,f(2));
        gkr::fold(&mut wrong_next_c,f(2));gkr::fold(&mut wrong_next_d,f(2));gkr::fold(&mut next_x,f(2));
    }assert!(changed_message);
    let correct_wiring=p.wiring(0,&r,&u,&v).unwrap();let wrong_wiring=sparse::wiring(&wrong,&shape,&r,&u,&v).unwrap();
    assert_eq!(wrong_wiring[0],correct_wiring[0]);assert_eq!(wrong_wiring[2],correct_wiring[2]);assert_eq!(wrong_wiring[3],correct_wiring[3]);
    assert_eq!(wrong_wiring[1]-correct_wiring[1],-f(10240));
    assert_eq!((wrong_wiring[1]-correct_wiring[1])*left,-f(6184960));drop(wrong);
    let(a,b)=p.first_coefficients(&r).unwrap();let(c,d)=p.second_coefficients(&r,&u,left).unwrap();
    // Remove only bank d indices1..503, retaining the ordinary placeholder contribution.
    let placeholder=d.value(0).unwrap();assert!(!placeholder.is_zero());
    let only_placeholder=Witness::new(1024,1,vec![(0,placeholder)]).unwrap();
    assert!(d.entries().iter().filter(|(i,_)|*i!=0).count()>1);
    assert_eq!(only_placeholder.value(0).unwrap(),d.value(0).unwrap());
    assert_ne!(ratio::quadratic(&c,&only_placeholder,p.witness()).unwrap().0,ratio::quadratic(&c,&d,p.witness()).unwrap().0);
    // Omit each whole contracted c factor separately, retaining every bank/OR c and every d.
    let rho=weight(505,&r);let qw=(0..91).map(|bit|pow(bit)*weight(156+bit,&u)).sum::<Fr>();
    assert_eq!(rho,-f(128));
    let expected_qw=BigUint::parse_bytes(b"114652423099798554354414575248",10).unwrap();
    assert_eq!(qw,Fr::from_le_bytes_mod_order(&expected_qw.to_bytes_le()));assert_eq!(left,f(604));
    let correct_scale=-rho*qw*left;let correct_message=ratio::quadratic(&c,&d,p.witness()).unwrap().0;
    let correct_dense:Vec<_>=(0..1024).map(|i|c.value(i).unwrap()).collect();
    for omitted_scale in[-qw*left,-rho*left,-rho*qw]{
        let delta_scale=omitted_scale-correct_scale;assert!(!delta_scale.is_zero());
        // One1024-Fr setup/reference vector; no product-term expansion or production array.
        let mut changed_c=correct_dense.clone();
        for bit in 0..64{changed_c[92+bit]+=delta_scale*pow(bit);}
        for i in(0..92).chain(156..1024){assert_eq!(changed_c[i],correct_dense[i]);}
        let changed=Witness::from_dense(&changed_c,503).unwrap();
        let message=ratio::quadratic(&changed,&d,p.witness()).unwrap().0;
        assert_eq!(message[0]-correct_message[0],f(65)*delta_scale);assert_ne!(message,correct_message);
        assert!(changed.entries().len()<=503);assert_eq!(d.value(0).unwrap(),placeholder);
    }
    assert_eq!(ratio::quadratic(&c,&d,&p.witness().fold(&u).unwrap()).err(),Some(GkrError::PointDimension));
    assert_eq!(ratio::quadratic(&a,&b,&p.witness().fold(&[f(2)]).unwrap()).err(),Some(GkrError::PointDimension));
    // Keeping an unused input preserves all637 rows while changing full-X messages/line/claim.
    let mut spare=x.clone();spare[900]+=Fr::one();assert!(residuals(&spare).iter().all(Zero::is_zero));
    let extra=AdmittedPacket::new(Descriptor::canonical(),Witness::from_dense(&spare,1024).unwrap()).unwrap();
    assert_eq!(extra.descriptor_bytes(),p.descriptor_bytes());assert_eq!(mle(&spare,&u)-left,f(16));
    assert_eq!(mle(&spare,&v)-mle(&x,&v),f(5184));
    let delta:Vec<_>=extra.witness().line(&u,&v).unwrap().iter().zip(p.witness().line(&u,&v).unwrap()).map(|(a,b)|*a-b).collect();
    assert_eq!(delta,[16,128,456,952,1289,1182,743,316,87,14,1].map(f));
    let mut delta_x=vec![Fr::zero();1024];delta_x[900]=Fr::one();assert_eq!(delta,independent_line(&delta_x,&u,&v));
    let full=extra.witness().fold(&[f(2)]).unwrap();assert_ne!(full,p.witness().fold(&[f(2)]).unwrap());
    let(mut aa,mut bb)=p.first_coefficients(&r).unwrap();let mut old_x=p.witness().clone();let mut changed_x=extra.witness().clone();
    let mut detected=false;
    for _ in 0..10{detected|=ratio::quadratic(&aa,&bb,&old_x).unwrap().0!=ratio::quadratic(&aa,&bb,&changed_x).unwrap().0;
        aa=aa.fold(&[f(2)]).unwrap();bb=bb.fold(&[f(2)]).unwrap();
        old_x=old_x.fold(&[f(2)]).unwrap();changed_x=changed_x.fold(&[f(2)]).unwrap();}
    assert!(detected,"unused-X change reaches an actual sumcheck message after shared-index folds");
    let mut reversed=x.clone();for b in (0..10).rev(){
        let mut next=vec![Fr::zero();reversed.len()/2];
        // Symmetric-coordinate consistency only; it cannot distinguish bit order.
        for i in 0..next.len(){next[i]=(Fr::one()-u[b])*reversed[i]+u[b]*reversed[i+next.len()];}reversed=next;
    }
    let asymmetric:Vec<_>=(0..10).map(|b|f(b as u64+2)).collect();
    let mut bit_reversed=asymmetric.clone();bit_reversed.reverse();assert_ne!(mle(&x,&asymmetric),mle(&x,&bit_reversed));
    assert_eq!(reversed[0],mle(&x,&u));
    let mut swapped=circuit.clone();for term in &mut swapped.terms{if term.row==503{term.row=504;}else if term.row==504{term.row=503;}}
    assert_ne!(sparse::wiring(&swapped,&shape,&asymmetric,&u,&v).unwrap(),p.wiring(0,&asymmetric,&u,&v).unwrap());drop(swapped);
    let mut pad=circuit.clone();pad.terms.push(term(637,0,0,[Fr::one(),Fr::zero(),Fr::zero(),Fr::zero()]));
    assert_eq!(pad.terms.capacity(),15138);assert!(pad.terms.capacity()+circuit.terms.capacity()<=3*7569);
    assert_ne!(sparse::wiring(&pad,&shape,&r,&u,&v).unwrap(),p.wiring(0,&r,&u,&v).unwrap());drop(pad);
    let mut dropped=circuit.clone();dropped.terms.retain(|t|t.row<503);
    assert_ne!(sparse::wiring(&dropped,&shape,&r,&u,&v).unwrap(),p.wiring(0,&r,&u,&v).unwrap());drop(dropped);
    for family in[0,1,2]{let mut mutant=circuit.clone();
        let index=if family==0{mutant.terms.iter().position(|t|t.row==507&&!t.gate.c3.is_zero()).unwrap()}
            else if family==1{mutant.terms.iter().position(|t|t.row==505&&!t.gate.c3.is_zero()).unwrap()}
            else{mutant.terms.iter().position(|t|t.row==572&&t.gate.left==439).unwrap()};
        if family==2{mutant.terms[index].gate.c1=-mutant.terms[index].gate.c1;}
        else{mutant.terms[index].gate.c3=Fr::zero();}
        assert_ne!(dense_first(&mutant,&x,&r),dense_first(&circuit,&x,&r));
        assert_ne!(dense_second(&mutant,&r,&u,left),dense_second(&circuit,&r,&u,left));
        assert_ne!(sparse::wiring(&mutant,&shape,&r,&u,&v).unwrap(),p.wiring(0,&r,&u,&v).unwrap());
    }
    assert_eq!(p.first_coefficients(&[f(2);9]).err(),Some(GkrError::PointDimension));
    assert_eq!(p.second_coefficients(&[f(2);9],&u,left).err(),Some(GkrError::PointDimension));
    assert_eq!(p.second_coefficients(&r,&[f(2);9],left).err(),Some(GkrError::PointDimension));
    for(i,rr,uu,vv)in[(1,r.clone(),u.clone(),v.clone()),(0,vec![f(2);9],u.clone(),v.clone()),
        (0,r.clone(),vec![f(2);9],v.clone()),(0,r,u,vec![f(3);9])]{assert_eq!(p.wiring(i,&rr,&uu,&vv),Err(GkrError::PointDimension));}
}

fn consumer_controls(){
    let(x,_)=fixture(Fixture::Main);let p=AdmittedPacket::new(Descriptor::canonical(),Witness::from_dense(&x,1024).unwrap()).unwrap();
    let mut t=Transcript::new(packet::DOMAIN);let(proof,_)=p.prove(&mut t,|_|{}).unwrap();
    for fault in 0..12{let mut changed=proof.clone();let expected=match fault{
        0=>{changed.layers.clear();GkrError::ProofLayerCount},1=>{changed.layers[0].rounds.pop();GkrError::SumcheckRoundCount},
        2=>{changed.layers[0].rounds[0].push(Fr::zero());GkrError::SumcheckDegree},
        3=>{changed.layers[0].line_coefficients.pop();GkrError::LineDegree},
        4=>{changed.layers[0].left_value+=Fr::one();GkrError::TerminalExpression},
        5=>{changed.layers[0].right_value+=Fr::one();GkrError::TerminalExpression},
        6=>{changed.layers[0].line_coefficients[0]+=Fr::one();GkrError::LineEndpoints},
        7=>{changed.layers[0].line_coefficients[1]+=Fr::one();GkrError::LineEndpoints},
        8=>{changed.layers.push(changed.layers[0].clone());GkrError::ProofLayerCount},
        9=>{changed.layers[0].rounds.push(vec![Fr::zero();3]);GkrError::SumcheckRoundCount},
        10=>{changed.layers[0].rounds[0].pop();GkrError::SumcheckDegree},
        _=>{changed.layers[0].line_coefficients.push(Fr::zero());GkrError::LineDegree},
    };assert_eq!(p.verify(&changed,&mut Transcript::new(packet::DOMAIN)),Err(expected),"consumer fault{fault}");}
    let mut initial=proof.clone();initial.layers[0].rounds[0][0]+=Fr::one();
    assert_eq!(p.verify(&initial,&mut Transcript::new(packet::DOMAIN)),Err(GkrError::SumcheckIdentity));
    let mut round=proof.clone();round.layers[0].rounds[0][1]-=Fr::one();round.layers[0].rounds[0][2]+=Fr::one();
    assert_eq!(round.layers[0].rounds[0][0],proof.layers[0].rounds[0][0]);
    assert_eq!(gkr::eval_polynomial(&round.layers[0].rounds[0],Fr::one()),gkr::eval_polynomial(&proof.layers[0].rounds[0],Fr::one()));
    let mut rt=Transcript::new(packet::DOMAIN);p.bind(&mut rt);gkr::output_point(1024,&mut rt);gkr::append_usize(&mut rt,b"gkr-layer-index",0);
    gkr::append_polynomial(&mut rt,b"gkr-sumcheck-polynomial",&round.layers[0].rounds[0]);
    let z=rt.challenge_scalar(b"gkr-sumcheck-challenge");
    assert_ne!(gkr::eval_polynomial(&round.layers[0].rounds[0],z),round.layers[0].rounds[1][0]+gkr::eval_polynomial(&round.layers[0].rounds[1],Fr::one()));
    assert_eq!(p.verify(&round,&mut Transcript::new(packet::DOMAIN)),Err(GkrError::SumcheckIdentity));
    // Endpoint preservation is insufficient without the still-open committed-input join.
    let mut line=proof.clone();line.layers[0].line_coefficients[1]-=Fr::one();line.layers[0].line_coefficients[2]+=Fr::one();
    assert_eq!(line.layers[0].line_coefficients[0],proof.layers[0].left_value);
    assert_eq!(gkr::eval_polynomial(&line.layers[0].line_coefficients,Fr::one()),proof.layers[0].right_value);
    let changed=p.verify(&line,&mut Transcript::new(packet::DOMAIN)).unwrap();let(_,challenges,lambda,_)=replay(&p,&line);
    assert!(lambda!=Fr::zero()&&lambda!=Fr::one());assert_eq!(changed.point,gkr::line_point(&challenges[..10],&challenges[10..],lambda));
    assert_eq!(changed.value-mle(&x,&changed.point),lambda*(lambda-Fr::one()));assert!(!(changed.value-mle(&x,&changed.point)).is_zero());
    for fault in 0..3{let mut wrong=Transcript::new(packet::DOMAIN);
        let result=gkr::verify_with_wiring(&[10],1024,&proof,&mut wrong,|t|{
            if fault==0{t.append_bytes(b"ratio-packet-descriptor-wrong",&p.descriptor_bytes());}
            else if fault==1{t.append_scalar(b"unbound-host-A",&word(&x,1,91));p.bind(t);}
            else{p.bind(t);gkr::output_point(1024,t);}
        },|i,r,u,v|p.wiring(i,r,u,v));assert!(result.is_err(),"binding/order fault{fault}");
    }
    let circuit=reference();let shape=sparse::validate(&circuit,0).unwrap();
    for fault in 0..3{let mut mutant=if fault==0{c1_right_mutant(&circuit)}else{circuit.clone()};match fault{
        0=>{},1=>mutant.terms[594].gate.c1=-f(122879999),
        _=>mutant.terms[1300].gate.c3=-mutant.terms[1300].gate.c3,
    }
        assert_eq!(gkr::verify_with_wiring(&[10],1024,&proof,&mut Transcript::new(packet::DOMAIN),|t|p.bind(t),
            |_,r,u,v|sparse::wiring(&mutant,&shape,r,u,v)),Err(GkrError::TerminalExpression));
    }
    let bytes=gkr::encode_proof(&proof).unwrap();assert!(sparse::decode_proof(&circuit,0,&bytes[..bytes.len()-1]).is_err());
    let mut extra=bytes.clone();extra.push(0);assert!(sparse::decode_proof(&circuit,0,&extra).is_err());
    let mut invalid=bytes.clone();invalid[..32].fill(255);assert!(sparse::decode_proof(&circuit,0,&invalid).is_err());
    assert!(gkr::decode_dimensions(&[9],&bytes).is_err());assert!(gkr::decode_dimensions(&[11],&bytes).is_err());
}

#[test]
fn whole_packet_matches_bounded_sparse_proof(){
    source_tuple_controls();admission_controls();residual_controls();binding_controls();
    proof_differentials();phase_and_factor_controls();consumer_controls();
}

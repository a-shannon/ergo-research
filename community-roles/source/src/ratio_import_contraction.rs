//! Three source-derived field rows over one complete X. No native or PCS claim.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use crate::{gkr::{self, GkrError, GkrProof, InputClaim, LayerProof},
    implicit_witness::Witness, ratio_contraction::{eq, quadratic, RoundRecord},
    sparse, transcript::Transcript};

pub(crate) const N: usize = 1024;
pub(crate) const ROWS: usize = 4;
pub(crate) const TE: u64 = 122880000;
pub(crate) const DOMAIN: &[u8] = b"ratio-import-contraction-local-test-v1";
const SOURCE_SHA: &str = "AFEA8F2B7B54302FB75C7613ACA87E05AA02FAE842AF92DB38CB2B66DC0F23D9";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Role { Numerator91, Delta64, Quotient91, Remainder64, Difficulty224,
    TimestampEnd64, TimestampStart64 }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Order { SourceRowsQuotientOuter, DenominatorOuter, ConstantFirst }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Padding { ZeroPolynomial, ExternalOutput }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Rail {
    pub role: Role, pub owner: usize, pub source_local: usize,
    pub raw_base: usize, pub local: usize, pub width: usize,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Descriptor {
    pub source_sha: &'static str, pub n: usize, pub h: usize, pub e: usize,
    pub owner: usize, pub tier: usize, pub ratio: usize, pub width: usize,
    pub row_stride: usize, pub owner_base: usize, pub raw_rows: [usize;3],
    pub window_base: usize, pub window_width: usize, pub local_window: usize,
    pub raw_placeholder: usize, pub placeholder: usize, pub rails: [Rail;7],
    pub input_len: usize, pub input_log: usize, pub row_count: usize, pub row_log: usize,
    pub log_copies: usize, pub local_rows: [usize;3], pub row_terms: [usize;3],
    pub product_count: usize, pub term_count: usize, pub te: u64, pub offset: u64,
    pub product_sign: i8, pub order: Order, pub padding: Padding,
}
impl Descriptor {
    pub fn canonical() -> Self { Self {
        source_sha:SOURCE_SHA,n:2048,h:11,e:64,owner:1983,tier:1,ratio:0,
        width:1048576,row_stride:16384,owner_base:2079326208,
        raw_rows:[32497822,32497823,32497824],window_base:2079982535,
        window_width:503,local_window:1,raw_placeholder:2079326208,placeholder:0,
        rails:[
            Rail{role:Role::Numerator91,owner:1983,source_local:656327,raw_base:2079982535,local:1,width:91},
            Rail{role:Role::Delta64,owner:1983,source_local:656418,raw_base:2079982626,local:92,width:64},
            Rail{role:Role::Quotient91,owner:1983,source_local:656482,raw_base:2079982690,local:156,width:91},
            Rail{role:Role::Remainder64,owner:1983,source_local:656573,raw_base:2079982781,local:247,width:64},
            Rail{role:Role::Difficulty224,owner:1982,source_local:987674,raw_base:2079265306,local:504,width:224},
            Rail{role:Role::TimestampEnd64,owner:1983,source_local:525330,raw_base:2079851538,local:728,width:64},
            Rail{role:Role::TimestampStart64,owner:1023,source_local:525330,raw_base:1073218578,local:792,width:64},
        ],input_len:1024,input_log:10,row_count:4,row_log:2,log_copies:0,
        local_rows:[0,1,2],row_terms:[315,193,5979],product_count:5824,term_count:6487,
        te:122880000,offset:64,product_sign:-1,order:Order::SourceRowsQuotientOuter,
        padding:Padding::ZeroPolynomial,
    } }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum AdmissionError {
    Descriptor(&'static str), Protocol(GkrError), Witness(String), Residual(usize),
}
pub(crate) struct AdmittedJoin {
    descriptor: Descriptor, witness: Witness, shape: sparse::Shape, delta: Fr,
}
fn add(a:usize,b:usize)->Result<usize,AdmissionError>{
    a.checked_add(b).ok_or(AdmissionError::Descriptor("overflow"))
}
fn mul(a:usize,b:usize)->Result<usize,AdmissionError>{
    a.checked_mul(b).ok_or(AdmissionError::Descriptor("overflow"))
}
fn admit_descriptor(d:&Descriptor)->Result<sparse::Shape,AdmissionError>{
    // The unchanged empty call admits geometry only, not the absent term loop.
    let empty=sparse::Circuit{input_len:d.input_len,row_count:d.row_count,terms:Vec::new()};
    let shape=sparse::validate(&empty,d.log_copies).map_err(AdmissionError::Protocol)?;
    let products=mul(d.rails[2].width,d.rails[1].width)?;
    let first=add(d.rails[0].width,d.rails[4].width)?;
    let second=add(add(add(d.rails[1].width,d.rails[5].width)?,d.rails[6].width)?,1)?;
    let third=add(add(d.rails[0].width,products)?,d.rails[3].width)?;
    let count=add(add(first,second)?,third)?;
    if count>1usize<<20{return Err(AdmissionError::Descriptor("term cap"));}
    if shape.input_bits!=10||shape.row_bits!=2||shape.copies!=1
        ||shape.input_len!=N||shape.row_count!=ROWS||d.input_log!=10||d.row_log!=2||d.log_copies!=0{
        return Err(AdmissionError::Descriptor("fixed dimensions"));
    }
    let base=mul(d.owner,d.width)?;
    let row=add(mul(d.owner,d.row_stride)?,8350)?;
    let window_end=add(d.window_base,d.window_width)?;
    let local_end=add(d.local_window,d.window_width)?;
    if base!=d.owner_base||d.raw_placeholder!=base||d.placeholder!=0||d.local_window!=1
        ||d.window_base!=add(base,656327)?||window_end!=add(base,656830)?||local_end!=504
        ||d.raw_rows!=[row,add(row,1)?,add(row,2)?]{
        return Err(AdmissionError::Descriptor("mapping intervals"));
    }
    for rail in &d.rails {
        let raw=add(mul(rail.owner,d.width)?,rail.source_local)?;
        let raw_end=add(rail.raw_base,rail.width)?;
        let end=add(rail.local,rail.width)?;
        if raw!=rail.raw_base||end>N||rail.local==0||rail.width==0
            ||raw_end>add(mul(rail.owner,d.width)?,d.width)?{
            return Err(AdmissionError::Descriptor("mapping intervals"));
        }
    }
    let mut previous=d.local_window;
    for rail in &d.rails[..4] {
        if rail.owner!=d.owner||rail.local!=previous
            ||rail.raw_base!=add(d.window_base,rail.local-d.local_window)?{
            return Err(AdmissionError::Descriptor("mapping intervals"));
        }
        previous=add(rail.local,rail.width)?;
    }
    if previous>local_end{return Err(AdmissionError::Descriptor("mapping intervals"));}
    previous=local_end;
    for rail in &d.rails[4..] {
        if rail.local!=previous{return Err(AdmissionError::Descriptor("mapping intervals"));}
        // Every imported raw interval is disjoint from the whole mapped window
        // and from the placeholder; canonical roles also fix their mutual order.
        let end=add(rail.raw_base,rail.width)?;
        if (rail.raw_base<window_end&&d.window_base<end)
            ||(rail.raw_base<=d.raw_placeholder&&d.raw_placeholder<end){
            return Err(AdmissionError::Descriptor("mapping intervals"));
        }
        previous=add(rail.local,rail.width)?;
    }
    for i in 4..7{for j in i+1..7{
        let a=&d.rails[i];let b=&d.rails[j];
        if a.raw_base<add(b.raw_base,b.width)?&&b.raw_base<add(a.raw_base,a.width)?{
            return Err(AdmissionError::Descriptor("mapping intervals"));
        }
    }}
    if products!=5824||count!=6487||d.product_count!=products||d.term_count!=count
        ||d.row_terms!=[first,second,third]{return Err(AdmissionError::Descriptor("term count"));}
    if *d!=Descriptor::canonical(){return Err(AdmissionError::Descriptor("canonical descriptor"));}
    Ok(shape)
}
fn rail_value(w:&Witness,start:usize,width:usize)->Result<Fr,AdmissionError>{
    let mut value=Fr::zero();let mut power=Fr::one();
    for bit in 0..width{value+=power*w.value(start+bit).map_err(AdmissionError::Witness)?;power+=power;}
    Ok(value)
}
fn weight(point:&[Fr],start:usize,width:usize)->Fr{
    let mut value=Fr::zero();let mut power=Fr::one();
    for bit in 0..width{value+=power*eq(point,start+bit);power+=power;}value
}
fn constant(value:Fr)->Result<Witness,GkrError>{
    let entries=if value.is_zero(){Vec::new()}else{vec![(0,value)]};
    Witness::new(N,1,entries).map_err(|_|GkrError::InvalidWireIndex)
}
fn rails(entries:&[(usize,usize,Fr)],capacity:usize)->Result<Witness,GkrError>{
    let mut out=Vec::with_capacity(capacity);
    for &(start,width,scale) in entries{
        let mut coefficient=scale;
        for bit in 0..width{if !coefficient.is_zero(){out.push((start+bit,coefficient));}coefficient+=coefficient;}
    }
    Witness::new(N,capacity,out).map_err(|_|GkrError::InvalidWireIndex)
}
fn row_weights(r:&[Fr])->Result<[Fr;3],GkrError>{
    if r.len()!=2{return Err(GkrError::PointDimension);}
    Ok([eq(r,0),eq(r,1),eq(r,2)])
}
fn linear(rho:[Fr;3],z:&[Fr])->Fr{
    (rho[0]+rho[2])*weight(z,1,91)-rho[0]*Fr::from(TE)*weight(z,504,224)
        +rho[1]*(weight(z,92,64)-weight(z,728,64)+weight(z,792,64))
        -rho[2]*weight(z,247,64)
}
fn phase(mut a:Witness,mut b:Witness,input:&Witness,claim:&mut Fr,rounds:&mut Vec<Vec<Fr>>,
    transcript:&mut Transcript,phase_index:usize,observe:&mut impl FnMut(&RoundRecord))
    ->Result<(Vec<Fr>,Fr),GkrError>{
    let mut x=input.clone();let mut point=Vec::with_capacity(input.dimensions());
    while x.extent()>1{
        let(polynomial,work)=quadratic(&a,&b,&x)?;
        if polynomial[0]+gkr::eval_polynomial(&polynomial,Fr::one())!=*claim{return Err(GkrError::SumcheckIdentity);}
        gkr::append_polynomial(transcript,b"gkr-sumcheck-polynomial",&polynomial);
        let challenge=transcript.challenge_scalar(b"gkr-sumcheck-challenge");
        *claim=gkr::eval_polynomial(&polynomial,challenge);
        observe(&RoundRecord{phase:phase_index,round:point.len(),extent:x.extent(),
            support:[a.entries().len(),b.entries().len(),x.entries().len()],polynomial,challenge,work});
        a=a.fold(&[challenge]).map_err(|_|GkrError::PointDimension)?;
        b=b.fold(&[challenge]).map_err(|_|GkrError::PointDimension)?;
        x=x.fold(&[challenge]).map_err(|_|GkrError::PointDimension)?;
        rounds.push(polynomial.to_vec());point.push(challenge);
    }
    Ok((point,x.value(0).map_err(|_|GkrError::InvalidWireIndex)?))
}
impl AdmittedJoin {
    pub fn new(descriptor:Descriptor,witness:Witness)->Result<Self,AdmissionError>{
        let shape=admit_descriptor(&descriptor)?;
        if witness.extent()!=shape.input_len||witness.dimensions()!=shape.input_bits{
            return Err(AdmissionError::Protocol(GkrError::InvalidInputWidth));
        }
        let mut values=[Fr::zero();7];
        for(value,rail)in values.iter_mut().zip(&descriptor.rails){
            *value=rail_value(&witness,rail.local,rail.width)?;
        }
        let residuals=[values[0]-Fr::from(TE)*values[4],
            values[1]-values[5]+values[6]-Fr::from(64u64),
            values[0]-values[2]*values[1]-values[3]];
        for(row,residual)in residuals.iter().enumerate(){
            if !residual.is_zero(){return Err(AdmissionError::Residual(row));}
        }
        Ok(Self{descriptor,witness,shape,delta:values[1]})
    }
    pub fn with_admitted<R>(descriptor:Descriptor,witness:Witness,
        consumer:impl FnOnce(&Self)->R)->Result<R,AdmissionError>{
        let join=Self::new(descriptor,witness)?;Ok(consumer(&join))
    }
    pub fn witness(&self)->&Witness{&self.witness}
    pub fn descriptor(&self)->&Descriptor{&self.descriptor}
    pub fn descriptor_bytes(&self)->Vec<u8>{concat!(
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
    ).as_bytes().to_vec()}
    pub fn bind(&self,transcript:&mut Transcript){
        transcript.append_bytes(b"ratio-import-descriptor",&self.descriptor_bytes());
    }
    pub fn first_coefficients(&self,r:&[Fr])->Result<(Witness,Witness),GkrError>{
        let rho=row_weights(r)?;
        let a=rails(&[(1,91,rho[0]+rho[2]),(92,64,rho[1]),(156,91,-rho[2]*self.delta),
            (247,64,-rho[2]),(504,224,-rho[0]*Fr::from(TE)),(728,64,-rho[1]),(792,64,rho[1])],662)?;
        Ok((a,constant(-Fr::from(64u64)*rho[1])?))
    }
    pub fn second_coefficients(&self,r:&[Fr],u:&[Fr],left_value:Fr)->Result<(Witness,Witness),GkrError>{
        let rho=row_weights(r)?;
        if u.len()!=self.shape.input_bits{return Err(GkrError::PointDimension);}
        let c=rails(&[(92,64,-rho[2]*weight(u,156,91)*left_value)],64)?;
        let d=constant(linear(rho,u)*left_value-Fr::from(64u64)*rho[1]*eq(u,0))?;
        Ok((c,d))
    }
    pub fn wiring(&self,index:usize,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],GkrError>{
        if index!=0||r.len()!=self.shape.row_bits||u.len()!=self.shape.input_bits||v.len()!=self.shape.input_bits{
            return Err(GkrError::PointDimension);
        }
        let rho=row_weights(r)?;
        Ok([-Fr::from(64u64)*rho[1]*eq(u,0)*eq(v,0),linear(rho,u)*eq(v,0),Fr::zero(),
            -rho[2]*weight(u,156,91)*weight(v,92,64)])
    }
    pub fn prove(&self,transcript:&mut Transcript,mut observe:impl FnMut(&RoundRecord))
        ->Result<(GkrProof,InputClaim),GkrError>{
        self.bind(transcript);let output=gkr::output_point(self.shape.row_count,transcript);
        gkr::append_usize(transcript,b"gkr-layer-index",0);
        let mut claim=Fr::zero();let mut rounds=Vec::with_capacity(20);
        let(a,b)=self.first_coefficients(&output)?;
        let(u,left_value)=phase(a,b,&self.witness,&mut claim,&mut rounds,transcript,0,&mut observe)?;
        let(c,d)=self.second_coefficients(&output,&u,left_value)?;
        let(v,right_value)=phase(c,d,&self.witness,&mut claim,&mut rounds,transcript,1,&mut observe)?;
        let coefficients=self.wiring(0,&output,&u,&v)?;
        if coefficients[0]+coefficients[1]*left_value+coefficients[3]*left_value*right_value!=claim{
            return Err(GkrError::TerminalExpression);
        }
        let line=self.witness.line(&u,&v).map_err(|_|GkrError::PointDimension)?;
        transcript.append_scalar(b"gkr-left-value",&left_value);transcript.append_scalar(b"gkr-right-value",&right_value);
        gkr::append_polynomial(transcript,b"gkr-line-polynomial",&line);
        let challenge=transcript.challenge_scalar(b"gkr-line-challenge");
        let point=gkr::line_point(&u,&v,challenge);let value=gkr::eval_polynomial(&line,challenge);
        Ok((GkrProof{layers:vec![LayerProof{rounds,left_value,right_value,line_coefficients:line}]},InputClaim{point,value}))
    }
    pub fn verify(&self,proof:&GkrProof,transcript:&mut Transcript)->Result<InputClaim,GkrError>{
        gkr::verify_with_wiring(&[self.shape.input_bits],self.shape.row_count,proof,transcript,
            |t|self.bind(t),|i,r,u,v|self.wiring(i,r,u,v))
    }
}

//! One admitted field-product family. No native authentication or PCS opening.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use crate::{gkr::{self, GkrError, GkrProof, InputClaim, LayerProof},
    implicit_witness::Witness, sparse, transcript::Transcript};

pub(crate) const N: usize = 512;
pub(crate) const Q_START: usize = 156;
pub(crate) const Q_WIDTH: usize = 91;
pub(crate) const D_START: usize = 92;
pub(crate) const D_WIDTH: usize = 64;
pub(crate) const DOMAIN: &[u8] = b"ratio-contraction-local-test-v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Fixture { Main, Zero, Nonboolean, AllOneRails, Full512 }
impl Fixture {
    pub fn id(self) -> &'static str { match self {
        Self::Main=>"main",Self::Zero=>"zero",Self::Nonboolean=>"nonboolean",
        Self::AllOneRails=>"all-one-rails",Self::Full512=>"full-512" } }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Role { Quotient91, Delta64, Placeholder }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Order { QuotientOuterConstantAfter, DenominatorOuter, ConstantBefore }
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Descriptor {
    pub fixture: Fixture, pub n: usize, pub h: usize, pub e: usize,
    pub owner: usize, pub tier: usize, pub ratio: usize,
    pub width: usize, pub row_stride: usize, pub owner_base: usize, pub raw_row: usize,
    pub window_base: usize, pub window_width: usize, pub raw_q: usize, pub raw_d: usize,
    pub raw_placeholder: usize, pub input_len: usize, pub input_log: usize,
    pub row_count: usize, pub row_log: usize, pub local_row: usize,
    pub local_window: usize, pub local_q: usize, pub q_width: usize,
    pub local_d: usize, pub d_width: usize, pub placeholder: usize,
    pub q_role: Role, pub d_role: Role, pub constant_role: Role,
    pub order: Order, pub sign: i8, pub log_copies: usize,
    pub product_count: usize, pub term_count: usize,
    pub imports: [(usize,usize,usize);3], pub offset: usize,
}
impl Descriptor {
    pub fn canonical(fixture: Fixture) -> Self { Self {
        fixture,n:2048,h:11,e:64,owner:1983,tier:1,ratio:0,width:1048576,row_stride:16384,
        owner_base:2079326208,raw_row:32497824,window_base:2079982535,window_width:503,
        raw_q:2079982690,raw_d:2079982626,raw_placeholder:2079326208,
        input_len:512,input_log:9,row_count:1,row_log:0,local_row:0,local_window:1,
        local_q:156,q_width:91,local_d:92,d_width:64,placeholder:0,
        q_role:Role::Quotient91,d_role:Role::Delta64,constant_role:Role::Placeholder,
        order:Order::QuotientOuterConstantAfter,sign:-1,log_copies:0,
        product_count:5824,term_count:5825,
        imports:[(1982,987674,224),(1983,525330,64),(1023,525330,64)],offset:64 } }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum AdmissionError { Descriptor(&'static str), Protocol(GkrError), Witness(String) }

pub(crate) struct AdmittedFamily {
    descriptor: Descriptor, fixed_e: Fr, witness: Witness, shape: sparse::Shape,
    q_value: Fr, d_value: Fr,
}

fn checked_add(a:usize,b:usize)->Result<usize,AdmissionError>{
    a.checked_add(b).ok_or(AdmissionError::Descriptor("overflow"))
}
fn checked_mul(a:usize,b:usize)->Result<usize,AdmissionError>{
    a.checked_mul(b).ok_or(AdmissionError::Descriptor("overflow"))
}
pub(crate) fn eq(point:&[Fr],index:usize)->Fr {
    point.iter().enumerate().fold(Fr::one(),|a,(bit,z)|
        a*if index>>bit&1==1{*z}else{Fr::one()-z})
}
fn rail_entries(start:usize,width:usize,scale:Fr)->Vec<(usize,Fr)> {
    let mut entries=Vec::with_capacity(width);let mut power=Fr::one();
    for bit in 0..width{let value=scale*power;if !value.is_zero(){entries.push((start+bit,value));}power+=power;}
    entries
}
fn coefficient(start:usize,width:usize,scale:Fr)->Result<Witness,GkrError>{
    Witness::new(N,width,rail_entries(start,width,scale)).map_err(|_|GkrError::InvalidWireIndex)
}
fn constant(value:Fr)->Result<Witness,GkrError>{
    let entries=if value.is_zero(){Vec::new()}else{vec![(0,value)]};
    Witness::new(N,1,entries).map_err(|_|GkrError::InvalidWireIndex)
}
fn weighted_rail(point:&[Fr],start:usize,width:usize)->Fr{
    let mut result=Fr::zero();let mut power=Fr::one();
    for bit in 0..width{result+=power*eq(point,start+bit);power+=power;}result
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MessageWork { pub pair_count:usize,pub pair_capacity:usize,pub value_queries:usize }
pub(crate) fn quadratic(a:&Witness,b:&Witness,x:&Witness)->Result<([Fr;3],MessageWork),GkrError>{
    if a.extent()!=b.extent()||a.extent()!=x.extent()||x.extent()<2{return Err(GkrError::PointDimension);}
    let aa=a.entries();let bb=b.entries();let mut pairs=Vec::with_capacity(aa.len()+bb.len());
    let(mut i,mut j)=(0,0);let mut previous=None;
    while i<aa.len()||j<bb.len(){
        let left=aa.get(i).map(|v|v.0>>1);let right=bb.get(j).map(|v|v.0>>1);
        let next=match(left,right){(Some(l),Some(r))=>l.min(r),(Some(l),None)=>l,(None,Some(r))=>r,(None,None)=>break};
        if previous!=Some(next){pairs.push(next);previous=Some(next);}
        while i<aa.len()&&aa[i].0>>1==next{i+=1;}
        while j<bb.len()&&bb[j].0>>1==next{j+=1;}
    }
    let mut polynomial=[Fr::zero();3];
    for pair in &pairs{
        let low=2*pair;let high=low+1;
        let a0=a.value(low).map_err(|_|GkrError::InvalidWireIndex)?;
        let a1=a.value(high).map_err(|_|GkrError::InvalidWireIndex)?;
        let b0=b.value(low).map_err(|_|GkrError::InvalidWireIndex)?;
        let b1=b.value(high).map_err(|_|GkrError::InvalidWireIndex)?;
        let x0=x.value(low).map_err(|_|GkrError::InvalidWireIndex)?;
        let x1=x.value(high).map_err(|_|GkrError::InvalidWireIndex)?;
        let da=a1-a0;let db=b1-b0;let dx=x1-x0;
        polynomial[0]+=a0*x0+b0;polynomial[1]+=a0*dx+da*x0+db;polynomial[2]+=da*dx;
    }
    let work=MessageWork{pair_count:pairs.len(),pair_capacity:pairs.capacity(),value_queries:6*pairs.len()};
    Ok((polynomial,work))
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RoundRecord {
    pub phase:usize,pub round:usize,pub extent:usize,pub support:[usize;3],
    pub polynomial:[Fr;3],pub challenge:Fr,pub work:MessageWork,
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

impl AdmittedFamily {
    pub fn new(descriptor:Descriptor,fixed_e:Fr,witness:Witness)->Result<Self,AdmissionError>{
        // This unchanged actual call admits geometry only; its term loop is empty.
        let empty=sparse::Circuit{input_len:descriptor.input_len,row_count:descriptor.row_count,terms:Vec::new()};
        let shape=sparse::validate(&empty,descriptor.log_copies).map_err(AdmissionError::Protocol)?;
        let base=checked_mul(descriptor.owner,descriptor.width)?;
        let row=checked_add(checked_mul(descriptor.owner,descriptor.row_stride)?,8352)?;
        let end=checked_add(descriptor.window_base,descriptor.window_width)?;
        let local_end=checked_add(descriptor.local_window,descriptor.window_width)?;
        let q_end=checked_add(descriptor.local_q,descriptor.q_width)?;
        let d_end=checked_add(descriptor.local_d,descriptor.d_width)?;
        let products=checked_mul(descriptor.q_width,descriptor.d_width)?;
        let count=checked_add(products,1)?;
        if count>1usize<<20{return Err(AdmissionError::Descriptor("term cap"));}
        if shape.input_bits!=9||shape.row_bits!=0||shape.copies!=1||shape.input_len!=512||shape.row_count!=1
            ||descriptor.input_log!=9||descriptor.row_log!=0||descriptor.log_copies!=0{
            return Err(AdmissionError::Descriptor("fixed dimensions"));}
        if base!=descriptor.owner_base||row!=descriptor.raw_row
            ||descriptor.raw_placeholder!=base||descriptor.window_base!=checked_add(base,656327)?
            ||end!=checked_add(base,656830)?||local_end!=504||local_end>descriptor.input_len
            ||descriptor.placeholder>=descriptor.local_window||descriptor.raw_q!=checked_add(descriptor.window_base,155)?
            ||descriptor.raw_d!=checked_add(descriptor.window_base,91)?||q_end!=247||d_end!=descriptor.local_q{
            return Err(AdmissionError::Descriptor("mapping intervals"));}
        if products!=5824||count!=5825||descriptor.product_count!=products||descriptor.term_count!=count{
            return Err(AdmissionError::Descriptor("term count"));}
        if descriptor!=Descriptor::canonical(descriptor.fixture){return Err(AdmissionError::Descriptor("canonical descriptor"));}
        if witness.extent()!=shape.input_len||witness.dimensions()!=shape.input_bits{
            return Err(AdmissionError::Protocol(GkrError::InvalidInputWidth));}
        let mut q_value=Fr::zero();let mut d_value=Fr::zero();
        for(start,width,result)in[(Q_START,Q_WIDTH,&mut q_value),(D_START,D_WIDTH,&mut d_value)]{
            let mut power=Fr::one();for bit in 0..width{
                *result+=power*witness.value(start+bit).map_err(AdmissionError::Witness)?;power+=power;}
        }
        if fixed_e-q_value*d_value!=Fr::zero(){return Err(AdmissionError::Protocol(GkrError::NonzeroOutput));}
        Ok(Self{descriptor,fixed_e,witness,shape,q_value,d_value})
    }
    pub fn with_admitted<R>(descriptor:Descriptor,fixed_e:Fr,witness:Witness,
        consumer:impl FnOnce(&Self)->R)->Result<R,AdmissionError>{
        let family=Self::new(descriptor,fixed_e,witness)?;Ok(consumer(&family))
    }
    pub fn witness(&self)->&Witness{&self.witness}
    pub fn values(&self)->(Fr,Fr){(self.q_value,self.d_value)}
    pub fn descriptor_bytes(&self)->Vec<u8>{
        let text=format!(concat!(
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
            "constant-channel=c0\nconstant-order=after-products\nterm-count=5825\nfixture={}\nE-encoding=existing-canonical-Fr-scalar-event\n"),self.descriptor.fixture.id());
        text.into_bytes()
    }
    pub fn bind(&self,transcript:&mut Transcript){
        transcript.append_bytes(b"ratio-family-descriptor",&self.descriptor_bytes());
        transcript.append_scalar(b"ratio-fixed-E",&self.fixed_e);
    }
    pub fn first_coefficients(&self)->Result<(Witness,Witness),GkrError>{
        Ok((coefficient(Q_START,Q_WIDTH,-self.d_value)?,constant(self.fixed_e)?))
    }
    pub fn second_coefficients(&self,u:&[Fr],left_value:Fr)->Result<(Witness,Witness),GkrError>{
        if u.len()!=self.shape.input_bits{return Err(GkrError::PointDimension);}
        Ok((coefficient(D_START,D_WIDTH,-weighted_rail(u,Q_START,Q_WIDTH)*left_value)?,
            constant(self.fixed_e*eq(u,0))?))
    }
    pub fn wiring(&self,index:usize,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],GkrError>{
        if index!=0||r.len()!=self.shape.row_bits||u.len()!=self.shape.input_bits||v.len()!=self.shape.input_bits{
            return Err(GkrError::PointDimension);}
        Ok([self.fixed_e*eq(u,0)*eq(v,0),Fr::zero(),Fr::zero(),
            -weighted_rail(u,Q_START,Q_WIDTH)*weighted_rail(v,D_START,D_WIDTH)])
    }
    pub fn prove(&self,transcript:&mut Transcript,mut observe:impl FnMut(&RoundRecord))
        ->Result<(GkrProof,InputClaim),GkrError>{
        self.bind(transcript);let output=gkr::output_point(self.shape.row_count,transcript);
        gkr::append_usize(transcript,b"gkr-layer-index",0);
        let mut claim=Fr::zero();let mut rounds=Vec::with_capacity(18);
        let(a,b)=self.first_coefficients()?;
        let(u,left_value)=phase(a,b,&self.witness,&mut claim,&mut rounds,transcript,0,&mut observe)?;
        let(c,d)=self.second_coefficients(&u,left_value)?;
        // Restart original complete X; the first phase's reduced X is gone.
        let(v,right_value)=phase(c,d,&self.witness,&mut claim,&mut rounds,transcript,1,&mut observe)?;
        let coefficients=self.wiring(0,&output,&u,&v)?;
        if coefficients[0]+coefficients[3]*left_value*right_value!=claim{return Err(GkrError::TerminalExpression);}
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

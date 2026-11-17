//! Complete local field packet; imported Boolean/native/PCS premises stay open.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use crate::{gkr::{self,GkrError,GkrProof,InputClaim,LayerProof},
    implicit_witness::Witness,ratio_contraction::{eq,quadratic,RoundRecord},
    ratio_import_contraction::Descriptor as SourceDescriptor,sparse,transcript::Transcript};

pub(crate) const N:usize=1024;
pub(crate) const DOMAIN:&[u8]=b"ratio-packet-contraction-local-test-v1";
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) enum Order{BankThenTier,TierThenBank}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) enum Padding{ZeroPolynomial,ExternalOutput}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) enum AuxRole{Or64,Diff64,Borrow65}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) struct Aux{pub role:AuxRole,pub raw:usize,pub local:usize,pub width:usize}
#[derive(Clone,Debug,PartialEq,Eq)]
pub(crate) struct Descriptor{
    pub source:SourceDescriptor,pub input_len:usize,pub input_log:usize,
    pub row_count:usize,pub row_log:usize,pub log_copies:usize,pub row_base:usize,
    pub bank_start:usize,pub bank_len:usize,pub tier_start:usize,pub tier_len:usize,
    pub local_bank:usize,pub local_tier:usize,pub pad_start:usize,pub aux:[Aux;3],
    pub product_count:usize,pub small_count:usize,pub term_count:usize,
    pub order:Order,pub padding:Padding,
}
impl Descriptor{pub fn canonical()->Self{Self{
    source:SourceDescriptor::canonical(),input_len:N,input_log:10,row_count:N,row_log:10,
    log_copies:0,row_base:32489472,bank_start:673,bank_len:503,tier_start:8350,tier_len:134,
    local_bank:0,local_tier:503,pad_start:637,
    aux:[Aux{role:AuxRole::Or64,raw:2079982845,local:311,width:64},
        Aux{role:AuxRole::Diff64,raw:2079982909,local:375,width:64},
        Aux{role:AuxRole::Borrow65,raw:2079982973,local:439,width:65}],
    product_count:5824,small_count:1745,term_count:7569,
    order:Order::BankThenTier,padding:Padding::ZeroPolynomial,
}}}
#[derive(Clone,Debug,PartialEq,Eq)]
pub(crate) enum AdmissionError{Descriptor(&'static str),Protocol(GkrError),Witness(String),Residual(usize)}
#[derive(Clone,Debug,PartialEq,Eq)]
pub(crate) struct AggregateWork{pub updates:usize,pub scratch_capacity:usize,pub retained:usize}
pub(crate) struct AdmittedPacket{descriptor:Descriptor,witness:Witness,shape:sparse::Shape,delta:Fr}
fn add(a:usize,b:usize)->Result<usize,AdmissionError>{a.checked_add(b).ok_or(AdmissionError::Descriptor("overflow"))}
fn mul(a:usize,b:usize)->Result<usize,AdmissionError>{a.checked_mul(b).ok_or(AdmissionError::Descriptor("overflow"))}
fn admit(d:&Descriptor)->Result<sparse::Shape,AdmissionError>{
    let empty=sparse::Circuit{input_len:d.input_len,row_count:d.row_count,terms:Vec::new()};
    let shape=sparse::validate(&empty,d.log_copies).map_err(AdmissionError::Protocol)?;
    let q=mul(d.source.rails[2].width,d.source.rails[1].width)?;
    let r0=add(d.source.rails[0].width,d.source.rails[4].width)?;
    let r1=add(add(add(d.source.rails[1].width,d.source.rails[5].width)?,d.source.rails[6].width)?,1)?;
    let r2=add(add(d.source.rails[0].width,q)?,d.source.rails[3].width)?;
    let arith=add(add(r0,r1)?,r2)?;
    let or_tail=d.aux[0].width.checked_sub(1).ok_or(AdmissionError::Descriptor("aux width"))?;
    let extra=add(add(add(2,mul(4,or_tail)?)?,add(1,mul(5,d.aux[1].width)?)?)?,4)?;
    let count=add(add(d.bank_len,arith)?,extra)?;
    if count>1usize<<20{return Err(AdmissionError::Descriptor("term cap"));}
    if shape.input_bits!=10||shape.row_bits!=10||shape.copies!=1||shape.input_len!=N
        ||shape.row_count!=N||d.input_log!=10||d.row_log!=10||d.log_copies!=0{
        return Err(AdmissionError::Descriptor("fixed dimensions"));
    }
    let base=mul(d.source.owner,d.source.width)?;
    let row_base=mul(d.source.owner,d.source.row_stride)?;
    let bank_end=add(d.bank_start,d.bank_len)?;let tier_end=add(d.tier_start,d.tier_len)?;
    let pad=add(d.local_tier,d.tier_len)?;
    for rail in &d.source.rails{
        let raw=add(mul(rail.owner,d.source.width)?,rail.source_local)?;
        let end=add(rail.local,rail.width)?;let raw_end=add(rail.raw_base,rail.width)?;
        if raw!=rail.raw_base||end>N||raw_end>add(mul(rail.owner,d.source.width)?,d.source.width)?{
            return Err(AdmissionError::Descriptor("mapping intervals"));
        }
    }
    for aux in &d.aux{
        if add(aux.local,aux.width)?>504||aux.raw!=add(d.source.window_base,
            aux.local.checked_sub(1).ok_or(AdmissionError::Descriptor("mapping intervals"))?)?{
            return Err(AdmissionError::Descriptor("mapping intervals"));
        }
    }
    if base!=2079326208||row_base!=d.row_base||bank_end!=1176||tier_end!=8484||pad!=637
        ||add(d.source.window_base,d.source.window_width)?!=2079983038{
        return Err(AdmissionError::Descriptor("mapping intervals"));
    }
    if d.source!=SourceDescriptor::canonical(){return Err(AdmissionError::Descriptor("source descriptor"));}
    if q!=5824||count!=7569||d.product_count!=q||d.term_count!=count||d.small_count!=count-q{
        return Err(AdmissionError::Descriptor("term count"));
    }
    if *d!=Descriptor::canonical(){return Err(AdmissionError::Descriptor("canonical descriptor"));}
    Ok(shape)
}
fn value(w:&Witness,i:usize)->Result<Fr,AdmissionError>{w.value(i).map_err(AdmissionError::Witness)}
fn word(w:&Witness,start:usize,width:usize)->Result<Fr,AdmissionError>{
    let mut sum=Fr::zero();let mut power=Fr::one();
    for bit in 0..width{sum+=power*value(w,start+bit)?;power+=power;}Ok(sum)
}
fn check(row:usize,residual:Fr)->Result<(),AdmissionError>{
    if residual.is_zero(){Ok(())}else{Err(AdmissionError::Residual(row))}
}
fn weight(point:&[Fr],start:usize,width:usize)->Fr{
    let mut sum=Fr::zero();let mut power=Fr::one();
    for bit in 0..width{sum+=power*eq(point,start+bit);power+=power;}sum
}
fn linear(row:usize,start:usize,width:usize,scale:Fr,
    visit:&mut impl FnMut(usize,usize,usize,[Fr;4])->Result<(),GkrError>)->Result<(),GkrError>{
    let mut c=scale;for bit in 0..width{
        visit(row,start+bit,0,[Fr::zero(),c,Fr::zero(),Fr::zero()])?;c+=c;
    }Ok(())
}
// Exactly1745 small gate callbacks. The5824-term rectangle is never emitted.
pub(crate) fn small(mut visit:impl FnMut(usize,usize,usize,[Fr;4])->Result<(),GkrError>)
    ->Result<(),GkrError>{
    for k in 0..503{visit(k,1+k,1+k,[Fr::zero(),-Fr::one(),Fr::zero(),Fr::one()])?;}
    linear(503,1,91,Fr::one(),&mut visit)?;linear(503,504,224,-Fr::from(122880000u64),&mut visit)?;
    linear(504,92,64,Fr::one(),&mut visit)?;linear(504,728,64,-Fr::one(),&mut visit)?;
    linear(504,792,64,Fr::one(),&mut visit)?;
    visit(504,0,0,[-Fr::from(64u64),Fr::zero(),Fr::zero(),Fr::zero()])?;
    linear(505,1,91,Fr::one(),&mut visit)?;linear(505,247,64,-Fr::one(),&mut visit)?;
    linear(506,311,1,Fr::one(),&mut visit)?;linear(506,92,1,-Fr::one(),&mut visit)?;
    for bit in 1..64{
        linear(506+bit,311+bit,1,Fr::one(),&mut visit)?;
        linear(506+bit,92+bit,1,-Fr::one(),&mut visit)?;
        linear(506+bit,310+bit,1,-Fr::one(),&mut visit)?;
        visit(506+bit,92+bit,310+bit,[Fr::zero(),Fr::zero(),Fr::zero(),Fr::one()])?;
    }
    linear(570,374,1,Fr::one(),&mut visit)?;
    visit(570,0,0,[-Fr::one(),Fr::zero(),Fr::zero(),Fr::zero()])?;
    linear(571,439,1,Fr::one(),&mut visit)?;
    for bit in 0..64{
        for(start,scale)in[(247,Fr::one()),(92,-Fr::one()),(439,-Fr::one()),
            (375,-Fr::one()),(440,Fr::from(2u64))]{linear(572+bit,start+bit,1,scale,&mut visit)?;}
    }
    linear(636,503,1,Fr::one(),&mut visit)?;
    visit(636,0,0,[-Fr::one(),Fr::zero(),Fr::zero(),Fr::zero()])?;Ok(())
}
fn update(out:&mut Vec<(usize,Fr)>,index:usize,v:Fr)->Result<(),GkrError>{
    if !v.is_zero(){if out.len()==out.capacity(){return Err(GkrError::InvalidWireIndex);}out.push((index,v));}Ok(())
}
fn aggregate(mut entries:Vec<(usize,Fr)>,support:usize)->Result<(Witness,AggregateWork),GkrError>{
    let(updates,scratch_capacity)=(entries.len(),entries.capacity());
    entries.sort_unstable_by_key(|entry|entry.0);
    let(mut write,mut group,mut sum)=(0,None,Fr::zero());
    for read in 0..entries.len(){let(index,v)=entries[read];
        if group!=Some(index){if let Some(old)=group{if !sum.is_zero(){entries[write]=(old,sum);write+=1;}}
            group=Some(index);sum=Fr::zero();}sum+=v;
    }
    if let Some(old)=group{if !sum.is_zero(){entries[write]=(old,sum);write+=1;}}
    entries.truncate(write);
    // Raw scratch can exceed N. Normalize capacity before inherited admission.
    let normalized=entries.into_boxed_slice().into_vec();
    let witness=Witness::new(N,support,normalized).map_err(|_|GkrError::InvalidWireIndex)?;
    Ok((witness,AggregateWork{updates,scratch_capacity,retained:write}))
}
fn phase(mut a:Witness,mut b:Witness,input:&Witness,claim:&mut Fr,rounds:&mut Vec<Vec<Fr>>,
    t:&mut Transcript,index:usize,observe:&mut impl FnMut(&RoundRecord))->Result<(Vec<Fr>,Fr),GkrError>{
    let mut x=input.clone();let mut point=Vec::with_capacity(10);
    while x.extent()>1{
        let(p,work)=quadratic(&a,&b,&x)?;
        if p[0]+gkr::eval_polynomial(&p,Fr::one())!=*claim{return Err(GkrError::SumcheckIdentity);}
        gkr::append_polynomial(t,b"gkr-sumcheck-polynomial",&p);
        let challenge=t.challenge_scalar(b"gkr-sumcheck-challenge");*claim=gkr::eval_polynomial(&p,challenge);
        observe(&RoundRecord{phase:index,round:point.len(),extent:x.extent(),
            support:[a.entries().len(),b.entries().len(),x.entries().len()],polynomial:p,challenge,work});
        a=a.fold(&[challenge]).map_err(|_|GkrError::PointDimension)?;
        b=b.fold(&[challenge]).map_err(|_|GkrError::PointDimension)?;
        x=x.fold(&[challenge]).map_err(|_|GkrError::PointDimension)?;
        rounds.push(p.to_vec());point.push(challenge);
    }Ok((point,x.value(0).map_err(|_|GkrError::InvalidWireIndex)?))
}
impl AdmittedPacket{
    pub fn new(descriptor:Descriptor,witness:Witness)->Result<Self,AdmissionError>{
        let shape=admit(&descriptor)?;
        if witness.extent()!=N||witness.dimensions()!=10{return Err(AdmissionError::Protocol(GkrError::InvalidInputWidth));}
        for bit in 0..503{let x=value(&witness,1+bit)?;check(bit,x*(x-Fr::one()))?;}
        let mut words=[Fr::zero();7];
        for(v,rail)in words.iter_mut().zip(&descriptor.source.rails){*v=word(&witness,rail.local,rail.width)?;}
        check(503,words[0]-Fr::from(122880000u64)*words[4])?;
        check(504,words[1]-words[5]+words[6]-Fr::from(64u64))?;
        check(505,words[0]-words[2]*words[1]-words[3])?;
        check(506,value(&witness,311)?-value(&witness,92)?)?;
        for bit in 1..64{let z=value(&witness,311+bit)?;let d=value(&witness,92+bit)?;
            let prev=value(&witness,310+bit)?;check(506+bit,z-d-prev+d*prev)?;}
        check(570,value(&witness,374)?-Fr::one())?;check(571,value(&witness,439)?)?;
        for bit in 0..64{check(572+bit,value(&witness,247+bit)?-value(&witness,92+bit)?
            -value(&witness,439+bit)?-value(&witness,375+bit)?+Fr::from(2u64)*value(&witness,440+bit)?)?;}
        check(636,value(&witness,503)?-Fr::one())?;
        Ok(Self{descriptor,witness,shape,delta:words[1]})
    }
    pub fn with_admitted<R>(d:Descriptor,w:Witness,consumer:impl FnOnce(&Self)->R)->Result<R,AdmissionError>{
        let packet=Self::new(d,w)?;Ok(consumer(&packet))
    }
    pub fn witness(&self)->&Witness{&self.witness}
    pub fn descriptor(&self)->&Descriptor{&self.descriptor}
    pub fn descriptor_bytes(&self)->Vec<u8>{concat!(
        "version=ratio-packet-contraction-v1\n",
        "source-sha256=AFEA8F2B7B54302FB75C7613ACA87E05AA02FAE842AF92DB38CB2B66DC0F23D9\n",
        "source-n-h-e-owner-tier-index=2048,11,64,1983,1,0\n",
        "source-width-rowstride-wirebase-rowbase=1048576,16384,2079326208,32489472\n",
        "bank-source-rows=673,503\ntier-source-rows=8350,134\nrow-map=bank-first-0-tier-503-v1\n",
        "source-window=2079982535,503\nsource-placeholder=2079326208\n",
        "source-A=Numerator91,1983,656327,2079982535,91\n",
        "source-Delta=Delta64,1983,656418,2079982626,64\n",
        "source-Q=Quotient91,1983,656482,2079982690,91\n",
        "source-R=Remainder64,1983,656573,2079982781,64\n",
        "import-D=Difficulty224,1982,987674,2079265306,224\n",
        "import-end=TimestampEnd64,1983,525330,2079851538,64\n",
        "import-start=TimestampStart64,1023,525330,1073218578,64\n",
        "aux-OR=2079982845,311,64\naux-diff=2079982909,375,64\naux-borrow=2079982973,439,65\n",
        "wire-map=window-one-imports-504-728-792-placeholder-zero-v1\n",
        "input-output-log-copies=1024,1024,10,10,0\npad=637,387,zero-polynomial\n",
        "bank=x*x-x,left-right-self\narithmetic=A-122880000*D;Delta-end+start-64;A-Q*Delta-R\n",
        "or=z0-Delta0;zi-Deltai-zprev+Deltai*zprev;z63-1\n",
        "cmp=b0;Ri-Deltai-bi-di+2*bnext;b64-1\n",
        "channels=c0,c1,c3;c2zero\nlinear-right=placeholder-except-bank-self\n",
        "product=-2-power-p-plus-q,Q-outer-Delta-inner\n",
        "family-terms=503,6487,254,2,321,2\nterm-count=7569\nbulk=5824\nsmall=1745\n",
    ).as_bytes().to_vec()}
    pub fn bind(&self,t:&mut Transcript){t.append_bytes(b"ratio-packet-descriptor",&self.descriptor_bytes());}
    pub fn first_counted(&self,r:&[Fr])->Result<(Witness,Witness,[AggregateWork;2]),GkrError>{
        if r.len()!=10{return Err(GkrError::PointDimension);}
        let(mut a,mut b)=(Vec::with_capacity(1833),Vec::with_capacity(3));
        small(|row,l,h,c|{let rho=eq(r,row);
            let right=if c[3].is_zero(){Fr::zero()}else{self.witness.value(h).map_err(|_|GkrError::InvalidWireIndex)?};
            update(&mut a,l,rho*(c[1]+c[3]*right))?;update(&mut b,l,rho*c[0])})?;
        let mut scale=-eq(r,505)*self.delta;
        for bit in 0..91{update(&mut a,156+bit,scale)?;scale+=scale;}
        let(a,aw)=aggregate(a,855)?;let(b,bw)=aggregate(b,1)?;Ok((a,b,[aw,bw]))
    }
    pub fn first_coefficients(&self,r:&[Fr])->Result<(Witness,Witness),GkrError>{
        let(a,b,_)=self.first_counted(r)?;Ok((a,b))
    }
    pub fn second_counted(&self,r:&[Fr],u:&[Fr],left:Fr)->Result<(Witness,Witness,[AggregateWork;2]),GkrError>{
        if r.len()!=10||u.len()!=10{return Err(GkrError::PointDimension);}
        let(mut c,mut d)=(Vec::with_capacity(630),Vec::with_capacity(1682));
        small(|row,l,h,cs|{let k=eq(r,row)*eq(u,l);
            update(&mut c,h,k*cs[3]*left)?;update(&mut d,h,k*(cs[0]+cs[1]*left))})?;
        let mut scale=-eq(r,505)*weight(u,156,91)*left;
        for bit in 0..64{update(&mut c,92+bit,scale)?;scale+=scale;}
        let(c,cw)=aggregate(c,503)?;let(d,dw)=aggregate(d,504)?;Ok((c,d,[cw,dw]))
    }
    pub fn second_coefficients(&self,r:&[Fr],u:&[Fr],left:Fr)->Result<(Witness,Witness),GkrError>{
        let(c,d,_)=self.second_counted(r,u,left)?;Ok((c,d))
    }
    pub fn wiring(&self,index:usize,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],GkrError>{
        if index!=0||r.len()!=10||u.len()!=10||v.len()!=10{return Err(GkrError::PointDimension);}
        let mut coefficients=[Fr::zero();4];
        small(|row,l,h,c|{let k=eq(r,row)*eq(u,l)*eq(v,h);
            for channel in[0,1,3]{coefficients[channel]+=k*c[channel];}Ok(())})?;
        coefficients[3]-=eq(r,505)*weight(u,156,91)*weight(v,92,64);Ok(coefficients)
    }
    pub fn prove(&self,t:&mut Transcript,mut observe:impl FnMut(&RoundRecord))->Result<(GkrProof,InputClaim),GkrError>{
        self.bind(t);let r=gkr::output_point(self.shape.row_count,t);gkr::append_usize(t,b"gkr-layer-index",0);
        let mut claim=Fr::zero();let mut rounds=Vec::with_capacity(20);
        let(a,b)=self.first_coefficients(&r)?;
        let(u,left)=phase(a,b,&self.witness,&mut claim,&mut rounds,t,0,&mut observe)?;
        let(c,d)=self.second_coefficients(&r,&u,left)?;
        let(v,right)=phase(c,d,&self.witness,&mut claim,&mut rounds,t,1,&mut observe)?;
        let cs=self.wiring(0,&r,&u,&v)?;
        if cs[0]+cs[1]*left+cs[3]*left*right!=claim{return Err(GkrError::TerminalExpression);}
        let line=self.witness.line(&u,&v).map_err(|_|GkrError::PointDimension)?;
        t.append_scalar(b"gkr-left-value",&left);t.append_scalar(b"gkr-right-value",&right);
        gkr::append_polynomial(t,b"gkr-line-polynomial",&line);let lambda=t.challenge_scalar(b"gkr-line-challenge");
        Ok((GkrProof{layers:vec![LayerProof{rounds,left_value:left,right_value:right,line_coefficients:line.clone()}]},
            InputClaim{point:gkr::line_point(&u,&v,lambda),value:gkr::eval_polynomial(&line,lambda)}))
    }
    pub fn verify(&self,p:&GkrProof,t:&mut Transcript)->Result<InputClaim,GkrError>{
        gkr::verify_with_wiring(&[10],N,p,t,|t|self.bind(t),|i,r,u,v|self.wiring(i,r,u,v))
    }
}

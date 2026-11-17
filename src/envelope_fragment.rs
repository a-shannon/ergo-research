//! Test-only consumer-owned synthetic projection. No old-X/native authentication.
//! Layout authority: envelope-fragment-layout proposal-2, 91F96257 / CAFB74D8.
use ark_bn254::Fr;
use ark_ff::{One, PrimeField, Zero};
use num_bigint::{BigInt, Sign};
use num_traits::{Signed, ToPrimitive};
use crate::{gkr::Gate, sparse::{Circuit, Term}, wiring::{evaluate_shift, RightIndex}};

pub(crate) const INPUT: usize = 1 << 17;
pub(crate) const ROWS: usize = 1 << 18;
pub(crate) const OPS: usize = 73;
pub(crate) const I: u128 = 1_199_990_374_400;
pub(crate) const RESET: u128 = 122_702_194_049_536;
const P: i64 = 1_000_000_000;
const TE: i64 = 122_880_000;
const DEN: i64 = 4_000_000_000;
pub(crate) fn h(o: usize) -> usize { assert!(o < OPS); 8192 + 1024*o }
pub(crate) fn row(o: usize, local: usize) -> usize { assert!(local < 1024); 131072+1024*o+local }
pub(crate) fn slot(s: usize) -> usize { assert!(s < 22); 256*(s+1) }

#[derive(Clone, Copy, Debug)]
pub(crate) enum Word { Bits(usize, usize), Constant(u128) }
impl Word {
    fn bit(self, b: usize) -> Self {
        match self {
            Self::Bits(base,w) if b < w => Self::Bits(base+b,1),
            Self::Bits(..) => Self::Constant(0),
            Self::Constant(x) => Self::Constant(if b < 128 { (x>>b)&1 } else { 0 }),
        }
    }
}
pub(crate) fn word(base: usize, width: usize) -> Word { Word::Bits(base,width) }
fn d(s: usize) -> Word { word(slot(s),224) }
fn t(s: usize) -> Word { word(slot(s),64) }
fn w(s: usize) -> Word { word(slot(s),95) }
fn out(o: usize, width: usize) -> Word { word(h(o),width) }
fn ug() -> Word { word(h(1)+72,65) }
fn phi(o: usize) -> Word { word(h(o),1) }
fn half(o: usize) -> Word { word(h(o)+137,65) }
fn v(o: usize) -> Word { word(h(o)+72,65) }
fn f(x: i64) -> Fr { if x < 0 { -Fr::from(x.unsigned_abs()) } else { Fr::from(x as u64) } }
fn fc(x: u128) -> Fr { Fr::from_le_bytes_mod_order(&x.to_le_bytes()) }

/// Logical address metadata is code-owned and never a commitment-membership claim.
pub(crate) const D_OWNERS: [Option<usize>;10] = [None,Some(0),Some(1),Some(2),Some(3),Some(4),Some(1022),Some(2046),Some(3006),Some(845758)];
pub(crate) const TIME_OWNERS: [usize;3] = [1023,2047,3007];
pub(crate) const W_OWNERS: [usize;5] = [0,1,2,3,4];
pub(crate) const D_LOCAL: usize = 987674;
pub(crate) const TIME_LOCAL: usize = 525330;
pub(crate) const W_LOCAL: usize = 987450;

#[derive(Clone, Copy)]
enum Policy { Zero, Minimal(Word) }
#[derive(Clone, Copy)]
enum Op {
    Pin, Grid(Word), Cmp(usize,Word,Word,Policy,bool), Max(usize,Word,Word),
    Ratio(Word,Word,Word,i64), Pred, Smax, Floor(Word),
    Wadd(Word,Word,Word), Add(Word,i64,Word), Alias(usize,Word,Word), Empty,
}
/// Fixed immutable operands; helpers/public fields are never supplied by a peer.
fn op(o: usize) -> Op {
    match o {
        0 => Op::Pin, 1 => Op::Grid(out(34,224)),
        2..=11 => Op::Cmp(224,ug(),d(o-2),Policy::Zero,true),
        12 => Op::Ratio(d(7),t(11),t(10),0),
        13 => Op::Ratio(d(8),t(12),t(11),64), 14 => Op::Pred, 15 => Op::Smax,
        16 => Op::Max(224,d(0),d(1)),
        17..=20 => Op::Max(224,out(o-1,224),d(o-15)),
        21..=24 => Op::Max(224,out(o-1,224),d(o-15)),
        25 => Op::Floor(d(9)), 26 => Op::Grid(out(25,66)),
        27 => Op::Cmp(66,v(26),out(25,66),Policy::Zero,false),
        28 => Op::Cmp(66,half(26),out(25,66),Policy::Minimal(phi(26)),false),
        29 => Op::Cmp(65,ug(),v(26),Policy::Zero,false),
        30 => Op::Floor(out(24,224)),
        31 => Op::Max(224,Word::Constant(I),Word::Constant(RESET)),
        32 => Op::Max(224,out(31,224),out(15,92)),
        33 => Op::Max(224,out(32,224),out(24,224)),
        34 => Op::Max(224,out(33,224),out(30,66)),
        35 => Op::Cmp(224,ug(),out(34,224),Policy::Zero,false),
        36 => Op::Cmp(224,half(1),out(34,224),Policy::Minimal(phi(1)),false),
        37 => Op::Wadd(w(13),Word::Constant(0),word(slot(1),65)),
        38..=41 => Op::Wadd(w(o-24),w(o-25),word(slot(o-36),65)),
        42 => Op::Add(Word::Constant(0),17867,ug()),
        43 => Op::Add(w(13),17867,ug()),
        44 => Op::Add(w(14),9548,ug()), 45 => Op::Add(w(15),9548,ug()),
        46 => Op::Add(w(16),2090,v(54)), 47 => Op::Add(w(17),2090,v(59)),
        48 => Op::Max(224,d(4),d(5)),
        49..=52 => Op::Max(224,d(52-o),out(o-1,224)),
        53 => Op::Floor(out(51,224)), 54 => Op::Grid(out(53,66)),
        55 => Op::Cmp(66,v(54),out(53,66),Policy::Zero,false),
        56 => Op::Cmp(66,half(54),out(53,66),Policy::Minimal(phi(54)),false),
        57 => Op::Cmp(65,ug(),v(54),Policy::Zero,false),
        58 => Op::Floor(out(50,224)), 59 => Op::Grid(out(58,66)),
        60 => Op::Cmp(66,v(59),out(58,66),Policy::Zero,false),
        61 => Op::Cmp(66,half(59),out(58,66),Policy::Minimal(phi(59)),false),
        62 => Op::Cmp(65,ug(),v(59),Policy::Zero,false),
        63 => Op::Max(96,out(42,96),out(43,96)),
        64..=67 => Op::Max(96,out(o-1,96),out(o-20,96)),
        68 => Op::Alias(96,word(slot(18)+64,96),out(67,96)),
        69 => Op::Max(96,word(slot(19),96),word(slot(20),96)),
        70 => Op::Cmp(96,word(slot(21),96),out(69,96),Policy::Zero,false),
        71 => Op::Alias(65,word(slot(18)+160,65),ug()), 72 => Op::Empty,
        _ => unreachable!(),
    }
}

/// Algebra sink: the analytic implementation factors words/products; it has no
/// access to Circuit/Term and never expands an input or row weight domain.
trait Algebra {
    fn constant(&mut self, row: usize, c: Fr);
    fn linear(&mut self, row: usize, a: Word, c: Fr);
    fn product(&mut self, row: usize, a: Word, b: Word, c: Fr);
    fn signed(&mut self, r: usize, a: Word, sign: Word, c: Fr) {
        self.linear(r,a,c); self.product(r,sign,a,-f(2)*c);
    }
}
struct Literal { terms: Vec<Term> }
impl Literal {
    fn term(&mut self, row: usize, left: usize, right: usize, channel: usize, c: Fr) {
        if c.is_zero() { return; }
        let mut coeff=[Fr::zero();4]; coeff[channel]=c;
        self.terms.push(Term{row,gate:Gate{left,right,c0:coeff[0],c1:coeff[1],c2:coeff[2],c3:coeff[3]}});
    }
}
impl Algebra for Literal {
    fn constant(&mut self,r:usize,c:Fr){self.term(r,0,0,0,c)}
    fn linear(&mut self,r:usize,a:Word,c:Fr){
        match a { Word::Constant(x)=>self.constant(r,c*fc(x)), Word::Bits(base,width)=>{
            let mut k=c; for b in 0..width {self.term(r,base+b,0,1,k);k+=k;}
        }}
    }
    fn product(&mut self,r:usize,a:Word,b:Word,c:Fr){
        match (a,b) {
            (Word::Constant(x),_)=>self.linear(r,b,c*fc(x)),
            (_,Word::Constant(x))=>self.linear(r,a,c*fc(x)),
            (Word::Bits(left,lw),Word::Bits(right,rw))=>{
                let mut lk=c; for i in 0..lw {let mut k=lk;for j in 0..rw {self.term(r,left+i,right+j,3,k);k+=k;}lk+=lk;}
            }
        }
    }
}
pub(crate) fn eq(point:&[Fr],index:usize)->Fr {
    point.iter().enumerate().fold(Fr::one(),|a,(b,z)|a*if index>>b&1==1{*z}else{Fr::one()-z})
}
struct Analytic<'a> { r:&'a[Fr],u:&'a[Fr],v:&'a[Fr],coeff:[Fr;4],cached_row:usize,cached_weight:Fr }
impl Analytic<'_> {
    fn rw(&mut self,row:usize)->Fr {if self.cached_row!=row{self.cached_row=row;self.cached_weight=eq(self.r,row);}self.cached_weight}
    fn weight(point:&[Fr],a:Word)->Fr {
        match a {Word::Constant(x)=>fc(x)*eq(point,0),Word::Bits(base,width)=>{
            let mut sum=Fr::zero();let mut k=Fr::one();for b in 0..width{sum+=k*eq(point,base+b);k+=k;}sum
        }}
    }
}
impl Algebra for Analytic<'_> {
    fn constant(&mut self,r:usize,c:Fr){if c.is_zero(){return;}let z=self.rw(r);if !z.is_zero(){self.coeff[0]+=z*eq(self.u,0)*eq(self.v,0)*c;}}
    fn linear(&mut self,r:usize,a:Word,c:Fr){if c.is_zero(){return;}match a{
        Word::Constant(x)=>self.constant(r,c*fc(x)),_=>{let z=self.rw(r);if !z.is_zero(){self.coeff[1]+=z*Self::weight(self.u,a)*eq(self.v,0)*c;}}
    }}
    fn product(&mut self,r:usize,a:Word,b:Word,c:Fr){if c.is_zero(){return;}match(a,b){
        (Word::Constant(x),_)=>self.linear(r,b,c*fc(x)),(_,Word::Constant(x))=>self.linear(r,a,c*fc(x)),
        _=>{let z=self.rw(r);if !z.is_zero(){self.coeff[3]+=z*Self::weight(self.u,a)*Self::weight(self.v,b)*c;}}
    }}
}
fn cmp(s:&mut impl Algebra,o:usize,start:usize,width:usize,l:Word,r:Word,diff:usize,borrow:usize){
    s.linear(row(o,start),word(borrow,1),f(1));
    for b in 0..width{let z=row(o,start+1+b);s.linear(z,l.bit(b),f(1));s.linear(z,r.bit(b),f(-1));
        s.linear(z,word(borrow+b,1),f(-1));s.linear(z,word(diff+b,1),f(-1));s.linear(z,word(borrow+b+1,1),f(2));}
}
fn or_rows(s:&mut impl Algebra,o:usize,start:usize,a:Word,z:usize,width:usize){
    s.linear(row(o,start),word(z,1),f(1));s.linear(row(o,start),a.bit(0),f(-1));
    for b in 1..width{let r=row(o,start+b);s.linear(r,word(z+b,1),f(1));s.linear(r,a.bit(b),f(-1));
        s.linear(r,word(z+b-1,1),f(-1));s.product(r,a.bit(b),word(z+b-1,1),f(1));}
}
fn emit(s:&mut impl Algebra,o:usize,include_polynomial:bool){
    let b=h(o);let one=f(1);
    match op(o){
        Op::Pin=>{
            let mut at=0;for (base,width,value) in [(slot(18),3,6u128),(slot(18)+8,12,3008),(slot(18)+24,12,3072),(slot(18)+40,12,3008)]{
                for bit in 0..width{s.linear(row(o,at),word(base+bit,1),one);s.constant(row(o,at),-fc((value>>bit)&1));at+=1;}}
            for k in 10..=12{s.linear(row(o,at),word(slot(k)+63,1),one);at+=1;}
            for k in 13..=17{for bit in 95..224{s.linear(row(o,at),word(slot(k)+bit,1),one);at+=1;}}
            assert_eq!(at,687);
        }
        Op::Grid(_)=>{
            for k in 0..65{s.linear(row(o,0),word(b+k,1),one);}s.constant(row(o,0),-one);
            s.linear(row(o,1),word(b+65,7),one);for k in 0..65{s.linear(row(o,1),word(b+k,1),-Fr::from(k as u64));}
            for k in 0..65{s.linear(row(o,2+k),word(b+72+k,1),one);s.linear(row(o,2+k),word(b+k,1),-one);}
            for k in 0..64{s.linear(row(o,67+k),word(b+137+k,1),one);s.linear(row(o,67+k),word(b+k+1,1),-one);}
            s.linear(row(o,131),word(b+201,1),one);
        }
        Op::Cmp(width,l,r,policy,nz)=>{
            cmp(s,o,0,width,l,r,b,b+width);let last=word(b+2*width,1);
            match policy{Policy::Zero=>s.linear(row(o,width+1),last,one),Policy::Minimal(phi)=>{
                s.constant(row(o,width+1),one);s.linear(row(o,width+1),phi,-one);s.linear(row(o,width+1),last,-one);s.product(row(o,width+1),phi,last,one);
            }}
            if nz{assert_eq!(width,224);or_rows(s,o,227,r,b+449,224);s.linear(row(o,451),word(b+672,1),one);s.constant(row(o,451),-one);}
        }
        Op::Max(width,l,r)=>{
            cmp(s,o,0,width,l,r,b+width,b+2*width);let select=word(b+3*width,1);
            for bit in 0..width{let z=row(o,width+1+bit);s.linear(z,word(b+bit,1),one);s.linear(z,l.bit(bit),-one);
                s.product(z,select,r.bit(bit),-one);s.product(z,select,l.bit(bit),one);}
        }
        Op::Ratio(d,end,start,offset)=>{
            s.linear(row(o,0),word(b,91),one);s.linear(row(o,0),d,f(-TE));
            s.linear(row(o,1),word(b+91,64),one);s.linear(row(o,1),end,f(-1));s.linear(row(o,1),start,one);s.constant(row(o,1),f(-offset));
            s.linear(row(o,2),word(b,91),one);s.product(row(o,2),word(b+155,91),word(b+91,64),f(-1));s.linear(row(o,2),word(b+246,64),f(-1));
            or_rows(s,o,3,word(b+91,64),b+310,64);s.linear(row(o,67),word(b+373,1),one);s.constant(row(o,67),f(-1));
            cmp(s,o,68,64,word(b+246,64),word(b+91,64),b+374,b+438);s.linear(row(o,133),word(b+502,1),one);s.constant(row(o,133),f(-1));
        }
        Op::Pred=>{
            let n=word(b,130);let sn=word(b+130,1);let q=word(b+131,92);let sq=word(b+223,1);
            let rem=word(b+224,37);let sr=word(b+261,1);let c=word(b+262,92);let sc=word(b+354,1);
            if include_polynomial{s.signed(row(o,0),n,sn,one);s.linear(row(o,0),word(h(12)+155,91),f(4*P));s.linear(row(o,0),word(h(13)+155,91),f(-8*P));s.constant(row(o,0),f(-8*P-6144));}
            s.signed(row(o,1),n,sn,one);s.signed(row(o,1),q,sq,f(-DEN));s.signed(row(o,1),rem,sr,f(-1));
            s.signed(row(o,2),c,sc,one);s.signed(row(o,2),q,sq,f(-1));s.linear(row(o,2),word(b+706,1),f(-1));
            s.linear(row(o,3),word(b+706,1),one);s.linear(row(o,3),word(b+613,1),f(-1));s.product(row(o,3),sr,word(b+613,1),one);
            let fields=[(n,sn,355,130),(q,sq,485,92),(rem,sr,577,37),(c,sc,614,92)];let mut at=4;
            for (mag,_,z,width) in fields{or_rows(s,o,at,mag,b+z,width);at+=width;}assert_eq!(at,355);
            for (k,(_,sign,z,width)) in fields.into_iter().enumerate(){s.linear(row(o,355+k),sign,one);s.product(row(o,355+k),sign,word(b+z+width-1,1),f(-1));}
            for (at,sign,nz) in [(359,sq,b+576),(360,sr,b+613)]{s.product(row(o,at),word(nz,1),sign,one);s.product(row(o,at),word(nz,1),sn,f(-1));}
            cmp(s,o,361,37,rem,Word::Constant(DEN as u128),b+707,b+744);s.linear(row(o,399),word(b+781,1),one);s.constant(row(o,399),f(-1));
        }
        Op::Smax=>{
            cmp(s,o,0,92,Word::Constant(I),word(h(14)+262,92),b+93,b+185);
            s.linear(row(o,93),word(b+92,1),one);s.linear(row(o,93),word(b+277,1),f(-1));s.product(row(o,93),word(h(14)+354,1),word(b+277,1),one);
            for bit in 0..92{let r=row(o,94+bit);s.linear(r,word(b+bit,1),one);s.linear(r,Word::Constant(I).bit(bit),f(-1));
                s.product(r,word(b+92,1),word(h(14)+262+bit,1),f(-1));s.product(r,word(b+92,1),Word::Constant(I).bit(bit),one);}
        }
        Op::Floor(m)=>{s.linear(row(o,0),m,f(3));s.linear(row(o,0),word(b,66),f(-2));s.linear(row(o,0),word(b+66,1),f(-1));}
        Op::Wadd(next,prev,d)=>{s.linear(row(o,0),next,one);s.linear(row(o,0),prev,f(-1));s.linear(row(o,0),d,f(-1));}
        Op::Add(w,m,v)=>{s.linear(row(o,0),word(b,96),one);s.linear(row(o,0),w,f(-1));s.linear(row(o,0),v,f(-m));}
        Op::Alias(width,l,r)=>for bit in 0..width{s.linear(row(o,bit),l.bit(bit),one);s.linear(row(o,bit),r.bit(bit),f(-1));},
        Op::Empty=>{}
    }
}
fn field_len(o:usize)->usize{match op(o){Op::Pin|Op::Wadd(..)|Op::Alias(..)|Op::Empty=>0,Op::Grid(..)=>202,
    Op::Cmp(w,_,_,_,nz)=>if nz{673}else{2*w+1},Op::Max(w,..)=>3*w+1,Op::Ratio(..)=>503,Op::Pred=>782,Op::Smax=>278,Op::Floor(..)=>67,Op::Add(..)=>96}}
pub(crate) fn active_intervals()->Vec<(usize,usize)>{
    let mut raw=vec![(0,2)];for s in 0..18{let width=if(10..13).contains(&s){64}else{224};raw.push((slot(s),slot(s)+width));}
    for (a,n) in [(0,3),(8,12),(24,12),(40,12),(64,96),(160,65)]{raw.push((slot(18)+a,slot(18)+a+n));}
    for s in 19..22{raw.push((slot(s),slot(s)+96));}for o in 0..OPS{let n=field_len(o);if n>0{raw.push((h(o),h(o)+n));}}
    raw.sort_unstable();let mut merged:Vec<(usize,usize)>=Vec::new();for (a,b) in raw{if let Some(last)=merged.last_mut(){assert!(last.1<=a);if last.1==a{last.1=b;continue;}}merged.push((a,b));}merged
}
fn mask()->Vec<bool>{let mut bits=vec![false;INPUT];for(a,b)in active_intervals(){bits[a..b].fill(true);}bits}
pub(crate) fn circuit()->Circuit { component(&(0..OPS).collect::<Vec<_>>(),true) }
/// Component selection omits other op constraints explicitly; never full SAT.
pub(crate) fn component(selected:&[usize],polynomial:bool)->Circuit{
    use ark_ff::BigInteger;
    assert!(num_bigint::BigUint::from_bytes_le(&Fr::MODULUS.to_bytes_le())>(num_bigint::BigUint::from(1u8)<<155));
    let mut s=Literal{terms:Vec::new()};let active=mask();
    for(i,yes)in active.into_iter().enumerate(){
        if i==0{s.linear(i,word(0,1),f(1));}else if i==1{s.linear(i,word(1,1),f(1));s.constant(i,f(-1));}
        else if yes{s.terms.push(Term{row:i,gate:Gate{left:i,right:i,c0:Fr::zero(),c1:f(-1),c2:Fr::zero(),c3:f(1)}});}
        else{s.linear(i,word(i,1),f(1));}
    }
    for &o in selected{emit(&mut s,o,polynomial);}assert!(s.terms.len()<1<<20);
    Circuit{input_len:INPUT,row_count:ROWS,terms:s.terms}
}
#[derive(Clone,Copy)]
pub(crate) enum WiringFault { RelocatedRight, OmittedOrigin2 }
pub(crate) fn coefficients(r:&[Fr],u:&[Fr],v:&[Fr])->[Fr;4]{coefficients_impl(r,u,v,None,false)}
pub(crate) fn mutant_coefficients(r:&[Fr],u:&[Fr],v:&[Fr],fault:WiringFault)->[Fr;4]{
    match fault{WiringFault::RelocatedRight=>coefficients_impl(r,u,v,None,true),WiringFault::OmittedOrigin2=>coefficients_impl(r,u,v,Some(63),false)}
}
fn coefficients_impl(r:&[Fr],u:&[Fr],v:&[Fr],omit:Option<usize>,wrong_right:bool)->[Fr;4]{
    assert_eq!((r.len(),u.len(),v.len()),(18,17,17));
    let mut s=Analytic{r,u,v,coeff:[Fr::zero();4],cached_row:usize::MAX,cached_weight:Fr::zero()};
    let low=&r[..17];let high=Fr::one()-r[17];let intervals=active_intervals();let mut cursor=2;
    let boolean_row=r.iter().enumerate().try_fold(0usize,|a,(b,z)|if z.is_zero(){Some(a)}else if *z==Fr::one(){Some(a|(1<<b))}else{None});
    // Gate(left=right=i,c1=-1,c3=1) makes BOTH channels three-point.
    if let Some(i)=boolean_row.filter(|i|*i<INPUT){
        if i>=2{if intervals.iter().any(|(a,b)|*a<=i&&i<*b){let j=eq(u,i)*eq(v,i);s.coeff[1]-=j;s.coeff[3]+=j;}
            else{s.coeff[1]+=eq(u,i)*eq(v,0);}}
    }else if !high.is_zero(){for &(a,b) in &intervals{let a=a.max(2);if a>=b{continue;}
        if cursor<a{s.coeff[1]+=high*evaluate_shift(low,u,v,0,cursor as u64,a as u64,0,RightIndex::GlobalZero).unwrap();}
        let j=high*evaluate_shift(low,u,v,0,a as u64,b as u64,0,RightIndex::SameRow).unwrap();s.coeff[1]-=j;s.coeff[3]+=j;cursor=b;
    }
    if cursor<INPUT{s.coeff[1]+=high*evaluate_shift(low,u,v,0,cursor as u64,INPUT as u64,0,RightIndex::GlobalZero).unwrap();}}
    s.linear(0,word(0,1),f(1));s.linear(1,word(1,1),f(1));s.constant(1,f(-1));
    for o in 0..OPS{if Some(o)!=omit&&boolean_row.map_or(true,|i|(131072+1024*o..131072+1024*(o+1)).contains(&i)){emit(&mut s,o,true);}}
    if wrong_right{
        // A single code-owned linear contribution is deliberately relocated.
        let old=eq(v,0);let bad=eq(v,1<<16);s.coeff[1]+=eq(r,row(12,0))*Analytic::weight(u,word(h(12),91))*(bad-old);
    }
    s.coeff
}

#[derive(Clone)]
pub(crate) struct Witness { pub(crate) bits:Vec<bool> }
impl Witness {
    pub(crate) fn empty()->Self{let mut x=Self{bits:vec![false;INPUT]};x.bits[1]=true;x}
    pub(crate) fn get(&self,a:Word)->BigInt{match a{Word::Constant(x)=>BigInt::from(x),Word::Bits(base,width)=>{
        let mut n=BigInt::from(0);for b in 0..width{if self.bits[base+b]{n+=BigInt::from(1)<<b;}}n
    }}}
    pub(crate) fn put(&mut self,a:Word,n:&BigInt){match a{Word::Constant(x)=>assert_eq!(*n,BigInt::from(x)),Word::Bits(base,width)=>{
        assert!(n.sign()!=Sign::Minus,"negative unsigned word");assert!(n.bits()<=width as u64,"quiet width truncation forbidden");
        for b in 0..width{self.bits[base+b]=((n>>b)&BigInt::from(1))==BigInt::from(1);}
    }}}
    pub(crate) fn set(&mut self,base:usize,width:usize,n:impl Into<BigInt>){self.put(word(base,width),&n.into());}
    pub(crate) fn input(&self)->Vec<Fr>{self.bits.iter().map(|b|Fr::from(u64::from(*b))).collect()}
    fn assign_cmp(&mut self,l:Word,r:Word,width:usize,diff:usize,borrow:usize){
        self.bits[borrow]=false;let mut c=0i8;for bit in 0..width{let a=self.get(l.bit(bit)).to_i8().unwrap();let b=self.get(r.bit(bit)).to_i8().unwrap();
            let raw=a-b-c;self.bits[diff+bit]=raw.rem_euclid(2)==1;c=i8::from(raw<0);self.bits[borrow+bit+1]=c==1;}
    }
    fn assign_or(&mut self,a:Word,z:usize,width:usize){let mut yes=false;for bit in 0..width{yes|=self.get(a.bit(bit))==BigInt::from(1);self.bits[z+bit]=yes;}}
    fn signed_put(&mut self,base:usize,width:usize,sign:usize,n:&BigInt){self.set(base,width,n.abs());self.bits[sign]=n.sign()==Sign::Minus;}
    pub(crate) fn assign_pred_values(&mut self,n:BigInt,q:BigInt,r:BigInt,c:BigInt){
        let b=h(14);self.signed_put(b,130,b+130,&n);self.signed_put(b+131,92,b+223,&q);self.signed_put(b+224,37,b+261,&r);self.signed_put(b+262,92,b+354,&c);
        for(a,z,width)in [(word(b,130),b+355,130),(word(b+131,92),b+485,92),(word(b+224,37),b+577,37),(word(b+262,92),b+614,92)]{self.assign_or(a,z,width);}
        self.bits[b+706]=r>BigInt::from(0);self.assign_cmp(word(b+224,37),Word::Constant(DEN as u128),37,b+707,b+744);
    }
    pub(crate) fn pred_for_n(&mut self,n:BigInt){let q=&n/DEN;let r=&n-DEN*&q;let c=&q+BigInt::from(u8::from(r>BigInt::from(0)));self.assign_pred_values(n,q,r,c);}
    pub(crate) fn signed_get(&self,base:usize,width:usize,sign:usize)->BigInt{let n=self.get(word(base,width));if self.bits[sign]{-n}else{n}}
    pub(crate) fn assign_ratio(&mut self,o:usize,d_override:Option<Word>){
        let Op::Ratio(d,end,start,offset)=op(o)else{panic!("ratio opcode")};let b=h(o);let a=self.get(d_override.unwrap_or(d))*TE;let delta=self.get(end)-self.get(start)+offset;
        assert!(delta>BigInt::from(0));let q=&a/&delta;let rem=&a-&q*&delta;
        for(base,width,n)in [(b,91,a),(b+91,64,delta),(b+155,91,q),(b+246,64,rem)]{self.set(base,width,n);}
        self.assign_or(word(b+91,64),b+310,64);self.assign_cmp(word(b+246,64),word(b+91,64),64,b+374,b+438);
    }
    pub(crate) fn assign_one(&mut self,o:usize,grid_e:Option<usize>,omit_origin2:bool){let b=h(o);match op(o){
        Op::Pin|Op::Wadd(..)|Op::Empty=>{},Op::Alias(_,l,r)=>{let n=self.get(r);self.put(l,&n);},
        Op::Cmp(width,l,r,_,nz)=>{self.assign_cmp(l,r,width,b,b+width);if nz{self.assign_or(r,b+449,224);}},
        Op::Max(width,l,mut r)=>{if o==63&&omit_origin2{r=l;}self.assign_cmp(l,r,width,b+width,b+2*width);let n=self.get(if self.bits[b+3*width]{r}else{l});self.set(b,width,n);},
        Op::Grid(bound)=>{let n=self.get(bound);let e=grid_e.unwrap_or_else(||(0usize..=64).find(|e|n<=(BigInt::from(1)<<*e)).expect("grid cap"));assert!(e<=64);
            for k in 0..65{self.bits[b+k]=k==e;}self.set(b+65,7,e);self.set(b+72,65,BigInt::from(1)<<e);self.set(b+137,65,if e==0{BigInt::from(0)}else{BigInt::from(1)<<(e-1)});
        },
        Op::Ratio(..)=>self.assign_ratio(o,None),Op::Pred=>{let n=-4*P*self.get(word(h(12)+155,91))+8*P*self.get(word(h(13)+155,91))+8*P+6144;self.pred_for_n(n);},
        Op::Smax=>{self.assign_cmp(Word::Constant(I),word(h(14)+262,92),92,b+93,b+185);let use_c=!self.bits[h(14)+354]&&self.bits[b+277];self.bits[b+92]=use_c;
            let n=if use_c{self.get(word(h(14)+262,92))}else{BigInt::from(I)};self.set(b,92,n);},
        Op::Floor(m)=>{let a:BigInt=BigInt::from(3)*self.get(m);let q:BigInt=&a/2;let r=a-2*&q;self.set(b,66,q);self.set(b+66,1,r);},
        Op::Add(w,m,v)=>{let n=self.get(w)+m*self.get(v);self.set(b,96,n);},
    }}
}
pub(crate) const ORDER:[usize;73]=[12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,30,31,32,33,34,1,2,3,4,5,6,7,8,9,10,11,29,35,36,37,38,39,40,41,48,49,50,51,52,53,54,55,56,58,59,60,61,57,62,42,43,44,45,46,47,63,64,65,66,67,68,69,70,71,0,72];
pub(crate) fn fixture(negative:bool,d_zero:bool,e:Option<usize>,omit:bool,early:u64)->Witness{
    let mut x=Witness::empty();for s in 0..6{x.set(slot(s),224,if s==0&&d_zero{0u128}else{1});}
    for(s,n)in [(6,if negative{1}else{I+10}),(7,I+1),(8,if negative{1}else{I+2}),(9,3)]{x.set(slot(s),224,n);}
    for(s,n)in [(10,1000u64),(11,2024),(12,2984)]{x.set(slot(s),64,n);}for s in 13..18{x.set(slot(s),224,(s-12) as u64);}
    for(base,width,n)in [(slot(18),3,6u64),(slot(18)+8,12,3008),(slot(18)+24,12,3072),(slot(18)+40,12,3008)]{x.set(base,width,n);}
    x.set(slot(19),96,early);x.set(slot(20),96,99u64);x.set(slot(21),96,100u64);
    for o in ORDER{x.assign_one(o,if o==1{e}else{None},omit);}x
}
pub(crate) fn failures(c:&Circuit,x:&Witness)->Vec<(usize,Fr)>{
    let input=x.input();let mut rows=vec![Fr::zero();ROWS];for t in &c.terms{rows[t.row]+=t.gate.evaluate(&input);}
    rows.into_iter().enumerate().filter(|(_,v)|!v.is_zero()).collect()
}

/// Schedule-only scalar/analytic diagnostics, not a full old-X tuple join.
pub(crate) fn m(n:u64)->u64{assert!(n<1<<31);(n+64).min(843776)/1024}
pub(crate) fn active(a:u64,n:u64)->bool{a&1023==960&&(a>>10)<m(n)&&(a>>10)!=407}
pub(crate) fn endpoints(q:u64)->u64{(q+1).min(9)}
fn less(point:&[Fr],bound:u64)->Fr{
    let domain=1u64<<point.len();assert!(bound<=domain);if bound==domain{return Fr::one();}if bound==0{return Fr::zero();}
    let mut equal=Fr::one();let mut sum=Fr::zero();for b in(0..point.len()).rev(){if bound>>b&1==1{sum+=equal*(Fr::one()-point[b]);equal*=point[b];}else{equal*=Fr::one()-point[b];}}sum
}
pub(crate) fn selector(point:&[Fr],n:u64,low:usize)->Fr{
    assert_eq!(point.len(),31);let bound=m(n);let mut high=less(&point[10..],bound);if bound>407{high-=eq(&point[10..],407);}eq(&point[..10],low)*high
}
pub(crate) fn endpoint_coeff(r:&[Fr],u:&[Fr],v:&[Fr],n:u64,delta:u64)->Fr{
    assert_eq!((r.len(),u.len(),v.len()),(31,31,31));assert!((1..=8).contains(&delta));let bound=m(n);if bound<=delta{return Fr::zero();}
    let mut high=evaluate_shift(&r[10..],&u[10..],&v[10..],delta,delta,bound,0,RightIndex::GlobalZero).unwrap();
    if bound>407&&407>=delta{high-=eq(&r[10..],407)*eq(&u[10..],(407-delta)as usize)*eq(&v[10..],0);}
    eq(&r[..10],959)*eq(&u[..10],1023)*eq(&v[..10],0)*high
}

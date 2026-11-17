//! Portable local integer constraints. Conditional inputs are not authenticated words.
use ark_bn254::Fr;
use ark_ff::{BigInteger, One, PrimeField, Zero};
use num_bigint::BigUint;
use std::ops::Range;
use crate::{gkr::Gate, sparse::Term};

pub(crate) const INPUT: usize = 2048;
pub(crate) const ROWS: usize = 8192;
pub(crate) const LIVE: usize = 1994;
pub(crate) const GROUPS: [(&str, usize); 14] = [
    ("boolean",1994),("aliases",289),("positive",66),("range",1),
    ("score",1),("current",225),("predecessor",225),("maximum",2),
    ("guard",1),("gap-mask",225),("origin-zero",224),("terminal",225),
    ("padding",54),("max-mask",676),
];
#[derive(Clone,Debug)]
pub(crate) struct Layout {
    pub sw:Range<usize>,pub sv:Range<usize>,pub w:Range<usize>,pub v:Range<usize>,
    pub or:Range<usize>,pub a:Range<usize>,pub current:Range<usize>,pub p:Range<usize>,
    pub r:Range<usize>,pub d:Range<usize>,pub s:usize,pub gap:Range<usize>,
}
impl Layout {
    pub fn new()->Self {
        let l=Self{sw:0..224,sv:224..289,w:289..513,v:513..578,or:578..643,
            a:643..868,current:868..1093,p:1093..1318,r:1318..1543,d:1543..1768,
            s:1768,gap:1769..1994};
        let intervals=[l.sw.clone(),l.sv.clone(),l.w.clone(),l.v.clone(),l.or.clone(),
            l.a.clone(),l.current.clone(),l.p.clone(),l.r.clone(),l.d.clone(),
            l.s..l.s+1,l.gap.clone()];
        let mut end=0;for rail in intervals {assert_eq!(rail.start,end);end=rail.end;}
        assert_eq!(end,LIVE);assert!(LIVE<=INPUT);
        assert!(GROUPS.iter().map(|(_,n)|n).sum::<usize>()<=ROWS);l
    }
}
pub(crate) fn group(name:&str)->Range<usize>{
    let mut row=0;for (n,count) in GROUPS{if n==name{return row..row+count;}row+=count;}
    panic!("unknown local group")
}
pub(crate) fn row_label(row:usize)->&'static str {
    let local=row%ROWS;for (name,_) in GROUPS{if group(name).contains(&local){return name;}}
    "row-padding"
}
pub(crate) fn bounds()->Result<(),String>{
    let p=BigUint::from_bytes_le(&Fr::MODULUS.to_bytes_le());
    if p<=BigUint::from(1u8)<<227usize{return Err("integer residual modulus".into());}
    Layout::new();Ok(())
}
#[derive(Clone,Debug)]
pub(crate) struct ConditionalInputs {pub w:BigUint,pub v:BigUint}
#[derive(Clone,Debug)]
pub(crate) struct Spec {
    pub active:bool,pub origin_one:bool,pub reducing:bool,pub first:bool,
    pub terminal:bool,pub empty_terminal:bool,pub maturity:u64,
    pub guard_total:Option<BigUint>,pub expected:BigUint,
}
#[derive(Clone,Debug)]
pub(crate) struct LocalTerm {pub term:Term,pub previous:bool}
fn linear(w:usize,c:Fr)->Gate{Gate{left:w,right:0,c0:Fr::zero(),c1:c,c2:Fr::zero(),c3:Fr::zero()}}
fn constant(c:Fr)->Gate{Gate{left:0,right:0,c0:c,c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}}
fn product(l:usize,r:usize,c:Fr)->Gate{Gate{left:l,right:r,c0:Fr::zero(),c1:Fr::zero(),c2:Fr::zero(),c3:c}}
fn value(x:&BigUint)->Fr{Fr::from_le_bytes_mod_order(&x.to_bytes_le())}
struct Emit<F:FnMut(LocalTerm)> {sink:F,row:usize,count:usize}
impl<F:FnMut(LocalTerm)> Emit<F> {
    fn gate(&mut self,g:Gate,previous:bool){(self.sink)(LocalTerm{term:Term{row:self.row,gate:g},previous});self.count+=1;}
    fn lin(&mut self,w:usize,c:Fr){self.gate(linear(w,c),false);}
    fn bits(&mut self,rail:Range<usize>,c:Fr){let mut k=c;for w in rail{self.lin(w,k);k+=k;}}
    fn prod_bits(&mut self,s:usize,rail:Range<usize>,c:Fr){let mut k=c;for w in rail{self.gate(product(w,s,k),false);k+=k;}}
    fn next(&mut self){self.row+=1;}
    fn end(&self,name:&str){assert_eq!(self.row,group(name).end,"group {name}");}
}
pub(crate) fn emit_local(spec:&Spec,sink:impl FnMut(LocalTerm))->Result<usize,String> {
    bounds()?;
    if spec.maturity>=1<<16||spec.expected.bits()>225{return Err("local constant range before sink".into());}
    if spec.guard_total.as_ref().map_or(false,|n|n.bits()>224){return Err("local guard range before sink".into());}
    if spec.reducing&&!spec.active{return Err("inactive reduction before sink".into());}
    if spec.terminal&&!spec.reducing{return Err("terminal scope before sink".into());}
    let l=Layout::new();let one=Fr::one();let mut e=Emit{sink,row:0,count:0};
    for w in 0..LIVE {e.lin(w,if spec.active{-one}else{one});
        if spec.active{e.gate(product(w,w,one),false);}e.next();}e.end("boolean");
    for (src,dst) in [(l.sw.clone(),l.w.clone()),(l.sv.clone(),l.v.clone())] {
        for (a,b) in src.zip(dst){if spec.active{e.lin(b,one);e.lin(a,-one);}e.next();}}
    e.end("aliases");
    for i in 0..65 {if spec.active{e.lin(l.or.start+i,one);
        if i==0{e.lin(l.v.start,-one);}else{
            e.gate(Gate{left:l.or.start+i-1,right:l.v.start+i,c0:Fr::zero(),
                c1:-one,c2:-one,c3:one},false);}}
        e.next();}
    if spec.active{e.lin(l.or.end-1,one);e.gate(constant(-one),false);}e.next();e.end("positive");
    if spec.active{for w in l.v.start..l.v.end-1{e.gate(product(l.v.end-1,w,one),false);}}
    e.next();e.end("range");
    if spec.active{e.bits(l.a.clone(),one);e.bits(l.w.clone(),-one);e.bits(l.v.clone(),-Fr::from(spec.maturity));}
    e.next();e.end("score");
    for (a,b) in l.a.clone().zip(l.current.clone()) {if spec.active{e.lin(b,one);if spec.reducing{e.lin(a,-one);}}e.next();}
    e.end("current");
    for (i,w) in l.p.clone().enumerate(){if spec.active{e.lin(w,one);
        if spec.reducing&&!spec.first{e.gate(linear(l.r.start+i,-one),true);}}e.next();}
    e.end("predecessor");
    if spec.active&&spec.reducing {
        e.bits(l.current.clone(),one);e.bits(l.p.clone(),-one);e.bits(l.d.clone(),one);
        e.prod_bits(l.s,l.d.clone(),-Fr::from(2u8));e.lin(l.s,-one);
    }e.next();
    if spec.active&&spec.reducing{e.bits(l.r.clone(),one);e.bits(l.p.clone(),-one);
        e.prod_bits(l.s,l.d.clone(),-one);e.lin(l.s,-one);}
    e.next();e.end("maximum");
    if spec.active{if let Some(total)=&spec.guard_total{e.gate(constant(value(total)),false);
        e.bits(l.a.clone(),-one);e.bits(l.gap.clone(),-one);}}
    e.next();e.end("guard");
    for w in l.gap.clone(){if spec.active&&spec.guard_total.is_none(){e.lin(w,one);}e.next();}e.end("gap-mask");
    for w in l.w.clone(){if spec.active&&spec.origin_one{e.lin(w,one);}e.next();}e.end("origin-zero");
    for (i,w) in l.r.clone().enumerate(){if spec.terminal||spec.empty_terminal {
        if spec.terminal{e.lin(w,one);}e.gate(constant(-Fr::from(u64::from(spec.expected.bit(i as u64)))),false);
    }e.next();}e.end("terminal");
    for w in LIVE..INPUT{e.lin(w,one);e.next();}e.end("padding");
    for w in l.p.clone().chain(l.r.clone()).chain(l.d.clone()).chain(std::iter::once(l.s)){
        if spec.active&&!spec.reducing{e.lin(w,one);}e.next();}e.end("max-mask");
    assert_eq!(e.row,4208);Ok(e.count)
}
pub(crate) fn put(x:&mut[Fr],rail:Range<usize>,n:&BigUint)->Result<(),String>{
    if n.bits()>rail.len() as u64{return Err("local rail overflow".into());}
    for (i,w) in rail.enumerate(){x[w]=Fr::from(u64::from(n.bit(i as u64)));}Ok(())
}
pub(crate) fn produce(spec:&Spec,input:Option<&ConditionalInputs>,previous:&BigUint)->Result<Vec<Fr>,String>{
    bounds()?;let mut x=vec![Fr::zero();INPUT];let l=Layout::new();
    if !spec.active{return Ok(x);}
    let input=input.ok_or("missing conditional local input")?;
    if input.w.bits()>224||input.v.is_zero()||input.v>(BigUint::from(1u8)<<64usize)
        ||spec.maturity>=1<<16{return Err("local producer range".into());}
    for rail in [l.sw.clone(),l.w.clone()]{put(&mut x,rail,&input.w)?;}
    for rail in [l.sv.clone(),l.v.clone()]{put(&mut x,rail,&input.v)?;}
    let mut seen=false;for i in 0..65{seen|=input.v.bit(i);x[l.or.start+i as usize]=Fr::from(u64::from(seen));}
    let a=&input.w+&input.v*spec.maturity;put(&mut x,l.a.clone(),&a)?;
    if spec.reducing{let p=if spec.first{BigUint::from(0u8)}else{previous.clone()};
        let s=a>p;let d=if s{&a-&p-1u8}else{&p-&a};let r=if s{a.clone()}else{p.clone()};
        put(&mut x,l.current.clone(),&a)?;put(&mut x,l.p.clone(),&p)?;
        put(&mut x,l.r.clone(),&r)?;put(&mut x,l.d.clone(),&d)?;x[l.s]=Fr::from(u64::from(s));}
    if let Some(total)=&spec.guard_total{if total<&a{return Err("local guard underflow".into());}
        put(&mut x,l.gap.clone(),&(total-&a))?;}Ok(x)
}
#[derive(Clone,Debug)]
pub(crate) struct Failure {pub row:usize,pub label:&'static str,pub residual:Fr}
pub(crate) fn failures(terms:&[Term],rows:usize,lookup:impl Fn(usize)->Fr)->Vec<Failure>{
    use std::collections::BTreeMap;
    let mut sums=BTreeMap::<usize,Fr>::new();for t in terms{assert!(t.row<rows);let g=&t.gate;
        let a=lookup(g.left);let b=lookup(g.right);*sums.entry(t.row).or_insert(Fr::zero())+=g.c0+g.c1*a+g.c2*b+g.c3*a*b;}
    sums.into_iter().filter(|(_,z)|!z.is_zero()).map(|(row,residual)|Failure{row,label:row_label(row),residual}).collect()
}

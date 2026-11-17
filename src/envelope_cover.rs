//! Conditional local dyadic cover. No historical banks or authenticated inputs.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use num_bigint::BigUint;
use std::ops::Range;
use crate::{gkr::Gate, sparse::Term};

pub(crate) const BASE: usize = 10240;
pub(crate) const ROW_BASE: usize = 20480;
pub(crate) const INPUT: usize = 2048;
pub(crate) const ROWS: usize = 4096;
pub(crate) const INITIAL: u64 = 1199990374400;
pub(crate) const RESET: u64 = 122702199259136;
#[derive(Clone, Debug)]
pub(crate) enum Descriptor { Envelope, Unit { candidate: BigUint } }
#[derive(Clone, Debug)]
pub(crate) struct Layout {
    pub candidates: Vec<Range<usize>>, pub u: Range<usize>, pub hot: Range<usize>,
    pub half: Range<usize>, pub select: Range<usize>, pub selected: Range<usize>,
    pub gaps: Vec<Range<usize>>, pub minimal: Range<usize>, pub live: usize,
}
fn take(n: &mut usize, width: usize) -> Range<usize> { let lo=*n; *n+=width; lo..*n }
impl Layout {
    pub fn new(d: &Descriptor) -> Self {
        let widths: &[usize] = match d { Descriptor::Envelope => &[65,65,253,224,224,224,65], Descriptor::Unit{..} => &[65] };
        let mut n=0; let candidates=widths.iter().map(|w|take(&mut n,*w)).collect::<Vec<_>>();
        let u=take(&mut n,65); let hot=take(&mut n,65); let half=take(&mut n,64);
        let select=take(&mut n,widths.len()); let selected=take(&mut n,65);
        let gaps=widths.iter().map(|_|take(&mut n,65)).collect(); let minimal=take(&mut n,65);
        assert!(n<=INPUT); Self{candidates,u,hot,half,select,selected,gaps,minimal,live:n}
    }
}
#[derive(Clone, Debug)]
pub(crate) struct Cover { descriptor: Descriptor, layout: Layout }
impl Cover {
    pub fn new(descriptor: Descriptor) -> Result<Self,String> {
        crate::origin_score::bounds()?;
        if let Descriptor::Unit{candidate}=&descriptor {
            if candidate.is_zero() || candidate.bits()>65 { return Err("unit candidate width/positivity".into()); }
        }
        let layout=Layout::new(&descriptor); Ok(Self{descriptor,layout})
    }
    pub fn is_envelope(&self)->bool { matches!(self.descriptor,Descriptor::Envelope) }
    pub fn layout(&self)->&Layout { &self.layout }
    pub fn groups(&self)->Vec<(&'static str,Range<usize>)> {
        let n=self.layout.candidates.len(); let envelope=self.is_envelope();
        let sizes=[("boolean",self.layout.live),("constant-anchors",if envelope{130}else{65}),
            ("source-alias",if envelope{990}else{0}),("high-zero",if envelope{665}else{0}),
            ("onehot",1),("u-rail",1),("half-rail",1),("select-onehot",1),
            ("selected",65),("cover",n),("minimal",1),("padding",INPUT-self.layout.live)];
        let mut row=ROW_BASE; sizes.into_iter().map(|(name,count)|{let lo=row;row+=count;(name,lo..row)}).collect()
    }
    pub fn group(&self,name:&str)->Range<usize> { self.groups().into_iter().find(|(n,_)|*n==name).expect("code-owned cover group").1 }
    pub fn emit(&self,mut sink:impl FnMut(Term))->usize {
        let l=&self.layout; let mut e=Emitter{sink:&mut sink,row:ROW_BASE,count:0}; let one=Fr::one();
        for w in 0..l.live { e.row([linear(BASE+w,-one),product(BASE+w,BASE+w,one)]); }
        let constants=match &self.descriptor {Descriptor::Envelope=>vec![BigUint::from(INITIAL),BigUint::from(RESET)],Descriptor::Unit{candidate}=>vec![candidate.clone()]};
        for (rail,value) in l.candidates.iter().zip(constants.iter()) { for (b,w) in rail.clone().enumerate(){e.row([linear(BASE+w,one),constant(-Fr::from(u64::from(value.bit(b as u64))))]);} }
        if self.is_envelope() {
            for (rail,(source,width)) in l.candidates[2..].iter().zip([(5668usize,253usize),(641,224),(865,224),(8192+225,224),(8192+740,65)]) {
                assert_eq!(rail.len(),width); for (i,w) in rail.clone().enumerate(){ e.row([linear(BASE+w,one),linear(source+i,-one)]); }
            }
            for rail in &l.candidates[2..6] { for w in rail.start+65..rail.end { e.row([linear(BASE+w,one)]); } }
        }
        e.start();e.gate(constant(-one));for w in l.hot.clone(){e.gate(linear(BASE+w,one));}e.end();
        e.start();e.bits(l.u.clone(),one);e.bits(l.hot.clone(),-one);e.end();
        e.start();e.bits(l.half.clone(),one);e.bits(l.hot.start+1..l.hot.end,-one);e.end();
        e.start();e.gate(constant(-one));for w in l.select.clone(){e.gate(linear(BASE+w,one));}e.end();
        for b in 0..65 {e.start();e.gate(linear(BASE+l.selected.start+b,one));
            for (j,candidate) in l.candidates.iter().enumerate(){e.gate(product(BASE+l.select.start+j,BASE+candidate.start+b,-one));}e.end();}
        for (c,gap) in l.candidates.iter().zip(&l.gaps){e.start();e.bits(l.u.clone(),one);e.bits(c.start..c.start+65,-one);e.bits(gap.clone(),-one);e.end();}
        e.start();e.gate(constant(-one));e.bits(l.selected.clone(),one);e.bits(l.half.clone(),-one);e.bits(l.minimal.clone(),-one);e.end();
        for w in l.live..INPUT {e.row([linear(BASE+w,one)]);}
        assert_eq!(e.row,self.group("padding").end);
        assert!(e.row<=ROW_BASE+ROWS);
        if self.is_envelope(){assert_eq!((l.live,e.row-ROW_BASE,e.count),(1906,3910,9271));}
        else{assert_eq!((l.live,e.row-ROW_BASE,e.count),(455,2184,3479));}
        e.count
    }
    pub fn produce(&self,candidates:&[BigUint])->Result<Vec<Fr>,String> {
        if candidates.len()!=self.layout.candidates.len(){return Err("canonical candidate count".into());}
        match &self.descriptor {
            Descriptor::Envelope if candidates[0]!=BigUint::from(INITIAL)||candidates[1]!=BigUint::from(RESET)=>return Err("literal envelope constants".into()),
            Descriptor::Unit{candidate} if &candidates[0]!=candidate=>return Err("literal unit candidate".into()),_=>{}
        }
        let ceiling=BigUint::from(1u8)<<64usize;
        if candidates.iter().any(|c|c>&ceiling){return Err("local envelope <=2^64 profile".into());}
        let max=candidates.iter().max().ok_or("nonempty roster")?;
        let exp=(0usize..=64).find(|e|&(BigUint::from(1u8)<<e)>=max).ok_or("cover exponent")?;
        let u=BigUint::from(1u8)<<exp; let half=&u>>1usize;
        let selected=candidates.iter().position(|c|c>&half).ok_or("strict lower-half witness")?;
        let l=&self.layout;let mut x=vec![Fr::zero();INPUT];
        for (rail,value) in l.candidates.iter().zip(candidates){put(&mut x,rail.clone(),value)?;}
        put(&mut x,l.u.clone(),&u)?;put(&mut x,l.half.clone(),&half)?;x[l.hot.start+exp]=Fr::one();
        x[l.select.start+selected]=Fr::one();put(&mut x,l.selected.clone(),&candidates[selected])?;
        for (c,gap) in candidates.iter().zip(&l.gaps){put(&mut x,gap.clone(),&(&u-c))?;}
        put(&mut x,l.minimal.clone(),&(&candidates[selected]-&half-1u8))?;Ok(x)
    }
    pub fn authenticate(&self,terms:&[Term])->Result<(),String>{
        let mut i=0;let mut same=true;self.emit(|t|{same&=terms.get(i)==Some(&t);i+=1;});
        if !same||i!=terms.len(){return Err("canonical cover tuple fields/order/count".into());}Ok(())
    }
    pub fn verify(&self,terms:&[Term],mut lookup:impl FnMut(usize)->Fr)->Result<(),String>{
        self.authenticate(terms)?;let mut rows=vec![Fr::zero();ROWS];
        for t in terms{let g=&t.gate;let a=lookup(g.left);let b=lookup(g.right);rows[t.row-ROW_BASE]+=g.c0+g.c1*a+g.c2*b+g.c3*a*b;}
        if let Some(row)=rows.iter().position(|v|!v.is_zero()){let row=row+ROW_BASE;
            let name=self.groups().into_iter().find(|(_,r)|r.contains(&row)).map(|(n,_)|n).unwrap_or("cover-unused");return Err(format!("{name} row {row}"));}Ok(())
    }
}
pub(crate) fn put(x:&mut[Fr],rail:Range<usize>,n:&BigUint)->Result<(),String>{
    if n.bits()>rail.len() as u64{return Err("local bitword width".into());}
    for (b,w) in rail.enumerate(){x[w]=Fr::from(u64::from(n.bit(b as u64)));}Ok(())
}
pub(crate) fn linear(w:usize,c:Fr)->Gate{Gate{left:w,right:BASE,c0:Fr::zero(),c1:c,c2:Fr::zero(),c3:Fr::zero()}}
pub(crate) fn constant(c:Fr)->Gate{Gate{left:BASE,right:BASE,c0:c,c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}}
fn product(left:usize,right:usize,c:Fr)->Gate{Gate{left,right,c0:Fr::zero(),c1:Fr::zero(),c2:Fr::zero(),c3:c}}
struct Emitter<F:FnMut(Term)>{sink:F,row:usize,count:usize}
impl<F:FnMut(Term)> Emitter<F>{
    fn start(&mut self){} fn gate(&mut self,gate:Gate){(self.sink)(Term{row:self.row,gate});self.count+=1;}
    fn end(&mut self){self.row+=1;}
    fn row(&mut self,gates:impl IntoIterator<Item=Gate>){for gate in gates{self.gate(gate);}self.end();}
    fn bits(&mut self,rail:Range<usize>,c:Fr){let mut weight=c;for w in rail{self.gate(linear(BASE+w,weight));weight+=weight;}}
}

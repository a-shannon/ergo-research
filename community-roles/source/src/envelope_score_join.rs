//! Fixed local producer-to-consumer join; ordered tuples are not cryptographic authentication.
use ark_bn254::Fr;
use ark_ff::{One,Zero};
use num_bigint::BigUint;
use crate::{certified_legacy_bound as legacy,certified_modern_cap as modern,
    envelope_cover::{self as cover,Cover,Descriptor},origin_score as words,
    origin_score_map::{Plan as ScorePlan,Profile,Mode,GuardPolicy},sparse::Term};
pub(crate) const INPUT:usize=16384;
pub(crate) const ROWS:usize=65536;
pub(crate) const SCORE_BASE:usize=12288;
pub(crate) const SCORE_ROWS:usize=24576;
pub(crate) const BRIDGE_ROWS:usize=40960;
pub(crate) const TERMS:usize=93441;
#[derive(Clone,Debug)]
pub(crate) struct Declaration{
    pub legacy:legacy::Inputs,pub bound:BigUint,pub modern_d:BigUint,pub modern_q:BigUint,
    pub work:[BigUint;2],pub mode:Mode,pub prefix:usize,pub expected:BigUint,pub guard:GuardPolicy,
}
#[derive(Clone,Debug)]
pub(crate) struct Plan{declaration:Declaration,legacy:legacy::Statement,modern:modern::Statement,
    cover:Cover,score:ScorePlan}
impl Plan{
    pub fn new(d:Declaration)->Result<Self,String>{
        words::bounds()?;
        let legacy=legacy::Statement::new(&d.legacy,&d.bound)?;
        let modern=modern::Statement::new(&d.modern_d,&d.modern_q)?;
        if d.work.iter().any(|n|n.bits()>224)||!d.work[0].is_zero(){return Err("conditional work width/origin1".into());}
        let score=ScorePlan::new(1,2,vec![Profile{mode:d.mode,prefix:d.prefix,expected:d.expected.clone(),guard:d.guard.clone()}])?;
        let cover=Cover::new(Descriptor::Envelope)?;
        Ok(Self{declaration:d,legacy,modern,cover,score})
    }
    pub fn declaration(&self)->&Declaration{&self.declaration}
    pub fn cover(&self)->&Cover{&self.cover}
    fn canonical(&self,mut sink:impl FnMut(Term))->Result<usize,String>{
        // All fallible admissions precede even the internal emitter callbacks.
        Self::new(self.declaration.clone())?;
        for s in 0..2 {self.score.spec(0,s)?;}
        let mut count=0usize;
        legacy::emit(&self.legacy,|t|{count+=1;sink(t);});
        modern::emit(&self.modern,|mut t|{t.row+=16384;t.gate.left+=8192;t.gate.right+=8192;count+=1;sink(t);});
        self.cover.emit(|t|{count+=1;sink(t);});
        for s in 0..2{self.score.emit_owner(0,s,|mut t|{t.row+=SCORE_ROWS;t.gate.left+=SCORE_BASE;t.gate.right+=SCORE_BASE;count+=1;sink(t);})?;}
        let l=words::Layout::new();let mut row=BRIDGE_ROWS;
        for s in 0..2{for b in 0..65{for gate in [cover::linear(SCORE_BASE+s*words::INPUT+l.sv.start+b,Fr::one()),cover::linear(cover::BASE+self.cover.layout().u.start+b,-Fr::one())]{sink(Term{row,gate});count+=1;}row+=1;}}
        for s in 0..2{for b in 0..224{for gate in [cover::linear(SCORE_BASE+s*words::INPUT+l.sw.start+b,Fr::one()),cover::constant(-Fr::from(u64::from(self.declaration.work[s].bit(b as u64))))]{sink(Term{row,gate});count+=1;}row+=1;}}
        assert_eq!(row,41538);if self.declaration.prefix==2&&matches!(self.declaration.guard,GuardPolicy::Disabled){assert_eq!(count,TERMS);}Ok(count)
    }
    pub fn terms(&self)->Result<Vec<Term>,String>{
        let count=self.canonical(|_|{})?;let mut out=Vec::with_capacity(count);self.canonical(|t|out.push(t))?;
        assert_eq!((out.len(),out.capacity()),(count,count));
        if out.iter().any(|t|t.row>=ROWS||t.gate.left>=INPUT||t.gate.right>=INPUT){return Err("local join tuple extent".into());}Ok(out)
    }
    pub fn emit(d:Declaration,mut sink:impl FnMut(Term))->Result<usize,String>{
        let plan=Self::new(d)?;let terms=plan.terms()?;let n=terms.len();for t in terms{sink(t);}Ok(n)
    }
    pub fn authenticate(&self,terms:&[Term])->Result<(),String>{
        let mut i=0;let mut same=true;self.canonical(|t|{same&=terms.get(i)==Some(&t);i+=1;})?;
        if !same||i!=terms.len(){return Err("canonical join tuple fields/order/count".into());}Ok(())
    }
    pub fn verify(&self,terms:&[Term],mut lookup:impl FnMut(usize)->Fr)->Result<(),String>{
        self.authenticate(terms)?;
        let mut rows=vec![Fr::zero();ROWS];
        for t in terms{let g=&t.gate;let a=lookup(g.left);let b=lookup(g.right);rows[t.row]+=g.c0+g.c1*a+g.c2*b+g.c3*a*b;}
        if let Some(row)=rows.iter().position(|v|!v.is_zero()){return Err(format!("{} row {row}",self.row_label(row)));}Ok(())
    }
    pub fn row_label(&self,row:usize)->&'static str{
        if row<16384{return "legacy";}if row<20480{return "modern";}
        for (label,range) in self.cover.groups(){if range.contains(&row){return label;}}
        if (SCORE_ROWS..BRIDGE_ROWS).contains(&row){return words::row_label(row-SCORE_ROWS);}
        if (BRIDGE_ROWS..BRIDGE_ROWS+130).contains(&row){return "V-bridge";}
        if (BRIDGE_ROWS+130..41538).contains(&row){return "W-anchor";}"unused-row"
    }
    pub fn produce(&self)->Result<Vec<Fr>,String>{
        let d=&self.declaration;let mut x=vec![Fr::zero();INPUT];
        let old=legacy::producer(&d.legacy,&d.bound)?;x[..8192].copy_from_slice(&old);drop(old);
        let old=modern::producer(&d.modern_d)?;x[8192..10240].copy_from_slice(&old);drop(old);
        let candidates=[BigUint::from(cover::INITIAL),BigUint::from(cover::RESET),d.bound.clone(),d.legacy.d[0].clone(),d.legacy.d[1].clone(),d.modern_d.clone(),d.modern_q.clone()];
        let local=self.cover.produce(&candidates)?;x[10240..12288].copy_from_slice(&local);
        let mut u=BigUint::from(0u8);for (b,w) in self.cover.layout().u.clone().enumerate(){if local[w]==Fr::one(){u|=BigUint::from(1u8)<<b;}}drop(local);
        let mut previous=BigUint::from(0u8);
        for s in 0..2{let spec=self.score.spec(0,s)?;let local=words::produce(&spec,Some(&words::ConditionalInputs{w:d.work[s].clone(),v:u.clone()}),&previous)?;
            x[SCORE_BASE+s*2048..SCORE_BASE+(s+1)*2048].copy_from_slice(&local);
            previous=BigUint::from(0u8);let l=words::Layout::new();for (b,w) in l.r.enumerate(){if local[w]==Fr::one(){previous|=BigUint::from(1u8)<<b;}}}
        Ok(x)
    }
    pub fn coefficients(&self,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String>{
        if (r.len(),u.len(),v.len())!=(16,14,14){return Err("local join coefficient dimensions".into());}
        // Bounded tables only. Every placeholder retains its actual coordinate.
        let rr=(0..ROWS).map(|i|eq(r,i)).collect::<Vec<_>>();let uu=(0..INPUT).map(|i|eq(u,i)).collect::<Vec<_>>();let vv=(0..INPUT).map(|i|eq(v,i)).collect::<Vec<_>>();
        let mut out=[Fr::zero();4];self.canonical(|t|{let g=t.gate;let w=rr[t.row]*uu[g.left]*vv[g.right];for (sum,c) in out.iter_mut().zip([g.c0,g.c1,g.c2,g.c3]){*sum+=w*c;}})?;Ok(out)
    }
}
fn eq(p:&[Fr],i:usize)->Fr{p.iter().enumerate().fold(Fr::one(),|a,(b,z)|a*if i>>b&1==1{*z}else{Fr::one()-z})}

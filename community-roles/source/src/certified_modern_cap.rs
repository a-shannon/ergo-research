//! Local q(D) arithmetic for one positive source difficulty.
//! Parent/cut and physical X/ROW authority belong to the caller.
use ark_bn254::Fr;
use ark_ff::{BigInteger, One, PrimeField, Zero};
use num_bigint::BigUint;
use std::ops::Range;
use crate::{gkr::{Gate, GkrError}, sparse::{self, Circuit, Term}, transcript::Transcript};

pub(crate) const M:usize=2048;
pub(crate) const R:usize=4096;
pub(crate) const LIVE:usize=1383;
pub(crate) const TERMS:usize=6549;
fn power(e:usize)->BigUint{BigUint::from(1u8)<<e}
pub(crate) fn admit(d:&BigUint)->Result<(),String>{
    bounds(); // Field/ABI admission precedes every standalone statement/witness allocation.
    if d.is_zero()||d.bits()>224{return Err("positive D224".into());}
    if (d*3u8)>>1usize>power(64){return Err("dyadic profile coverage".into());}
    Ok(())
}
pub(crate) fn scalar(d:&BigUint)->Result<BigUint,String>{
    admit(d)?;let p=(d*3u8)>>1usize;
    (0usize..=64).map(power).find(|q|q>=&p).ok_or_else(||"dyadic profile coverage".into())
}
#[derive(Clone,Debug)]
pub(crate) struct Statement{ports:Vec<bool>,cap:Vec<bool>}
impl Statement{
    pub(crate) fn new(d:&BigUint,q:&BigUint)->Result<Self,String>{
        admit(d)?;
        if q.is_zero()||q> &power(64){return Err("public q profile".into());}
        Ok(Self{ports:(0..224).map(|i|d.bit(i)).collect(),cap:(0..65).map(|i|q.bit(i)).collect()})
    }
    pub(crate) fn bind(&self,t:&mut Transcript){
        t.append_bytes(b"elementary-cap-contract",b"q-of-native-D-local-projection-v1");
        for n in [M,R,TERMS,3008,3006,987674,224,1,0]{t.append_u64(b"elementary-cap-layout",n as u64);}
        for b in self.ports.iter().chain(&self.cap){t.append_u64(b"elementary-cap-bit",u64::from(*b));}
    }
}
#[derive(Clone,Debug)]
pub(crate) struct Layout{
    pub(crate) source:Range<usize>,pub(crate) operand:Range<usize>,pub(crate) p:Range<usize>,
    pub(crate) r:usize,pub(crate) s:Range<usize>,pub(crate) q:Range<usize>,
    pub(crate) prev:Range<usize>,pub(crate) hi:Range<usize>,pub(crate) low:Range<usize>,
    pub(crate) positive:Range<usize>,
}
impl Layout{
    pub(crate) fn new()->Self{
        let out=Self{source:1..225,operand:225..449,p:449..674,r:674,s:675..740,
            q:740..805,prev:805..869,hi:869..934,low:934..1159,positive:1159..1383};
        assert_eq!(out.positive.end,LIVE);out
    }
}
pub(crate) const GROUPS:[(&str,usize,usize);13]=[
    ("zero",1,1),("boolean",1382,2764),("input-anchors",224,448),("aliases",224,448),
    ("positive",1,449),("floor",1,450),("onehot",1,66),("q-rail",1,130),
    ("qprev-rail",1,128),("cover",1,355),("minimal",1,515),
    ("q-anchors",65,130),("padding",665,665)];
pub(crate) fn group(name:&str)->Range<usize>{
    let mut row=0;for (n,count,_) in GROUPS{if n==name{return row..row+count;}row+=count;}
    panic!("unknown group");
}
fn linear(w:usize,c:Fr)->Gate{Gate{left:w,right:0,c0:Fr::zero(),c1:c,c2:Fr::zero(),c3:Fr::zero()}}
fn constant(c:Fr)->Gate{Gate{left:0,right:0,c0:c,c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}}
fn bits(row:&mut Vec<Gate>,rail:Range<usize>,c:Fr){
    let mut weight=c;for w in rail{row.push(linear(w,weight));weight+=weight;}
}
struct Emitter<F:FnMut(Term)>{sink:F,row:usize,count:usize,group:usize,scratch:usize}
impl<F:FnMut(Term)> Emitter<F>{
    fn row(&mut self,gates:Vec<Gate>){
        assert!(gates.capacity()<=515,"row scratch capacity");
        self.scratch=self.scratch.max(gates.capacity());
        for gate in gates{assert!(gate.left<M&&gate.right<M);(self.sink)(Term{row:self.row,gate});self.count+=1;}
        self.row+=1;
    }
    fn end(&mut self){
        let rows=GROUPS[..=self.group].iter().map(|x|x.1).sum::<usize>();
        let terms=GROUPS[..=self.group].iter().map(|x|x.2).sum::<usize>();
        assert_eq!((self.row,self.count),(rows,terms),"group {}",GROUPS[self.group].0);self.group+=1;
    }
}
pub(crate) fn emit(stmt:&Statement,mut sink:impl FnMut(Term))->usize{
    assert_eq!((stmt.ports.len(),stmt.cap.len()),(224,65));
    let l=Layout::new();let one=Fr::one();
    let mut e=Emitter{sink:&mut sink,row:0,count:0,group:0,scratch:0};
    e.row(vec![linear(0,one)]);e.end();
    for w in 1..LIVE{e.row(vec![linear(w,-one),Gate{left:w,right:w,c0:Fr::zero(),c1:Fr::zero(),c2:Fr::zero(),c3:one}]);}e.end();
    for (i,b) in stmt.ports.iter().enumerate(){e.row(vec![linear(1+i,one),constant(-Fr::from(u64::from(*b)))]);}e.end();
    for i in 0..224{e.row(vec![linear(225+i,one),linear(1+i,-one)]);}e.end();
    let mut row=vec![constant(-one)];bits(&mut row,l.operand.clone(),one);bits(&mut row,l.positive.clone(),-one);e.row(row);e.end();
    let mut row=Vec::new();bits(&mut row,l.operand.clone(),Fr::from(3u64));bits(&mut row,l.p.clone(),-Fr::from(2u64));
    row.push(linear(l.r,-one));e.row(row);e.end();
    let mut row=vec![constant(-one)];for w in l.s.clone(){row.push(linear(w,one));}e.row(row);e.end();
    let mut row=Vec::new();bits(&mut row,l.q.clone(),one);bits(&mut row,l.s.clone(),-one);e.row(row);e.end();
    let mut row=Vec::new();bits(&mut row,l.prev.clone(),one);bits(&mut row,l.s.start+1..l.s.end,-one);e.row(row);e.end();
    let mut row=Vec::new();bits(&mut row,l.q.clone(),one);bits(&mut row,l.p.clone(),-one);bits(&mut row,l.hi.clone(),-one);e.row(row);e.end();
    let mut row=Vec::with_capacity(515);row.push(constant(-one));bits(&mut row,l.p.clone(),one);bits(&mut row,l.prev.clone(),-one);bits(&mut row,l.low.clone(),-one);e.row(row);e.end();
    for (i,b) in stmt.cap.iter().enumerate(){e.row(vec![linear(l.q.start+i,one),constant(-Fr::from(u64::from(*b)))]);}e.end();
    for w in LIVE..M{e.row(vec![linear(w,one)]);}e.end();
    assert_eq!((e.group,e.row,e.count,e.scratch),(13,2568,TERMS,515));e.scratch
}
pub(crate) fn bounds(){
    let modulus=BigUint::from_bytes_le(&Fr::MODULUS.to_bytes_le());
    let values=[power(226)-1u8,BigUint::from(64u8),power(65)-1u8,power(64)-1u8,
        power(225)+power(65)-2u8,power(225)+power(64)-1u8,power(224)];
    for n in values{assert!(n<modulus);}
    assert_eq!((std::mem::size_of::<Fr>(),std::mem::size_of::<Gate>(),std::mem::size_of::<Term>()),(32,144,152));
}
pub(crate) fn materialize(stmt:&Statement)->Circuit{
    bounds();let mut terms=Vec::with_capacity(TERMS);emit(stmt,|term|terms.push(term));
    assert_eq!((terms.len(),terms.capacity()),(TERMS,TERMS));
    let out=Circuit{input_len:M,row_count:R,terms};sparse::validate(&out,0).expect("elementary cap admission");out
}
pub(crate) fn put(x:&mut[Fr],rail:Range<usize>,value:&BigUint){
    assert!(value.bits()<=rail.len() as u64);
    for (i,w) in rail.enumerate(){x[w]=Fr::from(u64::from(value.bit(i as u64)));}
}
pub(crate) fn producer(d:&BigUint)->Result<Vec<Fr>,String>{
    admit(d)?;let l=Layout::new();let mut x=vec![Fr::zero();M];assert_eq!(x.capacity(),M);
    let p=(d*3u8)>>1usize;let r=(d*3u8)&BigUint::from(1u8);
    let q=scalar(d)?;let e=(0usize..=64).find(|e|power(*e)==q).unwrap();
    let prev=if e==0{BigUint::from(0u8)}else{power(e-1)};
    for rail in [l.source.clone(),l.operand.clone()]{put(&mut x,rail,d);}
    put(&mut x,l.p.clone(),&p);put(&mut x,l.r..l.r+1,&r);x[l.s.start+e]=Fr::one();
    put(&mut x,l.q.clone(),&q);put(&mut x,l.prev.clone(),&prev);
    put(&mut x,l.hi.clone(),&(&q-&p));put(&mut x,l.low.clone(),&(&p-&prev-1u8));
    put(&mut x,l.positive.clone(),&(d-1u8));Ok(x)
}
pub(crate) fn residuals(c:&Circuit,x:&[Fr])->Vec<Fr>{
    assert_eq!(x.len(),M);let mut out=vec![Fr::zero();R];
    for term in &c.terms{out[term.row]+=term.gate.evaluate(x);}out
}
pub(crate) fn eq_at(p:&[Fr],index:usize)->Fr{
    p.iter().enumerate().fold(Fr::one(),|a,(i,b)|a*if index>>i&1==1{*b}else{Fr::one()-b})
}
pub(crate) fn coefficients(stmt:&Statement,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],GkrError>{
    if (r.len(),u.len(),v.len())!=(12,11,11){return Err(GkrError::PointDimension);}
    let mut out=[Fr::zero();4];emit(stmt,|t|{
        let g=t.gate;let weight=eq_at(r,t.row)*eq_at(u,g.left)*eq_at(v,g.right);
        for (sum,c) in out.iter_mut().zip([g.c0,g.c1,g.c2,g.c3]){*sum+=weight*c;}
    });Ok(out)
}
fn authenticate_terms(stmt:&Statement,terms:&[Term])->Result<(),String>{
    if terms.len()!=TERMS{return Err("ordered tuple count".into());}
    let mut i=0;let mut equal=true;emit(stmt,|term|{equal &= terms[i]==term;i+=1;});
    if !equal{return Err("ordered tuple fields".into());}Ok(())
}

#[cfg(test)]
mod tests{
    use super::*;
    use ark_ff::Field;
    fn number(x:&[Fr],rail:Range<usize>)->BigUint{
        rail.enumerate().fold(BigUint::from(0u8),|a,(i,w)|{assert!(x[w].is_zero()||x[w].is_one());if x[w].is_one(){a+power(i)}else{a}})
    }
    fn positive(d:BigUint)->(Statement,Circuit,Vec<Fr>){
        let q=scalar(&d).unwrap();let stmt=Statement::new(&d,&q).unwrap();let c=materialize(&stmt);
        let x=producer(&d).unwrap();assert!(residuals(&c,&x).iter().all(Zero::is_zero));(stmt,c,x)
    }
    fn fail(c:&Circuit,x:&[Fr],name:&str){
        let residual=residuals(c,x);assert!(group(name).any(|row|!residual[row].is_zero()),"missing named failure {name}");
    }
    fn changed(c:&Circuit,x:&[Fr],wire:usize,name:&str){
        let mut bad=x.to_vec();bad[wire]=Fr::one()-bad[wire];fail(c,&bad,name);
    }
    #[test]
    fn exact_arithmetic_and_single_faults(){
        bounds();crate::certified_modern_cap_native::descriptor_faults();let l=Layout::new();
        for (d,p,q,r) in [(1u64,1u64,1u64,1u64),(3,4,4,1),(5,7,8,1),(6,9,16,0)]{
            let (_,_,x)=positive(BigUint::from(d));
            assert_eq!(number(&x,l.p.clone()),BigUint::from(p));assert_eq!(number(&x,l.q.clone()),BigUint::from(q));
            assert_eq!(x[l.r],Fr::from(r));
        }
        let max=(power(65)+1u8)/3u8;
        for d in [&max-1u8,max.clone()]{let (_,_,x)=positive(d);assert_eq!(number(&x,l.q.clone()),power(64));}
        let (_,_,top)=positive(max.clone());assert_eq!(number(&top,l.p.clone()),power(64));assert_eq!(top[l.r],Fr::one());
        assert!(admit(&(&max+1u8)).is_err());assert!(admit(&BigUint::from(0u8)).is_err());assert!(admit(&power(224)).is_err());
        let (_,c,x)=positive(BigUint::from(5u8));
        for (wire,name) in [(l.operand.start,"aliases"),(l.operand.end-1,"positive"),
            (l.p.start,"floor"),(l.p.end-1,"floor"),(l.r,"floor"),(l.s.start+3,"onehot"),
            (l.s.start+4,"onehot"),(l.q.start,"q-rail"),(l.q.end-1,"q-rail"),
            (l.prev.start,"qprev-rail"),(l.prev.end-1,"qprev-rail"),(l.hi.start,"cover"),
            (l.hi.end-1,"cover"),(l.low.start,"minimal"),(l.low.end-1,"minimal"),
            (l.positive.start,"positive"),(l.positive.end-1,"positive"),(LIVE,"padding")]{changed(&c,&x,wire,name);}
        let mut bad=x.clone();bad[l.p.start]=Fr::from(2u64);fail(&c,&bad,"boolean");
        bad=x.clone();bad[l.source.start]=Fr::from(2u64);fail(&c,&bad,"boolean");
        changed(&c,&x,l.source.start,"input-anchors");changed(&c,&x,l.q.start,"q-anchors");
        // One missing semantic predicate: nonminimal16 covers p7, but8 is already sufficient.
        bad=x.clone();bad[l.s.start+3]=Fr::zero();bad[l.s.start+4]=Fr::one();
        put(&mut bad,l.q.clone(),&BigUint::from(16u8));put(&mut bad,l.prev.clone(),&BigUint::from(8u8));
        put(&mut bad,l.hi.clone(),&BigUint::from(9u8));put(&mut bad,l.low.clone(),&BigUint::from(0u8));
        fail(&c,&bad,"minimal");
        let rows=residuals(&c,&bad);for n in ["positive","floor","onehot","q-rail","qprev-rail","cover"]{assert!(group(n).all(|row|rows[row].is_zero()));}
        // Independent zero-boundary witness: positivity and p>=1 are both impossible.
        let mut zero=vec![Fr::zero();M];zero[l.s.start]=Fr::one();
        put(&mut zero,l.q.clone(),&BigUint::from(1u8));put(&mut zero,l.hi.clone(),&BigUint::from(1u8));
        fail(&c,&zero,"positive");fail(&c,&zero,"minimal");
        let rows=residuals(&c,&zero);
        for n in ["zero","boolean","aliases","floor","onehot","q-rail","qprev-rail","cover","padding"]{
            assert!(group(n).all(|row|rows[row].is_zero()));
        }
        // Fixed public statement still names D5/q8; anchor failures are separate evidence.
        fail(&c,&zero,"input-anchors");fail(&c,&zero,"q-anchors");
        // Reconstruct every boundary rail independently; only the unsigned cover gap is impossible.
        let upper_stmt=Statement::new(&max,&power(64)).unwrap();let upper_c=materialize(&upper_stmt);
        let outside=&max+1u8;let three=&outside*3u8;let p=&three/2u8;let rem=&three%2u8;
        let q=power(64);let prev=power(63);let mut upper=vec![Fr::zero();M];
        for rail in [l.source.clone(),l.operand.clone()]{put(&mut upper,rail,&outside);}
        put(&mut upper,l.p.clone(),&p);put(&mut upper,l.r..l.r+1,&rem);upper[l.s.start+64]=Fr::one();
        put(&mut upper,l.q.clone(),&q);put(&mut upper,l.prev.clone(),&prev);
        put(&mut upper,l.low.clone(),&(&p-&prev-1u8));put(&mut upper,l.positive.clone(),&(&outside-1u8));
        // gapHi remains zero; q-p=-2, so cover rejects without a stale floor/positive helper.
        fail(&upper_c,&upper,"cover");let rows=residuals(&upper_c,&upper);
        for n in ["zero","boolean","aliases","floor","positive","onehot","q-rail","qprev-rail","minimal","q-anchors","padding"]{
            assert!(group(n).all(|row|rows[row].is_zero()));
        }
        fail(&upper_c,&upper,"input-anchors");
    }
    // Independent row generation uses powers and explicit Gate fields, never emit/Emitter/bits.
    fn literal(stmt:&Statement)->Vec<Term>{
        let mut out=Vec::with_capacity(TERMS);let mut index=0usize;
        let mono=|w:usize,channel:usize,c:Fr|{let mut a=[Fr::zero();4];a[channel]=c;
            Gate{left:w,right:if channel==3{w}else{0},c0:a[0],c1:a[1],c2:a[2],c3:a[3]}};
        let rail=|lo:usize,hi:usize,c:Fr|{(lo..hi).enumerate().map(|(i,w)|mono(w,1,c*Fr::from(2u64).pow([i as u64]))).collect::<Vec<_>>()};
        let mut row=|gates:Vec<Gate>|{assert!(gates.capacity()<=515,"literal row scratch capacity");for gate in gates{out.push(Term{row:index,gate});}index+=1;};
        row(vec![mono(0,1,Fr::one())]);
        for w in 1..1383{row(vec![mono(w,1,-Fr::one()),mono(w,3,Fr::one())]);}
        for i in 0..224{row(vec![mono(1+i,1,Fr::one()),mono(0,0,-Fr::from(u64::from(stmt.ports[i])))]);}
        for i in 0..224{row(vec![mono(225+i,1,Fr::one()),mono(1+i,1,-Fr::one())]);}
        let mut g=vec![mono(0,0,-Fr::one())];g.extend(rail(225,449,Fr::one()));g.extend(rail(1159,1383,-Fr::one()));row(g);
        let mut g=Vec::with_capacity(450);g.extend(rail(225,449,Fr::from(3u64)));g.extend(rail(449,674,-Fr::from(2u64)));g.push(mono(674,1,-Fr::one()));row(g);
        let mut g=vec![mono(0,0,-Fr::one())];for w in 675..740{g.push(mono(w,1,Fr::one()));}row(g);
        let mut g=rail(740,805,Fr::one());g.extend(rail(675,740,-Fr::one()));row(g);
        let mut g=rail(805,869,Fr::one());g.extend(rail(676,740,-Fr::one()));row(g);
        let mut g=Vec::with_capacity(355);g.extend(rail(740,805,Fr::one()));g.extend(rail(449,674,-Fr::one()));g.extend(rail(869,934,-Fr::one()));row(g);
        let mut g=Vec::with_capacity(515);g.push(mono(0,0,-Fr::one()));g.extend(rail(449,674,Fr::one()));g.extend(rail(805,869,-Fr::one()));g.extend(rail(934,1159,-Fr::one()));row(g);
        for i in 0..65{row(vec![mono(740+i,1,Fr::one()),mono(0,0,-Fr::from(u64::from(stmt.cap[i])))]);}
        for w in 1383..2048{row(vec![mono(w,1,Fr::one())]);}drop(row);
        assert_eq!((index,out.len(),out.capacity()),(2568,TERMS,TERMS));out
    }
    fn direct(terms:&[Term],r:&[Fr],u:&[Fr],v:&[Fr])->[Fr;4]{
        let mut out=[Fr::zero();4];for t in terms{let g=&t.gate;let w=eq_at(r,t.row)*eq_at(u,g.left)*eq_at(v,g.right);
            for (sum,c) in out.iter_mut().zip([g.c0,g.c1,g.c2,g.c3]){*sum+=w*c;}}out
    }
    fn point(n:usize,seed:u64)->Vec<Fr>{(0..n).map(|i|Fr::from(seed+3*i as u64)).collect()}
    #[test]
    fn literal_coefficients_and_admission(){
        bounds();let d=BigUint::from(5u8);let stmt=Statement::new(&d,&scalar(&d).unwrap()).unwrap();
        let c=materialize(&stmt);let mut literal=literal(&stmt);assert_eq!(c.terms,literal);
        let starts=[0usize,1,1383,1607,1831,1832,1833,1834,1835,1836,1837,1838,1903];
        for ((name,n,_),start) in GROUPS.into_iter().zip(starts){assert_eq!(group(name),start..start+n);}
        assert_eq!(sparse::validate(&c,0).unwrap().input_bits,11);
        let r=point(12,2);let u=point(11,7);let v=point(11,11);
        let wanted=coefficients(&stmt,&r,&u,&v).unwrap();assert_eq!(wanted,direct(&literal,&r,&u,&v));
        for seed in [17u64,31]{let rr=point(12,seed);let uu=point(11,seed+5);let vv=point(11,seed+9);
            assert_eq!(coefficients(&stmt,&rr,&uu,&vv).unwrap(),direct(&literal,&rr,&uu,&vv));}
        for channel in 0..4{
            let i=literal.iter().position(|t|![t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3][channel].is_zero()).unwrap_or(0);
            let saved=literal[i].clone();let g=&mut literal[i].gate;
            match channel{0=>g.c0+=Fr::one(),1=>g.c1+=Fr::one(),2=>g.c2+=Fr::one(),_=>g.c3+=Fr::one()}
            assert_eq!(authenticate_terms(&stmt,&literal).unwrap_err(),"ordered tuple fields");assert_ne!(direct(&literal,&r,&u,&v),wanted);literal[i]=saved;
        }
        for axis in 0..3{let saved=literal[0].clone();match axis{0=>literal[0].row+=1,1=>literal[0].gate.left+=1,_=>literal[0].gate.right+=1}
            assert_eq!(authenticate_terms(&stmt,&literal).unwrap_err(),"ordered tuple fields");assert_ne!(direct(&literal,&r,&u,&v),wanted);literal[0]=saved;}
        literal.swap(0,1);assert_eq!(authenticate_terms(&stmt,&literal).unwrap_err(),"ordered tuple fields");assert_eq!(direct(&literal,&r,&u,&v),wanted);literal.swap(0,1);
        let boolean=|n:usize,i:usize|(0..n).map(|b|Fr::from(((i>>b)&1)as u64)).collect::<Vec<_>>();
        for index in [0usize,TERMS-1]{let t=&literal[index];let rr=boolean(12,t.row);let uu=boolean(11,t.gate.left);let vv=boolean(11,t.gate.right);
            assert_eq!(coefficients(&stmt,&rr,&uu,&vv).unwrap(),direct(&literal,&rr,&uu,&vv));}
        for axis in 0..3{let (rr,uu,vv)=match axis{0=>(&r[..11],u.as_slice(),v.as_slice()),1=>(r.as_slice(),&u[..10],v.as_slice()),_=>(r.as_slice(),u.as_slice(),&v[..10])};
            assert_eq!(coefficients(&stmt,rr,uu,vv),Err(GkrError::PointDimension));}
        assert_eq!(authenticate_terms(&stmt,&literal[..TERMS-1]).unwrap_err(),"ordered tuple count");drop(literal);
        for axis in 0..3{let mut bad=c.clone();match axis{0=>bad.terms[0].row=R,1=>bad.terms[0].gate.left=M,_=>bad.terms[0].gate.right=M}
            assert!(matches!(sparse::validate(&bad,0),Err(GkrError::InvalidWireIndex)));}
        let mut bad=c.clone();bad.input_len=1usize<<25usize;assert!(matches!(sparse::validate(&bad,0),Err(GkrError::RepeatedSizeLimit)));
        bad.input_len=M;bad.row_count=3;assert!(sparse::validate(&bad,0).is_err());
        let d2=BigUint::from(6u8);let other=materialize(&Statement::new(&d2,&scalar(&d2).unwrap()).unwrap());
        assert_eq!(c.terms.len(),other.terms.len());for (a,b) in c.terms.iter().zip(&other.terms){assert_eq!((a.row,a.gate.left,a.gate.right),(b.row,b.gate.left,b.gate.right));}
    }
}


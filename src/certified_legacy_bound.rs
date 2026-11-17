//! TEST-only local ell=2 relation. Projected ports have no historical PCS authentication.
use ark_bn254::Fr;
use ark_ff::{BigInteger, One, PrimeField, Zero};
use num_bigint::BigUint;
use num_traits::ToPrimitive;
use std::ops::Range;
use crate::{gkr::{Gate, GkrError}, sparse::{self, Circuit, Term}, transcript::Transcript};

pub(crate) const M: usize = 8192;
pub(crate) const R: usize = 16384;
pub(crate) const LIVE: usize = 5936;
pub(crate) const TERMS: usize = 59952;
pub(crate) const MULT: u64 = 122880000;
pub(crate) const INITIAL: u64 = 0x011765000000;

#[derive(Clone, Debug)]
pub(crate) struct Inputs {
    pub(crate) d: [BigUint; 2],
    pub(crate) t: [u64; 3],
}
impl Inputs {
    pub(crate) fn admit(&self) -> Result<(), String> {
        if self.d.iter().any(|x| x.bits() > 224) { return Err("D224 overflow".into()); }
        if self.t.iter().any(|x| *x > i64::MAX as u64)
            || !(self.t[0] < self.t[1] && self.t[1] < self.t[2]) {
            return Err("selected timestamp domain/order".into());
        }
        (self.t[2]-self.t[1]).checked_add(64).ok_or("future denominator overflow")?;
        Ok(())
    }
    pub(crate) fn ports(&self) -> Vec<bool> {
        let mut out = Vec::with_capacity(640);
        for d in &self.d { for i in 0..224 { out.push(d.bit(i)); } }
        for t in self.t { for i in 0..64 { out.push(t >> i & 1 == 1); } }
        out
    }
}

#[derive(Clone, Debug)]
pub(crate) struct Statement { ports: Vec<bool>, bound: Vec<bool> }
impl Statement {
    pub(crate) fn new(input: &Inputs, b: &BigUint) -> Result<Self,String> {
        input.admit()?;
        if b.bits()>253 {return Err("B253 overflow".into());}
        Ok(Self { ports:input.ports(), bound:(0..253).map(|i|b.bit(i)).collect() })
    }
    pub(crate) fn bind(&self, t: &mut Transcript) {
        t.append_bytes(b"ell2-contract", b"legacy-j3072-a3008-local-projection-v1");
        t.append_u64(b"ell2-M", M as u64);
        t.append_u64(b"ell2-R", R as u64);
        t.append_u64(b"ell2-T", TERMS as u64);
        for bit in self.ports.iter().chain(&self.bound) { t.append_u64(b"ell2-public-bit", u64::from(*bit)); }
        for (height,owner,base,width) in [(2048u64,2046u64,987674u64,224u64),
            (3008,3006,987674,224),(1024,1023,525330,64),(2048,2047,525330,64),(3008,3007,525330,64)] {
            for v in [height,owner,base,width] {t.append_u64(b"ell2-projection",v);}
        }
    }
}
#[derive(Clone, Debug)]
pub(crate) struct Sub { pub(crate) initial:usize, pub(crate) diff:Range<usize>, pub(crate) borrow:Range<usize> }
impl Sub { fn allocate(cursor:&mut usize,w:usize)->Self {
    let initial=*cursor; *cursor+=1;
    Self{initial,diff:take(cursor,w),borrow:take(cursor,w)}
} }
#[derive(Clone,Debug)]
pub(crate) struct Layout {
    pub(crate) source:Range<usize>, pub(crate) operand:Range<usize>,
    pub(crate) delta:[Range<usize>;3], pub(crate) tc:[Range<usize>;3],
    pub(crate) positive:[Sub;2], pub(crate) numerator:[Range<usize>;2],
    pub(crate) nc:[Range<usize>;2], pub(crate) q:[Range<usize>;2],
    pub(crate) rem:[Range<usize>;2], pub(crate) pc:[Range<usize>;2],
    pub(crate) rem_sub:[Sub;2], pub(crate) a:Range<usize>, pub(crate) c:Range<usize>,
    pub(crate) ac:[Range<usize>;2], pub(crate) compare:Sub, pub(crate) selector:usize,
    pub(crate) b:Range<usize>, pub(crate) selected:Range<usize>,
}
fn take(cursor:&mut usize,n:usize)->Range<usize>{let lo=*cursor;*cursor+=n;lo..*cursor}
impl Layout {
    pub(crate) fn new()->Self {
        let mut p=1;
        let source=take(&mut p,640);let operand=take(&mut p,640);
        let delta=std::array::from_fn(|_|take(&mut p,64));
        let tc=std::array::from_fn(|_|take(&mut p,3));
        let positive=std::array::from_fn(|_|Sub::allocate(&mut p,64));
        let numerator=std::array::from_fn(|_|take(&mut p,251));
        let nc=std::array::from_fn(|_|take(&mut p,15*27));
        let mut q:[Range<usize>;2]=std::array::from_fn(|_|0..0);
        let mut rem=q.clone();let mut pc=q.clone();
        for k in 0..2 {q[k]=take(&mut p,251);rem[k]=take(&mut p,64);pc[k]=take(&mut p,18*19);}
        let rem_sub=std::array::from_fn(|_|Sub::allocate(&mut p,64));
        let a=take(&mut p,253);let c=take(&mut p,253);
        let ac=std::array::from_fn(|_|take(&mut p,15));
        let compare=Sub::allocate(&mut p,253);let selector=p;p+=1;
        let b=take(&mut p,253);let selected=take(&mut p,15);
        assert_eq!(p,LIVE);
        Self{source,operand,delta,tc,positive,numerator,nc,q,rem,pc,rem_sub,a,c,ac,compare,selector,b,selected}
    }
    pub(crate) fn d(&self,k:usize)->Range<usize>{self.operand.start+224*k..self.operand.start+224*(k+1)}
    pub(crate) fn time(&self,k:usize)->Range<usize>{self.operand.start+448+64*k..self.operand.start+448+64*(k+1)}
}
pub(crate) const GROUPS:[(&str,usize,usize);26]=[
    ("zero",1,1),("input-boolean",1280,2560),("input-anchors",640,1280),("aliases",640,1280),
    ("time-sign",3,3),("delta-boolean",192,384),("time-carry-boolean",9,18),("time-columns",12,542),
    ("positive",390,1160),("numerator-boolean",502,1004),("numerator-carry-boolean",810,1620),
    ("numerator-columns",32,2602),("product-boolean",1314,2628),("product-columns",38,34126),
    ("remainder-bound",390,1160),("ac-boolean",536,1072),("ac-columns",32,1100),
    ("comparison",761,2280),("selector",2,5),("b-boolean",253,506),
    ("selected-carry-boolean",15,30),("selected-columns",16,787),("inactive-carry",15,30),
    ("fallback",253,1012),("b-anchors",253,506),("padding",2256,2256)];
pub(crate) fn group(name:&str)->Range<usize>{
    let mut row=0;for (n,count,_) in GROUPS {if n==name{return row..row+count;}row+=count;}
    panic!("unknown group");
}
fn linear(w:usize,c:Fr)->Gate{Gate{left:w,right:0,c0:Fr::zero(),c1:c,c2:Fr::zero(),c3:Fr::zero()}}
fn constant(c:Fr)->Gate{Gate{left:0,right:0,c0:c,c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}}
fn product(l:usize,r:usize,c:Fr)->Gate{Gate{left:l,right:r,c0:Fr::zero(),c1:Fr::zero(),c2:Fr::zero(),c3:c}}
fn add_bits(row:&mut Vec<Gate>,range:Range<usize>,limb:usize,c:Fr){
    for (i,w) in range.enumerate().skip(limb*16).take(16){row.push(linear(w,c*Fr::from(1u64<<(i%16))));}
}
fn add_full(row:&mut Vec<Gate>,range:Range<usize>,c:Fr){
    for (i,w) in range.enumerate(){row.push(linear(w,c*Fr::from(1u64<<i)));}
}
fn carry(range:&Range<usize>,col:usize,width:usize,columns:usize)->Range<usize>{
    if col==0||col>=columns {0..0}else{range.start+(col-1)*width..range.start+col*width}
}
struct Emitter<F:FnMut(Term)> {sink:F,row:usize,count:usize,group:usize,max_scratch:usize}
impl<F:FnMut(Term)> Emitter<F>{
    fn row(&mut self,gates:Vec<Gate>){
        self.max_scratch=self.max_scratch.max(gates.len());
        for gate in gates {assert!(gate.left<M&&gate.right<M);(self.sink)(Term{row:self.row,gate});self.count+=1;}
        self.row+=1;
    }
    fn booleans(&mut self,bits:Range<usize>){for w in bits{self.row(vec![linear(w,-Fr::one()),product(w,w,Fr::one())]);}}
    fn end(&mut self){
        let rows:usize=GROUPS[..=self.group].iter().map(|x|x.1).sum();
        let terms:usize=GROUPS[..=self.group].iter().map(|x|x.2).sum();
        assert_eq!((self.row,self.count),(rows,terms),"group {}",GROUPS[self.group].0);self.group+=1;
    }
    fn strict(&mut self,x:Range<usize>,y:Range<usize>,s:&Sub,final_zero:bool){
        self.booleans(s.initial..s.initial+1);
        let mut anchor=linear(s.initial,Fr::one());anchor.c0=-Fr::one();self.row(vec![anchor]);
        let mut prev=s.initial;
        for i in 0..x.len(){
            let dw=s.diff.start+i;let bw=s.borrow.start+i;
            self.booleans(dw..dw+1);self.booleans(bw..bw+1);
            self.row(vec![linear(x.start+i,Fr::one()),linear(if i<y.len(){y.start+i}else{0},-Fr::one()),
                linear(prev,-Fr::one()),linear(dw,-Fr::one()),linear(bw,Fr::from(2u64))]);prev=bw;
        }
        if final_zero{self.row(vec![linear(prev,Fr::one())]);}
    }
}
pub(crate) fn emit(stmt:&Statement,mut sink:impl FnMut(Term))->usize{
    assert_eq!((stmt.ports.len(),stmt.bound.len()),(640,253));
    let l=Layout::new();let one=Fr::one();let radix=Fr::from(65536u64);
    let mut e=Emitter{sink:&mut sink,row:0,count:0,group:0,max_scratch:0};
    e.row(vec![linear(0,one)]);e.end();
    e.booleans(1..1281);e.end();
    for (i,b) in stmt.ports.iter().enumerate(){e.row(vec![linear(l.source.start+i,one),constant(-Fr::from(u64::from(*b)))]);}e.end();
    for i in 0..640 {e.row(vec![linear(l.operand.start+i,one),linear(l.source.start+i,-one)]);}e.end();
    for k in 0..3{e.row(vec![linear(l.time(k).end-1,one)]);}e.end();
    for r in &l.delta{e.booleans(r.clone());}e.end();
    for r in &l.tc{e.booleans(r.clone());}e.end();
    for k in 0..3{for j in 0..4{
        let mut row=vec![constant(if k==2&&j==0{Fr::from(64u64)}else{Fr::zero()})];
        if k<2{add_bits(&mut row,l.delta[k].clone(),j,one);add_bits(&mut row,l.time(k),j,one);add_bits(&mut row,l.time(k+1),j,-one);}
        else{add_bits(&mut row,l.delta[1].clone(),j,one);add_bits(&mut row,l.delta[2].clone(),j,-one);}
        add_full(&mut row,carry(&l.tc[k],j,1,4),one);
        add_full(&mut row,carry(&l.tc[k],j+1,1,4),-radix);e.row(row);
    }}e.end();
    for k in 0..2{e.strict(l.delta[k].clone(),0..0,&l.positive[k],true);}e.end();
    for r in &l.numerator{e.booleans(r.clone());}e.end();
    for r in &l.nc{e.booleans(r.clone());}e.end();
    for k in 0..2{for j in 0..16{
        let mut row=vec![constant(Fr::zero())];add_bits(&mut row,l.d(k),j,Fr::from(MULT));
        add_full(&mut row,carry(&l.nc[k],j,27,16),one);add_bits(&mut row,l.numerator[k].clone(),j,-one);
        add_full(&mut row,carry(&l.nc[k],j+1,27,16),-radix);e.row(row);
    }}e.end();
    for k in 0..2{e.booleans(l.q[k].clone());e.booleans(l.rem[k].clone());e.booleans(l.pc[k].clone());}e.end();
    for k in 0..2{let denominator=&l.delta[if k==0{0}else{2}];for col in 0..19{
        let mut row=Vec::with_capacity(1094);
        add_full(&mut row,carry(&l.pc[k],col,19,19),one);
        add_bits(&mut row,l.rem[k].clone(),col,one);add_bits(&mut row,l.numerator[k].clone(),col,-one);
        for qi in 0..16{if col>=qi&&col-qi<4{
            let di=col-qi;
            for x in 0..16{if qi*16+x<251{for y in 0..16{
                row.push(product(l.q[k].start+qi*16+x,denominator.start+di*16+y,Fr::from(1u64<<(x+y))));
            }}}
        }}
        add_full(&mut row,carry(&l.pc[k],col+1,19,19),-radix);e.row(row);
    }}e.end();
    for k in 0..2{e.strict(l.delta[if k==0{0}else{2}].clone(),l.rem[k].clone(),&l.rem_sub[k],true);}e.end();
    e.booleans(l.a.clone());e.booleans(l.c.clone());for r in &l.ac{e.booleans(r.clone());}e.end();
    for k in 0..2{for j in 0..16{
        let mut row=vec![constant(if k==0&&j==0{Fr::from(3u64)}else if k==1{Fr::from(if j<4{(INITIAL>>(j*16))&65535}else{0})}else{Fr::zero()})];
        if k==0{
            // Shift bit positions BEFORE assigning limbs; retain every one of251 source bits.
            for i in 0..251{if (i+1)/16==j{row.push(linear(l.q[1].start+i,Fr::from(1u64<<((i+1)%16))));}}
        }else{add_bits(&mut row,l.q[0].clone(),j,one);}
        add_full(&mut row,carry(&l.ac[k],j,1,16),one);
        add_bits(&mut row,if k==0{l.a.clone()}else{l.c.clone()},j,-one);
        add_full(&mut row,carry(&l.ac[k],j+1,1,16),-radix);e.row(row);
    }}e.end();
    e.strict(l.a.clone(),l.c.clone(),&l.compare,false);e.end();
    e.booleans(l.selector..l.selector+1);
    e.row(vec![linear(l.selector,one),linear(l.compare.borrow.end-1,one),constant(-one)]);e.end();
    e.booleans(l.b.clone());e.end();
    e.booleans(l.selected.clone());e.end();
    for j in 0..16{
        let mut row=Vec::new();add_bits(&mut row,l.b.clone(),j,one);add_bits(&mut row,l.q[0].clone(),j,one);
        add_bits(&mut row,l.a.clone(),j,-one);add_full(&mut row,carry(&l.selected,j,1,16),one);
        add_full(&mut row,carry(&l.selected,j+1,1,16),-radix);
        e.row(row.into_iter().map(|g|product(l.selector,g.left,g.c1)).collect());
    }e.end();
    for w in l.selected.clone(){e.row(vec![linear(w,one),product(l.selector,w,-one)]);}e.end();
    for (i,w) in l.b.clone().enumerate(){
        let bit=Fr::from(if i<64{(INITIAL>>i)&1}else{0});
        // (1-s)*(B_i-I_i), including its retained zero constant.
        e.row(vec![linear(w,one),constant(-bit),product(l.selector,w,-one),linear(l.selector,bit)]);
    }e.end();
    for (i,b) in stmt.bound.iter().enumerate(){e.row(vec![linear(l.b.start+i,one),constant(-Fr::from(u64::from(*b)))]);}e.end();
    for w in LIVE..M{e.row(vec![linear(w,one)]);}e.end();
    assert_eq!((e.group,e.row,e.count),(GROUPS.len(),10645,TERMS));assert_eq!(e.max_scratch,1094);
    e.max_scratch
}
fn authenticate_terms(stmt:&Statement,terms:&[Term])->Result<(),String>{
    if terms.len()!=TERMS{return Err("ordered tuple count".into());}
    let mut position=0usize;let mut equal=true;
    emit(stmt,|term|{equal &= terms[position]==term;position+=1;});
    if !equal{return Err("ordered tuple fields".into());}Ok(())
}
pub(crate) fn materialize(stmt:&Statement)->Circuit{
    bounds(); // Integer residual envelopes and field/ABI admission precede allocation.
    let mut terms=Vec::with_capacity(TERMS);emit(stmt,|t|terms.push(t));
    assert_eq!((terms.len(),terms.capacity()),(TERMS,TERMS));
    let c=Circuit{input_len:M,row_count:R,terms};
    sparse::validate(&c,0).expect("fixed ell2 admission");c
}
pub(crate) fn scalar(input:&Inputs)->Result<BigUint,String>{
    input.admit()?;let n0=&input.d[0]*BigUint::from(MULT);let n1=&input.d[1]*BigUint::from(MULT);
    let y1=n0/BigUint::from(input.t[1]-input.t[0]);
    let ymax=n1/BigUint::from(input.t[2]-input.t[1]+64);
    let a=(ymax<<1usize)+BigUint::from(3u8);let c=&y1+BigUint::from(INITIAL);
    Ok(if a>c{a-y1}else{BigUint::from(INITIAL)})
}
fn put(x:&mut[Fr],range:Range<usize>,value:&BigUint){
    assert!(value.bits()<=range.len() as u64);for (i,w) in range.enumerate(){x[w]=Fr::from(u64::from(value.bit(i as u64)));}
}
fn number(x:&[Fr],range:Range<usize>)->BigUint{
    let mut out=BigUint::from(0u8);for (i,w) in range.enumerate(){assert!(x[w]==Fr::zero()||x[w]==Fr::one());if x[w]==Fr::one(){out|=BigUint::from(1u8)<<i;}}out
}
fn limb(x:&[Fr],range:Range<usize>,j:usize)->u64{
    range.enumerate().skip(j*16).take(16).map(|(i,w)|if x[w]==Fr::one(){1u64<<(i%16)}else{0}).sum()
}
fn ordinary_carries(x:&mut[Fr],left:Range<usize>,right:Range<usize>,constant:u64,out:Range<usize>){
    let mut c=0u64;
    for j in 0..16{let k=if j<4{(constant>>(j*16))&65535}else{0};
        c=(limb(x,left.clone(),j)+limb(x,right.clone(),j)+k+c)>>16;
        assert!(c<=1);if j<15{x[out.start+j]=Fr::from(c);}else{assert_eq!(c,0);}
    }
}
fn sub_assign(x:&mut[Fr],a:Range<usize>,b:Range<usize>,s:&Sub){
    x[s.initial]=Fr::one();let mut borrow=1i64;
    for i in 0..a.len(){let av=if x[a.start+i]==Fr::one(){1}else{0};let bv=if i<b.len()&&x[b.start+i]==Fr::one(){1}else{0};
        let raw=av-bv-borrow;let next=i64::from(raw<0);let diff=raw+2*next;
        x[s.diff.start+i]=Fr::from(diff as u64);x[s.borrow.start+i]=Fr::from(next as u64);borrow=next;
    }
}
pub(crate) fn producer(input:&Inputs,b:&BigUint)->Result<Vec<Fr>,String>{
    input.admit()?;let l=Layout::new();let mut x=vec![Fr::zero();M];assert_eq!(x.capacity(),M);
    for (i,bit) in input.ports().into_iter().enumerate(){let f=Fr::from(u64::from(bit));x[l.source.start+i]=f;x[l.operand.start+i]=f;}
    let ds=[input.t[1]-input.t[0],input.t[2]-input.t[1],input.t[2]-input.t[1]+64];
    for k in 0..3{put(&mut x,l.delta[k].clone(),&BigUint::from(ds[k]));}
    for k in 0..3{let mut c=0u64;for j in 0..4{
        let sum=if k<2{limb(&x,l.delta[k].clone(),j)+limb(&x,l.time(k),j)+c}else{
            limb(&x,l.delta[1].clone(),j)+(if j==0{64}else{0})+c};
        c=sum>>16;if j<3{x[l.tc[k].start+j]=Fr::from(c);}else{assert_eq!(c,0);}
    }}
    for k in 0..2{sub_assign(&mut x,l.delta[k].clone(),0..0,&l.positive[k]);}
    for k in 0..2{
        let n=&input.d[k]*BigUint::from(MULT);put(&mut x,l.numerator[k].clone(),&n);
        let mut c=0u64;for j in 0..16{c=(MULT*limb(&x,l.d(k),j)+c)>>16;
            if j<15{put(&mut x,carry(&l.nc[k],j+1,27,16),&BigUint::from(c));}else{assert_eq!(c,0);}}
        let den=BigUint::from(ds[if k==0{0}else{2}]);let q=&n/&den;let r=&n%&den;
        put(&mut x,l.q[k].clone(),&q);put(&mut x,l.rem[k].clone(),&r);
        let mut c=0u64;for col in 0..19{
            let mut sum=c+limb(&x,l.rem[k].clone(),col);
            for qi in 0..16{if col>=qi&&col-qi<4{sum+=limb(&x,l.q[k].clone(),qi)*limb(&x,l.delta[if k==0{0}else{2}].clone(),col-qi);}}
            c=sum>>16;if col<18{put(&mut x,carry(&l.pc[k],col+1,19,19),&BigUint::from(c));}else{assert_eq!(c,0);}
        }
        sub_assign(&mut x,l.delta[if k==0{0}else{2}].clone(),l.rem[k].clone(),&l.rem_sub[k]);
    }
    let ymax=number(&x,l.q[1].clone());let y1=number(&x,l.q[0].clone());
    let av=(&ymax<<1usize)+BigUint::from(3u8);let cv=&y1+BigUint::from(INITIAL);
    put(&mut x,l.a.clone(),&av);put(&mut x,l.c.clone(),&cv);
    // Shifted source rail is partitioned first; its carries are Boolean.
    let shifted=&ymax<<1usize;let mut c=0u64;for j in 0..16{
        let low=((&shifted>>(16usize*j))&BigUint::from(65535u64)).to_u64().unwrap();
        c=(low+(if j==0{3}else{0})+c)>>16;assert!(c<=1);if j<15{x[l.ac[0].start+j]=Fr::from(c);}else{assert_eq!(c,0);}
    }
    ordinary_carries(&mut x,l.q[0].clone(),0..0,INITIAL,l.ac[1].clone());
    sub_assign(&mut x,l.a.clone(),l.c.clone(),&l.compare);
    let selected=av>cv;x[l.selector]=Fr::from(u64::from(selected));put(&mut x,l.b.clone(),b);
    if selected{ordinary_carries(&mut x,l.b.clone(),l.q[0].clone(),0,l.selected.clone());}
    Ok(x)
}
pub(crate) fn residuals(c:&Circuit,x:&[Fr])->Vec<Fr>{
    assert_eq!(x.len(),M);let mut out=vec![Fr::zero();R];for t in &c.terms{out[t.row]+=t.gate.evaluate(x);}out
}
pub(crate) fn eq_at(point:&[Fr],index:usize)->Fr{
    point.iter().enumerate().fold(Fr::one(),|acc,(i,x)|acc*if index>>i&1==1{*x}else{Fr::one()-x})
}
pub(crate) fn coefficients(stmt:&Statement,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],GkrError>{
    if (r.len(),u.len(),v.len())!=(14,13,13){return Err(GkrError::PointDimension);}
    let mut out=[Fr::zero();4];emit(stmt,|t|{
        let g=t.gate;let w=eq_at(r,t.row)*eq_at(u,g.left)*eq_at(v,g.right);
        for (o,c) in out.iter_mut().zip([g.c0,g.c1,g.c2,g.c3]){*o+=w*c;}
    });Ok(out)
}
pub(crate) fn bounds(){
    let p=BigUint::from_bytes_le(&Fr::MODULUS.to_bytes_le());
    assert!((BigUint::from(1u8)<<253usize)<p);
    // Absolute residual envelopes, including Boolean carry ranges, are below p.
    let product_abs=4u128*65535*65535+((1u128<<19)-1)*(65536+1)+2*65535;
    let constant_abs=(MULT as u128)*65535+((1u128<<27)-1)*(65536+1)+65535;
    let addition_abs=3u128*65535+65536+1;
    for (bound,bits) in [(product_abs,36usize),(constant_abs,44),(addition_abs,18),(6,4)] {
        assert!(bound<(1u128<<bits));assert!(BigUint::from(bound)<p);
    }
    assert_eq!((std::mem::size_of::<Fr>(),std::mem::size_of::<Gate>(),std::mem::size_of::<Term>()),(32,144,152));
}

#[cfg(test)]
mod tests {
    use super::*;
    fn fixture(d0:u64,d1:u64,step:u64)->Inputs{Inputs{d:[BigUint::from(d0),BigUint::from(d1)],t:[0,step,step+step]}}
    fn flip(x:&mut[Fr],w:usize){x[w]=Fr::one()-x[w];}
    fn fail(c:&Circuit,x:&[Fr],name:&str){
        let rows=residuals(c,x);assert!(group(name).any(|r|!rows[r].is_zero()),"missing named failure {name}");
    }
    fn changed(c:&Circuit,x:&[Fr],wire:usize,name:&str){
        let mut y=x.to_vec();flip(&mut y,wire);fail(c,&y,name);
    }
    fn positive(input:Inputs)->(Statement,Circuit,Vec<Fr>){
        let b=scalar(&input).unwrap();let stmt=Statement::new(&input,&b).unwrap();
        let c=materialize(&stmt);let x=producer(&input,&b).unwrap();
        assert!(residuals(&c,&x).iter().all(Zero::is_zero));(stmt,c,x)
    }
    #[test]
    fn ell2_exact_arithmetic_and_single_faults(){
        bounds();crate::certified_legacy_bound_native::descriptor_faults();let l=Layout::new();
        // Raw prediction below0, belowI, equalI, aboveI; divisions with/without remainders.
        for input in [fixture(1000,1,MULT),fixture(1,1,MULT),fixture(1,INITIAL,MULT),
            fixture(1,INITIAL*2,MULT),fixture(17,29,17),fixture(0,0,1),
            Inputs{d:[BigUint::from(3u8),BigUint::from(INITIAL/2)],t:[0,MULT,2*MULT-64]}] {
            let (_,c,x)=positive(input.clone());let b=number(&x,l.b.clone());
            assert_eq!(b,scalar(&input).unwrap());
            for k in 0..2{
                assert_eq!(number(&x,l.numerator[k].clone()),&input.d[k]*BigUint::from(MULT));
                let den=number(&x,l.delta[if k==0{0}else{2}].clone());
                assert_eq!(number(&x,l.q[k].clone())*&den+number(&x,l.rem[k].clone()),number(&x,l.numerator[k].clone()));
                assert!(number(&x,l.rem[k].clone())<den);
            }
        }
        // Choose exact q values with delta_star=MULT and delta1=MULT-64.
        for y in [65534u64,65535,65536,65537,32766,32767,32768,(1u64<<32)-1] {
            let input=Inputs{d:[BigUint::from(1u8),BigUint::from(y)],t:[0,MULT-64,2*(MULT-64)]};
            let (_,c,x)=positive(input);
            assert_eq!(number(&x,l.q[1].clone()),BigUint::from(y));
            assert_eq!(number(&x,l.a.clone()),BigUint::from(y)*2u8+3u8);
            let shifted=BigUint::from(y)<<1usize;let mut carry=0u64;
            for j in 0..16{
                let low=((&shifted>>(16usize*j))&BigUint::from(65535u64)).to_u64().unwrap();
                carry=(low+(if j==0{3}else{0})+carry)>>16;
                if j<15{assert_eq!(x[l.ac[0].start+j],Fr::from(carry));}else{assert_eq!(carry,0);}
            }
            assert!(residuals(&c,&x).iter().all(Zero::is_zero));
        }
        // Maximum shifted rail cannot be obtained fromD224 in this fixed multiplier profile:
        // isolate the exact A-column group with independently assigned q/A/carry rails.
        let (_,c,mut x)=positive(fixture(1,1,1));
        let ymax=(BigUint::from(1u8)<<251usize)-BigUint::from(1u8);
        put(&mut x,l.q[1].clone(),&ymax);put(&mut x,l.a.clone(),&((&ymax<<1usize)+BigUint::from(3u8)));
        let mut carry=0u64;let shifted=&ymax<<1usize;
        for j in 0..16{
            let low=((&shifted>>(16usize*j))&BigUint::from(65535u64)).to_u64().unwrap();
            carry=(low+(if j==0{3}else{0})+carry)>>16;
            if j<15{x[l.ac[0].start+j]=Fr::from(carry);}else{assert_eq!(carry,0);}
        }
        let rows=residuals(&c,&x);
        assert!(group("ac-columns").take(16).all(|r|rows[r].is_zero()));
        drop(rows);drop(c);drop(x);
        let input=fixture(17,29,17);let (_,c,x)=positive(input);
        // Statement and circuit never change. Each single field mutation fails its own group,
        // before any proof/output-anchor/known-X check can mask missing arithmetic.
        for k in 0..2 {
            changed(&c,&x,l.numerator[k].start,"numerator-columns");
            changed(&c,&x,l.q[k].start,"product-columns");
            changed(&c,&x,l.q[k].end-1,"product-columns");
            changed(&c,&x,l.rem[k].start,"product-columns");
            changed(&c,&x,l.nc[k].start,"numerator-columns");
            changed(&c,&x,l.pc[k].start,"product-columns");
            changed(&c,&x,l.rem_sub[k].borrow.start,"remainder-bound");
        }
        for k in 0..3 {
            changed(&c,&x,l.delta[k].start,"time-columns");
            changed(&c,&x,l.tc[k].start,"time-columns");
        }
        for k in 0..2 {
            let mut y=x.clone();put(&mut y,l.delta[k].clone(),&BigUint::from(0u8));fail(&c,&y,"positive");drop(y);
            changed(&c,&x,l.ac[k].start,"ac-columns");
            let mut y=x.clone();put(&mut y,l.rem[k].clone(),&number(&x,l.delta[if k==0{0}else{2}].clone()));
            fail(&c,&y,"remainder-bound");drop(y);
        }
        let mut y=x.clone();put(&mut y,l.delta[2].clone(),&BigUint::from(0u8));fail(&c,&y,"time-columns");drop(y);
        changed(&c,&x,l.operand.start,"aliases");changed(&c,&x,l.selector,"selector");
        changed(&c,&x,LIVE,"padding");
        changed(&c,&x,l.compare.borrow.start,"comparison");
        let mut y=x.clone();y[l.numerator[0].start]=Fr::from(2u64);fail(&c,&y,"numerator-boolean");drop(y);
        let mut y=x.clone();y[l.time(0).end-1]=Fr::one();fail(&c,&y,"time-sign");drop(y);
        let mut y=x.clone();y[l.delta[2].end-1]=Fr::one();fail(&c,&y,"time-columns");drop(y);
        assert_eq!(x[l.selector],Fr::zero());
        changed(&c,&x,l.b.start,"fallback");changed(&c,&x,l.selected.start,"inactive-carry");
        drop(c);drop(x);
        let (_,active_c,active_x)=positive(fixture(1,INITIAL*2,17));
        assert_eq!(active_x[l.selector],Fr::one());
        changed(&active_c,&active_x,l.selected.start,"selected-columns");
        changed(&active_c,&active_x,l.b.start,"b-anchors");
        // Exact comparator tie is an isolated valid subrelation, with fixed statement untouched.
        let mut tie=active_x.clone();let v=BigUint::from(INITIAL);
        put(&mut tie,l.a.clone(),&v);put(&mut tie,l.c.clone(),&v);
        sub_assign(&mut tie,l.a.clone(),l.c.clone(),&l.compare);tie[l.selector]=Fr::zero();
        let tie_rows=residuals(&active_c,&tie);
        assert!(group("comparison").chain(group("selector")).all(|r|tie_rows[r].is_zero()));
        let mut bad=fixture(1,1,1);bad.t=[2,1,3];assert!(bad.admit().is_err());
        bad.t=[0,1,i64::MAX as u64+1];assert!(bad.admit().is_err());
        bad=fixture(1,1,1);bad.d[0]=BigUint::from(1u8)<<224usize;assert!(bad.admit().is_err());
    }

    // Separate literal construction: row/term emission does not call emit or Emitter.
    // Reused wire numbering is immutable geometry; all row expressions are generated here.
    fn literal(stmt:&Statement)->Vec<Term>{
        let l=Layout::new();let one=Fr::one();let radix=Fr::from(65536u64);
        let mut out=Vec::with_capacity(TERMS);let mut n=0usize;
        let mut row=|gates:Vec<Gate>|{for gate in gates{out.push(Term{row:n,gate});}n+=1;};
        let boolean=|r:Range<usize>,row:&mut dyn FnMut(Vec<Gate>)|{
            for w in r{row(vec![linear(w,-one),product(w,w,one)]);}
        };
        let strict=|a:Range<usize>,b:Range<usize>,s:&Sub,end:bool,row:&mut dyn FnMut(Vec<Gate>)|{
            boolean(s.initial..s.initial+1,row);let mut g=linear(s.initial,one);g.c0=-one;row(vec![g]);
            for i in 0..a.len(){
                boolean(s.diff.start+i..s.diff.start+i+1,row);boolean(s.borrow.start+i..s.borrow.start+i+1,row);
                row(vec![linear(a.start+i,one),linear(if i<b.len(){b.start+i}else{0},-one),
                    linear(if i==0{s.initial}else{s.borrow.start+i-1},-one),linear(s.diff.start+i,-one),
                    linear(s.borrow.start+i,Fr::from(2u64))]);
            }if end{row(vec![linear(s.borrow.end-1,one)]);}
        };
        row(vec![linear(0,one)]);boolean(1..1281,&mut row);
        for i in 0..640{row(vec![linear(1+i,one),constant(-Fr::from(u64::from(stmt.ports[i])))]);}
        for i in 0..640{row(vec![linear(641+i,one),linear(1+i,-one)]);}
        for k in 0..3{row(vec![linear(l.time(k).end-1,one)]);}
        for r in &l.delta{boolean(r.clone(),&mut row);}for r in &l.tc{boolean(r.clone(),&mut row);}
        for k in 0..3{for j in 0..4{
            let mut gates=vec![constant(if k==2&&j==0{Fr::from(64u64)}else{Fr::zero()})];
            let rails=if k<2{vec![(l.delta[k].clone(),one),(l.time(k),one),(l.time(k+1),-one)]}
                else{vec![(l.delta[1].clone(),one),(l.delta[2].clone(),-one)]};
            for (r,c) in rails{add_bits(&mut gates,r,j,c);}
            add_full(&mut gates,carry(&l.tc[k],j,1,4),one);add_full(&mut gates,carry(&l.tc[k],j+1,1,4),-radix);row(gates);
        }}
        for k in 0..2{strict(l.delta[k].clone(),0..0,&l.positive[k],true,&mut row);}
        for r in &l.numerator{boolean(r.clone(),&mut row);}for r in &l.nc{boolean(r.clone(),&mut row);}
        for k in 0..2{for j in 0..16{
            let mut gates=vec![constant(Fr::zero())];add_bits(&mut gates,l.d(k),j,Fr::from(MULT));
            add_full(&mut gates,carry(&l.nc[k],j,27,16),one);add_bits(&mut gates,l.numerator[k].clone(),j,-one);
            add_full(&mut gates,carry(&l.nc[k],j+1,27,16),-radix);row(gates);
        }}
        for k in 0..2{for r in [&l.q[k],&l.rem[k],&l.pc[k]]{boolean(r.clone(),&mut row);}}
        for k in 0..2{for j in 0..19{
            let mut gates=Vec::with_capacity(1094);add_full(&mut gates,carry(&l.pc[k],j,19,19),one);
            add_bits(&mut gates,l.rem[k].clone(),j,one);add_bits(&mut gates,l.numerator[k].clone(),j,-one);
            // Independent pair enumeration selects the SUM OF LIMB indices, not summed bit positions.
            for qi in 0..251{for di in 0..64{if qi/16+di/16==j{
                gates.push(product(l.q[k].start+qi,l.delta[if k==0{0}else{2}].start+di,Fr::from(1u64<<((qi%16)+(di%16)))));
            }}}
            add_full(&mut gates,carry(&l.pc[k],j+1,19,19),-radix);
            // Literal order is quotient-limb/denominator-limb/bitpair, matching code-owned emitter.
            row(gates);
        }}
        for k in 0..2{strict(l.delta[if k==0{0}else{2}].clone(),l.rem[k].clone(),&l.rem_sub[k],true,&mut row);}
        boolean(l.a.clone(),&mut row);boolean(l.c.clone(),&mut row);for r in &l.ac{boolean(r.clone(),&mut row);}
        for k in 0..2{for j in 0..16{
            let c=if k==0{if j==0{3}else{0}}else if j<4{(INITIAL>>(16*j))&65535}else{0};
            let mut gates=vec![constant(Fr::from(c))];
            for i in 0..251{let pos=if k==0{i+1}else{i};if pos/16==j{gates.push(linear(l.q[if k==0{1}else{0}].start+i,Fr::from(1u64<<(pos%16))));}}
            add_full(&mut gates,carry(&l.ac[k],j,1,16),one);add_bits(&mut gates,if k==0{l.a.clone()}else{l.c.clone()},j,-one);
            add_full(&mut gates,carry(&l.ac[k],j+1,1,16),-radix);row(gates);
        }}
        strict(l.a.clone(),l.c.clone(),&l.compare,false,&mut row);boolean(l.selector..l.selector+1,&mut row);
        row(vec![linear(l.selector,one),linear(l.compare.borrow.end-1,one),constant(-one)]);
        boolean(l.b.clone(),&mut row);boolean(l.selected.clone(),&mut row);
        for j in 0..16{
            let mut gates=Vec::new();for (r,c) in [(l.b.clone(),one),(l.q[0].clone(),one),(l.a.clone(),-one)]{add_bits(&mut gates,r,j,c);}
            add_full(&mut gates,carry(&l.selected,j,1,16),one);add_full(&mut gates,carry(&l.selected,j+1,1,16),-radix);
            row(gates.into_iter().map(|g|product(l.selector,g.left,g.c1)).collect());
        }
        for w in l.selected.clone(){row(vec![linear(w,one),product(l.selector,w,-one)]);}
        for (i,w) in l.b.clone().enumerate(){let c=Fr::from(if i<64{INITIAL>>i&1}else{0});
            row(vec![linear(w,one),constant(-c),product(l.selector,w,-one),linear(l.selector,c)]);
        }
        for i in 0..253{row(vec![linear(l.b.start+i,one),constant(-Fr::from(u64::from(stmt.bound[i])))]);}
        for w in LIVE..M{row(vec![linear(w,one)]);}drop(row);
        assert_eq!((n,out.len(),out.capacity()),(10645,TERMS,TERMS));out
    }
    fn direct(terms:&[Term],r:&[Fr],u:&[Fr],v:&[Fr])->[Fr;4]{
        let mut out=[Fr::zero();4];for t in terms{
            let w=eq_at(r,t.row)*eq_at(u,t.gate.left)*eq_at(v,t.gate.right);
            for (o,c) in out.iter_mut().zip([t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3]){*o+=w*c;}
        }out
    }
    fn point(n:usize,seed:u64)->Vec<Fr>{(0..n).map(|i|Fr::from(seed+3*i as u64)).collect()}
    #[test]
    fn ell2_literal_coefficients_and_admission(){
        bounds();let input=fixture(17,29,17);let b=scalar(&input).unwrap();let stmt=Statement::new(&input,&b).unwrap();
        let c=materialize(&stmt);let mut literal=literal(&stmt);assert_eq!(c.terms,literal);
        let l=Layout::new();assert_eq!(l.selected.end,LIVE);
        let mut rows=0;let mut terms=0;for (name,n,t) in GROUPS{assert_eq!(group(name),rows..rows+n);rows+=n;terms+=t;}
        assert_eq!((rows,terms),(10645,TERMS));assert_eq!(sparse::validate(&c,0).unwrap().input_bits,13);
        let r=point(14,2);let u=point(13,7);let v=point(13,11);
        let wanted=coefficients(&stmt,&r,&u,&v).unwrap();assert_eq!(wanted,direct(&literal,&r,&u,&v));
        for seed in [17u64,31] {
            let rr=point(14,seed);let uu=point(13,seed+5);let vv=point(13,seed+9);
            assert_eq!(coefficients(&stmt,&rr,&uu,&vv).unwrap(),direct(&literal,&rr,&uu,&vv));
        }
        for channel in 0..4{
            let index=literal.iter().position(|t|![t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3][channel].is_zero()).unwrap_or(0);
            let saved=literal[index].clone();let g=&mut literal[index].gate;
            match channel{0=>g.c0+=Fr::one(),1=>g.c1+=Fr::one(),2=>g.c2+=Fr::one(),_=>g.c3+=Fr::one()}
            assert_eq!(authenticate_terms(&stmt,&literal).unwrap_err(),"ordered tuple fields");assert_ne!(literal,c.terms);assert_ne!(direct(&literal,&r,&u,&v),wanted);
            literal[index]=saved;
        }
        for axis in 0..3{
            let saved=literal[0].clone();match axis{0=>literal[0].row+=1,1=>literal[0].gate.left+=1,_=>literal[0].gate.right+=1}
            assert_eq!(authenticate_terms(&stmt,&literal).unwrap_err(),"ordered tuple fields");assert_ne!(literal,c.terms);assert_ne!(direct(&literal,&r,&u,&v),wanted);
            literal[0]=saved;
        }
        literal.swap(0,1);assert_eq!(authenticate_terms(&stmt,&literal).unwrap_err(),"ordered tuple fields");assert_ne!(literal,c.terms);
        assert_eq!(direct(&literal,&r,&u,&v),wanted);literal.swap(0,1); // Sum does not authenticate order.
        let bool_point=|n:usize,i:usize|(0..n).map(|b|Fr::from((i>>b&1)as u64)).collect::<Vec<_>>();
        for idx in [0usize,TERMS-1]{
            let t=&literal[idx];let rr=bool_point(14,t.row);let uu=bool_point(13,t.gate.left);let vv=bool_point(13,t.gate.right);
            assert_eq!(coefficients(&stmt,&rr,&uu,&vv).unwrap(),direct(&literal,&rr,&uu,&vv));
        }
        assert_eq!(coefficients(&stmt,&r[..13],&u,&v),Err(GkrError::PointDimension));
        assert_eq!(coefficients(&stmt,&r,&u[..12],&v),Err(GkrError::PointDimension));
        assert_eq!(coefficients(&stmt,&r,&u,&v[..12]),Err(GkrError::PointDimension));
        drop(literal);
        for axis in 0..3{let mut bad=c.clone();match axis{0=>bad.terms[0].row=R,1=>bad.terms[0].gate.left=M,_=>bad.terms[0].gate.right=M}
            assert!(matches!(sparse::validate(&bad,0),Err(GkrError::InvalidWireIndex)));
        }
        let mut bad=c.clone();bad.input_len=1<<25;assert!(matches!(sparse::validate(&bad,0),Err(GkrError::RepeatedSizeLimit)));
        bad.input_len=M;bad.row_count=3;assert!(sparse::validate(&bad,0).is_err());drop(bad);
        // Stored rows/term list/padding topology is independent of statement values and branch outcome.
        let other=fixture(1,INITIAL*2,17);let stmt2=Statement::new(&other,&scalar(&other).unwrap()).unwrap();
        let c2=materialize(&stmt2);assert_eq!(c2.terms.len(),c.terms.len());
        for (a,b) in c.terms.iter().zip(&c2.terms){assert_eq!((a.row,a.gate.left,a.gate.right),(b.row,b.gate.left,b.gate.right));}
    }
}

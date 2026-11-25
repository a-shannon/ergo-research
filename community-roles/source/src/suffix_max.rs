//! Standalone weighted suffix-MAX proposal; no live ABI/window adoption.
use ark_bn254::Fr;
use ark_ff::{BigInteger, One, PrimeField, Zero};
use num_bigint::BigUint;
use crate::{gkr::Gate, sparse::Term, transcript::Transcript, wiring::{evaluate_shift, RightIndex}};
pub const WIDTH: usize = 1 << 20;
pub const D_BASE: usize = 987674;
pub const BITS: usize = 224;
pub const HELPERS: usize = 673;
pub const ROW_WIDTH: usize = 2048;
const SOURCE: &[u8] = b"suffix-max-u224-weighted-v1;D987674;M,N,delta,s;LSB;BooleanCombined;work:F8F071C73405ED0CA430C38374212FE30089DE6E9BDA404D67D2329F190B0FBB;wiring:8A2E577E89808D7F7FB8198D1BD705225B38E8B7B3069344BC460EB83869272D";
#[derive(Clone,Debug)]
pub struct Layout {
    n:usize,c:usize,base:usize,slot_log:usize,input_len:usize,row_count:usize,terms:usize,edges:usize,local:Vec<Term>,
}
fn linear(row:usize,wire:usize,c:Fr)->Term {
    Term{row,gate:Gate{left:wire,right:0,c0:Fr::zero(),c1:c,c2:Fr::zero(),c3:Fr::zero()}}
}
fn product(row:usize,left:usize,right:usize,c:Fr)->Term {
    Term{row,gate:Gate{left,right,c0:Fr::zero(),c1:Fr::zero(),c2:Fr::zero(),c3:c}}
}
fn eq(p:&[Fr],i:usize)->Fr {
    p.iter().enumerate().fold(Fr::one(),|a,(b,x)|a*if i&(1usize<<b)==0{Fr::one()-x}else{*x})
}
impl Layout {
    pub fn new(n:usize,c:usize,base:usize)->Result<Self,String> {
        // Experimental candidate ceiling21; not a native rule or admission increase.
        if usize::BITS!=64 || n<2 || n>i32::MAX as usize || n.checked_next_power_of_two()!=Some(c)
            || !c.is_power_of_two() || c.trailing_zeros()>21 {return Err("suffix layout n/c geometry".into());}
        let end=base.checked_add(HELPERS).filter(|end|*end<=WIDTH).ok_or("suffix helper range")?;
        if base<D_BASE+BITS && D_BASE<end {return Err("suffix helper/D overlap".into());}
        // Exact representatives: both sides of D+2^224*s=N+delta are below2^225.
        let modulus=BigUint::from_bytes_le(&Fr::MODULUS.to_bytes_le());
        if modulus <= (BigUint::from(1u8)<<225usize) {return Err("suffix actual field modulus bound".into());}
        let input_len=c.checked_mul(WIDTH).ok_or("suffix input geometry")?;
        let row_count=c.checked_mul(ROW_WIDTH).ok_or("suffix row geometry")?;
        let terms=2690usize.checked_mul(n-1).and_then(|x|673usize.checked_mul(c-n+1).and_then(|y|x.checked_add(y))).ok_or("suffix term count")?;
        let edges=1121usize.checked_mul(n-1).ok_or("suffix edge count")?;
        let one=Fr::one();let mut local=Vec::with_capacity(2242);
        for bit in 0..HELPERS {
            let w=base+bit;
            local.push(Term{row:bit,gate:Gate{left:w,right:w,c0:Fr::zero(),c1:-one,c2:Fr::zero(),c3:one}});
        }
        let mut power=one;
        for bit in 0..BITS {
            local.push(linear(673,D_BASE+bit,power));
            local.push(linear(673,base+224+bit,-power));
            local.push(linear(673,base+448+bit,-power));
            power+=power;
        }
        local.push(linear(673,base+672,power));
        for bit in 0..BITS {
            let row=674+bit;
            local.push(linear(row,base+bit,one));local.push(linear(row,D_BASE+bit,-one));
            local.push(product(row,base+672,base+224+bit,-one));local.push(product(row,base+672,D_BASE+bit,one));
        }
        if local.len()!=2242 {return Err("suffix local template count".into());}
        Ok(Self{n,c,base,slot_log:c.trailing_zeros() as usize,input_len,row_count,terms,edges,local})
    }
    pub fn n(&self)->usize{self.n} pub fn c(&self)->usize{self.c} pub fn base(&self)->usize{self.base}
    pub fn input_log(&self)->usize{20+self.slot_log} pub fn row_log(&self)->usize{11+self.slot_log}
    pub fn input_len(&self)->usize{self.input_len} pub fn row_count(&self)->usize{self.row_count}
    pub fn term_count(&self)->usize{self.terms} pub fn edge_count(&self)->usize{self.edges}
    /// Callable proposal binding; actual source manifest remains independently pinned.
    pub fn bind(&self,t:&mut Transcript) {
        t.append_bytes(b"suffix-proposal-source",SOURCE);
        for (label,value) in [(b"suffix-n".as_slice(),self.n),(b"suffix-c",self.c),(b"suffix-helper-base",self.base),
            (b"suffix-D-base",D_BASE),(b"suffix-helper-bits",HELPERS),(b"suffix-row-width",ROW_WIDTH),
            (b"suffix-input-log",self.input_log()),(b"suffix-row-log",self.row_log())] {t.append_u64(label,value as u64);}
    }
    /// One physical owner; owner validation precedes the sink.
    pub fn emit_owner(&self,owner:usize,mut sink:impl FnMut(Term)->Result<(),String>)->Result<usize,String> {
        if owner>=self.c {return Err("suffix owner bounds".into());}
        let mut count=0;
        if owner<self.n-1 {
            for original in &self.local {
                let mut term=original.clone();term.row+=owner*ROW_WIDTH;
                term.gate.left+=owner*WIDTH;term.gate.right+=owner*WIDTH;sink(term)?;count+=1;
            }
        } else {
            for bit in 0..HELPERS {
                let mut term=linear(owner*ROW_WIDTH+bit,owner*WIDTH+self.base+bit,Fr::one());
                term.gate.right=owner*WIDTH;
                sink(term)?;count+=1;
            }
        }
        if owner>=1 && owner<self.n {
            for bit in 0..BITS {
                let row=owner*ROW_WIDTH+898+bit;
                let mut previous=linear(row,(owner-1)*WIDTH+self.base+224+bit,Fr::one());previous.gate.right=owner*WIDTH;sink(previous)?;count+=1;
                let mut current=linear(row,owner*WIDTH+self.base+bit,-Fr::one());current.gate.right=owner*WIDTH;sink(current)?;count+=1;
            }
        }
        Ok(count)
    }
    pub fn coefficients(&self,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String> {
        if r.len()!=self.row_log() || u.len()!=self.input_log() || v.len()!=self.input_log(){return Err("suffix coefficient dimensions".into());}
        let rr=&r[11..];let uu=&u[20..];let vv=&v[20..];
        let active=evaluate_shift(rr,uu,vv,0,0,(self.n-1) as u64,0,RightIndex::SameRow)?;
        let inactive=evaluate_shift(rr,uu,vv,0,(self.n-1) as u64,self.c as u64,0,RightIndex::SameRow)?;
        let previous=evaluate_shift(rr,uu,vv,1,1,self.n as u64,0,RightIndex::SameRow)?;
        let current=evaluate_shift(rr,uu,vv,0,1,self.n as u64,0,RightIndex::SameRow)?;
        let mut out=[Fr::zero();4];
        for term in &self.local {
            let g=&term.gate;let w=active*eq(&r[..11],term.row)*eq(&u[..20],g.left)*eq(&v[..20],g.right);
            for (sum,c) in out.iter_mut().zip([g.c0,g.c1,g.c2,g.c3]){*sum+=w*c;}
        }
        let zero=eq(&v[..20],0);
        for bit in 0..HELPERS {out[1]+=inactive*eq(&r[..11],bit)*eq(&u[..20],self.base+bit)*zero;}
        for bit in 0..BITS {out[1]+=eq(&r[..11],898+bit)*zero*(previous*eq(&u[..20],self.base+224+bit)-current*eq(&u[..20],self.base+bit));}
        Ok(out)
    }
}



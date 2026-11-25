//! Local symbolic scopes; no native banks, verified receipts or commitment domain.
use ark_bn254::Fr;
use ark_ff::{One,Zero};
use num_bigint::BigUint;
use crate::{origin_score::{self as words,Spec,INPUT,ROWS},sparse::Term,wiring::{evaluate_shift,RightIndex}};

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) enum Mode {Sampled,Exact}
#[derive(Clone,Debug)]
pub(crate) enum GuardPolicy {Disabled,Require{prefix:usize,total:BigUint}}
#[derive(Clone,Debug)]
// prefix counts this conditional local window; it is not a certified protocol 1..cut.
pub(crate) struct Profile {pub mode:Mode,pub prefix:usize,pub expected:BigUint,pub guard:GuardPolicy}
#[derive(Clone,Debug)]
pub(crate) struct Plan {first:u64,count:usize,slots:usize,profiles:Vec<Profile>}
#[derive(Clone,Debug,PartialEq,Eq)]
pub(crate) struct ConditionalImport {pub profile:usize,pub slot:usize,pub role:&'static str,pub width:usize}
pub(crate) fn maturity(mode:Mode,origin:u64)->u64{
    let zone=if origin<417792{0}else if origin<845760{1}else{2};
    match mode{Mode::Sampled=>[43410,23155,4995][zone],Mode::Exact=>[17867,9548,2090][zone]}
}
pub(crate) fn model_source(origin:u64,header_convention:bool)->Result<(u64,u64,u64),String>{
    if origin<845760{return Err("symbolic modern origin required".into());}
    let destination=origin.checked_sub(if header_convention{1}else{2}).ok_or("model owner underflow")?;
    Ok((destination,if header_convention{1}else{0},if header_convention{1089}else{1088}))
}
impl Plan {
    pub fn new(first:u64,count:usize,profiles:Vec<Profile>)->Result<Self,String>{
        words::bounds()?;
        if first==0||count>1<<21||profiles.is_empty()||profiles.len()>2{return Err("local descriptor dimensions".into());}
        first.checked_add(count as u64).ok_or("local absolute-origin overflow")?;
        if profiles.len()==2&&profiles[0].mode==profiles[1].mode{return Err("duplicate local profile".into());}
        for p in &profiles{if p.prefix>count||p.expected.bits()>225{return Err("local prefix/output range".into());}
            if let GuardPolicy::Require{prefix,total}=&p.guard{if *prefix>count||total.bits()>224{return Err("local guard scope/range".into());}}}
        let slots=count.max(1).checked_next_power_of_two().ok_or("local slot geometry")?;
        first.checked_add(slots as u64).ok_or("local padding-origin overflow")?;
        slots.checked_mul(profiles.len()).and_then(|n|n.checked_mul(ROWS)).ok_or("local row geometry overflow")?;
        Ok(Self{first,count,slots,profiles})
    }
    pub fn count(&self)->usize{self.count}pub fn slots(&self)->usize{self.slots}
    pub fn profiles(&self)->usize{self.profiles.len()}
    pub fn owner_log(&self)->usize{self.slots.trailing_zeros() as usize}
    pub fn profile_log(&self)->usize{usize::from(self.profiles.len()==2)}
    pub fn input_log(&self)->usize{11+self.owner_log()+self.profile_log()}
    pub fn row_log(&self)->usize{13+self.owner_log()+self.profile_log()}
    pub fn input_len(&self)->usize{INPUT*self.slots*self.profiles.len()}
    pub fn row_count(&self)->usize{ROWS*self.slots*self.profiles.len()}
    pub fn input_base(&self,p:usize,s:usize)->Result<usize,String>{self.spec(p,s)?;Ok((p*self.slots+s)*INPUT)}
    pub fn spec(&self,p:usize,s:usize)->Result<Spec,String>{
        let profile=self.profiles.get(p).ok_or("local profile index")?;
        if s>=self.slots{return Err("local slot index".into());}
        let active=s<self.count;let reducing=active&&s<profile.prefix;
        let guard_total=match &profile.guard{GuardPolicy::Require{prefix,total} if active&&s<*prefix=>Some(total.clone()),_=>None};
        Ok(Spec{active,origin_one:active&&self.first+s as u64==1,reducing,first:s==0,
            terminal:reducing&&s+1==profile.prefix,empty_terminal:s==0&&profile.prefix==0,
            maturity:maturity(profile.mode,self.first+s as u64),guard_total,expected:profile.expected.clone()})
    }
    pub fn imports(&self,p:usize,s:usize)->Result<Vec<ConditionalImport>,String>{
        let spec=self.spec(p,s)?;if !spec.active{return Ok(Vec::new());}
        Ok(vec![ConditionalImport{profile:p,slot:s,role:"conditional-W",width:224},
            ConditionalImport{profile:p,slot:s,role:"conditional-V",width:65}])
    }
    pub fn read<T>(&self,p:usize,s:usize,mut callback:impl FnMut(&ConditionalImport)->T)->Result<Vec<T>,String>{
        Ok(self.imports(p,s)?.iter().map(&mut callback).collect())
    }
    pub fn emit_owner(&self,p:usize,s:usize,mut sink:impl FnMut(Term))->Result<usize,String>{
        let spec=self.spec(p,s)?;let base=(p*self.slots+s)*INPUT;let rows=(p*self.slots+s)*ROWS;
        Ok(words::emit_local(&spec,|local|{let mut t=local.term;t.row+=rows;
            t.gate.left+=if local.previous{base.checked_sub(INPUT).expect("first predecessor is literal")}else{base};
            t.gate.right+=base;sink(t);})?)
    }
    pub fn terms(&self)->Result<Vec<Term>,String>{
        if self.slots>8{return Err("bounded tuple materialization only".into());}
        let mut count=0;for p in 0..self.profiles.len(){for s in 0..self.slots{count+=self.emit_owner(p,s,|_|{})?;}}
        let mut out=Vec::with_capacity(count);for p in 0..self.profiles.len(){for s in 0..self.slots{self.emit_owner(p,s,|t|out.push(t))?;}}
        assert_eq!((out.len(),out.capacity()),(count,count));Ok(out)
    }
    pub fn authenticate(&self,terms:&[Term])->Result<(),String>{
        if self.slots>8{return Err("bounded tuple authentication only".into());}
        let mut index=0;let mut equal=true;
        for p in 0..self.profiles.len(){for s in 0..self.slots{self.emit_owner(p,s,|t|{
            equal&=terms.get(index)==Some(&t);index+=1;
        })?;}}
        if index!=terms.len()||!equal{return Err("local ordered tuple fields/count".into());}Ok(())
    }
    fn segments(&self,p:usize)->Vec<(usize,usize)>{
        let profile=&self.profiles[p];let mut edges=vec![0,self.count,self.slots,profile.prefix];
        if self.count>0{edges.push(1);}if profile.prefix>0{edges.push(profile.prefix-1);}
        if let GuardPolicy::Require{prefix,..}=&profile.guard{edges.push(*prefix);}
        for boundary in [417792u64,845760]{if let Some(s)=boundary.checked_sub(self.first){if s<=self.slots as u64{edges.push(s as usize);}}}
        edges.sort_unstable();edges.dedup();edges.windows(2).filter(|x|x[0]<x[1]).map(|x|(x[0],x[1])).collect()
    }
    pub fn analytic_cost(&self)->Result<(usize,usize),String>{
        let mut templates=0;let mut segments=0;
        for p in 0..self.profiles.len(){for (lo,_) in self.segments(p){templates+=words::emit_local(&self.spec(p,lo)?,|_|{})?;segments+=1;}}
        Ok((segments,templates))
    }
    pub fn coefficients(&self,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String>{
        if (r.len(),u.len(),v.len())!=(self.row_log(),self.input_log(),self.input_log()){return Err("local coefficient dimensions".into());}
        let h=self.owner_log();let rr=&r[13..13+h];let uu=&u[11..11+h];let vv=&v[11..11+h];
        let row=(0..ROWS).map(|i|eq(&r[..13],i)).collect::<Vec<_>>();
        let left=(0..INPUT).map(|i|eq(&u[..11],i)).collect::<Vec<_>>();
        let right=(0..INPUT).map(|i|eq(&v[..11],i)).collect::<Vec<_>>();
        assert_eq!((row.len(),row.capacity(),left.len(),left.capacity(),right.len(),right.capacity()),(8192,8192,2048,2048,2048,2048));
        let mut out=[Fr::zero();4];
        for p in 0..self.profiles.len(){let role=eq(&r[13+h..],p)*eq(&u[11+h..],p)*eq(&v[11+h..],p);
            for (lo,hi) in self.segments(p){let spec=self.spec(p,lo)?;
                let same=evaluate_shift(rr,uu,vv,0,lo as u64,hi as u64,0,RightIndex::SameRow)?;
                let previous=if lo==0{Fr::zero()}else{evaluate_shift(rr,uu,vv,1,lo as u64,hi as u64,0,RightIndex::SameRow)?};
                words::emit_local(&spec,|local|{let t=local.term;let g=t.gate;
                    let weight=role*row[t.row]*left[g.left]*right[g.right]*if local.previous{previous}else{same};
                    for (sum,c) in out.iter_mut().zip([g.c0,g.c1,g.c2,g.c3]){*sum+=weight*c;}})?;
            }}Ok(out)
    }
    pub fn bank53_coefficients(&self,context:usize,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String>{
        if context>=2{return Err("bank53 context index".into());}
        if self.profiles.len()!=1{return Err("bank53 requires one profile plan".into());}
        let h=self.owner_log();
        if (r.len(),u.len(),v.len())!=(19+h,20+h,20+h){return Err("bank53 coefficient dimensions".into());}
        let row_base=409600+context*32768+16384;
        let input_base=671744+context*8192+5757;
        if row_base+ROWS>1<<19||input_base+INPUT>1<<20{return Err("bank53 physical selector range".into());}
        let rr=&r[19..];let uu=&u[20..];let vv=&v[20..];
        let row=(0..ROWS).map(|localrow|eq(&r[..19],row_base+localrow)).collect::<Vec<_>>();
        let left=(0..INPUT).map(|localbit|eq(&u[..20],input_base+localbit)).collect::<Vec<_>>();
        let right=(0..INPUT).map(|localbit|eq(&v[..20],input_base+localbit)).collect::<Vec<_>>();
        assert_eq!((row.len(),row.capacity(),left.len(),left.capacity(),right.len(),right.capacity()),(8192,8192,2048,2048,2048,2048));
        let mut out=[Fr::zero();4];
        for (lo,hi) in self.segments(0){let spec=self.spec(0,lo)?;
            let same=evaluate_shift(rr,uu,vv,0,lo as u64,hi as u64,0,RightIndex::SameRow)?;
            let previous=if lo==0{Fr::zero()}else{evaluate_shift(rr,uu,vv,1,lo as u64,hi as u64,0,RightIndex::SameRow)?};
            words::emit_local(&spec,|local|{let t=local.term;let g=t.gate;
                let weight=row[t.row]*left[g.left]*right[g.right]*if local.previous{previous}else{same};
                for (sum,c) in out.iter_mut().zip([g.c0,g.c1,g.c2,g.c3]){*sum+=weight*c;}})?;
        }Ok(out)
    }
}
pub(crate) fn eq(p:&[Fr],i:usize)->Fr{p.iter().enumerate().fold(Fr::one(),|a,(b,z)|a*if i>>b&1==1{*z}else{Fr::one()-z})}

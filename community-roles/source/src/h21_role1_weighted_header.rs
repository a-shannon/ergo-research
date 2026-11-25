//! The owner-local HEADER part of the physical H21 role-1 replay. The other
//! families still use their canonical inverse and the original common witness.
use super::*;
use std::collections::BTreeMap;

const WIDTH:usize=1<<20;
const ROWS:usize=1<<19;
// Row start, first left wire, row count. These five disjoint groups are
// validated against the actual, post-retirement HEADER emitter before use.
const CONDITIONAL:[(usize,usize,usize);5]=[
    (348440,991232,8192),(356632,999424,673),(357305,1000097,673),
    (357978,1000770,2048),(360026,1002818,2048),
];
pub(super) const RESERVED:usize=1<<30;

pub(super) fn reserve(original_required:usize,budget:usize)->Result<(),String>{
    if original_required.checked_add(RESERVED).is_none_or(|v|v>budget){
        return Err("H21 HEADER shared weighting exceeds role budget".into());
    }
    Ok(())
}

struct WeightedGate {left:usize,right:usize,weights:[Fr;4],group:usize}
pub(super) trait Source: Sync{
    fn omissions(&self,owner:usize)->Result<[bool;6],String>;
    fn emit(&self,sink:&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String>;
}
#[cfg(test)]
impl Source for crate::packed_owner_assembly::h21_structural_roster::H21StructuralRoster<'_>{
    fn omissions(&self,owner:usize)->Result<[bool;6],String>{self.header_omissions(owner)}
    fn emit(&self,sink:&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String>{self.full_header_template(sink)}
}
pub(super) struct Header<'a>{roster:&'a dyn Source,gates:Vec<WeightedGate>,owner_weight:Vec<Fr>}
impl<'a> Header<'a>{
    pub(super) fn new(roster:&'a dyn Source,r:&[Fr])->Result<Self,String>{
        if r.len()!=40{return Err("weighted H21 row coordinates".into());}
        let rows=gkr::eq_weights(&r[..19]);
        let mut gates=Vec::with_capacity(396561);
        let mut counts=[0;6];
        roster.emit(&mut |t|{
            if t.row>=ROWS || t.gate.left>=WIDTH || t.gate.right>=WIDTH{return Err("weighted HEADER local indices".into());}
            let mut group=0;
            for (i,&(start,wire,len)) in CONDITIONAL.iter().enumerate(){
                if (start..start+len).contains(&t.row){
                    if t.row!=start+counts[i+1] || t.gate.left!=wire+t.row-start || t.gate.right!=0 ||
                        [t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3]!=[Fr::zero(),Fr::one(),Fr::zero(),Fr::zero()]{
                        return Err("weighted HEADER condition is not its canonical unique zero anchor".into());
                    }
                    group=i+1;break;
                }
            }
            counts[group]+=1;
            let w=rows[t.row];
            gates.push(WeightedGate{left:t.gate.left,right:t.gate.right,
                weights:[t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3].map(|c|w*c),group});
            Ok(())
        })?;
        if gates.len()!=396561 || CONDITIONAL.iter().enumerate().any(|(i,x)|counts[i+1]!=x.2){
            return Err("weighted H21 HEADER template census".into());
        }
        Ok(Self{roster,gates,owner_weight:gkr::eq_weights(&r[19..])})
    }

    pub(super) fn round(&self,prefix:&[Fr],v:Option<(&[Fr],Fr)>)->Result<Round,String>{
        if prefix.len()>20 || v.is_some_and(|(u,_)|u.len()!=WIDTH){return Err("weighted HEADER prefix dimensions".into());}
        let w=gkr::eq_weights(prefix);
        let mut groups:[BuildGroup;6]=std::array::from_fn(|_|BuildGroup::default());
        let mask=w.len()-1;
        for gate in &self.gates {
            let target=if v.is_some(){gate.right}else{gate.left};
            let projection=w[target&mask];
            let bucket=target>>prefix.len();
            let group=&mut groups[gate.group];
            let [c0,c1,c2,c3]=gate.weights;
            if let Some((u,lv))=v {
                let factor=projection*u[gate.left];
                group.add_a(bucket,factor*(c2+c3*lv),None);
                group.fixed_b[bucket&1]+=factor*(c0+c1*lv);
            } else {
                group.add_a(bucket,projection*c1,(!c3.is_zero()).then(||(gate.right,projection*c3)));
                group.fixed_b[bucket&1]+=projection*c0;
                if !c2.is_zero(){group.bit_b.entry(gate.right).or_default()[bucket&1]+=projection*c2;}
            }
        }
        Ok(Round {groups:groups.map(BuildGroup::finish),k:prefix.len(),left:v.is_none()})
    }
}

#[derive(Default)]
struct APart {fixed:[Fr;2],var:Vec<(usize,usize,Fr)>}
#[derive(Default)]
struct BuildGroup {a:BTreeMap<usize,APart>,fixed_b:[Fr;2],bit_b:BTreeMap<usize,[Fr;2]>}
impl BuildGroup{
    fn add_a(&mut self,bucket:usize,fixed:Fr,var:Option<(usize,Fr)>){
        if fixed.is_zero() && var.is_none(){return;}
        let p=self.a.entry(bucket>>1).or_default();
        p.fixed[bucket&1]+=fixed;
        if let Some((bit,k))=var{p.var.push((bucket&1,bit,k));}
    }
    fn finish(self)->Group{Group{a:self.a.into_iter().collect(),fixed_b:self.fixed_b,bit_b:self.bit_b.into_iter().collect()}}
}
struct Group {a:Vec<(usize,APart)>,fixed_b:[Fr;2],bit_b:Vec<(usize,[Fr;2])>}
pub(super) struct Round {groups:[Group;6],k:usize,left:bool}
fn bit(raw:&[u8],i:usize)->bool {raw[i>>3]&(1<<(i&7))!=0}
impl Round{
    /// For k<20 return the quadratic in monomial order; at k=20 return A,B
    /// before multiplication by X. Common owner factors are applied once.
    pub(super) fn contribution(&self,header:&Header<'_>,owner:usize,x:&[Fr],raw:Option<&[u8]>,u_high:Option<&[Fr]>)->Result<[Fr;3],String>{
        if owner>=1<<21 || x.len()!=WIDTH>>self.k || raw.is_some_and(|r|r.len()!=WIDTH/8) ||
            self.left!=raw.is_some() || self.left==u_high.is_some() || u_high.is_some_and(|u|u.len()!=1<<21){
            return Err("weighted HEADER owner input".into());
        }
        let omit=header.roster.omissions(owner)?;
        let mut result=[Fr::zero();3];let mut b=[Fr::zero();2];
        for (group,skip) in self.groups.iter().zip(omit){
            if skip{continue;}
            b[0]+=group.fixed_b[0];b[1]+=group.fixed_b[1];
            if let Some(bits)=raw{
                for &(wire,weight) in &group.bit_b {if bit(bits,wire){b[0]+=weight[0];b[1]+=weight[1];}}
            }
            for (pair,a) in &group.a {
                let mut coeff=a.fixed;
                if let Some(bits)=raw {
                    for &(lane,wire,weight) in &a.var{if bit(bits,wire){coeff[lane]+=weight;}}
                }
                if self.k==20{result[0]+=coeff[0];continue;}
                let d=coeff[1]-coeff[0];
                let i=pair*2;
                if self.k==0 && raw.is_some() {
                    let bits=raw.unwrap();let lo=bit(bits,i);let hi=bit(bits,i+1);
                    if lo{result[0]+=coeff[0];result[1]+=d;}
                    if hi!=lo{
                        if hi{result[1]+=coeff[0];result[2]+=d;}else{result[1]-=coeff[0];result[2]-=d;}
                    }
                } else {
                    let lo=x[i];let dx=x[i+1]-lo;
                    result[0]+=coeff[0]*lo;result[1]+=coeff[0]*dx+d*lo;result[2]+=d*dx;
                }
            }
        }
        if self.k==20{result[1]=b[0];}else{result[0]+=b[0];result[1]+=b[1]-b[0];}
        let mut scale=header.owner_weight[owner];
        if let Some(high)=u_high{scale*=high[owner];}
        Ok(result.map(|v|v*scale))
    }
}

pub(super) fn combine(
    header:Option<&Header<'_>>,round:Option<&Round>,input:&mut impl EdgeInput,
    owner:usize,state:&EdgeReplayState,u_high:Option<&[Fr]>,
)->Result<[Fr;3],String>{
    let mut values=if state.x.len()==1{
        let (a,b)=state.banks.terminal();[a,b,Fr::zero()]
    }else{
        state.banks.message(&state.x).try_into().map_err(|_|"wrong quadratic degree")?
    };
    match (header,round){
        (None,None)=>{},
        (Some(h),Some(p))=>{
            let raw=if p.left{Some(input.header_bits(owner)?)}else{None};
            let contribution=p.contribution(h,owner,&state.x,raw,u_high)?;
            for i in 0..3{values[i]+=contribution[i];}
        },
        _=>return Err("incomplete HEADER contraction".into()),
    }
    Ok(values)
}

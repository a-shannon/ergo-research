//! Conditional two-owner modern Score join on one private sparse physical X.
//! No native Upper/MAX provenance, origin-zero anchor, terminal, PCS or admission.
use ark_bn254::Fr;
use ark_ff::{One,Zero};
use num_bigint::BigUint;
use std::collections::BTreeMap;
use crate::{origin_score as score,origin_score_map::{Plan as ScorePlan,Profile,Mode,GuardPolicy},
    certified_modern_cap as cap,h21_scheduled_max_cap::{Plan as Schedule,Writer as ScheduledWriter},
    h21_row_support::{relocate,Family as Relocation},gkr::Gate,sparse::Term};

const OWNERS:[usize;2]=[845759,845760];
const GUARDS:[usize;2]=[845759,845887];
const SOURCES:[usize;2]=[844670,844798];
const SCORE:[usize;2]=[677501,685693];
const CAP:[usize;2]=[1000770,1002818];
const MAX:[usize;2]=[999424,1000097];
const COUNT:[usize;2]=[1827838,1827775];
fn x(o:usize,q:usize)->usize{o*1048576+q}
fn row(o:usize,q:usize)->usize{o*524288+q}

#[derive(Clone,Copy,Debug,PartialEq,Eq,PartialOrd,Ord)]
enum Writer {Literal,Upper(usize),Max(usize,usize),Boundary(usize),Cap(usize,usize),Score(usize,usize)}
#[derive(Clone,Copy,Debug,PartialEq,Eq,PartialOrd,Ord)]
enum Family {Cap(usize,usize),Score(usize,usize),W(usize,usize),V(usize,usize)}
#[derive(Clone,Debug,PartialEq,Eq)]
struct Piece {family:Family,group:&'static str,term:Term}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
enum ReadKind {Upper,Max,Previous,V}
#[derive(Clone,Debug,PartialEq,Eq)]
struct Read {kind:ReadKind,context:usize,owner:usize,local:usize,width:usize,writer:Writer}
#[derive(Clone,Debug,PartialEq,Eq)]
struct Cell {writer:Writer,value:Fr}
#[derive(Clone,Debug,Default,PartialEq,Eq)]
struct SparseX {cells:BTreeMap<usize,Cell>}
impl SparseX {
    // A rail write is atomic and rejects every duplicate, including equal bits.
    fn write(&mut self,owner:usize,local:usize,width:usize,writer:Writer,bits:&[Fr])->Result<(),String>{
        if owner>=1<<21 || width==0 || local.checked_add(width).filter(|n|*n<=1<<20).is_none()
            ||bits.len()!=width{return Err("X rail width/extent".into());}
        if bits.iter().any(|v|!v.is_zero()&&!v.is_one()){return Err("X rail nonboolean".into());}
        if (0..width).any(|k|self.cells.contains_key(&x(owner,local+k))){return Err("X duplicate writer".into());}
        for (k,value) in bits.iter().enumerate(){self.cells.insert(x(owner,local+k),Cell{writer,value:*value});}Ok(())
    }
    fn word(&mut self,o:usize,q:usize,width:usize,w:Writer,n:&BigUint)->Result<(),String>{
        if n.bits()>width as u64{return Err("X integer width".into());}
        self.write(o,q,width,w,&(0..width).map(|k|Fr::from(u64::from(n.bit(k as u64)))).collect::<Vec<_>>())
    }
    fn read(&self,port:&Read)->Result<BigUint,String>{
        let mut n=BigUint::from(0u8);
        for k in 0..port.width {let cell=self.cells.get(&x(port.owner,port.local+k)).ok_or("read missing cell")?;
            if cell.writer!=port.writer{return Err("read writer provenance".into());}
            if !cell.value.is_zero()&&!cell.value.is_one(){return Err("read nonboolean".into());}
            if cell.value.is_one(){n+=BigUint::from(1u8)<<k;}}
        Ok(n)
    }
}

/// These are conditional values, never native-authenticated imports. Upper is
/// physically shared across contexts. MAX and initial Score.R are per context.
pub(super) struct Inputs {
    pub upper:[BigUint;2],pub max:[[BigUint;2];2],pub previous:[BigUint;2],
}
#[derive(Clone,Debug,PartialEq,Eq)]
struct Staged {x:SparseX,terms:Vec<Piece>,reads:Vec<Read>}
#[derive(Clone,Debug,PartialEq,Eq)]
pub(super) struct Published {x:SparseX,census:BTreeMap<(Family,&'static str),usize>}
#[derive(Clone,Debug,Default,PartialEq,Eq)]
pub(super) struct Destination {window:Option<Published>}

fn spec(c:usize,o:usize)->Result<score::Spec,String>{
    if c>=2||!OWNERS.contains(&o){return Err("Score window context/owner".into());}
    // GLOBAL semantics: first origin1, full context prefix. This is not a
    // two-slot Plan whose first/terminal bits would change the recurrence.
    let p=ScorePlan::new(1,COUNT[c],vec![Profile{mode:if c==0{Mode::Sampled}else{Mode::Exact},
        prefix:COUNT[c],expected:BigUint::from(0u8),guard:GuardPolicy::Disabled}])?;
    let s=p.spec(0,o)?;
    if !s.active||!s.reducing||s.first||s.terminal||s.origin_one||s.empty_terminal
        ||s.maturity!=[4995,2090][c]||s.guard_total.is_some(){return Err("global Score Spec drift".into());}Ok(s)
}
fn reads()->Vec<Read>{
    let mut out=Vec::new();for c in 0..2 {for j in 0..2 {
        out.push(Read{kind:ReadKind::Upper,context:c,owner:OWNERS[j]-1,local:987450,width:224,writer:Writer::Upper(j)});
        out.push(Read{kind:ReadKind::Max,context:c,owner:SOURCES[j],local:MAX[c],width:224,writer:Writer::Max(c,j)});
        out.push(Read{kind:ReadKind::Previous,context:c,owner:OWNERS[j]-1,local:SCORE[c]+1318,width:225,
            writer:if j==0{Writer::Boundary(c)}else{Writer::Score(c,0)}});
        out.push(Read{kind:ReadKind::V,context:c,owner:GUARDS[j],local:CAP[c]+740,width:65,writer:Writer::Cap(c,j)});
    }}out
}
fn port(kind:ReadKind,c:usize,j:usize)->Read {
    reads().into_iter().find(|p|p.kind==kind&&p.context==c&&p.owner==match kind {
        ReadKind::Upper|ReadKind::Previous=>OWNERS[j]-1,ReadKind::Max=>SOURCES[j],ReadKind::V=>GUARDS[j]
    }).expect("fixed window read")
}
fn cap_group(q:usize)->&'static str {
    let mut start=0;for (name,rows,_) in cap::GROUPS {if (start..start+rows).contains(&q){return name;}start+=rows;}
    panic!("Cap source row extent")
}
fn canonical()->Result<Vec<Piece>,String>{
    let mut out=Vec::with_capacity(59856);let schedule=Schedule::new();
    for j in 0..2 {
        schedule.visit_owner(GUARDS[j],|writer,t| {
            if let ScheduledWriter::Cap{context:c,origin}=writer {
                if origin!=GUARDS[j]+1{return Err("Cap origin drift".into());}
                let local=t.row-GUARDS[j]*524288;
                let q=if ([357978,360026][c]..[357978,360026][c]+2048).contains(&local){local-[357978,360026][c]}
                    else if ([476034,476554][c]..[476034,476554][c]+520).contains(&local){2048+local-[476034,476554][c]}
                    else{return Err("Cap candidate ROW drift".into());};
                out.push(Piece{family:Family::Cap(c,j),group:cap_group(q),term:t});
            }Ok(())
        })?;
    }
    for c in 0..2 {for j in 0..2 {let o=OWNERS[j];let s=spec(c,o)?;let mut error=None;
        score::emit_local(&s,|local| {
            let group=score::row_label(local.term.row);let mut t=local.term;
            t.row+=row(o,425984+c*32768);
            t.gate.left=x(if local.previous{o-1}else{o},SCORE[c]+t.gate.left);
            t.gate.right=x(o,SCORE[c]+t.gate.right);
            match relocate(Relocation::Score(c),o,&t){Ok(term)=>out.push(Piece{family:Family::Score(c,j),group,term}),Err(e)=>error=Some(e)}
        })?;if let Some(e)=error{return Err(e);}
        for k in 0..224 {for (left,right,c1,c2) in [(x(o,SCORE[c]+k),0,Fr::one(),Fr::zero()),
            (0,x(o-1,987450+k),Fr::zero(),-Fr::one())] {
            let t=Term{row:row(o,438272+c*32768+k),gate:Gate{left,right,c0:Fr::zero(),c1,c2,c3:Fr::zero()}};
            out.push(Piece{family:Family::W(c,j),group:"upper-read",term:relocate(Relocation::W(c),o,&t)?});
        }}
        for k in 0..65 {let t=Term{row:row(o,430192+c*32768+k),gate:Gate{
            left:x(o,SCORE[c]+224+k),right:x(GUARDS[j],CAP[c]+740+k),c0:Fr::zero(),c1:Fr::one(),c2:-Fr::one(),c3:Fr::zero()}};
            out.push(Piece{family:Family::V(c,j),group:"cap-read",term:relocate(Relocation::V(c),o,&t)?});}
    }}Ok(out)
}
fn census(terms:&[Piece])->BTreeMap<(Family,&'static str),usize>{
    let mut counts=BTreeMap::new();for p in terms{*counts.entry((p.family,p.group)).or_insert(0)+=1;}counts
}
fn shape()->BTreeMap<usize,Writer>{
    let mut out=BTreeMap::new();let mut add=|o,q,n,w|{for k in 0..n{assert!(out.insert(x(o,q+k),w).is_none());}};
    add(0,0,1,Writer::Literal);
    for j in 0..2 {add(OWNERS[j]-1,987450,224,Writer::Upper(j));}
    for c in 0..2 {add(845758,SCORE[c]+1318,225,Writer::Boundary(c));for j in 0..2 {
        add(SOURCES[j],MAX[c],224,Writer::Max(c,j));add(GUARDS[j],CAP[c],2048,Writer::Cap(c,j));
        add(OWNERS[j],SCORE[c],2048,Writer::Score(c,j));}}
    out
}
fn stage(input:&Inputs)->Result<Staged,String>{
    if input.upper[1]<input.upper[0]{return Err("conditional Upper must be monotone".into());}
    let mut sx=SparseX::default();sx.word(0,0,1,Writer::Literal,&BigUint::from(0u8))?;
    for j in 0..2 {sx.word(OWNERS[j]-1,987450,224,Writer::Upper(j),&input.upper[j])?;}
    for c in 0..2 {
        if input.previous[c].is_zero(){return Err("positive conditional boundary previous-R".into());}
        sx.word(845758,SCORE[c]+1318,225,Writer::Boundary(c),&input.previous[c])?;
        for j in 0..2 {
            cap::admit(&input.max[c][j])?;
            sx.word(SOURCES[j],MAX[c],224,Writer::Max(c,j),&input.max[c][j])?;
            let d=sx.read(&port(ReadKind::Max,c,j))?;
            sx.write(GUARDS[j],CAP[c],2048,Writer::Cap(c,j),&cap::producer(&d)?)?;
            let w=sx.read(&port(ReadKind::Upper,c,j))?;let v=sx.read(&port(ReadKind::V,c,j))?;
            let previous=sx.read(&port(ReadKind::Previous,c,j))?;
            let produced=score::produce(&spec(c,OWNERS[j])?,Some(&score::ConditionalInputs{w,v}),&previous)?;
            sx.write(OWNERS[j],SCORE[c],2048,Writer::Score(c,j),&produced)?;
        }
    }Ok(Staged{x:sx,terms:canonical()?,reads:reads()})
}
fn validate(staged:&Staged)->Result<BTreeMap<(Family,&'static str),usize>,String>{
    let expected=canonical()?;let count=census(&staged.terms);
    // This gate precedes every residual evaluation; missing zero-valued aliases
    // or entire term families cannot disappear silently.
    if count!=census(&expected)||staged.terms!=expected||staged.reads!=reads(){return Err("census ordered families/fields/reads".into());}
    let actual=staged.x.cells.iter().map(|(a,c)|(*a,c.writer)).collect::<BTreeMap<_,_>>();
    if actual!=shape(){return Err("census X writer shape".into());}
    if staged.x.cells.values().any(|c|!c.value.is_zero()&&!c.value.is_one()){return Err("census X boolean".into());}
    if !staged.x.cells[&0].value.is_zero(){return Err("census literal zero".into());}
    for read in &staged.reads {staged.x.read(read)?;}
    if staged.x.read(&port(ReadKind::Upper,0,1))?<staged.x.read(&port(ReadKind::Upper,0,0))? {
        return Err("conditional Upper must be monotone".into());}
    let mut row_writer=BTreeMap::new();let mut residual=BTreeMap::<usize,Fr>::new();
    for p in &staged.terms {let t=&p.term;let g=&t.gate;
        if let Some(old)=row_writer.insert(t.row,p.family){if old!=p.family{return Err("census ROW writer collision".into());}}
        let a=staged.x.cells.get(&g.left).ok_or("read missing left X")?.value;
        let b=staged.x.cells.get(&g.right).ok_or("read missing right X")?.value;
        *residual.entry(t.row).or_insert(Fr::zero())+=g.c0+g.c1*a+g.c2*b+g.c3*a*b;
    }
    if let Some((q,_))=residual.iter().find(|(_,v)|!v.is_zero()){return Err(format!("residual ROW {q}"));}Ok(count)
}
fn publish(destination:&mut Destination,staged:Staged)->Result<(),String>{
    if destination.window.is_some(){return Err("duplicate window publish".into());}
    let census=validate(&staged)?;
    destination.window=Some(Published{x:staged.x,census});Ok(())
}
pub(super) fn join(destination:&mut Destination,input:&Inputs)->Result<(),String>{publish(destination,stage(input)?)}

#[cfg(test)]
#[path="score_window_join_tests.rs"]
mod tests;

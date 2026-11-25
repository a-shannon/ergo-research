//! Conditional premodern Score summary and one modern consumer on sparse X.
//! Endpoint values and Map descriptors are premises, not native/global-U proof.
//! No global retirement, transcript, admission, frame read or PCS is performed.
use ark_bn254::Fr;
use ark_ff::{One, PrimeField, Zero, BigInteger};
use num_bigint::BigUint;
use std::collections::{BTreeMap, BTreeSet};
use crate::{gkr::Gate, sparse::Term, origin_score as score,
    origin_score_map::{Plan as ScorePlan, Profile, Mode, GuardPolicy},
    legacy_envelope_map::{Map, Binding, LowerSelector, LowerSource, LowerBranch},
    h21_row_support::{relocate, Family}};

const CUT:[u64;2]=[1827840,1827775];
const COUNT:[usize;2]=[1827838,1827775];
const MATURITY:[[u64;2];2]=[[43410,23155],[17867,9548]];
const HEIGHT:[usize;2]=[417791,845759];
const UPPER_OWNER:[usize;2]=[417789,845757];
const BASE:[usize;2]=[677501,685693];
const ROW_BASE:[usize;2]=[487421,502652];
const BOUNDARY:usize=845758;
const MODERN:usize=845759;
const SCHEDULE_D_BASE:usize=987674;
fn x(o:usize,q:usize)->usize{o*(1<<20)+q}
fn row(o:usize,q:usize)->usize{o*(1<<19)+q}

/// Frame identity is common; cuts and optional parent roots are per context.
/// None is explicitly a conditional descriptor with no native parent binding.
#[derive(Clone,Debug,PartialEq,Eq)]
pub(super) struct SourceIdentity {
    pub frame:[u8;32],pub cut:u64,pub parent_root:Option<[u8;32]>,
}
#[derive(Clone,Debug)]
pub(super) struct Endpoint {
    pub source:SourceIdentity,pub height:usize,pub owner:usize,pub local:usize,pub value:BigUint,
}
#[derive(Clone,Debug)]
pub(super) struct Inputs {pub endpoints:[[Endpoint;2];2],pub modern_w:BigUint,pub modern_v:[BigUint;2]}

#[derive(Clone,Debug)]
pub(super) struct Plan {bindings:[Binding;2],sources:[SourceIdentity;2],u:[BigUint;2]}
impl Plan {
    pub(super) fn new(maps:&[Map;2],sources:[SourceIdentity;2])->Result<Self,String>{
        score::bounds()?;
        let bindings=[maps[0].binding(),maps[1].binding()];
        if sources[0].frame!=sources[1].frame{return Err("different conditional frame identities".into());}
        for c in 0..2 {
            let mut expected=Map::new_modern_global_u_selected_lower(CUT[c],21,55,LowerSelector{
                source:LowerSource::HeaderDifficulty{height:841729},branch:LowerBranch::Pivot(54)})?.binding();
            // Prefix roots may differ. Each is checked against its own Map.
            expected.parent_root=bindings[c].parent_root;
            if bindings[c]!=expected || sources[c].cut!=CUT[c]
                || sources[c].parent_root!=bindings[c].parent_root {
                return Err("context Map/cut/parent/selected-source binding".into());
            }
        }
        let u=[maps[0].cap().to_biguint().ok_or("negative Map cap")?,
            maps[1].cap().to_biguint().ok_or("negative Map cap")?];
        // T<2^224, U<=2^64, m<2^16 imply A,B<2^224+2^80<2^225.
        // With R,d<2^225 and Boolean s, both integer residuals have |E|<2^227.
        let modulus=BigUint::from_bytes_le(&Fr::MODULUS.to_bytes_le());
        if modulus<=(BigUint::from(1u8)<<227usize) || u.iter().any(|n|n.is_zero()||*n>(BigUint::from(1u8)<<64usize))
            || MATURITY.iter().flatten().any(|m|*m>=1<<16){return Err("integer non-wrap profile".into());}
        Ok(Self{bindings,sources,u})
    }
    fn check_inputs(&self,input:&Inputs)->Result<(),String>{
        for c in 0..2 {for j in 0..2 {let e=&input.endpoints[c][j];
            if e.source!=self.sources[c] || e.height!=HEIGHT[j] || e.owner!=UPPER_OWNER[j]
                ||e.local!=987450 ||e.value.bits()>224 {return Err("typed endpoint source/height/physical Upper".into());}
            if input.endpoints[0][j].value!=e.value{return Err("shared frame Upper values differ".into());}
        }
            let t1=&input.endpoints[c][0].value;let t2=&input.endpoints[c][1].value;
            // Necessary for positive integer D over 427968 intervening heights;
            // this is not a proof of the full native WORKTREE relation.
            if t1>t2||t2-t1<BigUint::from(427968u64){return Err("conditional endpoint positive-work gap".into());}
        }
        if input.modern_w<=input.endpoints[0][1].value || input.modern_w.bits()>224
            ||input.modern_v.iter().any(|v|v.is_zero()||*v>(BigUint::from(1u8)<<64usize)){return Err("conditional modern input range".into());}
        Ok(())
    }
}

#[derive(Clone,Copy,Debug,PartialEq,Eq,PartialOrd,Ord)]
enum Writer {Zero,Upper(usize),Summary(usize),Modern(usize),Difficulty(usize),Scheduled(crate::h21_scheduled_max_cap::Writer)}
#[derive(Clone,Debug,PartialEq,Eq)]
struct Cell {writer:Writer,value:Fr}
#[derive(Clone,Debug,Default,PartialEq,Eq)]
struct SparseX {cells:BTreeMap<usize,Cell>}
impl SparseX {
    fn write(&mut self,o:usize,q:usize,w:Writer,bits:&[Fr])->Result<(),String>{
        if o>=1<<21||bits.is_empty()||q.checked_add(bits.len()).filter(|v|*v<=1<<20).is_none()
            ||bits.iter().any(|b|!b.is_zero()&&!b.is_one()){return Err("X range/bitness".into());}
        if (0..bits.len()).any(|k|self.cells.contains_key(&x(o,q+k))){return Err("duplicate X writer, including equal".into());}
        for (k,b) in bits.iter().enumerate(){self.cells.insert(x(o,q+k),Cell{writer:w,value:*b});}Ok(())
    }
    fn word(&mut self,o:usize,q:usize,width:usize,w:Writer,n:&BigUint)->Result<(),String>{
        if n.bits()>width as u64{return Err("X word overflow".into());}
        self.write(o,q,w,&(0..width).map(|k|Fr::from(u64::from(n.bit(k as u64)))).collect::<Vec<_>>())
    }
    fn word_read(&self,o:usize,q:usize,width:usize,w:Writer)->Result<BigUint,String>{
        let mut n=BigUint::from(0u8);for k in 0..width {
            let cell=self.cells.get(&x(o,q+k)).ok_or("missing X read")?;
            if cell.writer!=w||(!cell.value.is_zero()&&!cell.value.is_one()){return Err("X read writer/bitness".into());}
            if cell.value.is_one(){n+=BigUint::from(1u8)<<k;}
        }Ok(n)
    }
}
#[derive(Clone,Copy,Debug,PartialEq,Eq,PartialOrd,Ord)]
enum Relation {Summary(usize),Modern(usize),AliasW(usize),AliasV(usize),Scheduled(crate::h21_scheduled_max_cap::Writer)}
#[derive(Clone,Debug,PartialEq,Eq)]
struct Piece {relation:Relation,term:Term}
#[derive(Clone,Debug,PartialEq,Eq)]
pub(super) struct Staged {x:SparseX,terms:Vec<Piece>}
#[derive(Clone,Copy,Debug,PartialEq,Eq,PartialOrd,Ord)]
pub(super) enum ScoreCapRelation {
    ModernScore(usize),Cap(crate::h21_scheduled_max_cap::Writer),AliasW(usize),AliasV(usize),
}
#[derive(Clone,Debug,PartialEq,Eq)]
pub(super) struct ScoreCapRow {pub relation:ScoreCapRelation,pub term:Term}
#[derive(Clone,Debug,PartialEq,Eq)]
pub(super) struct ScoreCapXClaim {
    pub relation:ScoreCapRelation,pub owner:usize,pub start:usize,pub end:usize,
}
#[derive(Clone,Debug,PartialEq,Eq)]
pub(super) struct ScoreCapProjection {
    pub owner:usize,pub rows:Vec<ScoreCapRow>,pub x:Vec<ScoreCapXClaim>,
}

/// A value copied from a validated staged X cell. The tag is the writer that
/// actually populated the cell; a declared range alone never creates a value.
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(super) enum ScoreCapCellWriter {
    Zero,Upper(usize),Summary(usize),Modern(usize),Difficulty(usize),
    Scheduled(crate::h21_scheduled_max_cap::Writer),
}

#[derive(Clone,Debug,PartialEq,Eq)]
pub(super) struct ScoreCapXValue {
    address:usize,value:Fr,writer:ScoreCapCellWriter,
}
impl ScoreCapXValue {
    pub(super) fn address(&self)->usize {self.address}
    pub(super) fn value(&self)->Fr {self.value}
    pub(super) fn writer(&self)->ScoreCapCellWriter {self.writer}
}

/// Value-bearing counterpart to `ScoreCapProjection`. It is created only by
/// validating a complete session stage and contains the exact cells read or
/// written by the exported Score/Cap terms, plus their source metadata.
/// Frame authentication remains the responsibility of the producer of Plan.
#[derive(Clone,Debug)]
pub(super) struct ScoreCapValueProjection {
    structural:ScoreCapProjection,
    cells:Vec<ScoreCapXValue>,
    bindings:[Binding;2],
    sources:[SourceIdentity;2],
}
impl ScoreCapValueProjection {
    pub(super) fn owner(&self)->usize {self.structural.owner}
    pub(super) fn rows(&self)->&[ScoreCapRow] {&self.structural.rows}
    pub(super) fn x_claims(&self)->&[ScoreCapXClaim] {&self.structural.x}
    pub(super) fn cells(&self)->&[ScoreCapXValue] {&self.cells}
    pub(super) fn bindings(&self)->&[Binding;2] {&self.bindings}
    pub(super) fn sources(&self)->&[SourceIdentity;2] {&self.sources}
}

#[derive(Clone,Debug,Default,PartialEq,Eq)]
pub(super) struct Destination {published:Option<Staged>}
impl Destination {
    pub(super) fn boundary(&self,c:usize)->Result<BigUint,String>{
        if c>=2{return Err("context".into());}
        self.published.as_ref().ok_or("unpublished")?.x.word_read(BOUNDARY,BASE[c]+1318,225,Writer::Summary(c))
    }
    pub(super) fn max_running(&self,c:usize)->Result<BigUint,String>{
        if c>=2{return Err("context".into());}
        self.published.as_ref().ok_or("unpublished")?.x.word_read(844670,[999424,1000097][c],224,
            Writer::Scheduled(crate::h21_scheduled_max_cap::Writer::Max{context:c,end:844672}))
    }
}
fn modern_spec(c:usize)->Result<score::Spec,String>{
    let p=ScorePlan::new(1,COUNT[c],vec![Profile{mode:if c==0{Mode::Sampled}else{Mode::Exact},
        prefix:COUNT[c],expected:BigUint::from(0u8),guard:GuardPolicy::Disabled}])?;
    let s=p.spec(0,MODERN)?;
    if !s.active||!s.reducing||s.first||s.terminal||s.origin_one||s.empty_terminal
        ||s.maturity!=[4995,2090][c]||s.guard_total.is_some(){return Err("global first-modern Spec".into());}Ok(s)
}
fn gate(left:usize,right:usize,c0:Fr,c1:Fr,c2:Fr,c3:Fr)->Gate{Gate{left,right,c0,c1,c2,c3}}
fn scalar(n:&BigUint)->Fr{Fr::from_le_bytes_mod_order(&n.to_bytes_le())}
fn canonical(plan:&Plan)->Result<Vec<Piece>,String>{
    let mut terms=Vec::new();let one=Fr::one();let zero=Fr::zero();
    for c in 0..2 {
        let mut emit=|q:usize,g:Gate|terms.push(Piece{relation:Relation::Summary(c),term:Term{row:row(BOUNDARY,q),gate:g}});
        for k in 1318..=1768 {let a=x(BOUNDARY,BASE[c]+k);
            emit(ROW_BASE[c]+k,gate(a,a,zero,-one,zero,one));}
        let q1=ROW_BASE[c]+2801;let q2=q1+1;
        let a=scalar(&(&plan.u[c]*MATURITY[c][0]));let b=scalar(&(&plan.u[c]*MATURITY[c][1]));
        emit(q1,gate(0,0,b-a,zero,zero,zero));
        emit(q2,gate(0,0,-a,zero,zero,zero));
        let s=x(BOUNDARY,BASE[c]+1768);
        let mut weight=one;
        for k in 0..224 {
            emit(q1,gate(x(UPPER_OWNER[1],987450+k),0,zero,weight,zero,zero));
            emit(q1,gate(x(UPPER_OWNER[0],987450+k),0,zero,-weight,zero,zero));
            emit(q2,gate(x(UPPER_OWNER[0],987450+k),0,zero,-weight,zero,zero));weight+=weight;
        }
        let mut weight=one;for k in 0..225 {
            let d=x(BOUNDARY,BASE[c]+1543+k);let r=x(BOUNDARY,BASE[c]+1318+k);
            emit(q1,gate(d,s,zero,weight,zero,-Fr::from(2u8)*weight));
            emit(q2,gate(r,0,zero,weight,zero,zero));
            emit(q2,gate(d,s,zero,zero,zero,-weight));weight+=weight;
        }
        emit(q1,gate(s,0,zero,-one,zero,zero));emit(q2,gate(s,0,zero,-one,zero,zero));
        let mut error=None;
        score::emit_local(&modern_spec(c)?,|local|{
            let mut t=local.term;
            t.row=row(MODERN,425984+c*32768+t.row);
            t.gate.left=x(if local.previous{BOUNDARY}else{MODERN},BASE[c]+t.gate.left);
            t.gate.right=x(MODERN,BASE[c]+t.gate.right);
            match relocate(Family::Score(c),MODERN,&t){Ok(term)=>terms.push(Piece{relation:Relation::Modern(c),term}),Err(e)=>error=Some(e)}
        })?;if let Some(e)=error{return Err(e);}
    }Ok(terms)
}
fn canonical_session(plan:&Plan)->Result<Vec<Piece>,String>{
    let mut terms=canonical(plan)?;let one=Fr::one();let zero=Fr::zero();
    let schedule=crate::h21_scheduled_max_cap::Plan::new();
    schedule.visit_owner(844670,|writer,term| {
        if matches!(writer,crate::h21_scheduled_max_cap::Writer::Max{..}){
            terms.push(Piece{relation:Relation::Scheduled(writer),term});
        }Ok(())
    })?;
    schedule.visit_owner(MODERN,|writer,term| {
        if matches!(writer,crate::h21_scheduled_max_cap::Writer::Cap{..}){
            terms.push(Piece{relation:Relation::Scheduled(writer),term});
        }Ok(())
    })?;
    for c in 0..2 {for k in 0..224 {
        let q=438272+c*32768+k;
        for (left,c1) in [(x(MODERN,BASE[c]+k),one),(x(BOUNDARY,987450+k),-one)] {
            let term=Term{row:row(MODERN,q),gate:gate(left,0,zero,c1,zero,zero)};
            terms.push(Piece{relation:Relation::AliasW(c),term:relocate(Family::W(c),MODERN,&term)?});
        }
    }for k in 0..65 {
        let term=Term{row:row(MODERN,430192+c*32768+k),gate:gate(
            x(MODERN,BASE[c]+224+k),x(MODERN,[1000770,1002818][c]+740+k),zero,one,-one,zero)};
        terms.push(Piece{relation:Relation::AliasV(c),term:relocate(Family::V(c),MODERN,&term)?});
    }}Ok(terms)
}

/// Reuse the canonical conditional Summary emitter for a source-only ROW/X
/// lease probe. This exports terms, not values, parent custody or admission.
#[cfg(test)]
pub(super) fn summary_source_terms(plan:&Plan)->Result<Vec<(usize,Term)>,String>{
    Ok(canonical(plan)?.into_iter().filter_map(|piece|match piece.relation {
        Relation::Summary(context)=>Some((context,piece.term)),
        _=>None,
    }).collect())
}
fn shape()->BTreeMap<usize,Writer>{
    let mut s=BTreeMap::new();let mut add=|o,q,n,w|for k in 0..n{assert!(s.insert(x(o,q+k),w).is_none());};
    add(0,0,1,Writer::Zero);for j in 0..2{add(UPPER_OWNER[j],987450,224,Writer::Upper(j));}
    for c in 0..2{add(BOUNDARY,BASE[c]+1318,451,Writer::Summary(c));add(MODERN,BASE[c],2048,Writer::Modern(c));}s
}
fn stage(plan:&Plan,input:&Inputs)->Result<Staged,String>{
    plan.check_inputs(input)?;let mut sx=SparseX::default();sx.word(0,0,1,Writer::Zero,&BigUint::from(0u8))?;
    for j in 0..2{sx.word(UPPER_OWNER[j],987450,224,Writer::Upper(j),&input.endpoints[0][j].value)?;}
    for c in 0..2 {
        let a=&input.endpoints[c][0].value+&plan.u[c]*MATURITY[c][0];
        let b=&input.endpoints[c][1].value+&plan.u[c]*MATURITY[c][1];
        let rise=b>a;let r=if rise{b.clone()}else{a.clone()};let d=if rise{&b-&a-1u8}else{&a-&b};
        sx.word(BOUNDARY,BASE[c]+1318,225,Writer::Summary(c),&r)?;
        sx.word(BOUNDARY,BASE[c]+1543,225,Writer::Summary(c),&d)?;
        sx.word(BOUNDARY,BASE[c]+1768,1,Writer::Summary(c),&BigUint::from(u8::from(rise)))?;
        let previous=sx.word_read(BOUNDARY,BASE[c]+1318,225,Writer::Summary(c))?;
        let bits=score::produce(&modern_spec(c)?,Some(&score::ConditionalInputs{
            w:input.modern_w.clone(),v:input.modern_v[c].clone()}),&previous)?;
        sx.write(MODERN,BASE[c],Writer::Modern(c),&bits)?;
    }Ok(Staged{x:sx,terms:canonical(plan)?})
}
fn validate_with_terms(plan:&Plan,staged:&Staged,expected:Vec<Piece>,session:bool)->Result<(),String>{
    if session {
        let mut row_owners=BTreeMap::new();
        for p in &staged.terms {if let Some(old)=row_owners.insert(p.term.row,p.relation){
            if old!=p.relation{return Err("c146 semantic ROW owner collision".into());}
        }}
    }
    // Ordered full tuples, not only counts: even omitted zero aliases fail here.
    if staged.terms!=expected {return Err("census ordered complete terms".into());}
    let writers=staged.x.cells.iter().map(|(a,c)|(*a,c.writer)).collect::<BTreeMap<_,_>>();
    let mut expected_shape=shape();
    if session {for (owner,start,width,writer) in [
        (BOUNDARY,987450,224,Writer::Upper(2)),
        (844670,0,1,Writer::Zero),
        (844670,SCHEDULE_D_BASE,224,Writer::Difficulty(844672)),
        (844670,999424,673,Writer::Scheduled(crate::h21_scheduled_max_cap::Writer::Max{context:0,end:844672})),
        (844670,1000097,673,Writer::Scheduled(crate::h21_scheduled_max_cap::Writer::Max{context:1,end:844672})),
        (844798,999424,224,Writer::Scheduled(crate::h21_scheduled_max_cap::Writer::Max{context:0,end:844800})),
        (844798,1000097,224,Writer::Scheduled(crate::h21_scheduled_max_cap::Writer::Max{context:1,end:844800})),
        (MODERN,1000770,2048,Writer::Scheduled(crate::h21_scheduled_max_cap::Writer::Cap{context:0,origin:845760})),
        (MODERN,1002818,2048,Writer::Scheduled(crate::h21_scheduled_max_cap::Writer::Cap{context:1,origin:845760})),
    ] {for k in 0..width {if expected_shape.insert(x(owner,start+k),writer).is_some(){
        return Err("c146 session duplicate X writer including equal".into());
    }}}}
    if writers!=expected_shape{return Err("census X writer shape".into());}
    if staged.x.cells.values().any(|c|!c.value.is_zero()&&!c.value.is_one())||!staged.x.cells[&0].value.is_zero(){return Err("X bitness/zero".into());}
    let t1=staged.x.word_read(UPPER_OWNER[0],987450,224,Writer::Upper(0))?;
    let t2=staged.x.word_read(UPPER_OWNER[1],987450,224,Writer::Upper(1))?;
    if t1>t2||&t2-&t1<BigUint::from(427968u64){return Err("conditional endpoint positive-work gap".into());}
    let w0=staged.x.word_read(MODERN,BASE[0],224,Writer::Modern(0))?;
    let w1=staged.x.word_read(MODERN,BASE[1],224,Writer::Modern(1))?;
    if w0!=w1||w0<=t2{return Err("conditional shared modern positive work".into());}
    let mut writers=BTreeMap::new();let mut residual=BTreeMap::<usize,Fr>::new();
    for p in &staged.terms {
        if let Some(old)=writers.insert(p.term.row,p.relation){if old!=p.relation{return Err("cross-relation ROW writer".into());}}
        let g=&p.term.gate;
        let a=staged.x.cells.get(&g.left).ok_or("missing left X")?.value;
        let b=staged.x.cells.get(&g.right).ok_or("missing right X")?.value;
        *residual.entry(p.term.row).or_insert(Fr::zero())+=g.c0+g.c1*a+g.c2*b+g.c3*a*b;
    }
    if let Some((q,_))=residual.iter().find(|(_,v)|!v.is_zero()){return Err(format!("residual ROW {q}"));}Ok(())
}
fn validate(plan:&Plan,staged:&Staged)->Result<(),String>{validate_with_terms(plan,staged,canonical(plan)?,false)}
pub(super) fn validate_session(plan:&Plan,staged:&Staged)->Result<(),String>{
    validate_with_terms(plan,staged,canonical_session(plan)?,true)
}
/// Export only the owner-local modern Score and Cap join surface. Values,
/// aliases and the other owners remain with their source producers.
pub(super) fn project_local_score_cap(plan:&Plan,staged:&Staged)->Result<ScoreCapProjection,String>{
    validate_session(plan,staged)?;
    let mut rows=Vec::new();
    for piece in &staged.terms {match piece.relation {
        Relation::Modern(context)=>rows.push(ScoreCapRow{relation:ScoreCapRelation::ModernScore(context),term:piece.term.clone()}),
        Relation::Scheduled(crate::h21_scheduled_max_cap::Writer::Cap{context,origin})=>
            rows.push(ScoreCapRow{relation:ScoreCapRelation::Cap(crate::h21_scheduled_max_cap::Writer::Cap{context,origin}),term:piece.term.clone()}),
        Relation::AliasW(context)=>rows.push(ScoreCapRow{relation:ScoreCapRelation::AliasW(context),term:piece.term.clone()}),
        Relation::AliasV(context)=>rows.push(ScoreCapRow{relation:ScoreCapRelation::AliasV(context),term:piece.term.clone()}),
        _=>{}
    }}
    let mut x_claims=Vec::new();
    for context in 0..2 {
        let claims=[
            (ScoreCapRelation::ModernScore(context),MODERN,BASE[context],2048,Writer::Modern(context)),
            (ScoreCapRelation::Cap(crate::h21_scheduled_max_cap::Writer::Cap{context,origin:845760}),MODERN,
                [1000770,1002818][context],2048,Writer::Scheduled(crate::h21_scheduled_max_cap::Writer::Cap{context,origin:845760})),
        ];
        for (relation,owner,start,width,writer) in claims {
            if (start..start+width).any(|local|staged.x.cells.get(&x(owner,local)).map(|cell|cell.writer)!=Some(writer)) {
                return Err("c146 Score/Cap X source identity".into());
            }
            x_claims.push(ScoreCapXClaim{relation,owner,start:x(owner,start),end:x(owner,start+width)});
        }
    }
    Ok(ScoreCapProjection{owner:MODERN,rows,x:x_claims})
}

fn exported_writer(writer:Writer)->ScoreCapCellWriter {
    match writer {
        Writer::Zero=>ScoreCapCellWriter::Zero,
        Writer::Upper(context)=>ScoreCapCellWriter::Upper(context),
        Writer::Summary(context)=>ScoreCapCellWriter::Summary(context),
        Writer::Modern(context)=>ScoreCapCellWriter::Modern(context),
        Writer::Difficulty(owner)=>ScoreCapCellWriter::Difficulty(owner),
        Writer::Scheduled(writer)=>ScoreCapCellWriter::Scheduled(writer),
    }
}

/// Export the actual X support for the owner-local Score/Cap rows. Terms,
/// addresses, values, writer tags and source identities all come from this
/// Plan/Staged pair; callers cannot supply or relabel any of those claims.
pub(super) fn project_local_score_cap_values(
    plan:&Plan,staged:&Staged,
)->Result<ScoreCapValueProjection,String>{
    let structural=project_local_score_cap(plan,staged)?;
    let mut addresses=BTreeSet::new();
    for claim in &structural.rows {
        for address in [claim.term.gate.left,claim.term.gate.right] {
            if address >= (1usize<<41) {
                return Err("c146 Score/Cap X address outside canonical H21 space".into());
            }
            addresses.insert(address);
        }
    }
    for claim in &structural.x {
        let _=match claim.relation {
            ScoreCapRelation::ModernScore(context) if context<2 => Writer::Modern(context),
            ScoreCapRelation::Cap(crate::h21_scheduled_max_cap::Writer::Cap{context,origin})
                if context<2&&origin==MODERN+1 => Writer::Scheduled(
                    crate::h21_scheduled_max_cap::Writer::Cap{context,origin}),
            _=>return Err("c146 Score/Cap exported X claim relation".into()),
        };
        if claim.owner!=MODERN || claim.start>=claim.end || claim.end>(1usize<<41) {
            return Err("c146 Score/Cap exported X claim range".into());
        }
        addresses.extend(claim.start..claim.end);
    }
    let mut cells=Vec::with_capacity(addresses.len());
    for address in addresses {
        let cell=staged.x.cells.get(&address)
            .ok_or("c146 Score/Cap term X value missing from validated stage")?;
        if !cell.value.is_zero()&&!cell.value.is_one() {
            return Err("c146 Score/Cap exported X value is nonboolean".into());
        }
        cells.push(ScoreCapXValue {
            address,value:cell.value,writer:exported_writer(cell.writer),
        });
    }
    // Every declared output range must be backed by the corresponding staged
    // writer and every bit in it must be present in the value export.
    for claim in &structural.x {
        let expected=match claim.relation {
            ScoreCapRelation::ModernScore(context) if context<2 => Writer::Modern(context),
            ScoreCapRelation::Cap(crate::h21_scheduled_max_cap::Writer::Cap{context,origin})
                if context<2&&origin==MODERN+1 => Writer::Scheduled(
                    crate::h21_scheduled_max_cap::Writer::Cap{context,origin}),
            _=>return Err("c146 Score/Cap exported X claim relation".into()),
        };
        for address in claim.start..claim.end {
            let staged_cell=staged.x.cells.get(&address)
                .ok_or("c146 Score/Cap output X value missing from validated stage")?;
            if staged_cell.writer!=expected {
                return Err("c146 Score/Cap output X source/provenance mismatch".into());
            }
        }
    }
    Ok(ScoreCapValueProjection {
        structural,cells,bindings:plan.bindings.clone(),sources:plan.sources.clone(),
    })
}
#[cfg(test)]
pub(super) fn collide_row_owner_for_test(staged:&mut Staged){
    if let Some(piece)=staged.terms.iter_mut().find(|p|matches!(p.relation,
        Relation::Scheduled(crate::h21_scheduled_max_cap::Writer::Cap{..}))){
        piece.term.row=row(BOUNDARY,ROW_BASE[0]+2801);
    }
}
#[cfg(test)]
pub(super) fn flip_score_alias_for_test(staged:&mut Staged,context:usize,v:bool,bit:usize){
    if context<2&&bit<if v{65}else{224} {
        let local=BASE[context]+if v{224+bit}else{bit};
        if let Some(cell)=staged.x.cells.get_mut(&x(MODERN,local)){cell.value=Fr::one()-cell.value;}
    }
}
#[cfg(test)]
pub(super) fn alias_residual_for_test(staged:&Staged,context:usize,v:bool,bit:usize)->Result<(usize,Fr),String>{
    if context>=2||bit>=if v{65}else{224}{return Err("alias test coordinate".into());}
    let relation=if v{Relation::AliasV(context)}else{Relation::AliasW(context)};
    let address=x(MODERN,BASE[context]+if v{224+bit}else{bit});
    let touched=staged.terms.iter().find(|p|p.relation==relation
        &&(p.term.gate.left==address||p.term.gate.right==address)).ok_or("alias term missing")?;
    let row_address=touched.term.row;
    let mut residual=Fr::zero();
    for p in staged.terms.iter().filter(|p|p.relation==relation&&p.term.row==row_address){
        let g=&p.term.gate;
        let a=staged.x.cells.get(&g.left).ok_or("missing alias left X")?.value;
        let b=staged.x.cells.get(&g.right).ok_or("missing alias right X")?.value;
        residual+=g.c0+g.c1*a+g.c2*b+g.c3*a*b;
    }
    Ok((row_address,residual))
}
pub(super) fn stage_session(plan:&Plan,input:&Inputs,difficulty_d:&BigUint,
    max_patch:&crate::h21_scheduled_max_cap::Patch,
    lookahead_patch:&crate::h21_scheduled_max_cap::Patch,
    cap_patch:&crate::h21_scheduled_max_cap::Patch)->Result<Staged,String>{
    if difficulty_d.is_zero()||difficulty_d.bits()>224 {
        return Err("c146 session D source width/value mismatch".into());
    }
    let max_cells=max_patch.snapshot();let lookahead_cells=lookahead_patch.snapshot().into_iter().map(|(owner,start,writer,values)|{
        if values.len()<224 {return Err("c146 session MAX lookahead width mismatch".to_string());}
        Ok((owner,start,writer,values[..224].to_vec()))
    }).collect::<Result<Vec<_>,String>>()?;
    let cap_cells=cap_patch.snapshot();let mut claim=BTreeMap::new();
    for (owner,start,writer,values) in max_cells.iter().chain(lookahead_cells.iter()).chain(cap_cells.iter()){
        for k in 0..values.len(){if claim.insert((*owner,start+k),*writer).is_some(){
            return Err("c146 session duplicate X writer including equal".into());
        }}
    }
    let expected_max=vec![crate::h21_scheduled_max_cap::Writer::Max{context:0,end:844672},
        crate::h21_scheduled_max_cap::Writer::Max{context:1,end:844672}];
    let expected_cap=vec![crate::h21_scheduled_max_cap::Writer::Cap{context:0,origin:845760},
        crate::h21_scheduled_max_cap::Writer::Cap{context:1,origin:845760}];
    let expected_lookahead=vec![crate::h21_scheduled_max_cap::Writer::Max{context:0,end:844800},
        crate::h21_scheduled_max_cap::Writer::Max{context:1,end:844800}];
    if max_patch.writers()!=expected_max||lookahead_patch.writers()!=expected_lookahead
        ||cap_patch.writers()!=expected_cap||max_cells.iter().any(|(o,_,_,_)|*o!=844670)
        ||lookahead_cells.iter().any(|(o,_,_,_)|*o!=844798)||cap_cells.iter().any(|(o,_,_,_)|*o!=MODERN){
        return Err("c146 session MAX/Cap writer context/source mismatch".into());
    }
    let mut cap_values=BTreeMap::new();
    for (_,start,writer,values) in &cap_cells {
        let crate::h21_scheduled_max_cap::Writer::Cap{context,..}=writer else{
            return Err("c146 session Cap writer context/source mismatch".into());};
        if *context>=2||*start!=[1000770,1002818][*context]||values.len()!=2048{
            return Err("c146 session Cap writer context/source mismatch".into());}
        let mut value=BigUint::from(0u8);
        for (k,v) in values[740..805].iter().enumerate(){
            if !v.is_zero()&&!v.is_one(){return Err("c146 session nonboolean Cap alias".into());}
            if v.is_one(){value+=BigUint::from(1u8)<<k;}}
        cap_values.insert(*context,value);
    }
    if cap_values.len()!=2||cap_values.iter().any(|(c,v)|input.modern_v[*c]!=*v){
        return Err("c146 session Cap consumer value/source mismatch".into());}
    let mut staged=stage(plan,input)?;
    staged.x.write(BOUNDARY,987450,Writer::Upper(2),&(0..224).map(|k|Fr::from(u64::from(input.modern_w.bit(k)))).collect::<Vec<_>>())?;
    staged.x.word(844670,0,1,Writer::Zero,&BigUint::from(0u8))?;
    staged.x.word(844670,SCHEDULE_D_BASE,224,Writer::Difficulty(844672),difficulty_d)?;
    for (owner,start,writer,values) in max_cells.into_iter().chain(lookahead_cells).chain(cap_cells){
        staged.x.write(owner,start,Writer::Scheduled(writer),&values)?;
    }
    staged.terms=canonical_session(plan)?;Ok(staged)
}
pub(super) fn publish_session(plan:&Plan,destination:&mut Destination,staged:Staged)->Result<(),String>{
    if destination.published.is_some(){return Err("duplicate boundary publish".into());}
    validate_session(plan,&staged)?;destination.published=Some(staged);Ok(())
}
fn publish(plan:&Plan,destination:&mut Destination,staged:Staged)->Result<(),String>{
    if destination.published.is_some(){return Err("duplicate boundary publish".into());}
    validate(plan,&staged)?;destination.published=Some(staged);Ok(())
}
pub(super) fn join(plan:&Plan,destination:&mut Destination,input:&Inputs)->Result<(),String>{publish(plan,destination,stage(plan,input)?)}

#[cfg(test)]
#[path="score_prefix_r_anchor_tests.rs"]
mod tests;

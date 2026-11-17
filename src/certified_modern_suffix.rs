//! Bounded tagged positive-D -> suffix MAX -> all modern V ports.
//! Semantic/coefficient test interface only; no proof or native authentication.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use std::collections::BTreeSet;
use crate::{transcript::Transcript, wiring::{evaluate_shift, RightIndex}};

pub(crate) const FIRST:u64=844670;
pub(crate) const I0:u64=845760;
pub(crate) const N:u64=845824;
pub(crate) const ACTIVE:usize=1153;
pub(crate) const SLOTS:usize=2048;
pub(crate) const PORTS:usize=64;
pub(crate) const TERMS:u64=7246626;
pub(crate) const ROWS:u64=3851771;
pub(crate) const RANGES:[[u64;3];8]=[
    [987162,32,0],[987674,224,32],[987898,256,256],[988154,224,512],
    [999424,224,736],[999648,224,960],[999872,224,1184],[1000096,1,1408],
];
#[derive(Clone,Copy,Debug,PartialEq,Eq,PartialOrd,Ord)]
pub(crate) enum Wire {Native{owner:u64,local:u32},Cap{origin:u64,local:u32}}
impl Wire {
    pub(crate) fn owner(self)->u64{match self{Self::Native{owner,..}=>owner,Self::Cap{origin,..}=>origin}}
    pub(crate) fn local(self)->usize{match self{Self::Native{local,..}|Self::Cap{local,..}=>local as usize}}
    pub(crate) fn tag(self)->usize{usize::from(matches!(self,Self::Cap{..}))}
}
#[derive(Clone,Copy,Debug,PartialEq,Eq,PartialOrd,Ord)]
pub(crate) struct Row {pub(crate) family:u8,pub(crate) owner:u64,pub(crate) local:u32}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) struct Tuple {pub(crate) row:Row,pub(crate) left:Wire,pub(crate) right:Wire,pub(crate) c:[Fr;4]}
#[derive(Clone,Debug,PartialEq,Eq)]
pub(crate) enum Error {Descriptor(usize),Pin(usize),Range(usize),Port(usize),Roster,
    Framing,Coordinate,PointDimension,Residual(Row),TupleCount,TupleFields,Geometry,DeltaBound}
#[derive(Clone,Debug,PartialEq,Eq)]
pub(crate) struct Descriptor {pub(crate) fields:[u64;50],pub(crate) pins:[[u8;32];4],pub(crate) ranges:[[u64;3];8]}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) struct Port {pub(crate) fields:[u64;7]}
fn pin(s:&str)->[u8;32]{let mut out=[0;32];for (i,b) in out.iter_mut().enumerate(){*b=u8::from_str_radix(&s[2*i..2*i+2],16).expect("literal source pin");}out}
impl Descriptor {
    pub(crate) fn canonical()->Self{Self{
        fields:[1,1,I0,N,844672,FIRST,1153,2048,64,845823,20,20,2048,2048,4096,
            999424,673,736,1409,23,63,2048,1383,740,65,1838,1903,1,224,1383,224,
            1090,987674,224,0,64,0,1,0,1,2,3,2145,2242,448,6419,TERMS,393216,41,34],
        pins:[pin("F8F071C73405ED0CA430C38374212FE30089DE6E9BDA404D67D2329F190B0FBB"),
            pin("2E4F3EAFE5A7B41C6FE5B183E3A6F0AF026372AA23AC2661AE816BFD7B146BA2"),
            pin("1382740C3083A8A65C660B3D1F32A8D3787AC805A2AF6CD01144F7F43E484767"),
            pin("E798C2CAEE2AE15F02536C28C24505725EB21543651F57E5901A368F5C5156A4")],ranges:RANGES}}
}
pub(crate) fn ports()->Vec<Port>{let mut out=Vec::with_capacity(PORTS);for i in I0..I0+64{out.push(Port{fields:[i,i-1090,999424,224,1,740,65]});}out}
pub(crate) fn validate_descriptor(d:&Descriptor)->Result<(),Error>{let canonical=Descriptor::canonical();
    for i in 0..50{if d.fields[i]!=canonical.fields[i]{return Err(Error::Descriptor(i));}}
    for i in 0..4{if d.pins[i]!=canonical.pins[i]{return Err(Error::Pin(i));}}
    for i in 0..8{for j in 0..3{if d.ranges[i][j]!=canonical.ranges[i][j]{return Err(Error::Range(3*i+j));}}}Ok(())}
pub(crate) fn validate_ports(p:&[Port])->Result<(),Error>{if p.len()!=PORTS{return Err(Error::Roster);}
    for (i,p) in p.iter().enumerate(){if p.fields!=[I0+i as u64,I0+i as u64-1090,999424,224,1,740,65]{return Err(Error::Port(i));}}Ok(())}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) struct GeometryMath {pub(crate) first:u64,pub(crate) active:u64,pub(crate) slots:u64,pub(crate) ports:u64}
impl GeometryMath {
    pub(crate) fn from_interval(i0:u64,n:u64,lo:u64,hi:u64,owner_log:u32)->Result<Self,Error>{
        let lower=i0.checked_sub(1088).ok_or(Error::Geometry)?;
        let first=lower.checked_sub(2).ok_or(Error::Geometry)?;
        let active=n.checked_sub(lower).and_then(|x|x.checked_add(1)).ok_or(Error::Geometry)?;
        let slots=active.checked_add(1).and_then(u64::checked_next_power_of_two).ok_or(Error::Geometry)?;
        if owner_log>42||lo<i0||lo>=hi||hi>n||first.checked_add(slots).ok_or(Error::Geometry)?>(1u64<<owner_log){return Err(Error::Geometry);}
        Ok(Self{first,active,slots,ports:hi-lo})
    }
}
pub(crate) struct PackedSuffix {pub(crate) frames:Box<[u64]>,pub(crate) caps:Box<[u64]>}
impl PackedSuffix {
    pub(crate) fn zeroed()->Self{Self{frames:vec![0;SLOTS*23].into_boxed_slice(),caps:vec![0;PORTS*32].into_boxed_slice()}}
    pub(crate) fn framing(&self)->Result<(),Error>{
        if self.frames.len()!=47104||self.caps.len()!=2048{return Err(Error::Framing);}
        for frame in self.frames.chunks_exact(23){if frame[22]&!1u64!=0{return Err(Error::Framing);}}Ok(())
    }
    pub(crate) fn index(w:Wire)->Result<(bool,usize),Error>{match w{
        Wire::Native{owner,local}=>{if !(FIRST..FIRST+SLOTS as u64).contains(&owner){return Err(Error::Coordinate);}
            for [start,width,packed] in RANGES{if (start..start+width).contains(&(local as u64)){return Ok((false,(owner-FIRST) as usize*1472+packed as usize+local as usize-start as usize));}}
            Err(Error::Coordinate)},
        Wire::Cap{origin,local}=>{if !(I0..I0+64).contains(&origin)||local>=2048{return Err(Error::Coordinate);}
            Ok((true,(origin-I0) as usize*2048+local as usize))}}
    }
    pub(crate) fn read(&self,w:Wire)->Result<Fr,Error>{let (cap,index)=Self::index(w)?;let words=if cap{&self.caps}else{&self.frames};
        let word=words.get(index/64).ok_or(Error::Framing)?;Ok(Fr::from((word>>(index%64))&1))}
    pub(crate) fn set(&mut self,w:Wire,b:bool)->Result<(),Error>{let (cap,index)=Self::index(w)?;
        let words=if cap{&mut self.caps}else{&mut self.frames};let word=words.get_mut(index/64).ok_or(Error::Framing)?;
        *word=(*word&!(1u64<<(index%64)))|((b as u64)<<(index%64));Ok(())}
}
pub(crate) fn native(owner:u64,local:usize)->Wire{Wire::Native{owner,local:local as u32}}
pub(crate) fn cap(origin:u64,local:usize)->Wire{Wire::Cap{origin,local:local as u32}}
fn term(family:u8,owner:u64,row:usize,left:Wire,right:Wire,c:[Fr;4])->Tuple{Tuple{row:Row{family,owner,local:row as u32},left,right,c}}
fn mono(family:u8,owner:u64,row:usize,left:Wire,right:Wire,j:usize,c:Fr)->Tuple{let mut a=[Fr::zero();4];a[j]=c;term(family,owner,row,left,right,a)}
/// Native source row numbers and combined Boolean tuple order are preserved.
pub(crate) fn emit_decoder(owner:u64,active:bool,mut sink:impl FnMut(Tuple)){
    let one=Fr::one();let z=native(owner,0);
    if !active{let mut row=0;for [start,width,_] in RANGES[..4].iter().copied(){for b in 0..width{sink(mono(0,owner,row,native(owner,(start+b) as usize),z,1,one));row+=1;}}return;}
    for (row,wire,width) in [(0,987162,32),(480,987674,224),(704,988154,224),(928,987899,30)]{
        for b in 0..width{let w=native(owner,wire+b);sink(term(0,owner,row+b,w,w,[Fr::zero(),-one,Fr::zero(),one]));}}
    let mut row=958;for e in 0..256{if !(1..=30).contains(&e){sink(mono(0,owner,row,native(owner,987898+e),z,1,one));row+=1;}}
    sink(mono(0,owner,1184,z,z,0,-one));for e in 1..=30{sink(mono(0,owner,1184,native(owner,987898+e),z,1,one));}
    let mut p=one;for b in 0..8{sink(mono(0,owner,1185,native(owner,987186+b),z,1,p));p+=p;}
    for e in 1..=30{sink(mono(0,owner,1185,native(owner,987898+e),z,1,-Fr::from(e as u64)));}
    sink(mono(0,owner,1186,native(owner,987185),z,1,one));
    for b in 0..224{sink(mono(0,owner,1187+b,native(owner,987674+b),z,1,one));
        for e in 1..=30{let source=if e<3{b as isize+8*(3-e) as isize}else{b as isize-8*(e-3) as isize};
            if (0..23).contains(&source){sink(mono(0,owner,1187+b,native(owner,987898+e),native(owner,987162+source as usize),3,-one));}}}
    for (e,lo,start) in [(29,16,1411),(30,8,1418)]{for b in lo..23{sink(mono(0,owner,start+b-lo,native(owner,987898+e),native(owner,987162+b),3,one));}}
    sink(mono(0,owner,1433,z,z,0,-one));p=one;
    for b in 0..224{sink(mono(0,owner,1433,native(owner,987674+b),z,1,p));sink(mono(0,owner,1433,native(owner,988154+b),z,1,-p));p+=p;}
}
pub(crate) fn emit_max(owner:u64,active:bool,edge:bool,mut sink:impl FnMut(Tuple)){
    let one=Fr::one();let z=native(owner,0);
    for b in 0..673{let w=native(owner,999424+b);sink(if active{term(1,owner,b,w,w,[Fr::zero(),-one,Fr::zero(),one])}else{mono(1,owner,b,w,z,1,one)});}
    if active{let mut p=one;for b in 0..224{
        sink(mono(1,owner,673,native(owner,987674+b),z,1,p));
        sink(mono(1,owner,673,native(owner,999648+b),z,1,-p));
        sink(mono(1,owner,673,native(owner,999872+b),z,1,-p));p+=p;}
        sink(mono(1,owner,673,native(owner,1000096),z,1,p));
        for b in 0..224{let row=674+b;sink(mono(1,owner,row,native(owner,999424+b),z,1,one));
            sink(mono(1,owner,row,native(owner,987674+b),z,1,-one));
            sink(mono(1,owner,row,native(owner,1000096),native(owner,999648+b),3,-one));
            sink(mono(1,owner,row,native(owner,1000096),native(owner,987674+b),3,one));}}
    if edge{for b in 0..224{sink(mono(1,owner,898+b,native(owner-1,999648+b),z,1,one));sink(mono(1,owner,898+b,native(owner,999424+b),z,1,-one));}}
}
fn rail(origin:u64,row:usize,lo:usize,hi:usize,scale:Fr,sink:&mut impl FnMut(Tuple)){
    let mut p=scale;for w in lo..hi{sink(mono(2,origin,row,cap(origin,w),cap(origin,0),1,p));p+=p;}}
pub(crate) fn emit_cap(origin:u64,mut sink:impl FnMut(Tuple)){
    let one=Fr::one();let z=cap(origin,0);
    sink(mono(2,origin,0,z,z,1,one));
    for w in 1..1383{sink(mono(2,origin,w,cap(origin,w),z,1,-one));sink(mono(2,origin,w,cap(origin,w),cap(origin,w),3,one));}
    for b in 0..224{sink(mono(2,origin,1383+b,cap(origin,1+b),z,1,one));sink(mono(2,origin,1383+b,native(origin-1090,999424+b),z,1,-one));}
    for b in 0..224{sink(mono(2,origin,1607+b,cap(origin,225+b),z,1,one));sink(mono(2,origin,1607+b,cap(origin,1+b),z,1,-one));}
    sink(mono(2,origin,1831,z,z,0,-one));rail(origin,1831,225,449,one,&mut sink);rail(origin,1831,1159,1383,-one,&mut sink);
    rail(origin,1832,225,449,Fr::from(3u64),&mut sink);rail(origin,1832,449,674,-Fr::from(2u64),&mut sink);sink(mono(2,origin,1832,cap(origin,674),z,1,-one));
    sink(mono(2,origin,1833,z,z,0,-one));for w in 675..740{sink(mono(2,origin,1833,cap(origin,w),z,1,one));}
    rail(origin,1834,740,805,one,&mut sink);rail(origin,1834,675,740,-one,&mut sink);
    rail(origin,1835,805,869,one,&mut sink);rail(origin,1835,676,740,-one,&mut sink);
    rail(origin,1836,740,805,one,&mut sink);rail(origin,1836,449,674,-one,&mut sink);rail(origin,1836,869,934,-one,&mut sink);
    sink(mono(2,origin,1837,z,z,0,-one));rail(origin,1837,449,674,one,&mut sink);rail(origin,1837,805,869,-one,&mut sink);rail(origin,1837,934,1159,-one,&mut sink);
    for w in 1383..2048{sink(mono(2,origin,1903+w-1383,cap(origin,w),z,1,one));}
}
pub(crate) fn visit_all(mut sink:impl FnMut(Tuple)){
    for owner in FIRST..FIRST+SLOTS as u64{emit_decoder(owner,owner<FIRST+ACTIVE as u64,&mut sink);}
    for owner in FIRST..FIRST+SLOTS as u64{emit_max(owner,owner<FIRST+ACTIVE as u64,owner>FIRST&&owner<=FIRST+ACTIVE as u64,&mut sink);}
    for origin in I0..I0+64{emit_cap(origin,&mut sink);}
}
pub(crate) fn visit_row(row:Row,mut sink:impl FnMut(Tuple))->Result<(),Error>{
    let mut filter=|t:Tuple|{if t.row==row{sink(t);}};
    match row.family{
        0|1=>{if !(FIRST..FIRST+SLOTS as u64).contains(&row.owner)||row.local>=2048{return Err(Error::Coordinate);}
            if row.family==0{emit_decoder(row.owner,row.owner<FIRST+ACTIVE as u64,&mut filter);}else{emit_max(row.owner,row.owner<FIRST+ACTIVE as u64,row.owner>FIRST&&row.owner<=FIRST+ACTIVE as u64,&mut filter);}},
        2=>{if !(I0..I0+64).contains(&row.owner)||row.local>=4096{return Err(Error::Coordinate);}emit_cap(row.owner,&mut filter);},
        3=>{if row.owner>=(1<<20)||row.local>=4096{return Err(Error::Coordinate);}},_=>return Err(Error::Coordinate)}Ok(())
}
pub(crate) fn evaluate(t:Tuple,read:&mut impl FnMut(Wire)->Result<Fr,Error>)->Result<Fr,Error>{
    let mut out=t.c[0];let need_x=!t.c[1].is_zero()||!t.c[3].is_zero();let need_y=!t.c[2].is_zero()||!t.c[3].is_zero();
    let x=if need_x{read(t.left)?}else{Fr::zero()};let y=if need_y{read(t.right)?}else{Fr::zero()};
    if !t.c[1].is_zero(){out+=t.c[1]*x;}if !t.c[2].is_zero(){out+=t.c[2]*y;}if !t.c[3].is_zero(){out+=t.c[3]*x*y;}Ok(out)
}
#[derive(Clone,Copy,Debug,Default,PartialEq,Eq)]
pub(crate) struct Scan {pub(crate) terms:u64,pub(crate) rows:u64,pub(crate) channels:[u64;4]}
pub(crate) fn scan(read:&mut impl FnMut(Wire)->Result<Fr,Error>)->Result<Scan,Error>{
    let mut count=Scan::default();let mut previous=None;let mut residual=Fr::zero();let mut error=None;
    visit_all(|t|{if error.is_some(){return;}if previous!=Some(t.row){if let Some(r)=previous{if !residual.is_zero(){error=Some(Error::Residual(r));return;}}
            previous=Some(t.row);residual=Fr::zero();count.rows+=1;}
        count.terms+=1;for j in 0..4{count.channels[j]+=u64::from(!t.c[j].is_zero());}
        match evaluate(t,read){Ok(x)=>residual+=x,Err(e)=>error=Some(e)}});
    if let Some(e)=error{return Err(e);}if !residual.is_zero(){return Err(Error::Residual(previous.expect("emitted row")));}Ok(count)
}
pub(crate) struct AdmittedSuffix {descriptor:Descriptor,ports:Vec<Port>,packed:PackedSuffix,scan:Scan}
pub(crate) struct VRef<'a> {source:&'a AdmittedSuffix,origin:u64}
impl VRef<'_> {
    pub(crate) fn bit(&self,b:usize)->Result<Fr,Error>{if b>=65{return Err(Error::Coordinate);}self.source.read(cap(self.origin,740+b))}
}
impl AdmittedSuffix {
    pub(crate) fn new(d:Descriptor,p:Vec<Port>,packed:PackedSuffix)->Result<Self,Error>{
        validate_descriptor(&d)?;validate_ports(&p)?;crate::certified_modern_cap::bounds();packed.framing()?;
        let result=scan(&mut |w|packed.read(w))?;
        if result!= (Scan{terms:TERMS,rows:ROWS,channels:[2498,5871238,0,2736889]}){return Err(Error::TupleCount);}
        Ok(Self{descriptor:d,ports:p,packed,scan:result})
    }
    pub(crate) fn read(&self,w:Wire)->Result<Fr,Error>{self.packed.read(w)}
    pub(crate) fn packed(&self)->&PackedSuffix{&self.packed}
    pub(crate) fn counts(&self)->Scan{self.scan}
    pub(crate) fn visit_ports(&self,mut sink:impl FnMut(Port,VRef<'_>)){for p in &self.ports{sink(*p,VRef{source:self,origin:p.fields[0]});}}
    pub(crate) fn binding(&self)->Vec<u8>{let mut bytes=Vec::with_capacity(4331);bytes.extend_from_slice(b"certified-modern-suffix-v2\n");
        for x in self.descriptor.fields{bytes.extend_from_slice(&x.to_le_bytes());}for x in self.descriptor.pins{bytes.extend_from_slice(&x);}
        for range in self.descriptor.ranges{for x in range{bytes.extend_from_slice(&x.to_le_bytes());}}
        for p in &self.ports{for x in p.fields{bytes.extend_from_slice(&x.to_le_bytes());}}assert_eq!((bytes.len(),bytes.capacity()),(4331,4331));bytes}
    pub(crate) fn bind(&self,t:&mut Transcript){t.append_bytes(b"certified-modern-suffix-layout",&self.binding());}
    pub(crate) fn check_delta(&self,overrides:&[(Wire,Fr)])->Result<usize,Error>{
        // This private falsifier operates on one changed physical owner/cap. The
        // downstream next-owner/import rows are included, not supplied as advice.
        if overrides.len()>224{return Err(Error::DeltaBound);}
        if let Some((first,_))=overrides.first(){if overrides.iter().any(|(w,_)|w.owner()!=first.owner()||w.tag()!=first.tag()){return Err(Error::DeltaBound);}}
        let mut rows=BTreeSet::new();for (i,(wire,_)) in overrides.iter().enumerate(){PackedSuffix::index(*wire)?;
            if overrides[..i].iter().any(|(w,_)|w==wire){return Err(Error::Coordinate);}rows.extend(affected_rows(*wire)?);}
        if rows.len()>4096{return Err(Error::DeltaBound);}
        for row in &rows{let mut residual=Fr::zero();let mut error=None;visit_row(*row,|t|{
            match evaluate(t,&mut |w|overrides.iter().find(|(a,_)|*a==w).map(|(_,x)|Ok(*x)).unwrap_or_else(||self.read(w))){Ok(x)=>residual+=x,Err(e)=>error=Some(e)}})?;
            if let Some(e)=error{return Err(e);}if !residual.is_zero(){return Err(Error::Residual(*row));}}
        Ok(rows.len())
    }
}
/// Enumerate only the changed owner, its next neighbor and imported cap origin.
pub(crate) fn affected_rows(wire:Wire)->Result<BTreeSet<Row>,Error>{PackedSuffix::index(wire)?;let mut out=BTreeSet::new();
    let mut take=|t:Tuple|{if (t.left==wire&&(!t.c[1].is_zero()||!t.c[3].is_zero()))||(t.right==wire&&(!t.c[2].is_zero()||!t.c[3].is_zero())){out.insert(t.row);}};
    match wire{Wire::Native{owner,..}=>{
        emit_decoder(owner,owner<FIRST+ACTIVE as u64,&mut take);
        emit_max(owner,owner<FIRST+ACTIVE as u64,owner>FIRST&&owner<=FIRST+ACTIVE as u64,&mut take);
        if owner+1<=FIRST+ACTIVE as u64{emit_max(owner+1,owner+1<FIRST+ACTIVE as u64,true,&mut take);}
        if (I0..I0+64).contains(&(owner+1090)){emit_cap(owner+1090,&mut take);}},
        Wire::Cap{origin,..}=>emit_cap(origin,&mut take)}Ok(out)
}
pub(crate) fn eq(p:&[Fr],index:u64)->Fr{p.iter().enumerate().fold(Fr::one(),|a,(b,x)|a*if index>>b&1==1{*x}else{Fr::one()-x})}
pub(crate) fn native_keys()->Vec<usize>{let mut out=Vec::with_capacity(1410);out.push(0);for [start,width,_] in RANGES{out.extend((start..start+width).map(|x|x as usize));}out}
pub(crate) struct LocalWeights {pub(crate) rows:[Vec<Fr>;3],pub(crate) keys:Vec<usize>,pub(crate) native:[Vec<Fr>;2],pub(crate) cap:[Vec<Fr>;2]}
impl LocalWeights {
    pub(crate) fn new(r:&[Fr],u:&[Fr],v:&[Fr])->Result<Self,Error>{if (r.len(),u.len(),v.len())!=(34,41,41){return Err(Error::PointDimension);}
        let keys=native_keys();let rows=[(0..2048).map(|i|eq(&r[..12],i)).collect(),(0..2048).map(|i|eq(&r[..12],i)).collect(),(0..4096).map(|i|eq(&r[..12],i)).collect()];
        let native=[keys.iter().map(|i|eq(&u[..20],*i as u64)).collect(),keys.iter().map(|i|eq(&v[..20],*i as u64)).collect()];
        let cap=[(0..2048).map(|i|eq(&u[..20],i)).collect(),(0..2048).map(|i|eq(&v[..20],i)).collect()];Ok(Self{rows,keys,native,cap})
    }
    pub(crate) fn local(&self,t:Tuple)->Fr{let axis=|w:Wire,j:usize|if w.tag()==1{self.cap[j][w.local()]}else{self.native[j][self.keys.binary_search(&w.local()).expect("source retained native key")]};
        self.rows[t.row.family as usize][t.row.local as usize]*axis(t.left,0)*axis(t.right,1)}
    pub(crate) fn payload(&self)->usize{(self.rows.iter().map(Vec::capacity).sum::<usize>()+self.native.iter().map(Vec::capacity).sum::<usize>()+self.cap.iter().map(Vec::capacity).sum::<usize>())*32+self.keys.capacity()*8}
}
pub(crate) fn coefficients(d:&Descriptor,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],Error>{
    validate_descriptor(d)?;let weights=LocalWeights::new(r,u,v)?;
    let k=|offset,lo,hi|evaluate_shift(&r[12..32],&u[20..40],&v[20..40],offset,lo,hi,0,RightIndex::SameRow).map_err(|_|Error::Geometry);
    let active=k(0,FIRST,FIRST+ACTIVE as u64)?;let inactive=k(0,FIRST+ACTIVE as u64,FIRST+SLOTS as u64)?;
    let previous=k(1,FIRST+1,FIRST+ACTIVE as u64+1)?;let current=k(0,FIRST+1,FIRST+ACTIVE as u64+1)?;
    let ordinary=k(0,I0,I0+64)?;let imported=k(1090,I0,I0+64)?;
    let mut out=[Fr::zero();4];let mut add=|t:Tuple,owner:Fr|{let tags=eq(&r[32..34],t.row.family as u64)*eq(&u[40..],t.left.tag() as u64)*eq(&v[40..],t.right.tag() as u64);
        let w=weights.local(t)*owner*tags;for (x,c) in out.iter_mut().zip(t.c){*x+=w*c;}};
    emit_decoder(FIRST,true,|t|add(t,active));emit_decoder(FIRST,false,|t|add(t,inactive));
    emit_max(FIRST,true,false,|t|add(t,active));emit_max(FIRST,false,false,|t|add(t,inactive));
    emit_max(FIRST+1,false,true,|t|{if t.row.local>=898{add(t,if t.left.owner()==FIRST{previous}else{current});}});
    emit_cap(I0,|t|add(t,if t.left.tag()==0{imported}else{ordinary}));Ok(out)
}

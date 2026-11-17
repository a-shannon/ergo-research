//! Native projection remap and narrowly typed old-anchor replacement.
//! Local semantics/coefficient interface; no proof admission or authentication.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use crate::{certified_modern_suffix::eq, gkr::Gate, header_hash, serializer,
    serializer_field_projection, sparse::{Circuit, Term}, transcript::Transcript,
    wiring::{evaluate_shift, RightIndex}};

pub(crate) const FIRST:u64=844671;
pub(crate) const END:u64=845824;
pub(crate) const AUX:usize=655628;
pub(crate) const AUX_COUNT:usize=384;
pub(crate) const PROJECTION_ROWS:usize=1175;
pub(crate) const PROJECTION_TERMS:usize=2379;
pub(crate) const ROWS:usize=1207;
pub(crate) const TERMS:usize=2443;
pub(crate) const OLD_FIRST:usize=12836;
pub(crate) const OLD_END:usize=13220;
pub(crate) const OFFSET:usize=524288;
pub(crate) const WIDTH:usize=131072;
pub(crate) const N_BITS:usize=525650;
pub(crate) const DECODER:usize=987162;
pub(crate) const CHANNELS:[usize;4]=[1,1419,302,1897];

#[derive(Clone,Debug,PartialEq,Eq)]
pub(crate) enum Error {Descriptor(usize),Pin(usize),MapLength,Map(usize),PortLength,
    Port(usize),OldLength,Old(usize),Source,Projection(usize),Resource,Geometry,
    Framing,Padding(usize),Residual(usize),Alias(usize),Neighbor(usize),Coordinate,
    PointDimension}
#[derive(Clone,Debug,PartialEq,Eq)]
pub(crate) struct Descriptor {pub(crate) fields:[u64;20],pub(crate) pins:[[u8;32];7]}
fn pin(s:&str)->[u8;32]{let mut out=[0;32];for(i,b)in out.iter_mut().enumerate(){
    *b=u8::from_str_radix(&s[2*i..2*i+2],16).expect("literal source pin");}out}
impl Descriptor {pub(crate) fn canonical()->Self{Self{
    fields:[1,41,34,20,20,12,3,FIRST,END,AUX as u64,384,2379,1175,32,
        OLD_FIRST as u64,OLD_END as u64,19,12580,OFFSET as u64,DECODER as u64],
    pins:[pin("44123BCF2160A1785C6FB57FD6EBDA47195BFFFC30925409558EB8217C61DAF1"),
        pin("52C6D954F0E11EAE2749DCE34692941C457BEB50F598FFEED16848383071323A"),
        pin("CBED6254E4944FFD9EBA516D6CC882431ADD5DC0E2B58AC885BFDCC3470B7216"),
        pin("25A3D7401ABCC4546B3B2AC330368EF7BA80282F9B2864737AB0D01C34966FB0"),
        pin("60E7C61DD8FD6013E912D21825FDD8E365B230B65D963DB90158DDEF3A7222ED"),
        pin("7C0B197105F2B567B03BF3FA050ABED7CEE257C16BBA04B331FD4A8ECAA7CD12"),
        pin("9865DEF9F349BE8C63DE92CD8E0419480DAD1964C9AFCF7B2FE933003D99A751")]}}
    pub(crate) fn validate(&self)->Result<(),Error>{let c=Self::canonical();
        for i in 0..20{if self.fields[i]!=c.fields[i]{return Err(Error::Descriptor(i));}}
        for i in 0..7{if self.pins[i]!=c.pins[i]{return Err(Error::Pin(i));}}Ok(())}}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) struct Mapping {pub(crate) source:usize,pub(crate) target:usize}
pub(crate) fn mappings(used:usize)->[Mapping;384]{std::array::from_fn(|a|
    Mapping{source:used+a,target:AUX+a})}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) struct Alias {pub(crate) fields:[usize;5]}
pub(crate) fn aliases()->[Alias;32]{std::array::from_fn(|b|Alias{
    fields:[PROJECTION_ROWS+b,N_BITS+b,DECODER+b,0,1]})}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) struct OldBoundaryRow(pub(crate) usize);
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) struct Native {pub(crate) owner:u64,pub(crate) local:usize}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) struct Tuple {pub(crate) row:usize,pub(crate) left:Native,
    pub(crate) right:Native,pub(crate) c:[Fr;4]}
#[derive(Clone,Debug)]
pub(crate) struct Resources {pub(crate) core_terms:usize,pub(crate) core_capacity:usize,
    pub(crate) serializer_terms:usize,pub(crate) serializer_capacity:usize,
    pub(crate) boundary_terms:usize,pub(crate) boundary_capacity:usize,
    pub(crate) certificate_capacity:usize,pub(crate) projection_capacity:usize}

/// Owns genuine public source templates. Its fields are private: callers cannot
/// substitute a purported golden projection/serializer or old-row certificate.
pub(crate) struct Authority {serialized:serializer::Compiled,
    projected:serializer_field_projection::Compiled,certificate:Vec<Term>,resources:Resources}
impl Authority {
    pub(crate) fn build()->Result<Self,Error>{
        let joined=header_hash::build(None,[0;32]).map_err(|_|Error::Source)?;
        if joined.input.is_some() || joined.serializer.input.is_some()
            || joined.core.input_len!=65536 || joined.core.terms.len()>172864
            || joined.core.terms.capacity()>262144
            || joined.serializer.circuit.input_len!=WIDTH
            || joined.serializer.circuit.row_count!=262144
            || joined.serializer.circuit.terms.len()!=315546
            || joined.serializer.circuit.terms.capacity()>524288
            || joined.boundary.input_len!=1048576 || joined.boundary.row_count!=524288
            || joined.boundary.terms.len()!=419961 || joined.boundary.terms.capacity()>524288
            || joined.boundary_rows.global_padding!=(12580..405784){return Err(Error::Resource);}
        let mut certificate=Vec::with_capacity(386);
        for t in &joined.boundary.terms {if (OLD_FIRST-1..OLD_END+1).contains(&t.row){
            certificate.push(t.clone());}}
        if certificate.len()!=386 || certificate.capacity()!=386{return Err(Error::OldLength);}
        let mut resources=Resources{core_terms:joined.core.terms.len(),core_capacity:joined.core.terms.capacity(),
            serializer_terms:joined.serializer.circuit.terms.len(),serializer_capacity:joined.serializer.circuit.terms.capacity(),
            boundary_terms:joined.boundary.terms.len(),boundary_capacity:joined.boundary.terms.capacity(),
            certificate_capacity:certificate.capacity(),projection_capacity:0};
        let header_hash::Joined{serializer:serialized,core,boundary,input,compression_layout,
            selectors:_,remainder:_,boundary_rows:_}=joined;
        // Release the actual core and full old boundary before projection/assign.
        drop(core);drop(boundary);drop(input);drop(compression_layout);
        if serialized.layout.zero!=0 || serialized.layout.one!=1
            || serialized.stats.source_bits!=4088
            || serialized.layout.fields.timestamp!=std::array::from_fn(|b|1042+b)
            || serialized.layout.fields.n_bits!=std::array::from_fn(|b|1362+b)
            || serialized.layout.fields.height!=std::array::from_fn(|b|1394+b)
            || serialized.stats.used_input_bits.checked_add(384).filter(|x|*x<=WIDTH).is_none(){return Err(Error::Source);}
        let projected=serializer_field_projection::Compiled::build(&serialized).map_err(|_|Error::Source)?;
        if projected.residual_rows!=PROJECTION_ROWS || projected.circuit.terms.len()!=PROJECTION_TERMS
            || projected.circuit.row_count!=2048 || projected.circuit.input_len!=WIDTH
            || projected.circuit.terms.capacity()>4096{return Err(Error::Source);}
        let mut channels=[0usize;4];let mut previous=0;
        for t in &projected.circuit.terms {if t.row<previous || t.row>=PROJECTION_ROWS{return Err(Error::Source);}
            previous=t.row;for (j,c)in [t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3].iter().enumerate(){
                channels[j]+=usize::from(!c.is_zero());}}
        if channels!=CHANNELS{return Err(Error::Source);}
        resources.projection_capacity=projected.circuit.terms.capacity();
        Ok(Self{serialized,projected,certificate,resources})
    }
    pub(crate) fn serializer(&self)->&serializer::Compiled{&self.serialized}
    pub(crate) fn projection(&self)->&serializer_field_projection::Compiled{&self.projected}
    pub(crate) fn certificate(&self)->&[Term]{&self.certificate}
    pub(crate) fn resources(&self)->&Resources{&self.resources}
    pub(crate) fn used(&self)->usize{self.serialized.stats.used_input_bits}
    pub(crate) fn admit<'a>(&'a self,d:&Descriptor,map:&[Mapping],ports:&[Alias],
        old:&[Term],candidate:&Circuit)->Result<Layout<'a>,Error>{
        d.validate()?;
        if map.len()!=384{return Err(Error::MapLength);}
        for(i,m)in map.iter().enumerate(){if *m!=(Mapping{source:self.used()+i,target:AUX+i}){return Err(Error::Map(i));}}
        if ports.len()!=32{return Err(Error::PortLength);}
        let canonical=aliases();for(i,p)in ports.iter().enumerate(){if *p!=canonical[i]{return Err(Error::Port(i));}}
        if old.len()!=386{return Err(Error::OldLength);}
        for (i,t)in old.iter().enumerate(){let row=OLD_FIRST-1+i;let left=AUX-1+i;
            let expected=Term{row,gate:Gate{left,right:0,c0:Fr::zero(),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()}};
            if *t!=expected || *t!=self.certificate[i]{return Err(Error::Old(i));}}
        if candidate.input_len!=WIDTH || candidate.row_count!=2048
            || candidate.terms.len()!=PROJECTION_TERMS{return Err(Error::Source);}
        for (i,(x,y))in candidate.terms.iter().zip(&self.projected.circuit.terms).enumerate(){
            if x!=y{return Err(Error::Projection(i));}}
        Ok(Layout{authority:self})
    }
    /// The continuation cannot run until every source/layout certificate passes.
    pub(crate) fn admit_with<R>(&self,d:&Descriptor,map:&[Mapping],ports:&[Alias],
        old:&[Term],candidate:&Circuit,then:impl FnOnce(Layout<'_>)->R)->Result<R,Error>{
        let layout=self.admit(d,map,ports,old,candidate)?;Ok(then(layout))}
}

#[derive(Clone,Copy)]
pub(crate) struct Layout<'a>{authority:&'a Authority}
impl<'a> Layout<'a>{
    pub(crate) fn used(self)->usize{self.authority.used()}
    pub(crate) fn mapped(self,w:usize)->Result<usize,Error>{if w>=WIDTH{return Err(Error::Coordinate);}
        Ok(if (self.used()..self.used()+384).contains(&w){AUX+w-self.used()}else{OFFSET+w})}
    pub(crate) fn retain_old(self,owner:u64,row:OldBoundaryRow)->bool{
        !(FIRST<=owner && owner<END && (OLD_FIRST..OLD_END).contains(&row.0))}
    pub(crate) fn visit_row(self,owner:u64,row:usize,mut emit:impl FnMut(Tuple))->Result<(),Error>{
        if owner>=1<<20 || row>=4096{return Err(Error::Geometry);}
        if !(FIRST..END).contains(&owner) || row>=ROWS{return Ok(());}
        if row<PROJECTION_ROWS{let terms=&self.authority.projected.circuit.terms;
            let lo=terms.partition_point(|t|t.row<row);let hi=terms.partition_point(|t|t.row<=row);
            for t in &terms[lo..hi]{emit(Tuple{row,left:Native{owner,local:self.mapped(t.gate.left)?},
                right:Native{owner,local:self.mapped(t.gate.right)?},
                c:[t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3]});}}
        else {let b=row-PROJECTION_ROWS;emit(Tuple{row,left:Native{owner,local:N_BITS+b},
            right:Native{owner,local:0},c:[Fr::zero(),Fr::one(),Fr::zero(),Fr::zero()]});
            emit(Tuple{row,left:Native{owner:owner-1,local:DECODER+b},right:Native{owner,local:0},
                c:[Fr::zero(),-Fr::one(),Fr::zero(),Fr::zero()]});}Ok(())}
    /// Sorted source streaming shares exact tuple evaluation with sparse faults.
    pub(crate) fn check(self,owner:u64,read:&impl Fn(Native)->Result<Fr,Error>)->Result<(),Error>{
        if !(FIRST..END).contains(&owner){return Err(Error::Geometry);}
        let mut row=0;let mut residual=Fr::zero();
        for t in &self.authority.projected.circuit.terms{
            if t.row!=row{if !residual.is_zero(){return Err(Error::Residual(row));}row=t.row;residual=Fr::zero();}
            let x=Tuple{row:t.row,left:Native{owner,local:self.mapped(t.gate.left)?},
                right:Native{owner,local:self.mapped(t.gate.right)?},c:[t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3]};
            residual+=evaluate(x,read)?;}
        if !residual.is_zero(){return Err(Error::Residual(row));}
        for b in 0..32{if read(Native{owner,local:N_BITS+b})?!=read(Native{owner:owner-1,local:DECODER+b})?{
            return Err(Error::Alias(b));}}
        for (i,local)in [AUX-1,AUX+384].iter().enumerate(){if !read(Native{owner,local:*local})?.is_zero(){
            return Err(Error::Neighbor(i));}}Ok(())}
    pub(crate) fn residual(self,owner:u64,row:usize,read:&impl Fn(Native)->Result<Fr,Error>)->Result<Fr,Error>{
        let mut residual=Fr::zero();let mut failure=None;
        self.visit_row(owner,row,|t|match evaluate(t,read){Ok(x)=>residual+=x,Err(e)=>failure=Some(e)})?;
        if let Some(e)=failure{return Err(e);}Ok(residual)}
    pub(crate) fn coefficients(self,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],Error>{
        if r.len()!=34 || u.len()!=41 || v.len()!=41{return Err(Error::PointDimension);}
        let k=|offset|evaluate_shift(&r[12..32],&u[20..40],&v[20..40],offset,FIRST,END,0,RightIndex::SameRow)
            .map_err(|_|Error::Geometry);
        let k0=k(0)?;let k1=k(1)?;
        let scale=(Fr::one()-u[40])*(Fr::one()-v[40])*eq(&r[32..34],3);
        let mut out=[Fr::zero();4];
        for t in &self.authority.projected.circuit.terms{let weight=eq(&r[..12],t.row as u64)
            *eq(&u[..20],self.mapped(t.gate.left)? as u64)*eq(&v[..20],self.mapped(t.gate.right)? as u64)*k0;
            for(j,c)in [t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3].iter().enumerate(){out[j]+=weight*c;}}
        for b in 0..32{out[1]+=eq(&r[..12],(PROJECTION_ROWS+b)as u64)*eq(&v[..20],0)
            *(k0*eq(&u[..20],(N_BITS+b)as u64)-k1*eq(&u[..20],(DECODER+b)as u64));}
        for x in &mut out{*x*=scale;}Ok(out)}
    pub(crate) fn retired_coefficients(self,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],Error>{
        if r.len()!=39 || u.len()!=41 || v.len()!=41{return Err(Error::PointDimension);}
        let k=evaluate_shift(&r[19..39],&u[20..40],&v[20..40],0,FIRST,END,0,RightIndex::SameRow)
            .map_err(|_|Error::Geometry)?;
        let mut c=Fr::zero();for a in 0..384{c+=eq(&r[..19],(OLD_FIRST+a)as u64)*eq(&u[..20],(AUX+a)as u64);}
        Ok([Fr::zero(),c*k*eq(&v[..20],0)*(Fr::one()-u[40])*(Fr::one()-v[40]),Fr::zero(),Fr::zero()])}
}
pub(crate) fn evaluate(t:Tuple,read:&impl Fn(Native)->Result<Fr,Error>)->Result<Fr,Error>{
    let left=if t.c[1].is_zero() && t.c[3].is_zero(){Fr::zero()}else{read(t.left)?};
    let right=if t.c[2].is_zero() && t.c[3].is_zero(){Fr::zero()}else{read(t.right)?};
    Ok(t.c[0]+t.c[1]*left+t.c[2]*right+t.c[3]*left*right)}

/// Borrowed rails; formal placeholders never create another witness array.
pub(crate) struct BorrowedWitness<'a>{pub(crate) owner:u64,pub(crate) original:&'a [Fr],
    pub(crate) projected:&'a [Fr],pub(crate) decoder:&'a [Fr;32],pub(crate) neighbors:&'a [Fr;2]}
impl BorrowedWitness<'_>{pub(crate) fn read(&self,layout:Layout<'_>,wire:Native)->Result<Fr,Error>{
    if wire.owner==self.owner{if (AUX..AUX+384).contains(&wire.local){return Ok(self.projected[layout.used()+wire.local-AUX]);}
        if (OFFSET..OFFSET+WIDTH).contains(&wire.local){return Ok(self.original[wire.local-OFFSET]);}
        if wire.local==AUX-1{return Ok(self.neighbors[0]);}if wire.local==AUX+384{return Ok(self.neighbors[1]);}}
    if wire.owner.checked_add(1)==Some(self.owner) && (DECODER..DECODER+32).contains(&wire.local){return Ok(self.decoder[wire.local-DECODER]);}
    Err(Error::Coordinate)}}
pub(crate) struct Admitted<'a>{layout:Layout<'a>,witness:BorrowedWitness<'a>}
impl<'a> Admitted<'a>{pub(crate) fn new(layout:Layout<'a>,witness:BorrowedWitness<'a>)->Result<Self,Error>{
    if witness.original.len()!=WIDTH || witness.projected.len()!=WIDTH{return Err(Error::Framing);}
    if !(FIRST..END).contains(&witness.owner){return Err(Error::Geometry);}
    for (a,x)in witness.original[layout.used()..].iter().enumerate(){if !x.is_zero(){return Err(Error::Padding(layout.used()+a));}}
    layout.check(witness.owner,&|w|witness.read(layout,w))?;Ok(Self{layout,witness})}
    pub(crate) fn bit(&self,b:usize)->Result<&Fr,Error>{if b>=32{return Err(Error::Coordinate);}
        Ok(&self.witness.original[1362+b])}
    pub(crate) fn binding(&self)->Vec<u8>{let d=Descriptor::canonical();
        let prefix=b"projection-aux-retirement-v1\n";let mut bytes=Vec::with_capacity(prefix.len()+400);
        bytes.extend_from_slice(prefix);for f in d.fields{bytes.extend_from_slice(&f.to_le_bytes());}
        for p in d.pins{bytes.extend_from_slice(&p);}bytes.extend_from_slice(&(self.layout.used()as u64).to_le_bytes());
        bytes.extend_from_slice(&self.witness.owner.to_le_bytes());bytes}
    pub(crate) fn bind(&self,t:&mut Transcript){t.append_bytes(b"projection-aux-retirement-layout",&self.binding());}}

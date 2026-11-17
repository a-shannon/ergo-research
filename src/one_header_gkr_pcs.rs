//! Bounded TEST diagnostic: genuine serializer/projection -> sparse claim -> PCS.
//! Compact tail values are committed but not constrained by extra zero anchors.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use crate::{gkr::Gate, pcs, projection_aux_retirement as source,
    sparse::{Circuit, Term}, transcript::Transcript};
use serde::{Deserialize, Serialize};

pub(crate) const N: usize = 262144;
pub(crate) const R: usize = 524288;
pub(crate) const TERMS: usize = 317991;
pub(crate) const INPUT_USED: usize = 131491;
pub(crate) const ROWS_USED: usize = 263353;
pub(crate) const OWNER: u64 = 844671;
pub(crate) const PROJECTION: usize = 262144;
pub(crate) const ALIASES: usize = 263319;
pub(crate) const NEIGHBORS: usize = 263351;
pub(crate) const AUX: usize = 131072;
pub(crate) const DECODER: usize = 131456;
pub(crate) const NEIGHBOR_INPUT: usize = 131488;
pub(crate) const FORMAL: usize = 131490;
pub(crate) const DOMAIN: &[u8] = b"one-header-gkr-pcs-test-diagnostic-v1";
pub(crate) const KEY: &[u8] = include_bytes!("../fixtures/verifier-keys-v1/log18.vk");

pub(crate) const fn hex<const L: usize>(s: &str) -> [u8; L] {
    const fn digit(b: u8) -> u8 { match b {
        b'0'..=b'9' => b-b'0', b'a'..=b'f' => b-b'a'+10,
        b'A'..=b'F' => b-b'A'+10, _ => panic!("hex digit"),
    }}
    assert!(s.len() == 2*L);
    let b=s.as_bytes(); let mut out=[0; L]; let mut i=0;
    while i<L { out[i]=16*digit(b[2*i])+digit(b[2*i+1]); i+=1; } out
}
pub(crate) const SETUP_ID: [u8;32] = hex("0eb06acc69c9a222000e3ab4640ea3892e587612011e9140464e25ef57e31d3a");
const PINS: [[u8;32];8] = [
    hex("44123BCF2160A1785C6FB57FD6EBDA47195BFFFC30925409558EB8217C61DAF1"),
    hex("52C6D954F0E11EAE2749DCE34692941C457BEB50F598FFEED16848383071323A"),
    hex("CBED6254E4944FFD9EBA516D6CC882431ADD5DC0E2B58AC885BFDCC3470B7216"),
    hex("2D1EBCFD0814E39F7BEB81142363910233B7B6713A749956C5F961F96A33E693"),
    hex("7C0B197105F2B567B03BF3FA050ABED7CEE257C16BBA04B331FD4A8ECAA7CD12"),
    hex("9865DEF9F349BE8C63DE92CD8E0419480DAD1964C9AFCF7B2FE933003D99A751"),
    hex("0D3DF707CC5FDDDC52758D8809217DDD4ADE28548C448C7FCD65983196C4116C"),
    hex("D50F935A5471A6478F20F039A0CE12F0644043D60282C83706D36C2BC150F0BA"),
];

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Descriptor { pub(crate) words: [u64;36], pub(crate) pins: [[u8;32];8] }
impl Descriptor {
    pub(crate) fn canonical(a: &source::Authority) -> Self {
        Self { words: [1,18,19,0,844671,131072,262144,315546,a.used() as u64,
            384,131072,131456,32,131488,2,131490,131491,262144,1175,2379,
            263319,32,64,263351,2,317991,263353,12836,13220,524288,
            655628,525650,987162,844671,845824,18], pins: PINS }
    }
    pub(crate) fn bytes(&self) -> [u8;584] {
        let mut out=[0;584];
        for (i,w) in self.words.iter().enumerate() { out[i*8..i*8+8].copy_from_slice(&w.to_le_bytes()); }
        for (i,p) in self.pins.iter().enumerate() { out[288+i*32..320+i*32].copy_from_slice(p); }
        assert_eq!(pcs::VENDOR_PIN.len(),40); out[544..].copy_from_slice(pcs::VENDOR_PIN); out
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Error {
    Word(usize), Pin(usize), Setup(usize), Placement(usize), PlacementLength,
    Rows(usize), RowLength, Source, Axis(usize), Framing, Residual(usize), Commitment,
}
pub(crate) fn placements() -> [usize;419] {
    std::array::from_fn(|i| if i<384 {AUX+i} else if i<416 {DECODER+i-384}
        else if i<418 {NEIGHBOR_INPUT+i-416} else {FORMAL})
}
pub(crate) fn rows() -> [usize;9] { [0,262143,262144,263318,263319,263350,263351,263352,263353] }

/// Cheap admission is deliberately separate from the one source materialization.
/// Every metadata negative can therefore reach the real boundary with empty X.
pub(crate) fn with_input<T>(a: &source::Authority, d: &Descriptor, p: &[usize],
    row: &[usize], id: &[u8;32], x: &[Fr], then: impl FnOnce()->T) -> Result<T,Error> {
    validate_metadata(a,d,p,row,id)?;
    if x.len()!=N { return Err(Error::Framing); }
    Ok(then())
}
pub(crate) fn validate_metadata(a: &source::Authority,d: &Descriptor,p: &[usize],
    row: &[usize],id: &[u8;32]) -> Result<(),Error> {
    let expected=Descriptor::canonical(a);
    for i in 0..36 { if d.words[i]!=expected.words[i] { return Err(Error::Word(i)); } }
    for i in 0..8 { if d.pins[i]!=PINS[i] { return Err(Error::Pin(i)); } }
    for i in 0..32 { if id[i]!=SETUP_ID[i] { return Err(Error::Setup(i)); } }
    if p.len()!=419 { return Err(Error::PlacementLength); }
    for (i,w) in p.iter().enumerate() { if *w!=placements()[i] { return Err(Error::Placement(i)); } }
    if row.len()!=9 { return Err(Error::RowLength); }
    for (i,w) in row.iter().enumerate() { if *w!=rows()[i] { return Err(Error::Rows(i)); } }
    Ok(())
}

fn projection_axis(a: &source::Authority,w: usize) -> Result<usize,Error> {
    if w<a.used() { Ok(w) }
    else if w<a.used()+384 { Ok(AUX+w-a.used()) }
    else { Err(Error::Axis(w)) }
}
fn mapped_projection(a: &source::Authority,t: &Term) -> Result<Term,Error> {
    let mut out=t.clone();
    if t.row>=1175 { return Err(Error::Source); }
    out.row+=PROJECTION; out.gate.left=projection_axis(a,t.gate.left)?;
    out.gate.right=projection_axis(a,t.gate.right)?; Ok(out)
}
pub(crate) fn visit_terms(a: &source::Authority, mut emit: impl FnMut(Term)) -> Result<(),Error> {
    let s=&a.serializer().circuit; let q=&a.projection().circuit;
    if s.input_len!=131072 || s.row_count!=262144 || s.terms.len()!=315546
        || q.input_len!=131072 || q.row_count!=2048 || q.terms.len()!=2379
        || a.certificate().len()!=386 { return Err(Error::Source); }
    // Genuine source certificate and predecessor all-axis map are admitted here.
    a.admit(&source::Descriptor::canonical(),&source::mappings(a.used()),
        &source::aliases(),a.certificate(),q).map_err(|_|Error::Source)?;
    let mut previous=0;
    for t in &s.terms {
        if t.row<previous || t.row>=PROJECTION || t.gate.left>=131072 || t.gate.right>=131072 {
            return Err(Error::Source);
        } previous=t.row; emit(t.clone());
    }
    previous=0; let mut channels=[0usize;4];
    for t in &q.terms {
        if t.row<previous { return Err(Error::Source); } previous=t.row;
        for (i,c) in [t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3].iter().enumerate() {
            channels[i]+=usize::from(!c.is_zero());
        }
        emit(mapped_projection(a,t)?);
    }
    if channels!=[1,1419,302,1897] { return Err(Error::Source); }
    for b in 0..32 {
        for (left,c1) in [(1362+b,Fr::one()),(DECODER+b,-Fr::one())] {
            emit(Term { row:ALIASES+b,gate:Gate{left,right:FORMAL,c0:Fr::zero(),c1,c2:Fr::zero(),c3:Fr::zero()} });
        }
    }
    for (i,j) in [0,385].into_iter().enumerate() {
        let mut t=a.certificate()[j].clone();
        // Preserve the genuine coefficient tuple and both formal axes.
        t.row=NEIGHBORS+i; t.gate.left=NEIGHBOR_INPUT+i; t.gate.right=FORMAL; emit(t);
    } Ok(())
}

pub(crate) struct Compact { descriptor: Descriptor, circuit: Circuit }
impl Compact {
    pub(crate) fn build(a: &source::Authority,d: &Descriptor,p: &[usize],r: &[usize],
        id: &[u8;32]) -> Result<Self,Error> {
        validate_metadata(a,d,p,r,id)?;
        let mut terms=Vec::with_capacity(TERMS);
        visit_terms(a,|t| terms.push(t))?;
        if terms.len()!=TERMS || terms.capacity()!=TERMS { return Err(Error::Source); }
        let circuit=Circuit{input_len:N,row_count:R,terms};
        crate::sparse::validate(&circuit,0).map_err(|_|Error::Source)?;
        Ok(Self{descriptor:d.clone(),circuit})
    }
    pub(crate) fn circuit(&self)->&Circuit { &self.circuit }
    pub(crate) fn descriptor(&self)->&Descriptor { &self.descriptor }
    pub(crate) fn check(&self,x: &[Fr])->Result<(),Error> {
        if x.len()!=N { return Err(Error::Framing); }
        let mut row=0; let mut value=Fr::zero();
        for t in &self.circuit.terms {
            if t.row!=row { if !value.is_zero() { return Err(Error::Residual(row)); }
                row=t.row;value=Fr::zero(); }
            value+=t.gate.evaluate(x);
        }
        if !value.is_zero() { return Err(Error::Residual(row)); } Ok(())
    }
    pub(crate) fn statement(&self,id: [u8;32],bytes: &[u8],expected: &[u8])->Result<Statement,Error> {
        for i in 0..32 { if id[i]!=SETUP_ID[i] { return Err(Error::Setup(i)); } }
        if bytes!=expected || bytes.len()!=384 || pcs::decode_commitment(bytes).is_err() {
            return Err(Error::Commitment);
        }
        let commitment: [u8;384]=bytes.try_into().map_err(|_|Error::Commitment)?;
        Ok(Statement{descriptor:self.descriptor.bytes(),id,commitment})
    }
}
pub(crate) struct Statement { descriptor: [u8;584], id: [u8;32], commitment: [u8;384] }
impl Statement {
    pub(crate) fn transcript(&self)->Transcript {
        let mut t=Transcript::new(DOMAIN);
        t.append_bytes(b"compact-descriptor",&self.descriptor);
        t.append_bytes(b"compact-setup",&self.id);
        t.append_bytes(b"compact-commitment",&self.commitment); t
    }
    pub(crate) fn commitment(&self)->dory_pcs::backends::arkworks::ArkGT {
        pcs::decode_commitment(&self.commitment).expect("admitted canonical commitment")
    }
}

pub(crate) fn assign(a: &source::Authority,f: &crate::serializer::Fields)->Result<Vec<Fr>,Error> {
    let original=a.serializer().assign(f);
    let projected=a.projection().assign(&original).map_err(|_|Error::Source)?;
    if original.len()!=131072 || original.capacity()!=131072
        || projected.len()!=131072 || projected.capacity()!=131072 { return Err(Error::Framing); }
    let mut x=vec![Fr::zero();N];
    x[..131072].copy_from_slice(&original);
    x[AUX..DECODER].copy_from_slice(&projected[a.used()..a.used()+384]);
    x[DECODER..NEIGHBOR_INPUT].copy_from_slice(&original[1362..1394]);
    // Neighbors, distinct formal Native0 and unconstrained tail start at zero.
    drop(projected); drop(original); Ok(x)
}

#[derive(Serialize,Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct Timings {
    pub setup:u64,pub commit:u64,pub gkr_prove:u64,pub gkr_codec:u64,pub gkr_verify:u64,
    pub pcs_open:u64,pub pcs_codec:u64,pub key_admit:u64,pub pcs_verify:u64,
    pub snapshot_commit:u64,pub snapshot_open:u64,
}
#[derive(Serialize,Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct Capacities {
    pub compact_input:usize,pub compact_terms:usize,pub serializer_terms:usize,
    pub projection_terms:usize,pub certificate_terms:usize,pub committed_rows:usize,
    pub fr_size:usize,pub term_size:usize,pub g1_size:usize,pub g2_size:usize,pub gt_size:usize,
}
#[derive(Serialize,Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct Modeled {
    pub source_compile_peak:usize,pub source_retained:usize,pub sparse_fr_peak:usize,
    pub pairing_scratch:usize,pub msm_scratch:usize,pub dory_state:usize,
    pub codec_setup_scratch:usize,pub payload_ceiling:usize,
}
#[derive(Serialize,Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct Verdicts {
    pub ordinary:bool,pub pipeline:bool,pub snapshot_reject:bool,pub metadata:bool,
    pub compact_mapping:bool,pub wiring:bool,pub codec:bool,
}
#[derive(Serialize,Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct Diagnostic {
    pub schema:String,pub status:String,pub proof:bool,pub pcs:bool,pub setup:bool,
    pub log_n:usize,pub row_log:usize,pub log_copies:usize,pub terms:usize,
    pub input_used:usize,pub input_extent:usize,pub rows_used:usize,pub row_extent:usize,
    pub gkr_challenges:u64,pub gkr_scalars:usize,pub gkr_bytes:usize,pub dory_rounds:usize,
    pub dory_bytes:usize,pub commitment_bytes:usize,pub key_bytes:usize,pub descriptor_bytes:usize,
    pub setup_id:String,pub timings_us:Timings,pub capacities:Capacities,
    pub modeled_bytes:Modeled,pub verdicts:Verdicts,
}

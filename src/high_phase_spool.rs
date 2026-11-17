//! Private, small-shape scheduling differential; no production entry point.
use crate::{gkr, transcript::Transcript};
use ark_bn254::Fr;
use ark_ff::{BigInt, PrimeField, Zero};
use ark_serialize::CanonicalSerialize;
use blake2::{Blake2b512, Digest};
use serde::Serialize;
use std::fs::{File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};

type Triple = [Fr; 3];
type Seal = [u8; 64];
const HEADER: usize = 256;
const RECORD: usize = 96;
const MAX_RECORDS: usize = 64;
const MAX_TAPES: usize = 64;
const MAX_FILE: u64 = 6400;
const SELECTED: [usize; 11] = [0, 1, 2, 3, 4, 5, 6, 7, 11, 13, 14];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Error { Shape, Capacity, Path, Io, Read, Extent, Header, Canonical, Seal, SourceOrder, SumcheckIdentity }
impl Error {
    fn name(self) -> &'static str {
        match self {
            Self::Shape=>"Shape", Self::Capacity=>"Capacity", Self::Path=>"Path",
            Self::Io=>"Io", Self::Read=>"Read", Self::Extent=>"Extent", Self::Header=>"Header",
            Self::Canonical=>"Canonical", Self::Seal=>"Seal", Self::SourceOrder=>"SourceOrder",
            Self::SumcheckIdentity=>"SumcheckIdentity",
        }
    }
}
type Result<T> = std::result::Result<T, Error>;

fn digest(bytes: &[u8]) -> Seal { Blake2b512::digest(bytes).into() }
fn hex(bytes: &[u8]) -> String { bytes.iter().map(|x| format!("{x:02X}")).collect() }
fn scalar(x: Fr) -> Result<[u8; 32]> {
    let mut out = [0u8; 32];
    x.serialize_compressed(&mut out[..]).map_err(|_| Error::Canonical)?;
    Ok(out)
}
fn decode(bytes: &[u8]) -> Result<Fr> {
    if bytes.len() != 32 { return Err(Error::Extent); }
    let mut limbs = [0u64; 4];
    for (i, limb) in limbs.iter_mut().enumerate() {
        *limb = u64::from_le_bytes(bytes[8*i..8*i+8].try_into().map_err(|_| Error::Extent)?);
    }
    let value = Fr::from_bigint(BigInt(limbs)).ok_or(Error::Canonical)?;
    if scalar(value)?.as_slice() != bytes { return Err(Error::Canonical); }
    Ok(value)
}
fn record(t: Triple) -> Result<[u8; RECORD]> {
    let mut out = [0u8; RECORD];
    for i in 0..3 { out[32*i..32*i+32].copy_from_slice(&scalar(t[i])?); }
    Ok(out)
}
fn record_digest(rows: &[Triple]) -> Result<Seal> {
    let mut h = Blake2b512::new();
    for row in rows { h.update(record(*row)?); }
    Ok(h.finalize().into())
}
fn prefix_digest(prefix: &[Fr], bank: &[Fr]) -> Result<Seal> {
    let mut h = Blake2b512::new();
    h.update(b"private-bank-spool-prefix-v1");
    h.update((prefix.len() as u64).to_le_bytes());
    for x in prefix.iter().chain(bank) { h.update(scalar(*x)?); }
    Ok(h.finalize().into())
}

#[derive(Clone)]
struct PhaseSource {
    phase: u32,
    owner_bits: usize,
    rows: Vec<Triple>,
    original_records: usize,
    prefix: Vec<Fr>,
    tag: Seal,
    descriptor: Seal,
    claim: Fr,
}
impl PhaseSource {
    // Only private synthetic factories call this. This is not PackedAuthority.
    fn new(phase: u32, owner_bits: usize, rows: Vec<Triple>) -> Result<Self> {
        if phase > 1 || owner_bits > 2 || rows.len() != (16usize << owner_bits)
            || rows.len() > MAX_RECORDS { return Err(Error::Shape); }
        if rows.capacity() > MAX_RECORDS { return Err(Error::Capacity); }
        let prefix: Vec<Fr> = (0..16).map(|i| Fr::from(2+i as u64)).collect();
        if prefix.capacity() > 16 { return Err(Error::Capacity); }
        let tag = record_digest(&rows)?;
        let mut bytes = Vec::with_capacity(128);
        bytes.extend_from_slice(b"private-synthetic-phase-v1");
        bytes.extend_from_slice(&phase.to_le_bytes());
        bytes.extend_from_slice(&(owner_bits as u64).to_le_bytes());
        bytes.extend_from_slice(&tag);
        if bytes.capacity()>128 { return Err(Error::Capacity); }
        let descriptor = digest(&bytes);
        let claim = rows.iter().map(|t| t[0]*t[2]+t[1]).sum();
        let original_records=rows.len();
        Ok(Self {phase, owner_bits, rows, original_records, prefix, tag, descriptor, claim})
    }
    fn header(&self, round: usize, bank_point: &[Fr]) -> Result<[u8; HEADER]> {
        if round >= 4 || bank_point.len() != round { return Err(Error::Shape); }
        let mut h = [0u8; HEADER];
        h[..8].copy_from_slice(b"BKSPL001");
        let words = [1u32, self.phase, round as u32, (4-round) as u32,
                     self.owner_bits as u32, RECORD as u32];
        for (i, word) in words.iter().enumerate() { h[8+4*i..12+4*i].copy_from_slice(&word.to_le_bytes()); }
        let sizes = [self.original_records >> round, self.original_records, self.original_records*RECORD];
        for (i, size) in sizes.iter().enumerate() { h[32+8*i..40+8*i].copy_from_slice(&(*size as u64).to_le_bytes()); }
        h[56..60].copy_from_slice(&((self.prefix.len()+round) as u32).to_le_bytes());
        // h[60..64] stays reserved zero and is compared in every pass.
        h[64..128].copy_from_slice(&self.tag);
        h[128..192].copy_from_slice(&prefix_digest(&self.prefix, bank_point)?);
        h[192..256].copy_from_slice(&self.descriptor);
        Ok(h)
    }
}

struct InitialMeta {
    phase:u32,owner_bits:usize,original_records:usize,prefix:Vec<Fr>,
    tag:Seal,descriptor:Seal,claim:Fr,
}
impl InitialMeta {
    fn header(&self, round: usize, bank_point: &[Fr]) -> Result<[u8; HEADER]> {
        if round >= 4 || bank_point.len() != round { return Err(Error::Shape); }
        let mut h = [0u8; HEADER];
        h[..8].copy_from_slice(b"BKSPL001");
        let words = [1u32, self.phase, round as u32, (4-round) as u32,
                     self.owner_bits as u32, RECORD as u32];
        for (i, word) in words.iter().enumerate() { h[8+4*i..12+4*i].copy_from_slice(&word.to_le_bytes()); }
        let sizes = [self.original_records >> round, self.original_records, self.original_records*RECORD];
        for (i, size) in sizes.iter().enumerate() { h[32+8*i..40+8*i].copy_from_slice(&(*size as u64).to_le_bytes()); }
        h[56..60].copy_from_slice(&((self.prefix.len()+round) as u32).to_le_bytes());
        // h[60..64] stays reserved zero and is compared in every pass.
        h[64..128].copy_from_slice(&self.tag);
        h[128..192].copy_from_slice(&prefix_digest(&self.prefix, bank_point)?);
        h[192..256].copy_from_slice(&self.descriptor);
        Ok(h)
    }
}

/// Optional controls only. Neither initial metadata nor the writer owns rows.
struct ControlRows { rows:Vec<Triple> }
impl ControlRows {
    fn new()->Self {Self{rows:Vec::with_capacity(MAX_RECORDS)}}
    fn observe(&mut self,row:Triple)->Result<()> {
        if self.rows.len()==MAX_RECORDS || self.rows.capacity()!=MAX_RECORDS {
            return Err(Error::Capacity);
        }
        self.rows.push(row);Ok(())
    }
    fn into_source(self,meta:&InitialMeta)->PhaseSource {
        PhaseSource {phase:meta.phase,owner_bits:meta.owner_bits,original_records:meta.original_records,
            rows:self.rows,prefix:meta.prefix.clone(),tag:meta.tag,descriptor:meta.descriptor,claim:meta.claim}
    }
}
type RowVisitor<'a> = dyn FnMut(usize,Triple)->std::result::Result<(),String> + 'a;
type RowRun<'a> = dyn for<'v> FnMut(&mut RowVisitor<'v>)->std::result::Result<(),String> + 'a;

fn checked_pass(run:&mut RowRun<'_>,visitor:&mut dyn FnMut(usize,Triple)->Result<()>)->Result<()> {
    let mut stage=None;
    let result=run(&mut |index,row| visitor(index,row).map_err(|e| {
        stage=Some(e);e.name().to_string()
    }));
    result.map_err(|_|stage.unwrap_or(Error::Read))
}
fn prepare_initial(run:&mut RowRun<'_>,expected:usize,mut observer:Option<&mut ControlRows>)
    ->Result<(Seal,Triple)> {
    if expected==0 || expected>MAX_RECORDS {return Err(Error::Capacity);}
    let mut h=Blake2b512::new();let mut count=0;let mut first=None;
    checked_pass(run,&mut |index,row| {
        if index!=count || count>=expected {return Err(Error::SourceOrder);}
        let raw=record(row)?;h.update(raw);
        if let Some(control)=observer.as_deref_mut(){control.observe(row)?;}
        if first.is_none(){first=Some(row);}
        count+=1;Ok(())
    })?;
    if count!=expected {return Err(Error::SourceOrder);}
    Ok((h.finalize().into(),first.ok_or(Error::SourceOrder)?))
}
fn write_initial(run:&mut RowRun<'_>,meta:&InitialMeta,label:&str,evidence:&mut Evidence,
    metrics:&mut Metrics)->Result<usize> {
    if meta.owner_bits>2 || meta.original_records!=(16<<meta.owner_bits)
        || meta.original_records>MAX_RECORDS || meta.prefix.len()!=16
        || meta.prefix.capacity()!=16 {return Err(Error::Shape);}
    let current=evidence.add(&format!("{label}-r0.tape"),meta.header(0,&[])?,metrics)?;
    let mut h=Blake2b512::new();let mut count=0;
    checked_pass(run,&mut |index,row| {
        if index!=count || count>=meta.original_records {return Err(Error::SourceOrder);}
        let raw=EncodedRecord(record(row)?);h.update(raw.0);
        evidence.tapes[current].write_encoded(raw,metrics)?;count+=1;Ok(())
    })?;
    if count!=meta.original_records || Into::<Seal>::into(h.finalize())!=meta.tag {
        return Err(Error::SourceOrder);
    }
    evidence.tapes[current].seal()?;Ok(current)
}
struct EncodedRecord([u8;RECORD]);

#[derive(Default)]
struct Metrics { read_bytes: u64, write_bytes: u64, records_read: u64, pairs: u64, rounds: u64 }
struct Tape {
    file: File,
    path: PathBuf,
    name: String,
    header: [u8; HEADER],
    expected: Seal,
    writer: Blake2b512,
    records: usize,
    target: usize,
    sealed: bool,
    fail_next_read: bool,
    audit_size: u64,
    audit_seal: Seal,
}
impl Tape {
    fn create(root: &Path, name: &str, header: [u8; HEADER], metrics: &mut Metrics) -> Result<Self> {
        if name.len() > 64 || name.contains('/') || name.contains('\\') { return Err(Error::Path); }
        let path = root.join(name);
        if path.capacity() > 512 { return Err(Error::Capacity); }
        let mut options = OpenOptions::new();
        options.read(true).write(true).create_new(true);
        #[cfg(windows)] {
            use std::os::windows::fs::OpenOptionsExt;
            options.share_mode(0);
        }
        #[cfg(not(windows))] { return Err(Error::Path); }
        let mut file = options.open(&path).map_err(|_| Error::Io)?;
        file.write_all(&header).map_err(|_| Error::Io)?;
        metrics.write_bytes += HEADER as u64;
        let target = u64::from_le_bytes(header[32..40].try_into().map_err(|_| Error::Header)?) as usize;
        if target > MAX_RECORDS { return Err(Error::Shape); }
        let mut writer = Blake2b512::new(); writer.update(header);
        Ok(Self {file,path,name:name.into(),header,expected:[0;64],writer,
                 records:0,target,sealed:false,fail_next_read:false,audit_size:0,audit_seal:[0;64]})
    }
    fn write(&mut self, row: Triple, metrics: &mut Metrics) -> Result<()> {
        self.write_encoded(EncodedRecord(record(row)?),metrics)
    }
    fn write_encoded(&mut self,row:EncodedRecord,metrics:&mut Metrics)->Result<()> {
        if self.sealed || self.records>=MAX_RECORDS || self.records>=self.target {return Err(Error::Capacity);}
        self.file.write_all(&row.0).map_err(|_|Error::Io)?;
        self.writer.update(row.0);self.records+=1;metrics.write_bytes+=RECORD as u64;Ok(())
    }
    fn seal(&mut self) -> Result<()> {
        if self.records != self.target { return Err(Error::Extent); }
        self.file.flush().map_err(|_| Error::Io)?;
        self.file.sync_all().map_err(|_| Error::Io)?;
        self.expected = self.writer.clone().finalize().into(); self.sealed = true;
        Ok(())
    }
    fn start(&mut self, metrics: &mut Metrics) -> Result<Blake2b512> {
        if !self.sealed || self.file.metadata().map_err(|_| Error::Io)?.len()
            != (HEADER+self.target*RECORD) as u64 { return Err(Error::Extent); }
        self.file.seek(SeekFrom::Start(0)).map_err(|_| Error::Io)?;
        let mut raw = [0u8; HEADER];
        self.file.read_exact(&mut raw).map_err(|_| Error::Read)?;
        metrics.read_bytes += HEADER as u64;
        if raw != self.header { return Err(Error::Header); }
        let mut h = Blake2b512::new(); h.update(raw); Ok(h)
    }
    fn read(&mut self, h: &mut Blake2b512, metrics: &mut Metrics) -> Result<Triple> {
        if std::mem::take(&mut self.fail_next_read) { return Err(Error::Io); }
        let mut raw = [0u8; RECORD];
        self.file.read_exact(&mut raw).map_err(|_| Error::Read)?;
        metrics.read_bytes += RECORD as u64; metrics.records_read += 1; h.update(raw);
        Ok([decode(&raw[..32])?,decode(&raw[32..64])?,decode(&raw[64..])?])
    }
    fn finish(&mut self, h: Blake2b512) -> Result<()> {
        let mut extra = [0u8; 1];
        if self.file.read(&mut extra).map_err(|_| Error::Io)? != 0 { return Err(Error::Extent); }
        let actual: Seal = h.finalize().into();
        if actual != self.expected { return Err(Error::Seal); }
        Ok(())
    }
    // Faults never enter an admitted public source/reader factory.
    fn fault_bytes(&mut self, offset: u64, bytes: &[u8]) -> Result<()> {
        self.file.seek(SeekFrom::Start(offset)).map_err(|_| Error::Io)?;
        self.file.write_all(bytes).map_err(|_| Error::Io)?;
        self.file.flush().map_err(|_| Error::Io)?; Ok(())
    }
}

struct Evidence { root: PathBuf, tapes: Vec<Tape> }
impl Evidence {
    fn new() -> Result<Self> {
        let path = PathBuf::from(std::env::var_os("NIPOPOW_HIGH_PHASE_SPOOL_EVIDENCE").ok_or(Error::Path)?);
        if !crate::preview_test_paths::absolute_outside_source(&path) || path.capacity() > 512 { return Err(Error::Path); }
        let md = std::fs::symlink_metadata(&path).map_err(|_| Error::Io)?;
        if !md.is_dir() || md.file_type().is_symlink() { return Err(Error::Path); }
        #[cfg(windows)] {
            use std::os::windows::fs::MetadataExt;
            if md.file_attributes() & 0x400 != 0 { return Err(Error::Path); }
        }
        if std::fs::read_dir(&path).map_err(|_| Error::Io)?.next().is_some() { return Err(Error::Path); }
        Ok(Self {root:path,tapes:Vec::with_capacity(MAX_TAPES)})
    }
    fn add(&mut self, name: &str, header: [u8; HEADER], metrics: &mut Metrics) -> Result<usize> {
        if self.tapes.len() == MAX_TAPES { return Err(Error::Capacity); }
        let tape = Tape::create(&self.root,name,header,metrics)?;
        let i = self.tapes.len(); self.tapes.push(tape); Ok(i)
    }
    fn owned_bytes(&self) -> usize {
        self.tapes.capacity()*std::mem::size_of::<Tape>() + self.root.capacity()
            + self.tapes.iter().map(|t| t.path.capacity()+t.name.capacity()).sum::<usize>()
    }
    fn integrated_child(root: &Path, child: &str) -> Result<Self> {
        if !crate::preview_test_paths::absolute_outside_source(root) || !matches!(child,"preflight"|"real") {
            return Err(Error::Path);
        }
        let md=std::fs::symlink_metadata(root).map_err(|_|Error::Io)?;
        if !md.is_dir() || md.file_type().is_symlink() {return Err(Error::Path);}
        #[cfg(windows)] {use std::os::windows::fs::MetadataExt;
            if md.file_attributes()&0x400!=0 {return Err(Error::Path);}}
        let path=root.join(child); if path.capacity()>512 {return Err(Error::Capacity);}
        std::fs::create_dir(&path).map_err(|_|Error::Path)?;
        Ok(Self {root:path,tapes:Vec::with_capacity(MAX_TAPES)})
    }
}

#[derive(Clone, Copy)]
enum Fault { None, Header(usize), ShortHeader, FirstSeal, Noncanonical, ShortRead, Extra, Io,
             BetweenPass, Permute, Omit, Duplicate, Claim }
#[derive(Debug, PartialEq, Eq)]
struct PhaseResult { point: Vec<Fr>, terminal: Fr, claim: Fr, rounds: Vec<Vec<Fr>> }

fn arrays(rows: &[Triple]) -> (Vec<Fr>, Vec<Fr>, Vec<Fr>) {
    ((rows.iter().map(|t|t[0]).collect()),(rows.iter().map(|t|t[1]).collect()),(rows.iter().map(|t|t[2]).collect()))
}
fn dense(source: &PhaseSource, transcript: &mut Transcript) -> PhaseResult {
    let (a,b,x) = arrays(&source.rows);
    let mut claim=source.claim; let mut rounds=Vec::new();
    let (point,terminal)=gkr::prove_phase(a,b,&x,&mut claim,&mut rounds,transcript).unwrap();
    PhaseResult {point,terminal,claim,rounds}
}
fn send(poly: Vec<Fr>, claim: &mut Fr, transcript: &mut Transcript) -> Result<Fr> {
    if poly[0]+gkr::eval_polynomial(&poly,Fr::from(1u64)) != *claim { return Err(Error::SumcheckIdentity); }
    gkr::append_polynomial(transcript,b"gkr-sumcheck-polynomial",&poly);
    let t=transcript.challenge_scalar(b"gkr-sumcheck-challenge");
    *claim=gkr::eval_polynomial(&poly,t); Ok(t)
}
fn spooled(source: &PhaseSource, label: &str, evidence: &mut Evidence,
           transcript: &mut Transcript, metrics: &mut Metrics, fault: Fault) -> Result<PhaseResult> {
    spooled_owned(source.clone(),label,evidence,transcript,metrics,fault)
}
fn spooled_owned(mut source: PhaseSource, label: &str, evidence: &mut Evidence,
           transcript: &mut Transcript, metrics: &mut Metrics, fault: Fault) -> Result<PhaseResult> {
    if source.owner_bits>2 || source.rows.len()!=(16<<source.owner_bits) { return Err(Error::Shape); }
    let current=evidence.add(&format!("{label}-r0.tape"),source.header(0,&[])?,metrics)?;
    let mut initial=source.rows.clone();
    if matches!(fault,Fault::Permute) { initial.swap(0,1); }
    if matches!(fault,Fault::Omit) { initial.pop(); }
    if matches!(fault,Fault::Duplicate) { initial[1]=initial[0]; }
    for row in &initial { evidence.tapes[current].write(*row,metrics)?; }
    // The initial owned-order check does not accept a newly supplied writer hash.
    let ordered=record_digest(&initial)?;
    if ordered != source.tag { return Err(Error::SourceOrder); }
    drop(initial);
    evidence.tapes[current].seal()?;
    let first=source.rows[0];
    // Metadata carries the original extent; actual rows need not survive folds.
    drop(std::mem::take(&mut source.rows));
    let meta=InitialMeta {phase:source.phase,owner_bits:source.owner_bits,
        original_records:source.original_records,prefix:source.prefix,tag:source.tag,
        descriptor:source.descriptor,claim:source.claim};
    fold_initial(meta,current,first,label,evidence,transcript,metrics,fault)
}
fn fold_initial(source:InitialMeta,mut current:usize,first:Triple,label:&str,evidence:&mut Evidence,
    transcript:&mut Transcript,metrics:&mut Metrics,fault:Fault)->Result<PhaseResult> {
    let mut point=Vec::with_capacity(4+source.owner_bits);
    let mut rounds=Vec::with_capacity(4+source.owner_bits);
    let mut claim=source.claim;
    if matches!(fault,Fault::Claim) {claim+=Fr::from(1u64);}
    match fault {
        Fault::Header(offset) => evidence.tapes[current].fault_bytes(offset as u64,&[0xFE])?,
        Fault::ShortHeader => evidence.tapes[current].file.set_len(255).map_err(|_|Error::Io)?,
        Fault::FirstSeal => evidence.tapes[current].fault_bytes(HEADER as u64,&scalar(first[0]+Fr::from(1u64))?)?,
        Fault::Noncanonical => {
            let mut raw=[0u8;32];
            for (i,limb) in Fr::MODULUS.0.iter().enumerate() { raw[8*i..8*i+8].copy_from_slice(&limb.to_le_bytes()); }
            evidence.tapes[current].fault_bytes(HEADER as u64,&raw)?;
        },
        Fault::Extra => { let end=evidence.tapes[current].file.metadata().map_err(|_|Error::Io)?.len(); evidence.tapes[current].fault_bytes(end,&[0])?; },
        _=>(),
    }
    for bank_round in 0..4 {
        let count=source.original_records>>bank_round;
        let mut h=evidence.tapes[current].start(metrics)?;
        if bank_round==0 && matches!(fault,Fault::Io) { evidence.tapes[current].fail_next_read=true; }
        if bank_round==0 && matches!(fault,Fault::ShortRead) {
            evidence.tapes[current].file.set_len((HEADER+count*RECORD-1) as u64).map_err(|_|Error::Io)?;
        }
        let mut poly=vec![Fr::zero();3];
        for _ in 0..count/2 {
            let l=evidence.tapes[current].read(&mut h,metrics)?;
            let r=evidence.tapes[current].read(&mut h,metrics)?;
            let q=gkr::quadratic_message(&[l[0],r[0]],&[l[1],r[1]],&[l[2],r[2]]);
            for j in 0..3 { poly[j]+=q[j]; } metrics.pairs+=1;
        }
        evidence.tapes[current].finish(h)?;
        let t=send(poly.clone(),&mut claim,transcript)?; point.push(t);rounds.push(poly);metrics.rounds+=1;
        if bank_round==0 && matches!(fault,Fault::BetweenPass) {
            evidence.tapes[current].fault_bytes((HEADER+64) as u64,&scalar(first[2]+Fr::from(1u64))?)?;
        }
        let mut h=evidence.tapes[current].start(metrics)?;
        let next=if bank_round<3 { Some(evidence.add(&format!("{label}-r{}.tape",bank_round+1),source.header(bank_round+1,&point)?,metrics)?) } else {None};
        let mut owner_a=Vec::with_capacity(if next.is_none(){1<<source.owner_bits}else{0});
        let mut owner_b=Vec::with_capacity(owner_a.capacity());
        let mut owner_x=Vec::with_capacity(owner_a.capacity());
        for _ in 0..count/2 {
            let l=evidence.tapes[current].read(&mut h,metrics)?;
            let r=evidence.tapes[current].read(&mut h,metrics)?;
            let out=[l[0]+t*(r[0]-l[0]),l[1]+t*(r[1]-l[1]),l[2]+t*(r[2]-l[2])];
            if let Some(i)=next { evidence.tapes[i].write(out,metrics)?; }
            else {owner_a.push(out[0]);owner_b.push(out[1]);owner_x.push(out[2]);}
        }
        // Never seal a successor or admit owner arrays before this SAME seal check.
        evidence.tapes[current].finish(h)?;
        if let Some(i)=next {evidence.tapes[i].seal()?;current=i;}
        else {
            if owner_a.capacity()>4 || owner_b.capacity()>4 || owner_x.capacity()>4 {return Err(Error::Capacity);}
            let (high,terminal)=gkr::prove_phase(owner_a,owner_b,&owner_x,&mut claim,&mut rounds,transcript)
                .map_err(|_|Error::SumcheckIdentity)?;
            point.extend(high);drop(owner_x);
            return Ok(PhaseResult {point,terminal,claim,rounds});
        }
    }
    Err(Error::Shape)
}

#[derive(Serialize)]
pub(crate) struct PreflightReceipt {
    pub(crate) phase_cases: usize, pub(crate) math_checks: usize,
    pub(crate) codec_checks: usize, pub(crate) negative_checks: usize,
    pub(crate) tape_members: usize, pub(crate) retained_tape_bytes: u64,
    pub(crate) summary_blake2b512: String,
}
pub(crate) fn combined_preflight(root:&Path) -> PreflightReceipt {
    let evidence=Evidence::integrated_child(root,"preflight").unwrap();
    tests::run_preflight(evidence)
}

#[derive(Serialize)]
pub(crate) struct RealFault {
    phase:u32, label:&'static str, stage:&'static str, challenges:u64,
}
/// Actual X authority is supplied only by consuming core_pool_boolean's token.
pub(crate) struct RealEvidence {
    evidence:Evidence, metrics:Metrics, faults:Vec<RealFault>, math_checks:usize,
    next_phase:u32, u_final:Option<Fr>, v_initial:Option<Fr>,
    source_metrics:crate::core_pool_boolean::HighSourceMetrics,
    control_source_passes:u64,control_source_records:u64,
    pub(crate) u_high_final_matches_v_initial:bool,
}
#[derive(Serialize)]
pub(crate) struct RealReport {
    pub(crate) read_bytes:u64, pub(crate) written_bytes:u64,
    pub(crate) records_read:u64, pub(crate) pairs:u64, pub(crate) bank_rounds:u64,
    pub(crate) tape_members:usize, pub(crate) retained_tape_bytes:u64,
    pub(crate) math_checks:usize, pub(crate) negative_checks:usize,
    pub(crate) owned_capacity_bytes:usize, pub(crate) fault_ledger:Vec<RealFault>,
    pub(crate) artifacts:Vec<(String,u64,String)>,
    pub(crate) source_passes:u64,pub(crate) source_owner_loads:u64,
    pub(crate) source_records:u64,pub(crate) source_payload_bytes:u64,
    pub(crate) control_source_passes:u64,pub(crate) control_source_records:u64,
    pub(crate) control_source_payload_bytes:u64,
}
impl RealEvidence {
    pub(crate) fn new(root:&Path)->Self {
        Self {evidence:Evidence::integrated_child(root,"real").unwrap(),metrics:Metrics::default(),
            faults:Vec::with_capacity(64),math_checks:0,next_phase:0,u_final:None,v_initial:None,
            u_high_final_matches_v_initial:false,source_metrics:Default::default(),control_source_passes:0,control_source_records:0}
    }
    pub(crate) fn begin_v(&mut self,claim:Fr)->std::result::Result<(),String> {
        if self.next_phase!=1 || self.u_final!=Some(claim) || self.v_initial.is_some() {
            return Err("real U-final/V-initial boundary".into());
        }
        self.v_initial=Some(claim); self.u_high_final_matches_v_initial=true; Ok(())
    }
    pub(crate) fn prove_real<P:crate::core_pool_boolean::HighRows>(&mut self,
        token:crate::core_pool_boolean::RealHighPhase<'_,'_,P>,
        claim:&mut Fr,rounds:&mut Vec<Vec<Fr>>,transcript:&mut Transcript)
        ->std::result::Result<(Vec<Fr>,Fr),String> {
        let (authority,phase,prefix,mut producer,incoming)=token.into_parts();
        if phase!=self.next_phase || phase>1 || incoming!=*claim || prefix.len()!=16
            || prefix.capacity()!=16 || authority.banks()!=SELECTED || producer.records()!=64
            || (phase==1 && self.v_initial.is_none()) {
            return Err("real phase token shape/context".into());
        }
        // The optional observer is only the bounded Dense/fault control object.
        let mut controls=ControlRows::new();
        let (tag,first)=prepare_initial(&mut |v|producer.pass(v),64,Some(&mut controls))
            .map_err(|e|e.name().to_string())?;
        let meta=InitialMeta {phase,owner_bits:2,original_records:64,prefix,tag,
            descriptor:authority.spool_descriptor(),claim:incoming};
        let source=controls.into_source(&meta);
        let mut expected_t=transcript.clone();let expected=dense(&source,&mut expected_t);
        self.real_controls(&source,transcript,&expected)?;
        self.source_controls(&source,transcript)?;
        // Control rows/metadata are not an input to the real second source pass.
        drop(source);
        let label=if phase==0{"u"}else{"v"};
        let current=write_initial(&mut |v|producer.pass(v),&meta,label,
            &mut self.evidence,&mut self.metrics).map_err(|e|e.name().to_string())?;
        let metrics=producer.metrics();
        if metrics.passes!=2 || metrics.owner_loads!=8 || metrics.records!=128 {
            return Err("real source pass accounting".into());
        }
        self.source_metrics.passes+=metrics.passes;
        self.source_metrics.owner_loads+=metrics.owner_loads;
        self.source_metrics.records+=metrics.records;
        // Owns U kernels or V tau, prefix weights and the mutable loader borrow.
        drop(producer);
        let actual=fold_initial(meta,current,first,label,&mut self.evidence,transcript,
            &mut self.metrics,Fault::None).map_err(|e|e.name().to_string())?;
        if authority.banks()!=SELECTED{return Err("real authority changed".into());}
        if actual!=expected || (transcript.challenges(),transcript.raw_queries(),transcript.bytes_absorbed())
            !=(expected_t.challenges(),expected_t.raw_queries(),expected_t.bytes_absorbed()) {
            return Err("real high phase differential".into());
        }
        let mut next=transcript.clone();let mut original=expected_t.clone();
        if next.challenge_scalar(b"real-phase-following")!=original.challenge_scalar(b"real-phase-following") {
            return Err("real high continuation differential".into());
        }
        self.math_checks+=2;*claim=actual.claim;rounds.extend(actual.rounds);
        if phase==0 {self.u_final=Some(actual.claim);}
        self.next_phase+=1;Ok((actual.point,actual.terminal))
    }
    fn source_controls(&mut self,source:&PhaseSource,initial:&Transcript)->std::result::Result<(),String> {
        let labels=["source-omit","source-duplicate","source-reorder","source-A","source-B","source-X",
            "source-physical","source-inactive","source-owner","source-extra","source-loader","source-overflow"];
        for label in labels {
            let phase=source.phase;let name=format!("{}-{label}",if phase==0{"u"}else{"v"});
            let before=initial.challenges();let t=initial.clone();let mut m=Metrics::default();
            let meta=InitialMeta {phase,owner_bits:2,original_records:64,prefix:source.prefix.clone(),
                tag:source.tag,descriptor:source.descriptor,claim:source.claim};
            let expected=if label=="source-overflow"{Error::Capacity}
                else if label=="source-loader"{Error::Read}else{Error::SourceOrder};
            let result=if label=="source-overflow" {
                prepare_initial(&mut |v| {
                    for (i,row) in source.rows.iter().copied().enumerate(){v(i,row)?;}Ok(())
                },65,None).map(|_|0)
            } else {
                // The simulator is confined to controls; it cannot issue a real token.
                let mut changed=false;
                self.control_source_passes+=1;let mut records=0u64;
                let result=write_initial(&mut |v| {
                    for (i,original) in source.rows.iter().copied().enumerate() {
                        if label=="source-loader" && i==0 {return Err("isolated source read".into());}
                        if label=="source-omit" && i==63 {changed=true;continue;}
                        let mut row=original;
                        match label {
                            "source-duplicate" if i==1=>row=source.rows[0],
                            "source-reorder" if i<2=>row=source.rows[1-i],
                            "source-A" if i==0=>row[0]+=Fr::from(1u64),
                            "source-B" if i==0=>row[1]+=Fr::from(1u64),
                            "source-X" if i==0=>row[2]+=Fr::from(1u64),
                            "source-physical" if i==8=>row=source.rows[11],
                            "source-physical" if i==11=>row=source.rows[8],
                            "source-inactive" if i==8=>row[2]=Fr::zero(),
                            "source-owner" if i==0=>row=source.rows[32],
                            "source-owner" if i==32=>row=source.rows[0],
                            _=>()
                        }
                        changed|=row!=original;v(i,row)?;records+=1;
                    }
                    if label=="source-extra"{changed=true;v(64,source.rows[0])?;records+=1;}
                    Ok(())
                },&meta,&name,&mut self.evidence,&mut m);
                self.control_source_records+=records;
                if label!="source-loader" && !changed{return Err(format!("vacuous source fault {name}"));}
                result
            };
            if result.err()!=Some(expected) || t.challenges()!=before {
                return Err(format!("source fault stage/challenge {name}"));
            }
            if label!="source-overflow" && self.evidence.tapes.last().unwrap().sealed {
                return Err("source fault admitted seal".into());
            }
            self.faults.push(RealFault{phase,label,stage:expected.name(),challenges:0});
        }
        // Positive observer-None cases use mock rows, never the actual source loader.
        for owner_bits in 0..2 {
            let n=16usize<<owner_bits;let mut rows=Vec::with_capacity(n);
            rows.extend_from_slice(&source.rows[..n]);
            let subset=PhaseSource {phase:source.phase,owner_bits,original_records:n,rows,
                prefix:source.prefix.clone(),tag:[0;64],descriptor:source.descriptor,
                claim:source.rows[..n].iter().map(|r|r[0]*r[2]+r[1]).sum()};
            let mut expected_t=initial.clone();let expected=dense(&subset,&mut expected_t);
            self.control_source_passes+=1;let mut first_records=0u64;
            let (tag,first)=prepare_initial(&mut |v| {
                for (i,row) in subset.rows.iter().copied().enumerate(){
                    first_records+=1;v(i,row)?;
                }Ok(())
            },n,None).map_err(|e|e.name().to_string())?;
            self.control_source_records+=first_records;
            let meta=InitialMeta {phase:source.phase,owner_bits,original_records:n,
                prefix:source.prefix.clone(),tag,descriptor:source.descriptor,claim:subset.claim};
            if meta.header(0,&[]).map_err(|e|e.name().to_string())?[64..128]!=tag {
                return Err("initial header tag".into());
            }
            let name=format!("{}-source-h{owner_bits}",if source.phase==0{"u"}else{"v"});
            let mut m=Metrics::default();self.control_source_passes+=1;let mut second_records=0u64;
            let current=write_initial(&mut |v| {
                for (i,row) in subset.rows.iter().copied().enumerate(){
                    v(i,row)?;second_records+=1;
                }Ok(())
            },&meta,&name,&mut self.evidence,&mut m).map_err(|e|e.name().to_string())?;
            self.control_source_records+=second_records;
            let mut t=initial.clone();
            let actual=fold_initial(meta,current,first,&name,&mut self.evidence,&mut t,&mut m,Fault::None)
                .map_err(|e|e.name().to_string())?;
            if actual!=expected || (t.challenges(),t.raw_queries(),t.bytes_absorbed())
                !=(expected_t.challenges(),expected_t.raw_queries(),expected_t.bytes_absorbed()) {
                return Err("observer-None high differential".into());
            }
            if t.challenge_scalar(b"source-control-following")
                !=expected_t.challenge_scalar(b"source-control-following") {
                return Err("observer-None high continuation".into());
            }
            self.math_checks+=2;
        }
        Ok(())
    }
    fn real_controls(&mut self,source:&PhaseSource,initial:&Transcript,expected:&PhaseResult)
        ->std::result::Result<(),String> {
        for (label,fault,error) in [("phase-header",Fault::Header(12),Error::Header),
            ("prefix-header",Fault::Header(128),Error::Header),
            ("first-seal",Fault::FirstSeal,Error::Seal),
            ("between-pass",Fault::BetweenPass,Error::Seal),
            ("false-claim",Fault::Claim,Error::SumcheckIdentity),
            ("order",Fault::Permute,Error::SourceOrder)] {
            let mut t=initial.clone();let before=t.challenges();let mut metrics=Metrics::default();
            let name=format!("{}-{label}",if source.phase==0{"u"}else{"v"});
            let result=spooled(source,&name,&mut self.evidence,&mut t,&mut metrics,fault);
            if result.err()!=Some(error) {return Err(format!("real fault stage {name}"));}
            let advanced=t.challenges()-before;
            if advanced!=if matches!(fault,Fault::BetweenPass){1}else{0} {return Err("real fault challenge count".into());}
            self.faults.push(RealFault{phase:source.phase,label,stage:error.name(),challenges:advanced});
        }
        for label in ["owner-0-2","physical-11-ordinal-8","excluded-X","channel-swap","bank-LSB"] {
            let mut rows=source.rows.clone();
            match label {"owner-0-2"=>rows.swap(0,32),"physical-11-ordinal-8"=>rows.swap(8,11),
                "excluded-X"=>rows[8][2]=Fr::zero(),"channel-swap"=>rows[0].swap(0,1),_=>rows.swap(0,1)}
            if rows==source.rows {return Err(format!("vacuous real mutant {label}"));}
            let (a,b,x)=arrays(&rows);let mut claim=source.claim;let mut rounds=Vec::new();let mut t=initial.clone();
            let result=gkr::prove_phase(a,b,&x,&mut claim,&mut rounds,&mut t);
            if let Ok((point,terminal))=result {
                if (PhaseResult{point,terminal,claim,rounds})==*expected {return Err(format!("masked real mutant {label}"));}
            }
            self.math_checks+=1;
            self.faults.push(RealFault{phase:source.phase,label,stage:"PhaseDifferential",challenges:t.challenges()-initial.challenges()});
        }
        Ok(())
    }
    pub(crate) fn finish(mut self)->RealReport {
        assert_eq!(self.next_phase,2);assert!(self.u_high_final_matches_v_initial);
        assert_eq!((self.metrics.read_bytes,self.metrics.write_bytes,self.metrics.records_read,self.metrics.pairs,self.metrics.rounds),
            (50176,25088,480,120,8));
        assert_eq!(self.faults.len(),46);assert_eq!(self.math_checks,22);
        assert_eq!((self.source_metrics.passes,self.source_metrics.owner_loads,self.source_metrics.records),(4,16,256));
        assert_eq!(self.evidence.tapes.len(),60);
        assert_eq!((self.control_source_passes,self.control_source_records),(30,1470));
        let mut artifacts=Vec::with_capacity(60);let mut total=0;
        for tape in &mut self.evidence.tapes {
            let size=tape.file.metadata().unwrap().len();assert!(size<=6400);total+=size;
            tape.file.seek(SeekFrom::Start(0)).unwrap();let mut h=Blake2b512::new();let mut bytes=[0u8;256];
            loop{let n=tape.file.read(&mut bytes).unwrap();if n==0{break;}h.update(&bytes[..n]);}
            artifacts.push((tape.name.clone(),size,hex(&h.finalize())));
        }
        assert_eq!(total,258240);assert!(self.faults.capacity()<=64);
        let owned=self.evidence.owned_bytes();assert!(owned<=65536);
        // self drops every held handle before the caller proceeds to PCS.
        RealReport{read_bytes:self.metrics.read_bytes,written_bytes:self.metrics.write_bytes,
            records_read:self.metrics.records_read,pairs:self.metrics.pairs,bank_rounds:self.metrics.rounds,
            tape_members:60,retained_tape_bytes:total,math_checks:22,negative_checks:46,
            owned_capacity_bytes:owned,fault_ledger:self.faults,artifacts,
            source_passes:self.source_metrics.passes,source_owner_loads:self.source_metrics.owner_loads,
            source_records:self.source_metrics.records,source_payload_bytes:self.source_metrics.records*RECORD as u64,
            control_source_passes:self.control_source_passes,control_source_records:self.control_source_records,
            control_source_payload_bytes:self.control_source_records*RECORD as u64}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Instant;
    #[derive(Serialize)]
    struct FaultRecord { label: &'static str, stage: &'static str, challenges: u64 }
    #[derive(Serialize)]
    struct ArtifactView<'a> { name: &'a str, bytes: u64, blake2b512: String }
    struct ArtifactList<'a>(&'a [Tape]);
    impl Serialize for ArtifactList<'_> {
        fn serialize<S: serde::Serializer>(&self, serializer: S) -> std::result::Result<S::Ok,S::Error> {
            use serde::ser::SerializeSeq;
            let mut seq=serializer.serialize_seq(Some(self.0.len()))?;
            for tape in self.0 {
                let text=hex(&tape.audit_seal);
                if text.capacity()>256 { return Err(serde::ser::Error::custom("hex capacity")); }
                seq.serialize_element(&ArtifactView{name:&tape.name,bytes:tape.audit_size,blake2b512:text})?;
            }
            seq.end()
        }
    }
    #[derive(Serialize)]
    struct Diagnostic<'a> {
        schema: &'static str, phase_cases: usize, math_checks: usize, codec_checks: usize,
        negative_checks: usize, tape_members: usize, successful_read_bytes: u64, written_bytes: u64,
        records_read: u64, quadratic_pairs: u64, bank_rounds: u64, retained_tape_bytes: u64,
        owned_evidence_capacity_bytes: usize, stream_scratch_reserve_bytes: usize,
        fixture_reserve_bytes: usize, modeled_local_payload_bytes: usize, elapsed_seconds: f64,
        dense_spool_equal: bool, coupled_v_equal: bool, continuation_equal: bool,
        gkr_proof_created: bool, pcs_proof_created: bool, setup_invoked: bool, global_admission: bool,
        fault_ledger: &'a [FaultRecord], artifacts: ArtifactList<'a>,
    }
    fn eq(point: &[Fr], i: usize) -> Fr {
        point.iter().enumerate().fold(Fr::from(1u64),|a,(b,t)|a*if i>>b&1==1{*t}else{Fr::from(1u64)-t})
    }
    fn x_and_weights(owner_bits: usize) -> (Vec<Fr>,Vec<Fr>) {
        let x=(0..16<<owner_bits).map(|i|Fr::from(3+7*i as u64)).collect();
        let owners:Vec<Fr>=(0..owner_bits).map(|i|Fr::from(2+i as u64)).collect();
        let families=[Fr::from(2u64),Fr::from(3u64),Fr::from(5u64),Fr::from(7u64)];
        let weights=(0..16<<owner_bits).map(|i| {
            if SELECTED.contains(&(i%16)){eq(&owners,i/16)*eq(&families,i%16)}else{Fr::zero()}
        }).collect(); (x,weights)
    }
    fn u_source(bits: usize,x:&[Fr],w:&[Fr]) -> PhaseSource {
        PhaseSource::new(0,bits,x.iter().zip(w).map(|(x,w)|
            [*w*(Fr::from(7u64)+Fr::from(13u64)*x),*w*(Fr::from(5u64)+Fr::from(11u64)*x),*x]).collect()).unwrap()
    }
    fn v_source(bits: usize,x:&[Fr],w:&[Fr],u:&PhaseResult) -> PhaseSource {
        // Independent literal per-index coefficient expression; same original X,w.
        let rows=x.iter().enumerate().map(|(i,x)| {
            let alpha=eq(&u.point,i);let tau=w[i]*alpha;
            [tau*(Fr::from(11u64)+Fr::from(13u64)*u.terminal),
             tau*(Fr::from(5u64)+Fr::from(7u64)*u.terminal),*x]
        }).collect(); let s=PhaseSource::new(1,bits,rows).unwrap();assert_eq!(s.claim,u.claim);s
    }
    fn compare(source:&PhaseSource,label:&str,e:&mut Evidence,m:&mut Metrics,t:&mut Transcript) -> PhaseResult {
        let mut original=t.clone();let expected=dense(source,&mut original);
        let actual=spooled(source,label,e,t,m,Fault::None).unwrap();assert_eq!(actual,expected);
        for result in [&actual,&expected] {
            assert!(result.point.capacity()<=8 && result.rounds.capacity()<=8);
            assert!(result.rounds.iter().all(|p|p.capacity()<=3));
        }
        for (a,b) in actual.rounds.iter().flatten().zip(expected.rounds.iter().flatten()) {assert_eq!(scalar(*a).unwrap(),scalar(*b).unwrap());}
        assert_eq!((t.challenges(),t.raw_queries(),t.bytes_absorbed()),(original.challenges(),original.raw_queries(),original.bytes_absorbed()));
        let mut a=t.clone();let mut b=original.clone();assert_eq!(a.challenge_scalar(b"following-phase"),b.challenge_scalar(b"following-phase"));
        actual
    }
    fn rejected(label:&'static str,fault:Fault,error:Error,source:&PhaseSource,e:&mut Evidence,ledger:&mut Vec<FaultRecord>) {
        let mut t=Transcript::new(b"private-high-phase-fault-v1");let before=t.challenges();let mut m=Metrics::default();
        assert_eq!(spooled(source,label,e,&mut t,&mut m,fault).err(),Some(error),"{label}");
        let advanced=t.challenges()-before;
        assert_eq!(advanced,if matches!(fault,Fault::BetweenPass){1}else{0},"{label}");
        if matches!(fault,Fault::BetweenPass) {assert!(!e.tapes.last().unwrap().sealed);}
        ledger.push(FaultRecord{label,stage:error.name(),challenges:advanced});
    }
    #[test]
    #[ignore]
    fn sealed_bank_rounds_match_dense_phase() {
        let _receipt=run_preflight(Evidence::new().unwrap());
    }
    pub(super) fn run_preflight(mut evidence:Evidence)->PreflightReceipt {
        let started=Instant::now();assert_eq!(std::mem::size_of::<Fr>(),32);
        assert!(std::mem::size_of::<Tape>()<=1024);
        let mut metrics=Metrics::default();
        let mut phase_cases=0usize;let mut math_checks=0usize;let mut codec_checks=0usize;
        for bits in 0..=2 {
            let (x,w)=x_and_weights(bits);assert!(x.iter().all(|x|!x.is_zero()&&*x!=Fr::from(1u64)));
            for owner in 0..1<<bits {assert_eq!(w[owner*16+8],Fr::zero());assert!(!w[owner*16+11].is_zero());}
            let mut t=Transcript::new(b"private-coupled-high-phase-v1");
            let us=u_source(bits,&x,&w);let u=compare(&us,&format!("u-c{}",1<<bits),&mut evidence,&mut metrics,&mut t);phase_cases+=1;
            let vs=v_source(bits,&x,&w,&u);let _v=compare(&vs,&format!("v-c{}",1<<bits),&mut evidence,&mut metrics,&mut t);phase_cases+=1;math_checks+=1;
        }
        let (x,w)=x_and_weights(0);let mut t=Transcript::new(b"zero-kernel");
        let zero=PhaseSource::new(0,0,x.iter().map(|x|[Fr::zero(),Fr::zero(),*x]).collect()).unwrap();
        compare(&zero,"zero-kernel",&mut evidence,&mut metrics,&mut t);phase_cases+=1;
        let mut tau=vec![Fr::zero();16];for (i,bank) in SELECTED.iter().enumerate(){tau[*bank]=if i<10{Fr::from(i as u64+1)}else{-Fr::from(55u64)};}
        assert_eq!(tau.iter().copied().sum::<Fr>(),Fr::zero());assert!(SELECTED.iter().all(|i|!tau[*i].is_zero()));
        let sigma_zero=PhaseSource::new(1,0,x.iter().enumerate().map(|(i,x)|[tau[i]*Fr::from(17u64),tau[i]*Fr::from(19u64),*x]).collect()).unwrap();
        let mut t=Transcript::new(b"zero-sigma");compare(&sigma_zero,"zero-sigma",&mut evidence,&mut metrics,&mut t);phase_cases+=1;math_checks+=2;
        for value in [Fr::zero(),Fr::from(1u64),-Fr::from(1u64)] {assert_eq!(decode(&scalar(value).unwrap()),Ok(value));codec_checks+=1;}
        let mut modulus=[0u8;32];for(i,v)in Fr::MODULUS.0.iter().enumerate(){modulus[8*i..8*i+8].copy_from_slice(&v.to_le_bytes());}
        assert_eq!(decode(&modulus),Err(Error::Canonical));codec_checks+=1;
        let mut plus=modulus;plus[0]+=1;assert_eq!(decode(&plus),Err(Error::Canonical));codec_checks+=1;
        assert_eq!(decode(&[0xFF;32]),Err(Error::Canonical));codec_checks+=1;
        assert_eq!(decode(&[0;31]),Err(Error::Extent));assert_eq!(decode(&[0;33]),Err(Error::Extent));codec_checks+=2;
        for (phase,bits,len) in [(2,0,16),(0,3,128),(0,0,15)] {assert_eq!(PhaseSource::new(phase,bits,vec![[Fr::zero();3];len]).err(),Some(Error::Shape));math_checks+=1;}
        let source=u_source(0,&x,&w);let mut ledger=Vec::with_capacity(64);
        for(label,offset)in [("header-profile",0),("header-version",8),("header-phase",12),
            ("header-round",16),("header-remaining",20),("header-owner",24),("header-record-width",28),
            ("header-count",32),("header-original-count",40),("header-source-extent",48),
            ("header-prefix-count",56),("header-source",64),("header-prefix",128),
            ("header-descriptor",192),("header-reserved",60)] {
            rejected(label,Fault::Header(offset),Error::Header,&source,&mut evidence,&mut ledger);
        }
        for(label,fault,error)in [("short-header",Fault::ShortHeader,Error::Extent),("first-pass-seal",Fault::FirstSeal,Error::Seal),
            ("noncanonical",Fault::Noncanonical,Error::Canonical),("short-read",Fault::ShortRead,Error::Read),
            ("extra-record",Fault::Extra,Error::Extent),("read-io",Fault::Io,Error::Io),("between-pass",Fault::BetweenPass,Error::Seal),
            ("order-swap",Fault::Permute,Error::SourceOrder),("record-omitted",Fault::Omit,Error::SourceOrder),
            ("record-duplicate",Fault::Duplicate,Error::SourceOrder),("false-claim",Fault::Claim,Error::SumcheckIdentity)] {
            rejected(label,fault,error,&source,&mut evidence,&mut ledger);
        }
        #[cfg(windows)] {
            let open=OpenOptions::new().write(true).open(&evidence.tapes[0].path);
            assert_eq!(open.err().unwrap().raw_os_error(),Some(32));
            ledger.push(FaultRecord{label:"independent-writer",stage:"SharingViolation32",challenges:0});
        }
        // Semantic mutations are independent dense differentials, no forged source admission.
        let mut reference_t=Transcript::new(b"private-semantic-mutant");let reference=dense(&source,&mut reference_t);
        for(name,mut rows)in [("excluded-X",source.rows.clone()),("channel-swap",source.rows.clone()),
            ("bank-LSB",source.rows.clone()),("physical-bank-ordinal",source.rows.clone())] {
            if name=="excluded-X"{rows[8][2]=Fr::zero();}else if name=="channel-swap"{rows[0].swap(0,1);}
            else if name=="physical-bank-ordinal"{rows.swap(8,11);}else{rows.swap(0,1);}
            let mutant=PhaseSource::new(0,0,rows).unwrap();let mut t=Transcript::new(b"private-semantic-mutant");assert_ne!(dense(&mutant,&mut t),reference);math_checks+=1;
            ledger.push(FaultRecord{label:name,stage:"DenseDifferential",challenges:4});
        }
        let (x2,w2)=x_and_weights(1);let owner_source=u_source(1,&x2,&w2);
        let mut rows=owner_source.rows.clone();rows.swap(0,16);
        let owner_mutant=PhaseSource::new(0,1,rows).unwrap();
        let mut a=Transcript::new(b"owner-mutant");let mut b=a.clone();
        assert_ne!(dense(&owner_source,&mut a),dense(&owner_mutant,&mut b));math_checks+=1;
        ledger.push(FaultRecord{label:"owner-LSB",stage:"DenseDifferential",challenges:5});
        let mut a=Transcript::new(b"challenge-order-mutant");let mut b=a.clone();
        b.challenge_scalar(b"premature-bank-challenge");
        let expected=dense(&source,&mut a);let changed=dense(&source,&mut b);
        assert_ne!(expected.point,changed.point);assert_ne!(a.challenge_scalar(b"following-phase"),b.challenge_scalar(b"following-phase"));math_checks+=1;
        ledger.push(FaultRecord{label:"challenge-order",stage:"DenseDifferential",challenges:5});
        drop(owner_source);drop(owner_mutant);drop(x2);drop(w2);
        assert_eq!(ledger.len(),33);assert!(ledger.capacity()<=64);
        let mut byte_total=0u64;
        for tape in &mut evidence.tapes {
            let size=tape.file.metadata().unwrap().len();assert!(size<=MAX_FILE);byte_total+=size;
            tape.file.seek(SeekFrom::Start(0)).unwrap();let mut h=Blake2b512::new();let mut buf=[0u8;256];
            loop{let n=tape.file.read(&mut buf).unwrap();if n==0{break;}h.update(&buf[..n]);}
            tape.audit_seal=h.finalize().into();tape.audit_size=size;
        }
        assert_eq!(evidence.tapes.len(),59);assert_eq!(byte_total,100255);assert!(byte_total<=64*MAX_FILE);
        let owned=evidence.owned_bytes();let scratch=65536usize;
        // Conservative bounded small-fixture reserve for source/dense/round/codec/report vectors.
        let fixture_reserve=131072usize;
        let modeled=owned+scratch+fixture_reserve+64*std::mem::size_of::<FaultRecord>()+32768;
        assert!(modeled<=1048576);assert_eq!((phase_cases,math_checks,codec_checks),(8,14,8));
        let report=Diagnostic {
            schema:"private-high-phase-spool-v1",phase_cases,math_checks,codec_checks,
            negative_checks:ledger.len(),tape_members:evidence.tapes.len(),
            successful_read_bytes:metrics.read_bytes,written_bytes:metrics.write_bytes,
            records_read:metrics.records_read,quadratic_pairs:metrics.pairs,bank_rounds:metrics.rounds,
            retained_tape_bytes:byte_total,owned_evidence_capacity_bytes:owned,stream_scratch_reserve_bytes:scratch,
            fixture_reserve_bytes:fixture_reserve,modeled_local_payload_bytes:modeled,
            elapsed_seconds:started.elapsed().as_secs_f64(),dense_spool_equal:true,coupled_v_equal:true,
            continuation_equal:true,gkr_proof_created:false,pcs_proof_created:false,setup_invoked:false,
            global_admission:false,fault_ledger:&ledger,artifacts:ArtifactList(&evidence.tapes),
        };
        let bytes=serde_json::to_vec(&report).unwrap();assert!(bytes.len()<=16384 && bytes.capacity()<=32768);
        let path=evidence.root.join("phase-summary.json");let mut f=OpenOptions::new().write(true).create_new(true).open(path).unwrap();f.write_all(&bytes).unwrap();f.sync_all().unwrap();
        println!("high_phase_spool_differential {}",std::str::from_utf8(&bytes).unwrap());
        PreflightReceipt{phase_cases,math_checks,codec_checks,negative_checks:ledger.len(),
            tape_members:evidence.tapes.len(),retained_tape_bytes:byte_total,
            summary_blake2b512:hex(&digest(&bytes))}
    }
}

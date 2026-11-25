//! Autonomous seven-claim rectangular sumcheck over a Boolean packed MLE.
//! `Statement` is supplied independently of the proof; this module has no header profile.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use ark_serialize::CanonicalDeserialize;
use blake2::{Blake2b512, Digest};
use dory_pcs::backends::arkworks::{ArkDoryProof, ArkGT};
use std::time::Instant;

use crate::{packed::{self, PackedCommitted, PackedFile}, pcs::{self, Setup}, transcript::Transcript};

pub const PROFILE: &[u8] = b"packed-opening-batch-v1";
pub const DOMAIN: &[u8] = b"nipopow-packed-opening-batch-v1";
const MAGIC: &[u8; 8] = b"OPBAT001";
pub const CLAIMS: usize = 7;
const VERSION: u8 = 1;
const LAYOUT: &[u8] = b"bn254-fr-canonical32-lsb-low-column-high-row-v1";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Claim { pub point: Vec<Fr>, pub value: Fr }

/// Caller-owned expected public statement. No member is decoded from the proof.
#[derive(Clone)]
pub struct Statement {
    pub log_n: usize,
    pub setup_id: [u8; 32],
    pub commitment: ArkGT,
    pub corpus_id: Option<[u8; 32]>,
    pub claims: [Claim; CLAIMS],
}

pub struct Proof { pub rounds: Vec<[Fr; 3]>, pub terminal: Fr, pub pcs: ArkDoryProof }

#[derive(Clone, Default, Debug)]
pub struct Metrics {
    pub projection_seconds: f64,
    pub low_round_seconds: f64,
    pub transition_seconds: f64,
    pub high_round_seconds: f64,
    pub pcs_seconds: f64,
    pub projection_scans: usize,
    pub transition_scans: usize,
    pub maximum_fields: usize,
    pub pre_pcs_fields: usize,
    pub projected_capacity: usize,
    pub high_capacity: usize,
    pub row_capacity: usize,
    pub weight_capacity: usize,
}

fn admit(statement: &Statement, setup: &Setup) -> Result<(), String> {
    if statement.log_n > pcs::MAX_LOG_N || statement.log_n != setup.log_n
        || statement.setup_id != setup.id || statement.claims.iter().any(|c| c.point.len() != statement.log_n) {
        return Err("opening-batch expected statement/setup/dimension rejected".into());
    }
    Ok(())
}

#[derive(Clone,Copy)]
enum VerificationKey<'a> {
    Setup(&'a Setup),
    Admitted(&'a crate::verifier_key::AdmittedVerifierKey),
}

fn admit_verification_key(statement:&Statement,key:VerificationKey<'_>)->Result<(),String>{
    match key {
        VerificationKey::Setup(setup)=>admit(statement,setup),
        VerificationKey::Admitted(key)=>{
            if statement.log_n>pcs::MAX_VERIFY_LOG_N || statement.log_n!=key.log_n()
                || statement.setup_id!=*key.id()
                || statement.claims.iter().any(|claim|claim.point.len()!=statement.log_n) {
                return Err("opening-batch expected statement/verifier-key/dimension rejected".into());
            }
            Ok(())
        }
    }
}

fn bind(statement: &Statement, transcript: &mut Transcript) -> Result<(), String> {
    bind_frontend(statement,transcript,None)
}
fn bind_frontend(statement:&Statement,transcript:&mut Transcript,audit:Option<&mut FrontendAudit>)->Result<(),String>{
    transcript.append_bytes(b"opening-batch-profile", PROFILE);
    transcript.append_u64(b"opening-batch-version", VERSION as u64);
    transcript.append_bytes(b"opening-batch-layout", LAYOUT);
    transcript.append_u64(b"opening-batch-k", statement.log_n as u64);
    transcript.append_u64(b"opening-batch-sigma", statement.log_n.div_ceil(2) as u64);
    transcript.append_u64(b"opening-batch-nu", (statement.log_n / 2) as u64);
    transcript.append_u64(b"opening-batch-q", CLAIMS as u64);
    transcript.append_bytes(b"opening-batch-setup", &statement.setup_id);
    let commitment=pcs::encode_commitment(&statement.commitment)?;
    if audit.is_some() && (commitment.len()!=384||commitment.capacity()>512){
        return Err("frontend commitment serialization capacity drift".into());
    }
    transcript.append_bytes(b"opening-batch-commitment", &commitment);
    drop(commitment);
    transcript.append_u64(b"opening-batch-corpus-present", statement.corpus_id.is_some() as u64);
    if let Some(id) = statement.corpus_id { transcript.append_bytes(b"opening-batch-corpus-id", &id); }
    for (j, claim) in statement.claims.iter().enumerate() {
        transcript.append_u64(b"opening-batch-claim-index", j as u64);
        transcript.append_u64(b"opening-batch-point-length", claim.point.len() as u64);
        for x in &claim.point { transcript.append_scalar(b"opening-batch-coordinate", x); }
        transcript.append_scalar(b"opening-batch-claimed-value", &claim.value);
    }
    Ok(())
}

fn eq_point(a: &[Fr], b: &[Fr]) -> Fr {
    a.iter().zip(b).fold(Fr::one(), |acc, (x,y)| acc * ((Fr::one()-x)*(Fr::one()-y)+x*y))
}

fn weights(point: &[Fr]) -> Vec<Fr> {
    fill_weights(point, Vec::with_capacity(1usize<<point.len()))
}
fn fill_weights(point: &[Fr], mut result: Vec<Fr>) -> Vec<Fr> {
    result.push(Fr::one());
    for x in point {
        let len = result.len();
        result.resize(len*2,Fr::zero());
        for i in 0..len { let v=result[i]; result[i]=v*(Fr::one()-x); result[i+len]=v*x; }
    }
    result
}

fn eval_quadratic(c: &[Fr; 3], z: Fr) -> Fr { c[0] + z*(c[1]+z*c[2]) }
fn check_round(c: &[Fr; 3], prior: Fr) -> Result<(), String> {
    if c[0]+c[0]+c[1]+c[2] != prior { return Err("opening-batch round sum rejected".into()); }
    Ok(())
}
fn terminal(t: &mut Transcript, v: Fr) {
    t.append_scalar(b"opening-batch-terminal-value", &v);
    t.append_bytes(b"opening-batch-pcs-separator", b"unchanged-transparent-dory-v1");
}

trait RowSource {
    fn input_len(&self) -> usize;
    fn read_row(&self, width: usize, row: usize) -> Result<Vec<Fr>, String>;
}
impl RowSource for PackedFile {
    fn input_len(&self) -> usize { self.input_len() }
    fn read_row(&self, width: usize, row: usize) -> Result<Vec<Fr>, String> { crate::packed_rows::read_row(self, width, row) }
}
fn read_boolean<S: RowSource>(source: &S, width: usize, row: usize) -> Result<Vec<Fr>, String> {
    let values = source.read_row(width,row)?;
    if values.len()!=width { return Err("opening-batch short row".into()); }
    if values.iter().any(|v| !v.is_zero() && !v.is_one()) { return Err("opening-batch non-Boolean row".into()); }
    Ok(values)
}
fn fields(metrics: &mut Metrics, live: usize) { metrics.maximum_fields = metrics.maximum_fields.max(live); }

fn project_fused<S: RowSource>(source: &S, claims: &[Claim; CLAIMS], sigma: usize,
    width: usize, rows: usize, metrics: &mut Metrics) -> Result<Vec<Vec<Fr>>, String> {
    let mark = Instant::now();
    let high: [Vec<Fr>; CLAIMS] = std::array::from_fn(|j| weights(&claims[j].point[sigma..]));
    metrics.weight_capacity = metrics.weight_capacity.max(high.iter().map(Vec::capacity).max().unwrap_or(0));
    let mut projected: [Vec<Fr>; CLAIMS] = std::array::from_fn(|_| vec![Fr::zero(); width]);
    for h in 0..rows {
        let values = read_boolean(source, width, h)?;
        metrics.row_capacity = metrics.row_capacity.max(values.capacity());
        for (l, value) in values.iter().enumerate() {
            if value.is_one() {
                for j in 0..CLAIMS { projected[j][l] += high[j][h]; }
            }
        }
    }
    metrics.projection_seconds = mark.elapsed().as_secs_f64();
    metrics.projection_scans += 1;
    metrics.projected_capacity = metrics.projected_capacity.max(projected.iter().map(Vec::capacity).sum());
    let high_capacity = high.iter().map(Vec::capacity).sum::<usize>();
    let live = metrics.projected_capacity + high_capacity + metrics.row_capacity;
    fields(metrics, live);
    drop(high);
    Ok(projected.into_iter().collect())
}

#[cfg(test)]
fn project_reference<S: RowSource>(source: &S, claims: &[Claim; CLAIMS], sigma: usize,
    width: usize, rows: usize, metrics: &mut Metrics) -> Result<Vec<Vec<Fr>>, String> {
    let mark = Instant::now();
    let mut projected = Vec::with_capacity(CLAIMS);
    for claim in claims {
        let high = weights(&claim.point[sigma..]);
        let mut projection = vec![Fr::zero(); width];
        metrics.weight_capacity = metrics.weight_capacity.max(high.capacity());
        for h in 0..rows {
            let values = read_boolean(source, width, h)?;
            metrics.row_capacity = metrics.row_capacity.max(values.capacity());
            for l in 0..width { if values[l].is_one() { projection[l] += high[h]; } }
        }
        metrics.projection_scans += 1;
        projected.push(projection);
        let cap = projected.iter().map(Vec::capacity).sum::<usize>();
        metrics.projected_capacity = metrics.projected_capacity.max(cap);
        fields(metrics, cap + high.capacity() + metrics.row_capacity);
    }
    metrics.projection_seconds = mark.elapsed().as_secs_f64();
    Ok(projected)
}

enum ProjectionMode {
    Fused,
    #[cfg(test)]
    Reference,
}

// Private extraction shared with the sealed native32 diagnostic. A frontend is
// not an opening proof: the public producer must still call packed::open.
#[derive(Debug)]
struct Frontend {
    rounds: Vec<[Fr;3]>, terminal: Fr, point: Vec<Fr>, metrics: Metrics,
}

const FRONTEND_CAPACITY_LIMIT:usize=64*1024*1024;
const FRONTEND_PHASE_NAMES:[&str;8]=["admission_complete","projection_start","projection_done",
    "low_rounds_done","transition_start","transition_done","high_rounds_done","frontend_complete"];

#[derive(Clone,Copy,Debug,Default)]
struct FrontendPhaseMark { name:&'static str, elapsed_ns:u128 }

#[derive(Clone,Copy,Debug,Default,PartialEq,Eq)]
struct FrontendCapacityInventory {
    field_capacity_bytes:usize, descriptor_capacity_bytes:usize,
    row_scratch_capacity_bytes:usize, total_capacity_bytes:usize,
}

#[derive(Clone,Debug,Default)]
struct FrontendAuditStats {
    held_capacity_bytes:usize, fixed_capacity_bytes:usize, preflight_capacity_bound_bytes:usize,
    state_peak_capacity_bytes:usize, phase_peak_capacity_bytes:[usize;6],
    phase_peak_inventory:[FrontendCapacityInventory;6], row_loads:[usize;2],
    phase_marks:[FrontendPhaseMark;8],
}

struct FrontendAudit {
    stats:FrontendAuditStats, started:Instant, mark_count:usize, emit_marks:bool, dimension:usize,
    statement_point_capacity_bytes:usize,
}

fn frontend_add(a:usize,b:usize)->Result<usize,String>{a.checked_add(b).ok_or("frontend capacity addition overflow".into())}
fn frontend_mul(a:usize,b:usize)->Result<usize,String>{a.checked_mul(b).ok_or("frontend capacity product overflow".into())}
fn frontend_field_bytes(capacity:usize)->Result<usize,String>{frontend_mul(capacity,std::mem::size_of::<Fr>())}
fn frontend_vector_bytes<T>(values:&Vec<T>)->Result<usize,String>{frontend_mul(values.capacity(),std::mem::size_of::<T>())}
fn frontend_projected_bytes(values:&Vec<Vec<Fr>>)->Result<usize,String>{
    values.iter().try_fold(0usize,|sum,value|frontend_add(sum,frontend_vector_bytes(value)?))
}

impl FrontendAudit {
    // The child module owns sealed admission. This private value only meters
    // allocations; it grants no authority to manufacture a native statement.
    fn new(statement:&Statement,held_capacity_bytes:usize,emit_marks:bool)->Result<Self,String>{
        let k=statement.log_n;
        if k>32||k>=usize::BITS as usize||statement.claims.iter().any(|c|c.point.len()!=k){
            return Err("frontend audited dimensions rejected".into());
        }
        let point_bytes=statement.claims.iter().try_fold(0usize,|sum,claim|
            frontend_add(sum,frontend_vector_bytes(&claim.point)?))?;
        // Typed, bounded local storage, not a megabyte padding allowance:
        // powers7 + mu7 + polynomial3 + phase scalar locals8 + inner locals6
        // + equality builder locals3 + packed Boolean constants2 =36 Fr.
        // The Vec headers include both projection arrays and overlapping
        // builder/row/return headers; dynamic outer descriptors are separate.
        // Transcript scratch covers its cloned hash/digest, query growth to64,
        // a <=62-byte challenge frame and32-byte scalar serialization. Bind's
        // 384-byte codec can transiently overlap old256/new512-byte allocations;
        // all768 bytes are reserved before binding and its final cap is checked.
        let mut fixed=frontend_add(std::mem::size_of::<Statement>(),point_bytes)?;
        for size in [std::mem::size_of::<Transcript>(),std::mem::size_of::<FrontendAudit>(),
            2*std::mem::size_of::<Frontend>(),std::mem::size_of::<Metrics>(),
            (2*CLAIMS+8)*std::mem::size_of::<Vec<Fr>>(),std::mem::size_of::<Vec<Vec<Fr>>>(),
            36*std::mem::size_of::<Fr>(),32*std::mem::size_of::<usize>(),
            std::mem::size_of::<Transcript>()+64+16+64+62+32+768+4*std::mem::size_of::<Vec<u8>>()]{
            fixed=frontend_add(fixed,size)?;
        }
        let c=1usize.checked_shl(k.div_ceil(2) as u32).ok_or("frontend column shift overflow")?;
        let rows=1usize.checked_shl((k/2) as u32).ok_or("frontend row shift overflow")?;
        let width=c.max(rows);
        let projection_fields=frontend_add(frontend_mul(2*CLAIMS+1,width)?,frontend_mul(4,k)?)?;
        let descriptors=frontend_mul(CLAIMS,std::mem::size_of::<Vec<Fr>>())?;
        let scratch=frontend_add(c.div_ceil(8),std::mem::size_of::<Vec<u8>>())?;
        let bound=frontend_add(frontend_add(frontend_add(frontend_add(held_capacity_bytes,fixed)?,
            frontend_field_bytes(projection_fields)?)?,descriptors)?,scratch)?;
        if bound>FRONTEND_CAPACITY_LIMIT{return Err("frontend preflight exceeds64MiB".into());}
        let mut audit=Self{stats:FrontendAuditStats{held_capacity_bytes,fixed_capacity_bytes:fixed,
            preflight_capacity_bound_bytes:bound,..Default::default()},started:Instant::now(),
            mark_count:0,emit_marks,dimension:k,statement_point_capacity_bytes:point_bytes};
        audit.record(0,0,0,0)?;
        Ok(audit)
    }
    fn record(&mut self,phase:usize,fields:usize,descriptors:usize,row_scratch:usize)->Result<(),String>{
        if phase>=6{return Err("frontend capacity phase outside ledger".into());}
        let total=frontend_add(frontend_add(frontend_add(frontend_add(self.stats.held_capacity_bytes,
            self.stats.fixed_capacity_bytes)?,fields)?,descriptors)?,row_scratch)?;
        if total>FRONTEND_CAPACITY_LIMIT||total>self.stats.preflight_capacity_bound_bytes{
            return Err("frontend live capacity exceeds checked bound".into());
        }
        if total>self.stats.phase_peak_capacity_bytes[phase]{
            self.stats.phase_peak_capacity_bytes[phase]=total;
            self.stats.phase_peak_inventory[phase]=FrontendCapacityInventory{field_capacity_bytes:fields,
                descriptor_capacity_bytes:descriptors,row_scratch_capacity_bytes:row_scratch,total_capacity_bytes:total};
        }
        self.stats.state_peak_capacity_bytes=self.stats.state_peak_capacity_bytes.max(total);
        Ok(())
    }
    fn mark(&mut self,index:usize)->Result<(),String>{
        if index!=self.mark_count||index>=FRONTEND_PHASE_NAMES.len(){return Err("frontend phase order drift".into());}
        let mark=FrontendPhaseMark{name:FRONTEND_PHASE_NAMES[index],elapsed_ns:self.started.elapsed().as_nanos()};
        if self.emit_marks{
            use std::io::Write;
            let mut output=std::io::stdout().lock();
            if index==0{writeln!(output).map_err(|_|"frontend phase newline failed")?;}
            writeln!(output,"NIPOPOW_OPENING_FRONTEND_PHASE {{\"name\":\"{}\",\"elapsed_ns\":{}}}",mark.name,mark.elapsed_ns)
                .map_err(|_|"frontend phase write failed")?;
            output.flush().map_err(|_|"frontend phase flush failed")?;
        }
        self.stats.phase_marks[index]=mark;self.mark_count+=1;Ok(())
    }
}

fn frontend_record(audit:&mut Option<&mut FrontendAudit>,phase:usize,fields:usize,
    descriptors:usize,row_scratch:usize)->Result<(),String>{
    if let Some(audit)=audit.as_deref_mut(){audit.record(phase,fields,descriptors,row_scratch)?;}Ok(())
}
fn frontend_mark(audit:&mut Option<&mut FrontendAudit>,index:usize)->Result<(),String>{
    if let Some(audit)=audit.as_deref_mut(){audit.mark(index)?;}Ok(())
}
fn frontend_reserve<T>(count:usize,audit:&mut Option<&mut FrontendAudit>,phase:usize,
    live_fields:usize,live_descriptors:usize,descriptor:bool)->Result<Vec<T>,String>{
    if audit.is_none(){return Ok(Vec::with_capacity(count));}
    let bytes=frontend_mul(count,std::mem::size_of::<T>())?;
    let fields=frontend_add(live_fields,if descriptor{0}else{bytes})?;
    let descriptors=frontend_add(live_descriptors,if descriptor{bytes}else{0})?;
    frontend_record(audit,phase,fields,descriptors,0)?;
    let mut result=Vec::new();result.try_reserve_exact(count).map_err(|_|"frontend reservation failed")?;
    // Fail on excess actual capacity; no following allocation or witness read.
    let actual=frontend_vector_bytes(&result)?;
    frontend_record(audit,phase,frontend_add(live_fields,if descriptor{0}else{actual})?,
        frontend_add(live_descriptors,if descriptor{actual}else{0})?,0)?;
    if result.capacity()!=count{return Err("frontend exact reservation capacity drift".into());}
    Ok(result)
}
fn frontend_weights(point:&[Fr],audit:&mut Option<&mut FrontendAudit>,phase:usize,
    live_fields:usize,descriptors:usize)->Result<Vec<Fr>,String>{
    if audit.is_none(){return Ok(weights(point));}
    let count=1usize.checked_shl(point.len() as u32).ok_or("frontend equality shift overflow")?;
    let values=frontend_reserve(count,audit,phase,live_fields,descriptors,false)?;
    Ok(fill_weights(point,values))
}
fn frontend_read_boolean<S:RowSource>(source:&S,width:usize,row:usize,audit:&mut Option<&mut FrontendAudit>,
    scan:usize,phase:usize,live_fields:usize,descriptors:usize)->Result<Vec<Fr>,String>{
    if audit.is_none(){return read_boolean(source,width,row);}
    if scan>=2{return Err("frontend scan outside ledger".into());}
    let scratch=frontend_add(width.div_ceil(8),std::mem::size_of::<Vec<u8>>())?;
    frontend_record(audit,phase,frontend_add(live_fields,frontend_field_bytes(width)?)?,descriptors,scratch)?;
    let values=read_boolean(source,width,row)?;
    frontend_record(audit,phase,frontend_add(live_fields,frontend_vector_bytes(&values)?)?,descriptors,scratch)?;
    if values.capacity()>width{return Err("frontend row capacity exceeds declared width".into());}
    let audit=audit.as_deref_mut().ok_or("frontend audit missing")?;
    audit.stats.row_loads[scan]=audit.stats.row_loads[scan].checked_add(1).ok_or("frontend row counter overflow")?;
    Ok(values)
}

fn project_fused_audited<S:RowSource>(source:&S,claims:&[Claim;CLAIMS],sigma:usize,width:usize,rows:usize,
    metrics:&mut Metrics,audit:&mut Option<&mut FrontendAudit>,retained_fields:usize)->Result<Vec<Vec<Fr>>,String>{
    if audit.is_none(){return project_fused(source,claims,sigma,width,rows,metrics);}
    let mark=Instant::now();
    let mut high:[Vec<Fr>;CLAIMS]=std::array::from_fn(|_|Vec::new());
    let mut projected:[Vec<Fr>;CLAIMS]=std::array::from_fn(|_|Vec::new());
    let mut live=retained_fields;
    for j in 0..CLAIMS{
        high[j]=frontend_weights(&claims[j].point[sigma..],audit,1,live,0)?;
        live=frontend_add(live,frontend_vector_bytes(&high[j])?)?;
    }
    metrics.weight_capacity=metrics.weight_capacity.max(high.iter().map(Vec::capacity).max().unwrap_or(0));
    for bank in &mut projected{
        *bank=frontend_reserve(width,audit,1,live,0,false)?;bank.resize(width,Fr::zero());
        live=frontend_add(live,frontend_vector_bytes(bank)?)?;
    }
    for h in 0..rows{
        let values=frontend_read_boolean(source,width,h,audit,0,1,live,0)?;
        metrics.row_capacity=metrics.row_capacity.max(values.capacity());
        for (l,value) in values.iter().enumerate(){if value.is_one(){for j in 0..CLAIMS{projected[j][l]+=high[j][h];}}}
    }
    metrics.projection_seconds=mark.elapsed().as_secs_f64();metrics.projection_scans+=1;
    metrics.projected_capacity=projected.iter().map(Vec::capacity).sum();
    let live_fields=metrics.projected_capacity+high.iter().map(Vec::capacity).sum::<usize>()+metrics.row_capacity;
    fields(metrics,live_fields);
    drop(high);
    let bank_bytes=projected.iter().try_fold(retained_fields,|sum,bank|frontend_add(sum,frontend_vector_bytes(bank)?))?;
    let mut result=frontend_reserve(CLAIMS,audit,1,bank_bytes,0,true)?;
    result.extend(projected);
    Ok(result)
}

/// Returns a complete proof and a ledger. Production challenges are sampled only by Transcript.
pub fn prove(source: &PackedFile, committed: &PackedCommitted, setup: &Setup,
    statement: &Statement) -> Result<(Proof, Metrics, Transcript), String> {
    let mut transcript=Transcript::new(DOMAIN);
    let (proof, metrics)=prove_on(source, committed, setup, statement, &mut transcript, None)?;
    Ok((proof,metrics,transcript))
}

fn prove_on<S: RowSource + 'static>(source: &S, committed: &PackedCommitted, setup: &Setup,
    statement: &Statement, transcript: &mut Transcript, #[allow(unused_variables)] controlled: Option<&[Fr]>)
    -> Result<(Proof, Metrics), String> {
    prove_on_mode(source, committed, setup, statement, transcript, controlled, ProjectionMode::Fused)
}

#[cfg(test)]
fn prove_on_reference<S: RowSource + 'static>(source: &S, committed: &PackedCommitted, setup: &Setup,
    statement: &Statement, transcript: &mut Transcript, controlled: Option<&[Fr]>)
    -> Result<(Proof, Metrics), String> {
    prove_on_mode(source, committed, setup, statement, transcript, controlled, ProjectionMode::Reference)
}

fn prove_on_mode<S: RowSource + 'static>(source: &S, committed: &PackedCommitted, setup: &Setup,
    statement: &Statement, transcript: &mut Transcript, #[allow(unused_variables)] controlled: Option<&[Fr]>,
    projection_mode: ProjectionMode) -> Result<(Proof, Metrics), String> {
    admit(statement,setup)?;
    if source.input_len()!=1usize<<statement.log_n || committed.nu!=statement.log_n/2
        || committed.sigma!=statement.log_n.div_ceil(2)
        || pcs::encode_commitment(&committed.commitment)?!=pcs::encode_commitment(&statement.commitment)? {
        return Err("opening-batch source/commitment mismatch".into());
    }
    let Frontend{rounds,terminal:value,point:challenges,mut metrics}=
        prove_frontend_on_mode(source,statement,transcript,controlled,projection_mode,None)?;
    let mark=Instant::now();
    // This exact unchanged API is the sole opening and always runs, including W(z)=0.
    // The generic reader exists only to isolate row failures in direct tests.
    let packed = (source as &dyn std::any::Any).downcast_ref::<PackedFile>()
        .ok_or("opening-batch PCS requires packed source")?;
    let pcs=packed::open(committed,packed,&challenges,setup,transcript)?;
    metrics.pcs_seconds=mark.elapsed().as_secs_f64();
    Ok((Proof{rounds,terminal:value,pcs},metrics))
}

fn prove_frontend_on_mode<S:RowSource>(source:&S,statement:&Statement,transcript:&mut Transcript,
    controlled:Option<&[Fr]>,projection_mode:ProjectionMode,mut audit:Option<&mut FrontendAudit>)
    ->Result<Frontend,String>{
    if let Some(audit)=audit.as_deref(){
        let point_bytes=statement.claims.iter().try_fold(0usize,|sum,claim|
            frontend_add(sum,frontend_vector_bytes(&claim.point)?))?;
        if audit.dimension!=statement.log_n||statement.claims.iter().any(|c|c.point.len()!=statement.log_n)
            ||audit.statement_point_capacity_bytes!=point_bytes
            ||source.input_len()!=1usize.checked_shl(statement.log_n as u32).ok_or("frontend source shift overflow")?{
            return Err("frontend audited source/statement dimensions rejected".into());
        }
        match &projection_mode{ProjectionMode::Fused=>{},#[cfg(test)] ProjectionMode::Reference=>{
            return Err("frontend audit requires one fused projection scan".into());}}
    }
    frontend_mark(&mut audit,0)?;
    bind_frontend(statement,transcript,audit.as_deref_mut())?;
    let k=statement.log_n; let sigma=k.div_ceil(2); let nu=k/2;
    let c=1usize<<sigma; let rows=1usize<<nu;
    let mut metrics=Metrics::default();
    let mut challenges=frontend_reserve(k,&mut audit,0,0,0,false)?;
    let alpha=challenge(transcript,b"opening-batch-alpha",controlled,0)?;
    let mut powers=[Fr::one();CLAIMS];
    for j in 1..CLAIMS {powers[j]=powers[j-1]*alpha;}
    let mut sum=Fr::zero();
    for j in 0..CLAIMS {sum+=powers[j]*statement.claims[j].value;}
    frontend_mark(&mut audit,1)?;
    let mut projected = match projection_mode {
        ProjectionMode::Fused => project_fused_audited(source, &statement.claims, sigma, c, rows,
            &mut metrics,&mut audit,frontend_vector_bytes(&challenges)?)?,
        #[cfg(test)]
        ProjectionMode::Reference => project_reference(source, &statement.claims, sigma, c, rows, &mut metrics)?,
    };
    frontend_mark(&mut audit,2)?;
    let mut mu=powers;
    let descriptor_bytes=frontend_vector_bytes(&projected)?;
    let projected_bytes=frontend_projected_bytes(&projected)?;
    let mut rounds=frontend_reserve(k,&mut audit,2,
        frontend_add(projected_bytes,frontend_vector_bytes(&challenges)?)?,descriptor_bytes,false)?;
    let mark=Instant::now();
    for t in 0..sigma {
        let mut coeff=[Fr::zero();3];
        for j in 0..CLAIMS {
            let live=frontend_add(frontend_add(projected_bytes,frontend_vector_bytes(&challenges)?)?,frontend_vector_bytes(&rounds)?)?;
            let suffix=frontend_weights(&statement.claims[j].point[t+1..sigma],&mut audit,2,live,descriptor_bytes)?;
            metrics.weight_capacity=metrics.weight_capacity.max(suffix.capacity());
            let a=statement.claims[j].point[t]; let beta0=Fr::one()-a; let beta1=a+a-Fr::one();
            for (u,e) in suffix.iter().enumerate() {
                let c0=projected[j][2*u]; let delta=projected[j][2*u+1]-c0;
                let w=mu[j]*e;
                coeff[0]+=w*beta0*c0;
                coeff[1]+=w*(beta0*delta+beta1*c0);
                coeff[2]+=w*beta1*delta;
            }
            fields(&mut metrics,projected.iter().map(Vec::capacity).sum::<usize>()+suffix.capacity());
        }
        check_round(&coeff,sum)?;
        let z=append_round_challenge(transcript,0,t,&coeff,controlled,t+1)?;
        sum=eval_quadratic(&coeff,z);
        challenges.push(z);
        for j in 0..CLAIMS {
            let len=projected[j].len()/2;
            for u in 0..len {let c0=projected[j][2*u];projected[j][u]=c0+z*(projected[j][2*u+1]-c0);}
            projected[j].truncate(len);
            let a=statement.claims[j].point[t];mu[j]*=(Fr::one()-a)+(a+a-Fr::one())*z;
        }
        rounds.push(coeff);
    }
    metrics.low_round_seconds=mark.elapsed().as_secs_f64();
    let mut joined=Fr::zero();for j in 0..CLAIMS {joined+=mu[j]*projected[j][0];}
    if joined!=sum { return Err("opening-batch low join rejected".into()); }
    frontend_record(&mut audit,2,frontend_add(frontend_add(projected_bytes,frontend_vector_bytes(&challenges)?)?,
        frontend_vector_bytes(&rounds)?)?,descriptor_bytes,0)?;
    frontend_mark(&mut audit,3)?;
    drop(projected);
    frontend_mark(&mut audit,4)?;
    let mark=Instant::now();
    let retained=frontend_add(frontend_vector_bytes(&challenges)?,frontend_vector_bytes(&rounds)?)?;
    let low_weight=frontend_weights(&challenges,&mut audit,3,retained,0)?;
    metrics.weight_capacity=metrics.weight_capacity.max(low_weight.capacity());
    let low_bytes=frontend_vector_bytes(&low_weight)?;
    let mut f=frontend_reserve(rows,&mut audit,3,frontend_add(retained,low_bytes)?,0,false)?;
    f.resize(rows,Fr::zero());
    for h in 0..rows {
        let live=frontend_add(frontend_add(retained,low_bytes)?,frontend_vector_bytes(&f)?)?;
        let values=frontend_read_boolean(source,c,h,&mut audit,1,3,live,0)?;
        metrics.row_capacity=metrics.row_capacity.max(values.capacity());
        for l in 0..c {if values[l].is_one() {f[h]+=low_weight[l];}}
    }
    metrics.transition_scans=1;
    let mut b=frontend_reserve(rows,&mut audit,3,
        frontend_add(frontend_add(retained,low_bytes)?,frontend_vector_bytes(&f)?)?,0,false)?;
    b.resize(rows,Fr::zero());
    for j in 0..CLAIMS {
        let live=frontend_add(frontend_add(frontend_add(retained,low_bytes)?,frontend_vector_bytes(&f)?)?,frontend_vector_bytes(&b)?)?;
        let high=frontend_weights(&statement.claims[j].point[sigma..],&mut audit,3,live,0)?;
        metrics.weight_capacity=metrics.weight_capacity.max(high.capacity());
        for h in 0..rows {b[h]+=mu[j]*high[h];}
        let live=low_weight.capacity()+f.capacity()+b.capacity()+high.capacity()+metrics.row_capacity;
        fields(&mut metrics,live);
    }
    metrics.high_capacity=f.capacity()+b.capacity();
    let actual=(0..rows).fold(Fr::zero(),|s,h| s+f[h]*b[h]);
    if actual!=sum {return Err("opening-batch high join rejected".into());}
    drop(low_weight);
    metrics.transition_seconds=mark.elapsed().as_secs_f64();
    frontend_mark(&mut audit,5)?;
    frontend_record(&mut audit,4,frontend_add(frontend_add(retained,frontend_vector_bytes(&f)?)?,frontend_vector_bytes(&b)?)?,0,0)?;
    let mark=Instant::now();
    for t in 0..nu {
        let mut coeff=[Fr::zero();3];
        for u in 0..f.len()/2 {
            let f0=f[2*u];let b0=b[2*u];let df=f[2*u+1]-f0;let db=b[2*u+1]-b0;
            coeff[0]+=f0*b0;coeff[1]+=f0*db+b0*df;coeff[2]+=df*db;
        }
        check_round(&coeff,sum)?;
        let z=append_round_challenge(transcript,1,sigma+t,&coeff,controlled,sigma+t+1)?;
        sum=eval_quadratic(&coeff,z);challenges.push(z);
        let len=f.len()/2;
        for u in 0..len {let f0=f[2*u];let b0=b[2*u];f[u]=f0+z*(f[2*u+1]-f0);b[u]=b0+z*(b[2*u+1]-b0);}
        f.truncate(len);b.truncate(len);rounds.push(coeff);
    }
    metrics.high_round_seconds=mark.elapsed().as_secs_f64();
    frontend_mark(&mut audit,6)?;
    let value=f[0];
    let mut wz=Fr::zero();for j in 0..CLAIMS {wz+=powers[j]*eq_point(&statement.claims[j].point,&challenges);}
    if sum!=value*wz {return Err("opening-batch terminal relation rejected".into());}
    drop(f);drop(b);
    metrics.pre_pcs_fields=0;
    terminal(transcript,value);
    frontend_record(&mut audit,5,retained,0,0)?;
    if let Some(audit)=audit.as_deref(){
        if audit.stats.row_loads!=[rows,rows]||metrics.projection_scans!=1||metrics.transition_scans!=1
            ||rounds.len()!=k||challenges.len()!=k{return Err("frontend completion census drift".into());}
    }
    frontend_mark(&mut audit,7)?;
    Ok(Frontend{rounds,terminal:value,point:challenges,metrics})
}

// Prototype-only source for the same frontend algebra with no per-row field
// expansion. The source digest is supplied by the caller, not inferred from a
// reader that may fail or drift between the two frontend passes.
trait BitRowSource {
    fn input_len(&self)->usize;
    fn read_row_bits(&self,width:usize,row:usize)->Result<Vec<u8>,String>;
    fn scan_rows(&self,width:usize,mut consume:impl FnMut(usize,&[u8])->Result<(),String>)
        ->Result<(),String>{
        if width<8 || !width.is_power_of_two() || self.input_len()%width!=0 {
            return Err("opening-batch bit source row geometry".into());
        }
        for row in 0..self.input_len()/width {
            let bytes=self.read_row_bits(width,row)?;
            if bytes.len()!=width/8 {return Err("opening-batch bit row length drift".into());}
            consume(row,&bytes)?;
        }
        Ok(())
    }
}
impl BitRowSource for PackedFile {
    fn input_len(&self)->usize{self.input_len()}
    fn read_row_bits(&self,width:usize,row:usize)->Result<Vec<u8>,String>{self.read_row_bits(width,row)}
}

struct NativeCheckedBitRows<'s,'p,'n,'c> {
    source:&'s crate::packed_owner_assembly::NativePcsSource<'p,'n>,
    committed:&'c packed::NativePcsCommitted,
    setup:&'c Setup,
}
impl BitRowSource for NativeCheckedBitRows<'_,'_,'_,'_> {
    fn input_len(&self)->usize{self.source.input_len()}
    fn read_row_bits(&self,_width:usize,_row:usize)->Result<Vec<u8>,String>{
        Err("native PCS requires a complete sequential pass".into())
    }
    fn scan_rows(&self,width:usize,consume:impl FnMut(usize,&[u8])->Result<(),String>)
        ->Result<(),String>{
        if width!=crate::packed_owner_assembly::NativePcsSource::ROW_BITS {
            return Err("native PCS frontend row width mismatch".into());
        }
        packed::scan_native_verified(self.source,self.committed,self.setup,consume)
    }
}

fn require_pass_digest(digest:Blake2b512,expected:&[u8;64])->Result<(),String>{
    if digest.finalize().as_slice()!=expected{return Err("opening-batch bit source digest mismatch".into());}
    Ok(())
}

fn prove_frontend_bitpacked_on<S:BitRowSource>(source:&S,statement:&Statement,
    expected_digest:Option<&[u8;64]>,transcript:&mut Transcript)->Result<Frontend,String>{
    let k=statement.log_n;
    let sigma=k.div_ceil(2);
    let nu=k/2;
    let dim=packed::bitpacked_dimensions(k,source.input_len())?;
    let width=dim.width;
    let rows=dim.rows;
    bind_frontend(statement,transcript,None)?;
    let mut metrics=Metrics::default();
    let alpha=challenge(transcript,b"opening-batch-alpha",None,0)?;
    let mut powers=[Fr::one();CLAIMS];
    for j in 1..CLAIMS {powers[j]=powers[j-1]*alpha;}
    let mut sum=Fr::zero();
    for j in 0..CLAIMS {sum+=powers[j]*statement.claims[j].value;}

    let mark=Instant::now();
    let high:[Vec<Fr>;CLAIMS]=std::array::from_fn(|j|weights(&statement.claims[j].point[sigma..]));
    let mut projected:[Vec<Fr>;CLAIMS]=std::array::from_fn(|_|vec![Fr::zero();width]);
    let mut first_digest=Blake2b512::new();
    let mut first_count=0usize;
    source.scan_rows(width,|h,bytes|{
        if h!=first_count || bytes.len()!=width/8 {return Err("opening-batch bit first pass row order/width".into());}
        first_digest.update(bytes);
        metrics.row_capacity=metrics.row_capacity.max(bytes.len());
        for l in 0..width {
            if bytes[l/8]>>(l%8)&1!=0 {
                for j in 0..CLAIMS {projected[j][l]+=high[j][h];}
            }
        }
        first_count+=1;Ok(())
    })?;
    if first_count!=rows{return Err("opening-batch bit first pass row count".into());}
    if let Some(expected)=expected_digest {require_pass_digest(first_digest,expected)?;}
    metrics.projection_seconds=mark.elapsed().as_secs_f64();
    metrics.projection_scans=1;
    metrics.projected_capacity=projected.iter().map(Vec::capacity).sum();
    metrics.weight_capacity=high.iter().map(Vec::capacity).max().unwrap_or(0);
    let live_fields=metrics.projected_capacity+high.iter().map(Vec::capacity).sum::<usize>();
    fields(&mut metrics,live_fields);
    drop(high);

    let mut mu=powers;
    let mut challenges=Vec::with_capacity(k);
    let mut rounds=Vec::with_capacity(k);
    let mark=Instant::now();
    for t in 0..sigma {
        let mut coeff=[Fr::zero();3];
        for j in 0..CLAIMS {
            let suffix=weights(&statement.claims[j].point[t+1..sigma]);
            metrics.weight_capacity=metrics.weight_capacity.max(suffix.capacity());
            let a=statement.claims[j].point[t];let beta0=Fr::one()-a;let beta1=a+a-Fr::one();
            for (u,e) in suffix.iter().enumerate() {
                let c0=projected[j][2*u];let delta=projected[j][2*u+1]-c0;
                let w=mu[j]*e;
                coeff[0]+=w*beta0*c0;
                coeff[1]+=w*(beta0*delta+beta1*c0);
                coeff[2]+=w*beta1*delta;
            }
            let live_fields=metrics.projected_capacity+suffix.capacity();
            fields(&mut metrics,live_fields);
        }
        check_round(&coeff,sum)?;
        let z=append_round_challenge(transcript,0,t,&coeff,None,t+1)?;
        sum=eval_quadratic(&coeff,z);challenges.push(z);
        for j in 0..CLAIMS {
            let len=projected[j].len()/2;
            for u in 0..len {let c0=projected[j][2*u];projected[j][u]=c0+z*(projected[j][2*u+1]-c0);}
            projected[j].truncate(len);
            let a=statement.claims[j].point[t];mu[j]*=(Fr::one()-a)+(a+a-Fr::one())*z;
        }
        rounds.push(coeff);
    }
    metrics.low_round_seconds=mark.elapsed().as_secs_f64();
    let mut joined=Fr::zero();for j in 0..CLAIMS {joined+=mu[j]*projected[j][0];}
    if joined!=sum{return Err("opening-batch bit low join rejected".into());}
    drop(projected);

    let mark=Instant::now();
    let low_weight=weights(&challenges);
    let mut f=vec![Fr::zero();rows];
    let mut second_digest=Blake2b512::new();
    let mut second_count=0usize;
    source.scan_rows(width,|h,bytes|{
        if h!=second_count || bytes.len()!=width/8 {return Err("opening-batch bit second pass row order/width".into());}
        second_digest.update(bytes);
        metrics.row_capacity=metrics.row_capacity.max(bytes.len());
        for l in 0..width {if bytes[l/8]>>(l%8)&1!=0 {f[h]+=low_weight[l];}}
        second_count+=1;Ok(())
    })?;
    if second_count!=rows{return Err("opening-batch bit second pass row count".into());}
    if let Some(expected)=expected_digest {require_pass_digest(second_digest,expected)?;}
    metrics.transition_scans=1;
    let mut b=vec![Fr::zero();rows];
    for j in 0..CLAIMS {
        let high=weights(&statement.claims[j].point[sigma..]);
        metrics.weight_capacity=metrics.weight_capacity.max(high.capacity());
        for h in 0..rows {b[h]+=mu[j]*high[h];}
        fields(&mut metrics,low_weight.capacity()+f.capacity()+b.capacity()+high.capacity());
    }
    metrics.high_capacity=f.capacity()+b.capacity();
    let actual=(0..rows).fold(Fr::zero(),|s,h|s+f[h]*b[h]);
    if actual!=sum{return Err("opening-batch bit high join rejected".into());}
    drop(low_weight);
    metrics.transition_seconds=mark.elapsed().as_secs_f64();

    let mark=Instant::now();
    for t in 0..nu {
        let mut coeff=[Fr::zero();3];
        for u in 0..f.len()/2 {
            let f0=f[2*u];let b0=b[2*u];let df=f[2*u+1]-f0;let db=b[2*u+1]-b0;
            coeff[0]+=f0*b0;coeff[1]+=f0*db+b0*df;coeff[2]+=df*db;
        }
        check_round(&coeff,sum)?;
        let z=append_round_challenge(transcript,1,sigma+t,&coeff,None,sigma+t+1)?;
        sum=eval_quadratic(&coeff,z);challenges.push(z);
        let len=f.len()/2;
        for u in 0..len {let f0=f[2*u];let b0=b[2*u];f[u]=f0+z*(f[2*u+1]-f0);b[u]=b0+z*(b[2*u+1]-b0);}
        f.truncate(len);b.truncate(len);rounds.push(coeff);
    }
    metrics.high_round_seconds=mark.elapsed().as_secs_f64();
    let value=f[0];
    let mut wz=Fr::zero();for j in 0..CLAIMS {wz+=powers[j]*eq_point(&statement.claims[j].point,&challenges);}
    if sum!=value*wz{return Err("opening-batch bit terminal relation rejected".into());}
    metrics.pre_pcs_fields=0;
    terminal(transcript,value);
    Ok(Frontend{rounds,terminal:value,point:challenges,metrics})
}

/// Private producer experiment; the public producer and its k24 admission stay unchanged.
pub(crate) fn prove_bitpacked_precomputed_v(source:&PackedFile,committed:&PackedCommitted,
    setup:&Setup,statement:&Statement,expected_digest:&[u8;64])
    ->Result<(Proof,Metrics,Transcript),String>{
    admit(statement,setup)?;
    if source.input_len()!=1usize<<statement.log_n || committed.nu!=statement.log_n/2
        || committed.sigma!=statement.log_n.div_ceil(2)
        || pcs::encode_commitment(&committed.commitment)?!=pcs::encode_commitment(&statement.commitment)? {
        return Err("opening-batch bit source/commitment mismatch".into());
    }
    let mut transcript=Transcript::new(DOMAIN);
    let frontend=prove_frontend_bitpacked_on(source,statement,Some(expected_digest),&mut transcript)?;
    let point=frontend.point.clone();
    let (proof,metrics)=finish_bitpacked_precomputed_v(
        source,committed,setup,expected_digest,frontend,&point,&mut transcript)?;
    Ok((proof,metrics,transcript))
}

/// Complete producer-backed N3/H2 opening. A caller's transcript receives no
/// frontend or PCS state until every fresh native source pass and proof succeeds.
pub(crate) fn prove_native_on(
    source:&crate::packed_owner_assembly::NativePcsSource<'_,'_>,
    committed:&packed::NativePcsCommitted,setup:&Setup,statement:&Statement,
    transcript:&mut Transcript,
)->Result<(Proof,Metrics),String>{
    admit(statement,setup)?;
    if statement.log_n!=crate::packed_owner_assembly::NativePcsSource::LOG_N
        || source.input_len()!=1usize<<statement.log_n
        || committed.packed().nu!=statement.log_n/2
        || committed.packed().sigma!=statement.log_n.div_ceil(2)
        || pcs::encode_commitment(&committed.commitment())?
            !=pcs::encode_commitment(&statement.commitment)? {
        return Err("opening-batch native source/commitment mismatch".into());
    }
    let mut next=transcript.clone();
    let checked=NativeCheckedBitRows{source,committed,setup};
    let Frontend{rounds,terminal:value,point,mut metrics}=
        prove_frontend_bitpacked_on(&checked,statement,None,&mut next)?;
    let mark=Instant::now();
    let pcs=packed::open_native(source,committed,setup,&point,&mut next)?;
    metrics.pcs_seconds=mark.elapsed().as_secs_f64();
    *transcript=next;
    Ok((Proof{rounds,terminal:value,pcs},metrics))
}

fn finish_bitpacked_precomputed_v(source:&PackedFile,committed:&PackedCommitted,setup:&Setup,
    expected_digest:&[u8;64],frontend:Frontend,pcs_point:&[Fr],transcript:&mut Transcript)
    ->Result<(Proof,Metrics),String>{
    let Frontend{rounds,terminal:value,point,mut metrics}=frontend;
    if point!=pcs_point{return Err("opening-batch PCS point drift".into());}
    let mark=Instant::now();
    let pcs=packed::open_precomputed_v_bound(source,committed,setup,&point,expected_digest,transcript)?;
    metrics.pcs_seconds=mark.elapsed().as_secs_f64();
    Ok((Proof{rounds,terminal:value,pcs},metrics))
}

#[cfg(test)]
#[path="opening_batch_native32_tests.rs"]
mod native32_tests;

#[cfg(test)]
#[path="c329_native_pcs_tests.rs"]
mod c329_native_pcs_tests;

#[cfg(test)]
#[path="native_prefix_seven_join.rs"]
mod native_seven_join;

#[cfg(test)]
#[path="historical_prefix_seven_common51_tests.rs"]
mod historical_seven_common51;

/// Diagnostic H21 producer join. This admission owns the exact regenerated
/// log41 prover key; ordinary setup and opening admissions remain unchanged.
/// Neither a session nor its serialized output certifies a history.
#[cfg(test)]
pub(crate) mod h21_producer {
    use super::*;
    use crate::packed::UntrustedH21CandidateFile;

    pub(crate) struct H21PcsProver { setup: Setup }

    impl H21PcsProver {
        pub(crate) fn regenerate(mark: impl Fn(&str)) -> Result<Self,String> {
            let setup=pcs::regenerate_log41_prover_for_sparse_test(mark)?;
            // Only the exact-coordinate regenerator can create this type. Its
            // original streamed setup-ID check binds both prover coordinates
            // and the admitted verifier bytes before this seal is returned.
            if setup.log_n!=41 || setup.prover.g1_vec.len()!=1usize<<21
                || setup.prover.g2_vec.len()!=1usize<<21 {
                return Err("H21 PCS regenerated key geometry drift".into());
            }
            Ok(Self{setup})
        }
        pub(crate) fn setup_id(&self)->[u8;32] {self.setup.id}
        pub(crate) fn key_bytes(&self)->&'static [u8] {
            include_bytes!("../fixtures/verifier-keys-v1/log41.vk")
        }
    }

    /// The rows and C were computed from this same held untrusted polynomial.
    /// The large prover coordinates may be dropped between commit and opening;
    /// a freshly regenerated sealed key with the same ID is required to open.
    pub(crate) struct H21PcsSession<'a> {
        candidate:&'a UntrustedH21CandidateFile,
        committed:PackedCommitted,
        setup_id:[u8;32],
    }

    fn admit_expected(statement:&Statement,setup_id:[u8;32],commitment:&ArkGT)
        ->Result<(),String>{
        if statement.log_n!=41 || statement.setup_id!=setup_id
            || statement.corpus_id.is_none()
            || statement.claims.iter().any(|claim|claim.point.len()!=41) {
            return Err("H21 PCS expected statement/key/dimension rejected".into());
        }
        let actual=pcs::encode_commitment(commitment)?;
        let requested=pcs::encode_commitment(&statement.commitment)?;
        // Round-trip using the existing subgroup-checked canonical codec.
        if pcs::encode_commitment(&pcs::decode_commitment(&actual)?)?!=actual
            || requested!=actual {
            return Err("H21 PCS canonical commitment mismatch".into());
        }
        Ok(())
    }

    impl<'a> H21PcsSession<'a> {
        pub(crate) fn commit(candidate:&'a UntrustedH21CandidateFile,
            expected_identity:&[u8],prover:&H21PcsProver)->Result<Self,String>{
            if expected_identity.is_empty()
                || candidate.requested_logical_public_identity()!=expected_identity {
                return Err("H21 PCS requested logical identity mismatch".into());
            }
            let source=candidate.untrusted_polynomial();
            let dim=packed::bitpacked_dimensions(41,source.input_len())?;
            if dim.width!=1usize<<21 || dim.rows!=1usize<<20 {
                return Err("H21 PCS held candidate geometry mismatch".into());
            }
            let committed=packed::commit(source,&prover.setup)?;
            // No path is reopened and no NativeComplete source is manufactured.
            let canonical=pcs::encode_commitment(&committed.commitment)?;
            if pcs::encode_commitment(&pcs::decode_commitment(&canonical)?)?!=canonical {
                return Err("H21 PCS commitment codec drift".into());
            }
            Ok(Self{candidate,committed,setup_id:prover.setup.id})
        }
        pub(crate) fn commitment(&self)->ArkGT {self.committed.commitment}
        pub(crate) fn setup_id(&self)->[u8;32] {self.setup_id}
        pub(crate) fn candidate_digest(&self)->[u8;64] {*self.candidate.actual_blake2b512()}

        /// Claims are prover input only. The separate atomic consumer derives
        /// its own seven claims and must verify the returned bytes through PCS.
        pub(crate) fn prove_unverified(&self,prover:&H21PcsProver,statement:&Statement)
            ->Result<(Vec<u8>,Metrics),String>{
            if prover.setup.id!=self.setup_id {
                return Err("H21 PCS regenerated key differs from commit key".into());
            }
            admit_expected(statement,self.setup_id,&self.committed.commitment)?;
            let source=self.candidate.untrusted_polynomial();
            let digest=self.candidate.actual_blake2b512();
            let mut transcript=Transcript::new(DOMAIN);
            let frontend=prove_frontend_bitpacked_on(source,statement,Some(digest),&mut transcript)?;
            let point=frontend.point.clone();
            let (proof,metrics)=finish_bitpacked_precomputed_v(source,&self.committed,
                &prover.setup,digest,frontend,&point,&mut transcript)?;
            Ok((encode_proof(&proof,41)?,metrics))
        }
    }

    #[test]
    fn h21_e2e1_pcs_statement_admission_preserves_legacy_cap_and_canonical_binding(){
        let setup=pcs::generate_setup(5).unwrap();
        let committed=pcs::commit(&vec![Fr::zero();32],&setup).unwrap();
        let mut statement=Statement{log_n:41,setup_id:setup.id,
            commitment:committed.commitment,corpus_id:Some([7;32]),
            claims:std::array::from_fn(|_|Claim{point:vec![Fr::one();41],value:Fr::zero()})};
        admit_expected(&statement,setup.id,&committed.commitment).unwrap();
        // This checks statement framing, never constructs a sealed H21 key or
        // session and never claims that a small setup is a log41 setup.
        assert_eq!(pcs::MAX_LOG_N,24);
        assert!(admit(&statement,&setup).is_err());
        statement.corpus_id=None;assert!(admit_expected(&statement,setup.id,&committed.commitment).is_err());
        statement.corpus_id=Some([7;32]);statement.claims[6].point.pop();
        assert!(admit_expected(&statement,setup.id,&committed.commitment).is_err());
        statement.claims[6].point.push(Fr::one());statement.setup_id[0]^=1;
        assert!(admit_expected(&statement,setup.id,&committed.commitment).is_err());
        statement.setup_id=setup.id;statement.log_n=40;
        assert!(admit_expected(&statement,setup.id,&committed.commitment).is_err());
        statement.log_n=41;
        let other=pcs::commit(&vec![Fr::one();32],&setup).unwrap();
        assert!(admit_expected(&statement,setup.id,&other.commitment).is_err());
    }
}

fn challenge(t:&mut Transcript,label:&[u8],controlled:Option<&[Fr]>,i:usize)->Result<Fr,String>{
    let sampled=t.try_challenge_scalar(label)?;
    #[cfg(test)] {if let Some(v)=controlled {return v.get(i).copied().filter(|x| !x.is_zero()).ok_or("controlled challenge missing/zero".into());}}
    let _=(controlled,i);Ok(sampled)
}
fn append_round_challenge(t:&mut Transcript,phase:u64,index:usize,c:&[Fr;3],controlled:Option<&[Fr]>,i:usize)->Result<Fr,String>{
    t.append_u64(b"opening-batch-round-phase",phase);
    t.append_u64(b"opening-batch-round-index",index as u64);
    for coefficient in c {t.append_scalar(b"opening-batch-quadratic-coefficient",coefficient);}
    challenge(t,b"opening-batch-round-challenge",controlled,i)
}

/// Verify against the caller's expected statement, then invoke PCS unconditionally.
pub fn verify(statement:&Statement,setup:&Setup,proof:&Proof)->Result<Transcript,String>{
    let mut t=Transcript::new(DOMAIN);
    verify_on(statement,VerificationKey::Setup(setup),proof,&mut t,None)?;
    Ok(t)
}
/// Verify a batch with only an admitted verifier key; no prover setup is loaded.
pub fn verify_admitted(statement:&Statement,key:&crate::verifier_key::AdmittedVerifierKey,
    proof:&Proof)->Result<Transcript,String>{
    let mut t=Transcript::new(DOMAIN);
    verify_on(statement,VerificationKey::Admitted(key),proof,&mut t,None)?;
    Ok(t)
}
fn verify_on(statement:&Statement,key:VerificationKey<'_>,proof:&Proof,t:&mut Transcript,controlled:Option<&[Fr]>)->Result<(),String>{
    #[cfg(test)] {verify_on_core(statement,key,proof,t,controlled,None)}
    #[cfg(not(test))] {verify_on_core(statement,key,proof,t,controlled)}
}
// Both normal and observed verification execute this exact predicate. The
// test-only observer can record reached sites but cannot choose a transcript,
// statement, challenge or an alternate acceptance path.
fn verify_on_core(statement:&Statement,key:VerificationKey<'_>,proof:&Proof,t:&mut Transcript,controlled:Option<&[Fr]>,
    #[cfg(test)] mut observer:Option<&mut dyn FnMut(Common51Event)>)->Result<(),String>{
    admit_verification_key(statement,key)?;
    #[cfg(test)] if let Some(observe)=observer.as_deref_mut(){observe(Common51Event::FrontendEntered);}
    let z=replay_frontend_on(statement,&proof.rounds,proof.terminal,t,controlled)?;
    #[cfg(test)] if let Some(observe)=observer.as_deref_mut(){observe(Common51Event::FrontendComplete);}
    #[cfg(test)] if let Some(observe)=observer.as_deref_mut(){observe(Common51Event::PcsEntered);}
    let result=match key {
        VerificationKey::Setup(setup)=>pcs::verify(statement.commitment,proof.terminal,&z,&proof.pcs,setup,t),
        VerificationKey::Admitted(key)=>pcs::verify_admitted(statement.commitment,proof.terminal,&z,&proof.pcs,key,t),
    }.map_err(|e|format!("opening-batch final PCS rejected: {e}"));
    result?;
    #[cfg(test)] if let Some(observe)=observer.as_deref_mut(){observe(Common51Event::PcsComplete);}
    Ok(())
}

#[cfg(test)]
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) enum Common51Event{FrontendEntered,FrontendComplete,PcsEntered,PcsComplete}
#[cfg(test)]
pub(crate) struct Common51Success{
    pub(crate) transcript:Transcript,
    pub(crate) frontend_ns:u128,
    pub(crate) pcs_ns:u128,
}
// No success observation or partially advanced transcript escapes an error.
// Entry diagnostics are for isolated fixtures; they carry no acceptance token.
#[cfg(test)]
pub(crate) fn verify_admitted_observed51(statement:&Statement,key:&crate::verifier_key::AdmittedVerifierKey,
    proof:&Proof,diagnostic:&mut dyn FnMut(Common51Event))->Result<Common51Success,String>{
    let mut t=Transcript::new(DOMAIN);let mut frontend_start=None;let mut pcs_start=None;
    let mut frontend_ns=None;let mut pcs_ns=None;
    let mut observe=|event|{match event{
        Common51Event::FrontendComplete=>frontend_ns=frontend_start.map(|start:Instant|start.elapsed().as_nanos()),
        Common51Event::PcsComplete=>pcs_ns=pcs_start.map(|start:Instant|start.elapsed().as_nanos()),
        _=>(),
    }
        diagnostic(event);
        match event{Common51Event::FrontendEntered=>frontend_start=Some(Instant::now()),
            Common51Event::PcsEntered=>pcs_start=Some(Instant::now()),_=>()}
    };
    verify_on_core(statement,VerificationKey::Admitted(key),proof,&mut t,None,Some(&mut observe))?;
    drop(observe);
    Ok(Common51Success{transcript:t,frontend_ns:frontend_ns.ok_or("common51 frontend observation incomplete")?,
        pcs_ns:pcs_ns.ok_or("common51 PCS observation incomplete")?})
}

// Private reduction replay for an independently admitted statement. This leaves
// the transcript at the PCS separator; it does not authenticate an opening.
fn replay_frontend_on(statement:&Statement,rounds:&[[Fr;3]],value:Fr,t:&mut Transcript,
    controlled:Option<&[Fr]>)->Result<Vec<Fr>,String>{
    let k=statement.log_n;let sigma=k.div_ceil(2);
    if rounds.len()!=k {return Err("opening-batch round count rejected".into());}
    bind(statement,t)?;
    let a=challenge(t,b"opening-batch-alpha",controlled,0)?;
    let mut power=Fr::one();let mut sum=Fr::zero();
    for claim in &statement.claims {sum+=power*claim.value;power*=a;}
    let mut z=Vec::with_capacity(k);
    for (i,coeff) in rounds.iter().enumerate(){
        check_round(coeff,sum)?;
        let x=append_round_challenge(t,if i<sigma {0}else{1},i,coeff,controlled,i+1)?;
        sum=eval_quadratic(coeff,x);z.push(x);
    }
    let mut power=Fr::one();let mut w=Fr::zero();
    for claim in &statement.claims {w+=power*eq_point(&claim.point,&z);power*=a;}
    if sum!=value*w {return Err("opening-batch terminal relation rejected".into());}
    terminal(t,value);
    Ok(z)
}

/// Fixed v1 wire: magic[8], version/u8, k/u8, q/u8, reserved/u8,
/// k * 3 canonical Fr[32], terminal Fr[32], PCS length/u32le, exact PCS bytes.
pub fn encode_proof(proof:&Proof,k:usize)->Result<Vec<u8>,String>{
    if k>pcs::MAX_VERIFY_LOG_N || proof.rounds.len()!=k || proof.pcs.nu!=k/2 || proof.pcs.sigma!=k.div_ceil(2) {
        return Err("opening-batch encode dimension".into());
    }
    let backend=pcs::encode_proof(&proof.pcs)?;
    let length=u32::try_from(backend.len()).map_err(|_|"PCS length overflow")?;
    let capacity=12usize.checked_add(k.checked_mul(96).ok_or("round size overflow")?)
        .and_then(|n|n.checked_add(36)).and_then(|n|n.checked_add(backend.len())).ok_or("packet size overflow")?;
    let mut out=Vec::with_capacity(capacity);out.extend_from_slice(MAGIC);
    out.extend_from_slice(&[VERSION,k as u8,CLAIMS as u8,0]);
    for round in &proof.rounds {for x in round {out.extend_from_slice(&pcs::encode(x)?);}}
    out.extend_from_slice(&pcs::encode(&proof.terminal)?);
    out.extend_from_slice(&length.to_le_bytes());out.extend_from_slice(&backend);
    Ok(out)
}
pub fn decode_proof(bytes:&[u8],expected_k:usize)->Result<Proof,String>{
    if expected_k>pcs::MAX_VERIFY_LOG_N {return Err("opening-batch expected dimension unsupported".into());}
    let prefix=12usize.checked_add(expected_k.checked_mul(96).ok_or("round size overflow")?)
        .and_then(|n|n.checked_add(36)).ok_or("packet size overflow")?;
    if bytes.len()<prefix {return Err("opening-batch packet truncated".into());}
    if &bytes[..8]!=MAGIC || bytes[8]!=VERSION || bytes[9] as usize!=expected_k
        || bytes[10] as usize!=CLAIMS || bytes[11]!=0 {return Err("opening-batch packet header rejected".into());}
    let mut offset=12;let mut rounds=Vec::with_capacity(expected_k);
    for _ in 0..expected_k {let mut c=[Fr::zero();3];for x in &mut c {*x=scalar(&bytes[offset..offset+32])?;offset+=32;}rounds.push(c);}
    let terminal=scalar(&bytes[offset..offset+32])?;offset+=32;
    let size=u32::from_le_bytes(bytes[offset..offset+4].try_into().unwrap()) as usize;offset+=4;
    let end=offset.checked_add(size).ok_or("opening-batch PCS length overflow")?;
    if end!=bytes.len() {return Err("opening-batch PCS length/trailing bytes rejected".into());}
    let pcs=pcs::decode_proof(&bytes[offset..end],expected_k)?;
    Ok(Proof{rounds,terminal,pcs})
}
fn scalar(bytes:&[u8])->Result<Fr,String>{
    if bytes.len()!=32 {return Err("opening-batch scalar length".into());}
    let mut reader=bytes;let x=Fr::deserialize_compressed(&mut reader).map_err(|e|e.to_string())?;
    if !reader.is_empty() || pcs::encode(&x)?!=bytes {return Err("opening-batch noncanonical scalar".into());}
    Ok(x)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::{BigInteger, Field, PrimeField};
    use dory_pcs::backends::arkworks::{ArkFr, ArkG1, ArkworksVerifierSetup, BN254, G1Routines, G2Routines};
    use dory_pcs::primitives::arithmetic::{DoryRoutines, Group, PairingCurve};
    use dory_pcs::{DoryError, Mode, MultilinearLagrange, Polynomial, ProverSetup, Transparent};
    use std::{fs::OpenOptions,io::Write,sync::atomic::{AtomicU64,Ordering}};
    static NEXT:AtomicU64=AtomicU64::new(0);
    fn fixture(bits:&[u8],k:usize)->(std::path::PathBuf,PackedFile,Setup,PackedCommitted,Statement){
        let mut bytes=vec![0u8;bits.len().div_ceil(8)];
        for (i,bit) in bits.iter().enumerate(){if *bit!=0 {bytes[i/8]|=1<<(i%8);}}
        let path=std::env::temp_dir().join(format!("opening-batch-{}-{}.bin",std::process::id(),NEXT.fetch_add(1,Ordering::Relaxed)));
        let mut file=OpenOptions::new().write(true).create_new(true).open(&path).unwrap();
        file.write_all(&bytes).unwrap();drop(file);
        let packed=PackedFile::open(&path,k).unwrap();let setup=pcs::generate_setup(k).unwrap();
        let committed=packed::commit(&packed,&setup).unwrap();
        let claims=std::array::from_fn(|j|{
            let point=(0..k).map(|i|Fr::from((5+7*i+101*j) as u64)).collect::<Vec<_>>();
            Claim{value:dense_mle(&bits.iter().map(|b|Fr::from(*b as u64)).collect::<Vec<_>>(),&point),point}
        });
        let statement=Statement{log_n:k,setup_id:setup.id,commitment:committed.commitment,
            corpus_id:Some([0x53;32]),claims};
        (path,packed,setup,committed,statement)
    }
    fn distinct_log9_bits_and_bytes()->(Vec<u8>,Vec<u8>){
        let words=(0u32..16).map(|row|0xA5A5_5A5Au32^row.wrapping_mul(0x9E37_79B9))
            .collect::<Vec<_>>();
        let unique=words.iter().copied().collect::<std::collections::HashSet<_>>();
        assert_eq!(unique.len(),16,"log9 fixture must exercise 16 distinct rows");
        println!("log9_unique_row_words={:?}",words.iter().map(|word|format!("{word:08X}"))
            .collect::<Vec<_>>());
        let bytes=words.iter().flat_map(|word|word.to_le_bytes()).collect::<Vec<_>>();
        let bits=bytes.iter().flat_map(|byte|{
            let value=*byte;(0..8).map(move |bit|(value>>bit)&1)
        }).collect::<Vec<_>>();
        assert_eq!(bits.len(),1usize<<9);
        (bits,bytes)
    }
    fn generated_admitted_key_with_id(setup:&Setup,id:[u8;32])->crate::verifier_key::AdmittedVerifierKey{
        let bytes=pcs::encode(&dory_pcs::backends::arkworks::ArkworksVerifierSetup(setup.verifier.clone())).unwrap();
        crate::verifier_key::admit_generated_test_key(setup.log_n,&bytes,id).unwrap()
    }
    fn generated_admitted_key(setup:&Setup)->crate::verifier_key::AdmittedVerifierKey{
        generated_admitted_key_with_id(setup,setup.id)
    }
    struct ImplicitZeroPolynomial { log_n:usize }
    impl Polynomial<ArkFr> for ImplicitZeroPolynomial {
        fn num_vars(&self)->usize {self.log_n}
        fn evaluate(&self,point:&[ArkFr])->ArkFr {
            assert_eq!(point.len(),self.log_n);
            ArkFr(Fr::zero())
        }
        fn commit<E,Mo,M1>(&self,_nu:usize,_sigma:usize,_setup:&ProverSetup<E>)
            ->Result<(E::GT,Vec<E::G1>,ArkFr),DoryError>
        where E:PairingCurve,Mo:Mode,M1:DoryRoutines<E::G1>,
            E::G1:Group<Scalar=ArkFr>,E::GT:Group<Scalar=ArkFr> {
            Err(DoryError::InvalidInput("implicit-zero diagnostic supplies row commitments directly".into()))
        }
    }
    impl MultilinearLagrange<ArkFr> for ImplicitZeroPolynomial {
        fn vector_matrix_product(&self,left_vec:&[ArkFr],nu:usize,sigma:usize)->Vec<ArkFr> {
            assert_eq!(nu+sigma,self.log_n);
            assert_eq!(left_vec.len(),1usize<<nu);
            vec![ArkFr(Fr::zero());1usize<<sigma]
        }
    }
    fn zero_batch_statement(log_n:usize,setup_id:[u8;32],commitment:ArkGT)->Statement {
        let claims=std::array::from_fn(|j|Claim{
            point:(0..log_n).map(|i|Fr::from((j*log_n+i+2) as u64)).collect(),
            value:Fr::zero(),
        });
        Statement{log_n,setup_id,commitment,corpus_id:Some([0x53;32]),claims}
    }
    fn implicit_zero_batch_proof(setup:&Setup,statement:&Statement)
        ->(Proof,Vec<Fr>,Transcript,Transcript) {
        let k=statement.log_n;
        assert_eq!(setup.log_n,k);
        assert!(statement.claims.iter().all(|claim|claim.value.is_zero()));
        let mut producer_t=Transcript::new(DOMAIN);
        bind(statement,&mut producer_t).unwrap();
        let alpha=challenge(&mut producer_t,b"opening-batch-alpha",None,0).unwrap();
        let mut z=Vec::with_capacity(k);
        let mut sum=Fr::zero();
        for i in 0..k {
            let coefficients=[Fr::zero();3];
            check_round(&coefficients,sum).unwrap();
            let x=append_round_challenge(&mut producer_t,if i<k.div_ceil(2){0}else{1},i,
                &coefficients,None,i+1).unwrap();
            sum=eval_quadratic(&coefficients,x);
            z.push(x);
        }
        let mut power=Fr::one();let mut terminal_weight=Fr::zero();
        for claim in &statement.claims {
            terminal_weight+=power*eq_point(&claim.point,&z);
            power*=alpha;
        }
        assert_eq!(sum,Fr::zero()*terminal_weight);
        terminal(&mut producer_t,Fr::zero());
        let before_pcs=producer_t.clone();
        pcs::bind_statement(setup,&statement.commitment,&Fr::zero(),&z,&mut producer_t).unwrap();
        let polynomial=ImplicitZeroPolynomial{log_n:k};
        let nu=k/2;let sigma=k.div_ceil(2);
        let rows=vec![<ArkG1 as Group>::identity();1usize<<nu];
        let point_ark=z.iter().copied().map(ArkFr).collect::<Vec<_>>();
        let (pcs_proof,blind)=dory_pcs::prove::<_,BN254,G1Routines,G2Routines,_,_,Transparent>(
            &polynomial,&point_ark,rows,ArkFr(Fr::zero()),nu,sigma,&setup.prover,&mut producer_t,
        ).unwrap();
        assert!(blind.is_none());
        let proof=Proof{rounds:vec![[Fr::zero();3];k],terminal:Fr::zero(),pcs:pcs_proof};
        (proof,z,before_pcs,producer_t)
    }
    fn dense_mle(values:&[Fr],point:&[Fr])->Fr{
        values.iter().enumerate().fold(Fr::zero(),|sum,(index,v)|{
            let weight=point.iter().enumerate().fold(Fr::one(),|w,(bit,x)|w*if(index>>bit)&1==1{*x}else{Fr::one()-x});
            sum+*v*weight
        })
    }
    fn dense_claims(values:&[Fr],points:&[Vec<Fr>;CLAIMS])->[Claim;CLAIMS]{
        std::array::from_fn(|j|Claim{point:points[j].clone(),value:dense_mle(values,&points[j])})
    }
    fn dense_round(values:&[Fr],claims:&[Claim;CLAIMS],alpha:Fr,z:&[Fr],t:usize)->[Fr;3]{
        // Directly enumerate all remaining Boolean inputs for three T values;
        // this oracle does not use rectangular projections or paired-vector formulas.
        let n=values.len().trailing_zeros() as usize;
        let work=|x:Fr|{
            let mut point=z.to_vec();point.push(x);
            let mut total=Fr::zero();
            for suffix in 0..1usize<<(n-t-1){
                for bit in 0..n-t-1 {point.push(Fr::from(((suffix>>bit)&1) as u64));}
                let f=dense_mle(values,&point);
                let mut power=Fr::one();let mut w=Fr::zero();
                for claim in claims {w+=power*eq_point(&claim.point,&point);power*=alpha;}
                total+=f*w;point.truncate(t+1);
            }
            total
        };
        let y0=work(Fr::zero());let y1=work(Fr::one());let ym=work(-Fr::one());
        let half=Fr::from(2u64).inverse().unwrap();
        let a2=(y1+ym-y0-y0)*half;let a1=y1-y0-a2;[y0,a1,a2]
    }
    fn rectangle_against_dense(values:&[Fr],claims:&[Claim;CLAIMS],alpha:Fr)->(Vec<[Fr;3]>,Fr,Fr){
        let k=values.len().trailing_zeros() as usize;let sigma=k.div_ceil(2);let nu=k/2;
        let c=1usize<<sigma;let rows=1usize<<nu;
        let weight=|point:&[Fr],index:usize|point.iter().enumerate().fold(Fr::one(),|v,(i,x)|
            v*if(index>>i)&1==1{*x}else{Fr::one()-x});
        let mut projections=std::array::from_fn::<_,CLAIMS,_>(|j|(0..c).map(|l|
            (0..rows).fold(Fr::zero(),|s,h|s+values[h*c+l]*weight(&claims[j].point[sigma..],h))).collect::<Vec<_>>());
        let mut powers=[Fr::one();CLAIMS];for j in 1..CLAIMS{powers[j]=powers[j-1]*alpha;}
        let mut mu=powers;let mut sum=Fr::zero();for j in 0..CLAIMS{sum+=powers[j]*claims[j].value;}
        let mut z=Vec::new();let mut rounds=Vec::new();
        for t in 0..sigma{
            let mut coeff=[Fr::zero();3];
            for j in 0..CLAIMS{
                let a=claims[j].point[t];let beta0=Fr::one()-a;let beta1=a+a-Fr::one();
                for u in 0..projections[j].len()/2{
                    let c0=projections[j][2*u];let delta=projections[j][2*u+1]-c0;
                    let w=mu[j]*weight(&claims[j].point[t+1..sigma],u);
                    coeff[0]+=w*beta0*c0;
                    coeff[1]+=w*(beta0*delta+beta1*c0);
                    coeff[2]+=w*beta1*delta;
                }
            }
            assert_eq!(coeff,dense_round(values,claims,alpha,&z,t));
            check_round(&coeff,sum).unwrap();
            let x=Fr::from((19+3*t) as u64);sum=eval_quadratic(&coeff,x);z.push(x);
            for j in 0..CLAIMS{
                let len=projections[j].len()/2;
                for u in 0..len{let c0=projections[j][2*u];projections[j][u]=c0+x*(projections[j][2*u+1]-c0);}
                projections[j].truncate(len);
                let a=claims[j].point[t];mu[j]*=(Fr::one()-a)+(a+a-Fr::one())*x;
            }
            rounds.push(coeff);
        }
        let low_join=(0..CLAIMS).fold(Fr::zero(),|s,j|s+mu[j]*projections[j][0]);
        assert_eq!(low_join,sum);
        let mut f=(0..rows).map(|h|(0..c).fold(Fr::zero(),|s,l|s+values[h*c+l]*weight(&z,l))).collect::<Vec<_>>();
        let mut b=(0..rows).map(|h|(0..CLAIMS).fold(Fr::zero(),|s,j|s+mu[j]*weight(&claims[j].point[sigma..],h))).collect::<Vec<_>>();
        let high_join=(0..rows).fold(Fr::zero(),|s,h|s+f[h]*b[h]);
        assert_eq!(high_join,low_join);
        for t in 0..nu{
            let mut coeff=[Fr::zero();3];
            for u in 0..f.len()/2{
                let f0=f[2*u];let b0=b[2*u];let df=f[2*u+1]-f0;let db=b[2*u+1]-b0;
                coeff[0]+=f0*b0;coeff[1]+=f0*db+b0*df;coeff[2]+=df*db;
            }
            assert_eq!(coeff,dense_round(values,claims,alpha,&z,sigma+t));
            check_round(&coeff,sum).unwrap();
            let x=Fr::from((19+3*(sigma+t)) as u64);sum=eval_quadratic(&coeff,x);z.push(x);
            let len=f.len()/2;
            for u in 0..len{let f0=f[2*u];let b0=b[2*u];f[u]=f0+x*(f[2*u+1]-f0);b[u]=b0+x*(b[2*u+1]-b0);}
            f.truncate(len);b.truncate(len);rounds.push(coeff);
        }
        assert_eq!(f[0],dense_mle(values,&z));
        assert_eq!(sum,f[0]*(0..CLAIMS).fold(Fr::zero(),|s,j|s+powers[j]*eq_point(&claims[j].point,&z)));
        (rounds,low_join,high_join)
    }
    struct BadSource{len:usize,kind:u8}
    impl RowSource for BadSource{
        fn input_len(&self)->usize{self.len}
        fn read_row(&self,width:usize,_row:usize)->Result<Vec<Fr>,String>{
            match self.kind {0=>Ok(vec![Fr::zero();width-1]),1=>Ok(vec![Fr::from(2u64);width]),_=>Err("injected reader error".into())}
        }
    }
    struct BadRowSource { input_len:usize, bad_row:usize, kind:u8 }
    impl RowSource for BadRowSource {
        fn input_len(&self)->usize { self.input_len }
        fn read_row(&self,width:usize,row:usize)->Result<Vec<Fr>,String> {
            if row!=self.bad_row { return Ok(vec![Fr::zero();width]); }
            match self.kind {
                0=>Ok(vec![Fr::zero();width-1]),
                1=>Ok(vec![Fr::from(2u64);width]),
                _=>Err("injected reader error".into()),
            }
        }
    }
    struct FrontendTinySource {
        values:Vec<Fr>,calls:std::cell::Cell<usize>,failure:Option<(usize,u8)>,
    }
    impl RowSource for FrontendTinySource {
        fn input_len(&self)->usize{self.values.len()}
        fn read_row(&self,width:usize,row:usize)->Result<Vec<Fr>,String>{
            let call=self.calls.get();self.calls.set(call+1);
            if let Some((at,kind))=self.failure{if call==at{return match kind{
                0=>Ok(vec![Fr::zero();width-1]),1=>Ok(vec![Fr::from(2u64);width]),
                2=>Err("injected frontend row error".into()),_=>{
                    let mut values=Vec::with_capacity(width+1);values.resize(width,Fr::zero());Ok(values)
                },};}}
            Ok(self.values[row*width..(row+1)*width].to_vec())
        }
    }
    fn frontend_tiny_statement(values:&[Fr],k:usize)->Statement{
        let points=std::array::from_fn(|j|(0..k).map(|i|Fr::from((5+7*i+101*j) as u64)).collect());
        Statement{log_n:k,setup_id:[0x71;32],commitment:<ArkGT as Group>::identity(),
            corpus_id:Some([0x53;32]),claims:dense_claims(values,&points)}
    }
    #[test]
    fn frontend_extraction_matches_dense_and_reference(){
        for k in 0..=5{
            let values=(0..1usize<<k).map(|i|Fr::from(((i*73+(i>>1)*19+5)>>1&1) as u64)).collect::<Vec<_>>();
            let source=FrontendTinySource{values,calls:std::cell::Cell::new(0),failure:None};
            let statement=frontend_tiny_statement(&source.values,k);
            let mut fused_t=Transcript::new(DOMAIN);let mut reference_t=Transcript::new(DOMAIN);
            let fused=prove_frontend_on_mode(&source,&statement,&mut fused_t,None,ProjectionMode::Fused,None).unwrap();
            let reference=prove_frontend_on_mode(&source,&statement,&mut reference_t,None,ProjectionMode::Reference,None).unwrap();
            let held=std::mem::size_of::<FrontendTinySource>()+source.values.capacity()*std::mem::size_of::<Fr>();
            let mut audit=FrontendAudit::new(&statement,held,false).unwrap();
            let mut audited_t=Transcript::new(DOMAIN);
            let audited=prove_frontend_on_mode(&source,&statement,&mut audited_t,None,ProjectionMode::Fused,Some(&mut audit)).unwrap();
            for other in [&reference,&audited]{
                assert_eq!(fused.rounds,other.rounds);assert_eq!(fused.terminal,other.terminal);assert_eq!(fused.point,other.point);
            }
            assert_eq!(fused.rounds.len(),k);assert_eq!(fused.point.len(),k);
            let mut dense_t=Transcript::new(DOMAIN);bind(&statement,&mut dense_t).unwrap();
            let alpha=dense_t.try_challenge_scalar(b"opening-batch-alpha").unwrap();let mut point=Vec::new();
            for i in 0..k{
                let coefficients=dense_round(&source.values,&statement.claims,alpha,&point,i);
                assert_eq!(fused.rounds[i],coefficients);
                point.push(append_round_challenge(&mut dense_t,if i<k.div_ceil(2){0}else{1},i,&coefficients,None,i+1).unwrap());
            }
            assert_eq!(point,fused.point);assert_eq!(fused.terminal,dense_mle(&source.values,&point));
            terminal(&mut dense_t,fused.terminal);
            let counters=|t:&Transcript|(t.challenges(),t.raw_queries(),t.bytes_absorbed());
            assert_eq!(counters(&fused_t),counters(&reference_t));assert_eq!(counters(&fused_t),counters(&audited_t));
            assert_eq!(counters(&fused_t),counters(&dense_t));
            let next=fused_t.try_challenge_scalar(b"frontend-continuation").unwrap();
            for t in [&mut reference_t,&mut audited_t,&mut dense_t]{assert_eq!(next,t.try_challenge_scalar(b"frontend-continuation").unwrap());}
            assert_eq!(audit.stats.row_loads,[1usize<<(k/2);2]);assert_eq!(audit.mark_count,8);
            assert_eq!(audit.stats.phase_marks.iter().map(|m|m.name).collect::<Vec<_>>(),FRONTEND_PHASE_NAMES);
            assert!(audit.stats.phase_marks.windows(2).all(|m|m[0].elapsed_ns<=m[1].elapsed_ns));
            assert_eq!(audit.stats.state_peak_capacity_bytes,*audit.stats.phase_peak_capacity_bytes.iter().max().unwrap());
            assert!(audit.stats.state_peak_capacity_bytes<=audit.stats.preflight_capacity_bound_bytes);
            assert!(audit.stats.preflight_capacity_bound_bytes<=FRONTEND_CAPACITY_LIMIT);
            for (peak,inventory) in audit.stats.phase_peak_capacity_bytes.iter().zip(&audit.stats.phase_peak_inventory){
                assert_eq!(*peak,inventory.total_capacity_bytes);
                assert_eq!(*peak,audit.stats.held_capacity_bytes+audit.stats.fixed_capacity_bytes
                    +inventory.field_capacity_bytes+inventory.descriptor_capacity_bytes+inventory.row_scratch_capacity_bytes);
            }
            assert_eq!(audited.metrics.projection_scans,1);assert_eq!(audited.metrics.transition_scans,1);
            assert_eq!(audited.metrics.pre_pcs_fields,0);assert_eq!(audited.metrics.pcs_seconds,0.0);
        }
    }
    #[test]
    fn frontend_audit_capacity_and_row_failures_are_isolated(){
        let k=3;let source=FrontendTinySource{values:vec![Fr::zero();1<<k],calls:std::cell::Cell::new(0),failure:None};
        let statement=frontend_tiny_statement(&source.values,k);
        assert!(FrontendAudit::new(&statement,FRONTEND_CAPACITY_LIMIT,false).is_err());assert_eq!(source.calls.get(),0);
        assert!(FrontendAudit::new(&statement,usize::MAX,false).is_err());
        assert!(frontend_add(usize::MAX,1).is_err());assert!(frontend_mul(usize::MAX,2).is_err());
        let mut audit=FrontendAudit::new(&statement,0,false).unwrap();
        let room=FRONTEND_CAPACITY_LIMIT-audit.stats.preflight_capacity_bound_bytes;
        assert_eq!(FrontendAudit::new(&statement,room,false).unwrap().stats.preflight_capacity_bound_bytes,FRONTEND_CAPACITY_LIMIT);
        assert!(FrontendAudit::new(&statement,room+1,false).is_err());
        let extra=FrontendAudit::new(&statement,123,false).unwrap();
        assert_eq!(extra.stats.preflight_capacity_bound_bytes,audit.stats.preflight_capacity_bound_bytes+123);
        assert!(audit.record(6,0,0,0).is_err());assert!(audit.record(0,FRONTEND_CAPACITY_LIMIT,0,0).is_err());
        assert!(audit.mark(1).is_err());assert_eq!(audit.mark_count,0);
        let mut transcript=Transcript::new(DOMAIN);let before=(transcript.challenges(),transcript.raw_queries(),transcript.bytes_absorbed());
        assert!(prove_frontend_on_mode(&source,&statement,&mut transcript,None,ProjectionMode::Reference,Some(&mut audit)).is_err());
        assert_eq!(before,(transcript.challenges(),transcript.raw_queries(),transcript.bytes_absorbed()));assert_eq!(source.calls.get(),0);
        let mut changed=statement.clone();changed.claims[0].point.push(Fr::zero());
        assert!(prove_frontend_on_mode(&source,&changed,&mut transcript,None,ProjectionMode::Fused,Some(&mut audit)).is_err());
        assert_eq!(before,(transcript.challenges(),transcript.raw_queries(),transcript.bytes_absorbed()));assert_eq!(source.calls.get(),0);
        let mut changed=statement.clone();changed.claims[0].point.reserve_exact(k+1);
        assert!(prove_frontend_on_mode(&source,&changed,&mut transcript,None,ProjectionMode::Fused,Some(&mut audit)).is_err());
        assert_eq!(before,(transcript.challenges(),transcript.raw_queries(),transcript.bytes_absorbed()));assert_eq!(source.calls.get(),0);
        for (kind,message) in [(0,"short row"),(1,"non-Boolean row"),(2,"injected frontend row error"),(3,"capacity")]{
            for at in [0,1usize<<(k/2)]{
                let source=FrontendTinySource{values:vec![Fr::zero();1<<k],calls:std::cell::Cell::new(0),failure:Some((at,kind))};
                let mut audit=FrontendAudit::new(&statement,0,false).unwrap();let mut transcript=Transcript::new(DOMAIN);
                let error=prove_frontend_on_mode(&source,&statement,&mut transcript,None,ProjectionMode::Fused,Some(&mut audit)).unwrap_err();
                assert!(error.contains(message),"{error}");assert!(audit.mark_count<8);
            }
        }
        let mut under=FrontendAudit::new(&statement,0,false).unwrap();
        under.stats.preflight_capacity_bound_bytes=under.stats.fixed_capacity_bytes;
        let mut transcript=Transcript::new(DOMAIN);
        assert!(prove_frontend_on_mode(&source,&statement,&mut transcript,None,ProjectionMode::Fused,Some(&mut under)).unwrap_err().contains("capacity"));
        assert_eq!(source.calls.get(),0);
        let mut extra_scan=FrontendAudit::new(&statement,0,false).unwrap();extra_scan.stats.row_loads[0]=1;
        let mut transcript=Transcript::new(DOMAIN);
        assert!(prove_frontend_on_mode(&source,&statement,&mut transcript,None,ProjectionMode::Fused,Some(&mut extra_scan)).unwrap_err().contains("census drift"));
        let mut changed=statement.clone();
        changed.claims=std::array::from_fn(|_|statement.claims[0].clone());
        changed.claims[3].value+=Fr::one();
        let controlled=vec![Fr::from(2u64);k+1];let mut transcript=Transcript::new(DOMAIN);
        assert!(prove_frontend_on_mode(&source,&changed,&mut transcript,Some(&controlled),ProjectionMode::Fused,None)
            .unwrap_err().contains("round sum rejected"));
        // Check the typed fixed-inventory equation without an extra stdout
        // record or a native witness/backend operation.
        assert_eq!(std::mem::size_of::<Fr>(),32);assert_eq!(std::mem::size_of::<Vec<Fr>>(),24);
        assert_eq!(std::mem::size_of::<Metrics>(),104);assert_eq!(std::mem::size_of::<Frontend>(),184);
        assert_eq!(std::mem::size_of::<Statement>(),856);
        let native=Statement{log_n:32,setup_id:statement.setup_id,commitment:statement.commitment,
            corpus_id:statement.corpus_id,claims:std::array::from_fn(|_|Claim{point:vec![Fr::zero();32],value:Fr::zero()})};
        let native_audit=FrontendAudit::new(&native,0,false).unwrap();
        let fixed=std::mem::size_of::<Statement>()+7*32*32+2*std::mem::size_of::<Transcript>()
            +std::mem::size_of::<FrontendAudit>()+2*184+104+(2*CLAIMS+8)*24+24+36*32+32*8
            +64+16+64+62+32+768+4*24;
        assert_eq!(native_audit.stats.fixed_capacity_bytes,fixed);
        assert_eq!(native_audit.stats.preflight_capacity_bound_bytes,fixed+31461376+168+8216);
    }
    #[test]
    fn modulus_and_rectangular_dense_oracle(){
        assert_eq!(Fr::MODULUS.to_string(),"21888242871839275222246405745257275088548364400416034343698204186575808495617");
        for k in 1..=5 {
            let values=(0..1usize<<k).map(|i|Fr::from((i*i+3*i+17) as u64)).collect::<Vec<_>>();
            let points=std::array::from_fn(|j|(0..k).map(|i|Fr::from((5+7*i+101*j) as u64)).collect());
            let claims=dense_claims(&values,&points);
            let alpha=Fr::from(13u64);let mut power=Fr::one();let mut sum=Fr::zero();
            for claim in &claims {sum+=power*claim.value;power*=alpha;}
            let (rect_rounds,low_join,high_join)=rectangle_against_dense(&values,&claims,alpha);
            assert_eq!(rect_rounds.len(),k);assert_eq!(low_join,high_join);
            let mut z=Vec::new();
            for t in 0..k {
                let coeff=dense_round(&values,&claims,alpha,&z,t);
                check_round(&coeff,sum).unwrap();
                let x=Fr::from((19+3*t) as u64);sum=eval_quadratic(&coeff,x);z.push(x);
            }
            let mut power=Fr::one();let mut w=Fr::zero();
            for claim in &claims {w+=power*eq_point(&claim.point,&z);power*=alpha;}
            assert_eq!(sum,dense_mle(&values,&z)*w);
        }
    }
    #[test]
    fn replay_frontend_matches_producer_and_full_verifier(){
        for k in [0,3,4]{
            let bits=(0..1usize<<k).map(|i|(((i*73+(i>>1)*19+5)>>1)&1) as u8).collect::<Vec<_>>();
            let (path,source,setup,committed,statement)=fixture(&bits,k);
            let (proof,_,producer_t)=prove(&source,&committed,&setup,&statement).unwrap();
            let mut replay_t=Transcript::new(DOMAIN);
            let point=replay_frontend_on(&statement,&proof.rounds,proof.terminal,&mut replay_t,None).unwrap();
            assert_eq!(point.len(),k);assert_eq!(replay_t.challenges(),(k+1) as u64);
            let values=bits.iter().map(|bit|Fr::from(*bit as u64)).collect::<Vec<_>>();
            assert_eq!(dense_mle(&values,&point),proof.terminal);
            let pcs=packed::open(&committed,&source,&point,&setup,&mut replay_t).unwrap();
            let joined=Proof{rounds:proof.rounds.clone(),terminal:proof.terminal,pcs};
            assert_eq!(encode_proof(&joined,k).unwrap(),encode_proof(&proof,k).unwrap());
            let key=generated_admitted_key(&setup);
            let setup_t=verify(&statement,&setup,&joined).unwrap();
            let admitted_t=verify_admitted(&statement,&key,&joined).unwrap();
            let counters=|t:&Transcript|(t.challenges(),t.raw_queries(),t.bytes_absorbed());
            let continuation=producer_t.clone().try_challenge_scalar(b"replay-endpoint-continuation").unwrap();
            for t in [&replay_t,&setup_t,&admitted_t]{
                assert_eq!(counters(t),counters(&producer_t));
                assert_eq!(t.clone().try_challenge_scalar(b"replay-endpoint-continuation").unwrap(),continuation);
            }
            drop(source);std::fs::remove_file(path).unwrap();
        }
    }
    #[test]
    fn replay_frontend_rejects_isolated_mutants(){
        let k=3;
        let values=(0..1usize<<k).map(|i|Fr::from(((i*73+(i>>1)*19+5)>>1&1) as u64)).collect::<Vec<_>>();
        let source=FrontendTinySource{values,calls:std::cell::Cell::new(0),failure:None};
        let statement=frontend_tiny_statement(&source.values,k);
        let controlled=(0..=k).map(|i|Fr::from((2+3*i) as u64)).collect::<Vec<_>>();
        let mut producer_t=Transcript::new(DOMAIN);
        let frontend=prove_frontend_on_mode(&source,&statement,&mut producer_t,Some(&controlled),ProjectionMode::Fused,None).unwrap();
        let mut replay_t=Transcript::new(DOMAIN);
        let point=replay_frontend_on(&statement,&frontend.rounds,frontend.terminal,&mut replay_t,Some(&controlled)).unwrap();
        assert_eq!(point,frontend.point);
        let counters=|t:&Transcript|(t.challenges(),t.raw_queries(),t.bytes_absorbed());
        assert_eq!(counters(&replay_t),counters(&producer_t));
        assert_eq!(replay_t.clone().try_challenge_scalar(b"replay-prefix-continuation").unwrap(),
            producer_t.clone().try_challenge_scalar(b"replay-prefix-continuation").unwrap());
        let reject=|expected:&Statement,rounds:&[[Fr;3]],value:Fr,message:&str|{
            let mut t=Transcript::new(DOMAIN);
            assert!(replay_frontend_on(expected,rounds,value,&mut t,Some(&controlled)).unwrap_err().contains(message));
        };
        let mut extra_round=frontend.rounds.clone();extra_round.push([Fr::zero();3]);
        for rounds in [&frontend.rounds[..k-1],&extra_round[..]]{
            let mut t=Transcript::new(DOMAIN);let before=counters(&t);
            assert!(replay_frontend_on(&statement,rounds,frontend.terminal,&mut t,Some(&controlled)).unwrap_err().contains("round count"));
            assert_eq!(counters(&t),before);
        }
        for i in 0..k{for coefficient in 0..3{
            let mut rounds=frontend.rounds.clone();rounds[i][coefficient]+=Fr::one();
            reject(&statement,&rounds,frontend.terminal,"round sum");
        }}
        // Preserve the first round's endpoint sum; the next join must still fail.
        let mut rounds=frontend.rounds.clone();rounds[0][0]+=Fr::one();rounds[0][1]-=Fr::from(2u64);
        reject(&statement,&rounds,frontend.terminal,"round sum");
        assert!(!frontend.terminal.is_zero());
        let weight=|expected:&Statement|{
            let mut power=Fr::one();let mut result=Fr::zero();
            for claim in &expected.claims{result+=power*eq_point(&claim.point,&point);power*=controlled[0];}result
        };
        assert!(!weight(&statement).is_zero());
        reject(&statement,&frontend.rounds,frontend.terminal+Fr::one(),"terminal relation");
        for j in 0..CLAIMS{
            let mut wrong=statement.clone();wrong.claims[j].value+=Fr::one();
            reject(&wrong,&frontend.rounds,frontend.terminal,"round sum");
            for coordinate in 0..k{
                let mut wrong=statement.clone();wrong.claims[j].point[coordinate]+=Fr::one();
                assert_ne!(weight(&wrong),weight(&statement));
                reject(&wrong,&frontend.rounds,frontend.terminal,"terminal relation");
            }
        }
        let mut wrong=statement.clone();wrong.claims.swap(0,1);
        assert_ne!(statement.claims[0].value,statement.claims[1].value);
        reject(&wrong,&frontend.rounds,frontend.terminal,"round sum");
        // Controlled challenges isolate non-algebraic binding: reduction alone
        // is not a receipt, and altered metadata must change its continuation.
        for field in 0..2{
            let mut wrong=statement.clone();
            if field==0{wrong.corpus_id=Some([0x54;32]);}else{wrong.setup_id[0]^=1;}
            let mut changed_t=Transcript::new(DOMAIN);
            assert_eq!(replay_frontend_on(&wrong,&frontend.rounds,frontend.terminal,&mut changed_t,Some(&controlled)).unwrap(),point);
            assert_ne!(changed_t.try_challenge_scalar(b"replay-prefix-continuation").unwrap(),
                replay_t.clone().try_challenge_scalar(b"replay-prefix-continuation").unwrap());
        }
    }
    #[test]
    fn packed_dense_differential_and_packet_rejections(){
        for k in 0..=5 {
            let bits=(0..1usize<<k).map(|i|(((i*73+((i>>1)*19)+5)>>1)&1) as u8).collect::<Vec<_>>();
            let (path,packed,setup,committed,statement)=fixture(&bits,k);
            let (proof,metrics,t_prove)=prove(&packed,&committed,&setup,&statement).unwrap();
            let t_verify=verify(&statement,&setup,&proof).unwrap();
            assert_eq!((t_prove.challenges(),t_prove.raw_queries(),t_prove.bytes_absorbed()),
                (t_verify.challenges(),t_verify.raw_queries(),t_verify.bytes_absorbed()));
            assert!(t_prove.challenges() >= (k+1) as u64);
            let mut next_p=t_prove.clone();let mut next_v=t_verify.clone();
            assert_eq!(next_p.try_challenge_scalar(b"continuation").unwrap(),next_v.try_challenge_scalar(b"continuation").unwrap());
            let encoded=encode_proof(&proof,k).unwrap();let decoded=decode_proof(&encoded,k).unwrap();
            assert_eq!(encode_proof(&decoded,k).unwrap(),encoded);
            assert_eq!(metrics.projection_scans,1);assert_eq!(metrics.transition_scans,1);
            let c=1usize<<k.div_ceil(2);let r=1usize<<(k/2);
            assert!(metrics.maximum_fields<=((CLAIMS+1)*c+CLAIMS*r).max(2*c+3*r),
                "fused live-field bound k={k}: {}",metrics.maximum_fields);
            assert_eq!(metrics.pre_pcs_fields,0);
            let values=bits.iter().map(|b|Fr::from(*b as u64)).collect::<Vec<_>>();
            let mut replay=Transcript::new(DOMAIN);bind(&statement,&mut replay).unwrap();
            let alpha=replay.try_challenge_scalar(b"opening-batch-alpha").unwrap();
            let mut z=Vec::new();
            for (i,round) in decoded.rounds.iter().enumerate(){
                assert_eq!(*round,dense_round(&values,&statement.claims,alpha,&z,i));
                let x=append_round_challenge(&mut replay,if i<k.div_ceil(2){0}else{1},i,round,None,i+1).unwrap();z.push(x);
            }
            assert_eq!(proof.terminal,dense_mle(&values,&z));
            // Independent dense Boolean prover: direct-enumeration messages and
            // unchanged dense PCS path must reproduce the complete outer packet.
            let dense_committed=pcs::commit(&values,&setup).unwrap();
            assert_eq!(pcs::encode_commitment(&dense_committed.commitment).unwrap(),
                pcs::encode_commitment(&statement.commitment).unwrap());
            let mut dense_t=Transcript::new(DOMAIN);bind(&statement,&mut dense_t).unwrap();
            let dense_alpha=dense_t.try_challenge_scalar(b"opening-batch-alpha").unwrap();
            let mut dense_z=Vec::new();let mut dense_rounds=Vec::new();
            for i in 0..k{
                let c=dense_round(&values,&statement.claims,dense_alpha,&dense_z,i);
                let x=append_round_challenge(&mut dense_t,if i<k.div_ceil(2){0}else{1},i,&c,None,i+1).unwrap();
                dense_rounds.push(c);dense_z.push(x);
            }
            let dense_terminal=dense_mle(&values,&dense_z);
            terminal(&mut dense_t,dense_terminal);
            let dense_pcs=pcs::open(&dense_committed,&dense_z,&setup,&mut dense_t).unwrap();
            let dense_proof=Proof{rounds:dense_rounds,terminal:dense_terminal,pcs:dense_pcs};
            assert_eq!(encode_proof(&dense_proof,k).unwrap(),encoded);
            assert_eq!((dense_t.challenges(),dense_t.raw_queries(),dense_t.bytes_absorbed()),
                (t_prove.challenges(),t_prove.raw_queries(),t_prove.bytes_absorbed()));
            assert_eq!(dense_t.challenges(),(k+1+2*k.div_ceil(2)+2) as u64);
            if k==4 {
                assert_eq!((t_prove.challenges(),t_prove.raw_queries(),t_prove.bytes_absorbed()),(11,15,14611));
                assert_eq!(pcs::encode(&t_prove.clone().try_challenge_scalar(b"continuation").unwrap()).unwrap(),
                    [8,219,156,130,102,213,43,95,71,177,242,9,97,207,177,172,
                     201,220,124,254,183,226,242,137,50,149,224,89,99,20,224,12]);
            }
            assert_eq!(dense_t.try_challenge_scalar(b"continuation").unwrap(),
                t_prove.clone().try_challenge_scalar(b"continuation").unwrap());
            // Header count fields and every scalar class are bounded before PCS decode.
            for i in 8..12 {let mut bad=encoded.clone();bad[i]^=1;assert!(decode_proof(&bad,k).is_err());}
            let mut bad=encoded.clone();bad[0]^=1;assert!(decode_proof(&bad,k).is_err());
            let mut bad=encoded.clone();bad.pop();assert!(decode_proof(&bad,k).is_err());
            let mut bad=encoded.clone();bad.push(0);assert!(decode_proof(&bad,k).is_err());
            let mut bad=encoded.clone();let size_at=12+96*k+32;bad[size_at..size_at+4].copy_from_slice(&u32::MAX.to_le_bytes());assert!(decode_proof(&bad,k).is_err());
            let modulus=Fr::MODULUS.to_bytes_le();let mut bad=encoded.clone();bad[12+96*k..12+96*k+32].copy_from_slice(&modulus[..32]);assert!(decode_proof(&bad,k).is_err());
            if k>0 {let mut bad=encoded.clone();bad[12..44].copy_from_slice(&modulus[..32]);assert!(decode_proof(&bad,k).is_err());}
            let mut wrong=statement.clone();wrong.setup_id[0]^=1;assert!(verify(&wrong,&setup,&proof).is_err());
            let mut wrong=statement.clone();wrong.corpus_id=Some([7;32]);assert!(verify(&wrong,&setup,&proof).is_err());
            let mut wrong=statement.clone();wrong.commitment=pcs::generate_setup(k).and_then(|s|{
                let other=pcs::commit(&vec![Fr::one();1usize<<k],&s)?;Ok(other.commitment)}).unwrap();
            if pcs::encode_commitment(&wrong.commitment).unwrap()!=pcs::encode_commitment(&statement.commitment).unwrap(){assert!(verify(&wrong,&setup,&proof).is_err());}
            drop(packed);std::fs::remove_file(path).unwrap();
        }
    }
    #[test]
    #[ignore="explicit k24 comparison; set NIPOPOW_OPENING_FUSION_DIR to a fresh output directory"]
    fn diagnostic_k24_fused_opening_matches_reference_and_separates_projection_io(){
        use std::path::PathBuf;
        const K:usize=24;
        let out=PathBuf::from(std::env::var_os("NIPOPOW_OPENING_FUSION_DIR")
            .expect("NIPOPOW_OPENING_FUSION_DIR must name a fresh output directory"));
        assert!(out.is_dir(),"diagnostic output directory must already exist");
        let source_path=out.join(format!("opening-fusion-k24-packed-{}.bin",std::process::id()));
        let mixed=(0..(1usize<<(K-3))).map(|i|((i.wrapping_mul(73)^(i>>3)^(i>>11))&0xff) as u8).collect::<Vec<_>>();
        let mut writer=packed::PackedFileWriter::create_new(&source_path,K).unwrap();
        writer.write_bytes(&mixed).unwrap();
        let packed=writer.finish().unwrap();
        let setup=pcs::generate_setup(K).unwrap();
        let committed=packed::commit(&packed,&setup).unwrap();
        let claims=std::array::from_fn(|j|{
            let point=(0..K).map(|i|Fr::from(((2+17*j+31*i)%251+1) as u64)).collect::<Vec<_>>();
            Claim{value:packed.evaluate(&point).unwrap(),point}
        });
        let statement=Statement{log_n:K,setup_id:setup.id,commitment:committed.commitment,
            corpus_id:Some([0x53;32]),claims};
        let sigma=K.div_ceil(2);let c=1usize<<sigma;let rows=1usize<<(K/2);

        packed.reset_io_metrics();
        let mut reference_projection_metrics=Metrics::default();
        let before=Instant::now();
        let reference_projection=project_reference(&packed,&statement.claims,sigma,c,rows,&mut reference_projection_metrics).unwrap();
        let reference_projection_seconds=before.elapsed().as_secs_f64();
        let reference_projection_io=packed.io_metrics_snapshot();
        assert_eq!(reference_projection_io.read_calls,(CLAIMS*rows) as u64);
        assert_eq!(reference_projection_io.read_bytes,14*1024*1024);
        assert_eq!(reference_projection_metrics.projection_scans,CLAIMS);

        packed.reset_io_metrics();
        let mut fused_projection_metrics=Metrics::default();
        let before=Instant::now();
        let fused_projection=project_fused(&packed,&statement.claims,sigma,c,rows,&mut fused_projection_metrics).unwrap();
        let fused_projection_seconds=before.elapsed().as_secs_f64();
        let fused_projection_io=packed.io_metrics_snapshot();
        assert_eq!(fused_projection_io.read_calls,rows as u64);
        assert_eq!(fused_projection_io.read_bytes,2*1024*1024);
        assert_eq!(fused_projection_metrics.projection_scans,1);
        assert_eq!(fused_projection,reference_projection);

        // Complete proving comparison follows the explicit baseline-then-fused order.
        packed.reset_io_metrics();
        let before=Instant::now();
        let mut reference_transcript=Transcript::new(DOMAIN);
        let (reference_proof,reference_metrics)=prove_on_reference(&packed,&committed,&setup,&statement,&mut reference_transcript,None).unwrap();
        let reference_prove_seconds=before.elapsed().as_secs_f64();
        let reference_all_io=packed.io_metrics_snapshot();
        packed.reset_io_metrics();
        let before=Instant::now();
        let mut fused_transcript=Transcript::new(DOMAIN);
        let (fused_proof,fused_metrics)=prove_on(&packed,&committed,&setup,&statement,&mut fused_transcript,None).unwrap();
        let fused_prove_seconds=before.elapsed().as_secs_f64();
        let fused_all_io=packed.io_metrics_snapshot();
        let reference_packet=encode_proof(&reference_proof,K).unwrap();
        let fused_packet=encode_proof(&fused_proof,K).unwrap();
        assert_eq!(reference_proof.rounds,fused_proof.rounds);
        assert_eq!(reference_proof.terminal,fused_proof.terminal);
        assert_eq!(reference_packet,fused_packet);
        let ledger=|t:&Transcript|(t.challenges(),t.raw_queries(),t.bytes_absorbed());
        assert_eq!(ledger(&reference_transcript),ledger(&fused_transcript));
        let mut reference_next=reference_transcript.clone();let mut fused_next=fused_transcript.clone();
        assert_eq!(reference_next.try_challenge_scalar(b"continuation").unwrap(),fused_next.try_challenge_scalar(b"continuation").unwrap());
        assert_eq!(ledger(&verify(&statement,&setup,&reference_proof).unwrap()),ledger(&reference_transcript));
        assert_eq!(ledger(&verify(&statement,&setup,&fused_proof).unwrap()),ledger(&fused_transcript));
        assert_eq!(reference_all_io.read_calls-reference_projection_io.read_calls,
            fused_all_io.read_calls-fused_projection_io.read_calls,"transition and PCS source read calls should remain equal");
        assert_eq!(reference_all_io.read_bytes-reference_projection_io.read_bytes,
            fused_all_io.read_bytes-fused_projection_io.read_bytes,"transition and PCS source reads should remain equal");

        let metrics_path=out.join(format!("opening-fusion-k24-metrics-{}.txt",std::process::id()));
        let baseline_projection_peak_fields=(CLAIMS+1)*c+rows;
        let fused_projection_peak_fields=(CLAIMS+1)*c+CLAIMS*rows;
        let report=format!(concat!(
            "run_order=baseline_then_fused\nsource_bytes={}\nk={}\nclaims={}\n",
            "baseline_projection_reads={}\nbaseline_projection_bytes={}\nbaseline_projection_seconds={:.6}\n",
            "fused_projection_reads={}\nfused_projection_bytes={}\nfused_projection_seconds={:.6}\n",
            "baseline_nonprojection_reads={}\nfused_nonprojection_reads={}\n",
            "baseline_nonprojection_bytes={}\nfused_nonprojection_bytes={}\n",
            "baseline_complete_prove_seconds={:.6}\nfused_complete_prove_seconds={:.6}\n",
            "proof_bytes={}\nbaseline_projection_peak_fields={}\nfused_projection_peak_fields={}\n",
            "baseline_maximum_fields={}\nfused_maximum_fields={}\n"
        ),mixed.len(),K,CLAIMS,reference_projection_io.read_calls,reference_projection_io.read_bytes,reference_projection_seconds,
            fused_projection_io.read_calls,fused_projection_io.read_bytes,fused_projection_seconds,
            reference_all_io.read_calls-reference_projection_io.read_calls,fused_all_io.read_calls-fused_projection_io.read_calls,
            reference_all_io.read_bytes-reference_projection_io.read_bytes,fused_all_io.read_bytes-fused_projection_io.read_bytes,
            reference_prove_seconds,fused_prove_seconds,reference_packet.len(),baseline_projection_peak_fields,
            fused_projection_peak_fields,reference_metrics.maximum_fields,fused_metrics.maximum_fields);
        let mut file=OpenOptions::new().write(true).create_new(true).open(metrics_path).unwrap();
        file.write_all(report.as_bytes()).unwrap();
        println!("{report}");
    }
    #[test]
    fn verifier_codec_boundary_is_k41_while_producer_stays_k24(){
        assert_eq!(pcs::MAX_LOG_N,24);
        assert_eq!(pcs::MAX_VERIFY_LOG_N,41);
        assert!(decode_proof(&[],41).err().unwrap().contains("truncated"));
        assert!(decode_proof(&[],42).err().unwrap().contains("unsupported"));
        let k=41;
        let mut packet=vec![0u8;12+96*k+36];
        packet[..8].copy_from_slice(MAGIC);
        packet[8]=VERSION;packet[9]=k as u8;packet[10]=CLAIMS as u8;packet[11]=0;
        let err=decode_proof(&packet,k).err().unwrap();
        assert!(err.contains("Dory proof length"),"{err}");
    }
    #[test]
    fn producer_rejects_only_k25_before_source_and_transcript_work(){
        let (path,packed,setup,committed,mut statement)=fixture(&[0,1],1);
        statement.log_n=25;
        for claim in &mut statement.claims {claim.point=vec![Fr::zero();25];}
        // Metadata-only facade: every admission field matches k=25 except the
        // producer cap. It must fail before this unused k=1 backend is touched.
        let metadata_setup=Setup{prover:setup.prover.clone(),verifier:setup.verifier.clone(),id:setup.id,log_n:25};
        let mut transcript=Transcript::new(DOMAIN);
        let before=(transcript.challenges(),transcript.raw_queries(),transcript.bytes_absorbed());
        let err=prove_on(&packed,&committed,&metadata_setup,&statement,&mut transcript,None).err().unwrap();
        assert!(err.contains("expected statement/setup/dimension"),"{err}");
        assert_eq!((transcript.challenges(),transcript.raw_queries(),transcript.bytes_absorbed()),before,
            "producer cap must reject before binding or source access");
        drop(packed);std::fs::remove_file(path).unwrap();
    }
    #[test]
    fn admitted_odd_dimension_matches_batch_transcript_and_rejects_mutants(){
        let k=9;let bits=(0..1usize<<k).map(|i|(((i*73+((i>>1)*19)+5)>>1)&1) as u8).collect::<Vec<_>>();
        let (path,packed,setup,committed,statement)=fixture(&bits,k);
        let (proof,_,prover_t)=prove(&packed,&committed,&setup,&statement).unwrap();
        let packet=encode_proof(&proof,k).unwrap();let decoded=decode_proof(&packet,k).unwrap();
        let key=generated_admitted_key(&setup);
        let setup_t=verify(&statement,&setup,&decoded).unwrap();
        let admitted_t=verify_admitted(&statement,&key,&decoded).unwrap();
        let ledger=|t:&Transcript|(t.challenges(),t.raw_queries(),t.bytes_absorbed());
        assert_eq!(ledger(&prover_t),ledger(&setup_t));
        assert_eq!(ledger(&setup_t),ledger(&admitted_t));
        let mut p=prover_t.clone();let mut v=admitted_t.clone();
        assert_eq!(p.try_challenge_scalar(b"continuation").unwrap(),v.try_challenge_scalar(b"continuation").unwrap());

        let encoded_key=pcs::encode(&dory_pcs::backends::arkworks::ArkworksVerifierSetup(setup.verifier.clone())).unwrap();
        let wrong_id=crate::verifier_key::admit_generated_test_key(k,&encoded_key,[0;32]).unwrap();
        assert!(verify_admitted(&statement,&wrong_id,&decoded).err().unwrap().contains("verifier-key/dimension"));
        let other_setup=pcs::generate_setup(k-1).unwrap();
        let wrong_dimension=generated_admitted_key_with_id(&other_setup,setup.id);
        assert!(verify_admitted(&statement,&wrong_dimension,&decoded).err().unwrap().contains("verifier-key/dimension"));
        let mut untouched=Transcript::new(DOMAIN);
        let untouched_before=(untouched.challenges(),untouched.raw_queries(),untouched.bytes_absorbed());
        assert!(verify_on(&statement,VerificationKey::Admitted(&wrong_id),&decoded,&mut untouched,None).is_err());
        assert_eq!((untouched.challenges(),untouched.raw_queries(),untouched.bytes_absorbed()),untouched_before,
            "key admission must reject before transcript binding");
        let mut wrong=statement.clone();wrong.claims[0].point.pop();
        assert!(verify_admitted(&wrong,&key,&decoded).err().unwrap().contains("dimension rejected"));
        let mut wrong=statement.clone();wrong.claims[0].value+=Fr::one();
        assert!(verify_admitted(&wrong,&key,&decoded).err().unwrap().contains("round sum rejected"));
        let mut wrong=statement.clone();
        let other_values=vec![Fr::one();1usize<<k];
        wrong.commitment=pcs::commit(&other_values,&setup).unwrap().commitment;
        assert!(verify_admitted(&wrong,&key,&decoded).is_err());
        drop(packed);std::fs::remove_file(path).unwrap();
    }
    #[test]
    fn bitpacked_precomputed_v_odd_log9_matches_packet_transcript_and_verifier(){
        let k=9;
        let (bits,bytes)=distinct_log9_bits_and_bytes();
        let (path,source,setup,committed,statement)=fixture(&bits,k);
        let mut digest=[0u8;64];digest.copy_from_slice(Blake2b512::digest(&bytes).as_slice());
        let (baseline,_,baseline_t)=prove(&source,&committed,&setup,&statement).unwrap();
        let fallback_before=source.fallback_calls_for_test();
        assert!(fallback_before.iter().all(|count|*count>0),"baseline exercises both fallback counters");
        let (candidate,metrics,candidate_t)=
            prove_bitpacked_precomputed_v(&source,&committed,&setup,&statement,&digest).unwrap();
        assert_eq!(source.fallback_calls_for_test(),fallback_before,
            "optimized entry must not expand field rows or call the legacy PCS scan");
        assert_eq!(metrics.row_capacity,4,"log9 reads exactly four packed bytes per row");
        let baseline_packet=encode_proof(&baseline,k).unwrap();
        let candidate_packet=encode_proof(&candidate,k).unwrap();
        assert_eq!(candidate_packet,baseline_packet);
        assert_eq!((metrics.projection_scans,metrics.transition_scans),(1,1));
        let ledger=|t:&Transcript|(t.challenges(),t.raw_queries(),t.bytes_absorbed());
        assert_eq!(ledger(&candidate_t),ledger(&baseline_t));
        let mut a=candidate_t.clone();let mut b=baseline_t.clone();
        assert_eq!(a.try_challenge_scalar(b"continuation").unwrap(),b.try_challenge_scalar(b"continuation").unwrap());
        let decoded=decode_proof(&candidate_packet,k).unwrap();
        let verifier_t=verify(&statement,&setup,&decoded).unwrap();
        assert_eq!(ledger(&candidate_t),ledger(&verifier_t));
        let key=generated_admitted_key(&setup);
        let admitted_t=verify_admitted(&statement,&key,&decoded).unwrap();
        assert_eq!(ledger(&candidate_t),ledger(&admitted_t));
        drop(source);std::fs::remove_file(path).unwrap();
    }
    #[test]
    fn bitpacked_frontend_faults_fail_before_packet_or_pcs(){
        use std::cell::Cell;
        #[derive(Clone,Copy,Debug)]enum Fault{Read,Short,Bit,SecondPass,RepeatRowZero,SwapAdjacent}
        struct Injected<'a>{source:&'a PackedFile,mode:Fault,calls:Cell<usize>,rows:usize}
        impl BitRowSource for Injected<'_>{
            fn input_len(&self)->usize{self.source.input_len()}
            fn read_row_bits(&self,width:usize,row:usize)->Result<Vec<u8>,String>{
                let call=self.calls.get();self.calls.set(call+1);
                if matches!(self.mode,Fault::Read)&&call==1{return Err("injected bit source read".into());}
                let selected_row=match (self.mode,call){
                    (Fault::RepeatRowZero,1)=>0,
                    (Fault::SwapAdjacent,1)=>2,
                    (Fault::SwapAdjacent,2)=>1,
                    _=>row,
                };
                let mut bytes=self.source.read_row_bits(width,selected_row)?;
                if matches!(self.mode,Fault::Short)&&call==0{bytes.pop();}
                if matches!(self.mode,Fault::Bit)&&call==0{bytes[0]^=1;}
                if matches!(self.mode,Fault::SecondPass)&&call==self.rows{bytes[0]^=1;}
                Ok(bytes)
            }
        }
        let k=9;let (bits,bytes)=distinct_log9_bits_and_bytes();
        let (path,source,setup,committed,statement)=fixture(&bits,k);
        let mut digest=[0u8;64];digest.copy_from_slice(Blake2b512::digest(&bytes).as_slice());
        let rows=1usize<<(k/2);
        for mode in [Fault::Read,Fault::Short,Fault::Bit,Fault::SecondPass,
            Fault::RepeatRowZero,Fault::SwapAdjacent]{
            let faulty=Injected{source:&source,mode,calls:Cell::new(0),rows};
            let mut transcript=Transcript::new(DOMAIN);
            let error=prove_frontend_bitpacked_on(&faulty,&statement,Some(&digest),&mut transcript).err().unwrap();
            let expected=match mode {
                Fault::Read=>"injected bit source read",Fault::Short=>"row length drift",
                _=>"digest mismatch",
            };
            assert!(error.contains(expected),"fault={mode:?}: expected {expected}, got {error}");
            if matches!(mode,Fault::RepeatRowZero|Fault::SwapAdjacent){
                assert!(error.contains("digest mismatch"),"{error}");
                println!("log9_reorder_mutant={mode:?} result=Err({error})");
            }
        }
        let mut wrong=digest;wrong[0]^=1;
        assert!(prove_bitpacked_precomputed_v(&source,&committed,&setup,&statement,&wrong)
            .err().unwrap().contains("digest mismatch"));
        let mut mismatched=statement.clone();
        mismatched.commitment=mismatched.commitment
            +BN254::pair(&setup.prover.g1_vec[0],&setup.prover.g2_vec[0]);
        assert!(prove_bitpacked_precomputed_v(&source,&committed,&setup,&mismatched,&digest)
            .err().unwrap().contains("source/commitment mismatch"));
        let mut transcript=Transcript::new(DOMAIN);
        let frontend=prove_frontend_bitpacked_on(&source,&statement,Some(&digest),&mut transcript).unwrap();
        let mut drifted_point=frontend.point.clone();drifted_point[0]+=Fr::one();
        let before=(transcript.challenges(),transcript.raw_queries(),transcript.bytes_absorbed());
        assert!(finish_bitpacked_precomputed_v(&source,&committed,&setup,&digest,frontend,
            &drifted_point,&mut transcript).err().unwrap().contains("point drift"));
        assert_eq!(before,(transcript.challenges(),transcript.raw_queries(),transcript.bytes_absorbed()));
        drop(source);std::fs::remove_file(path).unwrap();
    }
    #[test]
    fn implicit_zero_batch_k9_matches_dense_reference_and_transcripts(){
        let k=9;let bits=vec![0u8;1usize<<k];
        let (path,packed,setup,committed,_)=fixture(&bits,k);
        let statement=zero_batch_statement(k,setup.id,committed.commitment);
        let (dense,_,dense_t)=prove(&packed,&committed,&setup,&statement).unwrap();
        let (implicit,z,before_pcs,implicit_t)=implicit_zero_batch_proof(&setup,&statement);
        let dense_packet=encode_proof(&dense,k).unwrap();
        let implicit_packet=encode_proof(&implicit,k).unwrap();
        assert_eq!(implicit_packet,dense_packet);
        assert_eq!((implicit_t.challenges(),implicit_t.raw_queries(),implicit_t.bytes_absorbed()),
            (dense_t.challenges(),dense_t.raw_queries(),dense_t.bytes_absorbed()));
        let decoded=decode_proof(&implicit_packet,k).unwrap();
        let key=generated_admitted_key(&setup);
        let mut pcs_t=before_pcs.clone();
        pcs::verify_admitted(statement.commitment,Fr::zero(),&z,&decoded.pcs,&key,&mut pcs_t).unwrap();
        let setup_t=verify(&statement,&setup,&decoded).unwrap();
        let admitted_t=verify_admitted(&statement,&key,&decoded).unwrap();
        let ledger=|t:&Transcript|(t.challenges(),t.raw_queries(),t.bytes_absorbed());
        assert_eq!(ledger(&dense_t),ledger(&pcs_t));
        assert_eq!(ledger(&setup_t),ledger(&admitted_t));
        let mut dense_cont=dense_t.clone();let mut pcs_cont=pcs_t.clone();
        let mut setup_cont=setup_t.clone();let mut admitted_cont=admitted_t.clone();
        let continuation=dense_cont.try_challenge_scalar(b"continuation").unwrap();
        assert_eq!(pcs_cont.try_challenge_scalar(b"continuation").unwrap(),continuation);
        assert_eq!(setup_cont.try_challenge_scalar(b"continuation").unwrap(),continuation);
        assert_eq!(admitted_cont.try_challenge_scalar(b"continuation").unwrap(),continuation);
        drop(packed);std::fs::remove_file(path).unwrap();
    }
    #[test]
    #[ignore="expensive k=41 implicit-zero prover/verifier diagnostic"]
    fn diagnostic_k41_implicit_zero_batch_passes_pinned_admitted_verifier(){
        let k=41;
        let setup=pcs::generate_setup_for_scale_diagnostic(k).unwrap();
        let pinned_key_bytes:&[u8]=include_bytes!("../fixtures/verifier-keys-v1/log41.vk");
        let key=crate::verifier_key::admit(k,pinned_key_bytes).unwrap();
        let regenerated_verifier=pcs::encode(&ArkworksVerifierSetup(setup.verifier.clone())).unwrap();
        assert_eq!(regenerated_verifier,pinned_key_bytes,"diagnostic prover setup differs from pinned verifier bytes");
        assert_eq!(setup.id.as_slice(),key.id(),"diagnostic setup ID differs from pinned key ID");
        let statement=zero_batch_statement(k,setup.id,<ArkGT as Group>::identity());
        let (proof,z,before_pcs,producer_t)=implicit_zero_batch_proof(&setup,&statement);
        let packet=encode_proof(&proof,k).unwrap();
        let decoded=decode_proof(&packet,k).unwrap();
        assert_eq!(encode_proof(&decoded,k).unwrap(),packet,"batch encoding is not canonical");

        let mut pcs_t=before_pcs.clone();
        pcs::verify_admitted(statement.commitment,Fr::zero(),&z,&decoded.pcs,&key,&mut pcs_t).unwrap();
        let batch_t=verify_admitted(&statement,&key,&decoded).unwrap();
        let ledger=|t:&Transcript|(t.challenges(),t.raw_queries(),t.bytes_absorbed());
        assert_eq!(ledger(&producer_t),ledger(&pcs_t));
        assert_eq!(ledger(&producer_t),ledger(&batch_t));
        let mut producer_cont=producer_t.clone();let mut pcs_cont=pcs_t.clone();let mut batch_cont=batch_t.clone();
        let continuation=producer_cont.try_challenge_scalar(b"continuation").unwrap();
        assert_eq!(pcs_cont.try_challenge_scalar(b"continuation").unwrap(),continuation);
        assert_eq!(batch_cont.try_challenge_scalar(b"continuation").unwrap(),continuation);

        let mut wrong_domain=Transcript::new(b"wrong-k41-domain");
        assert!(pcs::verify_admitted(statement.commitment,Fr::zero(),&z,&decoded.pcs,&key,&mut wrong_domain).is_err());
        let mut wrong=statement.clone();wrong.claims[0].value=Fr::one();
        assert!(verify_admitted(&wrong,&key,&decoded).is_err());
        let mut wrong=statement.clone();wrong.claims[0].point[0]+=Fr::one();
        let err=verify_admitted(&wrong,&key,&decoded).err().expect("mutated point must reject");
        assert!(err.contains("final PCS rejected"),"{err}");
        let mut wrong=statement.clone();wrong.commitment=setup.prover.ht;
        let err=verify_admitted(&wrong,&key,&decoded).err().expect("mutated commitment must reject");
        assert!(err.contains("final PCS rejected"),"{err}");
        let mut wrong=statement.clone();wrong.corpus_id=Some([0x54;32]);
        let err=verify_admitted(&wrong,&key,&decoded).err().expect("mutated corpus ID must reject");
        assert!(err.contains("final PCS rejected"),"{err}");
        let mut altered=Proof{rounds:decoded.rounds.clone(),terminal:decoded.terminal,pcs:decoded.pcs.clone()};
        altered.pcs.final_message.as_mut().unwrap().e1=setup.prover.g1_vec[0];
        let err=verify_admitted(&statement,&key,&altered).err().expect("mutated Dory final message must reject");
        assert!(err.contains("final PCS rejected"),"{err}");
    }
    #[test]
    fn row_failures_and_round_algebra_reject(){
        assert!(read_boolean(&BadSource{len:8,kind:0},4,0).unwrap_err().contains("short"));
        assert!(read_boolean(&BadSource{len:8,kind:1},4,0).unwrap_err().contains("non-Boolean"));
        assert!(read_boolean(&BadSource{len:8,kind:2},4,0).unwrap_err().contains("injected"));
        assert!(check_round(&[Fr::zero();3],Fr::one()).is_err());
        assert!(check_round(&[Fr::one(),Fr::zero(),Fr::zero()],Fr::one()).is_err());
    }
    #[test]
    fn fused_projection_matches_exact_reference_across_shapes_and_claim_sets(){
        for (k,pattern) in [(0,0u8),(1,1),(2,2),(3,3),(4,4),(5,5)] {
            let bits=(0..1usize<<k).map(|i|match pattern {
                0|1=>0,
                2=>1,
                _=>(((i*73+((i>>1)*19)+5)>>1)&1) as u8,
            }).collect::<Vec<_>>();
            let (path,packed,_setup,_committed,statement)=fixture(&bits,k);
            let sigma=k.div_ceil(2);let width=1usize<<sigma;let rows=1usize<<(k/2);
            let mut unique=statement.claims.clone();
            if k>0 {unique[0].point[0]=Fr::from(2u64);unique[1].point[0]=Fr::from(3u64);}
            let mut fused_metrics=Metrics::default();
            let fused=project_fused(&packed,&unique,sigma,width,rows,&mut fused_metrics).unwrap();
            let mut reference_metrics=Metrics::default();
            let reference=project_reference(&packed,&unique,sigma,width,rows,&mut reference_metrics).unwrap();
            assert_eq!(fused,reference,"unique k={k}");
            assert_eq!(fused_metrics.projection_scans,1);
            assert_eq!(reference_metrics.projection_scans,CLAIMS);

            let mut duplicated=unique.clone();duplicated[6]=duplicated[0].clone();
            let mut fused_metrics=Metrics::default();
            let fused=project_fused(&packed,&duplicated,sigma,width,rows,&mut fused_metrics).unwrap();
            let mut reference_metrics=Metrics::default();
            let reference=project_reference(&packed,&duplicated,sigma,width,rows,&mut reference_metrics).unwrap();
            assert_eq!(fused,reference,"duplicate k={k}");
            drop(packed);std::fs::remove_file(path).unwrap();
        }
    }
    #[test]
    fn fused_projection_reads_and_validates_rows_even_when_all_claim_weights_are_zero(){
        let claims:[Claim;CLAIMS]=std::array::from_fn(|_|Claim{point:vec![Fr::zero(),Fr::zero()],value:Fr::zero()});
        for kind in 0..3 {
            let source=BadRowSource{input_len:4,bad_row:1,kind};
            let mut metrics=Metrics::default();
            let error=project_fused(&source,&claims,1,2,2,&mut metrics).unwrap_err();
            assert!(match kind {0=>error.contains("short row"),1=>error.contains("non-Boolean"),_=>error.contains("injected")},"{error}");
        }
    }
    #[test]
    fn each_claim_bound_and_ordered(){
        let k=3;let bits=[0,1,1,0,1,0,0,1];
        let (path,packed,setup,committed,statement)=fixture(&bits,k);
        let (proof,_,_)=prove(&packed,&committed,&setup,&statement).unwrap();
        let key=generated_admitted_key(&setup);
        for j in 0..CLAIMS {
            let mut bad=statement.clone();bad.claims[j].value+=Fr::one();assert!(verify(&bad,&setup,&proof).is_err());
            assert!(verify_admitted(&bad,&key,&proof).is_err());

            for long in [false,true] {
                let mut bad=statement.clone();
                if long {bad.claims[j].point.push(Fr::zero());} else {bad.claims[j].point.pop();}
                let mut transcript=Transcript::new(DOMAIN);
                let before=(transcript.challenges(),transcript.raw_queries(),transcript.bytes_absorbed());
                let err=verify_on(&bad,VerificationKey::Admitted(&key),&proof,&mut transcript,None).err().unwrap();
                assert!(err.contains("verifier-key/dimension"),"claim {j}, long={long}: {err}");
                assert_eq!((transcript.challenges(),transcript.raw_queries(),transcript.bytes_absorbed()),before,
                    "claim {j}, long={long}: dimension rejected before transcript binding");
            }
            let mut bad=statement.clone();bad.claims[j].point[0]+=Fr::one();
            assert_ne!(dense_mle(&bits.map(|b|Fr::from(b as u64)),&bad.claims[j].point),statement.claims[j].value);
            assert!(verify(&bad,&setup,&proof).is_err());
            assert!(verify_admitted(&bad,&key,&proof).is_err());
        }
        let mut bad=statement.clone();bad.claims.swap(0,1);assert!(verify(&bad,&setup,&proof).is_err());
        assert!(verify_admitted(&bad,&key,&proof).is_err());
        let mut bad=statement.clone();bad.claims[1]=bad.claims[0].clone();assert!(verify(&bad,&setup,&proof).is_err());
        assert!(verify_admitted(&bad,&key,&proof).is_err());
        drop(packed);std::fs::remove_file(path).unwrap();
    }
    #[test]
    fn zero_factor_still_requires_pcs_and_false_terminal_reaches_pcs(){
        let k=1;let bits=[0,1];
        let (path,packed,setup,committed,mut statement)=fixture(&bits,k);
        let key=generated_admitted_key(&setup);
        for claim in &mut statement.claims {claim.point=vec![Fr::zero()];claim.value=Fr::zero();}
        let controlled=[Fr::one(),Fr::one()];
        let mut tp=Transcript::new(DOMAIN);
        let (mut proof,_) = prove_on(&packed,&committed,&setup,&statement,&mut tp,Some(&controlled)).unwrap();
        assert_eq!(proof.terminal,Fr::one());
        let mut tv_setup=Transcript::new(DOMAIN);
        verify_on(&statement,VerificationKey::Setup(&setup),&proof,&mut tv_setup,Some(&controlled)).unwrap();
        let mut tv_admitted=Transcript::new(DOMAIN);
        verify_on(&statement,VerificationKey::Admitted(&key),&proof,&mut tv_admitted,Some(&controlled)).unwrap();
        assert_eq!((tp.challenges(),tp.raw_queries(),tp.bytes_absorbed()),
            (tv_setup.challenges(),tv_setup.raw_queries(),tv_setup.bytes_absorbed()));
        assert_eq!((tv_setup.challenges(),tv_setup.raw_queries(),tv_setup.bytes_absorbed()),
            (tv_admitted.challenges(),tv_admitted.raw_queries(),tv_admitted.bytes_absorbed()));
        // Test-only omission mutant: replay every reduction check but omit PCS.
        // The altered terminal passes this mutant because the final factor is zero.
        proof.terminal=Fr::from(2u64);
        let mut mutant_t=Transcript::new(DOMAIN);bind(&statement,&mut mutant_t).unwrap();
        let mutant_alpha=challenge(&mut mutant_t,b"opening-batch-alpha",Some(&controlled),0).unwrap();
        let mut mutant_sum=Fr::zero();let mut mutant_power=Fr::one();
        for claim in &statement.claims{mutant_sum+=mutant_power*claim.value;mutant_power*=mutant_alpha;}
        let mut mutant_z=Vec::new();
        for (i,c) in proof.rounds.iter().enumerate(){
            check_round(c,mutant_sum).unwrap();
            let z=append_round_challenge(&mut mutant_t,if i<k.div_ceil(2){0}else{1},i,c,Some(&controlled),i+1).unwrap();
            mutant_sum=eval_quadratic(c,z);mutant_z.push(z);
        }
        let mut mutant_w=Fr::zero();let mut mutant_power=Fr::one();
        for claim in &statement.claims{mutant_w+=mutant_power*eq_point(&claim.point,&mutant_z);mutant_power*=mutant_alpha;}
        assert!(mutant_w.is_zero());assert_eq!(mutant_sum,proof.terminal*mutant_w);
        let err_setup=verify_on(&statement,VerificationKey::Setup(&setup),&proof,&mut Transcript::new(DOMAIN),Some(&controlled)).unwrap_err();
        assert!(err_setup.contains("final PCS rejected"),"{err_setup}");
        let err_admitted=verify_on(&statement,VerificationKey::Admitted(&key),&proof,&mut Transcript::new(DOMAIN),Some(&controlled)).unwrap_err();
        assert!(err_admitted.contains("final PCS rejected"),"{err_admitted}");
        let mut missing=encode_proof(&proof,k).unwrap();missing.truncate(12+96*k+32);
        assert!(decode_proof(&missing,k).is_err());
        drop(packed);std::fs::remove_file(path).unwrap();

        // Fresh reduction and proof are internally consistent for a different
        // polynomial, while the expected commitment remains bound to the first.
        let (path_a,source_a,setup_a,committed_a,mut expected)=fixture(&[0,1],1);
        let (path_b,source_b,_,_,_)=fixture(&[1,0],1);
        for claim in &mut expected.claims {claim.value=source_b.evaluate(&claim.point).unwrap();}
        let mut t=Transcript::new(DOMAIN);
        let (fresh,_) = prove_on(&source_b,&committed_a,&setup_a,&expected,&mut t,None).unwrap();
        let err=verify(&expected,&setup_a,&fresh).err().unwrap();
        assert!(err.contains("final PCS rejected"),"{err}");
        drop(source_a);drop(source_b);std::fs::remove_file(path_a).unwrap();std::fs::remove_file(path_b).unwrap();
    }
    #[test]
    fn degenerate_boolean_sources_and_nonzero_challenges(){
        for (k,bits) in [(0,vec![0]),(1,vec![0,0]),(2,vec![1,1,1,1]),(3,vec![0,1,0,1,0,1,0,1])] {
            let (path,packed,setup,committed,mut statement)=fixture(&bits,k);
            // Repeated points and alpha=1, with all challenge coordinates -1
            // exercise legal near-modulus values and zero coefficients.
            for claim in &mut statement.claims {
                claim.point=vec![Fr::one();k];claim.value=packed.evaluate(&claim.point).unwrap();
            }
            let mut controls=vec![Fr::one()];controls.extend(vec![-Fr::one();k]);
            let mut t=Transcript::new(DOMAIN);
            let (proof,_)=prove_on(&packed,&committed,&setup,&statement,&mut t,Some(&controls)).unwrap();
            let key=generated_admitted_key(&setup);
            verify_on(&statement,VerificationKey::Admitted(&key),&proof,&mut Transcript::new(DOMAIN),Some(&controls)).unwrap();
            drop(packed);std::fs::remove_file(path).unwrap();
        }
    }
}

#[cfg(test)]
mod row_stream_tests {
    use super::*;
    use crate::packed::PackedFileWriter;

    fn bit(index: usize) -> u8 {
        (((index * 73 + (index >> 3) * 19 + 5) >> 2)
            ^ (index >> 16) ^ (index >> 17)) as u8 & 1
    }

    #[test]
    fn wide_row_source_and_fused_projection_match_independent_columns() {
        let width = 1usize << 17;
        let output = std::env::var_os("NIPOPOW_PCS_ROW_DIR")
            .map(std::path::PathBuf::from).unwrap_or_else(std::env::temp_dir);
        assert!(output.is_dir(), "row artifact directory must already exist");
        let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH)
            .unwrap().as_nanos();
        let path = output.join(format!("wide-consumer-{}-{nonce}.bits", std::process::id()));
        let bytes = (0..2 * width / 8)
            .map(|byte| (0..8).fold(0u8, |value, b| value | (bit(byte * 8 + b) << b)))
            .collect::<Vec<_>>();
        let mut writer = PackedFileWriter::create_new(&path, 18).unwrap();
        writer.write_bytes(&bytes).unwrap();
        let source = writer.finish().unwrap();
        for row in 0..2 {
            source.reset_io_metrics();
            let values = RowSource::read_row(&source, width, row).unwrap();
            assert_eq!(values.len(), width);
            for (column, value) in values.iter().enumerate() {
                assert_eq!(*value, Fr::from(bit(row * width + column) as u64));
            }
            let io = source.io_metrics_snapshot();
            assert_eq!(io.read_calls, 2);
            assert_eq!(io.read_bytes, (width / 8) as u64);
        }
        let claims: [Claim; CLAIMS] = std::array::from_fn(|j| Claim {
            point: (0..18).map(|i| Fr::from((3 + j * 19 + i) as u64)).collect(),
            value: Fr::zero(),
        });
        source.reset_io_metrics();
        let mut metrics = Metrics::default();
        // Synthetic sigma17/two-row stride, not a balanced k33 proof.
        let projected = project_fused(&source, &claims, 17, width, 2, &mut metrics).unwrap();
        for (j, projection) in projected.iter().enumerate() {
            let high = claims[j].point[17];
            for (column, value) in projection.iter().enumerate() {
                let expected = Fr::from(bit(column) as u64) * (Fr::one() - high)
                    + Fr::from(bit(width + column) as u64) * high;
                assert_eq!(*value, expected, "claim={j} column={column}");
            }
        }
        let io = source.io_metrics_snapshot();
        assert_eq!(io.read_calls, 4);
        assert_eq!(io.read_bytes, (2 * width / 8) as u64);
        assert_eq!(metrics.projection_scans, 1);
        assert_eq!(metrics.row_capacity, width);
        assert_eq!(metrics.maximum_fields, (CLAIMS + 1) * width + CLAIMS * 2);
        println!("wide_row_width={width} projection_reads={} projection_bytes={} retained_projection_fields={} additional_chunk_fields_at_most=65536; no PCS or k33 admission",
            io.read_calls, io.read_bytes, metrics.maximum_fields);
    }
}

//! Local r4 certificate profile for the retained mainnet snapshots.
//! The receiver reconstructs x from canonical public fields and root-bound
//! records, verifies seven relations and the common PCS, then derives the audit.
use super::{full_structural as relation, *};
use crate::native_work_opening::{NativeWorkMembershipContext, MAX_OPENING_BYTES};
use crate::packed_owner_assembly::{H21EligibleContext, NativePrefix};
use num_bigint::BigUint;
use std::io::Read;

#[cfg(all(windows, feature = "h21-snapshot-n0"))]
#[path = "role1_header_ordinal_test.rs"]
mod role1_header_ordinal_test;

#[cfg(all(windows,feature="h21-snapshot-n0"))]
fn original_n0_public_context()->Result<H21StructuralDiagnostic,String>{
    let x=bounded_file(&external("NIPOPOW_V2_INPUTS")?.join("statement.x"),MAX_X)?;
    if format!("{:x}",Blake2b::<U32>::digest(&x))!="43f5da4d4fe06df86b39bdf9c0bf3805be3783e7f8246a5a2ed09e4fe62ff44d"{
        return Err("wrong original N0 statement".into());
    }
    let (fields,sampled,exact)=Outputs::read_prefix(&x)?;
    let (root,total,tip,time,maps)=relation::read_statement_fields(fields)?;
    relation::build_full_context(&x,root,total,tip,time,maps,sampled,exact)
}

#[cfg(all(windows,feature="h21-snapshot-n0"))]
fn original_n0_u0_context()->Result<(H21StructuralDiagnostic,Vec<u8>),String>{
    let marker=bounded_file(&external("NIPOPOW_V2_ROLE1_N0_MARKER")?,520)?;
    if format!("{:x}",Blake2b::<U32>::digest(&marker))!="56096f2fcb41f665a86bdc8787e58d9bf7bedc94418783fe0f7aa7e685cd2feb"
        || marker.len()!=520 || &marker[..8]!=b"R4GKR001"{return Err("wrong historical U0 marker".into());}
    Ok((original_n0_public_context()?,marker))
}

#[cfg(all(windows,feature="h21-snapshot-n0"))]
#[test]
#[ignore="detached complete N0 POINT GKR from the sealed witness and original commitment"]
fn produce_detached_n0_point_role()->Result<(),String>{
    let budget=relation::detached_role::standalone_budget(relation::detached_role::POINT)?;
    let owned=original_n0_public_context()?;
    relation::detached_role::produce(relation::detached_role::POINT,&owned,budget)
}

#[cfg(all(windows,feature="h21-snapshot-n0"))]
#[test]
#[ignore="verify the detached N0 POINT role from public inputs and proof bytes only"]
fn verify_detached_n0_point_role()->Result<(),String>{
    relation::detached_role::verify_public(relation::detached_role::POINT,&original_n0_public_context()?)
}

#[cfg(all(windows,feature="h21-snapshot-n0"))]
#[test]
#[ignore="complete detached N0 AUD2 metadata GKR, two structural workers"]
fn produce_detached_n0_metadata_role()->Result<(),String>{
    use relation::detached_role as d;
    let budget=d::standalone_budget(d::METADATA)?;
    d::produce(d::METADATA,&original_n0_public_context()?,budget)
}

#[cfg(all(windows,feature="h21-snapshot-n0"))]
#[test]
#[ignore="verify the detached N0 AUD2 metadata role from public inputs and proof bytes"]
fn verify_detached_n0_metadata_role()->Result<(),String>{
    use relation::detached_role as d;
    d::verify_public(d::METADATA,&original_n0_public_context()?)
}

#[cfg(all(windows,feature="h21-snapshot-n0"))]
#[test]
#[ignore="produce the detached N0 tree role using the canonical historical witness"]
fn produce_detached_n0_tree_role()->Result<(),String>{
    use relation::detached_role as d;
    let budget=d::standalone_budget(d::TREE)?;
    d::produce(d::TREE,&original_n0_public_context()?,budget)
}

#[cfg(all(windows,feature="h21-snapshot-n0"))]
#[test]
#[ignore="derive the public GKR claim from a detached N0 tree proof"]
fn verify_detached_n0_tree_role()->Result<(),String>{
    use relation::detached_role as d;
    d::verify_public(d::TREE,&original_n0_public_context()?)
}

#[cfg(all(windows,feature="h21-snapshot-n0"))]
#[test]
#[ignore="produce the detached N0 height_daa role using the canonical historical witness"]
fn produce_detached_n0_height_daa_role()->Result<(),String>{
    use relation::detached_role as d;
    let budget=d::standalone_budget(d::HEIGHT_DAA)?;
    d::produce(d::HEIGHT_DAA,&original_n0_public_context()?,budget)
}

#[cfg(all(windows,feature="h21-snapshot-n0"))]
#[test]
#[ignore="derive the public GKR claim from a detached N0 height_daa proof"]
fn verify_detached_n0_height_daa_role()->Result<(),String>{
    use relation::detached_role as d;
    d::verify_public(d::HEIGHT_DAA,&original_n0_public_context()?)
}

#[cfg(all(windows,feature="h21-snapshot-n0"))]
#[test]
#[ignore="durable first GKR round for an aligned range of the original N0 witness"]
fn produce_real_n0_role1_u0_shards()->Result<(),String>{
    if std::env::var("RAYON_NUM_THREADS").as_deref()!=Ok("1") ||
        std::env::var("RUST_TEST_THREADS").as_deref()!=Ok("1"){return Err("U0 range requires one worker".into());}
    let (owned,marker)=original_n0_u0_context()?;let context=owned.context()?;
    let (r,_)=super::h21_atomic_seven::frozen_role1_u0_prefix(&context,&marker[136..])?;
    crate::sparse_stream_roster::h21_u0::produce(&context.roster,&r,&owned.public_bytes,
        include_bytes!("../fixtures/verifier-keys-v1/log41.vk"),&marker,&external("NIPOPOW_V2_ROLE1_N0_WITNESS")?)
}

#[cfg(all(windows,feature="h21-snapshot-n0"))]
#[test]
#[ignore="real-data differential for the full historical tree, height/difficulty and metadata owner messages"]
fn test_real_n0_structural_owner_batches()->Result<(),String>{
    use crate::sparse_stream_roster::{H21CandidateRole as Role,h21_structural_batch_tests as check};
    crate::sparse_stream_roster::h21_structural_batches::check_resource_bounds()?;
    let (owned,marker)=original_n0_u0_context()?;
    let context=owned.context()?;
    let file=external("NIPOPOW_V2_ROLE1_N0_WITNESS")?;
    let mut reports=Vec::new();
    for role in [Role::Tree,Role::HeightDaa,Role::Metadata] {
        let r=super::h21_atomic_seven::historical_edge_output_point(&context,role.index(),&marker[136..])?;
        let shape=context.candidate_role_shape(role)?;
        if r.len()!=shape.row_log(){return Err("wrong historical row point".into());}
        reports.push(check::check(&context,context.roster.daa(),&shape,&r,&file)?);
    }
    println!("H21_STRUCTURAL_BATCH_MATCH {}",serde_json::json!({
        "snapshot":"N0","roles":[2,4,6],"reports":reports,"proof_exported":false,
        "later_challenge_points":"diagnostic","global_reference":"bounded genuine occurrences"
    }));
    Ok(())
}

#[cfg(all(windows,feature="h21-snapshot-n0"))]
#[test]
#[ignore="compare serial and concurrent owner contributions on the retained N0 witness"]
fn test_real_n0_role1_owner_batches()->Result<(),String>{
    crate::sparse_stream_roster::h21_owner_lanes_respect_the_existing_role_budget()?;
    let (owned,marker)=original_n0_u0_context()?;
    let context=owned.context()?;
    let (r,_)=super::h21_atomic_seven::frozen_role1_u0_prefix(&context,&marker[136..])?;
    crate::sparse_stream_roster::h21_owner_batches::check_h21_owner_batches(
        &context.roster,&r,&external("NIPOPOW_V2_ROLE1_N0_WITNESS")?)
}

#[cfg(all(windows,feature="h21-snapshot-n0"))]
#[test]
#[ignore="check fully covered N0 U0 receipts against the original initial sumcheck and derive U1 challenge"]
fn check_real_n0_role1_u0_set()->Result<(),String>{
    let (owned,marker)=original_n0_u0_context()?;let context=owned.context()?;
    let (r,mut transcript)=super::h21_atomic_seven::frozen_role1_u0_prefix(&context,&marker[136..])?;
    crate::sparse_stream_roster::h21_u0::qualify_inventory(&owned.public_bytes,&marker,&r,&mut transcript)
}

#[cfg(all(windows,feature="h21-snapshot-n0"))]
#[test]
#[ignore="real N0 statement, F60 commitment and sparse held original witness rows"]
fn role1_weighted_messages_on_real_n0_rows()->Result<(),String>{
    let x=bounded_file(&external("NIPOPOW_V2_INPUTS")?.join("statement.x"),MAX_X)?;
    let marker=bounded_file(&external("NIPOPOW_V2_ROLE1_N0_MARKER")?,520)?;
    if format!("{:x}",Blake2b::<U32>::digest(&x))!="43f5da4d4fe06df86b39bdf9c0bf3805be3783e7f8246a5a2ed09e4fe62ff44d" ||
        format!("{:x}",Blake2b::<U32>::digest(&marker))!="56096f2fcb41f665a86bdc8787e58d9bf7bedc94418783fe0f7aa7e685cd2feb" ||
        marker.len()!=520 || &marker[..8]!=b"R4GKR001" {return Err("wrong original N0 statement or marker".into());}
    let (fields,sampled,a_b)=Outputs::read_prefix(&x)?;
    let (root,total,tip,time,maps)=relation::read_statement_fields(fields)?;
    let public=relation::build_full_context(&x,root,total,tip,time,maps,sampled,a_b)?;
    if &Blake2b::<U32>::digest(&public.public_bytes)[..]!=&marker[8..40] ||
        &Blake2b::<U32>::digest(include_bytes!("../fixtures/verifier-keys-v1/log41.vk"))[..]!=&marker[40..72] {
        return Err("N0 proof session or key changed".into());
    }
    let context=public.context()?;
    let r=super::h21_atomic_seven::frozen_role1_output_point_for_measurement(&context,&marker[136..])?;
    crate::sparse_stream_roster::measure_weighted_n0_messages(&context.roster,&r,
        &external("NIPOPOW_V2_ROLE1_N0_WITNESS")?)
}

#[path = "full_native_audit.rs"]
mod native_audit;
#[path = "full_tail.rs"]
mod full_tail;
#[path = "full_cold_client.rs"]
mod full_cold_client;

const PROFILE: &[u8] = b"Ergo/mainnet/NiPoPoW-V2/r4/public-profile/1\0native=8995ff243b140e7fe716bd3204423dd35690c2e4;tree=work-profile-v1;struct=GKR-Dory-BN254-ee2f29a812da5ea75d28333792d1f5c83af876848e90113bb6fe68fc783affe6;mode=sampled-plus-tail-summary;work=zero-genesis-U224BE;max_d=2^64;raw_max=514;k0=64;L=1024;s=240;beta=7/10;samples=466;audit=sha512-r4-1;attempts=2;native_and_audit_Q=2^80+1;a=4/15;h=(3/4)(1-2^-32);b=16/15;nu=1/20;omega=16;b1=8319;exp_theta=13/10;sample_m=43410,23155,4995;exact_m=17867,9548,2090;native_tail_versions=2..4;compare=max-work-then-canonical";
const WINDOW: usize = 1088;
const CERTIFICATE_MAGIC: &[u8; 8] = b"NPV2AUD2";
const MAX_X: usize = 32 * 1024;
const MAX_INNER: usize = 192 * 1024;
const MAX_DISCLOSURES: usize = (WINDOW + 3) * (4 + MAX_OPENING_BYTES);
const MAX_STRUCTURE: usize = MAX_INNER + MAX_DISCLOSURES + 32;
const MAX_AUDIT: usize = 12 + 39_144 * (2 + MAX_OPENING_BYTES);
const MAX_CERT: usize = 20 + MAX_X + MAX_STRUCTURE + MAX_AUDIT;
type Word = [u8; 28];

fn check_legacy_allowance(v1_work: Word, history_exp: usize, bootstrap_exp: usize) -> Result<(), String> {
    if history_exp > 64 || bootstrap_exp > 64 { return Err("legacy cap exponent outside grid".into()); }
    // A cold client carries the prefix ending at B into exact continuation.
    // A larger cap reached later on the sampled branch cannot fund that prefix.
    let limit = BigUint::from(8319u32) << history_exp.min(bootstrap_exp);
    if BigUint::from_bytes_be(&v1_work) > limit { return Err("legacy allowance exceeded".into()); }
    Ok(())
}

#[test]
fn v1_allowance_is_admitted_at_both_proven_caps() {
    let equality = fixed_uint(&BigUint::from(8319u32)).unwrap();
    let excess = fixed_uint(&BigUint::from(8320u32)).unwrap();
    assert!(check_legacy_allowance(equality, 1, 0).is_ok());
    assert!(check_legacy_allowance(excess, 1, 0).is_err());
    assert!(check_legacy_allowance(excess, 0, 1).is_err());
    assert!(check_legacy_allowance(excess, 1, 1).is_ok());
}

fn frame(out: &mut Vec<u8>, bytes: &[u8]) -> Result<(), String> {
    let n = u32::try_from(bytes.len()).map_err(|_| "field exceeds U32")?;
    out.extend(n.to_be_bytes());
    out.extend(bytes);
    Ok(())
}

fn take<'a>(input: &mut &'a [u8], n: usize) -> Result<&'a [u8], String> {
    let (bytes, remaining) = input.split_at_checked(n).ok_or("truncated certificate")?;
    *input = remaining;
    Ok(bytes)
}
fn field<'a>(input: &mut &'a [u8], limit: usize) -> Result<&'a [u8], String> {
    let n = u32::from_be_bytes(take(input, 4)?.try_into().unwrap()) as usize;
    if n > limit { return Err("field exceeds profile bound".into()); }
    take(input, n)
}
fn require_empty(bytes: &[u8]) -> Result<(), String> {
    if bytes.is_empty() { Ok(()) } else { Err("trailing certificate bytes".into()) }
}
fn fixed_uint<const N: usize>(v: &BigUint) -> Result<[u8; N], String> {
    let bytes = v.to_bytes_be();
    let mut result = [0; N];
    let at = N.checked_sub(bytes.len()).ok_or("work exceeds width")?;
    result[at..].copy_from_slice(&bytes);
    Ok(result)
}

struct Outputs {
    fields: Vec<u8>, root: [u8; 32], total: Word, tip: [u8; 32], tip_time: i64,
    maps: [PublicMapParameters; 2], sampled: Word, a_b: [u8; 29],
    following: Word, w_b: Word, t1: Word, t2: Word, header: Vec<u8>, window: Vec<(u32,i64)>,
}

fn positions() -> impl Iterator<Item = usize> {
    let h = crate::h21_snapshot::H;
    [417_791, 845_759].into_iter().chain(h + 1 - WINDOW..=h)
        .chain(std::iter::once(crate::h21_snapshot::F))
}

impl Outputs {
    fn encode(&self) -> Result<Vec<u8>, String> {
        let mut x = Vec::new();
        frame(&mut x, PROFILE)?;
        x.extend((crate::h21_snapshot::H as u32).to_be_bytes());
        x.extend((crate::h21_snapshot::F as u32).to_be_bytes());
        frame(&mut x, &self.fields)?;
        x.extend(self.sampled);
        x.extend(self.a_b);
        for work in [self.following, self.w_b, self.t1, self.t2] { x.extend(work); }
        frame(&mut x, &self.header)?;
        for (bits,time) in &self.window { x.extend(bits.to_be_bytes()); x.extend(time.to_be_bytes()); }
        Ok(x)
    }
    fn read_prefix(x: &[u8]) -> Result<(&[u8], Word, [u8; 29]), String> {
        let mut input = x;
        if x.len() > MAX_X || field(&mut input, PROFILE.len())? != PROFILE
            || take(&mut input, 4)? != (crate::h21_snapshot::H as u32).to_be_bytes()
            || take(&mut input, 4)? != (crate::h21_snapshot::F as u32).to_be_bytes() {
            return Err("unexpected V2 profile or query".into());
        }
        let fields = field(&mut input, 8192)?;
        Ok((fields, take(&mut input,28)?.try_into().unwrap(), take(&mut input,29)?.try_into().unwrap()))
    }
    fn from_records(fields: &[u8], sampled: Word, a_b: [u8; 29], mut records: &[u8]) -> Result<Self, String> {
        let (root,total,tip,tip_time,maps) = relation::read_statement_fields(fields)?;
        let n = crate::h21_snapshot::N;
        let h = crate::h21_snapshot::H;
        let f = crate::h21_snapshot::F;
        if h.checked_add(63) != Some(f) || f >= n || maps[0].terminal != n || maps[1].terminal != h
            || maps.iter().any(|m| m.exponent > 64) || BigUint::from_bytes_be(&total).bits() > 95
            || sampled > total || a_b[0] > 1 { return Err("public work/profile bounds".into()); }
        let ctx = NativeWorkMembershipContext::new(n,root,total).map_err(|e| e.to_string())?;
        let mut outputs = Self {fields:fields.to_vec(),root,total,tip,tip_time,maps,sampled,a_b,
            following:[0;28],w_b:[0;28],t1:[0;28],t2:[0;28],header:Vec::new(),window:Vec::with_capacity(WINDOW)};
        for expected in positions() {
            let enc = field(&mut records, MAX_OPENING_BYTES)?;
            let lower: Word = enc.get(12..40).ok_or("short public opening")?.try_into().unwrap();
            let member = ctx.verify_encoded(lower, enc).map_err(|e|e.to_string())?;
            if member.height() as usize != expected { return Err("public opening height/order".into()); }
            let upper = member.interval_be28().1;
            match expected {
                417_791 => outputs.t1 = upper,
                845_759 => outputs.t2 = upper,
                i if i == f => {
                    if upper >= total { return Err("empty following suffix".into()); }
                    outputs.following = fixed_uint(&(BigUint::from_bytes_be(&total)-BigUint::from_bytes_be(&upper)))?;
                }
                _ => {
                    let header = member.header();
                    outputs.window.push((header.n_bits, header.timestamp));
                    if expected == h { outputs.w_b = upper; outputs.header = member.raw().to_vec(); }
                }
            }
        }
        require_empty(records)?;
        check_legacy_allowance(outputs.t1, maps[0].exponent, maps[1].exponent)?;
        if outputs.window.len() != WINDOW || outputs.header.is_empty() || outputs.t1 > outputs.t2
            || outputs.t2 > outputs.w_b
            || BigUint::from_bytes_be(&outputs.following) < BigUint::from(4995u32) {
            return Err("context, legacy work or audit floor".into());
        }
        Ok(outputs)
    }
}

pub(super) struct VerifiedFullStructural {
    public: Outputs, x: Vec<u8>, proof: Vec<u8>,
}
impl VerifiedFullStructural {
    fn canonical_x(&self) -> &[u8] { &self.x }
    fn complete_proof(&self) -> &[u8] { &self.proof }
    fn header_count(&self) -> usize { crate::h21_snapshot::N }
    fn root(&self) -> [u8;32] { self.public.root }
    fn work(&self) -> Word { self.public.total }
    fn following_work(&self) -> Word { self.public.following }
    fn checkpoint_height(&self) -> u32 { crate::h21_snapshot::H as u32 }
    fn checkpoint_raw(&self) -> &[u8] { &self.public.header }
    fn context_nbits_times(&self) -> &[(u32,i64)] { &self.public.window }
    fn summary(&self) -> (Word,[u8;29],Word,Word) { (self.public.w_b,self.public.a_b,self.public.t1,self.public.t2) }
}

fn admit_structure(x: &[u8], proof: &[u8]) -> Result<VerifiedFullStructural,String> {
    let mut cursor = proof;
    let inner = field(&mut cursor, MAX_INNER)?;
    let records = field(&mut cursor, MAX_DISCLOSURES)?;
    require_empty(cursor)?;
    let (fields,r,a) = Outputs::read_prefix(x)?;
    let public = Outputs::from_records(fields,r,a,records)?;
    if public.encode()? != x { return Err("structural public outputs disagree with tree openings".into()); }
    let verified = relation::verify_full_structure(x,r,a,inner)?;
    if fields != verified.canonical_statement_bytes() || verified.sampled_work_bound() != r
        || verified.exact_bootstrap_bound() != a { return Err("different proven public fields".into()); }
    Ok(VerifiedFullStructural {public,x:x.to_vec(),proof:proof.to_vec()})
}

fn prepare(prefix: &NativePrefix) -> Result<(Outputs,Vec<u8>),String> {
    use crate::h21_scheduled_max_cap::{Eligible08NativeSnapshot, MaxStream, Plan as MaxPlan};
    use crate::work_tree_wiring::Descriptor;
    let n = crate::h21_snapshot::N;
    if prefix.header_count() != n { return Err("wrong snapshot for requested profile".into()); }
    let plan = WorkTreeHistoryPlan::compile(n as u64,21,prefix.root(),prefix.total_be28())?;
    let native = H21EligibleContext::new(&plan,prefix)?;
    let cut = Eligible08NativeSnapshot::new(&plan,prefix)?;
    let mut maxima = MaxStream::new(&plan,prefix,&cut)?;
    for (owner,_) in MaxPlan::eligible08().max_calendar() { maxima.push_native(native.native_owner_values_producer(),owner)?; }
    maxima.closed_native_snapshot(&plan,prefix)?;
    let mut stream = native.score_endpoint_stream(&maxima)?;
    while let Some(owner) = stream.next_owner() { stream.push_native(owner)?; }
    let [r,a] = stream.terminal_r()?;
    let tip = prefix.header(n)?;
    let fields = relation::statement_fields(prefix.root(),prefix.total_be28(),tip.id().map_err(|e|format!("{e:?}"))?,
        tip.timestamp, native.structural_map_parameters()?)?;
    let ctx = NativeWorkMembershipContext::new(n,prefix.root(),prefix.total_be28()).map_err(|e|e.to_string())?;
    let tree = Descriptor::new(n,prefix.root())?;
    let mut records = Vec::new();
    for height in positions() { frame(&mut records,&native_audit::encode_member(prefix,&tree,&ctx,height)?.0)?; }
    let outputs = Outputs::from_records(&fields,fixed_uint(&r)?,fixed_uint(&a)?,&records)?;
    Ok((outputs,records))
}

fn external(name:&str) -> Result<std::path::PathBuf,String> {
    let path = std::path::PathBuf::from(std::env::var_os(name).ok_or_else(||format!("missing {name}"))?);
    if !crate::preview_test_paths::absolute_outside_source(&path) {return Err(format!("invalid {name}"));}
    Ok(path)
}
fn publish_local(p:&Path,bytes:&[u8])->Result<(),String> {
    let mut f = OpenOptions::new().write(true).create_new(true).open(p).map_err(|e|e.to_string())?;
    f.write_all(bytes).and_then(|_|f.sync_all()).map_err(|e|e.to_string())
}
fn bounded_file(p:&Path,limit:usize)->Result<Vec<u8>,String> {
    let mut bytes=Vec::new();
    std::fs::File::open(p).map_err(|e|e.to_string())?.take(limit as u64+1)
        .read_to_end(&mut bytes).map_err(|e|e.to_string())?;
    if bytes.len()>limit{return Err("certificate input limit".into());}
    Ok(bytes)
}

#[test]
#[ignore="retained full snapshot; export exact public outputs and their authenticated paths"]
fn export_required_inputs() -> Result<(),String> {
    let out=external("NIPOPOW_V2_OUTPUT_DIR")?;
    crate::h21_native_admission_tests::with_selected_h21_prefix(|prefix|{
        let (public,records)=prepare(prefix)?;
        std::fs::create_dir(&out).map_err(|e|e.to_string())?;
        publish_local(&out.join("statement.x"),&public.encode()?)?;
        publish_local(&out.join("public-openings.bin"),&records)
    })
}

#[test]
#[ignore="complete sealed witness and measured long-run producer budget required"]
fn prove_and_export_full_certificate() -> Result<(),String> {
    let inputs=external("NIPOPOW_V2_INPUTS")?;
    let x=bounded_file(&inputs.join("statement.x"),MAX_X)?;
    let records=bounded_file(&inputs.join("public-openings.bin"),MAX_DISCLOSURES)?;
    let (fields,r,a)=Outputs::read_prefix(&x)?;
    let public=Outputs::from_records(fields,r,a,&records)?;
    if public.encode()?!=x{return Err("mismatched public input".into());}
    let original=H21StructuralDiagnostic::compile(public.root,public.total,public.tip,public.tip_time,public.maps)?;
    let source=original.open_untrusted_candidate(&external("NIPOPOW_H21_WITNESS")?,None)?;
    let budget_field=|name|std::env::var(name).map_err(|_|format!("missing {name}"))?
        .parse::<usize>().map_err(|e|e.to_string());
    let budget=sparse_stream_roster::H21Role1Budget {limit_bytes:budget_field("NIPOPOW_H21_ROLE_BUDGET_BYTES")?,
        caller_context_bytes:budget_field("NIPOPOW_H21_CONTEXT_BYTES")?, visitor_scratch_bytes:budget_field("NIPOPOW_H21_VISITOR_BYTES")?,
        unmeasured_bytes:budget_field("NIPOPOW_H21_RESERVE_BYTES")?};
    drop(original);
    let stage=external("NIPOPOW_V2_ROLE_CHECKPOINTS")?;
    let inner=relation::prove_full_structure(&x,public.root,public.total,public.tip,public.tip_time,public.maps,r,a,&source,budget,&stage)?;
    let mut structural=Vec::new();
    frame(&mut structural,&inner)?; frame(&mut structural,&records)?;
    drop(source);
    let seal=admit_structure(&x,&structural)?;
    let packet_path=external("NIPOPOW_V2_CERTIFICATE")?;
    crate::h21_native_admission_tests::with_selected_h21_prefix(|prefix|{
        let audit=native_audit::produce(&seal,prefix)?;
        native_audit::verify(&seal,&audit)?;
        let mut packet=CERTIFICATE_MAGIC.to_vec();
        frame(&mut packet,&x)?;frame(&mut packet,&structural)?;frame(&mut packet,&audit)?;
        publish_local(&packet_path,&packet)
    })
}

fn split_certificate(bytes:&[u8])->Result<(&[u8],&[u8],&[u8]),String>{
    if bytes.len()>MAX_CERT{return Err("certificate size".into());}
    let mut input=bytes;
    if take(&mut input,8)?!=CERTIFICATE_MAGIC{return Err("certificate magic".into());}
    let x=field(&mut input,MAX_X)?;let proof=field(&mut input,MAX_STRUCTURE)?;let audit=field(&mut input,MAX_AUDIT)?;
    require_empty(input)?;Ok((x,proof,audit))
}

#[test]
fn era_certificate_requires_revised_envelope() {
    assert_eq!(CERTIFICATE_MAGIC,b"NPV2AUD2");
    assert_eq!(split_certificate(b"NPV2AUD1").unwrap_err(),"certificate magic");
    assert_eq!(split_certificate(CERTIFICATE_MAGIC).unwrap_err(),"truncated certificate");
}

#[cfg(all(windows,feature = "h21-snapshot-n0"))]
#[test]
#[ignore="read-only N0 public statement and the sealed F60 session marker"]
fn era_reuses_real_n0_checkpoint_prefix() -> Result<(),String> {
    let x=bounded_file(&external("NIPOPOW_V2_INPUTS")?.join("statement.x"),MAX_X)?;
    let marker=bounded_file(&external("NIPOPOW_V2_ERA_MARKER")?,520)?;
    if format!("{:x}",Blake2b::<U32>::digest(&x)) != "43f5da4d4fe06df86b39bdf9c0bf3805be3783e7f8246a5a2ed09e4fe62ff44d" ||
       format!("{:x}",Blake2b::<U32>::digest(&marker)) != "56096f2fcb41f665a86bdc8787e58d9bf7bedc94418783fe0f7aa7e685cd2feb" {
        return Err("wrong historical N0 compatibility fixture".into());
    }
    let (fields,sampled,a_b)=Outputs::read_prefix(&x)?;
    let (root,total,tip,time,maps)=relation::read_statement_fields(fields)?;
    let owned=relation::build_full_context(&x,root,total,tip,time,maps,sampled,a_b)?;
    relation::compare_f60_checkpoint_prefixes(&owned,&marker)
}

#[test]
#[ignore="cold process, no witness or native prefix input"]
fn verify_full_certificate_from_bytes() -> Result<(),String> {
    let bytes=bounded_file(&external("NIPOPOW_V2_CERTIFICATE")?,MAX_CERT)?;
    let (x,proof,audit)=split_certificate(&bytes)?;
    let seal=admit_structure(x,proof)?;
    let checked=native_audit::verify(&seal,audit)?;
    println!("Verified bootstrap at height {}",checked.history().checkpoint_height());
    Ok(())
}

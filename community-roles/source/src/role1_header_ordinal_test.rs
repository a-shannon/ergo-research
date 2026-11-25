use super::*;
use crate::packed_owner_assembly::h21_structural_roster::{Family, H21StructuralRoster, PublicMapParameters};
use crate::sparse::Term;
use std::{collections::BTreeMap, ffi::c_void, hint::black_box, time::Instant};

const SLOTS: usize = 1 << 21;
const PASSES: u64 = 44;
const LIMIT_NS: f64 = 14.0*86400.0*1e9 / (44.0*SLOTS as f64);
const SCALAR_GROUP: usize = 4;
const REPEATS: usize = 3;

#[repr(C)]
#[derive(Clone,Copy,Default)]
struct FileTime { lo: u32, hi: u32 }
impl FileTime {fn ticks(self)->u64 {u64::from(self.hi)<<32 | u64::from(self.lo)}}
#[link(name="kernel32")]
extern "system" {
    fn GetCurrentThread()->*mut c_void;
    fn GetThreadTimes(t:*mut c_void,c:*mut FileTime,e:*mut FileTime,k:*mut FileTime,u:*mut FileTime)->i32;
}
fn cpu()->Result<u64,String>{
    let [mut c,mut e,mut k,mut u]=[FileTime::default();4];
    if unsafe {GetThreadTimes(GetCurrentThread(),&mut c,&mut e,&mut k,&mut u)}==0 {
        return Err(std::io::Error::last_os_error().to_string());
    }
    Ok(100*(k.ticks()+u.ticks()))
}

#[derive(Clone,Copy,PartialEq,Eq,Debug)]
enum Axis { Header, Left, Right }
impl Axis {fn name(self)->&'static str {match self {Self::Header=>"header",Self::Left=>"left",Self::Right=>"right"}}}

struct Engine<'a> {plan:&'a WorkTreeHistoryPlan,roster:H21StructuralRoster<'a>}
fn engine(plan:&WorkTreeHistoryPlan,maps:[PublicMapParameters;2],scores:[[u8;29];2])->Result<Engine<'_>,String>{
    let mut roster=H21StructuralRoster::from_public(plan,maps)?;
    roster.bind_terminal_scores(scores);
    Ok(Engine{plan,roster})
}
impl Engine<'_>{
    fn visit(&self, axis:Axis, owner:usize, mut sink:impl FnMut(Family,Term)->Result<(),String>)->Result<usize,String>{
        match axis {
            Axis::Header=>Ok(self.plan.visit_slot_terms(owner as u64,|term|sink(Family::Header,term))?.emitted),
            _=>Ok(self.roster.visit_endpoint(axis==Axis::Left,owner,|family,term|sink(family,term))?.terms),
        }
    }
}

fn compare(a:&Engine<'_>,b:&Engine<'_>,axis:Axis,owner:usize)->Result<usize,String>{
    let mut expected=Vec::with_capacity(450_000);
    let before=a.visit(axis,owner,|f,t|{
        // A term is its row, both addresses and all four canonical Fr values.
        expected.push((f,t,crate::c425_span_census::current_source_ordinal()));
        Ok(())
    })?;
    if expected.len()!=before{return Err("reference census differs".into());}
    let mut index=0;
    let after=b.visit(axis,owner,|f,t|{
        let (family,term,ordinal)=expected.get(index).ok_or("surplus ordinal term")?;
        if *family!=f || *term!=t || *ordinal!=crate::c425_span_census::current_source_ordinal(){
            return Err(format!("ordered {axis:?} difference at owner {owner} term {index}"));
        }
        index+=1;Ok(())
    })?;
    if before!=after || index!=before{return Err("missing ordinal term".into());}
    Ok(before)
}

fn timed(e:&Engine<'_>,axis:Axis,owner:usize,n:usize,census:usize)->Result<(u64,u64),String>{
    let begin=cpu()?;let wall=Instant::now();
    for _ in 0..n {
        let rows=e.visit(axis,black_box(owner),|_,t|{black_box(&t);Ok(())})?;
        if rows!=census{return Err("timed census differs".into());}
    }
    Ok((cpu()?.checked_sub(begin).ok_or("thread clock")?,wall.elapsed().as_nanos() as u64))
}

fn class(owner:usize)->&'static str {
    if owner>=crate::h21_snapshot::N{return "padding";}
    if owner==0{return "genesis";}
    if owner==1{return "initial";}
    if matches!(owner,417791|417792){return "reset";}
    if owner<844672 && owner%1024==0 {
        return match owner/1024 {1=>"singleton",2=>"M1",3=>"M2",4=>"M3",5=>"M4",6=>"M5",
            7=>"M6",8=>"M7",_=>"mature_legacy"};
    }
    if owner>=844672 && owner%128==0{return "mature_eip";}
    if owner+1<=417791{"carry_v1"}else if owner+1<844673{"carry_v2_legacy"}else{"carry_v2_eip"}
}

#[test]
#[ignore="real archival N0 byte-preserving HEADER and ordinary inverse endpoint A/B"]
fn real_n0_ordered_header_and_endpoints()->Result<(),String>{
    if std::env::var("RAYON_NUM_THREADS").as_deref()!=Ok("1") ||
        std::env::var("RUST_TEST_THREADS").as_deref()!=Ok("1"){return Err("one worker required".into());}
    let begin=Instant::now();
    let x=bounded_file(&external("NIPOPOW_V2_INPUTS")?.join("statement.x"),MAX_X)?;
    if x.len()!=14_246 || format!("{:x}",Blake2b::<U32>::digest(&x))!="43f5da4d4fe06df86b39bdf9c0bf3805be3783e7f8246a5a2ed09e4fe62ff44d"{
        return Err("N0 statement hash".into());
    }
    let (fields,sampled,exact)=Outputs::read_prefix(&x)?;
    let (root,total,_,_,maps)=relation::read_statement_fields(fields)?;
    let n=crate::h21_snapshot::N;
    let mut old_plan=WorkTreeHistoryPlan::compile(n as u64,21,root,total)?;
    let new_plan=WorkTreeHistoryPlan::compile(n as u64,21,root,total)?;
    old_plan.use_uncached_header_for_measurement();
    let mut sampled225=[0;29];sampled225[1..].copy_from_slice(&sampled);
    let old=engine(&old_plan,maps,[sampled225,exact])?;
    let new=engine(&new_plan,maps,[sampled225,exact])?;
    let mut counts=BTreeMap::new();
    for owner in 0..SLOTS{*counts.entry(class(owner)).or_insert(0usize)+=1;}
    if counts.len()!=17 || counts["mature_legacy"]!=815 || counts["mature_eip"]!=7617{return Err("historical class census".into());}
    let cases=[0,1,2,1024,2048,3072,4096,5120,6144,7168,8192,9216,300_101,417_791,417_792,
        417_793,600_023,843_776,844_672,1_541_249,n-1,n,SLOTS-1];
    let axes_owners=[2,2048,3072,9216,417_791,600_023,844_670,844_672,845_759,
        845_887,1_541_249,crate::h21_snapshot::H-1,crate::h21_snapshot::F-1,n-1,n];
    let mut rows=Vec::new();
    let setup_ns=begin.elapsed().as_nanos() as u64;
    for axis in [Axis::Header,Axis::Left,Axis::Right] {
        let sample=if axis==Axis::Header{&cases[..]}else{&axes_owners[..]};
        for &owner in sample {
            if axis==Axis::Right && owner==0{return Err("refusing unbounded global-zero endpoint".into());}
            let count=compare(&old,&new,axis,owner)?;
            let mut observations=Vec::new();
            // Outside measured blocks, pilot each implementation so the Windows CPU
            // clock covers several ticks. Alternate the order to distribute drift.
            let loops=|e:&Engine<'_>|->Result<usize,String>{
                let (_,w)=timed(e,axis,owner,1,count)?;
                Ok((160_000_000u64.div_ceil(w.max(1)) as usize).clamp(2,64))
            };
            let repeat=[loops(&old)?,loops(&new)?];
            for rep in 0..REPEATS {
                for version in if (rep+owner)%2==0{[0,1]}else{[1,0]} {
                    let e=if version==0{&old}else{&new};
                    let iterations=repeat[version];
                    let (c,w)=timed(e,axis,owner,iterations,count)?;
                    if c==0 || w==0{return Err("insufficient timer range".into());}
                    observations.push(serde_json::json!({"mode":if version==0{"reference"}else{"ordinal"},
                        "iterations":iterations,"thread_cpu_ns":c,"wall_ns":w}));
                }
            }
            rows.push(serde_json::json!({"axis":axis.name(),"owner":owner,"class":class(owner),
                "terms_compared":count,"full_order_and_c425_equal":true,"observations":observations}));
        }
    }
    println!("ROLE1_HEADER_ORDINAL_AB {}",serde_json::json!({"result":"POSITIVE_ORDERED_DIFFERENTIAL",
        "parent_manifest":"33D9A779C667297CB04387FEE3FF12DCABBE2F34DFF8EAFF4522072A1C8C6048",
        "slots":SLOTS,"passes":PASSES,"budget_ns_per_visit":LIMIT_NS,"setup_ns":setup_ns,
        "class_counts":counts,"samples":rows,"field_coefficients_per_gate":SCALAR_GROUP,
        "global_right_zero_enumerated":false,"global_zero_score_slack_family_owner_pairs_per_right_pass":4*SLOTS,
        "scope":"Exact ordered relation differential and serial owner timings. No witness reads, sumcheck accumulation, packed lookup, line, PCS or complete certificate; endpoint population classes not exhaustively timed."}));
    Ok(())
}

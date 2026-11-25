//! Off-chain production cache for the genuine historical N0 role-1 U0 message.
//! Its bytes are local producer input. The public GKR and PCS verifier is unchanged.
use super::*;
use ark_serialize::{CanonicalDeserialize,CanonicalSerialize};
use blake2::{Blake2b,Digest,digest::consts::U32};
use crate::packed_owner_assembly::h21_structural_roster::{Family,H21StructuralRoster};
use std::{collections::BTreeSet,fs,io::{Read,Seek,SeekFrom,Write},path::{Path,PathBuf},time::{Instant,SystemTime,UNIX_EPOCH}};

const SLOTS:usize=1<<21;
const WIDTH:usize=1<<20;
const SHARD:usize=512;
const WIRE:usize=144;
const X_SHA:&str="779b5863e53897ab377ceafd93d2b024027f8ee072f43431866957d0e7039a98";
const ID_B2:&str="cc066f5b3d742ddf9d4d20f228eeba7535d0a5ed39079ba6e119c88178860b90";
const KEY_SHA:&str="edf4b5c518f2701c9b11aaaadb454ae8ef31616ba9d1c0a4476bd755ffc29bd0";
const C_SHA:&str="e6fe4e4ec2337a2261d19b70aace5b3b225537a5fe4bd592117db989fcf99a59";
const WITNESS_B2:&str="de2057b4549f240160e811b7cf09c22e875b03916d6276b0de5998dabcf5f8f4644c7924c0245d621bb50fb16ac45e973a3a69b0ae5ed64e5251c05a5d0682ac";
const KERNEL:&str="fcee1a7afe1d675e6b48732a944f5f9ccf5ca426f2810b8fe68950ac8d67ca43";
const EXPECTED_BINDING:&str="294a4303eac41055d6a6de444b1e42d29bd8d6895f4072c629c16647be5b4710";

fn hex(b:&[u8])->String{b.iter().map(|v|format!("{v:02x}")).collect()}
fn sha(b:&[u8])->Result<[u8;32],String>{crate::native_prefix_auth_plan::role0_sha256(b)}
fn hash_text(b:&[u8])->Result<String,String>{Ok(hex(&sha(b)?))}
fn digest_text(value:&str)->bool{value.len()==64 && value.bytes().all(|b|b.is_ascii_digit() || (b'a'..=b'f').contains(&b))}
fn file_bytes(path:&Path,cap:usize)->Result<Vec<u8>,String>{
    let n=usize::try_from(fs::symlink_metadata(path).map_err(|e|e.to_string())?.len()).map_err(|_|"file size overflow")?;
    if n>cap{return Err("U0 input too large".into());}
    let mut f=crate::packed::open_untrusted_held_regular(path,n as u64)?;
    let mut bytes=vec![0;n];f.read_exact(&mut bytes).map_err(|e|e.to_string())?;
    Ok(bytes)
}
fn path_var(name:&str)->Result<PathBuf,String>{
    let path=PathBuf::from(std::env::var_os(name).ok_or_else(||format!("missing {name}"))?);
    if !crate::preview_test_paths::absolute_outside_source(&path){return Err(format!("unsafe {name}"));}
    Ok(path)
}
fn decimal(s:&str)->Result<usize,String>{
    let n=s.parse::<usize>().map_err(|e|e.to_string())?;
    if n.to_string()!=s{return Err("noncanonical decimal owner".into());}Ok(n)
}
fn number_var(name:&str)->Result<usize,String>{decimal(&std::env::var(name).map_err(|e|e.to_string())?)}
fn encoded(values:&[Fr])->Result<Vec<u8>,String>{
    let mut out=Vec::with_capacity(32*values.len());
    for f in values{f.serialize_compressed(&mut out).map_err(|e|e.to_string())?;}
    Ok(out)
}
fn name(lo:usize,hi:usize)->String{format!("u0-{lo:07}-{hi:07}.bin")}
fn range(lo:usize,hi:usize)->Result<(),String>{
    if lo>=hi || hi>SLOTS || lo%SHARD!=0 || hi%SHARD!=0{return Err("invalid aligned U0 owner interval".into());}
    Ok(())
}
fn origin(id:&[u8],key:&[u8],c:&[u8],witness:&[u8;64])->Result<(),String>{
    if crate::h21_snapshot::N!=1_819_648 || hex(&Blake2b::<U32>::digest(id))!=ID_B2 ||
        hash_text(key)?!=KEY_SHA || hash_text(c)?!=C_SHA || hex(witness)!=WITNESS_B2{
        return Err("U0 cache belongs to another historical witness, statement, key or commitment".into());
    }
    Ok(())
}
fn binding(r:&[Fr])->Result<[u8;32],String>{
    if r.len()!=40{return Err("wrong U0 output-point length".into());}
    let r_digest=hash_text(&encoded(r)?)?;
    let text=format!("NIPOPOW/H21/ROLE1/U0/1\nN0\n1819648,21,20,19,40\n{KERNEL}\n{X_SHA}\n{ID_B2}\n{KEY_SHA}\n{C_SHA}\n{WITNESS_B2}\n{r_digest}\n");
    let id=sha(text.as_bytes())?;
    if hex(&id)!=EXPECTED_BINDING{return Err("unexpected genuine N0 role1 output point".into());}
    Ok(id)
}

fn wire(id:&[u8;32],lo:usize,hi:usize,coefficients:&[Fr;3])->Result<Vec<u8>,String>{
    range(lo,hi)?;
    if hi-lo!=SHARD{return Err("wrong U0 shard geometry".into());}
    let mut bytes=b"R1U0SH01".to_vec();bytes.extend_from_slice(id);
    bytes.extend_from_slice(&(lo as u32).to_le_bytes());bytes.extend_from_slice(&(hi as u32).to_le_bytes());
    bytes.extend_from_slice(&encoded(coefficients)?);
    if bytes.len()!=WIRE{return Err("U0 canonical encoding extent".into());}Ok(bytes)
}
fn parse(bytes:&[u8],id:&[u8;32],lo:usize,hi:usize)->Result<[Fr;3],String>{
    if bytes.len()!=WIRE || &bytes[..8]!=b"R1U0SH01" || &bytes[8..40]!=id ||
        bytes[40..44]!=(lo as u32).to_le_bytes() || bytes[44..48]!=(hi as u32).to_le_bytes(){
        return Err("foreign, incomplete or reordered U0 shard".into());
    }
    let mut out=[Fr::zero();3];let mut values=&bytes[48..];
    for v in &mut out{*v=Fr::deserialize_compressed(&mut values).map_err(|e|e.to_string())?;}
    if !values.is_empty() || wire(id,lo,hi,&out)?!=bytes{return Err("noncanonical U0 field element".into());}
    Ok(out)
}
fn plus(a:&mut [Fr;3],b:[Fr;3]){for (to,n) in a.iter_mut().zip(b){*to+=n;}}

fn inventory_record(line:&str,lo:usize)->Result<(&str,&str),String>{
    let mut fields=line.split('\t');
    let first=fields.next().ok_or("missing interval start")?;
    let last=fields.next().ok_or("missing interval end")?;
    let shard=fields.next().ok_or("missing shard SHA256")?;
    let receipt=fields.next().ok_or("missing source receipt")?;
    if fields.next().is_some() || decimal(first)?!=lo || decimal(last)?!=lo+SHARD ||
        !digest_text(shard) || !digest_text(receipt){return Err("U0 inventory interval or SHA256".into());}
    Ok((shard,receipt))
}

pub(crate) struct Import{path:PathBuf,pin:String}
impl Import{
    pub(crate) fn from_env(id:&[u8],key:&[u8],c:&[u8],witness:&[u8;64])->Result<Option<Self>,String>{
        let path=std::env::var_os("NIPOPOW_V2_ROLE1_U0_SET");
        let hash=std::env::var_os("NIPOPOW_V2_ROLE1_U0_SET_SHA256");
        if path.is_none() && hash.is_none(){return Ok(None);}
        let path=path_var("NIPOPOW_V2_ROLE1_U0_SET")?;
        let pin=hash.and_then(|h|h.into_string().ok()).ok_or("missing U0 set SHA256")?;
        if !digest_text(&pin) || path.file_name().and_then(|n|n.to_str())!=Some("u0-set.tsv"){
            return Err("invalid U0 set path or expected SHA256".into());
        }
        origin(id,key,c,witness)?;
        Ok(Some(Self{path,pin}))
    }
    pub(crate) fn load(&self,r:&[Fr])->Result<[Fr;3],String>{
        let id=binding(r)?;let dir=self.path.parent().ok_or("missing inventory parent")?;
        crate::packed::check_stage_directory(dir)?;
        let receipt_dir=dir.join("receipts");crate::packed::check_stage_directory(&receipt_dir)?;
        let data=file_bytes(&self.path,1<<20)?;
        if hash_text(&data)?!=self.pin || !data.is_ascii() || data.contains(&b'\r') || !data.ends_with(b"\n"){
            return Err("U0 inventory SHA256 or framing".into());
        }
        let text=std::str::from_utf8(&data).map_err(|e|e.to_string())?;
        let mut lines=text.split_terminator('\n');
        if lines.next()!=Some(format!("R1U0SET1\t{}\t{SLOTS}\t{SHARD}",hex(&id)).as_str()){
            return Err("U0 inventory binding or geometry".into());
        }
        let mut total=[Fr::zero();3];let mut receipts=BTreeSet::new();
        for lo in (0..SLOTS).step_by(SHARD){
            let hi=lo+SHARD;
            let (shard,receipt)=inventory_record(lines.next().ok_or("gap in U0 inventory")?,lo)?;
            if receipts.insert(receipt) {
                let bytes=file_bytes(&receipt_dir.join(format!("{receipt}.json")),4<<20)?;
                if hash_text(&bytes)?!=receipt{return Err("U0 producer receipt differs".into());}
            }
            let bytes=file_bytes(&dir.join(name(lo,hi)),WIRE)?;
            if hash_text(&bytes)?!=shard{return Err("U0 shard SHA256 differs from sealed input".into());}
            plus(&mut total,parse(&bytes,&id,lo,hi)?);
        }
        if lines.next().is_some(){return Err("surplus U0 interval".into());}
        println!("ROLE1_U0_IMPORTED {}",serde_json::json!({"set_sha256":self.pin,"binding_sha256":hex(&id),
            "owners":SLOTS,"shards":SLOTS/SHARD,"source_receipts":receipts.len(),"coefficients_le_hex":hex(&encoded(&total)?)}));
        Ok(total)
    }
}

pub(super) fn emit(roster:&H21StructuralRoster<'_>,left:bool,owner:usize,
    sink:&mut dyn FnMut(EdgeTerm)->Result<(),String>)->Result<(),String>{
    roster.role1_complement(left,owner,|_:Family,t:Term|{
        let (slot,local)=h21_role1_edge_metadata(t.row)?;
        if global_edge_row(slot,local,21,19,0,&[19])?!=t.row{return Err("U0 physical edge canonical row".into());}
        sink(EdgeTerm{source_slot:slot,family_row:local,term:t})
    })?;Ok(())
}

pub(crate) fn produce(roster:&H21StructuralRoster<'_>,r:&[Fr],id:&[u8],key:&[u8],marker:&[u8],file:&Path)->Result<(),String>{
    if marker.len()!=520 || &marker[..8]!=b"R4GKR001" || marker[8..40]!=Blake2b::<U32>::digest(id)[..] ||
        marker[40..72]!=Blake2b::<U32>::digest(key)[..]{return Err("different U0 marker".into());}
    origin(id,key,&marker[136..],marker[72..136].try_into().unwrap())?;
    let identity=binding(r)?;let binding_hex=hex(&identity);
    let lo=number_var("NIPOPOW_V2_ROLE1_U0_START")?;let hi=number_var("NIPOPOW_V2_ROLE1_U0_END")?;
    range(lo,hi)?;
    if number_var("NIPOPOW_V2_ROLE1_U0_SHARD_OWNERS")?!=SHARD{return Err("unapproved U0 shard size".into());}
    let output=path_var("NIPOPOW_V2_ROLE1_U0_DIR")?;crate::packed::check_stage_directory(&output)?;
    let dir=fs::canonicalize(output).map_err(|e|e.to_string())?;
    let original=fs::canonicalize(file.parent().ok_or("missing original witness root")?).map_err(|e|e.to_string())?;
    if dir.starts_with(&original) || original.starts_with(&dir){return Err("U0 stage overlaps original witness directory".into());}
    let lock=dir.parent().ok_or("missing dedicated U0 attempt directory")?.join("u0-shard-writer.lock");
    let _owner=crate::packed::lock_stage_file(&lock,!lock.exists())?;
    let mut witness=crate::packed::open_untrusted_held_regular(file,1<<38)?;
    let mut loads=0u64;
    let mut input=h21_role1_input(|owner|{
        if owner>=SLOTS{return Err("invalid U0 witness owner".into());}
        let mut row=vec![0u8;WIDTH/8];
        witness.seek(SeekFrom::Start((owner*(WIDTH/8)) as u64)).map_err(|e|e.to_string())?;
        witness.read_exact(&mut row).map_err(|e|e.to_string())?;
        loads+=1;Ok(row)
    })?;
    let prep=Instant::now();
    let table=h21_weighted_header::Header::new(roster,r)?;let round=table.round(&[],None)?;
    let projection=EdgeFullStats::default().plan(WIDTH,&[],true)?;
    let lookup=EqWeightLookup::new(r);let weight=|edge:&EdgeTerm|Ok(lookup.at(edge.term.row));
    let prepare_ns=prep.elapsed().as_nanos() as u64;
    let stamp=SystemTime::now().duration_since(UNIX_EPOCH).map_err(|e|e.to_string())?.as_nanos();
    let mut range_sum=[Fr::zero();3];let mut done=0usize;
    for begin in (lo..hi).step_by(SHARD){
        let timer=Instant::now();let end=begin+SHARD;let mut coeff=[Fr::zero();3];let mut physical=0u64;
        for owner in begin..end{
            let mut visit=|side,slot,s:&mut dyn FnMut(EdgeTerm)->Result<(),String>|emit(roster,side,slot,s);
            // The memory strategy needs this owner's count only. Do not traverse any other physical endpoint here.
            let n=walk_edge_endpoint(&mut visit,true,owner,WIDTH,SLOTS,19,&[19],None,&mut |_|Ok(()))?;
            let state=edge_replay_u(&mut visit,&mut input,owner,WIDTH,SLOTS,19,&[19],n,&weight,&[],Some(&projection))?;
            plus(&mut coeff,h21_weighted_header::combine(Some(&table),Some(&round),&mut input,owner,&state,None)?);
            physical=physical.checked_add(n as u64).ok_or("U0 physical census overflow")?;
        }
        let bytes=wire(&identity,begin,end,&coeff)?;let final_path=dir.join(name(begin,end));
        let exists=final_path.try_exists().map_err(|e|e.to_string())?;
        if !exists{
            let tmp=dir.join(format!("{}.{}.{stamp}.partial",name(begin,end),std::process::id()));
            drop(crate::packed::create_blob(&tmp,&bytes)?);
            crate::packed::publish_noreplace(&tmp,&final_path)?;
        }
        // An existing file in the requested interval has NOT been trusted: the native source above was recomputed.
        if file_bytes(&final_path,WIRE)?!=bytes{return Err("different sealed U0 shard already exists".into());}
        let digest=hash_text(&bytes)?;
        plus(&mut range_sum,coeff);done+=1;
        println!("ROLE1_U0_SHARD {}",serde_json::json!({"lo":begin,"hi":end,"bytes":WIRE,"sha256":digest,
            "binding_sha256":binding_hex,"coefficients_le_hex":hex(&bytes[48..]),"reused":exists,
            "physical_terms":physical,"elapsed_ns":timer.elapsed().as_nanos() as u64}));
        std::io::stdout().flush().map_err(|e|e.to_string())?;
    }
    drop(input);
    println!("ROLE1_U0_RANGE {}",serde_json::json!({"start":lo,"end":hi,"shard_owners":SHARD,
        "binding_sha256":binding_hex,"completed_shards":done,"prepare_ns":prepare_ns,"witness_row_loads":loads,
        "coefficients_le_hex":hex(&encoded(&range_sum)?)}));
    Ok(())
}

pub(crate) fn qualify_inventory(id:&[u8],marker:&[u8],r:&[Fr],t:&mut Transcript)->Result<(),String>{
    if marker.len()!=520{return Err("wrong native U0 marker size".into());}
    let set=Import::from_env(id,include_bytes!("../fixtures/verifier-keys-v1/log41.vk"),
        &marker[136..],marker[72..136].try_into().unwrap())?.ok_or("missing complete U0 set")?;
    let poly=set.load(r)?;let mut rounds=Vec::new();let mut u=Vec::new();let mut claim=Fr::zero();
    absorb_u0(poly,&mut claim,&mut rounds,t,&mut u)?;
    println!("ROLE1_U0_COMPLETE {}",serde_json::json!({"set_sha256":set.pin,"binding_sha256":EXPECTED_BINDING,
        "owners":SLOTS,"complete_rounds":rounds.len(),"coefficients_le_hex":hex(&encoded(&poly)?),
        "next_challenge_le_hex":hex(&encoded(&u)?),"claim_after_round_le_hex":hex(&encoded(&[claim])?)}));
    Ok(())
}

#[test]
fn canonical_shard_and_split_reduction_resume_at_identical_challenge()->Result<(),String>{
    let id=[0x31;32];
    let left=[Fr::from(11u64),Fr::from(13u64),Fr::from(17u64)];
    let right=[-Fr::from(9u64),-Fr::from(20u64),-Fr::from(14u64)];
    let mut recovered=[Fr::zero();3];
    for (j,part) in [left,right].into_iter().enumerate(){
        let lo=j*SHARD;let bytes=wire(&id,lo,lo+SHARD,&part)?;
        let decoded=parse(&bytes,&id,lo,lo+SHARD)?;assert_eq!(decoded,part);plus(&mut recovered,decoded);
        assert!(parse(&bytes,&id,lo+SHARD,lo+2*SHARD).is_err());
        let mut bad=bytes.clone();bad[48..80].fill(255);assert!(parse(&bad,&id,lo,lo+SHARD).is_err());
    }
    let expected=[Fr::from(2u64),-Fr::from(7u64),Fr::from(3u64)];assert_eq!(recovered,expected);
    let line=format!("0\t512\t{KERNEL}\t{X_SHA}");assert_eq!(inventory_record(&line,0)?,(KERNEL,X_SHA));
    assert!(inventory_record(&line,512).is_err());
    for bad in [line.replacen("0\t","00\t",1),line.replacen("512","513",1),
        line.replace(KERNEL,&KERNEL.to_uppercase()),format!("{line}\t")] {
        assert!(inventory_record(&bad,0).is_err());
    }
    let mut a=Transcript::new(b"local U0 split-law test");let mut b=a.clone();
    let mut claim_old=Fr::zero();let mut claim_new=Fr::zero();
    let mut old=Vec::new();let mut new=Vec::new();let mut u=Vec::new();
    let alpha=send_round(expected.to_vec(),&mut claim_old,&mut old,&mut a).map_err(|e|e.to_string())?;
    absorb_u0(recovered,&mut claim_new,&mut new,&mut b,&mut u)?;
    assert_eq!(u,vec![alpha]);assert_eq!(old,new);assert_eq!(claim_old,claim_new);
    assert_eq!(a.challenge_scalar(b"next"),b.challenge_scalar(b"next"));
    let mut invalid=expected;invalid[2]+=Fr::one();
    assert!(absorb_u0(invalid,&mut Fr::zero(),&mut Vec::new(),&mut Transcript::new(b"initial"),
        &mut Vec::new()).is_err());
    Ok(())
}

//! Historical endpoint routing and one-role producer/atomic-consumer differential.
use super::*;
use crate::native_prefix_auth_plan::HistoricalRole4Endpoints;
use ark_ff::{BigInteger, PrimeField};
use std::{fs, io::Read, path::PathBuf};

const MEMBERS: [(&str, usize); 10] = [("statement.bin",568),("commitment.bin",384),
    ("role-0.gkr",5024),("role-1.gkr",5024),("role-2.gkr",5024),("role-3.gkr",3456),
    ("role-4.gkr",5024),("role-5.gkr",5024),("role-6.gkr",5024),("openings.bin",31581)];
const STAGES: [(&str, &str); 18] = [("admission","begin"),("admission","end"),
    ("witness","begin"),("witness","end"),("reference","begin"),("reference","end"),
    ("streaming","begin"),("streaming","end"),("equality","begin"),("equality","end"),
    ("producer_drop","end"),("export","begin"),("export","end"),
    ("consumer","begin"),("consumer","end"),("custody","begin"),("custody","end"),("complete","end")];
type Occurrence = (usize, usize, usize, [[u64; 4]; 4]);

fn key(term: &Term) -> Occurrence {
    (term.row,term.gate.left,term.gate.right,
        [term.gate.c0,term.gate.c1,term.gate.c2,term.gate.c3].map(|v|v.into_bigint().0))
}

// Bounded byte-chunk EQ scratch, never a complete input or row-domain table.
struct Weights { chunks: Vec<(usize, Vec<Fr>)> }
impl Weights {
    fn new(point: &[Fr]) -> Self {
        assert!(point.len() <= 42);
        let mut chunks = Vec::with_capacity(6);
        for (index, coordinates) in point.chunks(8).enumerate() {
            let mut table = Vec::with_capacity(1 << coordinates.len());
            for bits in 0..1usize << coordinates.len() {
                table.push(coordinates.iter().enumerate().fold(Fr::one(),|a,(b,x)|
                    a * if bits >> b & 1 == 1 {*x} else {Fr::one()-x}));
            }
            assert!(table.capacity() <= 256); chunks.push((index*8,table));
        }
        assert!(chunks.iter().map(|(_,v)|v.capacity()*32).sum::<usize>() <= 49152);
        Self { chunks }
    }
    fn at(&self, index: usize) -> Fr {
        self.chunks.iter().fold(Fr::one(),|a,(shift,table)|a*table[(index>>shift)&(table.len()-1)])
    }
}

fn channels(term: &Term, r: &Weights, u: &Weights, v: &Weights) -> [Fr;4] {
    let weight=r.at(term.row)*u.at(term.gate.left)*v.at(term.gate.right);
    [term.gate.c0,term.gate.c1,term.gate.c2,term.gate.c3].map(|c|weight*c)
}

fn fixture_statement(public: &Public) -> Vec<u8> {
    let mut bytes=public.profile().unwrap().to_vec();
    bytes.extend(crate::header_order::MAINNET_GENESIS);bytes.extend([0u8;32]);
    for value in [public.headers,4,2,22] {bytes.extend(value.to_le_bytes());}
    bytes.extend(public.root);bytes.extend(public.total);bytes.extend(public.tip);bytes.extend(public.tip_time.to_le_bytes());
    for (role,(input,row)) in [22u64,22,22,15,22,22,22].into_iter().zip([23u64,21,21,16,22,11,14]).enumerate() {
        bytes.extend((role as u64).to_le_bytes());bytes.extend((ROLES[role].len()as u64).to_le_bytes());
        bytes.extend(ROLES[role]);bytes.extend(input.to_le_bytes());bytes.extend(row.to_le_bytes());
    }
    assert_eq!(bytes.len(),568);bytes
}

fn changed_occurrence(original: &Term, fault: usize) -> Term {
    let mut term=original.clone();
    match fault {
        0=>term.row^=1,1=>term.gate.left^=1,2=>term.gate.right^=1,
        3=>term.gate.c0+=Fr::one(),4=>term.gate.c1+=Fr::one(),
        5=>term.gate.c2+=Fr::one(),6=>term.gate.c3+=Fr::one(),
        _=>unreachable!(),
    }
    term
}

fn numeric_family(occurrence: &Occurrence) -> Option<usize> {
    let row=occurrence.0;
    if (128..1usize<<21).contains(&row) {Some(0)}
    else if row>=1<<21 && ((row-(1<<21))>>17)&3==2 {Some(1)} else {None}
}

#[test]
fn endpoint_occurrences_and_coefficients() {
    transport_controls();
    for headers in [3u64,4] {
        let public=Public{headers,root:[0;32],total:[0;28],tip:[0;32],tip_time:0};
        let consumer=Consumer::new(&public).unwrap();
        let context=ProofContext::historical_tiny(&consumer,&fixture_statement(&public)).unwrap();
        let adapter=HistoricalRole4Endpoints::new(&context.height,&context.daa).unwrap();
        assert_eq!(HeightWork::history_endpoint_scope_controls_for_test(&consumer.parent).unwrap(),3);
        let circuit=context.tiny_historical_composite().unwrap();
        assert_eq!(circuit.terms.len(),if headers==3{329122}else{330050});
        assert!(circuit.terms.capacity() < 1<<20);
        let mut side_totals=[0usize;2];let mut numeric_reached=[false;2];
        for left in [true,false] {
            for owner in 0..4 {
                let mut expected:Vec<_>=circuit.terms.iter().filter(|term|
                    (if left{term.gate.left}else{term.gate.right})/layout::WIDTH==owner).map(key).collect();
                let mut actual=Vec::with_capacity(expected.len());
                let (mut distinct_height,mut distinct_numeric,mut nonzero_daa)=(false,false,false);
                let counts=adapter.visit(left,owner,|edge|{
                    assert!(actual.len()<circuit.terms.len());
                    if owner!=0 && edge.source_slot!=owner && edge.term.row<1<<21 {
                        if edge.term.row<128 {distinct_height=true;}else{distinct_numeric=true;}
                    }
                    if edge.term.row>=1<<21 && edge.source_slot!=0 {nonzero_daa=true;}
                    adapter.check_edge(left,owner,&edge)?;
                    if actual.is_empty() {
                        for fault in 0..4 {
                            let mut wrong=edge.clone();
                            match fault {0=>wrong.source_slot^=1,1=>wrong.family_row^=1,
                                2=>wrong.term.row^=1,_=>{if left{wrong.term.gate.left^=layout::WIDTH;}else{wrong.term.gate.right^=layout::WIDTH;}}}
                            assert!(adapter.check_edge(left,owner,&wrong).is_err(),"actual edge guard");
                        }
                    }
                    actual.push(key(&edge.term));Ok(())
                }).unwrap();
                assert_eq!(counts.total().unwrap(),actual.len());
                actual.sort_unstable();expected.sort_unstable();
                assert!(actual==expected,"complete endpoint occurrence multiset");
                for family in 0..2 {
                    if let Some(index)=actual.iter().position(|item|numeric_family(item)==Some(family)) {
                        numeric_reached[family]=true;
                        let mut omitted=actual.clone();omitted.remove(index);
                        assert!(omitted!=expected,"one numeric occurrence omitted in selected family");
                        assert!(omitted.iter().eq(expected.iter().enumerate().filter_map(|(i,item)|if i==index{None}else{Some(item)})),
                            "numeric omission preserves every other occurrence");
                        drop(omitted);
                        let mut duplicated=Vec::with_capacity(actual.len()+1);duplicated.extend_from_slice(&actual);
                        duplicated.push(actual[index]);duplicated.sort_unstable();
                        assert!(duplicated!=expected,"one numeric occurrence duplicated in selected family");
                        assert!(duplicated.iter().filter(|item|numeric_family(item)!=Some(family))
                            .eq(expected.iter().filter(|item|numeric_family(item)!=Some(family))),
                            "numeric duplicate preserves the other families");
                        assert_eq!(duplicated.iter().filter(|item|numeric_family(item)==Some(family)).count(),
                            expected.iter().filter(|item|numeric_family(item)==Some(family)).count()+1);
                    }
                }
                if owner==1 {assert!(distinct_height&&nonzero_daa,"height source_slot != q and nonzero DAA source");
                    if left {assert!(distinct_numeric,"numeric source_slot != nonzero endpoint q");}}
                if headers==3 && owner==3 {
                    assert_eq!(counts.height,0);assert_eq!(counts.daa.lanes,[0,0,0,81920]);
                    let lo=(1usize<<21)+3*(1<<19)+3*(1<<17);
                    let index=actual.iter().position(|item|(lo..lo+(1<<17)).contains(&item.0)).expect("N3 padding lane3 reached");
                    let mut omitted=actual.clone();omitted.remove(index);
                    assert!(omitted!=expected,"one N3 owner3 padding occurrence omitted");
                    assert!(omitted.iter().eq(expected.iter().enumerate().filter_map(|(i,item)|if i==index{None}else{Some(item)})),
                        "padding omission preserves every other occurrence");
                }
                assert!(actual==expected,"canonical multiset unchanged by isolated controls");
                side_totals[usize::from(!left)]+=actual.len();
            }
        }
        assert_eq!(side_totals,[circuit.terms.len();2]);
        assert!(numeric_reached.into_iter().all(|reached|reached),"both actual numeric families reached");
        let r:Vec<_>=(0..22).map(|i|Fr::from((i*7+3)as u64)).collect();
        let u:Vec<_>=(0..22).map(|i|Fr::from((i*11+5)as u64)).collect();
        let v:Vec<_>=(0..22).map(|i|Fr::from((i*13+9)as u64)).collect();
        let (rw,uw,vw)=(Weights::new(&r),Weights::new(&u),Weights::new(&v));
        let mut direct=[Fr::zero();4];
        for term in &circuit.terms {for (sum,value) in direct.iter_mut().zip(channels(term,&rw,&uw,&vw)){*sum+=value;}}
        assert_eq!(adapter.coefficients(&r,&u,&v).unwrap(),direct);
        assert_eq!(adapter.coefficients(&r[..21],&u,&v).err().unwrap(),"height/DAA composite dimension mismatch");
        let original=&circuit.terms[0];
        for fault in 0..7 {
            let changed=changed_occurrence(original,fault);
            assert_ne!(key(original),key(&changed),"row/endpoint/all coefficient identity");
            assert_ne!(channels(original,&rw,&uw,&vw),channels(&changed,&rw,&uw,&vw),"nonboolean single-term relation");
        }
        let global=circuit.terms.iter().find(|t|t.gate.right==0 && t.gate.left/layout::WIDTH>0).unwrap();
        let mut local=global.clone();local.gate.right=layout::WIDTH;
        assert_ne!(channels(global,&rw,&uw,&vw),channels(&local,&rw,&uw,&vw),"GLOBAL0 cannot become local0");
        let dummy=circuit.terms.iter().find(|t|t.gate.right/layout::WIDTH==1 && t.gate.right%layout::WIDTH==0).unwrap();
        let mut wrong=dummy.clone();wrong.gate.right=0;
        assert_ne!(key(dummy),key(&wrong),"local dummy cannot become GLOBAL0");
        let emitted=std::cell::Cell::new(false);
        assert_eq!(adapter.visit(true,4,|_|{emitted.set(true);Ok(())}).err().unwrap(),"history endpoint requested owner");
        assert!(!emitted.get());
        let legacy=HeightWork::new(&consumer.parent).unwrap();
        assert_eq!(HistoricalRole4Endpoints::new(&legacy,&context.daa).err().unwrap(),"history height endpoint mode or geometry");
    }
    // No Consumer/context, point templates or occurrence/EQ buffers overlap
    // this pointer-identity preflight. Two parent objects are the fault itself.
    let original=WorkTreeHistoryPlan::compile(3,2,[0;32],[0;28]).unwrap();
    let foreign=WorkTreeHistoryPlan::compile(3,2,[0;32],[0;28]).unwrap();
    let detached=HeightWork::compile_history(&foreign).unwrap();
    let daa=DaaHistoryRoster::compile(&original).unwrap();
    assert_eq!(HistoricalRole4Endpoints::new(&detached,&daa).err().unwrap(),"history endpoint parent identity");
}

fn oracle_alias_targets(q:usize,n:usize)->Vec<usize> {
    // Literal source offsets, independent of candidate builder/Epoch API.
    let mut targets=Vec::with_capacity(27);
    for d in [0usize,1,1025,2049,3073,4097,5121,6145,7169,8193,0,1,129,257,385,513,641,769,897,1025] {
        if let Some(t)=q.checked_add(d).filter(|t|*t<n){targets.push(t);}
    }
    for t in [2048usize,3072,4096,5120,6144,7168,8192]{if t<n{targets.push(t);}}
    targets.sort_unstable();targets.dedup();targets
}

fn literal_alias_class(owner:usize,n:usize)->bool {
    owner<n && ([2048usize,3072,4096,5120,6144,7168,8192].contains(&owner)
        || (owner>=9216 && owner<844672 && owner%1024==0 && owner!=417792)
        || (owner>=844672 && owner%128==0))
}

#[test]
fn inverse_calendar_and_bounded_candidates() {
    for n in [844672usize,844673,844801] {
        let parent=WorkTreeHistoryPlan::compile(n as u64,20,[0;32],[0;28]).unwrap();
        let daa=DaaHistoryRoster::compile(&parent).unwrap();
        let height=HeightWork::compile_history(&parent).unwrap();
        let adapter=HistoricalRole4Endpoints::new(&height,&daa).unwrap();
        for (epoch,target) in [(crate::daa_integer::Epoch::Eip,9216u64),(crate::daa_integer::Epoch::Legacy,844672)] {
            if target>=n as u64 {continue;} // Keep the wrong-epoch fault isolated from N clipping.
            let called=std::cell::Cell::new(false);
            assert_eq!(parent.header_boundary().mature_layout(epoch).visit_alias_terms(target,|_|{called.set(true);Ok(())}).err().unwrap(),
                "physical alias target is not a mature child of this epoch");
            assert!(!called.get(),"isolated wrong epoch before source callback");
        }
        for (epoch,target) in [(crate::daa_integer::Epoch::Legacy,417791u64),(crate::daa_integer::Epoch::Legacy,417792),
            (crate::daa_integer::Epoch::Legacy,417793),(crate::daa_integer::Epoch::Eip,844671),
            (crate::daa_integer::Epoch::Eip,844673)] {
            if target>=n as u64 {continue;}
            assert_eq!(parent.header_boundary().mature_layout(epoch).visit_alias_terms(target,|_|Err("unexpected calendar callback".into())).err().unwrap(),
                "physical alias target is not a mature child of this epoch");
        }
        let mut eip_farthest_reached=0usize;
        let owners=[0usize,1,1023,2047,2048,3071,3072,4096,5120,6144,7168,8191,8192,
            9215,9216,417790,417791,417792,417793,418815,418816,843647,843775,844543,844544,844671,844672,844673,844799,844800,n];
        for q in owners {
            for left in [true,false] {
                let targets=if left{oracle_alias_targets(q,n)}else{vec![q]};
                let mut expected=Vec::with_capacity(21280);
                let mut visited=0usize;
                for target in targets {
                    let mut count=0usize;
                    daa.visit_history_alias_source(target,|term|{
                        count+=1;
                        if (if left{term.gate.left}else{term.gate.right})/layout::WIDTH==q {
                            assert!(expected.len()<21280);expected.push(key(&term));
                        }
                        Ok(())
                    }).unwrap();
                    assert_eq!(count!=0,literal_alias_class(target,n),"independent N/calendar classification");
                    visited+=usize::from(count!=0);
                }
                let mut actual=Vec::with_capacity(21280);let mut first=None;
                let stats=daa.visit_history_alias_endpoint_terms(left,q,|term|{
                    assert!(actual.len()<21280);if first.is_none(){first=Some(term.clone());}actual.push(key(&term));Ok(())
                }).unwrap();
                assert!(stats.candidates<=if left{27}else{1});assert_eq!(stats.alias_sources,visited);
                assert!(stats.alias_occurrences<=21280);assert_eq!(stats.lanes[1],actual.len());
                actual.sort_unstable();expected.sort_unstable();assert!(actual==expected,"bounded inverse occurrence differential");
                if left && [843647usize,843775].contains(&q) && q+1025<n {
                    let target=q+1025;
                    let index=actual.iter().position(|item|item.0>>19==target && item.1/layout::WIDTH==q
                        && item.2/layout::WIDTH==target).expect("actual EIP farthest offset1025 reached");
                    assert_eq!(daa.owner_class(target as u64).unwrap(),
                        crate::daa_history_roster::OwnerClass::Mature(crate::daa_integer::Epoch::Eip));
                    eip_farthest_reached+=1;
                    let mut omitted=actual.clone();omitted.remove(index);
                    assert!(omitted!=expected,"one reached EIP farthest occurrence omitted");
                    assert!(omitted.iter().eq(expected.iter().enumerate().filter_map(|(i,item)|if i==index{None}else{Some(item)})),
                        "EIP farthest omission preserves every other occurrence");
                }
                if !actual.is_empty() {
                    let mut omitted=actual.clone();omitted.pop();assert!(omitted!=expected,"zero-channel occurrence omitted");
                    let mut duplicated=actual.clone();duplicated.push(actual[0]);assert!(duplicated!=expected,"occurrence multiplicity");
                    let term=first.unwrap();
                    let mut composite=term.clone();composite.row+=1usize<<daa.row_log();
                    let edge=crate::sparse_stream_roster::EdgeTerm {source_slot:term.row>>19,
                        family_row:(1<<19)|(term.row&((1<<19)-1)),term:composite};
                    adapter.check_edge(left,q,&edge).unwrap();
                    if edge.source_slot!=q {
                        let mut wrong=edge.clone();wrong.source_slot=q;
                        assert!(adapter.check_edge(left,q,&wrong).is_err(),"H20 row owner cannot become endpoint");
                    }
                    let p:Vec<_>=(0..40).map(|i|Fr::from((3+17*i)as u64)).collect();
                    let weights=Weights::new(&p);let good=channels(&term,&weights,&weights,&weights);
                    assert!(term.gate.c0.is_zero()&&term.gate.c3.is_zero(),"canonical zero channels retained");
                    for fault in [0usize,1,2,3,4,5,6] {
                        assert_ne!(good,channels(&changed_occurrence(&term,fault),&weights,&weights,&weights),"alias row/port/coefficient single fault");
                    }
                }
            }
        }
        assert_eq!(eip_farthest_reached,usize::from(n>844672)+usize::from(n>844800),"EIP farthest N-exclusive reach count");
        assert_eq!(daa.visit_history_alias_endpoint_terms(true,1<<20,|_|Ok(())).err().unwrap(),"history DAA endpoint owner");
    }
}

fn admit_type(file:bool,dir:bool,symlink:bool,attributes:u32,directory:bool)->Result<(),String> {
    if symlink || attributes&0x400!=0 || (if directory{!dir}else{!file}) {
        return Err("stream38 transport type/reparse".into());
    }
    Ok(())
}

fn metadata(path:&Path,directory:bool)->Result<fs::Metadata,String> {
    let m=fs::symlink_metadata(path).map_err(|e|e.to_string())?;
    #[cfg(windows)] let attributes={use std::os::windows::fs::MetadataExt;m.file_attributes()};
    #[cfg(not(windows))] let attributes=0u32;
    admit_type(m.is_file(),m.is_dir(),m.file_type().is_symlink(),attributes,directory)?;
    Ok(m)
}

fn read_member(dir:&Path,name:&str,size:usize)->Result<Vec<u8>,String> {
    metadata(dir,true)?;let path=dir.join(name);let before=metadata(&path,false)?;
    if before.len()!=size as u64{return Err("stream38 transport extent".into());}
    let mut options=OpenOptions::new();options.read(true);
    #[cfg(windows)] {use std::os::windows::fs::OpenOptionsExt;options.share_mode(1);}
    let mut f=options.open(&path).map_err(|e|e.to_string())?;
    let held=f.metadata().map_err(|e|e.to_string())?;let time=held.modified().map_err(|e|e.to_string())?;
    if held.len()!=before.len() || time!=before.modified().map_err(|e|e.to_string())?{return Err("stream38 open drift".into());}
    let mut bytes=vec![0u8;size];f.read_exact(&mut bytes).map_err(|e|e.to_string())?;
    let mut tail=[0u8;1];if f.read(&mut tail).map_err(|e|e.to_string())?!=0{return Err("stream38 trailing member".into());}
    let after=f.metadata().map_err(|e|e.to_string())?;let named=metadata(&path,false)?;
    if after.len()!=held.len() || named.len()!=held.len() || after.modified().map_err(|e|e.to_string())?!=time
        || named.modified().map_err(|e|e.to_string())?!=time{return Err("stream38 read drift".into());}
    Ok(bytes)
}

fn snapshot(dir:&Path)->Result<Vec<(String,String)>,String> {
    if !dir.is_absolute(){return Err("stream38 absolute directory".into());}metadata(dir,true)?;
    let mut names=Vec::with_capacity(10);
    for entry in dir.read_dir().map_err(|e|e.to_string())? {
        if names.len()==10{return Err("stream38 transport roster".into());}
        names.push(entry.map_err(|e|e.to_string())?.file_name().into_string().map_err(|_|"stream38 member name")?);
    }
    admit_names(&mut names)?;
    MEMBERS.iter().map(|(name,size)|Ok((name.to_string(),layout::hash_bytes(&read_member(dir,name,*size)?)))).collect()
}

fn admit_names(names:&mut Vec<String>)->Result<(),String> {
    names.sort();let mut expected:Vec<_>=MEMBERS.iter().map(|(name,_)|name.to_string()).collect();expected.sort();
    if *names!=expected{return Err("stream38 transport roster".into());}Ok(())
}

fn pin_roster(pins:&[(String,String)])->Result<(),String> {
    if pins.len()!=10 || pins.iter().zip(MEMBERS).any(|((name,hash),(expected,_))|
        name!=expected || hash.len()!=64 || !hash.bytes().all(|b|b.is_ascii_digit()||(b'a'..=b'f').contains(&b))) {
        return Err("stream38 retained pin roster".into());
    }
    Ok(())
}

fn loaded_member(name:&str,bytes:&[u8],pins:&[(String,String)])->Result<(),String> {
    pin_roster(pins)?;
    let index=MEMBERS.iter().position(|(member,_)|*member==name).ok_or("stream38 member name")?;
    if bytes.len()!=MEMBERS[index].1{return Err("stream38 consumed member extent".into());}
    if layout::hash_bytes(bytes)!=pins[index].1{return Err("stream38 consumed member digest".into());}Ok(())
}

fn bound_read(dir:&Path,name:&str,pins:&[(String,String)])->Result<Vec<u8>,String> {
    pin_roster(pins)?;
    let index=MEMBERS.iter().position(|(member,_)|*member==name).ok_or("stream38 member name")?;
    let bytes=read_member(dir,name,MEMBERS[index].1)?;loaded_member(name,&bytes,pins)?;Ok(bytes)
}

fn transport_controls() {
    let pins:Vec<_>=MEMBERS.iter().map(|(name,size)|(name.to_string(),layout::hash_bytes(&vec![37u8;*size]))).collect();
    for (name,size) in MEMBERS {
        let mut bytes=vec![37u8;size];loaded_member(name,&bytes,&pins).unwrap();
        bytes[0]^=1;assert_eq!(loaded_member(name,&bytes,&pins).err().unwrap(),"stream38 consumed member digest");
        bytes[0]^=1;bytes.pop();assert_eq!(loaded_member(name,&bytes,&pins).err().unwrap(),"stream38 consumed member extent");
        bytes.resize(size+1,37);assert_eq!(loaded_member(name,&bytes,&pins).err().unwrap(),"stream38 consumed member extent");
    }
    let mut names:Vec<_>=MEMBERS.iter().map(|(name,_)|name.to_string()).collect();admit_names(&mut names).unwrap();
    for fault in 0..3 {
        let mut wrong=names.clone();match fault{0=>{wrong.pop();},1=>wrong.push("extra.bin".into()),_=>wrong[0]=wrong[1].clone()};
        assert_eq!(admit_names(&mut wrong).err().unwrap(),"stream38 transport roster");
    }
    for directory in [true,false] {
        admit_type(!directory,directory,false,0,directory).unwrap();
        for (file,dir,symlink,attributes) in [(directory,!directory,false,0),(!directory,directory,true,0),(!directory,directory,false,0x400)] {
            assert_eq!(admit_type(file,dir,symlink,attributes,directory).err().unwrap(),"stream38 transport type/reparse");
        }
    }
    let mut wrong=pins.clone();wrong.swap(0,1);
    assert_eq!(loaded_member(MEMBERS[0].0,&vec![37;568],&wrong).err().unwrap(),"stream38 retained pin roster");
}

fn load(dir:&Path,pins:&[(String,String)])->Result<(Vec<u8>,Artifact),String> {
    let statement=bound_read(dir,"statement.bin",pins)?;
    crate::historical_prefix_public::decode_tiny_candidate(&statement)?;
    let commitment=bound_read(dir,"commitment.bin",pins)?;
    let mut roles=Vec::with_capacity(7);
    for role in 0..7{roles.push(RoleProof{role,bytes:bound_read(dir,&format!("role-{role}.gkr"),pins)?});}
    let batch=bound_read(dir,"openings.bin",pins)?;Ok((statement,Artifact{commitment,roles,batch}))
}

fn scalar_hex(value:Fr)->String {
    let mut bytes=value.into_bigint().to_bytes_le();bytes.resize(32,0);
    bytes.iter().map(|b|format!("{b:02x}")).collect()
}

fn claim_json(claim:&Claim)->serde_json::Value {
    serde_json::json!({"point":claim.point.iter().map(|v|scalar_hex(*v)).collect::<Vec<_>>(),"value":scalar_hex(claim.value)})
}

fn join(headers:u64) {
    let started=Instant::now();let location=std::cell::Cell::new("admission");let position=std::cell::Cell::new(0usize);
    let mark=|stage:&'static str,event:&'static str|->Result<(),String> {
        location.set(stage);let index=position.get();
        if STAGES.get(index)!=Some(&(stage,event)){return Err("stream38 marker order".into());}
        let ns=started.elapsed().as_nanos();if ns>180_000_000_000{return Err("stream38 deadline".into());}
        eprintln!("HISTORY_ROLE4_STREAM38_STAGE {stage} {event} {ns}");position.set(index+1);Ok(())
    };
    let operation=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||->Result<(),String>{
        mark("admission","begin")?;
        let input=std::env::var_os("NIPOPOW_ROLE4_STREAM38_INPUT_DIR").map(PathBuf::from).ok_or("stream38 input directory")?;
        let output=std::env::var_os("NIPOPOW_COMMON_PREFIX_DIR").map(PathBuf::from).ok_or("stream38 output directory")?;
        if !output.is_absolute() || output==input{return Err("stream38 fresh output directory".into());}
        metadata(&output,true)?;if output.read_dir().map_err(|e|e.to_string())?.next().is_some(){return Err("stream38 nonempty output".into());}
        let pins=snapshot(&input)?;let (statement,mut artifact)=load(&input,&pins)?;
        let decoded=crate::historical_prefix_public::decode_tiny_candidate(&statement)?;
        if decoded.headers!=headers || !matches!(headers,3|4){return Err("stream38 retained profile".into());}
        let c=pcs::decode_commitment(&artifact.commitment)?;
        if pcs::encode_commitment(&c)?!=artifact.commitment{return Err("stream38 canonical C".into());}
        drop(c);
        let key=verifier_key::admit(22,include_bytes!("../fixtures/verifier-keys-v1/log22.vk"))?;
        let private=std::env::temp_dir().join(format!("role4-stream38-n{headers}-{}.bits",std::process::id()));
        if private.exists(){return Err("stream38 private path exists".into());}mark("admission","end")?;
        mark("witness","begin")?;
        let bits={
            let w=witness::build(&witness::retained_headers_n(headers as usize)?)?;
            if (w.root,w.total,w.tip,w.tip_time)!=(decoded.root,decoded.total,decoded.tip,decoded.tip_time){return Err("stream38 witness fixture agreement".into());}
            let mut bits=vec![0u8;524288];
            for (index,value) in w.values.iter().enumerate(){if !value.is_zero()&&!value.is_one(){return Err("stream38 Boolean witness".into());}
                if value.is_one(){bits[index/8]|=1<<(index%8);}}
            bits
        };mark("witness","end")?;
        let (reference_claims,reference_counters,reference_continuation,producer_claim,producer_counters,producer_continuation,metrics,stream_ns)={
            let source=packed_source(&private,&bits)?;drop(bits);
            mark("reference","begin")?;
            let public=Public{headers:decoded.headers,root:decoded.root,total:decoded.total,tip:decoded.tip,tip_time:decoded.tip_time};
            let consumer=Consumer::new(&public)?;let context=ProofContext::historical_tiny(&consumer,&statement)?;
            let reference_claims=context.verify_roles(&artifact,&key).map_err(|e|format!("stream38 retained roles: {e:?}"))?;
            let reference=context.verify_role(&artifact.roles[4],&key,&artifact.commitment).map_err(|e|e.message)?;
            if reference.claim!=reference_claims[4]{return Err("stream38 fresh reference claim".into());}mark("reference","end")?;
            mark("streaming","begin")?;let began=Instant::now();
            let mut t=context.transcript(4,&key,&artifact.commitment);
            let (proof,claim,incremental_u,incremental_v,metrics)=prove_role4_historical_streaming(&context,&source,&mut t)?;
            let stream_ns=u64::try_from(began.elapsed().as_nanos()).map_err(|_|"stream38 stream clock")?;
            if incremental_u||incremental_v{return Err("stream38 replay branch".into());}mark("streaming","end")?;
            mark("equality","begin")?;
            let encoded=gkr::encode_proof(&proof)?;
            if encoded.len()!=5024 || gkr::encode_proof(&gkr::decode_dimensions(&[22],&encoded)?)?!=encoded
                || encoded!=artifact.roles[4].bytes{return Err("stream38 proof bytes differential".into());}
            let producer=Claim{point:claim.point,value:claim.value};
            let counters=[t.challenges(),t.raw_queries(),t.bytes_absorbed()];
            let continuation=t.clone().try_challenge_scalar(b"candidate-binding-role-continuation-v1")?;
            if producer!=reference.claim || counters!=reference.counters || continuation!=reference.continuation {
                return Err("stream38 claim/transcript differential".into());
            }
            if source.evaluate(&producer.point)?!=producer.value{return Err("stream38 held MLE".into());}
            let mut corrupt=proof.clone();corrupt.layers[0].rounds[0][0]+=Fr::one();
            if context.verify_role4(&corrupt,&mut context.transcript(4,&key,&artifact.commitment))!=Err(GkrError::SumcheckIdentity){return Err("stream38 isolated GKR attribution".into());}
            let terms=context.term_count() as u64;
            if metrics.callbacks!=44*terms || metrics.left_terms!=22*terms || metrics.right_terms!=22*terms
                || metrics.endpoint_calls!=176 || metrics.load_calls!=4 || metrics.loaded_fields!=4194304
                || metrics.loader_capacity_peak!=33554432 || metrics.load_decode_ns>stream_ns {
                return Err("stream38 observed count closure".into());
            }
            artifact.roles[4].bytes=encoded;mark("equality","end")?;
            (reference_claims,reference.counters,reference.continuation,producer,counters,continuation,metrics,stream_ns)
        }; // All source/witness/cache/context/producer graph handles dropped here.
        drop(key);drop(decoded);mark("producer_drop","end")?;
        mark("export","begin")?;
        // Gate output again immediately before the first create_new write.
        metadata(&output,true)?;if output.read_dir().map_err(|e|e.to_string())?.next().is_some(){return Err("stream38 output admission drift".into());}
        write_new(&output.join("statement.bin"),&statement)?;write_new(&output.join("commitment.bin"),&artifact.commitment)?;
        for packet in &artifact.roles{write_new(&output.join(format!("role-{}.gkr",packet.role)),&packet.bytes)?;}
        write_new(&output.join("openings.bin"),&artifact.batch)?;
        if snapshot(&output)?!=pins{return Err("stream38 output pins differential".into());}drop(artifact);drop(statement);mark("export","end")?;
        mark("consumer","begin")?;
        let (fresh_statement,fresh_artifact)=load(&output,&pins)?;
        let actual=verify_historical_tiny_bytes(&fresh_statement,&fresh_artifact)?;
        if actual!=reference_claims{return Err("stream38 atomic seven-claim differential".into());}
        mark("consumer","end")?;mark("custody","begin")?;
        if snapshot(&input)?!=pins || snapshot(&output)?!=pins{return Err("stream38 final custody".into());}
        let _=load(&input,&pins)?;let _=load(&output,&pins)?;
        fs::remove_file(&private).map_err(|e|e.to_string())?;mark("custody","end")?;
        let elapsed=u64::try_from(started.elapsed().as_nanos()).map_err(|_|"stream38 elapsed")?;
        let sha=crate::native_prefix_auth_plan::role0_sha256(&fresh_artifact.roles[4].bytes)?;
        let report=serde_json::json!({"schema":"role4-stream38-historical-tiny-v1","result":"PASS","headers":headers,
            "mode":"historical_tiny_testonly","roles":7,"files":10,"public_bytes":66133,"role4_bytes":5024,"opening_bytes":31581,
            "terms":if headers==3{329122}else{330050},"proofs_regenerated":1,"reference_roles_verified":7,
            "proof_sha256":sha.iter().map(|b|format!("{b:02x}")).collect::<String>(),
            "reference_claim":claim_json(&reference_claims[4]),"producer_claim":claim_json(&producer_claim),
            "reference_counters":reference_counters,"producer_counters":producer_counters,
            "reference_continuation":scalar_hex(reference_continuation),"producer_continuation":scalar_hex(producer_continuation),
            "checks":{"proof_bytes_equal":true,"claim_equal":true,"counters_equal":true,"continuation_equal":true,
                "held_mle_equal":true,"atomic_seven_claims_equal":true,"input_pins_equal":true,"output_pins_equal":true,
                "producer_dropped":true,"canonical_codec":true,"corrupt_gkr_sumcheck":true},
            "observed":{"endpoint_calls":metrics.endpoint_calls,"callbacks":metrics.callbacks,"left_terms":metrics.left_terms,"right_terms":metrics.right_terms,
                "load_calls":metrics.load_calls,"loaded_fields":metrics.loaded_fields,"load_decode_ns":metrics.load_decode_ns,
                "loader_capacity_peak":metrics.loader_capacity_peak,"read_calls":metrics.io.read_calls,"read_bytes":metrics.io.read_bytes,"read_ns":metrics.io.read_ns},
            "internal":{"observed":false,"cache_peak":null,"input_vector_clones":null},
            "ledger":{"replay_payload_bound":301989888,"loader_transient_bound":2105344,"stack_min":67108864,"worker_stack_reserve":268435456,"whole_process_bound":null},
            "stream_ns":stream_ns,"elapsed_ns":elapsed,"incremental_u":false,"incremental_v":false,
            "expected_public_in_receiver":false,"expected_c_in_receiver":false,"setup_in_producer":false,"full_history":false,"production":false});
        let encoded=serde_json::to_vec(&report).map_err(|e|e.to_string())?;
        if encoded.len()>16384 || position.get()!=17 || started.elapsed().as_nanos()>180_000_000_000{return Err("stream38 report/order/deadline".into());}
        location.set("complete");eprintln!("HISTORY_ROLE4_STREAM38_STAGE complete end {elapsed}");position.set(18);
        let mut out=std::io::stdout().lock();out.write_all(b"\nHISTORY_ROLE4_STREAM38_REPORT ").map_err(|e|e.to_string())?;
        out.write_all(&encoded).map_err(|e|e.to_string())?;out.write_all(b"\n").map_err(|e|e.to_string())?;out.flush().map_err(|e|e.to_string())?;
        Ok(())
    }));
    let error=match operation {Ok(Ok(()))=>None,Ok(Err(error))=>Some(error),Err(_)=>Some("stream38 panic".into())};
    if let Some(error)=error {
        let bounded:String=error.chars().filter(|c|c.is_ascii_graphic()||*c==' ').take(240).collect();
        eprintln!("HISTORY_ROLE4_STREAM38_HOLD {} {} {}",location.get(),started.elapsed().as_nanos(),bounded);
        panic!("role4 stream38 HOLD");
    }
}

#[test]
#[ignore = "requires accepted37 retained historical packet and a bounded fresh-output runner"]
fn historical_n3_streaming_join(){join(3);}

#[test]
#[ignore = "requires accepted37 retained historical packet and a bounded fresh-output runner"]
fn historical_n4_streaming_join(){join(4);}

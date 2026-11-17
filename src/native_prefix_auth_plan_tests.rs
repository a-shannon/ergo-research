//! One bounded source differential; no proof, opening or authenticated output.

// source28-role6-child-BEGIN
        mod role6_direct_prefix{
            use super::*;
            use crate::{sparse_stream_roster as edge,transcript::Transcript};
            use super::role2_residual_diagnostic as residual;
            use std::{cell::{Cell,RefCell},time::Instant,io::{Read,Write},fs::File};
            use ark_serialize::{CanonicalSerialize,CanonicalDeserialize};
            const WIDTH:usize=1<<20;const MIB:usize=1<<20;const REPORT:usize=16384;
            const RAW_SHA:&str="ABB3D74AE75256CED63110B72C2E0D5EBA1B90B09889E45EA327BDA1C9A640D2";
            const RAW_BLAKE:&str="8CDB90DA475E646280113D97C9469BE7EB86A1D04F20404C64239187284FC009";
            const PACK_SHA:&str="C1CC1CF72FF539F259A3BDEF756332BA52CB8AFF26C11AB4116D1B2F9D17ED43";
            const PACK_BLAKE:&str="725D7B1215E1185C52C1012D9294260612653ACAD53A02429B8EAAFD0F0770C8";
            const LEFT:&str="8CA65C0B38F5E600ABA12C728F98F02D1B34A1056EAC79C75E7EFF324EF2F1A1";
            struct Count{terms:u64,rows:u64}
            fn need(ok:bool,message:&str)->Result<(),String>{if ok{Ok(())}else{Err(message.into())}}
            fn plus(a:u64,b:u64)->Result<u64,String>{a.checked_add(b).ok_or("role6 count overflow".into())}
            fn times(a:u64,b:u64)->Result<u64,String>{a.checked_mul(b).ok_or("role6 count overflow".into())}
            fn counters(t:&Transcript)->[u64;3]{[t.challenges(),t.raw_queries(),t.bytes_absorbed()]}
            fn scalar(x:Fr)->Result<String,String>{let mut bytes=[0u8;32];x.serialize_compressed(&mut bytes[..]).map_err(|e|e.to_string())?;
                need(Fr::deserialize_compressed(&bytes[..]).map_err(|e|e.to_string())?==x,"role6 scalar canonical")?;
                Ok(bytes.iter().map(|b|format!("{b:02x}")).collect())}
            fn member_check(actual:&[u64;1],expected:&[Count;1])->Result<(),String>{need(actual[0]==expected[0].terms,"role6 pass count")}
            fn check_edge(e:&edge::EdgeTerm,left:bool,owner:usize,_strides:&[usize;1])->Result<usize,String>{
                need(e.term.row==edge::global_edge_row(e.source_slot,e.family_row,12,12,0,&[12])?,"role6 checked original row")?;
                need((if left{e.term.gate.left}else{e.term.gate.right})/WIDTH==owner,"role6 checked endpoint")?;Ok(0)}
            fn digest_counts(counts:&[usize])->Result<String,String>{need(counts.len()==4096,"role6 count vector width")?;
                let mut bytes=Vec::new();bytes.try_reserve_exact(32768).map_err(|e|e.to_string())?;need(bytes.capacity()==32768,"role6 digest capacity")?;
                for n in counts{bytes.extend_from_slice(&u64::try_from(*n).map_err(|_|"role6 count conversion")?.to_le_bytes());}
                Ok(screen_hex(&crate::native_prefix_auth_plan::role0_sha256(&bytes)?))}
            struct Writer{bytes:Vec<u8>}
            impl Writer{fn new()->Result<Self,String>{let mut bytes=Vec::new();bytes.try_reserve_exact(REPORT).map_err(|e|e.to_string())?;
                need(bytes.capacity()==REPORT,"role6 report allocation")?;Ok(Self{bytes})}}
            impl Write for Writer{fn write(&mut self,b:&[u8])->std::io::Result<usize>{if self.bytes.len().checked_add(b.len()).is_none_or(|n|n>REPORT){
                return Err(std::io::Error::other("role6 report cap"));}self.bytes.extend_from_slice(b);Ok(b.len())}fn flush(&mut self)->std::io::Result<()>{Ok(())}}
            struct Artifact{bytes:Vec<u8>,file:File,identity:U0FileInfo,path:std::path::PathBuf}
            fn open_artifact(path:&std::path::Path,size:usize)->Result<File,String>{
                use std::os::windows::fs::MetadataExt;
                need(path.is_absolute()&&path.as_os_str().len()<=1024,"role6 artifact absolute bounded path")?;
                need(size==33264||size==384,"role6 artifact admitted size")?;
                let md=std::fs::symlink_metadata(path).map_err(|e|e.to_string())?;
                need(md.is_file()&&md.file_attributes()&0x400==0&&md.len()==size as u64,"role6 artifact extent/type")?;
                let file=OpenOptions::new().read(true).share_mode(1).open(path).map_err(|e|e.to_string())?;
                let id=u0_file_info(&file)?;
                need(((u64::from(id.size_high)<<32)|u64::from(id.size_low))==size as u64
                    &&file.metadata().map_err(|e|e.to_string())?.len()==size as u64,"role6 artifact held extent")?;
                let current=OpenOptions::new().read(true).share_mode(1).open(path).map_err(|e|e.to_string())?;
                need(u0_file_info(&current)?==id,"role6 artifact opened path identity")?;Ok(file)
            }
            fn artifact_at(path:std::path::PathBuf,size:usize,pin:&str)->Result<Artifact,String>{
                let file=open_artifact(&path,size)?;let identity=u0_file_info(&file)?;
                let mut bytes=Vec::new();bytes.try_reserve_exact(size+1).map_err(|e|e.to_string())?;need(bytes.capacity()==size+1,"role6 artifact capacity")?;
                file.try_clone().map_err(|e|e.to_string())?.take(size as u64+1).read_to_end(&mut bytes).map_err(|e|e.to_string())?;
                need(bytes.len()==size&&screen_hex(&crate::native_prefix_auth_plan::role0_sha256(&bytes)?)==pin,"role6 artifact pin")?;
                let artifact=Artifact{bytes,file,identity,path};artifact_custody(&artifact)?;Ok(artifact)}
            fn artifact(env:&str,size:usize,pin:&str)->Result<Artifact,String>{
                artifact_at(std::path::PathBuf::from(std::env::var_os(env).ok_or("role6 artifact env")?),size,pin)}
            fn artifact_custody(artifact:&Artifact)->Result<(),String>{let current=open_artifact(&artifact.path,artifact.bytes.len())?;
                need(u0_file_info(&artifact.file)?==artifact.identity&&u0_file_info(&current)?==artifact.identity,"role6 artifact custody")}
            fn artifact_opener_controls()->Result<(),String>{
                let nonce=std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map_err(|e|e.to_string())?.as_nanos();
                let dir=std::env::temp_dir().join(format!("native-role6-artifact-{}-{nonce}",std::process::id()));
                std::fs::create_dir(&dir).map_err(|e|e.to_string())?;
                need(std::fs::read_dir(&dir).map_err(|e|e.to_string())?.next().is_none(),"role6 artifact fixture fresh empty directory")?;
                for size in [33264usize,384]{
                    let bytes:Vec<u8>=(0..size).map(|i|(i%251) as u8).collect();
                    let pin=screen_hex(&crate::native_prefix_auth_plan::role0_sha256(&bytes)?);
                    let path=dir.join(format!("artifact-{size}.bin"));
                    let twin=dir.join(format!("twin-{size}.bin"));
                    for p in [&path,&twin]{let mut file=OpenOptions::new().write(true).create_new(true).open(p).map_err(|e|e.to_string())?;
                        file.write_all(&bytes).and_then(|_|file.sync_all()).map_err(|e|e.to_string())?;}
                    {
                        let mut admitted=artifact_at(path.clone(),size,&pin)?;need(admitted.bytes==bytes,"role6 artifact deterministic positive bytes")?;
                        let reopened=open_artifact(&path,size)?;need(u0_file_info(&reopened)?==admitted.identity,"role6 artifact positive reopen")?;
                        need(OpenOptions::new().write(true).open(&path).err().is_some_and(|e|e.raw_os_error()==Some(32)),"role6 artifact write sharing denial")?;
                        need(std::fs::remove_file(&path).err().is_some_and(|e|e.raw_os_error()==Some(32)),"role6 artifact delete sharing denial")?;
                        admitted.path=twin.clone();need(artifact_custody(&admitted).err().as_deref()==Some("role6 artifact custody"),"role6 artifact detached path custody control")?;
                        admitted.path=path.clone();artifact_custody(&admitted)?;
                        let wrong_pin=if pin.starts_with('0'){format!("1{}",&pin[1..])}else{format!("0{}",&pin[1..])};
                        need(artifact_at(path.clone(),size,&wrong_pin).err().as_deref()==Some("role6 artifact pin"),"role6 artifact isolated pin control")?;
                    }
                    for length in [size-1,size+1]{let wrong=dir.join(format!("wrong-{size}-{length}.bin"));
                        let mut file=OpenOptions::new().write(true).create_new(true).open(&wrong).map_err(|e|e.to_string())?;
                        file.write_all(&vec![0;length]).map_err(|e|e.to_string())?;drop(file);
                        need(open_artifact(&wrong,size).err().as_deref()==Some("role6 artifact extent/type"),"role6 artifact isolated wrong-size control")?;
                        std::fs::remove_file(&wrong).map_err(|e|e.to_string())?;}
                    let alias=dir.join(format!("alias-{size}.bin"));std::fs::hard_link(&path,&alias).map_err(|e|e.to_string())?;
                    need(open_artifact(&path,size).err().as_deref()==Some("U0 regular single-link immutable source"),"role6 artifact isolated hard-link control")?;
                    std::fs::remove_file(&alias).map_err(|e|e.to_string())?;
                    let final_read=artifact_at(path.clone(),size,&pin)?;artifact_custody(&final_read)?;drop(final_read);
                    std::fs::remove_file(&path).map_err(|e|e.to_string())?;std::fs::remove_file(&twin).map_err(|e|e.to_string())?;
                }
                let wrong_type=dir.join("wrong-type");std::fs::create_dir(&wrong_type).map_err(|e|e.to_string())?;
                need(open_artifact(&wrong_type,384).err().as_deref()==Some("role6 artifact extent/type"),"role6 artifact isolated directory control")?;
                std::fs::remove_dir(&wrong_type).map_err(|e|e.to_string())?;
                need(open_artifact(std::path::Path::new("relative-artifact.bin"),384).err().as_deref()==Some("role6 artifact absolute bounded path"),"role6 artifact relative path control")?;
                need(std::fs::read_dir(&dir).map_err(|e|e.to_string())?.next().is_none(),"role6 artifact fixture cleanup empty")?;
                std::fs::remove_dir(&dir).map_err(|e|e.to_string())?;Ok(())
            }
            fn artifacts()->Result<(Artifact,Artifact,NativeRole0DiagnosticContext),String>{
                let key=artifact("NIPOPOW_ROLE4_KEY_PATH",33264,"D11220A1CBB08BE2C84F6B854EC2A932B3FCEC49C217963D079DD8053F7B31B2")?;
                let commitment=artifact("NIPOPOW_NATIVE_ROLE0_COMMITMENT_PATH",384,"2739A3353D579A7FA0F19B06EFDD26A625CDB80009C65707D8B96E7D8C0C9C90")?;
                let context=NativeRole0DiagnosticContext::admit(&key.bytes,&commitment.bytes)?;
                let mut wrong=key.bytes.clone();wrong[0]^=1;
                need(NativeRole0DiagnosticContext::admit(&wrong,&commitment.bytes).err().as_deref()==Some("native role0 code-owned verifier-key SHA-256 mismatch"),"role6 wrong artifact key control")?;
                need(NativeRole0DiagnosticContext::admit(&key.bytes[..33263],&commitment.bytes).err().as_deref()==Some("native role0 admitted artifact extent/setup identity"),"role6 key extent control")?;
                need(NativeRole0DiagnosticContext::admit(&key.bytes,&commitment.bytes[..383]).err().as_deref()==Some("native role0 admitted artifact extent/setup identity"),"role6 commitment extent control")?;
                need(NativeRole0DiagnosticContext::admit_with_setup_id(&key.bytes,&commitment.bytes,[0;32]).err().as_deref()==Some("native role0 admitted artifact extent/setup identity"),"role6 setup control")?;
                let changed=crate::pcs::encode_commitment(&dory_pcs::backends::arkworks::ArkGT(ark_ec::pairing::PairingOutput::<ark_bn254::Bn254>::zero()))?;
                need(NativeRole0DiagnosticContext::admit(&key.bytes,&changed).err().as_deref()==Some("native role0 code-owned commitment SHA-256 mismatch"),"role6 commitment pin control")?;
                Ok((key,commitment,context))}

            use crate::sparse_stream_roster::EdgeInput;
            const DOMAIN:&[u8]=b"native-prefix-role6-direct-full-diagnostic-v1";
            const NEXT:&[u8]=b"native-role6-direct-full-continuation-v1";
            const TOTAL:u64=316_001_708;
            const FIXED:[&str;8]=["admission","plan","binding","wiring","codec","verify","mle","custody"];
            fn clock(start:Instant)->Result<u64,String>{let n=u64::try_from(start.elapsed().as_nanos()).map_err(|_|"direct full clock")?;
                need(n<=3_600_000_000_000,"direct full deadline")?;Ok(n)}
            fn sum_cap(values:&[usize])->Result<usize,String>{values.iter().try_fold(0usize,|a,b|a.checked_add(*b)).ok_or("direct full capacity overflow".into())}
            struct Trace{start:Instant,stage:Cell<&'static str>,round:Cell<usize>,owner:Cell<usize>,row:Cell<usize>,terms:Cell<u64>,callbacks:Cell<u64>,
                substage:Cell<&'static str>,markers:Cell<usize>,census_mode:Cell<bool>,census:RefCell<[[u64;1];2]>,census_terms:[Cell<u64>;2],
                current:RefCell<[u64;1]>,current_terms:Cell<u64>,member_checks:Cell<u64>,fixed_begin:RefCell<[u64;8]>,fixed_ns:RefCell<[u64;8]>}
            impl Trace{
                fn new()->Self{Self{start:Instant::now(),stage:Cell::new("admission"),round:Cell::new(0),owner:Cell::new(0),row:Cell::new(0),terms:Cell::new(0),callbacks:Cell::new(0),
                    substage:Cell::new("admission"),markers:Cell::new(0),census_mode:Cell::new(false),census:RefCell::new([[0;1];2]),census_terms:[Cell::new(0),Cell::new(0)],
                    current:RefCell::new([0;1]),current_terms:Cell::new(0),member_checks:Cell::new(0),fixed_begin:RefCell::new([0;8]),fixed_ns:RefCell::new([0;8])}}
                fn line(stage:&str,event:u8,round:usize,owners:usize,terms:u64,n:u64)->Result<String,String>{
                    let line=format!("NATIVE_ROLE6_DIRECT_FULL_STAGE {stage} {} {round} {owners} {terms} {n}\n",event as char);
                    need(line.len()<=112,"direct full marker bound")?;Ok(line)}
                fn emit_at(&self,stage:&str,event:u8,round:usize,owners:usize,terms:u64,n:u64)->Result<(),String>{
                    need(self.markers.get()<268,"direct full marker count")?;let line=Self::line(stage,event,round,owners,terms,n)?;
                    let mut out=std::io::stderr().lock();out.write_all(line.as_bytes()).map_err(|e|e.to_string())?;out.flush().map_err(|e|e.to_string())?;
                    self.markers.set(self.markers.get()+1);Ok(())}
                fn fixed(&self,stage:&'static str,begin:bool)->Result<(),String>{let index=FIXED.iter().position(|s|*s==stage).ok_or("direct full fixed stage")?;
                    self.stage.set(stage);self.substage.set(stage);self.round.set(0);self.owner.set(0);self.row.set(0);self.terms.set(0);
                    let n=clock(self.start)?;if begin{self.fixed_begin.borrow_mut()[index]=n;}else{
                        self.fixed_ns.borrow_mut()[index]=n.checked_sub(self.fixed_begin.borrow()[index]).ok_or("direct full fixed clock")?;}
                    self.emit_at(stage,if begin{b'b'}else{b'e'},0,0,0,n)}
                fn event(&self,e:edge::EdgeFullEvent,expected:&[Count;1])->Result<(),String>{
                    self.stage.set(e.stage);self.round.set(e.round);self.terms.set(e.terms);
                    if e.event==b'b'{self.owner.set(0);self.row.set(0);self.substage.set(if e.stage.ends_with("high"){"high_internal_unknown"}else{"kernel"});
                        self.census_mode.set(e.stage.starts_with("census"));
                        if !self.census_mode.get(){*self.current.borrow_mut()=[0;1];self.current_terms.set(0);}}
                    if e.event==b'p'&&e.owners>0{
                        if e.stage.starts_with("census"){let side=usize::from(e.stage=="census_right");need(self.census_terms[side].get()==e.terms,"direct full census progress")?;
                            if e.owners==4096{member_check(&self.census.borrow()[side],expected)?;self.member_checks.set(plus(self.member_checks.get(),1)?);}}
                        else if e.stage!="line"{need(self.current_terms.get()==e.terms,"direct full pass progress")?;
                            if e.owners==4096{member_check(&self.current.borrow(),expected)?;self.member_checks.set(plus(self.member_checks.get(),1)?);}}
                    }
                    if e.stage.ends_with("high")&&e.event==b'p'{self.substage.set("confirmed_after_return");}
                    if e.stage=="wiring"{return self.fixed("wiring",e.event==b'b');}
                    self.emit_at(e.stage,e.event,e.round,e.owners,e.terms,clock(self.start)?)}
                fn term(&self,left:bool,tag:usize)->Result<(),String>{
                    self.callbacks.set(plus(self.callbacks.get(),1)?);
                    if self.census_mode.get(){let side=usize::from(!left);let mut c=self.census.borrow_mut();c[side][tag]=plus(c[side][tag],1)?;
                        self.census_terms[side].set(plus(self.census_terms[side].get(),1)?);self.terms.set(self.census_terms[side].get());}
                    else{let mut c=self.current.borrow_mut();c[tag]=plus(c[tag],1)?;self.current_terms.set(plus(self.current_terms.get(),1)?);self.terms.set(self.current_terms.get());}Ok(())}
            }
            struct Closed{report:Vec<u8>,hex:String,elapsed:u64}
            fn run(trace:&Trace)->Result<Closed,String>{
                trace.fixed("admission",true)?;let(raw,raw_id,raw_path)=residual::raw_hold().map_err(|e|format!("{e:?}"))?;
                let path=std::path::PathBuf::from(std::env::var_os("NIPOPOW_NATIVE_U_SEQUENCE_WITNESS").ok_or("direct full witness env")?);
                let(source,mut held,id)=useq_admit()?;let(key,commitment,context)=artifacts()?;trace.fixed("admission",false)?;trace.fixed("plan",true)?;
                let native=input();let candidate=crate::native_prefix_auth_plan::Candidate{n:3073,root:native.root(),total:native.total_be28(),
                    tip:ergo_header_core::blake2b256(native.raw(3073)?),tip_time:native.timestamp(3073)?};
                let parent=WorkTreeHistoryPlan::compile(3073,12,candidate.root,candidate.total)?;drop(native);
                let plan=NativePrefixAuthPlan::compile(&parent,Selection::s12(),candidate)?;
                let adapter=plan.admit_role6_for_test(&source,&context,&mut held)?;
                let detached=crate::packed::PackedFile::open_with_limit(&path,32,32)?;adapter.native_controls(&detached)?;drop(detached);
                let expected=[Count{terms:7_181_857,rows:6_499_651}];let strides=[12];
                let mut adapter_stats=crate::header_metadata_order_layout::Role6EndpointStats::default();
                let mut cache=edge::PackedEdgeInput::new(WIDTH,4096,|owner|{clock(trace.start)?;trace.owner.set(owner);trace.substage.set("load");
                    let view=source.native_role0_view()?;view.require_same_source(&source)?;let packet=view.read_copy(owner)?;
                    need(packet.len()==WIDTH&&packet.capacity_bytes()==131072,"direct full loader packet")?;trace.substage.set("kernel");Ok(packet.into_bytes())})?;
                edge::edge_input_geometry(&cache,WIDTH,4096)?;let cache_budget=cache.cache_budget_bytes()?;
                need(cache.metrics().metadata_capacity_bytes<=4096,"direct full cache metadata")?;trace.fixed("plan",false)?;
                trace.fixed("binding",true)?;let mut caller=Transcript::new(DOMAIN);
                let prepared=adapter.prepare(&caller)?;let initial=counters(&prepared);let mut working=caller.clone();
                trace.fixed("binding",false)?;let began=Instant::now();
                let(proof,claim,iu,iv,stats)=edge::prove_edge_terms_strategy_for_test(20,12,12,0,&strides,true,true,true,0,&mut cache,
                    |left,owner,sink|{if trace.census_mode.get(){trace.stage.set(if left{"census_left"}else{"census_right"});}
                        trace.owner.set(owner);trace.substage.set("kernel");adapter.visit(left,owner,&mut adapter_stats,&mut|e|{
                            trace.row.set(e.term.row);let tag=check_edge(&e,left,owner,&strides)?;sink(e)?;trace.term(left,tag)?;
                            if trace.callbacks.get()%65536==0{clock(trace.start)?;}Ok(())})},
                    &mut working,|t|*t=prepared.clone(),|r,u,v|plan.coefficients(6,r,u,v),&mut|e|trace.event(e,&expected))?;
                let producer_ns=u64::try_from(began.elapsed().as_nanos()).map_err(|_|"direct full producer clock")?;
                let packed=cache.metrics();drop(cache);
                need(adapter_stats.source_emitter_calls==202818&&adapter_stats.canonical_callbacks==474008194&&adapter_stats.selected_callbacks==TOTAL
                    &&adapter_stats.order_term_prevalidations==422064258&&adapter_stats.order_wire_prevalidations==844128516
                    &&adapter_stats.metadata_term_prevalidations==51943936&&adapter_stats.adjacency_calls==405636
                    &&adapter_stats.adjacency_wire_iterations==207685632&&adapter_stats.adjacency_wire_endpoint_checks==415326208,"role6 adapter boundaries")?;
                need(!iu&&!iv&&stats.term_callbacks==TOTAL&&trace.callbacks.get()==TOTAL&&trace.member_checks.get()==44,"direct full callback coverage")?;
                need(stats.owner_requests==176128&&stats.emitted_fields==21474828288&&stats.prefix_plans==42&&stats.suffix_tables==36&&stats.pattern_tables==40,
                    "direct full projection counts")?;
                need(stats.sequential_x_folds==0&&stats.sequential_bank_folds==0&&stats.input_vector_clones==0&&stats.line_internal_clones==4096
                    &&stats.line_cloned_fields==4294967296,"direct full folds/clones")?;
                need(packed.scalar_gets==150818997&&packed.logical_gets==150995125&&packed.vector_expansions==12288&&packed.expanded_fields==12884901888
                    &&packed.projection_calls==163840&&packed.projection_fields==8589926400,"direct full packed operation counts")?;
                need(packed.logical_gets==plus(packed.scalar_gets,stats.owner_requests)?&&stats.emitted_fields==plus(packed.expanded_fields,packed.projection_fields)?
                    &&packed.packed_bytes==times(packed.successful_loads,131072)?&&packed.successful_loads>0&&packed.successful_loads<=packed.logical_gets,"direct full counter products")?;
                need(packed.packet_capacity_peak_bytes==131072&&cache_budget==524288+packed.metadata_capacity_bytes
                    &&packed.cache_capacity_peak_bytes<=cache_budget,"direct full packed capacities")?;
                need(stats.prefix_full==32*MIB&&stats.prefix_suffix==4*MIB&&stats.prefix_patterns==8192&&stats.prefix_metadata<=1024&&stats.prefix_metadata>0
                    &&stats.banks<=96*MIB&&stats.x==32*MIB&&stats.row_lookup>0&&stats.row_lookup<=MIB
                    &&stats.u_weights==32*MIB&&stats.owner_weights==131072,"direct full owned capacities")?;
                need(stats.pass_ns.len()==42&&stats.pass_ns.iter().all(|n|*n>0),"direct full pass timings")?;
                let disjoint=[packed.load_ns,packed.decode_ns,packed.projection_ns,stats.prefix_build_ns,stats.message_ns,stats.line_ns]
                    .into_iter().try_fold(0u64,|a,b|a.checked_add(b)).ok_or("direct full timing overflow")?;
                need(disjoint<=producer_ns,"direct full disjoint timing")?;
                let left_digest=digest_counts(&stats.left_counts)?;let right_digest=digest_counts(&stats.right_counts)?;need(left_digest==LEFT&&right_digest==LEFT,"role6 endpoint count digests")?;
                let producer_peak=sum_cap(&[stats.prefix_full,stats.prefix_suffix,stats.prefix_patterns,stats.prefix_metadata,cache_budget,131072,
                    stats.banks,stats.x,stats.row_lookup,stats.u_weights,stats.owner_weights,16*MIB])?;
                let line_peak=sum_cap(&[32*MIB,32*MIB,32*MIB,MIB,cache_budget,stats.row_lookup,stats.u_weights,stats.owner_weights,16*MIB])?;
                let mle_peak=sum_cap(&[32*MIB,6*MIB,16*MIB,16*MIB])?;let component_peak=producer_peak.max(line_peak).max(mle_peak);
                need(component_peak<=512*MIB,"direct full component capacity")?;
                let(closed,_encoded)=adapter.close(&source,&proof,&claim,&prepared,&working,&mut caller,
                    &mut|s,b|trace.fixed(s,b),|bytes,verified,mle,verifier|{
                        trace.fixed("custody",true)?;residual::raw_hash(&raw).map_err(|e|format!("{e:?}"))?;
                        residual::packed_hash(&mut held).map_err(|e|format!("{e:?}"))?;
                        let raw_check=OpenOptions::new().read(true).share_mode(1).open(&raw_path).map_err(|e|e.to_string())?;
                        let packed_check=u0_open_bytes(&path)?;need(u0_file_info(&raw)?==raw_id&&u0_file_info(&raw_check)?==raw_id
                            &&u0_file_info(&held)?==id&&u0_file_info(&packed_check)?==id,"direct full final custody")?;adapter.require_source(&source)?;artifact_custody(&key)?;artifact_custody(&commitment)?;
                        trace.fixed("custody",false)?;need(trace.markers.get()==267,"direct full precomplete marker count")?;
                        let elapsed=clock(trace.start)?;let members:Vec<_>=(0..1).map(|tag|serde_json::json!({"tag":tag,"name":plan.descriptors()[6].ordered_tags[tag],
                            "stride_log":strides[tag],"terms":expected[tag].terms,"rows":expected[tag].rows})).collect();
                        let claim_point=verified.point.iter().map(|x|scalar(*x)).collect::<Result<Vec<_>,_>>()?;
                        let report=serde_json::json!({"schema":"native-role6-direct-full-v1","state":"ROLE6_DIRECT_FULL_PASS","stage":"complete","error":null,
                            "scope":{"role":6,"input_log":32,"row_log":24,"local_input_log":20,"slot_log":12,"base_row_log":12,"family_log":0,"owners":4096,
                                "active_headers":3073,"members":1,"deadline_seconds":3600,"component_limit_bytes":512*MIB,"job_limit_bytes":2048*MIB,
                                "strategy":"direct_prefix","loader_mode":"packed_owner_bits_lru4","incremental_u":false,"incremental_v":false,"full_u":true,"full_v":true,
                                "gkr":true,"pcs":false,"all_seven_roles":false,"production":false},
                            "inputs":{"raw_sha256":RAW_SHA,"raw_blake2b256":RAW_BLAKE,"witness_sha256":PACK_SHA,"witness_blake2b256":PACK_BLAKE,"verifier_key_sha256":screen_hex(&context.key_sha256_for_report()),
                                "commitment_sha256":screen_hex(&context.commitment_sha256_for_report()),"setup_id":screen_hex(&context.setup_id_for_report())},"members":members,
                            "census":{"left_terms":trace.census_terms[0].get(),"right_terms":trace.census_terms[1].get(),
                                "left_member_terms":trace.census.borrow()[0].to_vec(),"right_member_terms":trace.census.borrow()[1].to_vec(),
                                "left_counts_sha256":left_digest,"right_counts_sha256":right_digest},
                            "metrics":{"term_callbacks":stats.term_callbacks,"scalar_gets":packed.scalar_gets,"owner_requests":stats.owner_requests,"emitted_fields":stats.emitted_fields,
                                "full_expansions":packed.vector_expansions,"full_fields":packed.expanded_fields,"projections":packed.projection_calls,"projected_fields":packed.projection_fields,
                                "prefix_plans":stats.prefix_plans,"suffix_tables":stats.suffix_tables,"pattern_tables":stats.pattern_tables,"sequential_x_folds":stats.sequential_x_folds,
                                "sequential_bank_folds":stats.sequential_bank_folds,"input_vector_clones":stats.input_vector_clones,"line_internal_clones":stats.line_internal_clones,
                                "line_cloned_fields":stats.line_cloned_fields,"member_pass_checks":trace.member_checks.get()},
                            "adapter":{"source_emitter_calls":adapter_stats.source_emitter_calls,"canonical_callbacks":adapter_stats.canonical_callbacks,"selected_callbacks":adapter_stats.selected_callbacks,
                                "order_term_prevalidations":adapter_stats.order_term_prevalidations,"order_wire_prevalidations":adapter_stats.order_wire_prevalidations,
                                "metadata_term_prevalidations":adapter_stats.metadata_term_prevalidations,"adjacency_calls":adapter_stats.adjacency_calls,
                                "adjacency_wire_iterations":adapter_stats.adjacency_wire_iterations,"adjacency_wire_endpoint_checks":adapter_stats.adjacency_wire_endpoint_checks,
                                "prevalidation_mode":"source_derived_completed_calls"},
                            "packed":{"logical_gets":packed.logical_gets,"scalar_gets":packed.scalar_gets,"successful_loads":packed.successful_loads,"packed_bytes":packed.packed_bytes,
                                "vector_expansions":packed.vector_expansions,"expanded_fields":packed.expanded_fields,"load_ns":packed.load_ns,"decode_ns":packed.decode_ns,
                                "packet_capacity_peak_bytes":packed.packet_capacity_peak_bytes,"cache_capacity_peak_bytes":packed.cache_capacity_peak_bytes,"metadata_capacity_bytes":packed.metadata_capacity_bytes,
                                "projection_calls":packed.projection_calls,"projection_fields":packed.projection_fields,"projection_ns":packed.projection_ns},
                            "capacity":{"prefix_full":stats.prefix_full,"prefix_suffix":stats.prefix_suffix,"prefix_patterns":stats.prefix_patterns,"prefix_metadata":stats.prefix_metadata,
                                "cache_budget":cache_budget,"loader_packet":131072,"banks":stats.banks,"x":stats.x,"row_lookup":stats.row_lookup,"u_weights":stats.u_weights,
                                "owner_weights":stats.owner_weights,"control_reserve":16*MIB,"line_x":32*MIB,"line_clone":32*MIB,"line_next":32*MIB,"line_small":MIB,
                                "producer_peak_bound":producer_peak,"line_peak_bound":line_peak,"mle_batch_bound":32*MIB,"mle_vectors_bound":6*MIB,"mle_helper_reserve":16*MIB,
                                "mle_peak_bound":mle_peak,"component_peak_bound":component_peak},
                            "proof":{"bytes":bytes.len(),"sha256":screen_hex(&crate::native_prefix_auth_plan::role0_sha256(bytes)?),"layers":proof.layers.len(),"rounds":proof.layers[0].rounds.len(),"round_coefficients":3,
                                "line_coefficients":proof.layers[0].line_coefficients.len(),"canonical":true},
                            "claim":{"point":claim_point,"value":scalar(verified.value)?,"source_mle":scalar(mle)?,"equal":true},
                            "transcript":{"initial_counters":initial,"prover_counters":counters(&working),"verifier_counters":counters(verifier),
                                "prover_continuation":scalar(working.clone().challenge_scalar(NEXT))?,"verifier_continuation":scalar(verifier.clone().challenge_scalar(NEXT))?,"equal":true},
                            "timing":{"fixed_ns":*trace.fixed_ns.borrow(),"census_ns":stats.census_ns,"pass_ns":stats.pass_ns,"high_ns":stats.high_ns,"producer_ns":producer_ns,
                                "prefix_build_ns":stats.prefix_build_ns,"message_ns":stats.message_ns,"line_ns":stats.line_ns,"total_ns":elapsed},
                            "checks":{"ordinary":true,"admission":true,"census":true,"all_reads":true,"member_counts":true,"projection":true,"codec":true,
                                "verification":true,"source_mle":true,"transcript":true,"custody":true,"rollback":true},"elapsed_ns":elapsed});
                        let mut writer=Writer::new()?;serde_json::to_writer(&mut writer,&report).map_err(|e|e.to_string())?;
                        let hex:String=bytes.iter().map(|b|format!("{b:02x}")).collect();need(hex.len()==14528,"direct full proof hex extent")?;
                        clock(trace.start)?;Ok(Closed{report:writer.bytes,hex,elapsed})
                    })?;Ok(closed)
            }
            #[test]
            fn ordinary_boundaries(){
                artifact_opener_controls().unwrap();
                edge::direct_edge_boundaries_for_test();edge::packed_edge_input_boundaries_for_test();
                producer_failures();
                crate::header_metadata_order_layout::role6_endpoint_controls_for_test();
                crate::native_prefix_auth_plan::role6_full_controls_for_test().unwrap();
                let counts=crate::header_metadata_order_layout::HeaderMetadataOrderLayout::compile(3073,12,1562018269889).unwrap();
                assert_eq!(counts.term_count(),7181857);assert_eq!((counts.input_log(),counts.row_log()),(32,24));
                for stage in ["admission","census_right","u_terminal","v_terminal","complete","hold"]{
                    assert!(Trace::line(stage,b'p',20,4096,TOTAL,3_600_000_000_000).unwrap().len()<=112);}
                assert!(268*112+14528+64+REPORT+64+2048<65536);
                println!("\nNATIVE_ROLE6_COUNTS_REPORT {}",serde_json::json!({"schema":"native-role6-counts-v1","state":"COUNT_APIS_PASS",
                    "input_log":32,"row_log":24,"owners":4096,"active_headers":3073,"canonical_terms":7181857,
                    "occupied_rows":6499651,"nonlinear_terms":3933440,"count_only":true,"native_inputs":false}));
            }
            fn producer_failures(){
                struct Input<'a>{stage:&'a Cell<&'static str>,line_fault:bool}
                impl EdgeInput for Input<'_>{fn width(&self)->usize{8}fn owners(&self)->usize{4}
                    fn value(&mut self,_:usize,_:usize)->Result<Fr,String>{Ok(Fr::zero())}
                    fn vector(&mut self,owner:usize)->Result<Vec<Fr>,String>{if self.line_fault&&self.stage.get()=="line"&&owner==2{
                        Err("role6 isolated line read".into())}else{Ok(vec![Fr::zero();8])}}
                    fn capacity_bytes(&self)->Option<usize>{Some(0)}fn cache_budget_bytes(&self)->Result<usize,String>{Ok(0)}fn vector_clone_increment(&self)->u64{0}}
                for fault in ["u_high","v_high","line","line_read"]{let stage=Cell::new("start");let mut input=Input{stage:&stage,line_fault:fault=="line_read"};
                    let caller=Transcript::new(b"role6-producer-fault-fixture");let before=counters(&caller);let mut working=caller.clone();let reached=Cell::new(false);
                    let result=edge::prove_edge_terms_strategy_for_test(3,2,0,0,&[0],true,true,true,0,&mut input,
                        |_,owner,sink|sink(edge::EdgeTerm{source_slot:owner,family_row:0,term:crate::sparse::Term{row:owner,
                            gate:crate::gkr::Gate{left:owner*8,right:owner*8,c0:Fr::zero(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}}}),
                        &mut working,|_|{},|_,_,_|Ok([Fr::zero();4]),&mut|e|{stage.set(e.stage);if e.stage==fault&&e.event==b'b'{reached.set(true);return Err(format!("role6 isolated {fault}"));}Ok(())});
                    let expected=if fault=="line_read"{"role6 isolated line read".into()}else{format!("role6 isolated {fault}")};
                    assert_eq!(result.err().as_deref(),Some(expected.as_str()));assert!(fault=="line_read"||reached.get());assert_eq!(counters(&caller),before);
                }
            }
            #[test]
            #[ignore="one full native role6 direct-prefix proof; reviewed3600s/R4/Job2GiB controller required"]
            fn native_role6_direct_full_bounded(){
                let trace=Trace::new();let result=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||run(&trace))).unwrap_or_else(|_|Err("direct full panic".into()));
                match result{Ok(out)=>{
                    // All semantic checks and report/hex preparation precede this boundary.
                    trace.emit_at("complete",b'e',0,4096,TOTAL,out.elapsed).unwrap();
                    let mut stdout=std::io::stdout().lock();stdout.write_all(b"\nNATIVE_ROLE6_DIRECT_FULL_PROOF ").unwrap();stdout.write_all(out.hex.as_bytes()).unwrap();
                    stdout.write_all(b"\n\nNATIVE_ROLE6_DIRECT_FULL_REPORT ").unwrap();stdout.write_all(&out.report).unwrap();stdout.write_all(b"\n").unwrap();stdout.flush().unwrap();
                },Err(error)=>{
                    if trace.markers.get()<268{let _=trace.emit_at("hold",b'e',trace.round.get(),trace.owner.get(),trace.terms.get(),screen_ns(trace.start));}
                    let code:String=error.chars().map(|c|if c.is_ascii(){c}else{'_'}).take(256).collect();
                    let report=serde_json::to_vec(&serde_json::json!({"schema":"native-role6-direct-full-v1","state":"HOLD","stage":trace.stage.get(),
                        "error":{"code":code,"round":trace.round.get(),"owner":trace.owner.get(),"row":trace.row.get(),"completed_terms":trace.terms.get(),
                            "completed_callbacks":trace.callbacks.get(),"substage":trace.substage.get()},"elapsed_ns":screen_ns(trace.start)})).unwrap();
                    assert!(report.len()<=REPORT);let mut stdout=std::io::stdout().lock();stdout.write_all(b"\nNATIVE_ROLE6_DIRECT_FULL_REPORT ").unwrap();
                    stdout.write_all(&report).unwrap();stdout.write_all(b"\n").unwrap();stdout.flush().unwrap();drop(stdout);panic!("native direct full HOLD");
                }}
            }
        }
// source28-role6-child-END

#[cfg(test)]
mod role2_endpoint_probe {
    // source24-role2-u0-child-BEGIN
    mod u_rounds {
        // source26-direct-full-child-BEGIN
        mod direct_full{
            use super::*;
            use crate::sparse_stream_roster::EdgeInput;
            const DOMAIN:&[u8]=b"native-prefix-role2-direct-full-diagnostic-v1";
            const NEXT:&[u8]=b"native-role2-direct-full-continuation-v1";
            const TOTAL:u64=5_688_205_600;
            const FIXED:[&str;8]=["admission","plan","binding","wiring","codec","verify","mle","custody"];
            fn clock(start:Instant)->Result<u64,String>{let n=u64::try_from(start.elapsed().as_nanos()).map_err(|_|"direct full clock")?;
                need(n<=3_600_000_000_000,"direct full deadline")?;Ok(n)}
            fn sum_cap(values:&[usize])->Result<usize,String>{values.iter().try_fold(0usize,|a,b|a.checked_add(*b)).ok_or("direct full capacity overflow".into())}
            struct Trace{start:Instant,stage:Cell<&'static str>,round:Cell<usize>,owner:Cell<usize>,row:Cell<usize>,terms:Cell<u64>,callbacks:Cell<u64>,
                substage:Cell<&'static str>,markers:Cell<usize>,census_mode:Cell<bool>,census:RefCell<[[u64;40];2]>,census_terms:[Cell<u64>;2],
                current:RefCell<[u64;40]>,current_terms:Cell<u64>,member_checks:Cell<u64>,fixed_begin:RefCell<[u64;8]>,fixed_ns:RefCell<[u64;8]>}
            impl Trace{
                fn new()->Self{Self{start:Instant::now(),stage:Cell::new("admission"),round:Cell::new(0),owner:Cell::new(0),row:Cell::new(0),terms:Cell::new(0),callbacks:Cell::new(0),
                    substage:Cell::new("admission"),markers:Cell::new(0),census_mode:Cell::new(false),census:RefCell::new([[0;40];2]),census_terms:[Cell::new(0),Cell::new(0)],
                    current:RefCell::new([0;40]),current_terms:Cell::new(0),member_checks:Cell::new(0),fixed_begin:RefCell::new([0;8]),fixed_ns:RefCell::new([0;8])}}
                fn line(stage:&str,event:u8,round:usize,owners:usize,terms:u64,n:u64)->Result<String,String>{
                    let line=format!("NATIVE_ROLE2_DIRECT_FULL_STAGE {stage} {} {round} {owners} {terms} {n}\n",event as char);
                    need(line.len()<=112,"direct full marker bound")?;Ok(line)}
                fn emit_at(&self,stage:&str,event:u8,round:usize,owners:usize,terms:u64,n:u64)->Result<(),String>{
                    need(self.markers.get()<268,"direct full marker count")?;let line=Self::line(stage,event,round,owners,terms,n)?;
                    let mut out=std::io::stderr().lock();out.write_all(line.as_bytes()).map_err(|e|e.to_string())?;out.flush().map_err(|e|e.to_string())?;
                    self.markers.set(self.markers.get()+1);Ok(())}
                fn fixed(&self,stage:&'static str,begin:bool)->Result<(),String>{let index=FIXED.iter().position(|s|*s==stage).ok_or("direct full fixed stage")?;
                    self.stage.set(stage);self.substage.set(stage);self.round.set(0);self.owner.set(0);self.row.set(0);self.terms.set(0);
                    let n=clock(self.start)?;if begin{self.fixed_begin.borrow_mut()[index]=n;}else{
                        self.fixed_ns.borrow_mut()[index]=n.checked_sub(self.fixed_begin.borrow()[index]).ok_or("direct full fixed clock")?;}
                    self.emit_at(stage,if begin{b'b'}else{b'e'},0,0,0,n)}
                fn event(&self,e:edge::EdgeFullEvent,expected:&[residual::Count;40])->Result<(),String>{
                    self.stage.set(e.stage);self.round.set(e.round);self.terms.set(e.terms);
                    if e.event==b'b'{self.owner.set(0);self.row.set(0);self.substage.set(if e.stage.ends_with("high"){"high_internal_unknown"}else{"kernel"});
                        self.census_mode.set(e.stage.starts_with("census"));
                        if !self.census_mode.get(){*self.current.borrow_mut()=[0;40];self.current_terms.set(0);}}
                    if e.event==b'p'&&e.owners>0{
                        if e.stage.starts_with("census"){let side=usize::from(e.stage=="census_right");need(self.census_terms[side].get()==e.terms,"direct full census progress")?;
                            if e.owners==4096{member_check(&self.census.borrow()[side],expected)?;self.member_checks.set(plus(self.member_checks.get(),40)?);}}
                        else if e.stage!="line"{need(self.current_terms.get()==e.terms,"direct full pass progress")?;
                            if e.owners==4096{member_check(&self.current.borrow(),expected)?;self.member_checks.set(plus(self.member_checks.get(),40)?);}}
                    }
                    if e.stage.ends_with("high")&&e.event==b'p'{self.substage.set("confirmed_after_return");}
                    if e.stage=="wiring"{return self.fixed("wiring",e.event==b'b');}
                    self.emit_at(e.stage,e.event,e.round,e.owners,e.terms,clock(self.start)?)}
                fn term(&self,left:bool,tag:usize)->Result<(),String>{
                    self.callbacks.set(plus(self.callbacks.get(),1)?);
                    if self.census_mode.get(){let side=usize::from(!left);let mut c=self.census.borrow_mut();c[side][tag]=plus(c[side][tag],1)?;
                        self.census_terms[side].set(plus(self.census_terms[side].get(),1)?);self.terms.set(self.census_terms[side].get());}
                    else{let mut c=self.current.borrow_mut();c[tag]=plus(c[tag],1)?;self.current_terms.set(plus(self.current_terms.get(),1)?);self.terms.set(self.current_terms.get());}Ok(())}
            }
            struct Closed{report:Vec<u8>,hex:String,elapsed:u64}
            fn run(trace:&Trace)->Result<Closed,String>{
                trace.fixed("admission",true)?;let(raw,raw_id,raw_path)=residual::raw_hold().map_err(|e|format!("{e:?}"))?;
                let path=std::path::PathBuf::from(std::env::var_os("NIPOPOW_NATIVE_U_SEQUENCE_WITNESS").ok_or("direct full witness env")?);
                let(source,mut held,id)=useq_admit()?;trace.fixed("admission",false)?;trace.fixed("plan",true)?;
                let native=input();let candidate=crate::native_prefix_auth_plan::Candidate{n:3073,root:native.root(),total:native.total_be28(),
                    tip:ergo_header_core::blake2b256(native.raw(3073)?),tip_time:native.timestamp(3073)?};
                let parent=WorkTreeHistoryPlan::compile(3073,12,candidate.root,candidate.total)?;drop(native);
                let plan=NativePrefixAuthPlan::compile(&parent,Selection::s12(),candidate)?;
                let adapter=plan.role2_endpoints(&source,&mut held,trace.start)?;
                let(expected,strides)=residual::expectations(&parent,&plan).map_err(|e|format!("{e:?}"))?;
                let mut cache=edge::PackedEdgeInput::new(WIDTH,4096,|owner|{clock(trace.start)?;trace.owner.set(owner);trace.substage.set("load");
                    let view=source.native_role0_view()?;view.require_same_source(&source)?;let packet=view.read_copy(owner)?;
                    need(packet.len()==WIDTH&&packet.capacity_bytes()==131072,"direct full loader packet")?;trace.substage.set("kernel");Ok(packet.into_bytes())})?;
                edge::edge_input_geometry(&cache,WIDTH,4096)?;let cache_budget=cache.cache_budget_bytes()?;
                need(cache.metrics().metadata_capacity_bytes<=4096,"direct full cache metadata")?;trace.fixed("plan",false)?;
                trace.fixed("binding",true)?;let mut caller=Transcript::new(DOMAIN);let tuples=std::array::from_fn(|i|(expected[i].terms,expected[i].rows));
                let prepared=plan.prepare_role2_full_binding_for_test(&caller,&tuples,&strides)?;let initial=counters(&prepared);let mut working=caller.clone();
                trace.fixed("binding",false)?;let began=Instant::now();
                let(proof,claim,iu,iv,stats)=edge::prove_edge_terms_strategy_for_test(20,12,14,6,&strides,true,true,true,0,&mut cache,
                    |left,owner,sink|{if trace.census_mode.get(){trace.stage.set(if left{"census_left"}else{"census_right"});}
                        trace.owner.set(owner);trace.substage.set("kernel");adapter.visit(left,owner,&mut|e|{
                            trace.row.set(e.term.row);let tag=check_edge(&e,left,owner,&strides)?;sink(e)?;trace.term(left,tag)?;
                            if trace.callbacks.get()%65536==0{clock(trace.start)?;}Ok(())})},
                    &mut working,|t|*t=prepared.clone(),|r,u,v|plan.coefficients(2,r,u,v),&mut|e|trace.event(e,&expected))?;
                let producer_ns=u64::try_from(began.elapsed().as_nanos()).map_err(|_|"direct full producer clock")?;
                let packed=cache.metrics();drop(cache);
                need(!iu&&!iv&&stats.term_callbacks==TOTAL&&trace.callbacks.get()==TOTAL&&trace.member_checks.get()==1760,"direct full callback coverage")?;
                need(stats.owner_requests==176128&&stats.emitted_fields==21474828288&&stats.prefix_plans==42&&stats.suffix_tables==36&&stats.pattern_tables==40,
                    "direct full projection counts")?;
                need(stats.sequential_x_folds==0&&stats.sequential_bank_folds==0&&stats.input_vector_clones==0&&stats.line_internal_clones==4096
                    &&stats.line_cloned_fields==4294967296,"direct full folds/clones")?;
                need(packed.scalar_gets==2714825400&&packed.logical_gets==2715001528&&packed.vector_expansions==12288&&packed.expanded_fields==12884901888
                    &&packed.projection_calls==163840&&packed.projection_fields==8589926400,"direct full packed operation counts")?;
                need(packed.logical_gets==plus(packed.scalar_gets,stats.owner_requests)?&&stats.emitted_fields==plus(packed.expanded_fields,packed.projection_fields)?
                    &&packed.packed_bytes==times(packed.successful_loads,131072)?&&packed.successful_loads>0&&packed.successful_loads<=packed.logical_gets,"direct full counter products")?;
                need(packed.packet_capacity_peak_bytes==131072&&cache_budget==524288+packed.metadata_capacity_bytes
                    &&packed.cache_capacity_peak_bytes<=cache_budget,"direct full packed capacities")?;
                need(stats.prefix_full==32*MIB&&stats.prefix_suffix==4*MIB&&stats.prefix_patterns==8192&&stats.prefix_metadata<=1024&&stats.prefix_metadata>0
                    &&stats.banks<=96*MIB&&stats.x==32*MIB&&stats.row_lookup>0&&stats.row_lookup<=MIB
                    &&stats.u_weights==32*MIB&&stats.owner_weights==131072,"direct full owned capacities")?;
                need(stats.pass_ns.len()==42&&stats.pass_ns.iter().all(|n|*n>0),"direct full pass timings")?;
                let disjoint=[packed.load_ns,packed.decode_ns,packed.projection_ns,stats.prefix_build_ns,stats.message_ns,stats.line_ns]
                    .into_iter().try_fold(0u64,|a,b|a.checked_add(b)).ok_or("direct full timing overflow")?;
                need(disjoint<=producer_ns,"direct full disjoint timing")?;
                let left_digest=digest_counts(&stats.left_counts)?;let right_digest=digest_counts(&stats.right_counts)?;need(left_digest==LEFT,"direct full LEFT digest")?;
                let producer_peak=sum_cap(&[stats.prefix_full,stats.prefix_suffix,stats.prefix_patterns,stats.prefix_metadata,cache_budget,131072,
                    stats.banks,stats.x,stats.row_lookup,stats.u_weights,stats.owner_weights,16*MIB])?;
                let line_peak=sum_cap(&[32*MIB,32*MIB,32*MIB,MIB,cache_budget,stats.row_lookup,stats.u_weights,stats.owner_weights,16*MIB])?;
                let mle_peak=sum_cap(&[32*MIB,6*MIB,16*MIB,16*MIB])?;let component_peak=producer_peak.max(line_peak).max(mle_peak);
                need(component_peak<=512*MIB,"direct full component capacity")?;
                let(closed,_encoded)=plan.close_role2_full_for_test(&source,&proof,&claim,&prepared,&working,&mut caller,
                    &mut|s,b|trace.fixed(s,b),|bytes,verified,mle,verifier|{
                        trace.fixed("custody",true)?;residual::raw_hash(&raw).map_err(|e|format!("{e:?}"))?;
                        residual::packed_hash(&mut held).map_err(|e|format!("{e:?}"))?;
                        let raw_check=OpenOptions::new().read(true).share_mode(1).open(&raw_path).map_err(|e|e.to_string())?;
                        let packed_check=u0_open_bytes(&path)?;need(u0_file_info(&raw)?==raw_id&&u0_file_info(&raw_check)?==raw_id
                            &&u0_file_info(&held)?==id&&u0_file_info(&packed_check)?==id,"direct full final custody")?;adapter.require_source(&source)?;
                        trace.fixed("custody",false)?;need(trace.markers.get()==267,"direct full precomplete marker count")?;
                        let elapsed=clock(trace.start)?;let members:Vec<_>=(0..40).map(|tag|serde_json::json!({"tag":tag,"name":plan.descriptors()[2].ordered_tags[tag],
                            "stride_log":strides[tag],"terms":expected[tag].terms,"rows":expected[tag].rows})).collect();
                        let claim_point=verified.point.iter().map(|x|scalar(*x)).collect::<Result<Vec<_>,_>>()?;
                        let report=serde_json::json!({"schema":"native-role2-direct-full-v1","state":"ROLE2_DIRECT_FULL_PASS","stage":"complete","error":null,
                            "scope":{"role":2,"input_log":32,"row_log":32,"local_input_log":20,"slot_log":12,"base_row_log":14,"family_log":6,"owners":4096,
                                "active_headers":3073,"members":40,"deadline_seconds":3600,"component_limit_bytes":512*MIB,"job_limit_bytes":2048*MIB,
                                "strategy":"direct_prefix","loader_mode":"packed_owner_bits_lru4","incremental_u":false,"incremental_v":false,"full_u":true,"full_v":true,
                                "gkr":true,"pcs":false,"all_seven_roles":false,"production":false},
                            "inputs":{"raw_sha256":RAW_SHA,"raw_blake2b256":RAW_BLAKE,"witness_sha256":PACK_SHA,"witness_blake2b256":PACK_BLAKE},"members":members,
                            "census":{"left_terms":trace.census_terms[0].get(),"right_terms":trace.census_terms[1].get(),
                                "left_member_terms":trace.census.borrow()[0].to_vec(),"right_member_terms":trace.census.borrow()[1].to_vec(),
                                "left_counts_sha256":left_digest,"right_counts_sha256":right_digest},
                            "metrics":{"term_callbacks":stats.term_callbacks,"scalar_gets":packed.scalar_gets,"owner_requests":stats.owner_requests,"emitted_fields":stats.emitted_fields,
                                "full_expansions":packed.vector_expansions,"full_fields":packed.expanded_fields,"projections":packed.projection_calls,"projected_fields":packed.projection_fields,
                                "prefix_plans":stats.prefix_plans,"suffix_tables":stats.suffix_tables,"pattern_tables":stats.pattern_tables,"sequential_x_folds":stats.sequential_x_folds,
                                "sequential_bank_folds":stats.sequential_bank_folds,"input_vector_clones":stats.input_vector_clones,"line_internal_clones":stats.line_internal_clones,
                                "line_cloned_fields":stats.line_cloned_fields,"member_pass_checks":trace.member_checks.get()},
                            "packed":{"logical_gets":packed.logical_gets,"scalar_gets":packed.scalar_gets,"successful_loads":packed.successful_loads,"packed_bytes":packed.packed_bytes,
                                "vector_expansions":packed.vector_expansions,"expanded_fields":packed.expanded_fields,"load_ns":packed.load_ns,"decode_ns":packed.decode_ns,
                                "packet_capacity_peak_bytes":packed.packet_capacity_peak_bytes,"cache_capacity_peak_bytes":packed.cache_capacity_peak_bytes,"metadata_capacity_bytes":packed.metadata_capacity_bytes,
                                "projection_calls":packed.projection_calls,"projection_fields":packed.projection_fields,"projection_ns":packed.projection_ns},
                            "capacity":{"prefix_full":stats.prefix_full,"prefix_suffix":stats.prefix_suffix,"prefix_patterns":stats.prefix_patterns,"prefix_metadata":stats.prefix_metadata,
                                "cache_budget":cache_budget,"loader_packet":131072,"banks":stats.banks,"x":stats.x,"row_lookup":stats.row_lookup,"u_weights":stats.u_weights,
                                "owner_weights":stats.owner_weights,"control_reserve":16*MIB,"line_x":32*MIB,"line_clone":32*MIB,"line_next":32*MIB,"line_small":MIB,
                                "producer_peak_bound":producer_peak,"line_peak_bound":line_peak,"mle_batch_bound":32*MIB,"mle_vectors_bound":6*MIB,"mle_helper_reserve":16*MIB,
                                "mle_peak_bound":mle_peak,"component_peak_bound":component_peak},
                            "proof":{"bytes":bytes.len(),"sha256":screen_hex(&crate::native_prefix_auth_plan::role0_sha256(bytes)?),"layers":proof.layers.len(),"rounds":proof.layers[0].rounds.len(),"round_coefficients":3,
                                "line_coefficients":proof.layers[0].line_coefficients.len(),"canonical":true},
                            "claim":{"point":claim_point,"value":scalar(verified.value)?,"source_mle":scalar(mle)?,"equal":true},
                            "transcript":{"initial_counters":initial,"prover_counters":counters(&working),"verifier_counters":counters(verifier),
                                "prover_continuation":scalar(working.clone().challenge_scalar(NEXT))?,"verifier_continuation":scalar(verifier.clone().challenge_scalar(NEXT))?,"equal":true},
                            "timing":{"fixed_ns":*trace.fixed_ns.borrow(),"census_ns":stats.census_ns,"pass_ns":stats.pass_ns,"high_ns":stats.high_ns,"producer_ns":producer_ns,
                                "prefix_build_ns":stats.prefix_build_ns,"message_ns":stats.message_ns,"line_ns":stats.line_ns,"total_ns":elapsed},
                            "checks":{"ordinary":true,"admission":true,"census":true,"all_reads":true,"member_counts":true,"projection":true,"codec":true,
                                "verification":true,"source_mle":true,"transcript":true,"custody":true,"rollback":true},"elapsed_ns":elapsed});
                        let mut writer=Writer::new()?;serde_json::to_writer(&mut writer,&report).map_err(|e|e.to_string())?;
                        let hex:String=bytes.iter().map(|b|format!("{b:02x}")).collect();need(hex.len()==14528,"direct full proof hex extent")?;
                        clock(trace.start)?;Ok(Closed{report:writer.bytes,hex,elapsed})
                    })?;Ok(closed)
            }
            #[test]
            fn ordinary_boundaries(){
                edge::direct_edge_boundaries_for_test();crate::native_prefix_auth_plan::role2_full_binding_controls_for_test().unwrap();
                crate::native_prefix_auth_plan::role2_full_transaction_controls_for_test().unwrap();
                for stage in ["admission","census_right","u_terminal","v_terminal","complete","hold"]{
                    assert!(Trace::line(stage,b'p',20,4096,TOTAL,3_600_000_000_000).unwrap().len()<=112);}
                assert!(268*112+14528+64+REPORT+64+2048<65536);
                edge::packed_edge_input_boundaries_for_test();super::ordinary_boundaries();
            }
            #[test]
            #[ignore="one full native role2 direct-prefix proof; reviewed3600s/R4/Job2GiB controller required"]
            fn native_role2_direct_full_bounded(){
                let trace=Trace::new();let result=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||run(&trace))).unwrap_or_else(|_|Err("direct full panic".into()));
                match result{Ok(out)=>{
                    // All semantic checks and report/hex preparation precede this boundary.
                    trace.emit_at("complete",b'e',0,4096,TOTAL,out.elapsed).unwrap();
                    let mut stdout=std::io::stdout().lock();stdout.write_all(b"\nNATIVE_ROLE2_DIRECT_FULL_PROOF ").unwrap();stdout.write_all(out.hex.as_bytes()).unwrap();
                    stdout.write_all(b"\n\nNATIVE_ROLE2_DIRECT_FULL_REPORT ").unwrap();stdout.write_all(&out.report).unwrap();stdout.write_all(b"\n").unwrap();stdout.flush().unwrap();
                },Err(error)=>{
                    if trace.markers.get()<268{let _=trace.emit_at("hold",b'e',trace.round.get(),trace.owner.get(),trace.terms.get(),screen_ns(trace.start));}
                    let code:String=error.chars().map(|c|if c.is_ascii(){c}else{'_'}).take(256).collect();
                    let report=serde_json::to_vec(&serde_json::json!({"schema":"native-role2-direct-full-v1","state":"HOLD","stage":trace.stage.get(),
                        "error":{"code":code,"round":trace.round.get(),"owner":trace.owner.get(),"row":trace.row.get(),"completed_terms":trace.terms.get(),
                            "completed_callbacks":trace.callbacks.get(),"substage":trace.substage.get()},"elapsed_ns":screen_ns(trace.start)})).unwrap();
                    assert!(report.len()<=REPORT);let mut stdout=std::io::stdout().lock();stdout.write_all(b"\nNATIVE_ROLE2_DIRECT_FULL_REPORT ").unwrap();
                    stdout.write_all(&report).unwrap();stdout.write_all(b"\n").unwrap();stdout.flush().unwrap();drop(stdout);panic!("native direct full HOLD");
                }}
            }
        }
        // source26-direct-full-child-END
        // source25-packed-input-child-BEGIN
        mod packed_input {
            use super::*;
            #[derive(Serialize)]struct Packed{logical_gets:u64,scalar_gets:u64,successful_loads:u64,packed_bytes:u64,
                vector_expansions:u64,expanded_fields:u64,load_ns:u64,decode_ns:u64,
                packet_capacity_peak_bytes:usize,cache_capacity_peak_bytes:usize,metadata_capacity_bytes:usize}
            impl From<edge::PackedEdgeMetrics> for Packed{fn from(m:edge::PackedEdgeMetrics)->Self{Self{
                logical_gets:m.logical_gets,scalar_gets:m.scalar_gets,successful_loads:m.successful_loads,packed_bytes:m.packed_bytes,
                vector_expansions:m.vector_expansions,expanded_fields:m.expanded_fields,load_ns:m.load_ns,decode_ns:m.decode_ns,
                packet_capacity_peak_bytes:m.packet_capacity_peak_bytes,cache_capacity_peak_bytes:m.cache_capacity_peak_bytes,metadata_capacity_bytes:m.metadata_capacity_bytes}}}
            #[derive(Serialize)]struct Candidate{owners:usize,terms:u64,#[serde(serialize_with="forty")]member_terms:[u64;40],metrics:Metrics,packed:Packed}
            #[derive(Serialize)]struct PackedReport<'a>{schema:&'static str,state:&'static str,stage:&'static str,error:Option<&'a str>,scope:Scope,inputs:Inputs,members:&'a[Member<'a>],
                census:Census,candidate:Candidate,oracle:Oracle,capacity:Capacity,polynomial:Polynomial,sender:Sender,timing:Timing,checks:Checks,elapsed_ns:u64}
            fn emit(stage:&str,owners:usize,terms:u64,ns:u64)->Result<(),String>{
                let mut out=std::io::stderr().lock();writeln!(out,"NATIVE_ROLE2_PACKED_U0_STAGE stage={stage} owners={owners} terms={terms} elapsed_ns={ns}")
                    .map_err(|e|e.to_string())?;out.flush().map_err(|e|e.to_string())}
            struct Timeline{first:[u64;10]}
            impl Timeline{fn enter(&mut self,index:usize,start:Instant,pos:&Position)->Result<(),String>{
                    pos.reset(STAGES[index]);let n=clock(start)?;self.first[index]=n;
                    emit(STAGES[index],if index>=7{4096}else{0},if index>=7{T}else{0},n)}
                fn timing(&self)->Result<Timing,String>{super::Timeline{first:self.first}.timing()}}
            fn baseline(poly:[Fr;3],sender:&Sender)->Result<(),String>{
                need(triples(poly)?==["657440b3c062528dbe48250c9f686f73a818e2086c42329d62609f75ac63e406",
                    "4926b86aefc20f74a5fef27b211ffbce6d27da4e91f9d2f7a25a8915ae0f1010",
                    "eef0c61e236d2db56ee07be5e8f759729effe2204dc71886c18469e06b778b12"],"packed U0 source24 coefficient baseline")?;
                need(sender.initial_counters==[32,40,102061]&&sender.candidate_counters==[33,41,102421]
                    &&sender.reference_counters==[33,41,102421],"packed U0 source24 sender counters")?;
                for(actual,expected)in [(&sender.candidate_challenge,"ec99ae7a61882ae8887c79313254225bbdae2cefca39caa99a0860693373de06"),
                    (&sender.reference_challenge,"ec99ae7a61882ae8887c79313254225bbdae2cefca39caa99a0860693373de06"),
                    (&sender.candidate_claim,"5ab6a3e8dcc84a8e7c99412ee28ee835d1cd24388fc0999bb25221b6e843bf00"),
                    (&sender.reference_claim,"5ab6a3e8dcc84a8e7c99412ee28ee835d1cd24388fc0999bb25221b6e843bf00"),
                    (&sender.candidate_continuation,"39e1b80f9bb279b24371ae3e4e950ff7d27f671616a192d7f286523e0e076b17"),
                    (&sender.reference_continuation,"39e1b80f9bb279b24371ae3e4e950ff7d27f671616a192d7f286523e0e076b17")]{
                    need(actual==expected,"packed U0 source24 sender scalar baseline")?;}Ok(())
            }
    fn run(start:Instant,stage:&mut &'static str,pos:&Position)->Result<Vec<u8>,String>{
        let mut line=Timeline{first:[0;10]};line.enter(0,start,pos)?;
        let(raw,raw_id,raw_path)=residual::raw_hold().map_err(|e|format!("{e:?}"))?;
        let path=std::path::PathBuf::from(std::env::var_os("NIPOPOW_NATIVE_U_SEQUENCE_WITNESS").ok_or("U0 witness env")?);
        let(source,mut held,id)=useq_admit()?;
        *stage="plan";line.enter(1,start,pos)?;let native=input();let candidate=crate::native_prefix_auth_plan::Candidate{n:3073,root:native.root(),total:native.total_be28(),
        tip:ergo_header_core::blake2b256(native.raw(3073)?),tip_time:native.timestamp(3073)?};
        let parent=WorkTreeHistoryPlan::compile(3073,12,candidate.root,candidate.total)?;drop(native);
        let plan=NativePrefixAuthPlan::compile(&parent,Selection::s12(),candidate)?;let adapter=plan.role2_endpoints(&source,&mut held,start)?;
        let mut packed_input=edge::PackedEdgeInput::new(WIDTH,4096,|owner|{
            clock(start)?;let view=source.native_role0_view()?;view.require_same_source(&source)?;
            let packet=view.read_copy(owner)?;need(packet.len()==WIDTH&&packet.capacity_bytes()==131072,"packed U0 admitted packet")?;
            Ok(packet.into_bytes())
        })?;
        edge::edge_input_geometry(&packed_input,WIDTH,4096)?;
        need(packed_input.metrics().metadata_capacity_bytes<=4096,"packed U0 metadata bound")?;
        *stage="counts";line.enter(2,start,pos)?;let(expected,strides)=residual::expectations(&parent,&plan).map_err(|e|format!("{e:?}"))?;
        // Before generic allocations: fixed maximum simultaneous source model.
        need(524288+4096+32*MIB+96*MIB+MIB+131072+16*MIB<=COMPONENT,"packed U0 candidate preflight")?;
        let census=RefCell::new(Counted::default());*stage="census";line.enter(3,start,pos)?;
        let counts=edge::edge_u0_census_for_test(20,12,14,&strides,
        |left,owner,sink|{need(left&&owner==census.borrow().owners,"U0 census ordered owner")?;pos.owner.set(owner);pos.owner_terms.set(0);
            adapter.visit(left,owner,&mut|e|{let tag=check_edge(&e,left,owner,&strides)?;let row=e.term.row;pos.row.set(row);sink(e)?;
            census.borrow_mut().term(tag)?;pos.term(row)?;if pos.owner_terms.get()%65536==0{clock(start)?;}Ok(())})},
        |owners,terms|{let mut c=census.borrow_mut();need(owners==c.owners+1&&terms==c.terms,"U0 census progress")?;c.owners=owners;
            pos.owners.set(owners);clock(start)?;if owners%256==0{emit("census",owners,terms,clock(start)?)?;}Ok(())})?;
        let census=census.into_inner();need(counts.len()==4096&&counts.capacity()<=4096&&census.owners==4096&&census.terms==T,"U0 full census")?;
        member_check(&census.members,&expected)?;let digest=digest_counts(&counts)?;need(digest==LEFT,"U0 fixed LEFT digest")?;
        *stage="binding";line.enter(4,start,pos)?;let(pre,r)=binding(&plan,&expected,&strides,&digest)?;
        need(r.capacity()<=32,"U0 row point capacity")?;
        let observed=RefCell::new(Counted::default());let prefix=Cell::new(0u64);
        *stage="candidate";line.enter(5,start,pos)?;
        let(poly,metrics)=edge::edge_u0_round_with_input_for_test(20,12,14,6,&strides,&counts,&r,
        |left,owner,sink|{need(left&&owner==observed.borrow().owners,"U0 candidate ordered owner")?;pos.owner.set(owner);pos.owner_terms.set(0);
            adapter.visit(left,owner,&mut|e|{let tag=check_edge(&e,left,owner,&strides)?;let row=e.term.row;pos.row.set(row);sink(e)?;
            observed.borrow_mut().term(tag)?;pos.term(row)?;if pos.owner_terms.get()%65536==0{clock(start)?;}Ok(())})},
        &mut packed_input,
        |owners,terms|{let mut c=observed.borrow_mut();need(owners==c.owners+1&&terms==c.terms,"U0 candidate progress")?;
            prefix.set(plus(prefix.get(),counts[owners-1]as u64)?);need(terms==prefix.get(),"U0 candidate census prefix")?;c.owners=owners;pos.owners.set(owners);
            clock(start)?;if owners%256==0{emit("candidate",owners,terms,clock(start)?)?;}Ok(())})?;
        let observed=observed.into_inner();let packed=Packed::from(packed_input.metrics());drop(packed_input);member_check(&observed.members,&expected)?;
        need(observed.owners==4096&&observed.terms==T,"U0 candidate coverage")?;let f=&metrics.fallback;
        need(f.visits==T&&f.cache_gets==T+4096&&f.vector_clones==0&&f.replay_folds==0&&f.x_fold_fields==0&&f.bank_fold_entries==0&&f.fold_ns==0,"U0 exact cumulative metrics")?;
        need(metrics.weights_capacity_bytes<=MIB&&metrics.x_capacity_peak_bytes==32*MIB&&f.cache_capacity_peak_bytes<=524288+packed.metadata_capacity_bytes&&f.bank_capacity_peak_bytes<=96*MIB,"U0 actual generic capacities")?;
        need(packed.logical_gets==T+4096&&packed.scalar_gets==T&&packed.successful_loads==27630
        &&packed.packed_bytes==3621519360&&packed.vector_expansions==4096&&packed.expanded_fields==4294967296,
        "packed U0 exact access/LRU/expansion counts")?;
        need(packed.logical_gets==plus(packed.scalar_gets,packed.vector_expansions)?
        &&packed.packed_bytes==times(packed.successful_loads,131072)?
        &&packed.expanded_fields==times(packed.vector_expansions,WIDTH as u64)?,"packed U0 count products")?;
        need(packed.packet_capacity_peak_bytes==131072&&packed.cache_capacity_peak_bytes==f.cache_capacity_peak_bytes
        &&packed.cache_capacity_peak_bytes<=524288+packed.metadata_capacity_bytes&&packed.metadata_capacity_bytes<=4096,
        "packed U0 cache capacities")?;
        let candidate_peak_bound=[metrics.weights_capacity_bytes,metrics.x_capacity_peak_bytes,f.cache_capacity_peak_bytes,f.bank_capacity_peak_bytes,131072,16*MIB]
        .into_iter().try_fold(0usize,|a,b|a.checked_add(b)).ok_or("packed U0 capacity overflow")?;
        need(candidate_peak_bound<=COMPONENT,"U0 actual candidate peak")?;
        // Generic wrapper has already dropped cache, banks, X and row weights.
        *stage="oracle";line.enter(6,start,pos)?;let weights=U0OracleWeights::new(&r)?;need(weights.capacity_bytes()==4*MIB,"U0 oracle table capacity")?;
        let mut bits=LiteralBits::new(&source)?;let mut reference=[Fr::zero();3];let mut oracle=Counted::default();let mut occupied=[0u64;40];
        for slot in 0..4096{pos.owner.set(slot);pos.owner_terms.set(0);let mut previous=None;
        plan.visit_role_owner_terms(2,slot as u64,|t|{pos.row.set(t.row);let tag=literal(&t,slot,&strides)?;
            need(previous.is_none_or(|row|row<=t.row),"U0 literal row order")?;if previous!=Some(t.row){occupied[tag]=plus(occupied[tag],1)?;previous=Some(t.row);}
            let g=&t.gate;let y=if !g.c2.is_zero()||!g.c3.is_zero(){bits.bit(g.right)?}else{Fr::zero()};
            let(x0,x1)=if !g.c1.is_zero()||!g.c3.is_zero(){let pair=g.left&!1;(bits.bit(pair)?,bits.bit(pair+1)?)}else{(Fr::zero(),Fr::zero())};
            for(o,c)in reference.iter_mut().zip(u0_oracle_term(&t,x0,x1,y,weights.at(t.row)?)){*o+=c;}
            oracle.term(tag)?;pos.term(t.row)?;if pos.owner_terms.get()%65536==0{clock(start)?;}Ok(())})?;
        oracle.owners+=1;pos.owners.set(oracle.owners);clock(start)?;if oracle.owners%256==0{emit("oracle",oracle.owners,oracle.terms,clock(start)?)?;}
        }
        member_check(&oracle.members,&expected)?;for tag in 0..40{need(occupied[tag]==expected[tag].rows,"U0 literal occupied rows")?;}
        need(oracle.owners==4096&&oracle.terms==T,"U0 oracle coverage")?;compare(poly,reference)?;
        need(poly[0]+poly[0]+poly[1]+poly[2]==Fr::zero(),"U0 aggregate zero identity")?;
        let oracle_packets=bits.peak;let oracle_loads=bits.loads;let oracle_tables=weights.capacity_bytes();
        let oracle_control=MIB;let oracle_peak_bound=oracle_tables+oracle_packets+oracle_control+REPORT;
        need(oracle_packets<=524288&&oracle_peak_bound<=16*MIB,"U0 actual oracle peak")?;drop(bits);drop(weights);
        *stage="sender";line.enter(7,start,pos)?;let sender=sender(poly,&pre)?;baseline(poly,&sender)?;
        *stage="custody";line.enter(8,start,pos)?;residual::raw_hash(&raw).map_err(|e|format!("{e:?}"))?;residual::packed_hash(&mut held).map_err(|e|format!("{e:?}"))?;
        let raw_check=OpenOptions::new().read(true).share_mode(1).open(raw_path).map_err(|e|e.to_string())?;
        need(u0_file_info(&raw)?==raw_id&&u0_file_info(&raw_check)?==raw_id,"U0 RAW custody")?;let check=u0_open_bytes(&path)?;
        need(u0_file_info(&held)?==id&&u0_file_info(&check)?==id,"U0 packed custody")?;adapter.require_source(&source)?;
        line.first[9]=clock(start)?;let timing=line.timing()?;need(plus(plus(packed.load_ns,packed.decode_ns)?,metrics.message_ns)?<=timing.candidate_ns,
        "packed U0 load/decode/message disjoint timing")?;
        need(packed.load_ns>0&&packed.decode_ns>0&&metrics.message_ns>0,"packed U0 positive component timing")?;
        let members:[Member<'_>;40]=std::array::from_fn(|tag|Member{tag,name:&plan.descriptors()[2].ordered_tags[tag],stride_log:strides[tag],terms:expected[tag].terms,rows:expected[tag].rows});
        let report=PackedReport{schema:"native-role2-packed-u0-v1",state:"ROLE2_PACKED_U0_PASS",stage:"complete",error:None,
        scope:Scope{role:2,input_log:32,row_log:32,local_input_log:20,base_row_log:14,family_log:6,owners:4096,active_headers:3073,members:40,
            deadline_seconds:900,component_limit_bytes:COMPONENT,producer_limit_bytes:512*MIB,oracle_limit_bytes:16*MIB,job_limit_bytes:2048*MIB,
            loader_mode:"packed_owner_bits_lru4_to_fr",diagnostic_prefix:true,full_u:false,full_v:false,gkr:false,pcs:false,production:false},
        inputs:Inputs{raw_sha256:RAW_SHA,raw_blake2b256:RAW_BLAKE,witness_sha256:PACK_SHA,witness_blake2b256:PACK_BLAKE},members:&members,
        census:Census{owners:census.owners,terms:census.terms,member_terms:census.members,left_counts_sha256:digest},
        candidate:Candidate{owners:observed.owners,terms:observed.terms,member_terms:observed.members,metrics:Metrics{visits:f.visits,cache_gets:f.cache_gets,
            vector_clones:f.vector_clones,replay_folds:f.replay_folds,x_fold_fields:f.x_fold_fields,bank_fold_entries:f.bank_fold_entries,cloned_fields:times(f.vector_clones,WIDTH as u64)?,
            weights_capacity_bytes:metrics.weights_capacity_bytes,cache_capacity_peak_bytes:f.cache_capacity_peak_bytes,x_capacity_peak_bytes:metrics.x_capacity_peak_bytes,
            bank_capacity_peak_bytes:f.bank_capacity_peak_bytes,message_ns:metrics.message_ns,fold_ns:f.fold_ns},packed},
        oracle:Oracle{sources:oracle.owners,terms:oracle.terms,member_terms:oracle.members,packed_loads:oracle_loads,packed_bytes:times(oracle_loads,131072)?},
        capacity:Capacity{row_lookup:metrics.weights_capacity_bytes,cache:f.cache_capacity_peak_bytes,x:metrics.x_capacity_peak_bytes,banks:f.bank_capacity_peak_bytes,
            loader_row:32*MIB,loader_packet:131072,auxiliary_reserve:16*MIB,candidate_peak_bound,oracle_tables,oracle_packets,oracle_control,oracle_peak_bound},
        polynomial:Polynomial{candidate:triples(poly)?,oracle:triples(reference)?,equal:true,zero_identity:true},sender,timing,
        checks:Checks{ordinary:true,source_admission:true,census:true,source_order:true,member_counts:true,polynomial:true,sender:true,custody:true},elapsed_ns:line.first[9]};
        let mut writer=Writer::new()?;serde_json::to_writer(&mut writer,&report).map_err(|e|e.to_string())?;clock(start)?;
        *stage="complete";emit("complete",4096,T,line.first[9])?;Ok(writer.bytes)
    }
    #[test]
    fn ordinary_boundaries(){edge::packed_edge_input_boundaries_for_test();super::ordinary_boundaries();}
    #[test]
    #[ignore="one full native role2 U0; reviewed900s/Job2GiB/Rayon4 controller required"]
    fn native_role2_packed_u0_bounded(){let start=Instant::now();let mut stage="admission";let pos=Position::default();
        let result=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||run(start,&mut stage,&pos))).unwrap_or_else(|_|Err("U0 panic".into()));
        let encoded=match &result{Ok(bytes)=>bytes.clone(),Err(error)=>{let _=emit("hold",pos.owners.get(),pos.terms.get(),screen_ns(start));
        serde_json::to_vec(&serde_json::json!({"schema":"native-role2-packed-u0-v1","state":"HOLD","stage":stage,"error":{"code":error.chars().take(256).collect::<String>(),
            "owner":pos.owner.get(),"row":pos.row.get(),"completed_terms":pos.terms.get(),"completed_owners":pos.owners.get(),"owner_terms":pos.owner_terms.get(),"substage":pos.substage.get()}})).unwrap()}};
        assert!(encoded.len()<=REPORT);let mut out=std::io::stdout().lock();out.write_all(b"\nNATIVE_ROLE2_PACKED_U0_REPORT ").unwrap();out.write_all(&encoded).unwrap();
        out.write_all(b"\n").unwrap();out.flush().unwrap();drop(out);assert!(result.is_ok(),"native role2 U0 HOLD");
    }
        }
        // source25-packed-input-child-END

        use super::*;
        use crate::transcript::Transcript;
        use serde::Serialize;
        use std::cell::RefCell;
        const T:u64=129277400;
        const LEFT:&str="30EF6B91BEFDCDE58C543CC6566FDFDB99A87BC30C7EDFC801D4E1D5F877961B";
        const RAW_SHA:&str="ABB3D74AE75256CED63110B72C2E0D5EBA1B90B09889E45EA327BDA1C9A640D2";
        const RAW_BLAKE:&str="8CDB90DA475E646280113D97C9469BE7EB86A1D04F20404C64239187284FC009";
        const PACK_SHA:&str="C1CC1CF72FF539F259A3BDEF756332BA52CB8AFF26C11AB4116D1B2F9D17ED43";
        const PACK_BLAKE:&str="725D7B1215E1185C52C1012D9294260612653ACAD53A02429B8EAAFD0F0770C8";
        const CONTINUE:&[u8]=b"native-role2-u0-continuation-v1";
        const STAGES:[&str;10]=["admission","plan","counts","census","binding","candidate","oracle","sender","custody","complete"];
        fn plus(a:u64,b:u64)->Result<u64,String>{a.checked_add(b).ok_or("U0 counter overflow".into())}
        fn times(a:u64,b:u64)->Result<u64,String>{a.checked_mul(b).ok_or("U0 product overflow".into())}
        fn limit(n:u64)->Result<(),String>{need(n<=900_000_000_000,"U0 deadline")}
        fn clock(start:Instant)->Result<u64,String>{let n=u64::try_from(start.elapsed().as_nanos()).map_err(|_|"U0 clock overflow")?;
            limit(n)?;Ok(n)}
        #[derive(Default)]struct Position{owner:Cell<usize>,row:Cell<usize>,terms:Cell<u64>,owners:Cell<usize>,owner_terms:Cell<u64>,substage:Cell<&'static str>}
        impl Position{fn reset(&self,s:&'static str){self.owner.set(0);self.row.set(0);self.terms.set(0);self.owners.set(0);self.owner_terms.set(0);self.substage.set(s);}
            fn term(&self,row:usize)->Result<(),String>{self.row.set(row);self.terms.set(plus(self.terms.get(),1)?);
                self.owner_terms.set(plus(self.owner_terms.get(),1)?);Ok(())}}
        fn emit(stage:&str,owners:usize,terms:u64,ns:u64)->Result<(),String>{
            let mut out=std::io::stderr().lock();writeln!(out,"NATIVE_ROLE2_U0_STAGE stage={stage} owners={owners} terms={terms} elapsed_ns={ns}")
                .map_err(|e|e.to_string())?;out.flush().map_err(|e|e.to_string())}
        struct Timeline{first:[u64;10]}
        impl Timeline{fn enter(&mut self,index:usize,start:Instant,pos:&Position)->Result<(),String>{
                pos.reset(STAGES[index]);let n=clock(start)?;self.first[index]=n;
                emit(STAGES[index],if index>=7{4096}else{0},if index>=7{T}else{0},n)}
            fn timing(&self)->Result<Timing,String>{let a=&self.first;for w in a.windows(2){need(w[1]>w[0],"U0 stage clock order")?;}
                Ok(Timing{admission_ns:a[1]-a[0],plan_ns:a[2]-a[1],counts_ns:a[3]-a[2],census_ns:a[4]-a[3],binding_ns:a[5]-a[4],
                    candidate_ns:a[6]-a[5],oracle_ns:a[7]-a[6],sender_ns:a[8]-a[7],custody_ns:a[9]-a[8],total_ns:a[9]})}}
        fn literal(t:&Term,slot:usize,strides:&[usize;40])->Result<usize,String>{
            need(t.row<1usize<<32,"U0 literal row domain")?;let tag=t.row>>26;need(tag<40,"U0 literal member")?;
            let q=strides[tag];need(q<=14,"U0 literal stride")?;let local=t.row&((1usize<<26)-1);
            need(local>>(q+12)==0,"U0 literal zero extension")?;need(local>>q==slot,"U0 literal source")?;
            need(t.gate.left<1usize<<32&&t.gate.right<1usize<<32,"U0 literal endpoint domain")?;Ok(tag)
        }
        fn member_check(got:&[u64;40],expected:&[residual::Count;40])->Result<(),String>{
            for i in 0..40{need(got[i]==expected[i].terms,"U0 ordered member census")?;}Ok(())}
        fn hex32(s:&str)->Result<[u8;32],String>{need(s.len()==64,"U0 digest width")?;let mut out=[0;32];
            for i in 0..32{out[i]=u8::from_str_radix(&s[2*i..2*i+2],16).map_err(|_|"U0 digest hex")?;}Ok(out)}
        fn binding(plan:&NativePrefixAuthPlan<'_>,expected:&[residual::Count;40],strides:&[usize;40],digest:&str)->Result<(Transcript,Vec<Fr>),String>{
            need(digest==LEFT,"U0 fixed LEFT digest")?;
            let mut t=Transcript::new(b"native-prefix-role2-u0-diagnostic-v1");
            t.append_bytes(b"source-revision",b"source24-role2-u0-diagnostic-v1");
            for(label,pin)in [(b"native-fixture-sha256".as_slice(),RAW_SHA),(b"native-fixture-blake2b256".as_slice(),RAW_BLAKE),
                (b"witness-sha256".as_slice(),PACK_SHA),(b"witness-blake2b256".as_slice(),PACK_BLAKE)]{t.append_bytes(label,&hex32(pin)?);}
            for(label,n)in [(b"role-index".as_slice(),2u64),(b"headers".as_slice(),3073),(b"slot-log".as_slice(),12),
                (b"input-log".as_slice(),32),(b"row-log".as_slice(),32),(b"local-input-log".as_slice(),20),
                (b"base-row-log".as_slice(),14),(b"family-log".as_slice(),6),(b"member-count".as_slice(),40)]{t.append_u64(label,n);}
            for tag in 0..40{t.append_u64(b"member-tag",tag as u64);t.append_bytes(b"member-name",plan.descriptors()[2].ordered_tags[tag].as_bytes());
                t.append_u64(b"member-stride-log",strides[tag]as u64);t.append_u64(b"member-terms",expected[tag].terms);t.append_u64(b"member-rows",expected[tag].rows);}
            t.append_bytes(b"left-counts-sha256",&hex32(digest)?);plan.bind_plan_identity(&mut t)?;
            need(t.challenges()==0,"U0 binding sampled challenge")?;let r=crate::gkr::output_point(1usize<<32,&mut t);
            crate::gkr::append_usize(&mut t,b"gkr-layer-index",0);need(r.len()==32&&t.challenges()==32,"U0 prepared geometry")?;Ok((t,r))
        }
        fn counters(t:&Transcript)->[u64;3]{[t.challenges(),t.raw_queries(),t.bytes_absorbed()]}
        fn sender(poly:[Fr;3],pre:&Transcript)->Result<Sender,String>{
            let initial=counters(pre);let mut candidate=pre.clone();let mut reference=pre.clone();
            let(q,c)=edge::edge_u0_send_for_test(poly,&mut candidate)?;
            let(r,d)=useq_reference_send(poly,Fr::zero(),&mut reference)?;
            let cc=counters(&candidate);let rc=counters(&reference);
            let qc=candidate.clone().challenge_scalar(CONTINUE);let qr=reference.clone().challenge_scalar(CONTINUE);
            need(q==r&&c==d&&cc==rc&&qc==qr,"U0 independent sender divergence")?;
            need(initial[0]==32&&cc[0]==33&&initial[1]>=initial[0]&&cc[1]>=cc[0]&&cc[2]>initial[2]&&initial[2]>0,"U0 sender counters")?;
            Ok(Sender{initial_counters:initial,candidate_counters:cc,reference_counters:rc,candidate_challenge:scalar(q)?,reference_challenge:scalar(r)?,
                candidate_claim:scalar(c)?,reference_claim:scalar(d)?,candidate_continuation:scalar(qc)?,reference_continuation:scalar(qr)?,equal:true})
        }
        #[derive(Default,Serialize)]struct Loads{successful:u64,decoded_fields:u64,packed_bytes:u64,load_decode_ns:u64,row_capacity_peak_bytes:usize,packet_capacity_peak_bytes:usize}
        fn measured_load(source:&PackedFile,owner:usize,loads:&RefCell<Loads>,start:Instant)->Result<Vec<Fr>,String>{
            clock(start)?;let row=Cell::new(0);let packet=Cell::new(0);let began=Instant::now();
            let values=load(source,owner,&row,&packet)?;let ns=u64::try_from(began.elapsed().as_nanos()).map_err(|_|"U0 loader clock")?;
            let mut out=loads.borrow_mut();out.successful=plus(out.successful,1)?;out.decoded_fields=times(out.successful,WIDTH as u64)?;
            out.packed_bytes=times(out.successful,131072)?;out.load_decode_ns=plus(out.load_decode_ns,ns)?;
            out.row_capacity_peak_bytes=out.row_capacity_peak_bytes.max(row.get());out.packet_capacity_peak_bytes=out.packet_capacity_peak_bytes.max(packet.get());
            need(row.get()==32*MIB&&packet.get()==131072,"U0 loader exact capacity")?;Ok(values)
        }
        struct LiteralBits<'a>{inner:OracleBits<'a>,loads:u64,peak:usize}
        impl<'a> LiteralBits<'a>{fn new(source:&'a PackedFile)->Result<Self,String>{Ok(Self{inner:OracleBits::new(source)?,loads:0,peak:0})}
            fn bit(&mut self,wire:usize)->Result<Fr,String>{let miss=!self.inner.packets.iter().any(|(o,_)|*o==wire>>20);
                let x=self.inner.bit(wire)?;if miss{self.loads=plus(self.loads,1)?;}self.peak=self.peak.max(self.inner.packets.len()*131072);Ok(x)}}
        struct Counted{terms:u64,members:[u64;40],owners:usize}
        impl Default for Counted{fn default()->Self{Self{terms:0,members:[0;40],owners:0}}}
        impl Counted{fn term(&mut self,tag:usize)->Result<(),String>{self.terms=plus(self.terms,1)?;self.members[tag]=plus(self.members[tag],1)?;Ok(())}}
        fn forty<S:serde::Serializer>(values:&[u64;40],s:S)->Result<S::Ok,S::Error>{values.as_slice().serialize(s)}
        #[derive(Serialize)]struct Member<'a>{tag:usize,name:&'a str,stride_log:usize,terms:u64,rows:u64}
        #[derive(Serialize)]struct Census{owners:usize,terms:u64,#[serde(serialize_with="forty")]member_terms:[u64;40],left_counts_sha256:String}
        #[derive(Serialize)]struct Metrics{visits:u64,cache_gets:u64,vector_clones:u64,replay_folds:u64,x_fold_fields:u64,bank_fold_entries:u64,cloned_fields:u64,
            weights_capacity_bytes:usize,cache_capacity_peak_bytes:usize,x_capacity_peak_bytes:usize,bank_capacity_peak_bytes:usize,message_ns:u64,fold_ns:u64}
        #[derive(Serialize)]struct Candidate{owners:usize,terms:u64,#[serde(serialize_with="forty")]member_terms:[u64;40],metrics:Metrics,loads:Loads}
        #[derive(Serialize)]struct Oracle{sources:usize,terms:u64,#[serde(serialize_with="forty")]member_terms:[u64;40],packed_loads:u64,packed_bytes:u64}
        #[derive(Serialize)]struct Capacity{row_lookup:usize,cache:usize,x:usize,banks:usize,loader_row:usize,loader_packet:usize,auxiliary_reserve:usize,
            candidate_peak_bound:usize,oracle_tables:usize,oracle_packets:usize,oracle_control:usize,oracle_peak_bound:usize}
        #[derive(Serialize)]struct Polynomial{candidate:[String;3],oracle:[String;3],equal:bool,zero_identity:bool}
        #[derive(Serialize)]struct Sender{initial_counters:[u64;3],candidate_counters:[u64;3],reference_counters:[u64;3],candidate_challenge:String,reference_challenge:String,
            candidate_claim:String,reference_claim:String,candidate_continuation:String,reference_continuation:String,equal:bool}
        #[derive(Serialize)]struct Timing{admission_ns:u64,plan_ns:u64,counts_ns:u64,census_ns:u64,binding_ns:u64,candidate_ns:u64,oracle_ns:u64,sender_ns:u64,custody_ns:u64,total_ns:u64}
        #[derive(Serialize)]struct Scope{role:usize,input_log:usize,row_log:usize,local_input_log:usize,base_row_log:usize,family_log:usize,owners:usize,active_headers:usize,members:usize,
            deadline_seconds:usize,component_limit_bytes:usize,producer_limit_bytes:usize,oracle_limit_bytes:usize,job_limit_bytes:usize,loader_mode:&'static str,
            diagnostic_prefix:bool,full_u:bool,full_v:bool,gkr:bool,pcs:bool,production:bool}
        #[derive(Serialize)]struct Inputs{raw_sha256:&'static str,raw_blake2b256:&'static str,witness_sha256:&'static str,witness_blake2b256:&'static str}
        #[derive(Serialize)]struct Checks{ordinary:bool,source_admission:bool,census:bool,source_order:bool,member_counts:bool,polynomial:bool,sender:bool,custody:bool}
        #[derive(Serialize)]struct UReport<'a>{schema:&'static str,state:&'static str,stage:&'static str,error:Option<&'a str>,scope:Scope,inputs:Inputs,members:&'a[Member<'a>],
            census:Census,candidate:Candidate,oracle:Oracle,capacity:Capacity,polynomial:Polynomial,sender:Sender,timing:Timing,checks:Checks,elapsed_ns:u64}
        // Serde's fixed-array support stops at32; keep wire arrays as borrowed
        // slices over fixed40 counters without allocating another census vector.
        fn run(start:Instant,stage:&mut &'static str,pos:&Position)->Result<Vec<u8>,String>{
            let mut line=Timeline{first:[0;10]};line.enter(0,start,pos)?;
            let(raw,raw_id,raw_path)=residual::raw_hold().map_err(|e|format!("{e:?}"))?;
            let path=std::path::PathBuf::from(std::env::var_os("NIPOPOW_NATIVE_U_SEQUENCE_WITNESS").ok_or("U0 witness env")?);
            let(source,mut held,id)=useq_admit()?;
            *stage="plan";line.enter(1,start,pos)?;let native=input();let candidate=crate::native_prefix_auth_plan::Candidate{n:3073,root:native.root(),total:native.total_be28(),
                tip:ergo_header_core::blake2b256(native.raw(3073)?),tip_time:native.timestamp(3073)?};
            let parent=WorkTreeHistoryPlan::compile(3073,12,candidate.root,candidate.total)?;drop(native);
            let plan=NativePrefixAuthPlan::compile(&parent,Selection::s12(),candidate)?;let adapter=plan.role2_endpoints(&source,&mut held,start)?;
            *stage="counts";line.enter(2,start,pos)?;let(expected,strides)=residual::expectations(&parent,&plan).map_err(|e|format!("{e:?}"))?;
            // Before generic allocations: fixed maximum simultaneous source model.
            need(128*MIB+32*MIB+96*MIB+MIB+131072+16*MIB<=COMPONENT,"U0 candidate preflight")?;
            let census=RefCell::new(Counted::default());*stage="census";line.enter(3,start,pos)?;
            let counts=edge::edge_u0_census_for_test(20,12,14,&strides,
                |left,owner,sink|{need(left&&owner==census.borrow().owners,"U0 census ordered owner")?;pos.owner.set(owner);pos.owner_terms.set(0);
                    adapter.visit(left,owner,&mut|e|{let tag=check_edge(&e,left,owner,&strides)?;let row=e.term.row;pos.row.set(row);sink(e)?;
                        census.borrow_mut().term(tag)?;pos.term(row)?;if pos.owner_terms.get()%65536==0{clock(start)?;}Ok(())})},
                |owners,terms|{let mut c=census.borrow_mut();need(owners==c.owners+1&&terms==c.terms,"U0 census progress")?;c.owners=owners;
                    pos.owners.set(owners);clock(start)?;if owners%256==0{emit("census",owners,terms,clock(start)?)?;}Ok(())})?;
            let census=census.into_inner();need(counts.len()==4096&&counts.capacity()<=4096&&census.owners==4096&&census.terms==T,"U0 full census")?;
            member_check(&census.members,&expected)?;let digest=digest_counts(&counts)?;need(digest==LEFT,"U0 fixed LEFT digest")?;
            *stage="binding";line.enter(4,start,pos)?;let(pre,r)=binding(&plan,&expected,&strides,&digest)?;
            need(r.capacity()<=32,"U0 row point capacity")?;
            let observed=RefCell::new(Counted::default());let loads=RefCell::new(Loads::default());let prefix=Cell::new(0u64);
            *stage="candidate";line.enter(5,start,pos)?;
            let(poly,metrics)=edge::edge_u0_round_for_test(20,12,14,6,&strides,&counts,&r,
                |left,owner,sink|{need(left&&owner==observed.borrow().owners,"U0 candidate ordered owner")?;pos.owner.set(owner);pos.owner_terms.set(0);
                    adapter.visit(left,owner,&mut|e|{let tag=check_edge(&e,left,owner,&strides)?;let row=e.term.row;pos.row.set(row);sink(e)?;
                        observed.borrow_mut().term(tag)?;pos.term(row)?;if pos.owner_terms.get()%65536==0{clock(start)?;}Ok(())})},
                |owner|measured_load(&source,owner,&loads,start),
                |owners,terms|{let mut c=observed.borrow_mut();need(owners==c.owners+1&&terms==c.terms,"U0 candidate progress")?;
                    prefix.set(plus(prefix.get(),counts[owners-1]as u64)?);need(terms==prefix.get(),"U0 candidate census prefix")?;c.owners=owners;pos.owners.set(owners);
                    clock(start)?;if owners%256==0{emit("candidate",owners,terms,clock(start)?)?;}Ok(())})?;
            let observed=observed.into_inner();let loads=loads.into_inner();member_check(&observed.members,&expected)?;
            need(observed.owners==4096&&observed.terms==T,"U0 candidate coverage")?;let f=&metrics.fallback;
            need(f.visits==T&&f.cache_gets==T+4096&&f.vector_clones==4096&&f.replay_folds==0&&f.x_fold_fields==0&&f.bank_fold_entries==0&&f.fold_ns==0,"U0 exact cumulative metrics")?;
            need(metrics.weights_capacity_bytes<=MIB&&metrics.x_capacity_peak_bytes==32*MIB&&f.cache_capacity_peak_bytes<=128*MIB&&f.bank_capacity_peak_bytes<=96*MIB,"U0 actual generic capacities")?;
            need((4096..=T+4096).contains(&loads.successful)&&loads.row_capacity_peak_bytes==32*MIB&&loads.packet_capacity_peak_bytes==131072,"U0 loader cumulative capacity")?;
            let candidate_peak_bound=metrics.weights_capacity_bytes+metrics.x_capacity_peak_bytes+f.cache_capacity_peak_bytes+f.bank_capacity_peak_bytes+131072+16*MIB;
            need(candidate_peak_bound<=COMPONENT,"U0 actual candidate peak")?;
            // Generic wrapper has already dropped cache, banks, X and row weights.
            *stage="oracle";line.enter(6,start,pos)?;let weights=U0OracleWeights::new(&r)?;need(weights.capacity_bytes()==4*MIB,"U0 oracle table capacity")?;
            let mut bits=LiteralBits::new(&source)?;let mut reference=[Fr::zero();3];let mut oracle=Counted::default();let mut occupied=[0u64;40];
            for slot in 0..4096{pos.owner.set(slot);pos.owner_terms.set(0);let mut previous=None;
                plan.visit_role_owner_terms(2,slot as u64,|t|{pos.row.set(t.row);let tag=literal(&t,slot,&strides)?;
                    need(previous.is_none_or(|row|row<=t.row),"U0 literal row order")?;if previous!=Some(t.row){occupied[tag]=plus(occupied[tag],1)?;previous=Some(t.row);}
                    let g=&t.gate;let y=if !g.c2.is_zero()||!g.c3.is_zero(){bits.bit(g.right)?}else{Fr::zero()};
                    let(x0,x1)=if !g.c1.is_zero()||!g.c3.is_zero(){let pair=g.left&!1;(bits.bit(pair)?,bits.bit(pair+1)?)}else{(Fr::zero(),Fr::zero())};
                    for(o,c)in reference.iter_mut().zip(u0_oracle_term(&t,x0,x1,y,weights.at(t.row)?)){*o+=c;}
                    oracle.term(tag)?;pos.term(t.row)?;if pos.owner_terms.get()%65536==0{clock(start)?;}Ok(())})?;
                oracle.owners+=1;pos.owners.set(oracle.owners);clock(start)?;if oracle.owners%256==0{emit("oracle",oracle.owners,oracle.terms,clock(start)?)?;}
            }
            member_check(&oracle.members,&expected)?;for tag in 0..40{need(occupied[tag]==expected[tag].rows,"U0 literal occupied rows")?;}
            need(oracle.owners==4096&&oracle.terms==T,"U0 oracle coverage")?;compare(poly,reference)?;
            need(poly[0]+poly[0]+poly[1]+poly[2]==Fr::zero(),"U0 aggregate zero identity")?;
            let oracle_packets=bits.peak;let oracle_loads=bits.loads;let oracle_tables=weights.capacity_bytes();
            let oracle_control=MIB;let oracle_peak_bound=oracle_tables+oracle_packets+oracle_control+REPORT;
            need(oracle_packets<=524288&&oracle_peak_bound<=16*MIB,"U0 actual oracle peak")?;drop(bits);drop(weights);
            *stage="sender";line.enter(7,start,pos)?;let sender=sender(poly,&pre)?;
            *stage="custody";line.enter(8,start,pos)?;residual::raw_hash(&raw).map_err(|e|format!("{e:?}"))?;residual::packed_hash(&mut held).map_err(|e|format!("{e:?}"))?;
            let raw_check=OpenOptions::new().read(true).share_mode(1).open(raw_path).map_err(|e|e.to_string())?;
            need(u0_file_info(&raw)?==raw_id&&u0_file_info(&raw_check)?==raw_id,"U0 RAW custody")?;let check=u0_open_bytes(&path)?;
            need(u0_file_info(&held)?==id&&u0_file_info(&check)?==id,"U0 packed custody")?;adapter.require_source(&source)?;
            line.first[9]=clock(start)?;let timing=line.timing()?;need(plus(loads.load_decode_ns,metrics.message_ns)?<=timing.candidate_ns,"U0 load/message disjoint timing")?;
            let members:[Member<'_>;40]=std::array::from_fn(|tag|Member{tag,name:&plan.descriptors()[2].ordered_tags[tag],stride_log:strides[tag],terms:expected[tag].terms,rows:expected[tag].rows});
            let report=UReport{schema:"native-role2-u0-v1",state:"ROLE2_FULL_U0_PASS",stage:"complete",error:None,
                scope:Scope{role:2,input_log:32,row_log:32,local_input_log:20,base_row_log:14,family_log:6,owners:4096,active_headers:3073,members:40,
                    deadline_seconds:900,component_limit_bytes:COMPONENT,producer_limit_bytes:512*MIB,oracle_limit_bytes:16*MIB,job_limit_bytes:2048*MIB,
                    loader_mode:"packed_owner_bits_to_fr",diagnostic_prefix:true,full_u:false,full_v:false,gkr:false,pcs:false,production:false},
                inputs:Inputs{raw_sha256:RAW_SHA,raw_blake2b256:RAW_BLAKE,witness_sha256:PACK_SHA,witness_blake2b256:PACK_BLAKE},members:&members,
                census:Census{owners:census.owners,terms:census.terms,member_terms:census.members,left_counts_sha256:digest},
                candidate:Candidate{owners:observed.owners,terms:observed.terms,member_terms:observed.members,metrics:Metrics{visits:f.visits,cache_gets:f.cache_gets,
                    vector_clones:f.vector_clones,replay_folds:f.replay_folds,x_fold_fields:f.x_fold_fields,bank_fold_entries:f.bank_fold_entries,cloned_fields:times(f.vector_clones,WIDTH as u64)?,
                    weights_capacity_bytes:metrics.weights_capacity_bytes,cache_capacity_peak_bytes:f.cache_capacity_peak_bytes,x_capacity_peak_bytes:metrics.x_capacity_peak_bytes,
                    bank_capacity_peak_bytes:f.bank_capacity_peak_bytes,message_ns:metrics.message_ns,fold_ns:f.fold_ns},loads},
                oracle:Oracle{sources:oracle.owners,terms:oracle.terms,member_terms:oracle.members,packed_loads:oracle_loads,packed_bytes:times(oracle_loads,131072)?},
                capacity:Capacity{row_lookup:metrics.weights_capacity_bytes,cache:f.cache_capacity_peak_bytes,x:metrics.x_capacity_peak_bytes,banks:f.bank_capacity_peak_bytes,
                    loader_row:32*MIB,loader_packet:131072,auxiliary_reserve:16*MIB,candidate_peak_bound,oracle_tables,oracle_packets,oracle_control,oracle_peak_bound},
                polynomial:Polynomial{candidate:triples(poly)?,oracle:triples(reference)?,equal:true,zero_identity:true},sender,timing,
                checks:Checks{ordinary:true,source_admission:true,census:true,source_order:true,member_counts:true,polynomial:true,sender:true,custody:true},elapsed_ns:line.first[9]};
            let mut writer=Writer::new()?;serde_json::to_writer(&mut writer,&report).map_err(|e|e.to_string())?;clock(start)?;
            *stage="complete";emit("complete",4096,T,line.first[9])?;Ok(writer.bytes)
        }
        #[test]
        fn ordinary_boundaries(){controls().unwrap();super::ordinary_boundaries();}
        #[test]
        #[ignore="one full native role2 U0; reviewed900s/Job2GiB/Rayon4 controller required"]
        fn native_role2_u0_bounded(){let start=Instant::now();let mut stage="admission";let pos=Position::default();
            let result=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||run(start,&mut stage,&pos))).unwrap_or_else(|_|Err("U0 panic".into()));
            let encoded=match &result{Ok(bytes)=>bytes.clone(),Err(error)=>{let _=emit("hold",pos.owners.get(),pos.terms.get(),screen_ns(start));
                serde_json::to_vec(&serde_json::json!({"schema":"native-role2-u0-v1","state":"HOLD","stage":stage,"error":{"code":error.chars().take(256).collect::<String>(),
                    "owner":pos.owner.get(),"row":pos.row.get(),"completed_terms":pos.terms.get(),"completed_owners":pos.owners.get(),"owner_terms":pos.owner_terms.get(),"substage":pos.substage.get()}})).unwrap()}};
            assert!(encoded.len()<=REPORT);let mut out=std::io::stdout().lock();out.write_all(b"\nNATIVE_ROLE2_U0_REPORT ").unwrap();out.write_all(&encoded).unwrap();
            out.write_all(b"\n").unwrap();out.flush().unwrap();drop(out);assert!(result.is_ok(),"native role2 U0 HOLD");
        }
        fn controls()->Result<(),String>{
            use crate::gkr::Gate;
            need(size_of::<Fr>()==32&&size_of::<usize>()==8&&size_of::<Term>()==152,"U0 reviewed x64 ABI")?;
            let input=(0..8).flat_map(|s|[Fr::from((s&1)as u64),Fr::from(((s>>1)&1)as u64),Fr::from(((s>>2)&1)as u64),Fr::one()]).collect::<Vec<_>>();
            let mut terms=Vec::new();
            for s in 0..8{let left=4*s;let right=4*((s+5)%8)+3;let(c1,c2,c3)=(Fr::from(2),Fr::from(3),Fr::from(5));
                terms.push(Term{row:s,gate:Gate{left,right,c0:-(c1*input[left]+c2*input[right]+c3*input[left]*input[right]),c1,c2,c3}});}
            // Foreign row2 constant lives at endpoint0; its row sum is cancelled
            // by a local owner2 bit, so both the baseline and identity are honest.
            terms.push(Term{row:2,gate:Gate{left:9,right:0,c0:Fr::zero(),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()}});
            terms.push(Term{row:2,gate:Gate{left:0,right:0,c0:-Fr::one(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}});
            terms.push(Term{row:7,gate:Gate{left:28,right:0,c0:Fr::zero(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}});
            let mut setup=Transcript::new(b"role2-u0-ordinary-v1");let r=crate::gkr::output_point(8,&mut setup);
            let visit=|left:bool,owner:usize,sink:&mut dyn FnMut(edge::EdgeTerm)->Result<(),String>|{
                need(left,"U0 ordinary LEFT only")?;for t in terms.iter().filter(|t|t.gate.left/4==owner){
                    sink(edge::EdgeTerm{source_slot:t.row,family_row:0,term:t.clone()})?;}Ok(())};
            let counts=edge::edge_u0_census_for_test(2,3,0,&[0],visit,|_,_|Ok(()))?;
            need(counts.iter().sum::<usize>()==11&&counts[0]==2,"U0 ordinary foreign constant census")?;
            let mut oracle=[Fr::zero();3];for source in 0..8{for t in terms.iter().filter(|t|t.row==source){
                let j=t.gate.left&!1;for(sum,c)in oracle.iter_mut().zip(u0_oracle_term(t,input[j],input[j+1],input[t.gate.right],u0_direct_weight(&r,t.row))){*sum+=c;}}}
            let mut actual=None;
            for fault in 0..9{
                let result=edge::edge_u0_round_for_test(2,3,0,0,&[0],&counts,&r,
                    |left,owner,sink|{need(left,"U0 ordinary candidate LEFT")?;
                        for(index,t)in terms.iter().enumerate().filter(|(_,t)|t.gate.left/4==owner){
                            if fault==1&&index==9{continue;}
                            let mut changed=t.clone();if index==2{match fault{3=>changed.gate.c3+=Fr::one(),4=>changed.row=3,5=>changed.gate.left^=1,_=>{}}}
                            let mut e=edge::EdgeTerm{source_slot:changed.row,family_row:0,term:changed};
                            if fault==7&&index==2{e.family_row=1;}if fault==8&&index==2{e.source_slot=8;}
                            sink(e.clone())?;if fault==2&&index==10{sink(e)?;}
                        }Ok(())},
                    |owner|{let mut row=input[4*owner..4*owner+4].to_vec();if fault==6&&owner==2{row[1]=Fr::zero();}Ok(row)},|_,_|Ok(()));
                match fault{0=>{let(p,m)=result?;compare(p,oracle)?;need(m.fallback.visits==11&&m.fallback.vector_clones==8&&m.fallback.replay_folds==0,"U0 tiny full metrics")?;actual=Some(p);},
                    1=>need(result.err().ok_or("U0 omission survived")?=="edge endpoint source count changed between passes","U0 isolated omitted constant")?,
                    2=>need(result.err().ok_or("U0 duplicate survived")?=="edge endpoint source exceeded its baseline count","U0 isolated zero duplicate")?,
                    3..=6=>need(compare(result?.0,oracle).unwrap_err()=="endpoint kernel/oracle mismatch","U0 isolated arithmetic sensitivity")?,
                    _=>need(result.err().ok_or("U0 mapping survived")?=="edge endpoint wire or row outside declared slot","U0 isolated member/source")?,
                }
            }
            let p=actual.ok_or("U0 missing honest tiny result")?;need(p[0]+p[0]+p[1]+p[2]==Fr::zero(),"U0 ordinary zero identity")?;
            let mut pre=Transcript::new(b"role2-u0-sender-control-v1");crate::gkr::output_point(1usize<<32,&mut pre);crate::gkr::append_usize(&mut pre,b"gkr-layer-index",0);
            sender(p,&pre)?;
            let fixed=[Fr::from(2),-Fr::from(3),-Fr::one()];sender(fixed,&pre)?;
            let mut reference=pre.clone();useq_reference_send(fixed,Fr::zero(),&mut reference)?;
            let fingerprint=|t:&Transcript|(counters(t),t.clone().challenge_scalar(CONTINUE));
            for fault in 0..3{let mut bad=pre.clone();
                let label:&[u8]=if fault==1{b"wrong-polynomial-label"}else{b"gkr-sumcheck-polynomial"};
                let length=if fault==0{2u64}else{3u64};bad.append_bytes(label,&length.to_le_bytes());
                if fault==2{for c in fixed.into_iter().rev(){bad.append_scalar(b"gkr-polynomial-coefficient",&c);}}
                else{for c in fixed{bad.append_scalar(b"gkr-polynomial-coefficient",&c);}}
                bad.challenge_scalar(b"gkr-sumcheck-challenge");need(fingerprint(&bad)!=fingerprint(&reference),"U0 sender encoding mutant survived")?;
            }
            let mut divergent=pre.clone();divergent.append_bytes(b"isolated-prestate",b"x");
            useq_reference_send(fixed,Fr::zero(),&mut divergent)?;need(fingerprint(&divergent)!=fingerprint(&reference),"U0 sender prestate divergence")?;
            let mut bad=fixed;bad[0]+=Fr::one();let original=fingerprint(&pre);let mut c=pre.clone();
            need(edge::edge_u0_send_for_test(bad,&mut c).unwrap_err()==crate::gkr::GkrError::SumcheckIdentity.to_string(),"U0 bad identity candidate")?;
            need(fingerprint(&c)==original,"U0 failed candidate sender mutation")?;
            need(useq_reference_send(bad,Fr::zero(),&mut pre.clone()).unwrap_err()=="sequence independent prior claim","U0 bad identity reference")?;
            let strides=[11;40];let mut t=Term{row:(34<<26)+(1<<11),gate:Gate{left:0,right:0,c0:-Fr::one(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}};
            need(literal(&t,1,&strides)?==34,"U0 foreign-source literal constant")?;
            need(literal(&t,0,&strides).unwrap_err()=="U0 literal source","U0 literal wrong source")?;
            t.row|=1<<25;need(literal(&t,1,&strides).unwrap_err()=="U0 literal zero extension","U0 literal padding")?;
            t.row=40<<26;need(literal(&t,0,&strides).unwrap_err()=="U0 literal member","U0 literal member negative")?;
            need(plus(u64::MAX,1).unwrap_err()=="U0 counter overflow"&&times(u64::MAX,2).unwrap_err()=="U0 product overflow","U0 checked counters")?;
            need(limit(900_000_000_001).unwrap_err()=="U0 deadline","U0 deadline boundary")?;
            let r=general(32,41);let weights=U0OracleWeights::new(&r)?;need(weights.capacity_bytes()==4*MIB,"U0 independent table allocation")?;
            for index in std::iter::once(0).chain((0..32).map(|i|1usize<<i)).chain([(1usize<<32)-1]){
                need(weights.at(index)?==u0_direct_weight(&r,index),"U0 independent row tables")?;}
            Ok(())
        }
    }
    // source24-role2-u0-child-END
    use super::*;
    use super::role2_residual_diagnostic as residual;
    use crate::{packed::{PackedFile,PackedOwnerBits,PackedReaderFault},
        sparse_stream_roster::{self as edge,EdgeTerm},work_tree_fixed_hash as fixed};
    use serde::Serialize;
    use ark_serialize::{CanonicalSerialize,CanonicalDeserialize};
    use std::{cell::Cell,collections::VecDeque,io::Write,mem::size_of,time::Instant};
    const OWNERS:usize=4096;const MEMBERS:usize=40;const WIDTH:usize=1<<20;
    const MIB:usize=1024*1024;const COMPONENT:usize=320*MIB;const REPORT:usize=16384;
    const SELECTED:[usize;5]=[0,1,3072,4094,4095];
    #[derive(Clone,Copy,Serialize)]struct Recipe{row_offset:u64,row_step:u64,input_offset:u64,input_step:u64,
        coordinates:usize,index_origin:u64,left_value:u64}
    const RECIPE:Recipe=Recipe{row_offset:3,row_step:29,input_offset:101,input_step:37,coordinates:32,index_origin:1,left_value:17};
    fn points()->(Vec<Fr>,Vec<Fr>){
        ((0..RECIPE.coordinates).map(|i|Fr::from(RECIPE.row_offset+RECIPE.row_step*(i as u64+RECIPE.index_origin))).collect(),
         (0..RECIPE.coordinates).map(|i|Fr::from(RECIPE.input_offset+RECIPE.input_step*(i as u64+RECIPE.index_origin))).collect())
    }
    fn need(ok:bool,message:&str)->Result<(),String>{if ok{Ok(())}else{Err(message.into())}}
    fn add(a:usize,b:usize)->Result<usize,String>{a.checked_add(b).ok_or("endpoint size overflow".into())}
    fn bytes(n:usize)->Result<usize,String>{n.checked_mul(size_of::<Fr>()).ok_or("endpoint byte overflow".into())}
    fn deadline(n:u64)->Result<(),String>{need(n<=300_000_000_000,"endpoint deadline")}
    fn now(start:Instant)->Result<u64,String>{let n=u64::try_from(start.elapsed().as_nanos()).map_err(|_|"endpoint clock")?;
        deadline(n)?;Ok(n)}
    fn mark(stage:&str,phase:&str,owner:usize,n:u64)->Result<(),String>{
        let mut out=std::io::stderr().lock();writeln!(out,"NATIVE_ROLE2_ENDPOINT_STAGE {stage} phase={phase} owner={owner} elapsed_ns={n}")
            .map_err(|e|e.to_string())?;out.flush().map_err(|e|e.to_string())}
    fn scalar(x:Fr)->Result<String,String>{
        let mut b=[0u8;32];x.serialize_compressed(&mut b[..]).map_err(|e|e.to_string())?;
        let decoded=Fr::deserialize_compressed(&b[..]).map_err(|e|e.to_string())?;
        need(decoded==x,"endpoint scalar roundtrip")?;Ok(b.iter().map(|x|format!("{x:02x}")).collect())
    }
    fn triples(x:[Fr;3])->Result<[String;3],String>{Ok([scalar(x[0])?,scalar(x[1])?,scalar(x[2])?])}
    fn compare(a:[Fr;3],b:[Fr;3])->Result<(),String>{need(a==b,"endpoint kernel/oracle mismatch")}
    fn checked_count(observed:usize,canonical:usize)->Result<(),String>{need(observed==canonical,"endpoint component census")}
    fn increment(n:usize)->Result<usize,String>{n.checked_add(1).ok_or("endpoint counter overflow".into())}
    fn checked_members(observed:&[u64;40],expected:&[residual::Count;40])->Result<(),String>{
        for tag in 0..40{need(observed[tag]==expected[tag].terms,"endpoint per-member census")?;}Ok(())
    }
    fn row_valid(values:&Vec<Fr>,width:usize)->Result<(),String>{
        need(values.len()==width,"endpoint loader row width")?;
        need(values.capacity()==width,"endpoint loader row capacity")?;
        need(values.iter().all(|x|x.is_zero()||x.is_one()),"endpoint loader non-Boolean")
    }
    fn check_edge(e:&EdgeTerm,left:bool,owner:usize,strides:&[usize;40])->Result<usize,String>{
        crate::work_tree_wiring::check_role2_endpoint_edge(e,left,owner,12,strides)
    }
    fn load(source:&PackedFile,owner:usize,row_peak:&Cell<usize>,packet_peak:&Cell<usize>)->Result<Vec<Fr>,String>{
        need(owner<4096,"endpoint loader owner")?;
        let view=source.native_role0_view()?;view.require_same_source(source)?;
        let packet=view.read_copy(owner)?;need(packet.len()==WIDTH&&packet.capacity_bytes()==131072,"endpoint loader packet")?;
        packet_peak.set(packet_peak.get().max(packet.capacity_bytes()));
        let mut values=Vec::new();values.try_reserve_exact(WIDTH).map_err(|e|e.to_string())?;
        need(values.capacity()==WIDTH,"endpoint loader row capacity")?;
        for i in 0..WIDTH{values.push(Fr::from(u64::from(packet.bit_at(i))));}
        row_valid(&values,WIDTH)?;row_peak.set(row_peak.get().max(bytes(values.capacity())?));
        drop(packet);Ok(values)
    }
    // The oracle owns packed packets only; its LRU is independent of CopyCache.
    struct OracleBits<'a>{source:&'a PackedFile,packets:VecDeque<(usize,PackedOwnerBits)>,peak:usize}
    impl<'a> OracleBits<'a>{
        fn new(source:&'a PackedFile)->Result<Self,String>{let mut packets=VecDeque::new();packets.try_reserve_exact(4).map_err(|e|e.to_string())?;
            need(packets.capacity()<=4,"endpoint oracle cache header capacity")?;Ok(Self{source,packets,peak:0})}
        fn bit(&mut self,wire:usize)->Result<Fr,String>{need(wire<1usize<<32,"endpoint oracle wire")?;let owner=wire>>20;
            if let Some(i)=self.packets.iter().position(|(o,_)|*o==owner){let x=self.packets.remove(i).ok_or("endpoint oracle position")?;self.packets.push_front(x);}
            else{if self.packets.len()==4{self.packets.pop_back();}
                let view=self.source.native_role0_view()?;view.require_same_source(self.source)?;let p=view.read_copy(owner)?;
                need(p.len()==WIDTH&&p.capacity_bytes()==131072,"endpoint oracle packet capacity")?;self.packets.push_front((owner,p));}
            let capacity=self.packets.iter().try_fold(self.packets.capacity()*size_of::<(usize,PackedOwnerBits)>(),|n,(_,p)|add(n,p.capacity_bytes()))?;
            self.peak=self.peak.max(capacity);Ok(Fr::from(u64::from(self.packets[0].1.bit_at(wire&(WIDTH-1)))))
        }
    }
    fn direct(point:&[Fr],index:usize)->Fr {point.iter().enumerate().fold(Fr::one(),|v,(i,q)|v*if(index>>i)&1==1{*q}else{Fr::one()-q})}
    struct OracleWeights{tables:[Vec<Fr>;4],capacity:usize}
    impl OracleWeights{
        fn new(r:&[Fr],u:&[Fr])->Result<Self,String>{need(r.len()==32&&u.len()==32,"endpoint oracle points")?;
            let mut tables:[Vec<Fr>;4]=std::array::from_fn(|_|Vec::new());let mut capacity=0;
            for (i,p)in [&r[..16],&r[16..],&u[..16],&u[16..]].into_iter().enumerate(){
                tables[i].try_reserve_exact(65536).map_err(|e|e.to_string())?;need(tables[i].capacity()==65536,"endpoint oracle table capacity")?;
                for index in 0..65536{tables[i].push(direct(p,index));}capacity=add(capacity,bytes(tables[i].capacity())?)?;
            }need(capacity==8*MIB,"endpoint oracle table model")?;Ok(Self{tables,capacity})
        }
        fn at(&self,phase:usize,index:usize)->Fr{self.tables[2*phase][index&65535]*self.tables[2*phase+1][index>>16]}
    }
    fn polynomial(a:Fr,b:Fr,x0:Fr,x1:Fr,odd:bool)->[Fr;3]{
        let c=a*x0+b;let d=a*(x1-x0);if odd{[Fr::zero(),c,d]}else{[c,d-c,-d]}
    }
    fn oracle(parent:&WorkTreeHistoryPlan,left:bool,owner:usize,strides:&[usize;40],
        source:&PackedFile,r:&[Fr],u:&[Fr],start:Instant,location:&Cell<usize>,completed:&Cell<usize>)->Result<([Fr;3],usize,u64),String>{
        let began=Instant::now();let weights=OracleWeights::new(r,u)?;now(start)?;
        let mut bits=OracleBits::new(source)?;let mut out=[Fr::zero();3];let mut count=0u64;
        crate::work_tree_wiring::visit_full_roster_endpoint(parent.topology(),fixed::engine()?,parent.fixed_profile(),
            parent.leaf_boundary(),parent.work_boundary(),left,owner,&mut |e|{
                location.set(e.term.row);
                check_edge(&e,left,owner,strides)?;let g=&e.term.gate;let row=weights.at(0,e.term.row);
                let (wire,a,b)=if left{let y=if !g.c2.is_zero()||!g.c3.is_zero(){bits.bit(g.right)?}else{Fr::zero()};
                    (g.left,row*(g.c1+g.c3*y),row*(g.c0+g.c2*y))}
                else{let w=row*weights.at(1,g.left);(g.right,w*(g.c2+g.c3*Fr::from(RECIPE.left_value)),w*(g.c0+g.c1*Fr::from(RECIPE.left_value)))};
                let pair=wire&!1;let x0=bits.bit(pair)?;let x1=bits.bit(pair+1)?;
                for (o,c)in out.iter_mut().zip(polynomial(a,b,x0,x1,wire&1!=0)){*o+=c;}
                count=count.checked_add(1).ok_or("endpoint oracle count overflow")?;
                completed.set(usize::try_from(count).map_err(|_|"endpoint completed conversion")?);
                if count%65536==0{now(start)?;}Ok(())})?;
        let capacity=add(weights.capacity,bits.peak)?;need(capacity<=16*MIB,"endpoint oracle capacity")?;
        Ok((out,capacity,u64::try_from(began.elapsed().as_nanos()).map_err(|_|"endpoint oracle clock")?))
    }
    #[derive(Serialize)]struct Capacity{lookup:usize,loader_row:usize,loader_packet:usize,cache:usize,x:usize,banks:usize,oracle:usize,peak_bound:usize}
    #[derive(Serialize)]struct Component{phase:&'static str,owner:usize,canonical_count:usize,observed_count:usize,
        kernel_coefficients:[String;3],oracle_coefficients:[String;3],equal:bool,kernel_ns:u64,oracle_ns:u64,capacity:Capacity}
    #[derive(Serialize)]struct Member<'a>{tag:usize,name:&'a str,stride_log:usize,terms:u64,rows:u64,left_terms:u64,right_terms:u64}
    #[derive(Serialize)]struct Census<'a>{left_terms:u64,right_terms:u64,left_counts_sha256:String,right_counts_sha256:String,members:&'a [Member<'a>]}
    #[derive(Serialize)]struct Scope{input_log:usize,row_log:usize,owners:usize,active_headers:usize,members:usize,component_only:bool,
        full_u:bool,full_v:bool,gkr:bool,pcs:bool,production:bool,deadline_seconds:usize,component_limit_bytes:usize,producer_limit_bytes:usize,job_limit_bytes:usize,
        loader_mode:&'static str}
    #[derive(Serialize)]struct Inputs{raw_sha256:&'static str,witness_sha256:&'static str,witness_blake2b256:&'static str}
    #[derive(Serialize)]struct Checks{ordinary:bool,n3_multiset:bool,inverse_maps:bool,masks:bool,typed_reads:bool,detached_source:bool,census:bool,components:bool,custody:bool}
    #[derive(Serialize)]struct Report<'a>{schema:&'static str,state:&'static str,stage:&'static str,error:Option<&'a str>,scope:Scope,inputs:Inputs,recipe:Recipe,
        census:Census<'a>,components:&'a [Component],checks:Checks,elapsed_ns:u64}
    struct Writer{bytes:Vec<u8>}
    impl Writer{fn new()->Result<Self,String>{let mut bytes=Vec::new();bytes.try_reserve_exact(REPORT).map_err(|e|e.to_string())?;
        need(bytes.capacity()==REPORT,"endpoint report capacity")?;Ok(Self{bytes})}}
    impl Write for Writer{fn write(&mut self,b:&[u8])->std::io::Result<usize>{if self.bytes.len().checked_add(b.len()).is_none_or(|n|n>REPORT){
            return Err(std::io::Error::other("endpoint report cap"));}self.bytes.extend_from_slice(b);Ok(b.len())}
        fn flush(&mut self)->std::io::Result<()>{Ok(())}}
    fn digest_counts(counts:&[usize])->Result<String,String>{need(counts.len()==4096,"endpoint count digest width")?;
        let mut bytes=Vec::new();bytes.try_reserve_exact(32768).map_err(|e|e.to_string())?;need(bytes.capacity()==32768,"endpoint digest capacity")?;
        for n in counts{bytes.extend_from_slice(&u64::try_from(*n).map_err(|_|"endpoint count conversion")?.to_le_bytes());}
        Ok(screen_hex(&crate::native_prefix_auth_plan::role0_sha256(&bytes)?))}
    // Actual replay hook against an independent tiny per-occurrence oracle.
    // Only the producer side is mutated; the reference Terms stay unchanged.
    fn toy_controls()->Result<(),String>{
        let r=[Fr::from(3),Fr::from(5),Fr::from(7),Fr::from(11)];
        let u=[Fr::from(13),Fr::from(17),Fr::from(19),Fr::from(23)];
        let values=(0..16).map(|i|Fr::from((i&1)as u64)).collect::<Vec<_>>();
        let term=Term{row:1,gate:crate::gkr::Gate{left:1,right:5,c0:Fr::from(7),c1:Fr::from(2),c2:Fr::from(3),c3:Fr::from(5)}};
        for left in [true,false]{let owner=if left{0}else{1};
            let reference={let g=&term.gate;let row=direct(&r,term.row);
                let(wire,a,b)=if left{(g.left,row*(g.c1+g.c3*values[g.right]),row*(g.c0+g.c2*values[g.right]))}
                    else{let w=row*direct(&u,g.left);(g.right,w*(g.c2+g.c3*Fr::from(17)),w*(g.c0+g.c1*Fr::from(17)))};
                polynomial(a,b,values[wire&!1],values[(wire&!1)+1],wire&1!=0)};
            for fault in 0..11{if left&&matches!(fault,8|9){continue;}
                let mut changed=term.clone();match fault{1=>changed.gate.c3+=Fr::one(),2=>changed.gate.left^=1,
                3=>changed.row^=1,10=>{if left{changed.gate.left^=1;}else{changed.gate.right^=1;}},_=>{}}
                let mut producer_u=u;if fault==8{producer_u[0]+=Fr::one();}
                let weights=edge::EdgeFallbackWeightsForTest::new(&r,&producer_u,2);
                let producer_a=Fr::from(if fault==9{18u64}else{17u64});
                let decoded_fault=if fault==7{Some((if left{changed.gate.left}else{changed.gate.right})%4)}else{None};
                let count=if fault==4{2}else{1};
                let result=edge::edge_fallback_prefix_for_test(left,owner,2,2,2,0,&[2],count,&weights,producer_a,&[],
                    |side,selected,sink|{need(side==left&&selected==owner,"endpoint toy route")?;
                        sink(EdgeTerm{source_slot:0,family_row:changed.row,term:changed.clone()})},
                    |o|{if fault==5{return Err("endpoint toy isolated IO".into());}
                        let mut row=values[4*o..4*o+4].to_vec();if fault==6{row.pop();}Ok(row)},decoded_fault);
                match fault{0=>{let actual:[Fr;3]=result?.message.as_slice().try_into().map_err(|_|"endpoint toy triple")?;compare(actual,reference)?;},
                    1..=3|7..=10=>{let actual:[Fr;3]=result?.message.as_slice().try_into().map_err(|_|"endpoint toy mutant triple")?;
                        need(compare(actual,reference).unwrap_err()=="endpoint kernel/oracle mismatch","endpoint toy sensitivity")?;},
                    4=>need(result.err().ok_or("endpoint toy count accepted")?=="edge endpoint source count changed between passes","endpoint toy count identity")?,
                    5=>need(result.err().ok_or("endpoint toy IO accepted")?=="endpoint toy isolated IO","endpoint toy IO identity")?,
                    _=>need(result.err().ok_or("endpoint toy short accepted")?==crate::gkr::GkrError::InvalidInputWidth.to_string(),"endpoint toy short identity")?,
                }
            }
        }Ok(())
    }
    fn pure()->Result<(),String>{
        let(r,u)=points();
        for x0 in [Fr::zero(),Fr::one()]{for x1 in [Fr::zero(),Fr::one()]{for odd in [false,true]{
            let p=polynomial(Fr::from(5),Fr::from(7),x0,x1,odd);
            for z in [Fr::zero(),Fr::one(),Fr::from(11)]{let expected=(if odd{z}else{Fr::one()-z})*(Fr::from(5)*(x0+(x1-x0)*z)+Fr::from(7));
                need(crate::gkr::eval_polynomial(&p,z)==expected,"endpoint ordinary polynomial")?;}
        }}}
        let weights=OracleWeights::new(&r,&u)?;
        for phase in 0..2{for index in std::iter::once(0).chain((0..32).map(|bit|1usize<<bit)).chain([65535,65536,(1usize<<32)-1]){
            need(weights.at(phase,index)==direct(if phase==0{&r}else{&u},index),"endpoint ordinary lookup")?;}}
        let mut strides=[11;40];strides[0]=2;
        let t=Term{row:4,gate:crate::gkr::Gate{left:WIDTH,right:0,c0:Fr::zero(),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()}};
        let e=EdgeTerm{source_slot:1,family_row:0,term:t};check_edge(&e,true,1,&strides)?;
        let mut bad=e.clone();bad.term.row+=1;need(check_edge(&bad,true,1,&strides).unwrap_err()=="endpoint exact canonical row","endpoint row negative")?;
        bad=e.clone();bad.source_slot=4096;need(check_edge(&bad,true,1,&strides).unwrap_err()=="endpoint member/source","endpoint source negative")?;
        bad=e.clone();bad.family_row=40<<14;need(check_edge(&bad,true,1,&strides).unwrap_err()=="endpoint member/source","endpoint tag negative")?;
        bad=e.clone();bad.term.gate.left=1usize<<32;need(check_edge(&bad,true,1,&strides).unwrap_err()=="endpoint domain","endpoint domain negative")?;
        need(check_edge(&e,true,0,&strides).unwrap_err()=="endpoint owner mismatch","endpoint owner negative")?;
        bad=e.clone();bad.family_row=4;need(check_edge(&bad,true,1,&strides).unwrap_err()=="edge term row outside family/slot allocation","endpoint stride negative")?;
        bad=e.clone();bad.source_slot=2;need(check_edge(&bad,true,1,&strides).unwrap_err()=="endpoint exact canonical row","endpoint source-coordinate negative")?;
        bad=e.clone();bad.term.row|=1<<26;need(check_edge(&bad,true,1,&strides).unwrap_err()=="endpoint exact canonical row","endpoint zero-extension negative")?;
        let mut altered=strides;altered[0]=3;need(check_edge(&e,true,1,&altered).unwrap_err()=="endpoint exact canonical row","endpoint declared-stride negative")?;
        bad=e.clone();bad.term.gate.right=1usize<<32;need(check_edge(&bad,true,1,&strides).unwrap_err()=="endpoint domain","endpoint right domain negative")?;
        let a=[Fr::from(1),Fr::from(2),Fr::from(3)];compare(a,a)?;
        for i in 0..3{let mut b=a;b[i]+=Fr::one();need(compare(a,b).unwrap_err()=="endpoint kernel/oracle mismatch","endpoint coefficient negative")?;}
        need(checked_count(4,5).unwrap_err()=="endpoint component census","endpoint count-low negative")?;
        need(checked_count(6,5).unwrap_err()=="endpoint component census","endpoint count-high negative")?;
        let mut expected=[residual::Count::default();40];expected[0].terms=1;
        let mut observed=[0u64;40];observed[0]=1;checked_members(&observed,&expected)?;
        observed[0]=0;observed[1]=1;
        need(checked_members(&observed,&expected).unwrap_err()=="endpoint per-member census","endpoint conserved-total redistribution negative")?;
        need(deadline(300_000_000_001).unwrap_err()=="endpoint deadline","endpoint deadline negative")?;
        let mut row=Vec::with_capacity(4);row.extend([Fr::zero();4]);row_valid(&row,4)?;
        row.pop();need(row_valid(&row,4).unwrap_err()=="endpoint loader row width","endpoint width negative")?;
        row.push(Fr::zero());row[1]=Fr::from(2);need(row_valid(&row,4).unwrap_err()=="endpoint loader non-Boolean","endpoint Boolean negative")?;
        let mut excessive=Vec::with_capacity(5);excessive.extend([Fr::zero();4]);
        need(row_valid(&excessive,4).unwrap_err()=="endpoint loader row capacity","endpoint row-capacity negative")?;
        let mut noncanonical=[255u8;32];need(Fr::deserialize_compressed(&noncanonical[..]).is_err(),"endpoint noncanonical scalar")?;
        noncanonical.fill(0);need(scalar(Fr::zero())?=="00".repeat(32),"endpoint scalar zero encoding")?;
        need(add(usize::MAX,1).unwrap_err()=="endpoint size overflow","endpoint size negative")?;
        need(increment(usize::MAX).unwrap_err()=="endpoint counter overflow","endpoint counter negative")?;
        need(scalar(Fr::one())?==format!("01{}","00".repeat(31)),"endpoint scalar LE encoding")?;
        let mut writer=Writer::new()?;need(writer.write_all(&[0;REPORT+1]).is_err()&&writer.bytes.is_empty(),"endpoint report negative")?;
        Ok(())
    }
    #[test]
    fn ordinary_boundaries(){pure().unwrap();toy_controls().unwrap();crate::native_prefix_auth_plan::role2_endpoint_admission_controls().unwrap();
        crate::work_tree_wiring::role2_endpoint_ordinary_controls().unwrap();
        residual::ordinary_boundaries();}
    fn run(start:Instant,stage:&mut &'static str,phase:&mut &'static str,owner:&mut usize,location:&Cell<usize>,
        completed:&Cell<usize>,substage:&Cell<&'static str>)->Result<Vec<u8>,String>{
        *stage="admission";mark(stage,phase,0,now(start)?)?;
        let (raw,raw_id,raw_path)=residual::raw_hold().map_err(|e|format!("{e:?}"))?;
        let path=std::path::PathBuf::from(std::env::var_os("NIPOPOW_NATIVE_U_SEQUENCE_WITNESS").ok_or("endpoint witness env")?);
        let(source,mut held,id)=useq_admit()?;
        *stage="plan";substage.set("plan");completed.set(0);mark(stage,phase,0,now(start)?)?;
        let native=input();let candidate=Candidate{n:3073,root:native.root(),total:native.total_be28(),
            tip:ergo_header_core::blake2b256(native.raw(3073)?),tip_time:native.timestamp(3073)?};
        let parent=WorkTreeHistoryPlan::compile(3073,12,candidate.root,candidate.total)?;drop(native);
        let plan=NativePrefixAuthPlan::compile(&parent,Selection::s12(),candidate)?;let adapter=plan.role2_endpoints(&source,&mut held,start)?;
        *stage="counts";substage.set("counts");completed.set(0);mark(stage,phase,0,now(start)?)?;
        let(expected,strides)=residual::expectations(&parent,&plan).map_err(|e|format!("{e:?}"))?;
        *stage="controls";substage.set("controls");completed.set(0);mark(stage,phase,0,now(start)?)?;
        let view=source.native_role0_view()?;let detached=PackedFile::open_with_limit(&path,32,32)?;
        need(adapter.require_source(&detached).unwrap_err()=="native role0 detached packed source","endpoint detached negative")?;drop(detached);
        for f in [PackedReaderFault::Io,PackedReaderFault::Short,PackedReaderFault::ShortByOneByte]{
            let error=view.reader_fault_for_test(1,f).err().ok_or("endpoint typed read accepted")?;
            let expected=if matches!(f,PackedReaderFault::Io){"native role0 owner read: isolated native role0 reader fault"}
                else{"native role0 owner read: failed to fill whole buffer"};need(error==expected,"endpoint typed read identity")?;
        }
        let mut counts:[Vec<usize>;2]=std::array::from_fn(|_|Vec::new());let mut members=[[0u64;40];2];let mut totals=[0u64;2];
        for side in 0..2{counts[side].try_reserve_exact(4096).map_err(|e|e.to_string())?;need(counts[side].capacity()==4096,"endpoint census capacity")?;
            *phase=if side==0{"LEFT"}else{"RIGHT"};*stage="census";mark(stage,phase,0,now(start)?)?;
            for e in 0..4096{*owner=e;let mut count=0usize;completed.set(0);substage.set("census");
                adapter.visit(side==0,e,&mut |item|{location.set(item.term.row);let tag=check_edge(&item,side==0,e,&strides)?;
                    count=increment(count)?;
                    completed.set(count);
                    members[side][tag]=members[side][tag].checked_add(1).ok_or("endpoint member count overflow")?;
                    if count%65536==0{now(start)?;}Ok(())})?;
                counts[side].push(count);totals[side]=totals[side].checked_add(count as u64).ok_or("endpoint census total overflow")?;
                now(start)?;
                if(e+1)%256==0{mark(stage,phase,e+1,now(start)?)?;}
            }need(totals[side]==129277400,"endpoint total census")?;
            checked_members(&members[side],&expected)?;
        }
        let left_hash=digest_counts(&counts[0])?;let right_hash=digest_counts(&counts[1])?;
        let (r,u)=points();
        need(r.capacity()<=32&&u.capacity()<=32,"endpoint point capacity")?;
        let mut components=Vec::new();components.try_reserve_exact(10).map_err(|e|e.to_string())?;need(components.capacity()==10,"endpoint component capacity")?;
        for side in 0..2{for e in SELECTED{*stage="component";*phase=if side==0{"U0"}else{"V0"};*owner=e;mark(stage,phase,e,now(start)?)?;
            completed.set(0);substage.set("kernel");
            let weights=edge::EdgeFallbackWeightsForTest::new(&r,&u,20);let lookup=weights.capacity_bytes();need(lookup<=33*MIB,"endpoint lookup capacity")?;
            // Four rows128MiB, X32MiB, bank old/new96MiB, lookup<=33MiB,
            // loader packet128KiB and16MiB control/oracle reservation fit320MiB.
            need(add(add(add(add(128*MIB,32*MIB)?,96*MIB)?,lookup)?,16*MIB+131072)?<=COMPONENT,"endpoint component preflight")?;
            let row_peak=Cell::new(0);let packet_peak=Cell::new(0);let mut observed=0usize;let began=Instant::now();
            let result=edge::edge_fallback_prefix_for_test(side==0,e,20,12,14,6,&strides,counts[side][e],&weights,Fr::from(RECIPE.left_value),&[],
                |left,requested,sink|{need(left==(side==0)&&requested==e,"endpoint component route")?;
                    adapter.visit(left,requested,&mut |item|{location.set(item.term.row);check_edge(&item,left,requested,&strides)?;
                        let next=increment(observed)?;sink(item)?;observed=next;
                        completed.set(observed);
                        if observed%65536==0{now(start)?;}Ok(())})},
                |o|load(&source,o,&row_peak,&packet_peak),None)?;
            let kernel_ns=u64::try_from(began.elapsed().as_nanos()).map_err(|_|"endpoint kernel clock")?;
            checked_count(observed,counts[side][e])?;need(result.metrics.visits==observed as u64,"endpoint component metric census")?;
            let kernel:[Fr;3]=result.message.as_slice().try_into().map_err(|_|"endpoint kernel triple")?;
            let cache=result.metrics.cache_capacity_peak_bytes;let banks=result.metrics.bank_capacity_peak_bytes;
            let x=result.x_capacity_bytes;need(row_peak.get()==32*MIB&&x==32*MIB&&packet_peak.get()<=131072&&cache<=128*MIB&&banks<=96*MIB,"endpoint actual capacities")?;
            drop(result);drop(weights);now(start)?;
            completed.set(0);substage.set("oracle");
            let(reference,oracle_capacity,oracle_ns)=oracle(&parent,side==0,e,&strides,&source,&r,&u,start,location,completed)?;
            compare(kernel,reference)?;
            let generic_peak=add(add(add(add(add(lookup,cache)?,x)?,banks)?,packet_peak.get())?,16*MIB)?;
            let oracle_peak=add(lookup,oracle_capacity.max(16*MIB))?;
            let peak_bound=generic_peak.max(oracle_peak);
            need(peak_bound<=COMPONENT,"endpoint peak bound")?;
            components.push(Component{phase:*phase,owner:e,canonical_count:counts[side][e],observed_count:observed,
                kernel_coefficients:triples(kernel)?,oracle_coefficients:triples(reference)?,equal:kernel==reference,kernel_ns,oracle_ns,
                capacity:Capacity{lookup,loader_row:row_peak.get(),loader_packet:packet_peak.get(),cache,x,banks,oracle:oracle_capacity,peak_bound}});
        }}
        *stage="custody";*phase="none";*owner=4096;substage.set("custody");completed.set(0);location.set(0);mark(stage,phase,4096,now(start)?)?;
        residual::raw_hash(&raw).map_err(|e|format!("{e:?}"))?;residual::packed_hash(&mut held).map_err(|e|format!("{e:?}"))?;
        let raw_check=OpenOptions::new().read(true).share_mode(1).open(raw_path).map_err(|e|e.to_string())?;
        need(u0_file_info(&raw)?==raw_id&&u0_file_info(&raw_check)?==raw_id,"endpoint RAW custody")?;
        let check=u0_open_bytes(&path)?;need(u0_file_info(&held)?==id&&u0_file_info(&check)?==id,"endpoint packed custody")?;
        adapter.require_source(&source)?;
        let member_rows:[Member<'_>;40]=std::array::from_fn(|tag|Member{tag,name:&plan.descriptors()[2].ordered_tags[tag],stride_log:strides[tag],
            terms:expected[tag].terms,rows:expected[tag].rows,left_terms:members[0][tag],right_terms:members[1][tag]});
        let elapsed_ns=now(start)?;
        let report=Report{schema:"native-role2-endpoint-probe-v1",state:"ENDPOINT_COMPONENTS_PASS",stage:"complete",error:None,
            scope:Scope{input_log:32,row_log:32,owners:4096,active_headers:3073,members:40,component_only:true,full_u:false,full_v:false,
                gkr:false,pcs:false,production:false,deadline_seconds:300,component_limit_bytes:COMPONENT,producer_limit_bytes:512*MIB,job_limit_bytes:2048*MIB,
                loader_mode:"packed_owner_bits_to_fr"},recipe:RECIPE,
            inputs:Inputs{raw_sha256:"ABB3D74AE75256CED63110B72C2E0D5EBA1B90B09889E45EA327BDA1C9A640D2",
                witness_sha256:"C1CC1CF72FF539F259A3BDEF756332BA52CB8AFF26C11AB4116D1B2F9D17ED43",
                witness_blake2b256:"725D7B1215E1185C52C1012D9294260612653ACAD53A02429B8EAAFD0F0770C8"},
            census:Census{left_terms:totals[0],right_terms:totals[1],left_counts_sha256:left_hash,right_counts_sha256:right_hash,members:&member_rows},
            components:&components,checks:Checks{ordinary:true,n3_multiset:true,inverse_maps:true,masks:true,typed_reads:true,detached_source:true,
                census:true,components:true,custody:true},elapsed_ns};
        let mut writer=Writer::new()?;serde_json::to_writer(&mut writer,&report).map_err(|e|e.to_string())?;
        now(start)?;*stage="complete";mark(stage,phase,4096,elapsed_ns)?;Ok(writer.bytes)
    }
    #[test]
    #[ignore="native endpoint census and ten isolated U0/V0 components; reviewed300s/Job2GiB/Rayon4 controller"]
    fn native_role2_endpoint_probes_bounded(){let start=Instant::now();let(mut stage,mut phase,mut owner)=("admission","none",0usize);
        let location=Cell::new(0usize);let completed=Cell::new(0usize);let substage=Cell::new("admission");
        let result=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||run(start,&mut stage,&mut phase,&mut owner,&location,&completed,&substage)))
            .unwrap_or_else(|_|Err("endpoint panic".into()));
        let encoded=match &result{Ok(b)=>b.clone(),Err(error)=>{let _=mark("hold",phase,owner,screen_ns(start));
            let reason=error.chars().take(256).collect::<String>();serde_json::to_vec(&serde_json::json!({"schema":"native-role2-endpoint-probe-v1",
                "state":"HOLD","stage":stage,"error":{"code":reason,"phase":phase,"owner":owner,"row":location.get(),
                    "completed_count":completed.get(),"substage":substage.get()}})).unwrap()}};
        assert!(encoded.len()<=REPORT);let mut out=std::io::stdout().lock();out.write_all(b"\nNATIVE_ROLE2_ENDPOINT_REPORT ").unwrap();
        out.write_all(&encoded).unwrap();out.write_all(b"\n").unwrap();out.flush().unwrap();drop(out);assert!(result.is_ok(),"native endpoint HOLD");
    }
}
use ark_bn254::Fr;
use ark_ff::{One, Zero, PrimeField};
use crate::{native_prefix_auth_plan::*, daa_history_roster::{DaaHistoryRoster,OwnerClass},
    historical_prefix_height_work::HeightWork, packed_owner_assembly::NativePrefix,
    sparse::Term, work_tree_history_plan::WorkTreeHistoryPlan,
    work_tree_layout as layout, work_tree_wiring::eq_index};
use std::{fs::OpenOptions,io::Read};
use std::os::windows::fs::OpenOptionsExt;



// Stateful native U diagnostics. Production decoding/kernel/transcript are shared;
// reference banks, message expansion, folds and sender replay are independent.
const USEQ_CONTROL_NAMES:[&str;12]=["positive_exact","omission_rejected","duplicate_rejected",
    "decoded_bit_rejected","bad_sumcheck_rejected","weight_orientation_exact","positive_sequence",
    "cross_left_rejected","stale_challenge_rejected","reset_claim_rejected","wrong_claim_rejected",
    "terminal_scalar_rejected"];
fn useq_message(a:&[Fr],b:&[Fr],x:&[Fr])->[Fr;3] {
    let mut out=[Fr::zero();3];
    for i in (0..x.len()).step_by(2) {
        let (da,db,dx)=(a[i+1]-a[i],b[i+1]-b[i],x[i+1]-x[i]);
        out[0]+=a[i]*x[i]+b[i];out[1]+=a[i]*dx+da*x[i]+db;out[2]+=da*dx;
    } out
}
fn useq_fold(v:&mut Vec<Fr>,q:Fr){let n=v.len()/2;
    for i in 0..n {v[i]=v[2*i]+q*(v[2*i+1]-v[2*i]);}v.truncate(n);
}
fn useq_reference_send(p:[Fr;3],previous:Fr,t:&mut crate::transcript::Transcript)->Result<(Fr,Fr),String>{
    whole_require(p[0]+p[0]+p[1]+p[2]==previous,"sequence independent prior claim")?;
    t.append_bytes(b"gkr-sumcheck-polynomial",&3u64.to_le_bytes());
    for c in p {t.append_scalar(b"gkr-polynomial-coefficient",&c);}
    let q=t.challenge_scalar(b"gkr-sumcheck-challenge");Ok((q,p[0]+q*p[1]+q*q*p[2]))
}
fn useq_toy_oracle(terms:&[Term],input:&[Fr],r:&[Fr],qs:&[Fr],left_fault:bool)
    ->(Vec<[Fr;3]>,Vec<[Fr;3]>) {
    let mut sums=vec![[Fr::zero();3];qs.len()];let mut terminal=Vec::new();
    for owner in 0..8 {
        let mut a=vec![Fr::zero();4];let mut b=a.clone();let mut x=input[4*owner..4*owner+4].to_vec();
        for t in terms.iter().filter(|t|t.gate.left/4==owner) {
            let mut l=t.gate.left%4;if left_fault && t.row==2 {assert_eq!(l,0);l=1;}
            let w=u0_direct_weight(r,t.row);let y=input[t.gate.right];
            a[l]+=w*(t.gate.c1+t.gate.c3*y);b[l]+=w*(t.gate.c0+t.gate.c2*y);
        }
        for (j,q) in qs.iter().enumerate(){for (sum,c) in sums[j].iter_mut().zip(useq_message(&a,&b,&x)){*sum+=c;}
            useq_fold(&mut a,*q);useq_fold(&mut b,*q);useq_fold(&mut x,*q);}
        if qs.len()==2 {terminal.push([a[0],b[0],x[0]]);}
    }(sums,terminal)
}
fn useq_controls(results:&mut serde_json::Value)->Result<(),String>{
    use crate::{gkr::Gate,sparse_stream_roster as s,transcript::Transcript};
    u0_controls(results)?;
    let input=(0..8).flat_map(|o|[Fr::from((o&1) as u64),Fr::from(((o>>1)&1) as u64),
        Fr::from(((o>>2)&1) as u64),Fr::one()]).collect::<Vec<_>>();
    let mut terms=Vec::new();
    for o in 0..8 {let (left,right)=(4*o,4*((o+5)%8)+3);let (c1,c2,c3)=(Fr::from(2),Fr::from(3),Fr::from(5));
        terms.push(Term{row:o,gate:Gate{left,right,c0:-(c1*input[left]+c2*input[right]+c3*input[left]*input[right]),c1,c2,c3}});}
    terms.push(Term{row:7,gate:Gate{left:28,right:0,c0:Fr::zero(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}});
    let mut t=Transcript::new(b"native-u-sequence-eight-owner-control-v1");
    let r=crate::gkr::output_point(8,&mut t);crate::gkr::append_usize(&mut t,b"gkr-layer-index",0);
    let mut reference=t.clone();let counts=(0..8).map(|o|terms.iter().filter(|t|t.gate.left/4==o).count()).collect::<Vec<_>>();
    let result=s::edge_u_sequence_for_test(2,3,0,0,&[0],&counts,&r,2,&mut t,
        |left,o,sink|{whole_require(left,"toy LEFT")?;for term in terms.iter().filter(|t|t.gate.left/4==o){
            sink(s::EdgeTerm{source_slot:term.row,family_row:0,term:term.clone()})?;}Ok(())},
        |o|Ok(input[4*o..4*o+4].to_vec()),|_|Ok(()))?;
    let qs=result.rounds.iter().map(|x|x.challenge).collect::<Vec<_>>();
    let (polys,terminal)=useq_toy_oracle(&terms,&input,&r,&qs,false);
    for (j,round) in result.rounds.iter().enumerate(){
        whole_require(polys[j]==round.polynomial,"toy sequence polynomial")?;
        let (q,claim)=useq_reference_send(polys[j],round.previous_claim,&mut reference)?;
        whole_require(q==round.challenge && claim==round.claim && u0_counters(&reference)==round.counters
            && reference.clone().challenge_scalar(b"native-u-sequence-continuation")==round.continuation,"toy sequence sender")?;
    }
    whole_require(terminal==result.terminals && qs[0]!=Fr::zero() && qs[0]!=Fr::one()
        && !result.rounds[0].claim.is_zero(),"toy nondegenerate prefix/claim")?;
    let cross=useq_toy_oracle(&terms,&input,&r,&qs,true).0;
    whole_require(terms[2].gate.right/4!=2 && cross[0]!=polys[0],"toy LEFT association sensitivity")?;
    results["cross_left_rejected"]=serde_json::json!(true);
    let mut stale=qs.clone();stale[0]+=Fr::one();
    whole_require(useq_toy_oracle(&terms,&input,&r,&stale,false).0[1]!=polys[1],"toy stale prefix sensitivity")?;
    results["stale_challenge_rejected"]=serde_json::json!(true);
    let before_second={let mut rt=Transcript::new(b"native-u-sequence-eight-owner-control-v1");
        crate::gkr::output_point(8,&mut rt);crate::gkr::append_usize(&mut rt,b"gkr-layer-index",0);
        useq_reference_send(polys[0],Fr::zero(),&mut rt)?;rt};
    whole_require(s::edge_u_sequence_send_for_test(polys[1],Fr::zero(),&mut before_second.clone()).is_err(),"toy reset claim accepted")?;
    results["reset_claim_rejected"]=serde_json::json!(true);
    whole_require(s::edge_u_sequence_send_for_test(polys[1],result.rounds[0].claim+Fr::one(),&mut before_second.clone()).is_err(),
        "toy wrong prior accepted")?;results["wrong_claim_rejected"]=serde_json::json!(true);
    let mut bad=terminal.clone();bad[2][0]+=Fr::one();
    whole_require(useq_terminal_compare(bad[2],result.terminals[2]).is_err(),"toy terminal fault")?;
    results["terminal_scalar_rejected"]=serde_json::json!(true);
    // An all-GLOBAL0 toy isolates semantic coverage from physical loader misses.
    let physical=std::cell::RefCell::new([false;8]);let counts=vec![1usize;8];let mut seen=[0usize;2];
    let mut qt=Transcript::new(b"native-u-sequence-cache-coverage-v1");
    s::edge_u_sequence_for_test(2,3,0,0,&[0],&counts,&r,2,&mut qt,|_,o,sink|{
        sink(s::EdgeTerm{source_slot:o,family_row:0,term:Term{row:o,gate:Gate{left:4*o,right:0,
            c0:Fr::zero(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}}})},
        |o|{physical.borrow_mut()[o]=true;Ok(input[4*o..4*o+4].to_vec())},
        |event|{match event {
            s::EdgeUSequenceEvent::Begin(_)=>*physical.borrow_mut()=[false;8],
            s::EdgeUSequenceEvent::Closed(round)=>{seen[round.round]=physical.borrow().iter().filter(|x|**x).count();
                whole_require(round.metrics.fallback.vector_clones==8 && round.polynomial==[Fr::zero();3],"toy semantic coverage")?;},
            _=>{} }Ok(())})?;
    whole_require(seen==[8,7],"toy persistent cache must preserve semantic8/physical7")?;
    let nonce=std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map_err(|e|e.to_string())?.as_nanos();
    let from=std::env::temp_dir().join(format!("native-useq-{}-{nonce}.part",std::process::id()));
    let to=from.with_extension("closed");
    let fixture_metrics=useq_metrics(&result.rounds[0].metrics,result.rounds[0].wall_ns,&USeqLoad::default(),
        (0,0),crate::packed::PackedIoSnapshot::default(),crate::packed::PackedIoSnapshot::default())?;
    let ready=useq_closed_value(&result.rounds[0],&fixture_metrics)?;
    whole_require(ready["state"]=="CANDIDATE_COMPLETE" && from.extension().is_some_and(|x|x=="part"),"ready part fixture")?;
    useq_save(&from,&ready,8192,true)?;
    useq_save(&to,&serde_json::json!({"destination":2}),8192,true)?;
    whole_require(useq_finalize_checkpoint(&from,&to).is_err()
        && std::fs::read(&from).map_err(|e|e.to_string())?==serde_json::to_vec(&ready).map_err(|e|e.to_string())?
        && std::fs::read(&to).map_err(|e|e.to_string())?==b"{\"destination\":2}","toy exclusive checkpoint collision")?;
    std::fs::remove_file(&from).map_err(|e|e.to_string())?;std::fs::remove_file(&to).map_err(|e|e.to_string())?;
    results["positive_sequence"]=serde_json::json!(true);
    whole_require(USEQ_CONTROL_NAMES.iter().all(|k|results[*k]==true),"sequence incomplete controls")
}
#[test]
fn native_u_sequence_controls(){useq_controls(&mut serde_json::json!({})).unwrap();}

fn useq_terminal_compare(actual:[Fr;3],expected:[Fr;3])->Result<(),String>{
    whole_require(actual==expected,"oracle terminal scalar mismatch")
}
fn useq_finalize_checkpoint(from:&std::path::Path,to:&std::path::Path)->Result<(),String>{
    use std::os::windows::ffi::OsStrExt;
    #[link(name="kernel32")]
    extern "system"{fn MoveFileExW(from:*const u16,to:*const u16,flags:u32)->i32;}
    let mut a=from.as_os_str().encode_wide().collect::<Vec<_>>();
    let mut b=to.as_os_str().encode_wide().collect::<Vec<_>>();
    whole_require(!a.contains(&0) && !b.contains(&0),"checkpoint path NUL")?;a.push(0);b.push(0);
    // WRITE_THROUGH only: deliberately no REPLACE_EXISTING; collision is atomic.
    if unsafe{MoveFileExW(a.as_ptr(),b.as_ptr(),8)}==0{return Err(std::io::Error::last_os_error().to_string());}Ok(())
}

fn useq_event(report:&mut serde_json::Value,start:std::time::Instant,count:&mut usize,
    stage:&str,edge:&str,round:Option<usize>,owners:Option<usize>)->Result<(),String>{
    use std::io::Write;
    if edge=="begin" && !matches!(stage,"run"|"final-report"){report["stage"]=serde_json::json!(stage);}
    let value=serde_json::json!({"stage":stage,"edge":edge,"round":round,"completed_owners":owners,
        "elapsed_ns":screen_ns(start),"completed_rounds":report["completed_rounds"]});
    let line=format!("\nNATIVE_U_SEQUENCE_EVENT {value}\n");
    whole_require(line.len()<=256 && *count<if report["mode"]=="decoder-ab"{16}else{152},"sequence event budget")?;
    *count+=1;let mut out=std::io::stdout().lock();out.write_all(line.as_bytes()).map_err(|e|e.to_string())?;
    out.flush().map_err(|e|e.to_string())
}
fn useq_save(path:&std::path::Path,value:&serde_json::Value,cap:usize,new:bool)->Result<(),String>{
    use std::io::Write;
    let bytes=serde_json::to_vec(value).map_err(|e|e.to_string())?;whole_require(bytes.len()<=cap,"sequence artifact cap")?;
    let mut options=OpenOptions::new();options.write(true);if new{options.create_new(true);}else{options.truncate(true);}
    let mut file=options.open(path).map_err(|e|e.to_string())?;
    file.write_all(&bytes).map_err(|e|e.to_string())?;file.sync_all().map_err(|e|e.to_string())?;drop(file);Ok(())
}
fn useq_output()->Result<std::path::PathBuf,String>{
    use std::os::windows::fs::MetadataExt;
    let path=std::env::var_os("NIPOPOW_NATIVE_U_SEQUENCE_OUTPUT_DIR").map(std::path::PathBuf::from).ok_or("sequence output env")?;
    let md=std::fs::symlink_metadata(&path).map_err(|e|e.to_string())?;
    whole_require(md.is_dir() && md.file_attributes()&0x400==0 && std::fs::read_dir(&path).map_err(|e|e.to_string())?.next().is_none(),
        "sequence output not fresh regular directory")?;
    whole_require(!path.canonicalize().map_err(|e|e.to_string())?.starts_with(std::env::temp_dir().canonicalize().map_err(|e|e.to_string())?),
        "sequence output inside TEMP")?;Ok(path)
}
fn useq_admit()->Result<(crate::packed::PackedFile,std::fs::File,U0FileInfo),String>{
    use blake2::{Blake2b,Digest,digest::consts::U32};use std::io::{Seek,SeekFrom};
    let path=std::env::var_os("NIPOPOW_NATIVE_U_SEQUENCE_WITNESS").map(std::path::PathBuf::from).ok_or("sequence witness env")?;
    let mut held=u0_open_bytes(&path)?;let identity=u0_file_info(&held)?;
    let source=crate::packed::PackedFile::open_with_limit(&path,32,32)?;
    whole_require(source.input_len()==1usize<<32,"sequence witness geometry")?;
    let mut hash=Blake2b::<U32>::new();let mut scratch=vec![0u8;1<<20];let mut size=0u64;
    loop{let n=held.read(&mut scratch).map_err(|e|e.to_string())?;if n==0{break;}size+=n as u64;hash.update(&scratch[..n]);}
    whole_require(size==536870912 && screen_hex(&hash.finalize())==U0_WITNESS_BLAKE,"sequence held witness digest")?;
    drop(scratch);let check=u0_open_bytes(&path)?;
    whole_require(u0_file_info(&check)?==identity && u0_file_info(&held)?==identity,"sequence held identity")?;
    drop(check);held.seek(SeekFrom::Start(0)).map_err(|e|e.to_string())?;Ok((source,held,identity))
}
fn useq_legacy_row(source:&crate::packed::PackedFile,owner:usize)->Result<Vec<Fr>,String>{
    whole_require(owner<4096,"legacy row owner")?;let mut row=Vec::new();
    row.try_reserve_exact(1<<20).map_err(|e|e.to_string())?;
    for chunk in 0..16 {let values=source.read_copy_legacy_for_test(65536,owner*16+chunk)?;
        whole_require(values.len()==65536,"legacy chunk length")?;row.extend(values);}
    whole_require(row.len()==1<<20 && row.capacity()==1<<20,"legacy row capacity")?;Ok(row)
}
fn useq_ab(report:&mut serde_json::Value,start:std::time::Instant,events:&mut usize,
    samples:&mut Vec<serde_json::Value>)->Result<(),String>{
    useq_event(report,start,events,"source-validation","begin",None,None)?;let admission=std::time::Instant::now();
    let (source,held,identity)=useq_admit()?;
    report["timings_ns"]["source_validation"]=serde_json::json!(screen_ns(admission));
    useq_event(report,start,events,"source-validation","end",None,None)?;
    useq_event(report,start,events,"decoder-ab","begin",None,None)?;let begun=std::time::Instant::now();
    let mut a=[0u64;2];let mut b=[0u64;2];
    for owner in [0usize,2,1023,2048,3072,4095] {
        let expected=useq_legacy_row(&source,owner)?;let warm=crate::packed_rows::read_row(&source,1<<20,owner)?;
        whole_require(expected==warm && warm.capacity()==1<<20,"decoder warmup equality/capacity")?;drop(warm);
        for (block,order) in [["A","B","B","A"],["B","A","A","B"]].into_iter().enumerate(){
            for (position,variant) in order.into_iter().enumerate(){
                source.reset_io_metrics();let now=std::time::Instant::now();
                let row=if variant=="A"{useq_legacy_row(&source,owner)?}else{crate::packed_rows::read_row(&source,1<<20,owner)?};
                let ns=screen_ns(now);let io=source.io_metrics_snapshot();
                whole_require(row==expected && row.capacity()==1<<20 && io.read_calls==16 && io.read_bytes==131072,
                    "decoder measured equality/capacity/IO")?;drop(row);
                if variant=="A"{a[block]+=ns;}else{b[block]+=ns;}
                samples.push(serde_json::json!({"owner":owner,"block":block,"position":position,"variant":variant,
                    "decode_ns":ns,"io_read_calls":io.read_calls,"io_read_bytes":io.read_bytes,
                    "io_read_ns":u64::try_from(io.read_ns).map_err(|_|"decoder IO overflow")?}));
            }
        }
    }
    let an=a.iter().sum::<u64>();let bn=b.iter().sum::<u64>();let benefit=(bn as u128)*10<=(an as u128)*9
        && (0..2).all(|i|b[i]<a[i]);
    report["decoder_ab"]=serde_json::json!({"sample_count":samples.len(),"warmup_count":12,"legacy_ns":an,"lookup_ns":bn,
        "legacy_block_ns":a,"lookup_block_ns":b,"benefit":benefit,"every_fr_equal":true});
    report["timings_ns"]["decoder_ab"]=serde_json::json!(screen_ns(begun));
    whole_require(u0_file_info(&held)?==identity,"decoder final identity")?;
    useq_event(report,start,events,"decoder-ab","end",None,None)?;
    report["source_candidate_result"]=serde_json::json!(if benefit{"AB_PASS"}else{"AB_ONLY"});Ok(())
}
#[derive(Default)]
struct USeqLoad {loads:u64,decode_ns:u64,owners:Vec<bool>,all:Vec<bool>}
fn useq_metrics(m:&crate::sparse_stream_roster::EdgeU0RoundMetrics,wall:u64,load:&USeqLoad,
    baseline:(u64,u64),io:crate::packed::PackedIoSnapshot,io_before:crate::packed::PackedIoSnapshot)
    ->Result<serde_json::Value,String>{
    let f=&m.fallback;let loads=load.loads-baseline.0;
    whole_require(loads<=f.cache_gets,"sequence misses exceed gets")?;
    Ok(serde_json::json!({"wall_ns":wall,"visits":f.visits,"cache_gets":f.cache_gets,"cache_hits":f.cache_gets-loads,
        "vector_clones":f.vector_clones,"replay_folds":f.replay_folds,"x_fold_fields":f.x_fold_fields,
        "bank_fold_entries":f.bank_fold_entries,"bank_capacity_peak_bytes":f.bank_capacity_peak_bytes,
        "cache_capacity_peak_bytes":f.cache_capacity_peak_bytes,"x_capacity_peak_bytes":m.x_capacity_peak_bytes,
        "message_ns":m.message_ns,"fold_ns":f.fold_ns,"weights_capacity_bytes":m.weights_capacity_bytes,
        "loads":loads,"decoded_fields":loads*(1<<20),"decoded_bytes":loads*(1<<20)*32,
        "decode_ns":load.decode_ns-baseline.1,"unique_loaded_owners":load.owners.iter().filter(|x|**x).count(),
        "semantic_owners":f.vector_clones,"io_read_calls":io.read_calls-io_before.read_calls,
        "io_read_bytes":io.read_bytes-io_before.read_bytes,
        "io_read_ns":u64::try_from(io.read_ns-io_before.read_ns).map_err(|_|"sequence IO overflow")?}))
}
fn useq_poly(p:[Fr;3])->Result<Vec<String>,String>{p.iter().map(u0_hex_fr).collect()}
fn useq_closed_value(round:&crate::sparse_stream_roster::EdgeUSequenceRound,metrics:&serde_json::Value)
    ->Result<serde_json::Value,String>{
    Ok(serde_json::json!({"schema":"native-u-sequence-round-v1","version":1,"state":"CANDIDATE_COMPLETE",
        "oracle_pending":true,"round":round.round,"previous_claim":u0_hex_fr(&round.previous_claim)?,
        "polynomial":useq_poly(round.polynomial)?,"challenge":u0_hex_fr(&round.challenge)?,"claim":u0_hex_fr(&round.claim)?,
        "continuation":u0_hex_fr(&round.continuation)?,"transcript_counters":round.counters,"metrics":metrics}))
}
fn useq_native(report:&mut serde_json::Value,start:std::time::Instant,events:&mut usize,
    output:&std::path::Path,k:usize)->Result<(),String>{
    use crate::{sparse_stream_roster as s,transcript::Transcript};
    whole_require((2..=20).contains(&k),"sequence K outside2..20")?;
    let token=std::env::var("NIPOPOW_NATIVE_U_SEQUENCE_AB_RECEIPT_SHA256").map_err(|_|"sequence AB receipt env")?;
    whole_require(token.len()==64 && token.bytes().all(|b|b.is_ascii_digit() || (b'A'..=b'F').contains(&b)),"sequence AB token format")?;
    report["ab_receipt_sha256"]=serde_json::json!(token);
    useq_event(report,start,events,"construction","begin",None,None)?;let began=std::time::Instant::now();
    let native=input();let root=native.root();let total=native.total_be28();
    whole_require(screen_hex(&root)==U0_ROOT && screen_hex(&total)==U0_TOTAL,"sequence parent identity")?;
    let parent=WorkTreeHistoryPlan::compile(3073,12,root,total)?;drop(native);
    let height=HeightWork::compile_history(&parent)?;let daa=DaaHistoryRoster::compile(&parent)?;
    whole_require(height.input_log()==32 && height.row_log()==18 && daa.input_log()==32 && daa.row_log()==31,"sequence relation geometry")?;
    let adapter=Role4EndpointAdapter::new(&height,&daa,Role4EndpointScope::WholeS12)?;
    let binding=adapter.binding();let aliases=binding.whole_alias_identities.ok_or("sequence alias identities")?;
    report["identities"]["aliases"]=serde_json::json!(aliases.iter().flat_map(|x|x.iter()).map(|x|screen_hex(x)).collect::<Vec<_>>());
    report["timings_ns"]["construction"]=serde_json::json!(screen_ns(began));
    useq_event(report,start,events,"construction","end",None,None)?;
    useq_event(report,start,events,"source-validation","begin",None,None)?;let began=std::time::Instant::now();
    let (source,held,identity)=useq_admit()?;report["timings_ns"]["source_validation"]=serde_json::json!(screen_ns(began));
    useq_event(report,start,events,"source-validation","end",None,None)?;
    useq_event(report,start,events,"census","begin",None,Some(0))?;let began=std::time::Instant::now();
    let counts=s::edge_u0_census_for_test(20,12,19,&[19,19],
        |left,owner,sink|adapter.visit_endpoint(&binding,left,owner,|e|sink(e)).map(|_|()),
        |owners,terms|{report["census_terms"]=serde_json::json!(terms);
            if owners%1024==0{useq_event(report,start,events,"census","progress",None,Some(owners))?;}Ok(())})?;
    whole_require(counts.len()==4096 && counts.iter().sum::<usize>() as u64==U0_TERMS,"sequence census")?;
    report["timings_ns"]["census"]=serde_json::json!(screen_ns(began));
    useq_event(report,start,events,"census","end",None,Some(4096))?;
    let mut t=Transcript::new(b"native-s12-role4-u-sequence-diagnostic-v1");
    t.append_bytes(b"source-revision",U0_SOURCE.as_bytes());
    for (label,digest) in [(b"native-fixture-sha256".as_slice(),U0_FIXTURE_SHA),(b"native-fixture-blake2b256".as_slice(),U0_FIXTURE_BLAKE),
        (b"witness-sha256".as_slice(),U0_WITNESS_SHA),(b"witness-blake2b256".as_slice(),U0_WITNESS_BLAKE)]{t.append_bytes(label,&u0_digest(digest)?);}
    t.append_bytes(b"parent-root",&root);t.append_bytes(b"parent-total-work-be28",&total);
    for (label,value) in [(b"headers".as_slice(),3073),(b"slot-log".as_slice(),12),(b"input-log".as_slice(),32),
        (b"row-log".as_slice(),32),(b"role-index".as_slice(),4),(b"local-input-log".as_slice(),20),
        (b"base-row-log".as_slice(),19),(b"family-log".as_slice(),1),(b"height-member-row-log".as_slice(),19),
        (b"daa-member-row-log".as_slice(),19)]{t.append_u64(label,value);}
    for (label,digest) in [b"m1-map".as_slice(),b"m1-descriptor",b"m2-map",b"m2-descriptor"].into_iter()
        .zip(aliases.iter().flat_map(|x|x.iter())){t.append_bytes(label,digest);}
    parent.bind(&mut t);height.bind(&mut t);daa.bind(&mut t);
    let r=crate::gkr::output_point(1usize<<32,&mut t);crate::gkr::append_usize(&mut t,b"gkr-layer-index",0);
    let mut reference=t.clone();let load=std::cell::RefCell::new(USeqLoad{owners:vec![false;4096],all:vec![false;4096],..Default::default()});
    report["storage"]["load_ledger_capacity_bytes"]=serde_json::json!((load.borrow().owners.capacity()+load.borrow().all.capacity())*std::mem::size_of::<bool>());
    let mut baseline=(0u64,0u64);source.reset_io_metrics();let mut io_before=source.io_metrics_snapshot();
    let mut partial_metrics=serde_json::Value::Null;let mut terminal_start=None;
    let candidate_start=std::time::Instant::now();
    let candidate=s::edge_u_sequence_for_test(20,12,19,1,&[19,19],&counts,&r,k,&mut t,
        |left,owner,sink|adapter.visit_endpoint(&binding,left,owner,|e|sink(e)).map(|_|()),
        |owner|{whole_require(owner<4096,"sequence loader owner")?;let began=std::time::Instant::now();
            let row=crate::packed_rows::read_row(&source,1<<20,owner)?;let ns=screen_ns(began);
            whole_require(row.len()==1<<20 && row.capacity()==1<<20,"sequence row capacity")?;
            let mut l=load.borrow_mut();l.loads+=1;l.decode_ns+=ns;l.owners[owner]=true;l.all[owner]=true;Ok(row)},
        |event|{match event {
            s::EdgeUSequenceEvent::Begin(j)=>{
                let mut l=load.borrow_mut();l.owners.fill(false);baseline=(l.loads,l.decode_ns);io_before=source.io_metrics_snapshot();
                useq_event(report,start,events,"candidate-round","begin",Some(j),Some(0))?;
                useq_save(&output.join("candidate-round.part"),&serde_json::json!({"state":"PARTIAL","completed":false,"round":j,
                    "observations":null}),8192,true)?;
            },
            s::EdgeUSequenceEvent::Progress(j,owner,_)=>{if owner%1024==0{useq_event(report,start,events,"candidate-round","progress",Some(j),Some(owner))?;}},
            s::EdgeUSequenceEvent::Arithmetic(j,previous,poly,m,wall)=>{
                let l=load.borrow();partial_metrics=useq_metrics(&m,wall,&l,baseline,source.io_metrics_snapshot(),io_before)?;
                useq_save(&output.join("candidate-round.part"),&serde_json::json!({"state":"PARTIAL","completed":false,"round":j,
                    "observations":{"previous_claim":u0_hex_fr(&previous)?,"polynomial":useq_poly(poly)?,"metrics":partial_metrics}}),8192,false)?;
                whole_require(m.fallback.visits==U0_TERMS && m.fallback.vector_clones==4096
                    && m.fallback.replay_folds==4096*j as u64
                    && m.fallback.x_fold_fields==4096*(0..j).map(|i|(1u64<<20)>>i).sum::<u64>()
                    && (j!=0 || l.owners.iter().all(|x|*x)),"sequence round ledger")?;
            },
            s::EdgeUSequenceEvent::Closed(round)=>{
                if round.round==0{whole_require(round.challenge!=Fr::zero() && round.challenge!=Fr::one() && !round.claim.is_zero(),
                    "sequence degenerate first challenge/claim")?;}
                let value=useq_closed_value(&round,&partial_metrics)?;
                useq_save(&output.join("candidate-round.part"),&value,8192,false)?;
                let dest=output.join(format!("candidate-round-{:02}.json",round.round));
                whole_require(!dest.exists(),"sequence closed checkpoint collision")?;
                useq_finalize_checkpoint(&output.join("candidate-round.part"),&dest)?;
                report["completed_rounds"]=serde_json::json!(round.round+1);
                report["cumulative_loaded_owners"]=serde_json::json!(load.borrow().all.iter().filter(|x|**x).count());
                useq_event(report,start,events,"candidate-round","end",Some(round.round),Some(4096))?;
            },
            s::EdgeUSequenceEvent::TerminalBegin=>{
                terminal_start=Some(std::time::Instant::now());let mut l=load.borrow_mut();l.owners.fill(false);
                baseline=(l.loads,l.decode_ns);io_before=source.io_metrics_snapshot();
                useq_event(report,start,events,"terminal","begin",None,Some(0))?;
            },
            s::EdgeUSequenceEvent::TerminalProgress(owner)=>{if owner%1024==0{useq_event(report,start,events,"terminal","progress",None,Some(owner))?;}},
            s::EdgeUSequenceEvent::TerminalEnd(m,wall)=>{
                report["terminal_metrics"]=useq_metrics(&m,wall,&load.borrow(),baseline,source.io_metrics_snapshot(),io_before)?;
                report["timings_ns"]["terminal"]=serde_json::json!(screen_ns(terminal_start.ok_or("terminal start")?));
                useq_event(report,start,events,"terminal","end",None,Some(4096))?;
            },
        }Ok(())})?;
    report["timings_ns"]["candidate"]=serde_json::json!(screen_ns(candidate_start)-report["timings_ns"]["terminal"].as_u64().unwrap_or(0));
    report["storage"]["round_state_capacity_bytes"]=serde_json::json!(candidate.rounds.capacity()*std::mem::size_of::<s::EdgeUSequenceRound>());
    report["storage"]["terminal_capacity_bytes"]=serde_json::json!(candidate.terminals.capacity()*std::mem::size_of::<[Fr;3]>());
    whole_require(load.borrow().all.iter().all(|x|*x),"sequence cumulative ledger")?;drop(counts);
    useq_event(report,start,events,"oracle","begin",None,Some(0))?;let began=std::time::Instant::now();
    let weights=U0OracleWeights::new(&r)?;let aliases=whole_aliases(&daa)?;
    let numeric=crate::daa_work_actions::DaaWorkActions::new(&parent)?;
    let mut bytes=U0ByteCache{file:held,rows:std::collections::VecDeque::new(),loads:0,bytes:0,capacity_peak:0};
    let mut polys=vec![[Fr::zero();3];k];let mut terms=0u64;let mut fold_ns=0u64;let mut message_ns=0u64;
    report["storage"]["oracle_sums_capacity_bytes"]=serde_json::json!(polys.capacity()*std::mem::size_of::<[Fr;3]>());
    report["storage"]["alias_capacity_bytes"]=serde_json::json!(aliases.capacity()*std::mem::size_of::<OracleTuple>());
    let oracle_io_before=source.io_metrics_snapshot();let mut oracle_x_loads=0u64;
    let mut dense_capacity=0usize;let mut terminal_count=0u64;
    for owner in 0..4096 {
        let mut a=vec![Fr::zero();1<<20];let mut b=vec![Fr::zero();1<<20];let mut x=useq_legacy_row(&source,owner)?;
        oracle_x_loads+=1;
        dense_capacity=dense_capacity.max((a.capacity()+b.capacity()+x.capacity())*std::mem::size_of::<Fr>());
        whole_oracle_partition(&height,&daa,&numeric,&aliases,true,owner,|term|{
            whole_require(term.left/(1<<20)==owner,"oracle LEFT owner")?;
            let y=bytes.bit(term.right)?;let w=weights.at(term.row)?;let l=term.left%(1<<20);
            a[l]+=w*(term.c[1]+term.c[3]*y);b[l]+=w*(term.c[0]+term.c[2]*y);terms+=1;Ok(())})?;
        for (j,round) in candidate.rounds.iter().enumerate(){
            let now=std::time::Instant::now();let p=useq_message(&a,&b,&x);message_ns+=screen_ns(now);
            for (sum,value) in polys[j].iter_mut().zip(p){*sum+=value;}
            let now=std::time::Instant::now();useq_fold(&mut a,round.challenge);useq_fold(&mut b,round.challenge);
            useq_fold(&mut x,round.challenge);fold_ns+=screen_ns(now);
        }
        if k==20{useq_terminal_compare(candidate.terminals[owner],[a[0],b[0],x[0]])?;terminal_count+=1;}
        report["oracle_terms"]=serde_json::json!(terms);
        if (owner+1)%1024==0{useq_event(report,start,events,"oracle","progress",None,Some(owner+1))?;}
    }
    report["oracle_polynomials"]=serde_json::json!(polys.iter().map(|p|useq_poly(*p)).collect::<Result<Vec<_>,_>>()?);
    report["oracle_metrics"]=serde_json::json!({"visits":terms,"row_loads":bytes.loads+oracle_x_loads,
        "read_bytes":bytes.bytes+source.io_metrics_snapshot().read_bytes-oracle_io_before.read_bytes,
        "cache_capacity_peak_bytes":bytes.capacity_peak,"weights_capacity_bytes":weights.capacity_bytes(),
        "dense_capacity_peak_bytes":dense_capacity,"fold_ns":fold_ns,"message_ns":message_ns,
        "terminals_compared":terminal_count,"underlying_source_visits":null});
    whole_require(terms==U0_TERMS && u0_file_info(&bytes.file)?==identity,"oracle coverage/file identity")?;
    report["timings_ns"]["oracle"]=serde_json::json!(screen_ns(began));
    useq_event(report,start,events,"oracle","end",None,Some(4096))?;
    useq_event(report,start,events,"reference-sender","begin",None,None)?;let began=std::time::Instant::now();let mut claim=Fr::zero();
    for (j,round) in candidate.rounds.iter().enumerate(){
        whole_require(polys[j]==round.polynomial && round.previous_claim==claim,"sequence oracle polynomial/claim mismatch")?;
        let (q,next)=useq_reference_send(polys[j],claim,&mut reference)?;
        whole_require(q==round.challenge && next==round.claim && u0_counters(&reference)==round.counters
            && reference.clone().challenge_scalar(b"native-u-sequence-continuation")==round.continuation,"sequence reference sender mismatch")?;
        claim=next;report["round_equalities"][j]=serde_json::json!(true);report["oracle_checked_rounds"]=serde_json::json!(j+1);
    }
    report["terminal_checked"]=serde_json::json!(k==20 && terminal_count==4096);
    report["timings_ns"]["reference_sender"]=serde_json::json!(screen_ns(began));
    useq_event(report,start,events,"reference-sender","end",None,None)?;
    report["source_candidate_result"]=serde_json::json!("SEQUENCE_PASS");Ok(())
}
fn useq_run(sequence:bool){
    use std::io::Write;
    let start=std::time::Instant::now();let mut events=0usize;
    let k=if sequence {std::env::var("NIPOPOW_NATIVE_U_SEQUENCE_ROUNDS").ok().and_then(|s|
        s.parse::<usize>().ok().filter(|k|s==k.to_string())).unwrap_or(0)}else{0};
    let mut report=serde_json::json!({"schema":"native-s12-u-sequence-source-v1","version":1,
        "mode":if sequence{"sequence"}else{"decoder-ab"},"source_candidate_result":"HOLD","stage":"controls","reason":"",
        "elapsed_ns":0,"geometry":{"headers":3073,"slots":4096,"width":1048576,"input_log":32,"row_log":32,"role":4},
        "identities":{"source_revision":U0_SOURCE,"fixture_sha256":U0_FIXTURE_SHA,"fixture_blake2b256":U0_FIXTURE_BLAKE,
            "witness_sha256":U0_WITNESS_SHA,"witness_blake2b256":U0_WITNESS_BLAKE,"parent_root":U0_ROOT,"parent_total":U0_TOTAL,"aliases":null},
        "ab_receipt_sha256":null,"requested_rounds":k,"completed_rounds":0,"oracle_checked_rounds":0,
        "census_terms":0,"oracle_terms":0,"cumulative_loaded_owners":0,
        "controls":USEQ_CONTROL_NAMES.into_iter().map(|k|(k,false)).collect::<std::collections::BTreeMap<_,_>>(),
        "decoder_ab":null,"oracle_metrics":null,"round_equalities":vec![false;k.min(20)],"oracle_polynomials":[],
        "terminal_checked":false,"terminal_metrics":null,"timings_ns":{"controls":0,"construction":0,"source_validation":0,
            "census":0,"candidate":0,"terminal":0,"oracle":0,"reference_sender":0,"decoder_ab":0},
        "storage":{"fr_bytes":std::mem::size_of::<Fr>(),"load_ledger_capacity_bytes":0,"round_state_capacity_bytes":0,
            "terminal_capacity_bytes":0,"oracle_sums_capacity_bytes":0,"alias_capacity_bytes":0}});
    let output=useq_output().expect("sequence fresh output");let mut samples=Vec::new();
    useq_event(&mut report,start,&mut events,"run","begin",None,None).unwrap();
    let result=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||->Result<(),String>{
        useq_event(&mut report,start,&mut events,"controls","begin",None,None)?;let began=std::time::Instant::now();
        useq_controls(&mut report["controls"])?;report["timings_ns"]["controls"]=serde_json::json!(screen_ns(began));
        useq_event(&mut report,start,&mut events,"controls","end",None,None)?;
        if sequence{useq_native(&mut report,start,&mut events,&output,k)}else{useq_ab(&mut report,start,&mut events,&mut samples)}
    })).unwrap_or_else(|_|Err("sequence source panic".into()));
    if let Err(reason)=&result {
        let mut end=reason.len().min(1024);while !reason.is_char_boundary(end){end-=1;}report["reason"]=serde_json::json!(&reason[..end]);
        useq_event(&mut report,start,&mut events,"hold","hold",None,None).expect("sequence HOLD marker");
    }else{report["stage"]=serde_json::json!("final-report");}
    useq_event(&mut report,start,&mut events,"final-report","begin",None,None).unwrap();
    report["elapsed_ns"]=serde_json::json!(screen_ns(start));
    loop{let n=serde_json::to_vec(&report).unwrap().len();if n<=8192{break;}
        let reason=report["reason"].as_str().unwrap().to_owned();assert!(!reason.is_empty(),"sequence empty-reason report exceeds8KiB");
        let cut=reason.char_indices().last().map(|(i,_)|i).unwrap_or(0);report["reason"]=serde_json::json!(&reason[..cut]);}
    if !sequence{useq_save(&output.join("decoder-ab.json"),&serde_json::json!({"summary":report,"samples":samples}),16384,true).unwrap();}
    useq_save(&output.join("summary.json"),&report,8192,true).unwrap();
    let payload=serde_json::to_string(&report).unwrap();let prefix=if sequence{"NATIVE_U_SEQUENCE_REPORT"}else{"NATIVE_U_SEQUENCE_AB_REPORT"};
    let line=format!("\n{prefix} {payload}\n");assert!(line.len()<=if sequence{8224}else{16416});
    let mut out=std::io::stdout().lock();out.write_all(line.as_bytes()).unwrap();out.flush().unwrap();drop(out);
    useq_event(&mut report,start,&mut events,"final-report","end",None,None).unwrap();
    useq_event(&mut report,start,&mut events,"run","end",None,None).unwrap();
    assert!(result.is_ok(),"native U sequence HOLD");
}
#[test]
#[ignore="native decoder A/B; separate120s/2GiB controller"]
fn native_s12_decoder_ab_bounded(){useq_run(false);}
#[test]
#[ignore="native sequential local U; K2 first,separate1200s/2GiB controller"]
fn native_s12_u_sequence_bounded(){useq_run(true);}


// Combined join diagnostics. Existing U-sequence functions above remain literal.
const JH_OWNERS:[usize;6]=[0,2,1023,2048,3072,4095];
const JH_RIGHT_COUNTS:[usize;6]=[2832226,81952,81952,118681,232495,81920];
const JH_CONTINUATION:&[u8]=b"native-u-high-join-continuation-v1";
const JH_K2_POLYS:[[&str;3];2]=[
 ["F1591B75A6BD525591F7CEEEB0B78BFBF356D98849E98F0560E4AD2FFDFBB727","49602DE0F39A8DDD2FD68DB69F4A5857A33A7CE447D5DF5DF4C2D7CE06320024","D8EB9B057BCA7243618C00D9D7FE2B2A8C20558E4829F1BFC854617557C1BC1D"],
 ["A147345E111516EFB533640D59D167B67E205B20FDFBF30B91AB2346F040511F","1E7EE992D6C318FDCD8899157B6A5415CEE2499A997593E500788F8DAF2EBB2E","7F41947F147E651D8BF89707CECDE72DDC28DC3D0257AEADF99CA12315AC1504"]];
const JH_K2_Q:[&str;2]=["576B6DF944575DDF2B8F7691A9A6E7F9ACFB2E42123BC3A38113F6772F422712","2BD4B2D012F00FC0ECDBFD63ED8E8A3F95449D46447E9D5BC496AA469B102529"];
const JH_K2_CLAIM:[&str;2]=["DD4EE6EEE580E670A20787446A0AA45FED9BD9152939893AC92B157BBFBFAA10","9412305FA63C43C525B2F4E61802CE88ACDCA469B9FD1970D76E4F484A257D20"];
fn jh_k2(round:&crate::sparse_stream_roster::EdgeUSequenceRound)->Result<(),String>{
    let j=round.round;if j>=2{return Ok(());}
    whole_require(useq_poly(round.polynomial)?==JH_K2_POLYS[j].map(String::from)
        && u0_hex_fr(&round.challenge)?==JH_K2_Q[j] && u0_hex_fr(&round.claim)?==JH_K2_CLAIM[j],
        "join unchanged-prefix K2 observation mismatch")
}
fn jh_hash_len(n:usize)->Result<u32,String>{whole_require(n<=32768,"join SHA input cap")?;
    u32::try_from(n).map_err(|_|"join SHA length".into())}
fn jh_hash_result(ok:i32,n:u32,out:[u8;32])->Result<String,String>{
    whole_require(ok!=0 && n==32,"join SHA system result")?;Ok(screen_hex(&out))
}
fn jh_sha(bytes:&[u8])->Result<String,String>{
    use std::ffi::c_void;
    #[link(name="crypt32")]
    extern "system"{fn CryptHashCertificate2(alg:*const u16,flags:u32,reserved:*mut c_void,
        data:*const u8,len:u32,out:*mut u8,out_len:*mut u32)->i32;}
    let len=jh_hash_len(bytes.len())?;let alg=[83u16,72,65,50,53,54,0];
    let mut out=[0u8;32];let mut n=32u32;
    // All pointers refer to live bounded buffers for this synchronous ABI call;
    // the algorithm is NUL-terminated, flags/reserved are the documented zeros.
    let ok=unsafe{CryptHashCertificate2(alg.as_ptr(),0,std::ptr::null_mut(),bytes.as_ptr(),len,out.as_mut_ptr(),&mut n)};
    jh_hash_result(ok,n,out)
}
fn jh_commit(output:&std::path::Path,name:&str,value:&serde_json::Value,cap:usize)->Result<String,String>{
    let bytes=serde_json::to_vec(value).map_err(|e|e.to_string())?;
    whole_require(bytes.len()<=cap,"join destination cap")?;let hash=jh_sha(&bytes)?;
    let part=output.join("join.part");useq_save(&part,value,cap,!part.exists())?;
    useq_finalize_checkpoint(&part,&output.join(name))?;Ok(hash)
}
fn jh_part(output:&std::path::Path,value:&serde_json::Value)->Result<(),String>{
    let p=output.join("join.part");useq_save(&p,value,32768,!p.exists())
}
fn jh_event(report:&mut serde_json::Value,start:std::time::Instant,count:&mut usize,
    stage:&str,edge:&str,round:Option<usize>,owners:Option<usize>)->Result<(),String>{
    use std::io::Write;
    if edge=="begin" && !matches!(stage,"run"|"final-report"){report["stage"]=serde_json::json!(stage);}
    let value=serde_json::json!({"stage":stage,"edge":edge,"round":round,"completed_owners":owners,
        "elapsed_ns":screen_ns(start),"completed_rounds":report["completed_rounds"]});
    let line=format!("\nNATIVE_U_HIGH_JOIN_EVENT {value}\n");
    whole_require(line.len()<=256 && *count<156,"join event budget")?;*count+=1;
    let mut out=std::io::stdout().lock();out.write_all(line.as_bytes()).map_err(|e|e.to_string())?;
    out.flush().map_err(|e|e.to_string())
}
fn jh_high_equal(v:&serde_json::Value)->Result<(),String>{
    let a=v.as_array().ok_or("join high record shape")?;
    whole_require(a.len()==11 && a[1]==a[2] && a[3]==a[4] && a[5]==a[6]
        && a[7]==a[8] && a[9]==a[10],"join high observation mismatch")
}
fn jh_v_equal(v:&serde_json::Value)->Result<(),String>{
    let a=v.as_array().ok_or("join V record shape")?;
    whole_require(a.len()==6 && a[1]==a[2] && a[3][0]==a[4][0] && a[5]==true,
        "join V observation mismatch")
}
fn jh_live_equal(actual:Fr,replayed:Fr,oracle:Fr,left:Fr,oracle_left:Fr,
    t:&crate::transcript::Transcript,replay:&crate::transcript::Transcript,reference:&crate::transcript::Transcript)->Result<(),String>{
    whole_require(actual==replayed && actual==oracle && left==oracle_left
        && u0_counters(t)==u0_counters(reference) && u0_counters(t)==u0_counters(replay)
        && t.clone().challenge_scalar(JH_CONTINUATION)==reference.clone().challenge_scalar(JH_CONTINUATION)
        && t.clone().challenge_scalar(JH_CONTINUATION)==replay.clone().challenge_scalar(JH_CONTINUATION),
        "join final live high state mismatch")
}
fn jh_full_u(local:&[Fr],high:&[Fr])->Result<Vec<Fr>,String>{
    whole_require(local.len()==20 && high.len()==12,"join full U geometry")?;
    let mut u=local.to_vec();u.extend_from_slice(high);Ok(u)
}
fn jh_summary()->serde_json::Value{serde_json::json!({
    "schema":"native-u-high-join-summary-v1","version":1,"result":"HOLD","failed_stage":"controls","reason":"",
    "requested_rounds":20,"completed_rounds":0,"high_u_rounds":0,"sampled_v0_owners":[],
    "k20_closure_sha256":null,"join_observations_sha256":null,
    "k20_source_complete":false,"high_u_equal":false,"sampled_v0_equal":false,"elapsed_ns":0})}
fn jh_local_report()->serde_json::Value{serde_json::json!({
    "schema":"native-s12-u-sequence-source-v1","version":1,"mode":"sequence","source_candidate_result":"HOLD",
    "stage":"controls","reason":"","elapsed_ns":0,
    "geometry":{"headers":3073,"slots":4096,"width":1048576,"input_log":32,"row_log":32,"role":4},
    "identities":{"source_revision":U0_SOURCE,"fixture_sha256":U0_FIXTURE_SHA,"fixture_blake2b256":U0_FIXTURE_BLAKE,
        "witness_sha256":U0_WITNESS_SHA,"witness_blake2b256":U0_WITNESS_BLAKE,"parent_root":U0_ROOT,"parent_total":U0_TOTAL,"aliases":null},
    "ab_receipt_sha256":null,"requested_rounds":20,"completed_rounds":0,"oracle_checked_rounds":0,
    "census_terms":0,"oracle_terms":0,"cumulative_loaded_owners":0,
    "controls":USEQ_CONTROL_NAMES.into_iter().map(|k|(k,false)).collect::<std::collections::BTreeMap<_,_>>(),
    "decoder_ab":null,"oracle_metrics":null,"round_equalities":vec![false;20],"oracle_polynomials":[],
    "terminal_checked":false,"terminal_metrics":null,
    "timings_ns":{"controls":0,"construction":0,"source_validation":0,"census":0,"candidate":0,
        "terminal":0,"oracle":0,"reference_sender":0,"decoder_ab":0},
    "storage":{"fr_bytes":std::mem::size_of::<Fr>(),"load_ledger_capacity_bytes":0,"round_state_capacity_bytes":0,
        "terminal_capacity_bytes":0,"oracle_sums_capacity_bytes":0,"alias_capacity_bytes":0}})}

fn jh_join_value(sha:&str,counters:[u64;3],storage:[usize;4])->serde_json::Value{
    serde_json::json!({"schema":"native-u-high-join-observations-v1","version":1,"state":"JOIN_PARTIAL",
        "k20_closure_sha256":sha,"high_rounds":[],"high_u":[],"left_value":null,"oracle_left_value":null,"v0":[],
        "initial_counters":counters,"final_counters":null,
        "storage_bytes":[storage[0],storage[1],storage[2],storage[3],0,0],"timings_ns":[0,0,0,0]})
}
fn jh_closure(local:&serde_json::Value)->serde_json::Value{
    serde_json::json!({"schema":"native-u-high-k20-closure-v1","state":"U20_SOURCE_COMPLETE","oracle_pending":false,"local":local})
}
fn jh_controls()->Result<(),String>{
    use crate::{gkr::Gate,sparse_stream_roster as s,transcript::Transcript};
    whole_require(jh_sha(b"")?=="E3B0C44298FC1C149AFBF4C8996FB92427AE41E4649B934CA495991B7852B855"
        && jh_sha(b"abc")?=="BA7816BF8F01CFEA414140DE5DAE2223B00361A396177A9CB410FF61F20015AD"
        && jh_sha(&vec![0xA5;32768])?=="E755C415EBA1D77C6A3B6DE6B486AE16F1A2270D794FC12A1773E18E1FF94B94",
        "join system SHA known vectors")?;
    whole_require(jh_hash_len(32769).is_err() && jh_hash_result(0,32,[0;32]).is_err()
        && jh_hash_result(1,31,[0;32]).is_err(),"join SHA guard faults")?;
    let a=(0..8).map(|i|Fr::from(i+2)).collect::<Vec<_>>();
    let x=(0..8).map(|i|Fr::from(i*7+3)).collect::<Vec<_>>();
    let b=a.iter().zip(&x).map(|(a,x)|-*a**x).collect::<Vec<_>>();
    let mut t=Transcript::new(b"native-u-high-small-control-v1");let mut replay=t.clone();let mut reference=t.clone();
    let mut claim=Fr::zero();let mut rounds=Vec::new();
    let (point,value)=crate::gkr::prove_phase(a.clone(),b.clone(),&x,&mut claim,&mut rounds,&mut t).map_err(|e|e.to_string())?;
    let (mut oa,mut ob,mut ox)=(a.clone(),b.clone(),x.clone());let (mut prev,mut oprev)=(Fr::zero(),Fr::zero());
    let mut records=Vec::new();
    for j in 0..3 {
        let p:[Fr;3]=rounds[j].as_slice().try_into().map_err(|_|"toy high extent")?;
        let q=useq_message(&oa,&ob,&ox);
        let (replayed,next)=useq_reference_send(p,prev,&mut replay)?;
        let (oracle,other)=useq_reference_send(q,oprev,&mut reference)?;
        let record=serde_json::json!([j,useq_poly(p)?,useq_poly(q)?,u0_hex_fr(&point[j])?,u0_hex_fr(&oracle)?,
            u0_hex_fr(&next)?,u0_hex_fr(&other)?,u0_hex_fr(&replay.clone().challenge_scalar(JH_CONTINUATION))?,
            u0_hex_fr(&reference.clone().challenge_scalar(JH_CONTINUATION))?,u0_counters(&replay),u0_counters(&reference)]);
        whole_require(replayed==point[j],"toy high returned point")?;jh_high_equal(&record)?;records.push(record);
        useq_fold(&mut oa,oracle);useq_fold(&mut ob,oracle);useq_fold(&mut ox,oracle);prev=next;oprev=other;
    }
    whole_require(value==ox[0] && claim==prev && claim==oprev && u0_counters(&t)==u0_counters(&reference)
        && t.clone().challenge_scalar(JH_CONTINUATION)==reference.clone().challenge_scalar(JH_CONTINUATION),
        "toy actual high state")?;
    whole_require(point[0]!=Fr::zero() && point[0]!=Fr::one() && !Fr::from(2).is_zero()
        && !records[0][5].as_str().ok_or("toy claim")?.bytes().all(|b|b==b'0'),"toy high sensitivity")?;
    for field in [1usize,3,5,7,9] {
        let mut bad=records[0].clone();
        if field==1 {bad[field][0]=serde_json::json!(u0_hex_fr(&Fr::one())?);}
        else if field==9 {bad[field][0]=serde_json::json!(u64::MAX);}
        else {bad[field]=serde_json::json!(u0_hex_fr(&Fr::one())?);}
        whole_require(bad!=records[0] && jh_high_equal(&bad).is_err(),"toy high isolated observation fault")?;
    }
    let mut swapped=x.clone();swapped.swap(0,1);
    whole_require(a[0]!=a[1] && x[0]!=x[1]
        && crate::gkr::prove_phase(a.clone(),b.clone(),&swapped,&mut Fr::zero(),&mut Vec::new(),
            &mut Transcript::new(b"native-u-high-small-control-v1")).is_err(),"toy nonzero high X order fault")?;
    let mut changed=t.clone();changed.challenge_scalar(JH_CONTINUATION);
    whole_require(u0_counters(&changed)!=u0_counters(&t),"toy live continuation fault")?;
    jh_live_equal(claim,prev,oprev,value,ox[0],&t,&replay,&reference)?;
    whole_require(jh_live_equal(claim+Fr::one(),prev,oprev,value,ox[0],&t,&replay,&reference).is_err()
        && jh_live_equal(claim,prev,oprev,value+Fr::one(),ox[0],&t,&replay,&reference).is_err()
        && jh_live_equal(claim,prev,oprev,value,ox[0],&changed,&replay,&reference).is_err(),
        "toy actual high final guard faults")?;
    let local=vec![Fr::from(2);20];let high=vec![Fr::from(3);12];let full=jh_full_u(&local,&high)?;
    let mut reversed=high.clone();reversed.extend(local.clone());
    whole_require(full[..20]==local && full[20..]==high && full!=reversed,"toy U concatenation fault")?;
    let prefix=|domain:&[u8],reverse:bool,alter:bool,k:bool,layer:usize|{
        let mut t=Transcript::new(domain);for (l,v) in if reverse {[(b"b",2u64),(b"a",1)]}else{[(b"a",1u64),(b"b",2)]}{
            t.append_u64(l,v+u64::from(alter));}
        if k {t.append_u64(b"K",20);}let r=crate::gkr::output_point(8,&mut t);
        crate::gkr::append_usize(&mut t,b"gkr-layer-index",layer);(r,u0_counters(&t),t.clone().challenge_scalar(JH_CONTINUATION))};
    let good=prefix(b"native-s12-role4-u-sequence-diagnostic-v1",false,false,false,0);
    for bad in [prefix(b"changed-domain",false,false,false,0),
        prefix(b"native-s12-role4-u-sequence-diagnostic-v1",true,false,false,0),
        prefix(b"native-s12-role4-u-sequence-diagnostic-v1",false,true,false,0),
        prefix(b"native-s12-role4-u-sequence-diagnostic-v1",false,false,true,0),
        prefix(b"native-s12-role4-u-sequence-diagnostic-v1",false,false,false,1)]{
        whole_require(good!=bad,"toy prefix mutation")?;
    }
    let input=(0..32).map(|i|Fr::from(i+2)).collect::<Vec<_>>();
    let r=[Fr::from(2),Fr::from(3),Fr::from(5)];let u=[Fr::from(2),Fr::from(3),Fr::from(5),Fr::from(7),Fr::from(11)];
    let left=Fr::from(13);let weights=s::EdgeFallbackWeightsForTest::new(&r,&u,2);
    let mut terms=(0..8).map(|row|Term{row,gate:Gate{left:4*((row+2)%8)+(row+1)%4,right:row%4,
        c0:Fr::from(2),c1:Fr::from(3),c2:Fr::from(5),c3:Fr::from(7)}}).collect::<Vec<_>>();
    terms.push(Term{row:7,gate:Gate{left:0,right:0,c0:Fr::zero(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}});
    let candidate=|ts:&[Term],ww:&s::EdgeFallbackWeightsForTest,ll:Fr|{
        s::edge_fallback_prefix_for_test(false,0,2,3,0,0,&[0],terms.len(),ww,ll,&[],
            |_,_,sink|{for term in ts{sink(s::EdgeTerm{source_slot:term.row,family_row:0,term:term.clone()})?;}Ok(())},
            |o|Ok(input[4*o..4*o+4].to_vec()),None)};
    let reference_poly=|ts:&[Term],uu:&[Fr],ll:Fr|{
        let mut d=vec![Fr::zero();4];let mut e=vec![Fr::zero();4];
        for term in ts {let w=u0_direct_weight(&r,term.row)*u0_direct_weight(uu,term.gate.left);
            d[term.gate.right]+=w*(term.gate.c2+term.gate.c3*ll);
            e[term.gate.right]+=w*(term.gate.c0+term.gate.c1*ll);}
        useq_message(&d,&e,&input[..4])};
    let expected=reference_poly(&terms,&u,left);let actual=candidate(&terms,&weights,left)?;
    whole_require(actual.message==expected && actual.metrics.visits==9,"toy V positive/formal zero coverage")?;
    whole_require(candidate(&terms[..8],&weights,left).is_err(),"toy V omission")?;
    let mut duplicate=terms.clone();duplicate.push(terms[0].clone());
    whole_require(candidate(&duplicate,&weights,left).is_err(),"toy V duplicate")?;
    let mut foreign=terms.clone();foreign[0].gate.right+=4;
    whole_require(candidate(&foreign,&weights,left).is_err(),"toy V foreign RIGHT owner")?;
    let mut coefficient=terms.clone();coefficient[0].gate.c2+=Fr::one();
    whole_require(candidate(&coefficient,&weights,left)?.message!=expected,"toy V coefficient sensitivity")?;
    let mut row=terms.clone();row[0].row=1;
    whole_require(candidate(&row,&weights,left)?.message!=expected,"toy V row-weight sensitivity")?;
    let mut alias=terms.clone();alias[0].gate.left+=4;
    whole_require(alias[0].gate.left/4!=terms[0].gate.left/4
        && candidate(&alias,&weights,left)?.message!=expected,"toy V foreign-left alias sensitivity")?;
    let mut wrong=u;wrong[0]+=Fr::one();let wrong_weights=s::EdgeFallbackWeightsForTest::new(&r,&wrong,2);
    whole_require(candidate(&terms,&wrong_weights,left)?.message!=expected
        && candidate(&terms,&weights,left+Fr::one())?.message!=expected,"toy V U/scalar sensitivity")?;
    let record=serde_json::json!([0,useq_poly(expected)?,useq_poly(expected)?,[9,1,0,0,1,16,131072,1],[9,1,0,0,1,16,131072,1],true]);
    jh_v_equal(&record)?;let mut bad=record.clone();bad[3][0]=serde_json::json!(8);
    whole_require(jh_v_equal(&bad).is_err(),"toy V count observation fault")?;
    jh_size_controls()
}
fn jh_size_controls()->Result<(),String>{
    use crate::sparse_stream_roster::{EdgeUSequenceRound,EdgeU0RoundMetrics};
    let max=serde_json::json!(u64::MAX);let hex=u0_hex_fr(&Fr::zero())?;
    let fake=EdgeUSequenceRound{round:19,previous_claim:Fr::zero(),polynomial:[Fr::zero();3],challenge:Fr::zero(),
        claim:Fr::zero(),continuation:Fr::zero(),counters:[u64::MAX;3],metrics:EdgeU0RoundMetrics::default(),wall_ns:u64::MAX};
    let mut metrics=useq_metrics(&fake.metrics,0,&USeqLoad::default(),(0,0),
        crate::packed::PackedIoSnapshot::default(),crate::packed::PackedIoSnapshot::default())?;
    for v in metrics.as_object_mut().ok_or("max metrics")?.values_mut(){*v=max.clone();}
    whole_require(serde_json::to_vec(&useq_closed_value(&fake,&metrics)?).map_err(|e|e.to_string())?.len()==1609,
        "join actual round factory size")?;
    let mut local=jh_local_report();local["source_candidate_result"]=serde_json::json!("SEQUENCE_PASS");
    local["stage"]=serde_json::json!("reference-sender");local["elapsed_ns"]=max.clone();
    local["identities"]["aliases"]=serde_json::json!(vec![hex.clone();4]);local["ab_receipt_sha256"]=serde_json::json!(hex);
    local["completed_rounds"]=serde_json::json!(20);local["oracle_checked_rounds"]=serde_json::json!(20);
    local["census_terms"]=serde_json::json!(U0_TERMS);local["oracle_terms"]=serde_json::json!(U0_TERMS);
    local["cumulative_loaded_owners"]=serde_json::json!(4096);
    for v in local["controls"].as_object_mut().ok_or("max controls")?.values_mut(){*v=serde_json::json!(true);}
    local["round_equalities"]=serde_json::json!(vec![true;20]);local["oracle_polynomials"]=serde_json::json!(vec![vec![hex.clone();3];20]);
    local["terminal_checked"]=serde_json::json!(true);local["terminal_metrics"]=metrics;
    local["oracle_metrics"]=serde_json::json!({"visits":u64::MAX,"row_loads":u64::MAX,"read_bytes":u64::MAX,
        "cache_capacity_peak_bytes":u64::MAX,"weights_capacity_bytes":u64::MAX,"dense_capacity_peak_bytes":u64::MAX,
        "fold_ns":u64::MAX,"message_ns":u64::MAX,"terminals_compared":u64::MAX,"underlying_source_visits":null});
    for v in local["timings_ns"].as_object_mut().ok_or("max timings")?.values_mut(){*v=max.clone();}
    for (k,v) in local["storage"].as_object_mut().ok_or("max storage")?{if k!="fr_bytes"{*v=max.clone();}}
    whole_require(serde_json::to_vec(&local).map_err(|e|e.to_string())?.len()==7842
        && serde_json::to_vec(&jh_closure(&local)).map_err(|e|e.to_string())?.len()==7945,"join actual closure factory size")?;
    let mut join=jh_join_value(&hex,[u64::MAX;3],[0;4]);
    join["state"]=serde_json::json!("JOIN_SOURCE_COMPLETE");
    join["high_rounds"]=serde_json::json!((0..12).map(|j|serde_json::json!([j,vec![hex.clone();3],vec![hex.clone();3],
        hex,hex,hex,hex,hex,hex,vec![u64::MAX;3],vec![u64::MAX;3]])).collect::<Vec<_>>());
    join["high_u"]=serde_json::json!(vec![hex.clone();12]);join["left_value"]=serde_json::json!(hex);join["oracle_left_value"]=serde_json::json!(hex);
    join["v0"]=serde_json::json!(JH_OWNERS.map(|o|serde_json::json!([o,vec![hex.clone();3],vec![hex.clone();3],
        vec![u64::MAX;8],vec![u64::MAX;8],true])));
    join["final_counters"]=serde_json::json!(vec![u64::MAX;3]);join["storage_bytes"]=serde_json::json!(vec![u64::MAX;6]);
    join["timings_ns"]=serde_json::json!(vec![u64::MAX;4]);
    whole_require(serde_json::to_vec(&join).map_err(|e|e.to_string())?.len()==17440,"join actual observation factory size")?;
    let mut summary=jh_summary();summary["failed_stage"]=serde_json::json!("join-finalization");summary["reason"]=serde_json::json!("\0".repeat(1024));
    summary["completed_rounds"]=serde_json::json!(20);summary["high_u_rounds"]=serde_json::json!(12);
    summary["sampled_v0_owners"]=serde_json::json!(JH_OWNERS);summary["k20_closure_sha256"]=serde_json::json!(hex);
    summary["join_observations_sha256"]=serde_json::json!(hex);summary["elapsed_ns"]=max;
    for k in ["k20_source_complete","high_u_equal","sampled_v0_equal"]{summary[k]=serde_json::json!(true);}
    whole_require(serde_json::to_vec(&summary).map_err(|e|e.to_string())?.len()==6657,"join actual summary factory size")
}
#[test]
fn native_u_high_join_controls(){native_u_sequence_controls();jh_controls().unwrap();}
fn jh_native(report:&mut serde_json::Value,summary:&mut serde_json::Value,start:std::time::Instant,events:&mut usize,
    output:&std::path::Path,k:usize)->Result<(),String>{
    use crate::{sparse_stream_roster as s,transcript::Transcript};
    whole_require(k==20,"join requires K20")?;
    let token=std::env::var("NIPOPOW_NATIVE_U_SEQUENCE_AB_RECEIPT_SHA256").map_err(|_|"sequence AB receipt env")?;
    whole_require(token.len()==64 && token.bytes().all(|b|b.is_ascii_digit() || (b'A'..=b'F').contains(&b)),"sequence AB token format")?;
    report["ab_receipt_sha256"]=serde_json::json!(token);
    jh_event(report,start,events,"construction","begin",None,None)?;let began=std::time::Instant::now();
    let native=input();let root=native.root();let total=native.total_be28();
    whole_require(screen_hex(&root)==U0_ROOT && screen_hex(&total)==U0_TOTAL,"sequence parent identity")?;
    let parent=WorkTreeHistoryPlan::compile(3073,12,root,total)?;drop(native);
    let height=HeightWork::compile_history(&parent)?;let daa=DaaHistoryRoster::compile(&parent)?;
    whole_require(height.input_log()==32 && height.row_log()==18 && daa.input_log()==32 && daa.row_log()==31,"sequence relation geometry")?;
    let adapter=Role4EndpointAdapter::new(&height,&daa,Role4EndpointScope::WholeS12)?;
    let binding=adapter.binding();let aliases=binding.whole_alias_identities.ok_or("sequence alias identities")?;
    report["identities"]["aliases"]=serde_json::json!(aliases.iter().flat_map(|x|x.iter()).map(|x|screen_hex(x)).collect::<Vec<_>>());
    report["timings_ns"]["construction"]=serde_json::json!(screen_ns(began));
    jh_event(report,start,events,"construction","end",None,None)?;
    jh_event(report,start,events,"source-validation","begin",None,None)?;let began=std::time::Instant::now();
    let (source,held,identity)=useq_admit()?;report["timings_ns"]["source_validation"]=serde_json::json!(screen_ns(began));
    jh_event(report,start,events,"source-validation","end",None,None)?;
    jh_event(report,start,events,"census","begin",None,Some(0))?;let began=std::time::Instant::now();
    let counts=s::edge_u0_census_for_test(20,12,19,&[19,19],
        |left,owner,sink|adapter.visit_endpoint(&binding,left,owner,|e|sink(e)).map(|_|()),
        |owners,terms|{report["census_terms"]=serde_json::json!(terms);
            if owners%1024==0{jh_event(report,start,events,"census","progress",None,Some(owners))?;}Ok(())})?;
    whole_require(counts.len()==4096 && counts.iter().sum::<usize>() as u64==U0_TERMS,"sequence census")?;
    report["timings_ns"]["census"]=serde_json::json!(screen_ns(began));
    jh_event(report,start,events,"census","end",None,Some(4096))?;
    let mut t=Transcript::new(b"native-s12-role4-u-sequence-diagnostic-v1");
    t.append_bytes(b"source-revision",U0_SOURCE.as_bytes());
    for (label,digest) in [(b"native-fixture-sha256".as_slice(),U0_FIXTURE_SHA),(b"native-fixture-blake2b256".as_slice(),U0_FIXTURE_BLAKE),
        (b"witness-sha256".as_slice(),U0_WITNESS_SHA),(b"witness-blake2b256".as_slice(),U0_WITNESS_BLAKE)]{t.append_bytes(label,&u0_digest(digest)?);}
    t.append_bytes(b"parent-root",&root);t.append_bytes(b"parent-total-work-be28",&total);
    for (label,value) in [(b"headers".as_slice(),3073),(b"slot-log".as_slice(),12),(b"input-log".as_slice(),32),
        (b"row-log".as_slice(),32),(b"role-index".as_slice(),4),(b"local-input-log".as_slice(),20),
        (b"base-row-log".as_slice(),19),(b"family-log".as_slice(),1),(b"height-member-row-log".as_slice(),19),
        (b"daa-member-row-log".as_slice(),19)]{t.append_u64(label,value);}
    for (label,digest) in [b"m1-map".as_slice(),b"m1-descriptor",b"m2-map",b"m2-descriptor"].into_iter()
        .zip(aliases.iter().flat_map(|x|x.iter())){t.append_bytes(label,digest);}
    parent.bind(&mut t);height.bind(&mut t);daa.bind(&mut t);
    let r=crate::gkr::output_point(1usize<<32,&mut t);crate::gkr::append_usize(&mut t,b"gkr-layer-index",0);
    let mut reference=t.clone();let load=std::cell::RefCell::new(USeqLoad{owners:vec![false;4096],all:vec![false;4096],..Default::default()});
    report["storage"]["load_ledger_capacity_bytes"]=serde_json::json!((load.borrow().owners.capacity()+load.borrow().all.capacity())*std::mem::size_of::<bool>());
    let mut baseline=(0u64,0u64);source.reset_io_metrics();let mut io_before=source.io_metrics_snapshot();
    let mut partial_metrics=serde_json::Value::Null;let mut terminal_start=None;
    let candidate_start=std::time::Instant::now();
    let candidate=s::edge_u_sequence_for_test(20,12,19,1,&[19,19],&counts,&r,k,&mut t,
        |left,owner,sink|adapter.visit_endpoint(&binding,left,owner,|e|sink(e)).map(|_|()),
        |owner|{whole_require(owner<4096,"sequence loader owner")?;let began=std::time::Instant::now();
            let row=crate::packed_rows::read_row(&source,1<<20,owner)?;let ns=screen_ns(began);
            whole_require(row.len()==1<<20 && row.capacity()==1<<20,"sequence row capacity")?;
            let mut l=load.borrow_mut();l.loads+=1;l.decode_ns+=ns;l.owners[owner]=true;l.all[owner]=true;Ok(row)},
        |event|{match event {
            s::EdgeUSequenceEvent::Begin(j)=>{
                let mut l=load.borrow_mut();l.owners.fill(false);baseline=(l.loads,l.decode_ns);io_before=source.io_metrics_snapshot();
                jh_event(report,start,events,"candidate-round","begin",Some(j),Some(0))?;
                useq_save(&output.join("candidate-round.part"),&serde_json::json!({"state":"PARTIAL","completed":false,"round":j,
                    "observations":null}),8192,true)?;
            },
            s::EdgeUSequenceEvent::Progress(j,owner,_)=>{if owner%1024==0{jh_event(report,start,events,"candidate-round","progress",Some(j),Some(owner))?;}},
            s::EdgeUSequenceEvent::Arithmetic(j,previous,poly,m,wall)=>{
                let l=load.borrow();partial_metrics=useq_metrics(&m,wall,&l,baseline,source.io_metrics_snapshot(),io_before)?;
                useq_save(&output.join("candidate-round.part"),&serde_json::json!({"state":"PARTIAL","completed":false,"round":j,
                    "observations":{"previous_claim":u0_hex_fr(&previous)?,"polynomial":useq_poly(poly)?,"metrics":partial_metrics}}),8192,false)?;
                whole_require(m.fallback.visits==U0_TERMS && m.fallback.vector_clones==4096
                    && m.fallback.replay_folds==4096*j as u64
                    && m.fallback.x_fold_fields==4096*(0..j).map(|i|(1u64<<20)>>i).sum::<u64>()
                    && (j!=0 || l.owners.iter().all(|x|*x)),"sequence round ledger")?;
            },
            s::EdgeUSequenceEvent::Closed(round)=>{
                if round.round==0{whole_require(round.challenge!=Fr::zero() && round.challenge!=Fr::one() && !round.claim.is_zero(),
                    "sequence degenerate first challenge/claim")?;}
                let value=useq_closed_value(&round,&partial_metrics)?;
                useq_save(&output.join("candidate-round.part"),&value,4096,false)?;
                jh_k2(&round)?;
                let dest=output.join(format!("candidate-round-{:02}.json",round.round));
                whole_require(!dest.exists(),"sequence closed checkpoint collision")?;
                useq_finalize_checkpoint(&output.join("candidate-round.part"),&dest)?;
                report["completed_rounds"]=serde_json::json!(round.round+1);
                report["cumulative_loaded_owners"]=serde_json::json!(load.borrow().all.iter().filter(|x|**x).count());
                jh_event(report,start,events,"candidate-round","end",Some(round.round),Some(4096))?;
            },
            s::EdgeUSequenceEvent::TerminalBegin=>{
                terminal_start=Some(std::time::Instant::now());let mut l=load.borrow_mut();l.owners.fill(false);
                baseline=(l.loads,l.decode_ns);io_before=source.io_metrics_snapshot();
                jh_event(report,start,events,"terminal","begin",None,Some(0))?;
            },
            s::EdgeUSequenceEvent::TerminalProgress(owner)=>{if owner%1024==0{jh_event(report,start,events,"terminal","progress",None,Some(owner))?;}},
            s::EdgeUSequenceEvent::TerminalEnd(m,wall)=>{
                report["terminal_metrics"]=useq_metrics(&m,wall,&load.borrow(),baseline,source.io_metrics_snapshot(),io_before)?;
                report["timings_ns"]["terminal"]=serde_json::json!(screen_ns(terminal_start.ok_or("terminal start")?));
                jh_event(report,start,events,"terminal","end",None,Some(4096))?;
            },
        }Ok(())})?;
    report["timings_ns"]["candidate"]=serde_json::json!(screen_ns(candidate_start)-report["timings_ns"]["terminal"].as_u64().unwrap_or(0));
    report["storage"]["round_state_capacity_bytes"]=serde_json::json!(candidate.rounds.capacity()*std::mem::size_of::<s::EdgeUSequenceRound>());
    report["storage"]["terminal_capacity_bytes"]=serde_json::json!(candidate.terminals.capacity()*std::mem::size_of::<[Fr;3]>());
    whole_require(load.borrow().all.iter().all(|x|*x),"sequence cumulative ledger")?;drop(counts);
    jh_event(report,start,events,"oracle","begin",None,Some(0))?;let began=std::time::Instant::now();
    let weights=U0OracleWeights::new(&r)?;let aliases=whole_aliases(&daa)?;
    let numeric=crate::daa_work_actions::DaaWorkActions::new(&parent)?;
    let mut bytes=U0ByteCache{file:held,rows:std::collections::VecDeque::new(),loads:0,bytes:0,capacity_peak:0};
    let mut polys=vec![[Fr::zero();3];k];let mut terms=0u64;let mut fold_ns=0u64;let mut message_ns=0u64;
    report["storage"]["oracle_sums_capacity_bytes"]=serde_json::json!(polys.capacity()*std::mem::size_of::<[Fr;3]>());
    report["storage"]["alias_capacity_bytes"]=serde_json::json!(aliases.capacity()*std::mem::size_of::<OracleTuple>());
    let oracle_io_before=source.io_metrics_snapshot();let mut oracle_x_loads=0u64;
    let mut dense_capacity=0usize;let mut terminal_count=0u64;let mut oracle_terminals=Vec::with_capacity(4096);
    for owner in 0..4096 {
        let mut a=vec![Fr::zero();1<<20];let mut b=vec![Fr::zero();1<<20];let mut x=useq_legacy_row(&source,owner)?;
        oracle_x_loads+=1;
        dense_capacity=dense_capacity.max((a.capacity()+b.capacity()+x.capacity())*std::mem::size_of::<Fr>());
        whole_oracle_partition(&height,&daa,&numeric,&aliases,true,owner,|term|{
            whole_require(term.left/(1<<20)==owner,"oracle LEFT owner")?;
            let y=bytes.bit(term.right)?;let w=weights.at(term.row)?;let l=term.left%(1<<20);
            a[l]+=w*(term.c[1]+term.c[3]*y);b[l]+=w*(term.c[0]+term.c[2]*y);terms+=1;Ok(())})?;
        for (j,round) in candidate.rounds.iter().enumerate(){
            let now=std::time::Instant::now();let p=useq_message(&a,&b,&x);message_ns+=screen_ns(now);
            for (sum,value) in polys[j].iter_mut().zip(p){*sum+=value;}
            let now=std::time::Instant::now();useq_fold(&mut a,round.challenge);useq_fold(&mut b,round.challenge);
            useq_fold(&mut x,round.challenge);fold_ns+=screen_ns(now);
        }
        if k==20{let expected=[a[0],b[0],x[0]];oracle_terminals.push(expected);
            if candidate.terminals[owner]!=expected {jh_part(output,&serde_json::json!({"state":"PARTIAL","stage":"oracle","owner":owner,
                "candidate_terminal":useq_poly(candidate.terminals[owner])?,"oracle_terminal":useq_poly(expected)?}))?;}
            useq_terminal_compare(candidate.terminals[owner],expected)?;terminal_count+=1;}
        report["oracle_terms"]=serde_json::json!(terms);
        if (owner+1)%1024==0{jh_event(report,start,events,"oracle","progress",None,Some(owner+1))?;}
    }
    report["oracle_polynomials"]=serde_json::json!(polys.iter().map(|p|useq_poly(*p)).collect::<Result<Vec<_>,_>>()?);
    report["oracle_metrics"]=serde_json::json!({"visits":terms,"row_loads":bytes.loads+oracle_x_loads,
        "read_bytes":bytes.bytes+source.io_metrics_snapshot().read_bytes-oracle_io_before.read_bytes,
        "cache_capacity_peak_bytes":bytes.capacity_peak,"weights_capacity_bytes":weights.capacity_bytes(),
        "dense_capacity_peak_bytes":dense_capacity,"fold_ns":fold_ns,"message_ns":message_ns,
        "terminals_compared":terminal_count,"underlying_source_visits":null});
    whole_require(terms==U0_TERMS && u0_file_info(&bytes.file)?==identity,"oracle coverage/file identity")?;
    report["timings_ns"]["oracle"]=serde_json::json!(screen_ns(began));
    jh_event(report,start,events,"oracle","end",None,Some(4096))?;
    jh_event(report,start,events,"reference-sender","begin",None,None)?;let began=std::time::Instant::now();let mut claim=Fr::zero();let mut oracle_local=Vec::with_capacity(20);
    for (j,round) in candidate.rounds.iter().enumerate(){
        whole_require(polys[j]==round.polynomial && round.previous_claim==claim,"sequence oracle polynomial/claim mismatch")?;
        let (q,next)=useq_reference_send(polys[j],claim,&mut reference)?;
        whole_require(q==round.challenge && next==round.claim && u0_counters(&reference)==round.counters
            && reference.clone().challenge_scalar(b"native-u-sequence-continuation")==round.continuation,"sequence reference sender mismatch")?;
        oracle_local.push(q);claim=next;report["round_equalities"][j]=serde_json::json!(true);report["oracle_checked_rounds"]=serde_json::json!(j+1);
    }
    report["terminal_checked"]=serde_json::json!(k==20 && terminal_count==4096);
    report["timings_ns"]["reference_sender"]=serde_json::json!(screen_ns(began));
    jh_event(report,start,events,"reference-sender","end",None,None)?;

    // This checkpoint closes only local U arithmetic; extension cannot resume it.
    report["source_candidate_result"]=serde_json::json!("SEQUENCE_PASS");
    report["elapsed_ns"]=serde_json::json!(screen_ns(start));
    let closure=jh_closure(report);
    report["stage"]=serde_json::json!("k20-checkpoint");
    let closure_sha=jh_commit(output,"u20-closure.json",&closure,8192)?;
    summary["k20_closure_sha256"]=serde_json::json!(closure_sha);
    summary["k20_source_complete"]=serde_json::json!(true);
    let initial_counters=u0_counters(&t);
    let candidate_terminal_bytes=candidate.terminals.capacity()*std::mem::size_of::<[Fr;3]>();
    let oracle_terminal_bytes=oracle_terminals.capacity()*std::mem::size_of::<[Fr;3]>();
    whole_require(candidate.terminals.len()==4096 && oracle_terminals.len()==4096,"join terminal extent")?;
    let mut ca=Vec::with_capacity(4096);let mut cb=Vec::with_capacity(4096);let mut cx=Vec::with_capacity(4096);
    let mut oa=Vec::with_capacity(4096);let mut ob=Vec::with_capacity(4096);let mut ox=Vec::with_capacity(4096);
    for triple in &candidate.terminals {ca.push(triple[0]);cb.push(triple[1]);cx.push(triple[2]);}
    for triple in &oracle_terminals {oa.push(triple[0]);ob.push(triple[1]);ox.push(triple[2]);}
    let candidate_high_bytes=(ca.capacity()+cb.capacity()+cx.capacity())*std::mem::size_of::<Fr>();
    let oracle_high_bytes=(oa.capacity()+ob.capacity()+ox.capacity())*std::mem::size_of::<Fr>();
    let mut join=jh_join_value(&closure_sha,initial_counters,[candidate_terminal_bytes,oracle_terminal_bytes,candidate_high_bytes,oracle_high_bytes]);
    jh_event(report,start,events,"high-u","begin",None,None)?;
    let mut rounds=candidate.rounds.iter().map(|x|x.polynomial.to_vec()).collect::<Vec<_>>();
    let mut actual_claim=candidate.rounds.last().ok_or("join U19 state")?.claim;
    let mut replay=t.clone();let began=std::time::Instant::now();
    let phase=crate::gkr::prove_phase(ca,cb,&cx,&mut actual_claim,&mut rounds,&mut t);
    join["timings_ns"][0]=serde_json::json!(screen_ns(began));
    jh_part(output,&serde_json::json!({"state":"PARTIAL","stage":"high-u",
        "candidate_polynomials":rounds.iter().skip(20).map(|p|p.iter().map(u0_hex_fr).collect::<Result<Vec<_>,_>>())
            .collect::<Result<Vec<_>,_>>()?,"candidate_claim":u0_hex_fr(&actual_claim)?}))?;
    let (high,left_value)=phase.map_err(|e|e.to_string())?;
    whole_require(high.len()==12 && rounds.len()==32,"join actual high extent")?;
    join["high_u"]=serde_json::json!(high.iter().map(u0_hex_fr).collect::<Result<Vec<_>,_>>()?);
    join["left_value"]=serde_json::json!(u0_hex_fr(&left_value)?);
    let mut previous=candidate.rounds[19].claim;let mut oracle_previous=claim;
    let mut oracle_high=Vec::with_capacity(12);let began=std::time::Instant::now();
    for j in 0..12 {
        let oracle_poly=useq_message(&oa,&ob,&ox);
        let p:[Fr;3]=rounds[20+j].as_slice().try_into().map_err(|_|"join quadratic extent")?;
        let (replayed_q,next)=useq_reference_send(p,previous,&mut replay)?;
        let (oracle_q,oracle_next)=useq_reference_send(oracle_poly,oracle_previous,&mut reference)?;
        let record=serde_json::json!([j,useq_poly(p)?,useq_poly(oracle_poly)?,u0_hex_fr(&high[j])?,u0_hex_fr(&oracle_q)?,
            u0_hex_fr(&next)?,u0_hex_fr(&oracle_next)?,
            u0_hex_fr(&replay.clone().challenge_scalar(JH_CONTINUATION))?,
            u0_hex_fr(&reference.clone().challenge_scalar(JH_CONTINUATION))?,u0_counters(&replay),u0_counters(&reference)]);
        join["high_rounds"].as_array_mut().ok_or("join high array")?.push(record.clone());
        jh_part(output,&serde_json::json!({"state":"PARTIAL","observations":join}))?;
        whole_require(replayed_q==high[j],"join returned high challenge mismatch")?;
        jh_high_equal(&record)?;
        useq_fold(&mut oa,oracle_q);useq_fold(&mut ob,oracle_q);useq_fold(&mut ox,oracle_q);
        previous=next;oracle_previous=oracle_next;oracle_high.push(oracle_q);
        summary["high_u_rounds"]=serde_json::json!(j+1);
    }
    join["timings_ns"][1]=serde_json::json!(screen_ns(began));
    join["oracle_left_value"]=serde_json::json!(u0_hex_fr(&ox[0])?);
    join["final_counters"]=serde_json::json!(u0_counters(&t));
    jh_part(output,&serde_json::json!({"state":"PARTIAL","observations":join}))?;
    jh_live_equal(actual_claim,previous,oracle_previous,left_value,ox[0],&t,&replay,&reference)?;
    summary["high_u_equal"]=serde_json::json!(true);
    let u=jh_full_u(&candidate.rounds.iter().map(|x|x.challenge).collect::<Vec<_>>(),&high)?;
    let oracle_u=jh_full_u(&oracle_local,&oracle_high)?;
    whole_require(u==oracle_u,"join local/high coordinate orientation")?;
    drop(cx);drop(oa);drop(ob);drop(candidate);drop(oracle_terminals);
    jh_event(report,start,events,"high-u","end",None,None)?;
    jh_event(report,start,events,"sampled-v0","begin",None,None)?;
    let weights=crate::sparse_stream_roster::EdgeFallbackWeightsForTest::new(&r,&u,20);
    let independent_rows=U0OracleWeights::new(&r)?;let independent_u=U0OracleWeights::new(&oracle_u)?;
    join["storage_bytes"][4]=serde_json::json!(weights.capacity_bytes()+independent_rows.capacity_bytes()+independent_u.capacity_bytes());
    let mut candidate_ns=0u64;let mut oracle_ns=0u64;
    for (index,owner) in JH_OWNERS.into_iter().enumerate() {
        let mut d=vec![Fr::zero();1<<20];let mut e=vec![Fr::zero();1<<20];
        let io=source.io_metrics_snapshot();let began=std::time::Instant::now();
        let x=useq_legacy_row(&source,owner)?;let mut canonical_count=0usize;
        whole_oracle_partition(&height,&daa,&numeric,&aliases,false,owner,|term|{
            whole_require(term.right/(1<<20)==owner,"join oracle RIGHT owner")?;
            let w=independent_rows.at(term.row)?*independent_u.at(term.left)?;
            let wire=term.right%(1<<20);
            d[wire]+=w*(term.c[2]+term.c[3]*ox[0]);e[wire]+=w*(term.c[0]+term.c[1]*ox[0]);
            canonical_count=canonical_count.checked_add(1).ok_or("join V count overflow")?;Ok(())})?;
        let oracle_poly=useq_message(&d,&e,&x);let oracle_wall=screen_ns(began);
        oracle_ns=oracle_ns.checked_add(oracle_wall).ok_or("join V oracle time")?;
        let oracle_io=source.io_metrics_snapshot();
        let oracle_metrics=[canonical_count as u64,0,0,0,0,
            oracle_io.read_calls-io.read_calls,oracle_io.read_bytes-io.read_bytes,oracle_wall];
        let scratch=(d.capacity()+e.capacity()+x.capacity())*std::mem::size_of::<Fr>();
        join["storage_bytes"][5]=serde_json::json!(join["storage_bytes"][5].as_u64().ok_or("join V storage")?.max(scratch as u64));
        whole_require(canonical_count==JH_RIGHT_COUNTS[index],"join canonical RIGHT count")?;
        drop(d);drop(e);drop(x);
        let io=source.io_metrics_snapshot();let began=std::time::Instant::now();let mut loaded=Vec::new();
        let result=crate::sparse_stream_roster::edge_fallback_prefix_for_test(false,owner,20,12,19,1,&[19,19],
            canonical_count,&weights,left_value,&[],
            |left,o,sink|adapter.visit_endpoint(&binding,left,o,|term|sink(term)).map(|_|()),
            |requested|{whole_require(requested==owner,"join V loader owner")?;
                loaded.push(requested);crate::packed_rows::read_row(&source,1<<20,requested)},None)?;
        let candidate_wall=screen_ns(began);candidate_ns=candidate_ns.checked_add(candidate_wall).ok_or("join V candidate time")?;
        let candidate_io=source.io_metrics_snapshot();let m=&result.metrics;
        let candidate_metrics=[m.visits,m.vector_clones,m.replay_folds,m.x_fold_fields,m.cache_gets,
            candidate_io.read_calls-io.read_calls,candidate_io.read_bytes-io.read_bytes,candidate_wall];
        let polynomial:[Fr;3]=result.message.as_slice().try_into().map_err(|_|"join V quadratic extent")?;
        let record=serde_json::json!([owner,useq_poly(polynomial)?,useq_poly(oracle_poly)?,candidate_metrics,oracle_metrics,
            polynomial==oracle_poly && m.visits==canonical_count as u64]);
        join["v0"].as_array_mut().ok_or("join V array")?.push(record.clone());
        join["timings_ns"][2]=serde_json::json!(candidate_ns);join["timings_ns"][3]=serde_json::json!(oracle_ns);
        jh_part(output,&serde_json::json!({"state":"PARTIAL","observations":join}))?;
        whole_require(loaded==[owner] && m.vector_clones==1 && m.replay_folds==0 && m.x_fold_fields==0
            && m.cache_gets==1 && candidate_metrics[5]==16 && candidate_metrics[6]==131072
            && oracle_metrics[5]==16 && oracle_metrics[6]==131072,"join V loader/IO ledger")?;
        jh_v_equal(&record)?;
        summary["sampled_v0_owners"].as_array_mut().ok_or("join owners array")?.push(serde_json::json!(owner));
    }
    whole_require(u0_file_info(&bytes.file)?==identity,"join final held witness identity")?;
    summary["sampled_v0_equal"]=serde_json::json!(true);
    jh_event(report,start,events,"sampled-v0","end",None,None)?;
    report["stage"]=serde_json::json!("join-finalization");
    join["state"]=serde_json::json!("JOIN_SOURCE_COMPLETE");
    let hash=jh_commit(output,"join-observations.json",&join,32768)?;
    summary["join_observations_sha256"]=serde_json::json!(hash);Ok(())
}

fn jh_run(){
    use std::io::Write;
    let start=std::time::Instant::now();let mut events=0usize;let mut report=jh_local_report();let mut summary=jh_summary();
    let output=useq_output().expect("join fresh output");
    jh_event(&mut report,start,&mut events,"run","begin",None,None).unwrap();
    let result=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||->Result<(),String>{
        jh_event(&mut report,start,&mut events,"controls","begin",None,None)?;let began=std::time::Instant::now();
        useq_controls(&mut report["controls"])?;jh_controls()?;
        report["timings_ns"]["controls"]=serde_json::json!(screen_ns(began));
        jh_event(&mut report,start,&mut events,"controls","end",None,None)?;
        jh_native(&mut report,&mut summary,start,&mut events,&output,20)
    })).unwrap_or_else(|_|Err("join source panic".into()));
    summary["completed_rounds"]=report["completed_rounds"].clone();
    if let Err(reason)=&result{
        summary["failed_stage"]=report["stage"].clone();
        let mut end=reason.len().min(1024);while !reason.is_char_boundary(end){end-=1;}
        summary["reason"]=serde_json::json!(&reason[..end]);
        jh_event(&mut report,start,&mut events,"hold","hold",None,None).expect("join HOLD marker");
    }else{
        summary["result"]=serde_json::json!("JOIN_SOURCE_PASS");summary["failed_stage"]=serde_json::Value::Null;
    }
    jh_event(&mut report,start,&mut events,"final-report","begin",None,None).unwrap();
    summary["elapsed_ns"]=serde_json::json!(screen_ns(start));
    loop{
        let bytes=serde_json::to_vec(&summary).unwrap();if bytes.len()<=8192{break;}
        let reason=summary["reason"].as_str().unwrap().to_owned();assert!(!reason.is_empty(),"join empty-reason summary cap");
        let cut=reason.char_indices().last().map(|(i,_)|i).unwrap_or(0);summary["reason"]=serde_json::json!(&reason[..cut]);
    }
    useq_save(&output.join("summary.json"),&summary,8192,true).unwrap();
    let line=format!("\nNATIVE_U_HIGH_JOIN_REPORT {}\n",serde_json::to_string(&summary).unwrap());
    assert!(line.len()<=8224);let mut out=std::io::stdout().lock();out.write_all(line.as_bytes()).unwrap();out.flush().unwrap();drop(out);
    jh_event(&mut report,start,&mut events,"final-report","end",None,None).unwrap();
    jh_event(&mut report,start,&mut events,"run","end",None,None).unwrap();
    assert!(result.is_ok(),"native U high join HOLD");
}
#[test]
#[ignore="native U20/high-U/sampled V0; separate10200s/2GiB controller"]
fn native_s12_u_high_join_bounded(){jh_run();}

fn input() -> NativePrefix {
    let path=std::env::var_os("NIPOPOW_NATIVE_AUTH_FIXTURE").expect("pinned RAW fixture required");
    let mut file=OpenOptions::new().read(true).share_mode(1).open(path).unwrap();
    assert_eq!(file.metadata().unwrap().len(),869449);
    let mut bytes=Vec::new();file.take(869450).read_to_end(&mut bytes).unwrap();
    assert_eq!(bytes.len(),869449);
    assert_eq!(layout::hash_bytes(&bytes),"8cdb90da475e646280113d97c9469be7eb86a1d04f20404c64239187284fc009");
    let mut pos=0usize;let mut raws=Vec::with_capacity(3073);
    for _ in 0..3073 {
        let end=pos.checked_add(4).unwrap();assert!(end<=bytes.len());
        let n=u32::from_le_bytes(bytes[pos..end].try_into().unwrap()) as usize;pos=end;
        assert!((1..=514).contains(&n));let end=pos.checked_add(n).unwrap();assert!(end<=bytes.len());
        raws.push(bytes[pos..end].to_vec());pos=end;
    }
    assert_eq!(pos,bytes.len());NativePrefix::from_raw_headers(&raws).unwrap()
}

// Native role0 producer join. Each selector is bounded and independently
// selectable; the proof selector is never part of ordinary test execution.
#[cfg(test)]
mod role0_diagnostic {
    use super::*;
    use crate::{gkr::{self,GkrError,InputClaim}, packed::{PackedFile,PackedReaderFault},
        transcript::Transcript, native_prefix_auth_plan::NativeRole0DiagnosticContext};
    use std::{fs::File,io::{Read,Seek,SeekFrom,Write},path::{Path,PathBuf},time::Instant};
    use std::os::windows::fs::OpenOptionsExt;

    const OWNER_BYTES:usize=131072;

    struct PinnedArtifact { bytes:Vec<u8>, file:File, identity:U0FileInfo }

    fn pinned_artifact(env:&str,expected_len:usize,expected_sha:&str)->Result<PinnedArtifact,String>{
        let path=PathBuf::from(std::env::var_os(env).ok_or_else(||format!("{env} absent"))?);
        whole_require(path.is_absolute(),"role0 artifact path must be absolute")?;
        let file=OpenOptions::new().read(true).share_mode(1).open(&path).map_err(|e|e.to_string())?;
        let identity=u0_file_info(&file)?;
        whole_require(file.metadata().map_err(|e|e.to_string())?.len()==expected_len as u64,
            "role0 artifact exact extent")?;
        let mut bytes=Vec::with_capacity(expected_len);
        file.try_clone().map_err(|e|e.to_string())?.take(expected_len as u64+1)
            .read_to_end(&mut bytes).map_err(|e|e.to_string())?;
        whole_require(bytes.len()==expected_len && screen_hex(&crate::native_prefix_auth_plan::role0_sha256(&bytes)?)==expected_sha,
            "role0 artifact accepted SHA-256")?;
        Ok(PinnedArtifact{bytes,file,identity})
    }

    fn accepted_artifacts()->Result<(PinnedArtifact,PinnedArtifact,NativeRole0DiagnosticContext),String>{
        let key=pinned_artifact("NIPOPOW_ROLE4_KEY_PATH",33264,"D11220A1CBB08BE2C84F6B854EC2A932B3FCEC49C217963D079DD8053F7B31B2")?;
        let commitment=pinned_artifact("NIPOPOW_NATIVE_ROLE0_COMMITMENT_PATH",384,"2739A3353D579A7FA0F19B06EFDD26A625CDB80009C65707D8B96E7D8C0C9C90")?;
        let context=NativeRole0DiagnosticContext::admit(&key.bytes,&commitment.bytes)?;
        Ok((key,commitment,context))
    }

    fn with_plan<R>(run:impl FnOnce(&WorkTreeHistoryPlan,&NativePrefixAuthPlan<'_>,&Candidate)->R)->R{
        let native=input();let root=native.root();let total=native.total_be28();
        let candidate=Candidate{n:3073,root,total,
            tip:ergo_header_core::blake2b256(native.raw(3073).unwrap()),
            tip_time:native.timestamp(3073).unwrap()};
        let parent=WorkTreeHistoryPlan::compile(3073,12,root,total).unwrap();drop(native);
        let plan=NativePrefixAuthPlan::compile(&parent,Selection::s12(),candidate.clone()).unwrap();
        run(&parent,&plan,&candidate)
    }

    #[test]
    fn native_role0_shape_admission_is_exact(){
        for h in [11usize,13] {
            let plan=crate::core_pool::Plan::new(h).unwrap();
            assert!(plan.require_native_role0_shape().is_err());
        }
        let plan=crate::core_pool::Plan::new(12).unwrap();
        plan.require_native_role0_shape().unwrap();
        assert_eq!((plan.input_log(),plan.row_log(),plan.input_len(),plan.row_count()),
            (32,33,1usize<<32,1usize<<33));
    }

    #[test]
    #[ignore="bounded pinned-log32 source owner-window checks; no GKR proof"]
    fn native_role0_owner_windows_bounded(){
        let path=PathBuf::from(std::env::var_os("NIPOPOW_NATIVE_U_SEQUENCE_WITNESS").unwrap());
        let (source,mut held,identity)=useq_admit().unwrap();let view=source.native_role0_view().unwrap();
        view.require_same_source(&source).unwrap();
        let detached=PackedFile::open_with_limit(&path,32,32).unwrap();
        assert!(view.require_same_source(&detached).is_err(),"same-path detached handle rejected");
        assert!(PackedFile::open(&path,32).is_err(),"public opener remains capped at24");
        assert!(PackedFile::open_with_limit(&path,31,32).is_err(),"wrong log/extent rejected");
        assert_eq!(PackedFile::open_with_limit(&path,32,32).unwrap().input_len(),1usize<<32,
            "existing private diagnostic admission accepts exact log32");
        for owner in [0usize,3,4,4095] {
            let offset=(owner*OWNER_BYTES) as u64;held.seek(SeekFrom::Start(offset)).unwrap();
            let mut expected=vec![0u8;OWNER_BYTES];held.read_exact(&mut expected).unwrap();
            let actual=view.read_copy(owner).unwrap();
            assert_eq!(actual.len(),1usize<<20);assert!(actual.matches_bytes(&expected));
            for bit in [0usize,1,7,8,65535,65536,(1usize<<20)-1] {
                let expected_bit=expected[bit/8]>>(bit%8)&1!=0;
                assert_eq!(actual.bit_at(bit),expected_bit,"owner {owner} packed bit {bit}");
                assert_eq!(actual.bit(bit/65536,bit%65536).unwrap(),expected_bit,
                    "owner {owner} bank/local bit {bit}");
            }
            if owner==3 {
                assert!(!actual.matches_bytes(&held_slice(&mut held,((owner+1)*OWNER_BYTES) as u64)),
                    "one-owner shifted read rejected");
            }
        }
        assert!(view.read_copy(4096).is_err());assert!(view.read_copy(usize::MAX).is_err());
        assert!(view.reader_fault_for_test(4095,PackedReaderFault::Short).is_err());
        assert!(view.reader_fault_for_test(4095,PackedReaderFault::ShortByOneByte).is_err());
        assert!(view.reader_fault_for_test(4095,PackedReaderFault::Io).is_err());
        assert_eq!(u0_file_info(&held).unwrap(),identity);
    }

    fn held_slice(file:&mut File,offset:u64)->Vec<u8>{
        file.seek(SeekFrom::Start(offset)).unwrap();let mut bytes=vec![0u8;OWNER_BYTES];
        file.read_exact(&mut bytes).unwrap();bytes
    }

    #[derive(Clone,Copy,Debug)]
    enum BindingVariant {
        Exact, OmitAdmission, OmitPlanIdentity, OmitRoleFields, Reordered,
        WrongRole, WrongInputLog, WrongOutputLog,
    }

    fn bind_variant(plan:&NativePrefixAuthPlan<'_>,context:&NativeRole0DiagnosticContext,
        transcript:&mut Transcript,variant:BindingVariant)->Result<(),String>{
        match variant {
            BindingVariant::Exact=>plan.bind_role0_diagnostic_context(transcript,context),
            BindingVariant::OmitAdmission=>{
                plan.bind_role0_descriptor_fields_for_test(transcript,context,0,32,33)?;
                plan.bind_plan_identity(transcript)
            }
            BindingVariant::OmitPlanIdentity=>{
                context.bind_admission(transcript)?;
                plan.bind_role0_descriptor_fields_for_test(transcript,context,0,32,33)
            }
            BindingVariant::OmitRoleFields=>{
                context.bind_admission(transcript)?;plan.bind_plan_identity(transcript)
            }
            BindingVariant::Reordered=>{
                plan.bind_plan_identity(transcript)?;
                context.bind_admission(transcript)?;
                plan.bind_role0_descriptor_fields_for_test(transcript,context,0,32,33)
            }
            BindingVariant::WrongRole=>plan.bind_role0_diagnostic_context_with_fields(transcript,context,1,32,33),
            BindingVariant::WrongInputLog=>plan.bind_role0_diagnostic_context_with_fields(transcript,context,0,31,33),
            BindingVariant::WrongOutputLog=>plan.bind_role0_diagnostic_context_with_fields(transcript,context,0,32,32),
        }
    }

    fn verify_claim(plan:&NativePrefixAuthPlan<'_>,context:&NativeRole0DiagnosticContext,
        proof:&gkr::GkrProof,variant:BindingVariant)->Result<(InputClaim,Transcript),GkrError>{
        let mut preflight=context.transcript();
        bind_variant(plan,context,&mut preflight,variant).map_err(|_|GkrError::PointDimension)?;
        let mut verifier=context.transcript();
        let claim=gkr::verify_with_wiring(&[32],1usize<<33,proof,&mut verifier,
            |t|bind_variant(plan,context,t,variant).expect("prevalidated role0 transcript binder"),
            |layer,r,u,v|if layer==0 {plan.coefficients(0,r,u,v).map_err(|_|GkrError::PointDimension)}
                else {Err(GkrError::PointDimension)})?;
        Ok((claim,verifier))
    }

    #[test]
    #[ignore="bounded pinned-RAW binding controls; no source stream or GKR proof"]
    fn native_role0_context_binding_controls(){
        let (key,commitment,context)=accepted_artifacts().unwrap();
        let (source,_held,_identity)=useq_admit().unwrap();source.reset_io_metrics();
        with_plan(|parent,plan,candidate|{
            let descriptors=plan.descriptors().to_vec();
            assert_eq!(descriptors.len(),7);plan.validate_roster(&descriptors).unwrap();
            let mut reordered=descriptors.clone();reordered.swap(0,1);
            assert!(plan.validate_roster(&reordered).is_err());
            assert!(plan.validate_roster(&descriptors[..6]).is_err());
            assert_eq!((plan.descriptors()[0].input_log,plan.descriptors()[0].row_log),(32,33));
            let mut base=context.transcript();
            plan.bind_role0_diagnostic_context(&mut base,&context).unwrap();
            let expected=base.clone().challenge_scalar(b"role0-binding-control");
            let mut changed_candidate=candidate.clone();changed_candidate.tip[0]^=1;
            let changed_plan=NativePrefixAuthPlan::compile(parent,Selection::s12(),changed_candidate).unwrap();
            let mut changed_plan_transcript=context.transcript();
            changed_plan.bind_role0_diagnostic_context(&mut changed_plan_transcript,&context).unwrap();
            assert_ne!(expected,changed_plan_transcript.challenge_scalar(b"role0-binding-control"),
                "one candidate tip field is bound into plan identity");
            let mut changed_key=key.bytes.clone();changed_key[0]^=1;
            assert!(NativeRole0DiagnosticContext::admit(&changed_key,&commitment.bytes).is_err());
            let changed_commitment=crate::pcs::encode_commitment(
                &dory_pcs::backends::arkworks::ArkGT(
                    ark_ec::pairing::PairingOutput::<ark_bn254::Bn254>::zero())).unwrap();
            assert_ne!(changed_commitment,commitment.bytes,"mutant remains canonical encoded GT identity");
            assert_eq!(crate::pcs::encode_commitment(&crate::pcs::decode_commitment(&changed_commitment).unwrap()).unwrap(),changed_commitment);
            assert!(NativeRole0DiagnosticContext::admit(&key.bytes,&changed_commitment).is_err());
            assert!(NativeRole0DiagnosticContext::admit_with_setup_id(&key.bytes,&commitment.bytes,[0;32]).is_err());
            assert!(NativeRole0DiagnosticContext::admit(&key.bytes,&commitment.bytes[..383]).is_err());
            let mut after=context.transcript();after.challenge_scalar(b"before-binding");
            assert!(plan.bind_role0_diagnostic_context(&mut after,&context).is_err());
            let mut prechallenged=context.transcript();prechallenged.challenge_scalar(b"before-prove");
            assert!(plan.prove_role0_packed_for_test(&source,&mut prechallenged,&context).is_err());
            assert_eq!(source.io_metrics_snapshot().read_calls,0,
                "challenged transcript rejected before reading packed owners");
            for variant in [BindingVariant::OmitAdmission,BindingVariant::OmitPlanIdentity,
                BindingVariant::OmitRoleFields,BindingVariant::Reordered,
                BindingVariant::WrongRole,BindingVariant::WrongInputLog,BindingVariant::WrongOutputLog] {
                let mut mutant=context.transcript();bind_variant(plan,&context,&mut mutant,variant).unwrap();
                assert_ne!(expected,mutant.challenge_scalar(b"role0-binding-control"));
            }
            let mut identity_only=plan.bound_transcript().unwrap();
            assert_ne!(expected,identity_only.challenge_scalar(b"role0-binding-control"),
                "identity-only source-plan framing is not the diagnostic proof domain");
        });
        assert_eq!(source.io_metrics_snapshot().read_calls,0,
            "artifact-admission and transcript negatives precede owner reads");
        assert_eq!(u0_file_info(&key.file).unwrap(),key.identity);
        assert_eq!(u0_file_info(&commitment.file).unwrap(),commitment.identity);
    }

    #[test]
    #[ignore="one bounded native S12 role0 diagnostic GKR proof; reviewed controller required"]
    fn native_role0_gkr_claim_bounded(){
        let (source,held,witness_identity)=useq_admit().unwrap();
        let (key,commitment,context)=accepted_artifacts().unwrap();
        let output=capture_path().unwrap();
        let total_started=Instant::now();
        let (encoded,proof_elapsed,verify_elapsed)=with_plan(|parent,plan,candidate|{
            assert_eq!(plan.descriptors()[0].name,"corepool11");
            assert_eq!((plan.descriptors()[0].input_log,plan.descriptors()[0].row_log),(32,33));
            let mut producer=context.transcript();let proof_started=Instant::now();
            let (proof,producer_claim)=plan.prove_role0_packed_for_test(
                &source,&mut producer,&context).unwrap();
            let proof_elapsed=proof_started.elapsed().as_millis() as u64;
            let encoded=gkr::encode_proof(&proof).unwrap();
            let decoded=gkr::decode_dimensions(&[32],&encoded).unwrap();
            assert_eq!(gkr::encode_proof(&decoded).unwrap(),encoded);
            let verify_started=Instant::now();
            let (verifier_claim,mut verifier)=verify_claim(plan,&context,&decoded,BindingVariant::Exact).unwrap();
            let verify_elapsed=verify_started.elapsed().as_millis() as u64;
            assert_eq!(verifier_claim,producer_claim);
            assert_eq!(source.evaluate(&verifier_claim.point).unwrap(),verifier_claim.value,
                "diagnostic source-evaluation cross-check only");
            let mut changed_candidate=candidate.clone();changed_candidate.tip[0]^=1;
            let changed_plan=NativePrefixAuthPlan::compile(parent,Selection::s12(),changed_candidate).unwrap();
            assert!(verify_claim(&changed_plan,&context,&decoded,BindingVariant::Exact).is_err(),
                "proof is rejected when one bound candidate tip field changes");
            let mut changed_round=decoded.clone();changed_round.layers[0].rounds[0][0]+=Fr::one();
            assert!(verify_claim(plan,&context,&changed_round,BindingVariant::Exact).is_err(),
                "one-round GKR mutation rejected by independent verifier");
            for variant in [BindingVariant::OmitAdmission,BindingVariant::OmitPlanIdentity,
                BindingVariant::OmitRoleFields,BindingVariant::Reordered,BindingVariant::WrongRole,
                BindingVariant::WrongInputLog,BindingVariant::WrongOutputLog] {
                assert!(verify_claim(plan,&context,&decoded,variant).is_err(),
                    "single transcript binding mutation rejected: {variant:?}");
            }
            assert_eq!(producer.challenge_scalar(b"role0-continuation"),
                verifier.challenge_scalar(b"role0-continuation"));
            assert_eq!(producer_claim.point.len(),32);assert_eq!(proof.layers.len(),1);
            assert_eq!(proof.layers[0].rounds.len(),64);
            assert_eq!(proof.layers[0].line_coefficients.len(),33);
            (encoded,proof_elapsed,verify_elapsed)
        });
        assert_eq!(u0_file_info(&held).unwrap(),witness_identity);
        assert_eq!(u0_file_info(&key.file).unwrap(),key.identity);
        assert_eq!(u0_file_info(&commitment.file).unwrap(),commitment.identity);
        let proof_sha=crate::native_prefix_auth_plan::role0_sha256(&encoded).unwrap();
        let report=serde_json::json!({
            "schema":"native-prefix-role0-diagnostic-gkr-v1","state":"ROLE0_DIAGNOSTIC_GKR_PASS",
            "scope":{"native_n":3073,"role":0,"input_log":32,"output_row_log":33,"output_width":8589934592u64,
                "common_opening":false,"all_seven_claims":false,"full_history":false,"light_client":false,
                "no_fork":false,"eip":false,"oracle":false,"production":false},
            "admission":{"setup_id":screen_hex(&context.setup_id_for_report()),
                "verifier_key_sha256":screen_hex(&context.key_sha256_for_report()),
                "commitment_sha256":screen_hex(&context.commitment_sha256_for_report()),
                "key_bytes":33264,"commitment_bytes":384,"commitment_canonical":true,
                "generated_test_key_admission":true},
            "proof":{"file":"gkr-proof.bin","bytes":encoded.len(),"sha256":screen_hex(&proof_sha),
                "canonical_codec_roundtrip":true,"independent_verify":true,"source_evaluation_crosscheck":true,
                "mutated_round_rejected":true},
            "timing_ms":{"proof":proof_elapsed,"independent_verify":verify_elapsed,
                "whole_test":total_started.elapsed().as_millis() as u64}
        });
        write_capture(&output,&encoded,&report).unwrap();
    }

    fn capture_path()->Result<PathBuf,String>{
        let path=PathBuf::from(std::env::var_os("NIPOPOW_NATIVE_ROLE0_CAPTURE_DIR")
            .ok_or("NIPOPOW_NATIVE_ROLE0_CAPTURE_DIR absent")?);
        if !path.is_absolute() || path.parent().map_or(true,|parent|!parent.is_dir()) {
            return Err("native role0 capture directory must be a fresh absolute child of an existing directory".into());
        }
        match std::fs::symlink_metadata(&path) {
            Ok(_) => return Err("native role0 capture directory already exists".into()),
            Err(error) if error.kind()==std::io::ErrorKind::NotFound => (),
            Err(error) => return Err(format!("native role0 capture path check: {error}")),
        }
        Ok(path)
    }

    fn write_capture(dir:&Path,proof:&[u8],report:&serde_json::Value)->Result<(),String>{
        std::fs::create_dir(dir).map_err(|e|e.to_string())?;
        let mut proof_file=OpenOptions::new().write(true).create_new(true).open(dir.join("gkr-proof.bin"))
            .map_err(|e|e.to_string())?;
        proof_file.write_all(proof).map_err(|e|e.to_string())?;
        proof_file.sync_all().map_err(|e|e.to_string())?;drop(proof_file);
        let report_bytes=serde_json::to_vec_pretty(report).map_err(|e|e.to_string())?;
        let mut report_file=OpenOptions::new().write(true).create_new(true).open(dir.join("role0-result.json"))
            .map_err(|e|e.to_string())?;
        report_file.write_all(&report_bytes).map_err(|e|e.to_string())?;
        report_file.sync_all().map_err(|e|e.to_string())?;drop(report_file);Ok(())
    }

    fn accepted_role1_artifacts()->Result<(PinnedArtifact,PinnedArtifact,NativeRole1DiagnosticContext),String>{
        let key=pinned_artifact("NIPOPOW_ROLE4_KEY_PATH",33264,"D11220A1CBB08BE2C84F6B854EC2A932B3FCEC49C217963D079DD8053F7B31B2")?;
        let commitment=pinned_artifact("NIPOPOW_NATIVE_ROLE0_COMMITMENT_PATH",384,"2739A3353D579A7FA0F19B06EFDD26A625CDB80009C65707D8B96E7D8C0C9C90")?;
        let context=NativeRole1DiagnosticContext::admit(&key.bytes,&commitment.bytes)?;
        Ok((key,commitment,context))
    }

    fn role1_bind_variant(plan:&NativePrefixAuthPlan<'_>,context:&NativeRole1DiagnosticContext,
        t:&mut Transcript,variant:BindingVariant)->Result<(),String>{
        match variant{
            BindingVariant::Exact=>plan.bind_role1_diagnostic_context(t,context),
            BindingVariant::OmitAdmission=>{
                plan.bind_role1_descriptor_fields_for_test(t,context,1,32,31)?;plan.bind_plan_identity(t)
            },
            BindingVariant::OmitPlanIdentity=>{
                context.bind_admission(t)?;plan.bind_role1_descriptor_fields_for_test(t,context,1,32,31)
            },
            BindingVariant::OmitRoleFields=>{context.bind_admission(t)?;plan.bind_plan_identity(t)},
            BindingVariant::Reordered=>{
                plan.bind_plan_identity(t)?;context.bind_admission(t)?;
                plan.bind_role1_descriptor_fields_for_test(t,context,1,32,31)
            },
            BindingVariant::WrongRole=>plan.bind_role1_descriptor_fields_for_test(t,context,0,32,31),
            BindingVariant::WrongInputLog=>plan.bind_role1_descriptor_fields_for_test(t,context,1,31,31),
            BindingVariant::WrongOutputLog=>plan.bind_role1_descriptor_fields_for_test(t,context,1,32,32),
        }
    }

    fn role1_verify_claim(plan:&NativePrefixAuthPlan<'_>,context:&NativeRole1DiagnosticContext,
        proof:&gkr::GkrProof,variant:BindingVariant,wrong_domain:bool)->Result<(InputClaim,Transcript),GkrError>{
        let mut verifier=if wrong_domain{Transcript::new(b"native-prefix-role0-diagnostic-proof-v1")}else{context.transcript()};
        // Validate the same immutable framing before the unit-returning verifier
        // callback. No failed binding Result is discarded or converted to success.
        let mut preflight=verifier.clone();
        role1_bind_variant(plan,context,&mut preflight,variant).map_err(|_|GkrError::PointDimension)?;
        let claim=gkr::verify_with_wiring(&[32],1usize<<31,proof,&mut verifier,
            |t|role1_bind_variant(plan,context,t,variant).expect("immutable role1 verifier binding prevalidated"),
            |layer,r,u,v|if layer==0{plan.coefficients(1,r,u,v).map_err(|_|GkrError::PointDimension)}
                else{Err(GkrError::PointDimension)})?;
        Ok((claim,verifier))
    }

    #[test]
    fn native_role1_native32_context_policy_controls(){
        let (source,held,identity)=useq_admit().unwrap();
        let (key,commitment,context)=accepted_role1_artifacts().unwrap();
        with_plan(|parent,plan,candidate|{
            let mut exact=context.transcript();plan.bind_role1_diagnostic_context(&mut exact,&context).unwrap();
            assert_eq!(exact.challenges(),0);
            let mut after_challenge=context.transcript();after_challenge.challenge_scalar(b"prebind-fault");
            source.reset_io_metrics();
            assert!(plan.prove_role1_packed_for_test(&source,&mut after_challenge,&context).is_err());
            assert_eq!(source.io_metrics_snapshot().read_calls,0,"prechallenged proof rejects before source reads");
            for variant in [BindingVariant::WrongRole,BindingVariant::WrongInputLog,BindingVariant::WrongOutputLog]{
                let mut t=context.transcript();let before=t.bytes_absorbed();
                assert!(role1_bind_variant(plan,&context,&mut t,variant).is_err());
                assert_eq!(t.challenges(),0);assert_eq!(t.bytes_absorbed(),before);
            }
            let mut expected=exact.clone();let challenge=expected.challenge_scalar(b"role1-context-probe");
            for variant in [BindingVariant::OmitAdmission,BindingVariant::OmitPlanIdentity,
                BindingVariant::OmitRoleFields,BindingVariant::Reordered]{
                let mut t=context.transcript();role1_bind_variant(plan,&context,&mut t,variant).unwrap();
                assert_ne!(t.challenge_scalar(b"role1-context-probe"),challenge,"isolated framing mutation {variant:?}");
            }
            let mut wrong_domain=Transcript::new(b"native-prefix-role0-diagnostic-proof-v1");
            plan.bind_role1_diagnostic_context(&mut wrong_domain,&context).unwrap();
            assert_ne!(wrong_domain.challenge_scalar(b"role1-context-probe"),challenge);
            let mut changed=candidate.clone();changed.tip[0]^=1;
            let foreign=NativePrefixAuthPlan::compile(parent,Selection::s12(),changed).unwrap();
            let mut t=context.transcript();foreign.bind_role1_diagnostic_context(&mut t,&context).unwrap();
            assert_ne!(t.challenge_scalar(b"role1-context-probe"),challenge);
            let mut bad=candidate.clone();bad.root[0]^=1;
            assert!(NativePrefixAuthPlan::compile(parent,Selection::s12(),bad).is_err());
            let mut bad=candidate.clone();bad.total[0]^=1;
            assert!(NativePrefixAuthPlan::compile(parent,Selection::s12(),bad).is_err());
            let mut key_mutant=key.bytes.clone();key_mutant[0]^=1;
            assert!(NativeRole1DiagnosticContext::admit(&key_mutant,&commitment.bytes).is_err());
            assert!(NativeRole1DiagnosticContext::admit(&key.bytes[..33263],&commitment.bytes).is_err());
            assert!(NativeRole1DiagnosticContext::admit(&key.bytes,&commitment.bytes[..383]).is_err());
            assert!(NativeRole1DiagnosticContext::admit_with_setup_id(&key.bytes,&commitment.bytes,[0;32]).is_err());
            let changed_commitment=crate::pcs::encode_commitment(&dory_pcs::backends::arkworks::ArkGT(
                ark_ec::pairing::PairingOutput::<ark_bn254::Bn254>::zero())).unwrap();
            assert_ne!(changed_commitment,commitment.bytes);
            assert_eq!(crate::pcs::encode_commitment(&crate::pcs::decode_commitment(&changed_commitment).unwrap()).unwrap(),changed_commitment);
            assert!(NativeRole1DiagnosticContext::admit(&key.bytes,&changed_commitment).is_err());
            let r=vec![Fr::from(3u64);30];let u=vec![Fr::from(5u64);32];
            assert!(plan.coefficients(1,&r,&u,&u).is_err());
            let r=vec![Fr::from(3u64);31];assert!(plan.coefficients(1,&r,&u[..31],&u).is_err());
            assert!(plan.coefficients(1,&r,&u,&u[..31]).is_err());
        });
        assert_eq!(u0_file_info(&held).unwrap(),identity);
        assert_eq!(u0_file_info(&key.file).unwrap(),key.identity);
        assert_eq!(u0_file_info(&commitment.file).unwrap(),commitment.identity);
    }

    fn role1_native32_output()->Result<PathBuf,String>{
        let path=PathBuf::from(std::env::var_os("NIPOPOW_NATIVE_ROLE1_FULL_CAPTURE_DIR")
            .ok_or("NIPOPOW_NATIVE_ROLE1_FULL_CAPTURE_DIR absent")?);
        if !path.is_absolute()||path.parent().is_none_or(|p|!p.is_dir()){
            return Err("native role1 capture must be a fresh absolute child".into());
        }
        match std::fs::symlink_metadata(&path){
            Ok(_)=>Err("native role1 capture already exists".into()),
            Err(e) if e.kind()==std::io::ErrorKind::NotFound=>Ok(path),Err(e)=>Err(e.to_string()),
        }
    }
    fn role1_native32_marker(label:&str,value:serde_json::Value)->Result<(),String>{
        let line=format!("\n{label} {value}\n");
        if line.len()>1024{return Err("native role1 marker cap".into());}
        let mut out=std::io::stdout().lock();out.write_all(line.as_bytes()).map_err(|e|e.to_string())?;
        out.flush().map_err(|e|e.to_string())
    }
    fn role1_native32_export(dir:&Path,proof:&[u8],report:&serde_json::Value)->Result<(),String>{
        let bytes=serde_json::to_vec_pretty(report).map_err(|e|e.to_string())?;
        if proof.len()!=7264||bytes.len()>65536{return Err("native role1 proof/report extent".into());}
        std::fs::create_dir(dir).map_err(|e|e.to_string())?;
        for (name,data) in [("role1-native32.gkr",proof),("role1-native32-result.json",bytes.as_slice())]{
            let mut file=OpenOptions::new().write(true).create_new(true).open(dir.join(name)).map_err(|e|e.to_string())?;
            file.write_all(data).map_err(|e|e.to_string())?;file.sync_all().map_err(|e|e.to_string())?;drop(file);
        }
        Ok(())
    }

    #[test]
    #[ignore="native role1 full4096 producer; separate reviewed runtime budget required"]
    fn native_role1_native32_gkr_claim_bounded(){
        use crate::sparse_stream_roster as stream;
        use ark_serialize::CanonicalSerialize;
        let whole_started=Instant::now();let output=role1_native32_output().unwrap();
        let (source,held,identity)=useq_admit().unwrap();
        let (key,commitment,context)=accepted_role1_artifacts().unwrap();
        let (encoded,report)=with_plan(|parent,plan,candidate|->Result<(Vec<u8>,serde_json::Value),String>{
            let mut producer=context.transcript();source.reset_io_metrics();
            role1_native32_marker("NIPOPOW_ROLE1_NATIVE32_BEGIN",serde_json::json!({"role":1,"input_log":32,"output_row_log":31}))?;
            stream::begin_phase_trace_for_test();let began=Instant::now();
            let (proof,producer_claim,gv,bu)=plan.prove_role1_packed_for_test(&source,&mut producer,&context)?;
            let proof_ms=began.elapsed().as_millis() as u64;let marks=stream::take_phase_trace_for_test();
            let io=source.io_metrics_snapshot();
            let phases=["baseline_start","baseline_done","u_cache_streamed","u_anchor_done","u_local_done","u_handoff_done",
                "v_cache_grouped","v_anchor_done","v_local_done","v_handoff_done","terminal_wiring_done","line_start","line_done"];
            if marks.len()!=13||marks.iter().map(|m|m.name.as_str()).ne(phases)
                ||marks.windows(2).any(|m|m[0].elapsed_ns>m[1].elapsed_ns){return Err("native role1 ordered phase marks".into());}
            if gv.group_count!=2||gv.group_owner_counts.as_slice()!=&[4095,1]||gv.group_term_counts.as_slice()!=&[396_561,388_369]
                ||gv.baseline_term_callbacks!=1_624_305_664||gv.template_term_count!=784_930||gv.bank_term_callbacks!=784_930
                ||gv.handoff_term_callbacks!=0||gv.local_rounds!=20||gv.owner_handoff_count!=4096{
                return Err("native role1 complete grouped census".into());
            }
            if bu.prefix_builds!=21||bu.shared_term_iterations!=16_483_530||bu.owner_term_selections!=34_110_418_944
                ||bu.boolean_checked_loads!=102_400||bu.boolean_checked_fields!=107_374_182_400
                ||!bu.zero_anchor_sweep_skipped||bu.preweight_entry_size_bytes!=144
                ||bu.u_state_peak_capacity_bytes!=*bu.u_phase_peak_capacity_bytes.iter().max().ok_or("native role1 U phases")?
                ||bu.u_state_peak_capacity_bytes>bu.u_preflight_capacity_bound_bytes
                ||bu.u_preflight_capacity_bound_bytes>512*1024*1024||gv.grouped_state_peak_capacity_bytes>512*1024*1024
                ||io.read_bytes!=13_421_772_800||io.read_calls!=1_638_400{
                return Err("native role1 Boolean recurrence/capacity/source I/O".into());
            }
            let interval=marks[5].elapsed_ns.checked_sub(marks[3].elapsed_ns).ok_or("native role1 U interval")?;
            let parts=[bu.u_prefix_preweight_elapsed_ns,bu.u_owner_selection_elapsed_ns,bu.u_x_fold_elapsed_ns];
            let total=parts.iter().try_fold(0u64,|sum,x|sum.checked_add(*x)).ok_or("native role1 U timing overflow")?;
            if parts.iter().any(|x|u128::from(*x)>interval)||u128::from(total)>interval{return Err("native role1 disjoint U timings".into());}
            let codec_started=Instant::now();let encoded=gkr::encode_proof(&proof)?;
            let decoded=gkr::decode_dimensions(&[32],&encoded)?;
            let codec_bytes=227usize.checked_mul(Fr::zero().compressed_size()).ok_or("native role1 scalar extent overflow")?;
            if codec_bytes!=7264||encoded.len()!=codec_bytes||gkr::encode_proof(&decoded)?!=encoded||decoded.layers.len()!=1
                ||decoded.layers[0].rounds.len()!=64||decoded.layers[0].line_coefficients.len()!=33{
                return Err("native role1 canonical proof shape".into());
            }
            let codec_ms=codec_started.elapsed().as_millis() as u64;
            let verify_started=Instant::now();let (claim,mut verifier)=role1_verify_claim(plan,&context,&decoded,BindingVariant::Exact,false)
                .map_err(|e|e.to_string())?;let verify_ms=verify_started.elapsed().as_millis() as u64;
            if claim!=producer_claim||claim.point.len()!=32{return Err("native role1 independent claim".into());}
            if verifier.challenges()!=producer.challenges()||verifier.raw_queries()!=producer.raw_queries()
                ||verifier.bytes_absorbed()!=producer.bytes_absorbed(){return Err("native role1 transcript counters".into());}
            let mle_started=Instant::now();if source.evaluate(&claim.point)?!=claim.value{return Err("native role1 source MLE32".into());}
            let mle_ms=mle_started.elapsed().as_millis() as u64;
            for variant in [BindingVariant::OmitAdmission,BindingVariant::OmitPlanIdentity,BindingVariant::OmitRoleFields,
                BindingVariant::Reordered,BindingVariant::WrongRole,BindingVariant::WrongInputLog,BindingVariant::WrongOutputLog]{
                if role1_verify_claim(plan,&context,&decoded,variant,false).is_ok(){return Err(format!("native role1 binding mutant {variant:?}"));}
            }
            if role1_verify_claim(plan,&context,&decoded,BindingVariant::Exact,true).is_ok(){return Err("native role1 wrong domain accepted".into());}
            let mut changed=candidate.clone();changed.tip[0]^=1;
            let changed_plan=NativePrefixAuthPlan::compile(parent,Selection::s12(),changed)?;
            if role1_verify_claim(&changed_plan,&context,&decoded,BindingVariant::Exact,false).is_ok(){return Err("native role1 changed tip accepted".into());}
            let mut mutant=decoded.clone();mutant.layers[0].rounds[0][0]+=Fr::one();
            if role1_verify_claim(plan,&context,&mutant,BindingVariant::Exact,false).is_ok(){return Err("native role1 changed round accepted".into());}
            if producer.challenge_scalar(b"native-role1-diagnostic-continuation")!=verifier.challenge_scalar(b"native-role1-diagnostic-continuation"){
                return Err("native role1 continuation".into());
            }
            let scope=serde_json::json!({"native_n":3073,"role":1,"input_log":32,"output_row_log":31,"output_width":2147483648u64,
                "common_opening":false,"all_seven_claims":false,"full_history":false,"light_client":false,
                "no_fork":false,"eip":false,"oracle":false,"production":false});
            let admission=serde_json::json!({"setup_id":screen_hex(&context.setup_id_for_report()),
                "verifier_key_sha256":screen_hex(&context.key_sha256_for_report()),"commitment_sha256":screen_hex(&context.commitment_sha256_for_report()),
                "key_bytes":33264,"commitment_bytes":384,"commitment_canonical":true,"generated_test_key_admission":true,
                "scoped_limit_bytes":536870912,"state_peak_capacity_bytes":bu.u_state_peak_capacity_bytes.max(gv.grouped_state_peak_capacity_bytes),
                "token_struct_bytes":std::mem::size_of::<NativeRole1Admission<'_, '_>>()});
            let native_counts=serde_json::json!({"owners":4096,"full_owners":4095,"short_owners":1,"short_owner":3072,
                "baseline_term_callbacks":gv.baseline_term_callbacks,"producer_owner_loads":bu.boolean_checked_loads,
                "packed_read_bytes":io.read_bytes,"packed_read_calls":io.read_calls,"packed_read_ns":io.read_ns});
            let boolean_u=serde_json::json!({"prefix_builds":bu.prefix_builds,"shared_term_iterations":bu.shared_term_iterations,
                "owner_term_selections":bu.owner_term_selections,"boolean_checked_loads":bu.boolean_checked_loads,
                "boolean_checked_fields":bu.boolean_checked_fields,"zero_anchor_sweep_skipped":bu.zero_anchor_sweep_skipped,
                "preweight_entry_size_bytes":bu.preweight_entry_size_bytes,"preweight_peak_capacity_bytes":bu.preweight_peak_capacity_bytes,
                "u_state_peak_capacity_bytes":bu.u_state_peak_capacity_bytes,"u_preflight_capacity_bound_bytes":bu.u_preflight_capacity_bound_bytes,
                "u_phase_peak_capacity_bytes":bu.u_phase_peak_capacity_bytes,"u_prefix_preweight_elapsed_ns":bu.u_prefix_preweight_elapsed_ns,
                "u_owner_selection_elapsed_ns":bu.u_owner_selection_elapsed_ns,"u_x_fold_elapsed_ns":bu.u_x_fold_elapsed_ns});
            let grouped_v=serde_json::json!({"group_count":gv.group_count,"group_owner_counts":gv.group_owner_counts,"group_term_counts":gv.group_term_counts,
                "baseline_term_callbacks":gv.baseline_term_callbacks,"template_term_count":gv.template_term_count,"template_capacity_bytes":gv.template_capacity_bytes,
                "bank_term_callbacks":gv.bank_term_callbacks,"handoff_term_callbacks":gv.handoff_term_callbacks,
                "grouped_state_peak_capacity_bytes":gv.grouped_state_peak_capacity_bytes,"local_rounds":gv.local_rounds,"owner_handoff_count":gv.owner_handoff_count,
                "baseline_elapsed_ns":gv.baseline_elapsed_ns,"bank_build_elapsed_ns":gv.bank_build_elapsed_ns,
                "local_v_elapsed_ns":gv.local_v_elapsed_ns,"owner_handoff_elapsed_ns":gv.owner_handoff_elapsed_ns});
            let proof_record=serde_json::json!({"file":"role1-native32.gkr","bytes":encoded.len(),
                "sha256":screen_hex(&crate::native_prefix_auth_plan::role0_sha256(&encoded)?),"rounds":64,"line_coefficients":33,"scalars":227,
                "canonical_codec_roundtrip":true,"independent_verify":true,"source_evaluation_crosscheck":true,
                "mutated_round_rejected":true,"changed_tip_rejected":true,"binding_mutants_rejected":true,
                "wrong_domain_rejected":true,"claim_matches_producer":true,"continuation_matches":true,"transcript_counters_match":true});
            let phase_marks=marks.iter().map(|m|serde_json::json!({"name":m.name,"elapsed_ns":m.elapsed_ns})).collect::<Vec<_>>();
            let claim_record=serde_json::json!({"point_hex":claim.point.iter().map(u0_hex_fr).collect::<Result<Vec<_>,_>>()?,"value_hex":u0_hex_fr(&claim.value)?});
            let timing_ms=serde_json::json!({"proof":proof_ms,"codec":codec_ms,"independent_verify":verify_ms,"source_mle":mle_ms,
                "whole_test":whole_started.elapsed().as_millis() as u64});
            let report=serde_json::json!({"schema":"native-prefix-role1-diagnostic-gkr-v1","state":"ROLE1_DIAGNOSTIC_GKR_PASS",
                "scope":scope,"admission":admission,"proof":proof_record,"claim":claim_record,"native_counts":native_counts,
                "boolean_u":boolean_u,"grouped_v":grouped_v,"phase_marks":phase_marks,"timing_ms":timing_ms});
            Ok((encoded,report))
        }).unwrap();
        assert_eq!(u0_file_info(&held).unwrap(),identity);
        assert_eq!(u0_file_info(&key.file).unwrap(),key.identity);
        assert_eq!(u0_file_info(&commitment.file).unwrap(),commitment.identity);
        role1_native32_export(&output,&encoded,&report).unwrap();
        role1_native32_marker("NIPOPOW_ROLE1_NATIVE32_COMPLETE",serde_json::json!({"proof_bytes":7264,
            "producer_owner_loads":102400,"term_callbacks":1624305664u64})).unwrap();
    }

    // This kernel calibration is deliberately separate from the role0 admitted
    // proof domain. It reuses only the pinned source/plan fixture and reader.
    #[cfg(test)]
    mod role1_calibration {
        use super::*;
        use crate::sparse_stream_roster as stream;
        use std::cell::Cell;

        const OWNERS:[usize;3]=[1,3072,4095];
        const WIDTH:usize=1<<20;
        const ROW_WIDTH:usize=1<<19;
        const OWNER_BITS:usize=12;
        const DOMAIN:&[u8]=b"NIPOPOW-NATIVE-ROLE1-OWNER-CALIBRATION-KERNEL-v1";

        fn owner_class_name(class:OwnerClass)->&'static str {match class {
            OwnerClass::Initial=>"initial",OwnerClass::Short(crate::short_daa_layout::Profile::M2)=>"short-m2",
            OwnerClass::Padding=>"padding",_=>"unexpected",
        }}
        fn expected_class(owner:usize)->OwnerClass {match owner {
            1=>OwnerClass::Initial,3072=>OwnerClass::Short(crate::short_daa_layout::Profile::M2),
            4095=>OwnerClass::Padding,_=>panic!("unexpected calibration owner"),
        }}
        fn expected_counts(owner:usize)->crate::daa_history_roster::HeaderCounts {match owner {
            1=>crate::daa_history_roster::HeaderCounts{emitted:396_561,omitted_worktree:78_194,omitted_mature_a4:0,omitted_short_a4:0},
            3072=>crate::daa_history_roster::HeaderCounts{emitted:388_369,omitted_worktree:78_194,omitted_mature_a4:0,omitted_short_a4:8_192},
            4095=>crate::daa_history_roster::HeaderCounts{emitted:396_561,omitted_worktree:78_194,omitted_mature_a4:0,omitted_short_a4:0},
            _=>panic!("unexpected calibration owner"),
        }}
        fn validate_owner_class(plan:&NativePrefixAuthPlan<'_>,owner:usize,class:OwnerClass)->Result<(),String>{
            if !OWNERS.contains(&owner) || plan.daa().owner_class(owner as u64)?!=class {
                return Err("role1 calibration owner/class admission".into());
            }Ok(())
        }
        fn validate_counts(owner:usize,counts:crate::daa_history_roster::HeaderCounts)->Result<(),String>{
            if counts!=expected_counts(owner){return Err("role1 owner-class term census mismatch".into());}Ok(())
        }
        fn owner_base(owner:usize)->Result<(usize,usize),String>{
            Ok((owner.checked_mul(ROW_WIDTH).ok_or("role1 owner row base overflow")?,
                owner.checked_mul(WIDTH).ok_or("role1 owner input base overflow")?))
        }
        fn project_term(mut term:Term,owner:usize)->Result<Term,String>{
            let (row_base,input_base)=owner_base(owner)?;
            let row_end=row_base.checked_add(ROW_WIDTH).ok_or("role1 owner row end overflow")?;
            let input_end=input_base.checked_add(WIDTH).ok_or("role1 owner input end overflow")?;
            if !(row_base..row_end).contains(&term.row)
                || !(input_base..input_end).contains(&term.gate.left)
                || !(input_base..input_end).contains(&term.gate.right) {
                return Err("role1 term escapes selected physical owner".into());
            }
            term.row-=row_base;term.gate.left-=input_base;term.gate.right-=input_base;Ok(term)
        }
        fn require_owner_buffer(values:&Vec<Fr>)->Result<(),String>{
            if values.len()!=WIDTH || values.capacity()!=WIDTH {return Err("role1 owner buffer length/capacity mismatch".into());}Ok(())
        }
        fn require_owner_encoding(values:&[Fr],bytes:&[u8])->Result<(),String>{
            if values.len()!=WIDTH || bytes.len()!=OWNER_BYTES {
                return Err("role1 owner encoding extent mismatch".into());
            }
            if !values.iter().enumerate().all(|(bit,value)|
                *value==Fr::from(((bytes[bit/8]>>(bit%8))&1) as u64)) {
                return Err("role1 owner encoding differs from held source bytes".into());
            }
            Ok(())
        }
        fn read_owner(source:&PackedFile,owner:usize,loads:&Cell<usize>)->Result<Vec<Fr>,String>{
            if owner>=4096{return Err("role1 owner outside packed source".into());}
            let mut values=Vec::with_capacity(WIDTH);
            for bank in 0..16 {
                let mut part=source.read_copy(1<<16,owner*16+bank)?;
                if part.len()!=1<<16 || part.capacity()>(1<<16) {return Err("role1 packed bank extent/capacity".into());}
                values.append(&mut part);
            }
            require_owner_buffer(&values)?;
            loads.set(loads.get().checked_add(1).ok_or("role1 owner load counter overflow")?);Ok(values)
        }
        fn bind_kernel(plan:&NativePrefixAuthPlan<'_>,owner:usize,class:OwnerClass,t:&mut Transcript)->Result<(),String>{
            if t.challenges()!=0{return Err("role1 kernel transcript already challenged".into());}
            validate_owner_class(plan,owner,class)?;
            if plan.descriptors().len()!=7 {return Err("role1 complete source-plan roster missing".into());}
            let descriptor=&plan.descriptors()[1];
            if descriptor.role!=1 || descriptor.name!="retained-header" || descriptor.input_log!=32 || descriptor.row_log!=31 {
                return Err("role1 native descriptor shape mismatch".into());
            }
            t.append_bytes(b"role1-calibration-domain",DOMAIN);
            t.append_bytes(b"role1-calibration-scope",b"kernel-only;not-admitted;no-opening");
            t.append_u64(b"role1-calibration-role",1);t.append_u64(b"role1-calibration-input-log",20);
            t.append_u64(b"role1-calibration-row-log",19);t.append_u64(b"role1-calibration-owner",owner as u64);
            t.append_bytes(b"role1-calibration-owner-class",owner_class_name(class).as_bytes());
            t.append_u64(b"role1-calibration-cache-budget",0);
            plan.bind_plan_identity(t)
        }
        fn extend_point(local:&[Fr],owner:usize)->Vec<Fr>{
            let mut point=local.to_vec();
            for bit in 0..OWNER_BITS {point.push(Fr::from(((owner>>bit)&1) as u64));}
            point
        }
        fn native_coefficients(plan:&NativePrefixAuthPlan<'_>,owner:usize,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String>{
            let rr=extend_point(r,owner);let uu=extend_point(u,owner);let vv=extend_point(v,owner);
            plan.daa().header_coefficients(&rr,&uu,&vv)
        }
        fn direct_coefficients(plan:&NativePrefixAuthPlan<'_>,owner:usize,local_r:&[Fr],local_u:&[Fr],local_v:&[Fr])
            ->Result<(crate::daa_history_roster::HeaderCounts,[Fr;4]),String>{
            assert_eq!((local_r.len(),local_u.len(),local_v.len()),(19,20,20));
            let r=extend_point(local_r,owner);let u=extend_point(local_u,owner);let v=extend_point(local_v,owner);
            assert!(local_r.iter().chain(local_u).chain(local_v).all(|x|*x!=Fr::zero()&&*x!=Fr::one()));
            let mut reference=Reference::new(&r,&u,&v);
            let counts=plan.daa().visit_header_terms(owner as u64,|term|{project_term(term.clone(),owner)?;reference.add(term)} )?;
            validate_counts(owner,counts)?;
            assert_eq!(plan.daa().header_coefficients(&r,&u,&v).unwrap(),reference.c,
                "role1 owner {owner} native analytic/reference coefficients");
            Ok((counts,reference.c))
        }
        fn owner_mle(held:&mut File,owner:usize,point:&[Fr])->Result<(Fr,usize),String>{
            if point.len()!=20{return Err("role1 local claim point width".into());}
            let bytes=held_slice(held,(owner*OWNER_BYTES) as u64);
            let nonzero=bytes.iter().filter(|byte|**byte!=0).count();
            let weights=crate::gkr::eq_weights(point);
            let mut value=Fr::zero();
            for bit in 0..WIDTH {
                if bytes[bit/8]>>(bit%8)&1!=0 {value+=weights[bit];}
            }
            Ok((value,nonzero))
        }
        fn capture_directory()->Result<PathBuf,String>{
            let path=PathBuf::from(std::env::var_os("NIPOPOW_NATIVE_ROLE1_CAPTURE_DIR")
                .ok_or("NIPOPOW_NATIVE_ROLE1_CAPTURE_DIR absent")?);
            if !path.is_absolute() || path.parent().map_or(true,|parent|!parent.is_dir()) {
                return Err("role1 capture directory must be a fresh absolute child of an existing directory".into());
            }
            match std::fs::symlink_metadata(&path) {
                Ok(_)=>return Err("role1 capture directory already exists".into()),
                Err(error) if error.kind()==std::io::ErrorKind::NotFound=>(),
                Err(error)=>return Err(format!("role1 capture path check: {error}")),
            }
            Ok(path)
        }
        fn write_capture(dir:&Path,proofs:&[(String,Vec<u8>)],report:&serde_json::Value)->Result<(),String>{
            std::fs::create_dir(dir).map_err(|error|error.to_string())?;
            for (name,bytes) in proofs {
                let mut file=OpenOptions::new().write(true).create_new(true).open(dir.join(name)).map_err(|e|e.to_string())?;
                file.write_all(bytes).map_err(|e|e.to_string())?;file.sync_all().map_err(|e|e.to_string())?;
            }
            let bytes=serde_json::to_vec_pretty(report).map_err(|e|e.to_string())?;
            let mut file=OpenOptions::new().write(true).create_new(true).open(dir.join("role1-result.json")).map_err(|e|e.to_string())?;
            file.write_all(&bytes).map_err(|e|e.to_string())?;file.sync_all().map_err(|e|e.to_string())?;Ok(())
        }
            fn write_grouped_capture(dir:&Path,proofs:&[(String,Vec<u8>)],report:&serde_json::Value)->Result<(),String>{
                std::fs::create_dir(dir).map_err(|error|error.to_string())?;
                for (name,bytes) in proofs {
                    let mut file=OpenOptions::new().write(true).create_new(true).open(dir.join(name)).map_err(|e|e.to_string())?;
                    file.write_all(bytes).map_err(|e|e.to_string())?;file.sync_all().map_err(|e|e.to_string())?;
                }
                let bytes=serde_json::to_vec_pretty(report).map_err(|e|e.to_string())?;
                let mut file=OpenOptions::new().write(true).create_new(true).open(dir.join("role1-grouped-v-result.json")).map_err(|e|e.to_string())?;
                file.write_all(&bytes).map_err(|e|e.to_string())?;file.sync_all().map_err(|e|e.to_string())?;Ok(())
            }
        fn phase_ms(marks:&[stream::TestPhaseMark],start:&str,end:&str)->u64{
            let a=marks.iter().find(|mark|mark.name==start).unwrap().elapsed_ns;
            let b=marks.iter().find(|mark|mark.name==end).unwrap().elapsed_ns;
            ((b-a)/1_000_000).min(u64::MAX as u128) as u64
        }
        fn verify_role1(plan:&NativePrefixAuthPlan<'_>,owner:usize,class:OwnerClass,proof:&gkr::GkrProof)
            ->Result<(InputClaim,Transcript),GkrError>{
            let mut transcript=Transcript::new(DOMAIN);bind_kernel(plan,owner,class,&mut transcript).map_err(|_|GkrError::PointDimension)?;
            let claim=gkr::verify_with_wiring(&[20],1<<19,proof,&mut transcript,|_|{},|layer,r,u,v|{
                if layer!=0{return Err(GkrError::PointDimension);}
                native_coefficients(plan,owner,r,u,v).map_err(|_|GkrError::PointDimension)
            })?;
            Ok((claim,transcript))
        }

        #[test]
        fn native_role1_shape_is_exact(){
            assert_eq!((crate::native_prefix_auth_plan::INPUT_LOGS[1],crate::native_prefix_auth_plan::ROW_LOGS[1]),(32,31));
            assert_eq!((1usize<<20,1usize<<19,1usize<<12),(WIDTH,ROW_WIDTH,1usize<<OWNER_BITS));
        }

        #[test]
        #[ignore="bounded pinned witness and role1 owner mapping controls; no producer proof"]
        fn native_role1_owner_mapping_controls_bounded(){
            let (source,mut held,identity)=useq_admit().unwrap();
            let path=PathBuf::from(std::env::var_os("NIPOPOW_NATIVE_U_SEQUENCE_WITNESS").unwrap());
            let detached=PackedFile::open_with_limit(&path,32,32).unwrap();
            assert!(source.native_role0_view().unwrap().require_same_source(&detached).is_err());
            with_plan(|parent,plan,candidate|{
              for owner in OWNERS {
                let class=plan.daa().owner_class(owner as u64).unwrap();
                assert_eq!(class,expected_class(owner));assert!(validate_owner_class(plan,owner,class).is_ok());
                let local_r=general(19,17+owner as u64);let local_u=general(20,27+owner as u64);let local_v=general(20,39+owner as u64);
                let (counts,_)=direct_coefficients(plan,owner,&local_r,&local_u,&local_v).unwrap();
                assert!(validate_counts(owner,counts).is_ok());
                let mut loads=Cell::new(0);let actual=read_owner(&source,owner,&loads).unwrap();
                assert_eq!(loads.get(),1);assert_eq!(actual.len(),WIDTH);assert_eq!(actual.capacity(),WIDTH);
                let bytes=held_slice(&mut held,(owner*OWNER_BYTES) as u64);
                require_owner_encoding(&actual,&bytes).unwrap();
                if owner==4095 {
                    assert_eq!(bytes.iter().filter(|byte|**byte!=0).count(),93_036);
                    let zeros=vec![Fr::zero();WIDTH];
                    assert!(require_owner_encoding(&zeros,&bytes).is_err(),
                        "synthetic zero padding is rejected by the source encoding validator");
                }
                if owner==1 {
                    let shifted=read_owner(&source,owner+1,&Cell::new(0)).unwrap();
                    assert!(require_owner_encoding(&shifted,&bytes).is_err(),
                        "one-owner shifted load is rejected by the source encoding validator");
                }
                assert!(require_owner_buffer(&actual).is_ok());
                let mut oversized=Vec::with_capacity(WIDTH+1);oversized.resize(WIDTH,Fr::zero());
                assert_eq!(oversized.len(),WIDTH);assert!(oversized.capacity()>WIDTH);assert!(require_owner_buffer(&oversized).is_err());
                let base=Term{row:owner*ROW_WIDTH,gate:crate::gkr::Gate{left:owner*WIDTH,right:owner*WIDTH,c0:Fr::zero(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}};
                assert!(project_term(base.clone(),owner).is_ok());
                let mut bad_row=base.clone();bad_row.row+=ROW_WIDTH;assert!(project_term(bad_row,owner).is_err(),"shifted owner row rejected");
                let mut bad_left=base.clone();bad_left.gate.left+=WIDTH;assert!(project_term(bad_left,owner).is_err(),"off-owner left wire rejected");
                let mut bad_right=base;bad_right.gate.right+=WIDTH;assert!(project_term(bad_right,owner).is_err(),"off-owner right wire rejected");
              }
              for (owner,wrong) in [(1,OwnerClass::Padding),(3072,OwnerClass::Initial),(4095,OwnerClass::Short(crate::short_daa_layout::Profile::M2))] {
                  assert!(bind_kernel(plan,owner,wrong,&mut Transcript::new(DOMAIN)).is_err(),"wrong owner class rejected");
              }
              let good=expected_counts(1);let mut drift=good;drift.emitted+=1;
              assert!(validate_counts(1,drift).is_err(),"isolated initial census drift rejected");
              let mut drift=expected_counts(3072);drift.omitted_short_a4-=1;
              assert!(validate_counts(3072,drift).is_err(),"isolated short A4 census drift rejected");
              let mut drift=expected_counts(4095);drift.emitted=0;
              assert!(validate_counts(4095,drift).is_err(),"isolated padding census drift rejected");
              source.reset_io_metrics();
                let mut challenged=Transcript::new(DOMAIN);challenged.challenge_scalar(b"before-bind");
                assert!(bind_kernel(plan,1,OwnerClass::Initial,&mut challenged).is_err());
                let mut exact=Transcript::new(DOMAIN);bind_kernel(plan,1,OwnerClass::Initial,&mut exact).unwrap();
                let challenge=exact.challenge_scalar(b"role1-binding-control");
                let mut wrong_owner=Transcript::new(DOMAIN);bind_kernel(plan,3072,expected_class(3072),&mut wrong_owner).unwrap();
                assert_ne!(challenge,wrong_owner.challenge_scalar(b"role1-binding-control"));
                let mut no_plan=Transcript::new(DOMAIN);
                no_plan.append_bytes(b"role1-calibration-domain",DOMAIN);
                no_plan.append_bytes(b"role1-calibration-scope",b"kernel-only;not-admitted;no-opening");
                no_plan.append_u64(b"role1-calibration-role",1);no_plan.append_u64(b"role1-calibration-input-log",20);
                no_plan.append_u64(b"role1-calibration-row-log",19);no_plan.append_u64(b"role1-calibration-owner",1);
                no_plan.append_bytes(b"role1-calibration-owner-class",b"initial");no_plan.append_u64(b"role1-calibration-cache-budget",0);
                assert_ne!(challenge,no_plan.challenge_scalar(b"role1-binding-control"),"plan identity omission rejected");
                let mut no_role=Transcript::new(DOMAIN);no_role.append_bytes(b"role1-calibration-domain",DOMAIN);
                no_role.append_bytes(b"role1-calibration-scope",b"kernel-only;not-admitted;no-opening");
                no_role.append_u64(b"role1-calibration-input-log",20);no_role.append_u64(b"role1-calibration-row-log",19);
                no_role.append_u64(b"role1-calibration-owner",1);no_role.append_bytes(b"role1-calibration-owner-class",b"initial");
                no_role.append_u64(b"role1-calibration-cache-budget",0);plan.bind_plan_identity(&mut no_role).unwrap();
                assert_ne!(challenge,no_role.challenge_scalar(b"role1-binding-control"),"role field omission rejected");
                let mut changed_candidate=candidate.clone();changed_candidate.tip[0]^=1;
                let changed_plan=NativePrefixAuthPlan::compile(parent,Selection::s12(),changed_candidate).unwrap();
                let mut changed=Transcript::new(DOMAIN);bind_kernel(&changed_plan,1,OwnerClass::Initial,&mut changed).unwrap();
                assert_ne!(challenge,changed.challenge_scalar(b"role1-binding-control"),"source-plan candidate identity mutant rejected");
            });
            assert_eq!(source.io_metrics_snapshot().read_calls,0,"binding controls precede packed owner reads");
            assert_eq!(u0_file_info(&held).unwrap(),identity);
        }

        #[test]
        fn native_role1_phase_observer_is_transcript_neutral(){
            // A nontrivial satisfied relation exercises real row and wire weights:
            // -2 + 2*1 + 3*0 + 5*(1*0) = 0.
            let input=vec![Fr::one(),Fr::zero(),Fr::one(),Fr::one()];
            let terms=vec![Term{row:0,gate:crate::gkr::Gate{left:0,right:1,
                c0:-Fr::from(2u64),c1:Fr::from(2u64),c2:Fr::from(3u64),c3:Fr::from(5u64)}}];
            let run=|observed:bool|{
                let mut transcript=Transcript::new(b"role1-phase-observer-control-v1");
                if observed {stream::begin_phase_trace_for_test();}
                let result=stream::prove_with_cache_budget_for_test(2,0,2,0,&[2],Some(0),
                    |_|Ok(input.clone()),&mut transcript, |_|{},
                    |copy,sink|{assert_eq!(copy,0);for term in &terms{sink(term.clone())?;}Ok(())},
                    |r,u,v|{
                        let weight=crate::gkr::eq_weights(r)[0]
                            *crate::gkr::eq_weights(u)[0]
                            *crate::gkr::eq_weights(v)[1];
                        Ok([weight*(-Fr::from(2u64)),weight*Fr::from(2u64),
                            weight*Fr::from(3u64),weight*Fr::from(5u64)])
                    }).unwrap();
                let marks=if observed {stream::take_phase_trace_for_test()}else{Vec::new()};
                (result,transcript,marks)
            };
            let (plain,mut plain_t,_)=run(false);let (observed,mut observed_t,marks)=run(true);
            assert_eq!(plain,observed,"observer must preserve proof bytes and claim");
            assert_eq!(plain_t.challenges(),observed_t.challenges());
            assert_eq!(plain_t.challenge_scalar(b"observer-transcript-equivalence"),
                observed_t.challenge_scalar(b"observer-transcript-equivalence"),
                "observer must preserve transcript bytes/challenges");
            assert!(marks.iter().any(|mark|mark.name=="line_done"));
        }

        #[test]
        #[ignore="bounded per-owner role1 streamed-kernel calibration; no native full-history claim"]
        fn native_role1_per_owner_cost_calibration_bounded()->Result<(),String>{
            run_role1_owner_calibration(false)
        }

        #[test]
        #[ignore="bounded role1 direct-U-prefix equivalence and cost experiment; no native full-history claim"]
        fn native_role1_direct_u_prefix_cost_calibration_bounded()->Result<(),String>{
            run_role1_owner_calibration(true)
        }

        fn run_role1_owner_calibration(direct_u_prefix:bool)->Result<(),String>{
            let admission_started=Instant::now();
            let (source,mut held,witness_identity)=useq_admit().unwrap();
            let admission_elapsed=admission_started.elapsed().as_millis() as u64;
            let output=capture_directory().unwrap();
            let mut proofs=Vec::with_capacity(3);let mut rows=Vec::with_capacity(3);
            with_plan(|parent,plan,candidate| -> Result<(),String> {
                assert_eq!((candidate.n,plan.descriptors()[1].input_log,plan.descriptors()[1].row_log),(3073,32,31));
                for owner in OWNERS {
                    let class=plan.daa().owner_class(owner as u64).unwrap();assert_eq!(class,expected_class(owner));
                    let mut producer=Transcript::new(DOMAIN);bind_kernel(plan,owner,class,&mut producer).unwrap();
                    let mut transcript_preflight=Transcript::new(DOMAIN);
                    bind_kernel(plan,owner,class,&mut transcript_preflight).unwrap();assert_eq!(transcript_preflight.challenges(),0);
                    let local_r=general(19,401+owner as u64);let local_u=general(20,503+owner as u64);let local_v=general(20,607+owner as u64);
                    // Ensure non-Boolean challenge coordinates; the high owner suffix is fixed by the projection.
                    assert!(local_r.iter().all(|x|*x!=Fr::zero()&&*x!=Fr::one()));
                    assert!(local_u.iter().all(|x|*x!=Fr::zero()&&*x!=Fr::one()));
                    assert!(local_v.iter().all(|x|*x!=Fr::zero()&&*x!=Fr::one()));
                    let direct_started=Instant::now();
                    let (counts,direct)=direct_coefficients(plan,owner,&local_r,&local_u,&local_v)?;
                    let direct_elapsed=direct_started.elapsed().as_millis() as u64;
                    assert_eq!(native_coefficients(plan,owner,&local_r,&local_u,&local_v).unwrap(),direct);
                    let mut local_counts=0usize;
                    assert_eq!(std::mem::size_of::<Fr>(),32);
                    let preflight_loads=Cell::new(0usize);source.reset_io_metrics();
                    let preflight=read_owner(&source,owner,&preflight_loads)?;
                    let preflight_bytes=held_slice(&mut held,(owner*OWNER_BYTES) as u64);
                    require_owner_encoding(&preflight,&preflight_bytes)?;
                    let preflight_nonzero=preflight_bytes.iter().filter(|byte|**byte!=0).count();
                    if owner==4095 {assert_eq!(preflight_nonzero,93_036,"real padding owner bits retained");}
                    let preflight_io=source.io_metrics_snapshot();assert_eq!(preflight_loads.get(),1);
                    drop(preflight);source.reset_io_metrics();let loads=Cell::new(0usize);
                    println!("NIPOPOW_ROLE1_OWNER_BEGIN {}",serde_json::json!({"owner":owner,"owner_class":owner_class_name(class)}));
                    use std::io::Write;let _=std::io::stdout().flush();
                    stream::begin_phase_trace_for_test();let proof_started=Instant::now();
                    let mut load=|copy|{if copy!=0{return Err("role1 calibration copy index".into());}read_owner(&source,owner,&loads)};
                    let mut visit=|copy,sink:&mut dyn FnMut(Term)->Result<(),String>|{
                        if copy!=0{return Err("role1 one-copy term dispatch".into());}
                            let observed=plan.daa().visit_header_terms(owner as u64,|term|{
                                let local=project_term(term,owner)?;local_counts=local_counts.checked_add(1).ok_or("role1 term count overflow")?;sink(local)
                            })?;validate_counts(owner,observed)?;if observed!=counts{return Err("role1 per-owner DAA census changed".into());}Ok(())};
                    let wiring=|r:&[Fr],u:&[Fr],v:&[Fr]|native_coefficients(plan,owner,r,u,v);
                    let (proof,producer_claim)=if direct_u_prefix{
                        stream::prove_with_direct_u_prefix_for_test(20,0,19,0,&[19],Some(0),
                            &mut load,&mut producer,|_|{},&mut visit,wiring)
                    }else{
                        stream::prove_with_cache_budget_for_test(20,0,19,0,&[19],Some(0),
                            &mut load,&mut producer,|_|{},&mut visit,wiring)
                    }?;
                    let proof_elapsed=proof_started.elapsed().as_millis() as u64;
                    let marks=stream::take_phase_trace_for_test();
                    assert!(marks.iter().any(|mark|mark.name=="u_cache_streamed"));
                    assert!(marks.iter().any(|mark|mark.name=="v_cache_streamed"));
                    assert!(!marks.iter().any(|mark|mark.name=="u_cache_incremental"||mark.name=="v_cache_incremental"));
                    assert_eq!(local_counts,counts.emitted*45,"role1 45-sweep term recurrence changed");
                    assert_eq!(loads.get(),45,"role1 producer load recurrence changed");
                    let io=source.io_metrics_snapshot();assert_eq!(io.read_bytes,loads.get() as u64*OWNER_BYTES as u64);
                    let codec_started=Instant::now();
                    let encoded=gkr::encode_proof(&proof).unwrap();assert_eq!(encoded.len(),4576);
                    let decoded=gkr::decode_dimensions(&[20],&encoded).unwrap();assert_eq!(gkr::encode_proof(&decoded).unwrap(),encoded);
                    let codec_elapsed=codec_started.elapsed().as_millis() as u64;
                    let verify_started=Instant::now();let (claim,mut verifier)=verify_role1(plan,owner,class,&decoded).unwrap();
                    let verify_elapsed=verify_started.elapsed().as_millis() as u64;
                    assert_eq!(claim,producer_claim);assert_eq!(producer.challenge_scalar(b"role1-continuation"),verifier.challenge_scalar(b"role1-continuation"));
                    let mle_started=Instant::now();let (mle,nonzero_bytes)=owner_mle(&mut held,owner,&claim.point)?;
                    let mle_elapsed=mle_started.elapsed().as_millis() as u64;assert_eq!(mle,claim.value);
                    if owner==4095 {assert_eq!(nonzero_bytes,93_036);}
                    let mut mutant=decoded.clone();mutant.layers[0].rounds[0][0]+=Fr::one();
                    assert!(verify_role1(plan,owner,class,&mutant).is_err(),"mutated GKR round rejected");
                    let sha=screen_hex(&crate::native_prefix_auth_plan::role0_sha256(&encoded).unwrap());
                    if direct_u_prefix {
                        let baseline_sha=match owner {
                            1=>"BDF9739CB7BE77858966F9FEDA83C87B306410BE8C18C67BCA88E18BE01AC960",
                            3072=>"62090F9B2BBAA5AFAD374CAC271DFC2F722D5AD36CC8085ACD186DEB07EF4899",
                            4095=>"4DA7EA8FC1381D067FB5F07058B7FD69E3221B2C783EBBBD993849FDAF391B28",
                            _=>return Err("role1 direct-U baseline owner is not pinned".into()),
                        };
                        assert_eq!(sha,baseline_sha,"direct-U proof must equal the immutable baseline bytes");
                    }
                    let filename=format!("role1-owner-{owner:04}.gkr");
                    println!("NIPOPOW_ROLE1_OWNER_COMPLETE {}",serde_json::json!({"owner":owner,"proof_bytes":encoded.len(),"producer_owner_loads":loads.get()}));
                    let _=std::io::stdout().flush();
                    proofs.push((filename.clone(),encoded));
                    let mark_json=serde_json::Value::Array(marks.iter().map(|mark|serde_json::json!({"name":mark.name,"elapsed_ns":mark.elapsed_ns})).collect());
                    let mut row=serde_json::json!({
                        "owner":owner,"owner_class":owner_class_name(class),"emitted":counts.emitted,
                        "omitted_worktree":counts.omitted_worktree,"omitted_mature_a4":counts.omitted_mature_a4,
                        "omitted_short_a4":counts.omitted_short_a4,"local_input_log":20,"local_row_log":19,
                        "native_input_log":32,"native_row_log":31,"cache_budget_bytes":0,"fallback":"streamed",
                        "term_visits_per_sweep":counts.emitted,"producer_term_visits":local_counts,
                        "producer_owner_loads":loads.get(),"physical_packed_read_bytes":io.read_bytes,
                        "owner_preflight_loads":preflight_loads.get(),"owner_preflight_packed_read_bytes":preflight_io.read_bytes,
                        "owner_preflight_held_read_bytes":OWNER_BYTES,
                        "expanded_owner_vector_bytes":loads.get() as u64*WIDTH as u64*32
                    });
                    let measurements=serde_json::json!({
                        "peak_owner_vector_capacity_fields":WIDTH,"owner_mle_source_bytes":OWNER_BYTES,
                        "owner_vector_bytes":WIDTH as u64*32,"bank_scratch_max_bytes":(1u64<<16)*32,
                        "packed_byte_scratch_max_bytes":1u64<<13,
                        "owner_plus_bank_transient_bytes":(WIDTH as u64+(1u64<<16))*32,
                        "owner_bank_and_byte_scratch_bytes":(WIDTH as u64+(1u64<<16))*32+(1u64<<13),
                        "owner_mle_nonzero_bytes":nonzero_bytes,"phase_marks":mark_json,
                        "timing_ms":{"producer":proof_elapsed,"codec":codec_elapsed,"independent_verify":verify_elapsed,"owner_mle":mle_elapsed,
                            "direct_coefficients":direct_elapsed,"baseline":phase_ms(&marks,"baseline_start","baseline_done"),
                            "u_anchor":phase_ms(&marks,"baseline_done","u_anchor_done"),
                            "u_local":phase_ms(&marks,"u_anchor_done","u_local_done"),
                            "u_handoff":phase_ms(&marks,"u_local_done","u_handoff_done"),
                            "v_anchor":phase_ms(&marks,"u_handoff_done","v_anchor_done"),
                            "v_local":phase_ms(&marks,"v_anchor_done","v_local_done"),
                            "v_handoff":phase_ms(&marks,"v_local_done","v_handoff_done"),
                            "terminal_wiring":phase_ms(&marks,"v_handoff_done","terminal_wiring_done"),
                            "line":phase_ms(&marks,"line_start","line_done")},
                        "proof":{"file":filename,"bytes":4576,"sha256":sha,"rounds":40,"line_coefficients":21,
                            "canonical_codec_roundtrip":true,"independent_verify":true,"claim_matches_producer":true,
                            "owner_local_mle_matches":true,"continuation_matches":true,"mutated_round_rejected":true}
                    });
                    for (key,value) in measurements.as_object().unwrap() {
                        assert!(row.as_object_mut().unwrap().insert(key.clone(),value.clone()).is_none(),
                            "role1 report fields must not overlap");
                    }
                    rows.push(row);
                }
                // Only the bound tip changes: relation, owner, class and proof
                // remain identical. Compile this control once after the large
                // producer arrays have been dropped.
                let mut changed_candidate=candidate.clone();changed_candidate.tip[0]^=1;
                let changed_plan=NativePrefixAuthPlan::compile(parent,Selection::s12(),changed_candidate)?;
                assert_eq!(proofs.len(),OWNERS.len());
                for (owner,(_,encoded)) in OWNERS.into_iter().zip(proofs.iter()) {
                    let decoded=gkr::decode_dimensions(&[20],encoded).unwrap();
                    assert!(verify_role1(&changed_plan,owner,expected_class(owner),&decoded).is_err(),
                        "same role1 proof rejected after isolated bound candidate-tip mutation");
                }
                for row in &mut rows {row["proof"]["changed_plan_rejected"]=serde_json::json!(true);}
                Ok(())
            }).unwrap();
            assert_eq!(u0_file_info(&held).unwrap(),witness_identity);
            let mut report=serde_json::json!({
                "schema":"native-prefix-role1-owner-calibration-v1","state":"ROLE1_OWNER_CALIBRATION_PASS",
                "scope":{"role":1,"native_n":3073,"local_input_log":20,"local_row_log":19,
                    "native_input_log":32,"native_row_log":31,"owner_bits":12,"native32_claim":false,"role1_full_native_claim":false,
                    "common_opening":false,"all_seven_claims":false,"full_history":false,"light_client":false,
                    "no_fork":false,"eip":false,"oracle":false,"production":false,"key_admission":false,
                    "setup_or_recommit":false,"commitment_claim":false,"dory_opening":false},
                "owner_order":[1,3072,4095],"producer_owner_loads":135,
                "admission":{"locked_witness_bytes_hashed":536_870_912,"elapsed_ms":admission_elapsed},
                "owner_preflight_packed_read_bytes":rows.iter().map(|row|row["owner_preflight_packed_read_bytes"].as_u64().unwrap_or(0)).sum::<u64>(),
                "owner_preflight_held_read_bytes":3u64*OWNER_BYTES as u64,
                "physical_packed_read_bytes":135u64*OWNER_BYTES as u64,
                "expanded_owner_vector_bytes":135u64*WIDTH as u64*32,
                "verifier_owner_mle_read_bytes":3u64*OWNER_BYTES as u64,
                "owner_buffer_memory":{"owner_vector_bytes":WIDTH as u64*32,"bank_scratch_max_bytes":(1u64<<16)*32,
                    "packed_byte_scratch_max_bytes":1u64<<13,
                    "owner_plus_bank_transient_bytes":(WIDTH as u64+(1u64<<16))*32,
                    "owner_bank_and_byte_scratch_bytes":(WIDTH as u64+(1u64<<16))*32+(1u64<<13),"process_peak_claim":false},
                "proofs":rows
            });
            if direct_u_prefix {
                let fields=report.as_object_mut().unwrap();
                assert!(fields.insert("producer_variant".into(),serde_json::json!("direct_u_prefix_v1")).is_none());
                assert!(fields.insert("baseline_proofs_equal".into(),serde_json::json!(true)).is_none());
            }
            write_capture(&output,&proofs,&report).unwrap();
            Ok(())
        }

        mod grouped_v_calibration {
            use super::*;
            use ark_serialize::CanonicalSerialize;
            use std::io::Write as _;

            const OWNERS:[usize;4]=[1,2048,3072,4095];
            const GROUPS:[usize;4]=[0,0,1,0];
            const GROUP_TERMS:[usize;2]=[396_561,388_369];
            const GROUP_OWNERS:[usize;2]=[3,1];
            const FULL_TERMS:usize=396_561;
            const SHORT_TERMS:usize=388_369;
            const DOMAIN:&[u8]=b"NIPOPOW-NATIVE-ROLE1-GROUPED-V-CALIBRATION-v1";
            const STATE_LIMIT:usize=512*1024*1024;

            fn class_name(class:OwnerClass)->&'static str {match class {
                OwnerClass::Initial=>"initial",
                OwnerClass::M1=>"m1",
                OwnerClass::Short(crate::short_daa_layout::Profile::M2)=>"short-m2",
                OwnerClass::Padding=>"padding",
                _=>"unexpected",
            }}
            fn expected_class(owner:usize)->OwnerClass {match owner {
                1=>OwnerClass::Initial,2048=>OwnerClass::M1,
                3072=>OwnerClass::Short(crate::short_daa_layout::Profile::M2),
                4095=>OwnerClass::Padding,_=>panic!("unexpected grouped-V owner"),
            }}
            fn terms_for(owner:usize)->usize {if owner==3072 {SHORT_TERMS}else{FULL_TERMS}}
            fn admit_native_shape(plan:&NativePrefixAuthPlan<'_>)->Result<(),String>{
                if plan.daa().headers()!=3073 || plan.daa().slot_log()!=12 || plan.descriptors().len()!=7 {
                    return Err("grouped-V native plan dimensions".into());
                }
                let d=&plan.descriptors()[1];
                if d.role!=1 || d.name!="retained-header" || d.input_log!=32 || d.row_log!=31 {
                    return Err("grouped-V native descriptor shape".into());
                }
                let mut short_count=0usize;
                for owner in 0..4096 {
                    match plan.daa().owner_class(owner)? {
                        OwnerClass::Short(crate::short_daa_layout::Profile::M2) if owner==3072=>short_count+=1,
                        OwnerClass::Genesis|OwnerClass::Initial|OwnerClass::Carry|OwnerClass::Singleton|OwnerClass::M1|OwnerClass::Padding=>(),
                        _=>return Err("grouped-V unexpected native owner topology".into()),
                    }
                }
                if short_count!=1{return Err("grouped-V short owner census".into());}
                validate_group_map(plan,&OWNERS,&GROUPS)
            }
            fn check_header_counts(owner:usize,counts:crate::daa_history_roster::HeaderCounts)->Result<(),String>{
                if counts.emitted!=terms_for(owner) || counts.omitted_worktree!=78_194
                    || counts.omitted_mature_a4!=0 || counts.omitted_short_a4!=if owner==3072{8192}else{0} {
                    return Err("grouped-V complete native header census".into());
                }
                Ok(())
            }
            fn owner_slot(copy:usize)->Result<usize,String>{OWNERS.get(copy).copied().ok_or("grouped-V copy index".into())}
            fn validate_group_map(plan:&NativePrefixAuthPlan<'_>,owners:&[usize],groups:&[usize])->Result<(),String>{
                if owners!=OWNERS.as_slice() || groups.len()!=4{return Err("grouped-V owner order/extent differs from the admitted projection".into());}
                for (owner,group) in owners.iter().copied().zip(groups.iter().copied()){
                    let class=plan.daa().owner_class(owner as u64)?;
                    if class!=expected_class(owner) || group!=usize::from(matches!(class,OwnerClass::Short(_))){
                        return Err("grouped-V caller map differs from plan-derived class".into());
                    }
                }
                Ok(())
            }
            fn validate_group_census(owners:&[usize],groups:&[usize],terms:&[usize],expected:&[usize])->Result<(),String>{
                if owners.len()!=4 || groups.len()!=4 || terms.len()!=4 || expected.len()!=2 {
                    return Err("grouped-V census dimensions".into());
                }
                let mut templates=[None,None];
                for ((owner,group),count) in owners.iter().zip(groups).zip(terms){
                    let slot=templates.get_mut(*group).ok_or("grouped-V census group index")?;
                    if *count!=terms_for(*owner) || matches!(*slot,Some(prior) if prior!=*count){
                        return Err("grouped-V member topology/census differs within group".into());
                    }
                    *slot=Some(*count);
                }
                let actual=[templates[0].ok_or("grouped-V empty group 0")?,templates[1].ok_or("grouped-V empty group 1")?];
                if actual.as_slice()!=expected{return Err("grouped-V template term census differs".into());}
                Ok(())
            }
            fn projected_bind(plan:&NativePrefixAuthPlan<'_>,t:&mut Transcript)->Result<(),String>{
                if t.challenges()!=0 || plan.descriptors().len()!=7 {
                    return Err("grouped-V prechallenge source-plan shape".into());
                }
                let descriptor=&plan.descriptors()[1];
                if descriptor.role!=1 || descriptor.name!="retained-header" || descriptor.input_log!=32 || descriptor.row_log!=31 {
                    return Err("grouped-V native descriptor shape".into());
                }
                t.append_bytes(b"role1-grouped-v-domain",DOMAIN);
                t.append_bytes(b"role1-grouped-v-scope",b"four-owner projected role1 kernel;diagnostic only;no opening");
                t.append_u64(b"role1-grouped-v-role",1);
                t.append_u64(b"role1-grouped-v-native-n",3073);
                t.append_u64(b"role1-grouped-v-local-input-log",20);
                t.append_u64(b"role1-grouped-v-local-row-log",19);
                t.append_u64(b"role1-grouped-v-copy-bits",2);
                for (slot,owner) in OWNERS.iter().copied().enumerate(){
                    let class=plan.daa().owner_class(owner as u64)?;
                    if class!=expected_class(owner){return Err("grouped-V physical owner class".into());}
                    t.append_u64(b"role1-grouped-v-copy-slot",slot as u64);
                    t.append_u64(b"role1-grouped-v-physical-owner",owner as u64);
                    t.append_bytes(b"role1-grouped-v-owner-class",class_name(class).as_bytes());
                }
                // Optimization mode/grouping is deliberately not transcript-bound.
                plan.bind_plan_identity(t)
            }
            fn owner_coefficients(plan:&NativePrefixAuthPlan<'_>,owner:usize,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String>{
                if (r.len(),u.len(),v.len())!=(19,20,20){return Err("grouped-V local coordinate dimensions".into());}
                native_coefficients(plan,owner,r,u,v)
            }
            fn projected_coefficients(plan:&NativePrefixAuthPlan<'_>,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String>{
                if (r.len(),u.len(),v.len())!=(21,22,22){return Err("grouped-V projected coordinate dimensions".into());}
                let rw=crate::gkr::eq_weights(&r[19..]);
                let uw=crate::gkr::eq_weights(&u[20..]);
                let vw=crate::gkr::eq_weights(&v[20..]);
                let mut out=[Fr::zero();4];
                for (slot,owner) in OWNERS.iter().copied().enumerate(){
                    let c=owner_coefficients(plan,owner,&r[..19],&u[..20],&v[..20])?;
                    let weight=rw[slot]*uw[slot]*vw[slot];
                    for i in 0..4 {out[i]+=weight*c[i];}
                }
                Ok(out)
            }
            fn bind_projected(plan:&NativePrefixAuthPlan<'_>,t:&mut Transcript)->Result<(),String>{projected_bind(plan,t)}
            fn verify_projected(plan:&NativePrefixAuthPlan<'_>,proof:&gkr::GkrProof)->Result<(InputClaim,Transcript),GkrError>{
                let mut transcript=Transcript::new(DOMAIN);
                bind_projected(plan,&mut transcript).map_err(|_|GkrError::PointDimension)?;
                let claim=gkr::verify_with_wiring(&[22],1<<21,proof,&mut transcript,|_|{},|layer,r,u,v|{
                    if layer!=0{return Err(GkrError::PointDimension);}
                    projected_coefficients(plan,r,u,v).map_err(|_|GkrError::PointDimension)
                })?;
                Ok((claim,transcript))
            }
            fn encoded_fr(value:&Fr)->String{
                let mut bytes=Vec::with_capacity(value.compressed_size());
                value.serialize_compressed(&mut bytes).unwrap();
                assert_eq!(bytes.len(),32);
                screen_hex(&bytes)
            }
            fn local_mle(held:&mut File,owner:usize,point:&[Fr])->Result<(Fr,usize),String>{
                if point.len()!=20{return Err("grouped-V local MLE point width".into());}
                let bytes=held_slice(held,(owner*OWNER_BYTES) as u64);
                let nonzero=bytes.iter().filter(|byte|**byte!=0).count();
                let weights=crate::gkr::eq_weights(point);let mut value=Fr::zero();
                for bit in 0..WIDTH {if bytes[bit/8]>>(bit%8)&1!=0 {value+=weights[bit];}}
                Ok((value,nonzero))
            }
            fn projected_mle(held:&mut File,point:&[Fr])->Result<(Fr,usize),String>{
                if point.len()!=22{return Err("grouped-V projected MLE point width".into());}
                let slot_weights=crate::gkr::eq_weights(&point[20..]);let mut value=Fr::zero();let mut padding_nonzero=0;
                for (slot,owner) in OWNERS.iter().copied().enumerate(){
                    let (local,nonzero)=local_mle(held,owner,&point[..20])?;
                    value+=slot_weights[slot]*local;
                    if owner==4095 {padding_nonzero=nonzero;}
                }
                Ok((value,padding_nonzero))
            }
            fn rebased_term(term:Term,slot:usize)->Result<Term,String>{
                if slot>=4 || term.row>=ROW_WIDTH || term.gate.left>=WIDTH || term.gate.right>=WIDTH {
                    return Err("grouped-V local term projection escaped row/input window".into());
                }
                Ok(Term{row:slot*ROW_WIDTH+term.row,gate:crate::gkr::Gate{
                    left:slot*WIDTH+term.gate.left,right:slot*WIDTH+term.gate.right,
                    c0:term.gate.c0,c1:term.gate.c1,c2:term.gate.c2,c3:term.gate.c3,
                }})
            }
            fn report_phase_marks(marks:&[stream::TestPhaseMark])->serde_json::Value{
                serde_json::Value::Array(marks.iter().map(|mark|serde_json::json!({"name":mark.name,"elapsed_ns":mark.elapsed_ns})).collect())
            }
            fn timing_ms(start:Instant)->u64{start.elapsed().as_millis().min(u64::MAX as u128) as u64}
            fn run_projection_controls(plan:&NativePrefixAuthPlan<'_>)->Result<(),String>{
                admit_native_shape(plan)?;
                let mut group_by_copy=Vec::with_capacity(4);let mut counts=Vec::with_capacity(4);
                for owner in OWNERS {
                    let class=plan.daa().owner_class(owner as u64)?;
                    if class!=expected_class(owner){return Err("grouped-V owner class changed".into());}
                    let group=if matches!(class,OwnerClass::Short(_)){1}else{0};
                    group_by_copy.push(group);counts.push(terms_for(owner));
                }
                if group_by_copy.as_slice()!=GROUPS.as_slice() || counts.as_slice()!=[FULL_TERMS,FULL_TERMS,SHORT_TERMS,FULL_TERMS].as_slice() {
                    return Err("grouped-V owner-derived group/census mismatch".into());
                }
                validate_group_map(plan,&OWNERS,&group_by_copy)?;
                let _good=stream::GroupedVAdmission::try_new(2,&group_by_copy,&GROUP_TERMS)?;
                for (bad_map,bad_counts) in [
                    (vec![0,0,2,0],GROUP_TERMS.to_vec()),
                    (vec![0,0,0,0],GROUP_TERMS.to_vec()),
                ] {
                    if stream::GroupedVAdmission::try_new(2,&bad_map,&bad_counts).is_ok(){
                        return Err("grouped-V isolated admission mutant accepted".into());
                    }
                }
                if validate_group_census(&OWNERS,&group_by_copy,&counts,&[FULL_TERMS,SHORT_TERMS+1]).is_ok(){
                    return Err("grouped-V isolated expected-template-count mutant accepted".into());
                }
                // The actual high-owner projection is checked against the
                // unchanged term visitor at a non-Boolean point.
                let r=general(21,31);let u=general(22,47);let v=general(22,59);
                if r.iter().chain(&u).chain(&v).any(|x|*x==Fr::zero()||*x==Fr::one()){
                    return Err("grouped-V control point unexpectedly Boolean".into());
                }
                let analytic=projected_coefficients(plan,&r,&u,&v)?;
                let mut enumerated=Reference::new(&r,&u,&v);let mut observed=[0usize;4];
                for (slot,owner) in OWNERS.iter().copied().enumerate(){
                    let seen=plan.daa().visit_header_terms(owner as u64,|term|{
                        let local=project_term(term,owner)?;
                        let rebased=rebased_term(local,slot)?;
                        observed[slot]+=1;enumerated.add(rebased)
                    })?;
                    check_header_counts(owner,seen)?;
                    for field in 0..4 {
                        let mut bad=seen;
                        match field {0=>bad.emitted+=1,1=>bad.omitted_worktree+=1,2=>bad.omitted_mature_a4+=1,_=>bad.omitted_short_a4+=1}
                        if check_header_counts(owner,bad).is_ok(){return Err("grouped-V isolated header census mutant accepted".into());}
                    }
                }
                if observed!=[FULL_TERMS,FULL_TERMS,SHORT_TERMS,FULL_TERMS] || analytic!=enumerated.c {
                    return Err("grouped-V analytic/enumerated projection mismatch".into());
                }
                let mut changed=group_by_copy.clone();changed[0]=1;
                if validate_group_map(plan,&OWNERS,&changed).is_ok(){return Err("grouped-V class/mapping mutant accepted".into());}
                for wrong_owners in [[2048,1,3072,4095],[1,2048,3072,3072]] {
                    if validate_group_map(plan,&wrong_owners,&GROUPS).is_ok(){
                        return Err("grouped-V reordered/duplicate physical owner mutant accepted".into());
                    }
                }
                let mut endpoint=Term{row:2*ROW_WIDTH,gate:crate::gkr::Gate{left:2*WIDTH,right:WIDTH,c0:Fr::zero(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}};
                if project_term(endpoint.clone(),1).is_ok(){return Err("grouped-V endpoint row mutant accepted".into());}
                endpoint.row=ROW_WIDTH;endpoint.gate.left=2*WIDTH;
                if project_term(endpoint,1).is_ok(){return Err("grouped-V endpoint input mutant accepted".into());}
                Ok(())
            }

            #[test]
            fn native_role1_grouped_v_projection_controls(){
                with_plan(|_,plan,_|run_projection_controls(plan).unwrap());
            }

            struct ArmResult {
                encoded:Vec<u8>,
                proof:gkr::GkrProof,
                claim:InputClaim,
                transcript:Transcript,
                stats:Option<stream::GroupedVStats>,
                boolean_stats:Option<stream::BooleanUPreweightStats>,
                loads:usize,
                loads_by_copy:[usize;4],
                term_callbacks:usize,
                term_callbacks_by_copy:[usize;4],
                read_bytes:u64,
                timing:serde_json::Value,
                marks:Vec<stream::TestPhaseMark>,
                mle_nonzero_padding:usize,
            }

            fn run_arm(plan:&NativePrefixAuthPlan<'_>,source:&PackedFile,held:&mut File,admission:&stream::GroupedVAdmission,grouped:bool,boolean_u:bool)
                ->Result<ArmResult,String>{
                let mut producer=Transcript::new(DOMAIN);
                let bind_calls=Cell::new(0usize);
                let loads=Cell::new(0usize);let mut loads_by_copy=[0usize;4];let mut term_counts=[0usize;4];
                source.reset_io_metrics();
                let mut load=|copy:usize| -> Result<Vec<Fr>,String>{
                    let owner=owner_slot(copy)?;
                    loads_by_copy[copy]=loads_by_copy[copy].checked_add(1).ok_or("grouped-V owner load overflow")?;
                    read_owner(source,owner,&loads)
                };
                let mut visit=|copy:usize,sink:&mut dyn FnMut(Term)->Result<(),String>| -> Result<(),String>{
                    let owner=owner_slot(copy)?;
                    if boolean_u && term_counts[copy]!=0 {
                        return Err("Boolean-U native relation callback replayed after baseline".into());
                    }
                    let observed=plan.daa().visit_header_terms(owner as u64,|term|{
                        let local=project_term(term,owner)?;term_counts[copy]=term_counts[copy].checked_add(1).ok_or("grouped-V term count overflow")?;
                        sink(local)
                    })?;
                    check_header_counts(owner,observed)?;
                    Ok(())
                };
                let producer_started=Instant::now();stream::begin_phase_trace_for_test();
                let (proof,producer_claim,stats,boolean_stats)=if boolean_u {
                    if !grouped{return Err("Boolean-U requires grouped-V admission".into());}
                    let (proof,claim,stats,boolean_stats)=stream::prove_with_boolean_u_grouped_v_for_test(20,2,19,0,&[19],Some(0),admission,
                        &mut load,&mut producer,|t|{bind_calls.set(bind_calls.get()+1);projected_bind(plan,t).unwrap()},
                        &mut visit,|r,u,v|projected_coefficients(plan,r,u,v))?;
                    (proof,claim,Some(stats),Some(boolean_stats))
                } else if grouped {
                    let (proof,claim,stats)=stream::prove_with_direct_u_grouped_v_for_test(20,2,19,0,&[19],Some(0),admission,
                        &mut load,&mut producer,|t|{bind_calls.set(bind_calls.get()+1);projected_bind(plan,t).unwrap()},
                        &mut visit,|r,u,v|projected_coefficients(plan,r,u,v))?;
                    (proof,claim,Some(stats),None)
                } else {
                    let (proof,claim)=stream::prove_with_direct_u_prefix_for_test(20,2,19,0,&[19],Some(0),
                        &mut load,&mut producer,|t|{bind_calls.set(bind_calls.get()+1);projected_bind(plan,t).unwrap()},
                        &mut visit,|r,u,v|projected_coefficients(plan,r,u,v))?;
                    (proof,claim,None,None)
                };
                let producer_ms=timing_ms(producer_started);let marks=stream::take_phase_trace_for_test();
                if bind_calls.get()!=1{return Err("grouped-V statement must bind once after baseline admission".into());}
                let expected_marks=if grouped {[
                    "baseline_start","baseline_done","u_cache_streamed","u_anchor_done","u_local_done","u_handoff_done",
                    "v_cache_grouped","v_anchor_done","v_local_done","v_handoff_done","terminal_wiring_done","line_start","line_done"]
                } else {[
                    "baseline_start","baseline_done","u_cache_streamed","u_anchor_done","u_local_done","u_handoff_done",
                    "v_cache_streamed","v_anchor_done","v_local_done","v_handoff_done","terminal_wiring_done","line_start","line_done"]};
                if marks.len()!=expected_marks.len() || marks.iter().zip(expected_marks).any(|(mark,name)|mark.name!=*name) {
                    return Err("grouped-V phase marker order/count".into());
                }
                let sweeps=if boolean_u{1}else if grouped{23}else{45};
                let loads_per_owner=if boolean_u{25}else if grouped{26}else{45};
                if loads_by_copy.iter().any(|n|*n!=loads_per_owner) || loads.get()!=loads_per_owner*4 || term_counts!=[
                    FULL_TERMS*sweeps,FULL_TERMS*sweeps,SHORT_TERMS*sweeps,FULL_TERMS*sweeps] {
                    return Err("grouped-V producer load/term visitor recurrence".into());
                }
                let read_bytes=source.io_metrics_snapshot().read_bytes;
                if read_bytes!=(loads_per_owner*4) as u64*OWNER_BYTES as u64 {return Err("grouped-V packed source read extent".into());}
                let codec_started=Instant::now();let encoded=gkr::encode_proof(&proof).map_err(|e|e.to_string())?;
                let expected_bytes=157usize.checked_mul(Fr::zero().compressed_size()).ok_or("grouped-V codec extent overflow")?;
                if expected_bytes!=5024 || encoded.len()!=expected_bytes{return Err("grouped-V proof encoded extent".into());}
                let decoded=gkr::decode_dimensions(&[22],&encoded).map_err(|e|e.to_string())?;
                if gkr::encode_proof(&decoded).map_err(|e|e.to_string())?!=encoded || decoded.layers.len()!=1
                    || decoded.layers[0].rounds.len()!=44 || decoded.layers[0].line_coefficients.len()!=23 {
                    return Err("grouped-V proof canonical shape/roundtrip".into());
                }
                let codec_ms=timing_ms(codec_started);
                let verify_started=Instant::now();let (claim,mut verifier)=verify_projected(plan,&decoded).map_err(|e|e.to_string())?;
                let verify_ms=timing_ms(verify_started);
                if claim!=producer_claim || producer.challenges()!=verifier.challenges()
                    || producer.raw_queries()!=verifier.raw_queries() || producer.bytes_absorbed()!=verifier.bytes_absorbed()
                    || producer.challenge_scalar(b"role1-grouped-v-continuation")
                    !=verifier.challenge_scalar(b"role1-grouped-v-continuation") {
                    return Err("grouped-V producer/verifier claim or transcript".into());
                }
                let mle_started=Instant::now();let (mle,padding_nonzero)=projected_mle(held,&claim.point)?;
                let mle_ms=timing_ms(mle_started);
                if mle!=claim.value || padding_nonzero!=93_036 {return Err("grouped-V projected held-witness MLE".into());}
                let mut mutant=decoded.clone();mutant.layers[0].rounds[0][0]+=Fr::one();
                if verify_projected(plan,&mutant).is_ok(){return Err("grouped-V mutated proof round accepted".into());}
                let timing=serde_json::json!({"producer":producer_ms,"codec":codec_ms,"independent_verify":verify_ms,"owner_mle":mle_ms});
                Ok(ArmResult{encoded,proof:decoded,claim,transcript:producer,stats,boolean_stats,loads:loads.get(),loads_by_copy,
                    term_callbacks:term_counts.iter().sum(),term_callbacks_by_copy:term_counts,read_bytes,timing,marks,mle_nonzero_padding:padding_nonzero})
            }

            fn write_arm_event(kind:&str,arm:&str,proof_bytes:Option<usize>,loads:Option<usize>){
                let value=if kind=="BEGIN" {serde_json::json!({"arm":arm})}
                    else {serde_json::json!({"arm":arm,"proof_bytes":proof_bytes.unwrap(),"producer_owner_loads":loads.unwrap()})};
                println!("NIPOPOW_ROLE1_GROUPED_V_{kind} {}",value);let _=std::io::stdout().flush();
            }

            fn write_boolean_arm_event(kind:&str,arm:&str,proof_bytes:Option<usize>,loads:Option<usize>){
                let value=if kind=="BEGIN" {serde_json::json!({"arm":arm})}
                    else {serde_json::json!({"arm":arm,"proof_bytes":proof_bytes.unwrap(),"producer_owner_loads":loads.unwrap()})};
                println!("NIPOPOW_ROLE1_BOOLEAN_U_{kind} {}",value);let _=std::io::stdout().flush();
            }
            fn write_boolean_capture(dir:&Path,proofs:&[(String,Vec<u8>)],report:&serde_json::Value)->Result<(),String>{
                if proofs.len()!=2 || proofs[0].0!="boolean-u-reference.gkr" || proofs[1].0!="boolean-u-optimized.gkr"
                    || proofs.iter().any(|(_,bytes)|bytes.len()!=5024) {
                    return Err("Boolean-U closed proof artifact roster".into());
                }
                let bytes=serde_json::to_vec_pretty(report).map_err(|e|e.to_string())?;
                if bytes.len()>65536{return Err("Boolean-U report artifact cap".into());}
                std::fs::create_dir(dir).map_err(|e|e.to_string())?;
                for (name,bytes) in proofs {
                    let mut file=OpenOptions::new().write(true).create_new(true).open(dir.join(name)).map_err(|e|e.to_string())?;
                    file.write_all(bytes).map_err(|e|e.to_string())?;file.sync_all().map_err(|e|e.to_string())?;
                }
                let mut file=OpenOptions::new().write(true).create_new(true).open(dir.join("role1-boolean-u-result.json")).map_err(|e|e.to_string())?;
                file.write_all(&bytes).map_err(|e|e.to_string())?;file.sync_all().map_err(|e|e.to_string())?;Ok(())
            }

            #[test]
            #[ignore="bounded four-owner grouped-V role1 calibration; no native32 or client claim"]
            fn native_role1_grouped_v_cost_calibration_bounded()->Result<(),String>{
                run_calibration(false)
            }
            #[test]
            #[ignore="bounded Boolean-U plus grouped-V four-owner calibration; no native32 or client claim"]
            fn native_role1_boolean_u_cost_calibration_bounded()->Result<(),String>{
                run_calibration(true)
            }
            fn run_calibration(boolean_experiment:bool)->Result<(),String>{
                let (source,mut held,witness_identity)=useq_admit().unwrap();
                let output=capture_directory().unwrap();
                let mut arm_json=serde_json::Map::new();let mut proof_files=Vec::with_capacity(2);let mut saved:Vec<ArmResult>=Vec::with_capacity(2);
                let mut padding_nonzero=0usize;
                let mut report_out:Option<serde_json::Value>=None;
                with_plan(|parent,plan,candidate|->Result<(),String>{
                    if (candidate.n,plan.descriptors()[1].input_log,plan.descriptors()[1].row_log)!=(3073,32,31){
                        return Err("grouped-V source plan native shape".into());
                    }
                    let mut group_map=Vec::with_capacity(4);let mut owner_terms=Vec::with_capacity(4);
                    for owner in OWNERS {
                        let class=plan.daa().owner_class(owner as u64)?;
                        if class!=expected_class(owner){return Err("grouped-V physical owner class changed".into());}
                        group_map.push(if matches!(class,OwnerClass::Short(_)){1}else{0});owner_terms.push(terms_for(owner));
                    }
                    if group_map.as_slice()!=GROUPS.as_slice() || owner_terms.as_slice()!=[FULL_TERMS,FULL_TERMS,SHORT_TERMS,FULL_TERMS].as_slice(){
                        return Err("grouped-V plan-derived admission mismatch".into());
                    }
                    validate_group_map(plan,&OWNERS,&group_map)?;
                    validate_group_census(&OWNERS,&group_map,&owner_terms,&GROUP_TERMS)?;
                    let admission=stream::GroupedVAdmission::try_new(2,&group_map,&GROUP_TERMS)?;
                    run_projection_controls(plan)?;
                    for owner in OWNERS {
                        let preflight_loads=Cell::new(0usize);
                        let values=read_owner(&source,owner,&preflight_loads)?;
                        let bytes=held_slice(&mut held,(owner*OWNER_BYTES) as u64);
                        require_owner_encoding(&values,&bytes)?;
                        let mut wrong=bytes.clone();wrong[0]^=1;
                        if require_owner_encoding(&values,&wrong).is_ok(){return Err("grouped-V isolated source-bit mutant accepted".into());}
                        if owner==4095 {
                            if bytes.iter().filter(|byte|**byte!=0).count()!=93_036 {
                                return Err("grouped-V real padding census".into());
                            }
                            wrong.fill(0);
                            if require_owner_encoding(&values,&wrong).is_ok(){return Err("grouped-V zero padding mutant accepted".into());}
                        }
                    }
                    for arm in ["reference",if boolean_experiment{"boolean"}else{"grouped"}]{
                        if boolean_experiment{write_boolean_arm_event("BEGIN",arm,None,None);}
                        else{write_arm_event("BEGIN",arm,None,None);}
                        let result=run_arm(plan,&source,&mut held,&admission,boolean_experiment || arm=="grouped",boolean_experiment && arm=="boolean")?;
                        if boolean_experiment{write_boolean_arm_event("COMPLETE",arm,Some(result.encoded.len()),Some(result.loads));}
                        else{write_arm_event("COMPLETE",arm,Some(result.encoded.len()),Some(result.loads));}
                        padding_nonzero=result.mle_nonzero_padding;
                        let arm_sha=screen_hex(&crate::native_prefix_auth_plan::role0_sha256(&result.encoded)?);
                        if boolean_experiment && arm_sha!="C363C2ED3DB6D850794231830ED2586282D7FE2859B25D800E09801CE23CBCAF" {
                            return Err("Boolean-U proof differs from frozen source-6 baseline".into());
                        }
                        let arm_row=serde_json::json!({
                            "proof_bytes":result.encoded.len(),"proof_sha256":arm_sha,
                            "producer_owner_loads":result.loads,"owner_loads_by_copy":result.loads_by_copy,
                            "term_callbacks":result.term_callbacks,"term_callbacks_by_copy":result.term_callbacks_by_copy,
                            "packed_read_bytes":result.read_bytes,"claim_point_width":result.claim.point.len(),
                            "claim_value_hex":encoded_fr(&result.claim.value),"timing_ms":result.timing,
                            "phase_marks":report_phase_marks(&result.marks),
                            "canonical_codec_roundtrip":true,"independent_verify":true,
                            "claim_matches_producer":true,"continuation_matches":true,"owner_local_mle_matches":true
                        });
                        arm_json.insert(arm.to_owned(),arm_row);
                        let proof_name=(if boolean_experiment {
                            if arm=="reference"{"boolean-u-reference.gkr"}else{"boolean-u-optimized.gkr"}
                        }else if arm=="reference" {"grouped-v-reference.gkr"} else {"grouped-v-optimized.gkr"}).to_owned();
                        proof_files.push((proof_name,result.encoded.clone()));
                        saved.push(result);
                    }
                    if saved.len()!=2 || saved[0].encoded!=saved[1].encoded || saved[0].claim!=saved[1].claim {
                        return Err("grouped-V/reference proof or claim differs".into());
                    }
                    let mut reference_continuation=saved[0].transcript.clone();
                    let mut grouped_continuation=saved[1].transcript.clone();
                    if reference_continuation.challenges()!=grouped_continuation.challenges()
                        || reference_continuation.raw_queries()!=grouped_continuation.raw_queries()
                        || reference_continuation.bytes_absorbed()!=grouped_continuation.bytes_absorbed()
                        || reference_continuation.challenge_scalar(b"role1-grouped-v-transcript-equality")
                            !=grouped_continuation.challenge_scalar(b"role1-grouped-v-transcript-equality")
                        || reference_continuation.challenge_scalar(b"role1-grouped-v-continuation")
                        !=grouped_continuation.challenge_scalar(b"role1-grouped-v-continuation") {
                        return Err("grouped-V/reference transcript or continuation differs".into());
                    }
                    let stats=saved[1].stats.as_ref().ok_or("grouped-V stats missing from optimized arm")?;
                    let term_size=std::mem::size_of::<Term>();
                    if stats.group_count!=2 || stats.group_owner_counts.as_slice()!=GROUP_OWNERS.as_slice() || stats.group_term_counts.as_slice()!=GROUP_TERMS.as_slice()
                        || stats.baseline_term_callbacks!=1_578_052 || stats.template_term_count!=784_930
                        || stats.bank_term_callbacks!=784_930 || stats.handoff_term_callbacks!=0
                        || stats.local_rounds!=20 || stats.owner_handoff_count!=4
                        || stats.template_capacity_bytes<stats.template_term_count.checked_mul(term_size).ok_or("template capacity overflow")?
                        || stats.grouped_state_peak_capacity_bytes<stats.template_capacity_bytes
                        || stats.grouped_state_peak_capacity_bytes>STATE_LIMIT
                        || stats.group_weight_sums.len()!=2 || stats.group_d_local_contributions.len()!=2
                        || stats.group_weight_sums.iter().any(|x|*x==Fr::one())
                        || stats.group_d_local_contributions.iter().all(|x|x.is_zero()) {
                        return Err("grouped-V measured census/capacity/algebra statistics".into());
                    }
                    let mut changed_candidate=candidate.clone();changed_candidate.tip[0]^=1;
                    let changed_plan=NativePrefixAuthPlan::compile(parent,Selection::s12(),changed_candidate)?;
                    for result in &saved {if verify_projected(&changed_plan,&result.proof).is_ok(){return Err("same proof accepted under changed tip".into());}}
                    let ref_mle=saved[0].claim.point.clone();
                    if ref_mle.len()!=22 || ref_mle.iter().any(|x|*x==Fr::zero()||*x==Fr::one())
                        || padding_nonzero!=93_036 || saved[0].mle_nonzero_padding!=saved[1].mle_nonzero_padding {
                        return Err("grouped-V non-Boolean claim/padding witness".into());
                    }
                    let group_weight_hex:Vec<String>=stats.group_weight_sums.iter().map(encoded_fr).collect();
                    let group_d_hex:Vec<String>=stats.group_d_local_contributions.iter().map(encoded_fr).collect();
                    let grouped_v=serde_json::json!({
                        "group_count":stats.group_count,"group_owner_counts":stats.group_owner_counts,
                        "group_term_counts":stats.group_term_counts,"baseline_term_callbacks":stats.baseline_term_callbacks,
                        "template_term_count":stats.template_term_count,"term_size_bytes":term_size,
                        "template_capacity_bytes":stats.template_capacity_bytes,"bank_term_callbacks":stats.bank_term_callbacks,
                        "handoff_term_callbacks":stats.handoff_term_callbacks,
                        "grouped_state_peak_capacity_bytes":stats.grouped_state_peak_capacity_bytes,
                        "local_rounds":stats.local_rounds,"owner_handoff_count":stats.owner_handoff_count,
                        "baseline_elapsed_ns":stats.baseline_elapsed_ns,"bank_build_elapsed_ns":stats.bank_build_elapsed_ns,
                        "local_v_elapsed_ns":stats.local_v_elapsed_ns,"owner_handoff_elapsed_ns":stats.owner_handoff_elapsed_ns,
                        "group_weight_sums_hex":group_weight_hex,"group_d_local_contributions_hex":group_d_hex
                    });
                    let proof_hashes:Vec<String>=proof_files.iter().map(|(_,bytes)|
                        screen_hex(&crate::native_prefix_auth_plan::role0_sha256(bytes).unwrap())).collect();
                    let proof_artifacts:Vec<serde_json::Value>=proof_files.iter().zip(proof_hashes.iter()).map(|((file,bytes),sha)|
                        serde_json::json!({"file":file,"bytes":bytes.len(),"sha256":sha})).collect();
                    let scope=serde_json::json!({"role":1,"native_n":3073,"local_input_log":20,"local_row_log":19,"copy_bits":2,
                        "projected_input_log":22,"projected_row_log":21,"physical_owners":OWNERS,
                        "owner_classes":["initial","m1","short-m2","padding"],"group_by_copy":GROUPS,
                        "native32_claim":false,"common_opening":false,"all_seven_claims":false,"full_history":false,
                        "light_client":false,"no_fork":false,"eip":false,"oracle":false,"production":false,
                        "key_admission":false,"setup_or_recommit":false,"commitment_claim":false,"dory_opening":false});
                    let admission_json=serde_json::json!({"prebind_pass":true,"group_count":2,"group_owner_counts":GROUP_OWNERS,
                        "group_term_counts":GROUP_TERMS,"expected_owner_term_counts":[FULL_TERMS,FULL_TERMS,SHORT_TERMS,FULL_TERMS],
                        "baseline_term_callbacks":stats.baseline_term_callbacks,"template_term_count":stats.template_term_count,
                        "term_size_bytes":term_size,"template_capacity_bytes":stats.template_capacity_bytes,
                        "state_capacity_limit_bytes":STATE_LIMIT,"state_peak_capacity_bytes":stats.grouped_state_peak_capacity_bytes,
                        "padding_nonzero_bytes":padding_nonzero});
                    let proof_shape=serde_json::json!({"input_bits":22,"row_bits":21,"rounds":44,"line_coefficients":23,
                        "scalar_count":157,"proof_bytes":5024});
                    let equality=serde_json::json!({"proof_bytes_equal":true,"claim_equal":true,"transcript_equal":true,"continuation_equal":true,
                        "independent_verify_both":true,"mle_equal":true,"analytic_enumerated_coefficients_equal":true,
                        "non_boolean_coordinates":true,"nonzero_group_d_contribution":true,
                        "each_group_weight_sum_not_one":true,"real_padding_nonzero_bytes":true,
                        "changed_tip_rejected_both":true,"mutated_round_rejected_both":true});
                    let artifacts=serde_json::json!({"proofs":proof_artifacts,"result_file":if boolean_experiment{"role1-boolean-u-result.json"}else{"role1-grouped-v-result.json"}});
                    let mut report=serde_json::json!({"schema":if boolean_experiment{"native-prefix-role1-boolean-u-v1"}else{"native-prefix-role1-grouped-v-v1"},
                        "state":if boolean_experiment{"ROLE1_BOOLEAN_U_PASS"}else{"ROLE1_GROUPED_V_PASS"},
                        "scope":scope,"admission":admission_json,"proof_shape":proof_shape,"equality":equality,
                        "arms":arm_json,"grouped_v":grouped_v,"artifacts":artifacts});
                    if boolean_experiment {
                        let bs=saved[1].boolean_stats.as_ref().ok_or("Boolean-U statistics absent")?;
                        let u_start=saved[1].marks.iter().find(|mark|mark.name=="u_anchor_done").ok_or("Boolean-U start phase absent")?.elapsed_ns;
                        let u_end=saved[1].marks.iter().find(|mark|mark.name=="u_handoff_done").ok_or("Boolean-U end phase absent")?.elapsed_ns;
                        let u_interval=u_end.checked_sub(u_start).ok_or("Boolean-U phase time order")?;
                        let u_parts=[bs.u_prefix_preweight_elapsed_ns,bs.u_owner_selection_elapsed_ns,bs.u_x_fold_elapsed_ns];
                        let u_parts_total=u_parts.iter().try_fold(0u64,|sum,value|sum.checked_add(*value))
                            .ok_or("Boolean-U disjoint timing sum overflow")?;
                        if u_parts.iter().any(|elapsed|u128::from(*elapsed)>u_interval) || u128::from(u_parts_total)>u_interval {
                            return Err("Boolean-U disjoint timing spans exceed measured U interval".into());
                        }
                        if bs.prefix_builds!=21 || bs.shared_term_iterations!=16_483_530 || bs.owner_term_selections!=33_139_092
                            || bs.boolean_checked_loads!=100 || bs.boolean_checked_fields!=104_857_600
                            || !bs.zero_anchor_sweep_skipped || bs.preweight_entry_size_bytes!=144
                            || bs.preweight_peak_capacity_bytes<784_930usize.checked_mul(bs.preweight_entry_size_bytes).ok_or("Boolean-U preweight capacity overflow")?
                            || bs.u_state_peak_capacity_bytes<bs.preweight_peak_capacity_bytes || bs.u_state_peak_capacity_bytes>STATE_LIMIT
                            || bs.u_preflight_capacity_bound_bytes>STATE_LIMIT
                            || bs.u_state_peak_capacity_bytes>bs.u_preflight_capacity_bound_bytes
                            || bs.u_phase_peak_capacity_bytes.iter().any(|bytes|*bytes>STATE_LIMIT)
                            || bs.u_phase_peak_capacity_bytes.iter().copied().max()!=Some(bs.u_state_peak_capacity_bytes) {
                            return Err("Boolean-U measured recurrence/capacity statistics".into());
                        }
                        if saved[0].boolean_stats.is_some() || saved[0].loads!=104 || saved[0].term_callbacks!=36_295_196
                            || saved[1].loads!=100 || saved[1].term_callbacks!=1_578_052 {
                            return Err("Boolean-U reference/optimized producer recurrence".into());
                        }
                        report["boolean_u"]=serde_json::json!({"prefix_builds":bs.prefix_builds,
                            "shared_term_iterations":bs.shared_term_iterations,"owner_term_selections":bs.owner_term_selections,
                            "boolean_checked_loads":bs.boolean_checked_loads,"boolean_checked_fields":bs.boolean_checked_fields,
                            "zero_anchor_sweep_skipped":bs.zero_anchor_sweep_skipped,"preweight_entry_size_bytes":bs.preweight_entry_size_bytes,
                            "preweight_peak_capacity_bytes":bs.preweight_peak_capacity_bytes,"u_state_peak_capacity_bytes":bs.u_state_peak_capacity_bytes,
                            "u_preflight_capacity_bound_bytes":bs.u_preflight_capacity_bound_bytes,"u_phase_peak_capacity_bytes":bs.u_phase_peak_capacity_bytes,
                            "u_prefix_preweight_elapsed_ns":bs.u_prefix_preweight_elapsed_ns,
                            "u_owner_selection_elapsed_ns":bs.u_owner_selection_elapsed_ns,"u_x_fold_elapsed_ns":bs.u_x_fold_elapsed_ns});
                        report["equality"]["source6_baseline_equal"]=serde_json::json!(true);
                        report["admission"]["state_peak_capacity_bytes"]=serde_json::json!(
                            stats.grouped_state_peak_capacity_bytes.max(bs.u_state_peak_capacity_bytes));
                    }
                    report_out=Some(report);
                    Ok(())
                })?;
                if u0_file_info(&held).unwrap()!=witness_identity{return Err("grouped-V witness identity changed".into());}
                let report=report_out.ok_or("grouped-V closed report was not produced")?;
                if boolean_experiment{write_boolean_capture(&output,&proof_files,&report)?;}
                else{write_grouped_capture(&output,&proof_files,&report).map_err(|e|e.to_string())?;}
                Ok(())
            }
        }
    }
    mod role5_diagnostic {
        use super::*;
        use crate::header_adjacency_layout::HeaderAdjacencyLayout;
        use crate::native_prefix_auth_plan::{NativeRole5DiagnosticContext,NativeRole5Mark,emit_role5_mark};
        use crate::segment_adjacency::linear_for_test as linear;
        use ark_serialize::CanonicalSerialize;

        const REPORT_CAP:usize=32768;
        const METADATA_RESERVATION:usize=1024*1024;
        const RAW_SHA:&str="ABB3D74AE75256CED63110B72C2E0D5EBA1B90B09889E45EA327BDA1C9A640D2";
        const WITNESS_SHA:&str="C1CC1CF72FF539F259A3BDEF756332BA52CB8AFF26C11AB4116D1B2F9D17ED43";
        const WITNESS_BLAKE:&str="725D7B1215E1185C52C1012D9294260612653ACAD53A02429B8EAAFD0F0770C8";

        struct ReportWriter{bytes:Vec<u8>}
        impl Write for ReportWriter{
            fn write(&mut self,data:&[u8])->std::io::Result<usize>{
                let next=self.bytes.len().checked_add(data.len()).ok_or_else(||std::io::Error::other("role5 report overflow"))?;
                if next>REPORT_CAP{return Err(std::io::Error::other("role5 report exceeds32KiB"));}
                self.bytes.extend_from_slice(data);Ok(data.len())
            }
            fn flush(&mut self)->std::io::Result<()>{Ok(())}
        }
        fn report_bytes(value:&serde_json::Value)->Result<Vec<u8>,String>{
            let mut writer=ReportWriter{bytes:Vec::new()};
            writer.bytes.try_reserve_exact(REPORT_CAP).map_err(|e|e.to_string())?;
            if writer.bytes.capacity()!=REPORT_CAP{return Err("role5 report actual capacity".into());}
            serde_json::to_writer(&mut writer,value).map_err(|e|e.to_string())?;Ok(writer.bytes)
        }
        fn ns(start:Instant)->Result<u64,String>{u64::try_from(start.elapsed().as_nanos()).map_err(|_|"role5 duration overflow".into())}
        fn counters(t:&Transcript)->[u64;3]{[t.challenges(),t.raw_queries(),t.bytes_absorbed()]}
        fn io_record(io:crate::packed::PackedIoSnapshot)->Result<serde_json::Value,String>{
            Ok(serde_json::json!({"read_calls":io.read_calls,"read_bytes":io.read_bytes,
                "read_ns":u64::try_from(io.read_ns).map_err(|_|"role5 I/O timer overflow")?,
                "write_calls":io.write_calls,"write_bytes":io.write_bytes,
                "write_ns":u64::try_from(io.write_ns).map_err(|_|"role5 I/O timer overflow")?,
                "sync_calls":io.sync_calls,"sync_ns":u64::try_from(io.sync_ns).map_err(|_|"role5 I/O timer overflow")?}))
        }
        fn fingerprint(t:&Transcript)->([u64;3],Fr){(counters(t),t.clone().challenge_scalar(b"native-role5-transaction-control"))}
        fn mark(stage:&'static str,elapsed_ns:u64)->Result<(),String>{
            emit_role5_mark(NativeRole5Mark{stage,round:None,elapsed_ns})
        }
        fn save(path:&Path,bytes:&[u8],new:bool)->Result<(),String>{
            let mut options=OpenOptions::new();options.write(true);
            if new{options.create_new(true);}else{options.truncate(true);}
            let mut file=options.open(path).map_err(|e|e.to_string())?;
            file.write_all(bytes).map_err(|e|e.to_string())?;file.sync_all().map_err(|e|e.to_string())?;Ok(())
        }
        fn retain_hold(dir:&Path,reason:&str)->Result<(),String>{
            let path=dir.join("result.json.part");
            match std::fs::symlink_metadata(&path){
                Ok(_)=>Ok(()), // A ready .part remains opaque and unadmitted.
                Err(e) if e.kind()==std::io::ErrorKind::NotFound=>{
                    let reason=reason.chars().take(256).collect::<String>();
                    save(&path,&report_bytes(&serde_json::json!({"state":"HOLD","reason":reason}))?,true)
                },Err(e)=>Err(e.to_string()),
            }
        }
        fn export(dir:&Path,proof:&[u8],report:&serde_json::Value)->Result<(),String>{
            let bytes=report_bytes(report)?;
            if proof.len()!=7264{return Err("role5 export proof extent".into());}
            save(&dir.join("role5.gkr.part"),proof,true)?;
            useq_finalize_checkpoint(&dir.join("role5.gkr.part"),&dir.join("role5.gkr"))?;
            // This replaces only our diagnostic progress .part. Neither final
            // destination can be replaced; two-file publication is not atomic.
            save(&dir.join("result.json.part"),&bytes,false)?;
            useq_finalize_checkpoint(&dir.join("result.json.part"),&dir.join("result.json"))
        }
        fn output(sparse_support:bool)->Result<PathBuf,String>{
            use std::os::windows::fs::MetadataExt;
            let name=if sparse_support{"NIPOPOW_NATIVE_ROLE5_SUPPORT_CAPTURE_DIR"}else{"NIPOPOW_NATIVE_ROLE5_LINEAR_CAPTURE_DIR"};
            let path=PathBuf::from(std::env::var_os(name).ok_or("role5 output env absent")?);
            if !path.is_absolute(){return Err("role5 output absolute path".into());}
            let parent=path.parent().ok_or("role5 output parent")?;
            let md=std::fs::symlink_metadata(parent).map_err(|e|e.to_string())?;
            if !md.is_dir()||md.file_attributes()&0x400!=0{return Err("role5 output parent regular directory".into());}
            match std::fs::symlink_metadata(&path){
                Ok(_)=>return Err("role5 output must be fresh".into()),
                Err(e) if e.kind()==std::io::ErrorKind::NotFound=>(),Err(e)=>return Err(e.to_string()),
            }
            std::fs::create_dir(&path).map_err(|e|e.to_string())?;
            save(&path.join("result.json.part"),b"{\"state\":\"HOLD\",\"stage\":\"admission\"}",true)?;Ok(path)
        }

        #[test]
        fn native_role5_linear_capture_and_export_controls(){
            let value=serde_json::json!({"state":"HOLD","reason":"bounded"});
            assert_eq!(serde_json::from_slice::<serde_json::Value>(&report_bytes(&value).unwrap()).unwrap(),value);
            assert!(report_bytes(&serde_json::json!("x".repeat(REPORT_CAP))).is_err());
            let mut writer=ReportWriter{bytes:Vec::new()};
            assert!(writer.write_all(&vec![0;REPORT_CAP+1]).is_err());assert!(writer.bytes.is_empty());
            let base=std::env::temp_dir().join(format!("native-role5-retention-{}-{}",std::process::id(),
                std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
            std::fs::create_dir(&base).unwrap();
            let ready=b"{\"state\":\"ROLE5_LINEAR_DIAGNOSTIC_GKR_PASS\"}";
            save(&base.join("result.json.part"),ready,true).unwrap();
            retain_hold(&base,"caught late failure").unwrap();assert_eq!(std::fs::read(base.join("result.json.part")).unwrap(),ready);
            let existing=b"existing-final";save(&base.join("result.json"),existing,true).unwrap();
            assert!(useq_finalize_checkpoint(&base.join("result.json.part"),&base.join("result.json")).is_err());
            assert_eq!(std::fs::read(base.join("result.json")).unwrap(),existing);
            assert_eq!(std::fs::read(base.join("result.json.part")).unwrap(),ready);
            // Exercise the real two-file exporter failure AFTER it publishes
            // the proof, then the same caught-HOLD retention helper as run().
            assert!(export(&base,&vec![0;7264],&value).is_err());
            let observed_part=std::fs::read(base.join("result.json.part")).unwrap();
            retain_hold(&base,"report collision after proof publication").unwrap();
            assert_eq!(std::fs::read(base.join("role5.gkr")).unwrap(),vec![0;7264]);
            assert_eq!(std::fs::read(base.join("result.json")).unwrap(),existing);
            assert_eq!(std::fs::read(base.join("result.json.part")).unwrap(),observed_part);
            std::fs::remove_file(base.join("role5.gkr")).unwrap();
            std::fs::remove_file(base.join("result.json.part")).unwrap();
            retain_hold(&base,"missing part").unwrap();
            assert_eq!(serde_json::from_slice::<serde_json::Value>(&std::fs::read(base.join("result.json.part")).unwrap()).unwrap()["state"],"HOLD");
            std::fs::remove_file(base.join("result.json.part")).unwrap();std::fs::remove_file(base.join("result.json")).unwrap();
            std::fs::remove_dir(&base).unwrap();
        }

        fn run(dir:&Path,sparse_support:bool)->Result<(),String>{
            let mut raw=pinned_artifact("NIPOPOW_NATIVE_AUTH_FIXTURE",869449,RAW_SHA)?;
            // with_plan rereads the same locked RAW. Drop this byte buffer first;
            // retain its identity and immutable handle throughout the consumer.
            raw.bytes=Vec::new();
            let key=pinned_artifact("NIPOPOW_ROLE4_KEY_PATH",33264,"D11220A1CBB08BE2C84F6B854EC2A932B3FCEC49C217963D079DD8053F7B31B2")?;
            let commitment=pinned_artifact("NIPOPOW_NATIVE_ROLE0_COMMITMENT_PATH",384,"2739A3353D579A7FA0F19B06EFDD26A625CDB80009C65707D8B96E7D8C0C9C90")?;
            let context=NativeRole5DiagnosticContext::admit(&key.bytes,&commitment.bytes)?;
            let path=PathBuf::from(std::env::var_os("NIPOPOW_NATIVE_U_SEQUENCE_WITNESS").ok_or("role5 witness env absent")?);
            if !path.is_absolute(){return Err("role5 witness absolute path".into());}
            let mut held=u0_open_bytes(&path)?;let identity=u0_file_info(&held)?;
            let source=PackedFile::open_with_limit(&path,32,32)?;
            let (encoded,report)=with_plan(|parent,plan,candidate|->Result<(Vec<u8>,serde_json::Value),String>{
                println!();mark("admission_start",0)?;
                source.reset_io_metrics();
                let cap=plan.admit_role5_linear_for_test(&source,&context,&mut held)?;
                let admission_io=source.io_metrics_snapshot();let admission_ns=cap.elapsed_ns()?;
                if admission_io.read_calls!=4096||admission_io.read_bytes!=536870912{
                    return Err("role5 packed admission full comparison census".into());
                }
                mark("admission_complete",admission_ns)?;
                let foreign=HeaderAdjacencyLayout::compile(3073,12,[0;32],candidate.tip)?;
                if cap.require_layout(&foreign).is_ok(){return Err("role5 foreign layout capability accepted".into());}drop(foreign);
                let descriptor=cap.descriptor()?;let mut generic=context.transcript();let original=fingerprint(&generic);
                if linear::prove(&descriptor,1usize<<32,0,|_|panic!("generic native callback must not load"),&mut generic).is_ok()
                    ||fingerprint(&generic)!=original{return Err("role5 generic native callback admission".into());}
                if sparse_support{
                    let native=HeaderAdjacencyLayout::compile(3073,12,[0;32],candidate.tip)?;
                    let mut generic=context.transcript();let before=fingerprint(&generic);
                    let error=linear::prove_sparse_support_n3_for_test(&native,1usize<<32,0,
                        |_|panic!("support callback seam must refuse native32 before load"),&mut generic).unwrap_err();
                    if error!="linear diagnostic requires canonical N3/N4 layout"||fingerprint(&generic)!=before{
                        return Err("role5 native support callback refusal".into());
                    }
                }
                let mut late=context.transcript();late.challenge_scalar(b"before-role5-producer");let original=fingerprint(&late);
                let rejected=if sparse_support{linear::prove_native_role5_sparse_support_for_test(&cap,&mut late,0).is_err()}
                    else{linear::prove_native_role5_for_test(&cap,&mut late,0).is_err()};
                if !rejected||fingerprint(&late)!=original{
                    return Err("role5 late binder changed caller".into());
                }
                let mut overflow=context.transcript();let original=fingerprint(&overflow);
                let rejected=if sparse_support{linear::prove_native_role5_sparse_support_for_test(&cap,&mut overflow,usize::MAX).is_err()}
                    else{linear::prove_native_role5_for_test(&cap,&mut overflow,usize::MAX).is_err()};
                if !rejected||fingerprint(&overflow)!=original{
                    return Err("role5 retained budget overflow changed caller".into());
                }
                if source.io_metrics_snapshot().read_calls!=4096{return Err("role5 preflight faults performed producer reads".into());}
                let prepared=cap.prepare_binding(&context.transcript())?;
                let direct=plan.prepare_role5_binding_for_test(&context.transcript(),&context)?;
                if fingerprint(&prepared)!=fingerprint(&direct){return Err("role5 prepared binding differs".into());}
                let retained=key.bytes.capacity().checked_add(commitment.bytes.capacity())
                    .and_then(|x|x.checked_add(4*std::mem::size_of::<File>()))
                    .and_then(|x|x.checked_add(std::mem::size_of::<PackedFile>()))
                    .and_then(|x|x.checked_add(4*std::mem::size_of::<U0FileInfo>()))
                    .and_then(|x|x.checked_add(METADATA_RESERVATION)).ok_or("role5 caller retained overflow")?;
                let fixed=cap.fixed_retained_capacity_bytes()?;
                let total_retained=fixed.checked_add(retained).ok_or("role5 total retained overflow")?;
                let mut producer=context.transcript();source.reset_io_metrics();let began=Instant::now();
                let (proof,producer_claim,stats,support)=if sparse_support{
                    let (proof,claim,stats,support)=linear::prove_native_role5_sparse_support_for_test(&cap,&mut producer,retained)?;
                    (proof,claim,stats,Some(support))
                }else{
                    let (proof,claim,stats)=linear::prove_native_role5_for_test(&cap,&mut producer,retained)?;
                    (proof,claim,stats,None)
                };
                let proof_ns=ns(began)?;let producer_io=source.io_metrics_snapshot();
                let support_bytes=if let Some(s)=&support{
                    if s.chunks_per_owner!=16||s.parent_chunk_mask!=256||s.digest_chunk_mask!=1024
                        ||s.support_chunks!=[3074,3073]||s.low_round_read_calls!=[49184,49168]
                        ||s.low_round_skipped_chunks!=[999392,999408]||s.control_capacity_bytes!=256{
                        return Err("role5 native structural support census/inventory".into());
                    }s.control_capacity_bytes
                }else{0};
                let expected_reads=if sparse_support{[65536,114720,114704,65536]}else{[65536,1114112,1114112,65536]};
                let scoped_retained=total_retained.checked_add(support_bytes).ok_or("role5 support retained overflow")?;
                if stats.read_calls!=expected_reads
                    ||stats.reconstructed_fields!=stats.read_calls.map(|x|x*65536)
                    ||stats.high_fold_coordinates!=[16,16]||stats.initial_padding_chunks!=16368
                    ||stats.line_input_fields!=1usize<<32||stats.retained_capacity_bytes!=scoped_retained
                    ||stats.preflight_bound_bytes!=17220672usize.checked_add(scoped_retained).ok_or("role5 expected preflight overflow")?
                    ||stats.scoped_limit_bytes!=536870912||stats.helper_bounds_measured
                    ||producer_io.read_calls!=if sparse_support{360496}else{2359296}
                    ||producer_io.read_bytes!=if sparse_support{2953183232}else{19327352832}{
                    return Err("role5 native full linear census/resource model".into());
                }
                let phases=cap.marks_for_report()?;
                let began=Instant::now();let encoded=gkr::encode_proof(&proof)?;
                let codec_bytes=227usize.checked_mul(Fr::zero().compressed_size()).ok_or("role5 codec extent overflow")?;
                let decoded=gkr::decode_dimensions(&[32],&encoded)?;
                if codec_bytes!=7264||encoded.len()!=codec_bytes||encoded.capacity()>16384||gkr::encode_proof(&decoded)?!=encoded
                    ||decoded.layers.len()!=1||decoded.layers[0].rounds.len()!=64
                    ||decoded.layers[0].rounds.iter().any(|p|p.len()!=3)||decoded.layers[0].line_coefficients.len()!=33{
                    return Err("role5 canonical227Fr proof".into());
                }
                let codec_ns=ns(began)?;let began=Instant::now();
                let (claim,verifier)=plan.verify_role5_for_test(&decoded,&context)?;let verify_ns=ns(began)?;
                if claim!=producer_claim||claim.point.len()!=32||counters(&producer)!=counters(&verifier)||producer.challenges()!=86{
                    return Err("role5 independent claim/transcript counters".into());
                }
                let continuation=producer.clone().challenge_scalar(b"native-role5-linear-diagnostic-continuation");
                if continuation!=verifier.clone().challenge_scalar(b"native-role5-linear-diagnostic-continuation"){
                    return Err("role5 cloned continuation".into());
                }
                source.reset_io_metrics();let began=Instant::now();cap.check_source_mle(&claim)?;
                let mle_ns=ns(began)?;let mle_io=source.io_metrics_snapshot();
                let began=Instant::now();let mut changed=candidate.clone();changed.tip[0]^=1;
                let changed_plan=NativePrefixAuthPlan::compile(parent,Selection::s12(),changed)?;
                if changed_plan.verify_role5_for_test(&decoded,&context).is_ok(){return Err("role5 changed tip accepted".into());}
                drop(changed_plan);
                let mut mutant=decoded.clone();mutant.layers[0].rounds[0][0]+=Fr::one();
                if plan.verify_role5_for_test(&mutant,&context).is_ok(){return Err("role5 changed round accepted".into());}drop(mutant);
                for fault in 0..8{if plan.verify_role5_fault_for_test(&decoded,&context,fault).is_ok(){
                    return Err(format!("role5 isolated binding fault accepted:{fault}"));
                }}
                let negative_ns=ns(began)?;
                if u0_file_info(&held)?!=identity||u0_file_info(&raw.file)?!=raw.identity
                    ||u0_file_info(&key.file)?!=key.identity||u0_file_info(&commitment.file)?!=commitment.identity{
                    return Err("role5 final held input custody".into());
                }
                mark("consumers_complete",cap.elapsed_ns()?)?;
                let scope=serde_json::json!({"native_n":3073,"padded_owners":4096,"role":5,"input_log":32,"output_row_log":21,
                    "output_width":2097152,"local_input_log":20,"local_row_log":9,"id_bits":256,"chunk_bits":16,"term_count":786944,
                    "common_opening":false,"all_seven_claims":false,"full_history":false,"light_client":false,"production":false});
                let admission=serde_json::json!({"setup_id":screen_hex(&context.setup_id_for_report()),
                    "verifier_key_sha256":screen_hex(&context.key_sha256_for_report()),"commitment_sha256":screen_hex(&context.commitment_sha256_for_report()),
                    "key_bytes":33264,"commitment_bytes":384,"generated_test_key_admission":true,"commitment_canonical":true,
                    "witness_sha256":WITNESS_SHA,"witness_blake2b256":WITNESS_BLAKE,"witness_bytes":536870912,
                    "compared_owners":4096,"reference_read_bytes":536870912,"json_object_bytes":cap.json_bytes_for_report(),
                    "json_object_limit_bytes":8388608,"binding_overlap_bound_bytes":33554432,
                    "capability_struct_bytes":std::mem::size_of_val(&cap),"capability_retained_bytes":fixed,
                    "caller_retained_bytes":retained,"metadata_reservation_bytes":METADATA_RESERVATION,
                    "external_parent_context_included":false});
                let proof_record=serde_json::json!({"file":"role5.gkr","bytes":encoded.len(),
                    "sha256":screen_hex(&crate::native_prefix_auth_plan::role0_sha256(&encoded)?),"scalars":227,"rounds":64,"line_coefficients":33,
                    "canonical_codec_roundtrip":true,"independent_verify":true,"source_evaluation_crosscheck":true,
                    "changed_tip_rejected":true,"mutated_round_rejected":true,"binding_faults_rejected":8,
                    "generic_native_callback_rejected":true,"foreign_layout_rejected":true,"late_binder_rejected":true,"retained_overflow_rejected":true});
                let claim_record=serde_json::json!({"point_hex":claim.point.iter().map(u0_hex_fr).collect::<Result<Vec<_>,_>>()?,"value_hex":u0_hex_fr(&claim.value)?});
                let transcript=serde_json::json!({"producer":counters(&producer),"verifier":counters(&verifier),
                    "continuation_label":"native-role5-linear-diagnostic-continuation","continuation_hex":u0_hex_fr(&continuation)?});
                let io=serde_json::json!({"admission":io_record(admission_io)?,"producer":io_record(producer_io)?,"source_mle":io_record(mle_io)?});
                let timing=serde_json::json!({"admission":admission_ns,"proof":proof_ns,"codec":codec_ns,"independent_verify":verify_ns,
                    "source_mle":mle_ns,"negative_controls":negative_ns,"total_before_export":cap.elapsed_ns()?});
                let mut report=serde_json::json!({"schema":if sparse_support{"native-prefix-role5-sparse-support-diagnostic-gkr-v1"}else{"native-prefix-role5-linear-diagnostic-gkr-v1"},
                    "state":if sparse_support{"ROLE5_SPARSE_SUPPORT_DIAGNOSTIC_GKR_PASS"}else{"ROLE5_LINEAR_DIAGNOSTIC_GKR_PASS"},
                    "scope":scope,"admission":admission,"proof":proof_record,"claim":claim_record,"transcript":transcript,
                    "linear":stats,"io":io,"phase_marks":phases.as_slice(),"timing_ns":timing});
                if let Some(support)=support{
                    report.as_object_mut().ok_or("role5 report object")?.insert("support".into(),serde_json::to_value(support).map_err(|e|e.to_string())?);
                }
                mark("export_ready",cap.elapsed_ns()?)?;Ok((encoded,report))
            })?;
            export(dir,&encoded,&report)
        }
        #[test]
        #[ignore="one native role5 linear proof; experimental7200s/2GiB/Rayon4 reviewed controller required"]
        fn native_role5_linear_gkr_claim_bounded(){
            let dir=output(false).unwrap();
            if let Err(error)=run(&dir,false){
                // Retain fragments/final files even after a late error. Only
                // the independently settled controller may admit success.
                let retained=retain_hold(&dir,&error);panic!("native role5 HOLD:{error};retention:{retained:?}");
            }
        }
        #[test]
        #[ignore="one native role5 sparse-support proof; reviewed baseline and7200s/2GiB/Rayon4 controller required"]
        fn native_role5_sparse_support_gkr_claim_bounded(){
            let dir=output(true).unwrap();
            if let Err(error)=run(&dir,true){
                let retained=retain_hold(&dir,&error);panic!("native role5 support HOLD:{error};retention:{retained:?}");
            }
        }
    }
    mod role3_diagnostic {
        use super::{pinned_artifact,with_plan,PinnedArtifact};
        use super::super::{input,u0_open_bytes,u0_file_info,useq_finalize_checkpoint};
        use super::super::role3_native_types::{Hex,Scalar,Scalars,Grouped,Boolean};
        use ark_bn254::Fr;
        use ark_ff::{One,Zero};
        use crate::{gkr::{self,GkrError,GkrProof,InputClaim},native_prefix_auth_plan::{NativePrefixAuthPlan,NativeRole3DiagnosticContext,NativeRole3Mark,NativeRole3Memory},
            sparse_stream_roster::{self as stream,GroupedVAdmission,GroupedVStats,BooleanUPreweightStats},packed::PackedFile,
            sparse::Term,transcript::Transcript,work_tree_wiring::eq_index};
        use ark_serialize::CanonicalSerialize;
        use serde::Serialize;
        use std::{cell::Cell,mem::size_of,fs::{File,OpenOptions},io::Write,path::{Path,PathBuf},time::Instant};
        const REPORT_CAP:usize=32768;
        const EXPORT_BOUND:usize=1024*1024;
        const RAW_SHA:&str="ABB3D74AE75256CED63110B72C2E0D5EBA1B90B09889E45EA327BDA1C9A640D2";
        const WITNESS_SHA:&str="C1CC1CF72FF539F259A3BDEF756332BA52CB8AFF26C11AB4116D1B2F9D17ED43";
        const WITNESS_BLAKE:&str="725D7B1215E1185C52C1012D9294260612653ACAD53A02429B8EAAFD0F0770C8";
        const CONTINUATION:&[u8]=b"native-role3-diagnostic-continuation";
        fn add(a:usize,b:usize)->Result<usize,String>{a.checked_add(b).ok_or("native role3 export capacity overflow".into())}
        fn mul(a:usize,b:usize)->Result<usize,String>{a.checked_mul(b).ok_or("native role3 export capacity overflow".into())}
        fn ns(t:Instant)->Result<u64,String>{u64::try_from(t.elapsed().as_nanos()).map_err(|_|"native role3 duration overflow".into())}
        fn counters(t:&Transcript)->[u64;3]{[t.challenges(),t.raw_queries(),t.bytes_absorbed()]}
        fn fingerprint(t:&Transcript)->([u64;3],Fr){(counters(t),t.clone().challenge_scalar(CONTINUATION))}
        fn require(ok:bool,tag:&str)->Result<(),String>{if !ok{return Err(tag.into());}Ok(())}
        struct ReportWriter{bytes:Vec<u8>}
        impl Write for ReportWriter{fn write(&mut self,b:&[u8])->std::io::Result<usize>{
            let next=self.bytes.len().checked_add(b.len()).ok_or_else(||std::io::Error::other("role3 report overflow"))?;
            if next>REPORT_CAP{return Err(std::io::Error::other("role3 report exceeds32768B"));}self.bytes.extend_from_slice(b);Ok(b.len())}
            fn flush(&mut self)->std::io::Result<()>{Ok(())}}
        fn encode_report(value:&impl Serialize)->Result<Vec<u8>,String>{let mut w=ReportWriter{bytes:Vec::new()};
            w.bytes.try_reserve_exact(REPORT_CAP).map_err(|e|e.to_string())?;require(w.bytes.capacity()==REPORT_CAP,"role3 report actual capacity")?;
            serde_json::to_writer(&mut w,value).map_err(|e|e.to_string())?;Ok(w.bytes)}
        #[derive(Serialize)] struct Hold{state:&'static str,stage:&'static str}
        fn save(path:&Path,bytes:&[u8],new:bool)->Result<(),String>{let mut o=OpenOptions::new();o.write(true);
            if new{o.create_new(true);}else{o.truncate(true);}let mut f=o.open(path).map_err(|e|e.to_string())?;
            f.write_all(bytes).and_then(|_|f.sync_all()).map_err(|e|e.to_string())}
        fn retain_hold(dir:&Path)->Result<(),String>{let p=dir.join("result.json.part");match std::fs::symlink_metadata(&p){
            Ok(_)=>Ok(()),Err(e)if e.kind()==std::io::ErrorKind::NotFound=>save(&p,&encode_report(&Hold{state:"HOLD",stage:"failed"})?,true),Err(e)=>Err(e.to_string())}}
        fn export(dir:&Path,packet:&[u8],report:&[u8])->Result<(),String>{require(packet.len()==5696&&report.len()<=REPORT_CAP,"role3 export extent")?;
            save(&dir.join("role3.gkr.part"),packet,true)?;useq_finalize_checkpoint(&dir.join("role3.gkr.part"),&dir.join("role3.gkr"))?;
            save(&dir.join("result.json.part"),report,false)?;useq_finalize_checkpoint(&dir.join("result.json.part"),&dir.join("result.json"))}
        fn output()->Result<PathBuf,String>{use std::os::windows::fs::MetadataExt;
            let p=PathBuf::from(std::env::var_os("NIPOPOW_NATIVE_ROLE3_CAPTURE_DIR").ok_or("role3 capture env absent")?);
            require(p.is_absolute(),"role3 capture path must be absolute")?;let parent=p.parent().ok_or("role3 capture parent")?;
            let md=std::fs::symlink_metadata(parent).map_err(|e|e.to_string())?;require(md.is_dir()&&md.file_attributes()&0x400==0,"role3 capture parent plain directory")?;
            match std::fs::symlink_metadata(&p){Ok(_)=>return Err("role3 capture must be fresh".into()),Err(e)if e.kind()==std::io::ErrorKind::NotFound=>(),Err(e)=>return Err(e.to_string())}
            std::fs::create_dir(&p).map_err(|e|e.to_string())?;save(&p.join("result.json.part"),&encode_report(&Hold{state:"HOLD",stage:"admission"})?,true)?;Ok(p)}
        #[derive(Clone,Copy,Serialize)]struct Io{read_calls:u64,read_bytes:u64,read_ns:u64,write_calls:u64,write_bytes:u64,write_ns:u64,sync_calls:u64,sync_ns:u64}
        impl Io{fn new(x:crate::packed::PackedIoSnapshot)->Result<Self,String>{Ok(Self{read_calls:x.read_calls,read_bytes:x.read_bytes,read_ns:u64::try_from(x.read_ns).map_err(|_|"role3 IO duration")?,
            write_calls:x.write_calls,write_bytes:x.write_bytes,write_ns:u64::try_from(x.write_ns).map_err(|_|"role3 IO duration")?,sync_calls:x.sync_calls,sync_ns:u64::try_from(x.sync_ns).map_err(|_|"role3 IO duration")?})}}
        #[derive(Serialize)]struct IoStages{window_checks:Io,admission:Io,producer:Io,source_mle:Io,custody:Io}
        #[derive(Serialize)]struct Scope{input_log:usize,row_log:usize,owners:usize,active_headers:usize,local_input_log:usize,local_row_log:usize,terms_per_owner:usize,
            point_bank:usize,producer_limit_bytes:usize,job_limit_bytes:usize,deadline_seconds:usize,native_diagnostic:bool,all_seven_claims:bool,common_opening:bool,production:bool}
        #[derive(Serialize)]struct Inputs<'a>{raw_sha256:&'static str,witness_sha256:&'static str,witness_blake2b256:&'static str,key_sha256:Hex<'a>,commitment_sha256:Hex<'a>,
            setup_id:Hex<'a>,parent_root:Hex<'a>,candidate_tip:Hex<'a>,candidate_total:Hex<'a>,candidate_tip_time:i64}
        #[derive(Serialize)]struct Producer<'a>{loads:usize,reconstructed_fields:usize,canonical_visitors:usize,canonical_terms:usize,grouped:Grouped<'a>,boolean_u:Boolean<'a>,memory:NativeRole3Memory,io:IoStages}
        #[derive(Serialize)]struct Proof<'a>{scalars:usize,bytes:usize,rounds:usize,line_coefficients:usize,sha256:Hex<'a>,canonical_roundtrip:bool}
        #[derive(Serialize)]struct Claim<'a>{point_hex:Scalars<'a>,projected_point_hex:Scalars<'a>,value_hex:Scalar}
        #[derive(Serialize)]struct TranscriptRecord{producer_counters:[u64;3],verifier_counters:[u64;3],continuation_hex:Scalar}
        #[derive(Serialize)]struct Checks{independent_verify:bool,source_mle:bool,projection_basis:bool,negative_controls:bool,custody_unchanged:bool}
        #[derive(Serialize)]struct Timing{admission:u64,producer:u64,codec:u64,verify:u64,source_mle:u64,negative_controls:u64,custody:u64,export_preparation:u64,total_before_export:u64}
        #[derive(Serialize)]struct Report<'a>{schema:&'static str,state:&'static str,scope:Scope,inputs:Inputs<'a>,producer:Producer<'a>,proof:Proof<'a>,claim:Claim<'a>,
            transcript:TranscriptRecord,checks:Checks,phase_marks:[NativeRole3Mark;17],timing_ns:Timing}
        fn proof_capacity(p:&GkrProof)->Result<usize,String>{let mut bytes=mul(p.layers.capacity(),size_of::<crate::gkr::LayerProof>())?;
            for l in &p.layers{bytes=add(bytes,mul(l.rounds.capacity(),size_of::<Vec<Fr>>())?)?;bytes=add(bytes,mul(l.line_coefficients.capacity(),size_of::<Fr>())?)?;
                for r in &l.rounds{bytes=add(bytes,mul(r.capacity(),size_of::<Fr>())?)?;}}Ok(bytes)}
        fn owned_capacity(raw:&PinnedArtifact,key:&PinnedArtifact,commitment:&PinnedArtifact,path:&PathBuf,dir:&Path,
            proof:Option<&GkrProof>,packet:Option<&Vec<u8>>,projected:Option<&Vec<Fr>>)->Result<usize,String>{
            let mut bytes=add(size_of::<Report<'_>>(),size_of::<ReportWriter>())?;
            for n in [REPORT_CAP,3*size_of::<PinnedArtifact>(),size_of::<PackedFile>(),size_of::<File>(),size_of::<Transcript>()*6,
                raw.bytes.capacity(),key.bytes.capacity(),commitment.bytes.capacity(),path.capacity(),dir.as_os_str().len()*2,
                size_of::<GkrProof>()*3,size_of::<InputClaim>()*3,size_of::<GroupedVStats>(),size_of::<BooleanUPreweightStats>(),131072]{bytes=add(bytes,n)?;}
            if let Some(p)=proof{bytes=add(bytes,mul(proof_capacity(p)?,3)?)?;}if let Some(p)=packet{bytes=add(bytes,mul(p.capacity(),3)?)?;}
            if let Some(p)=projected{bytes=add(bytes,mul(p.capacity(),size_of::<Fr>())?)?;}
            require(bytes<=EXPORT_BOUND,"role3 typed export/held-buffer bound")?;Ok(bytes)
        }
        fn generic_denial()->Result<(),String>{let admission=GroupedVAdmission::try_new(12,&vec![0;4096],&[288158])?;
            for boolean in [false,true]{let loaded=Cell::new(0usize);let bound=Cell::new(0usize);let visited=Cell::new(0usize);let mut t=Transcript::new(b"role3-generic-denial");let before=fingerprint(&t);
                let loader=|_|{loaded.set(loaded.get()+1);Err("unexpected generic native owner load".into())};let binder=|_:&mut Transcript|bound.set(bound.get()+1);
                let visitor=|_,_:&mut dyn FnMut(Term)->Result<(),String>|{visited.set(visited.get()+1);Ok(())};
                let error=if boolean{stream::prove_with_boolean_u_grouped_v_for_test(13,12,14,0,&[14],Some(0),&admission,loader,&mut t,binder,visitor,|_,_,_|Ok([Fr::zero();4])).err()}
                    else{stream::prove_with_direct_u_grouped_v_for_test(13,12,14,0,&[14],Some(0),&admission,loader,&mut t,binder,visitor,|_,_,_|Ok([Fr::zero();4])).err()};
                require(error.as_deref()==Some("grouped V dimensions exceed the supported bound before allocation")&&loaded.get()==0&&bound.get()==0&&visited.get()==0&&fingerprint(&t)==before,
                    "role3 generic native callback denial")?;
            }Ok(())}
        fn window_controls(plan:&NativePrefixAuthPlan<'_>,source:&PackedFile)->Result<(),String>{let native=input();
            for owner in [0usize,1,3072,3073,4095]{let (height,_)=plan.padding_heights(owner)?;let raw=native.raw(height)?;
                let header=ergo_header_core::Header::decode(raw,None).map_err(|e|format!("{e:?}"))?;
                let(pk,w)=match &header.pow{ergo_header_core::PowSolution::V1{pk,w,..}=>(*pk.as_bytes(),*w.as_bytes()),_=>return Err("role3 requires accepted V1 point input".into())};
                let expected=crate::point_membership::witness(pk,w)?;let actual=source.read_copy(8192,owner*128+96)?;
                require(actual.len()==8192&&actual.capacity()==8192&&expected.len()==8192&&actual.iter().zip(&expected).all(|(x,b)|*x==Fr::from(*b as u64)),"role3 actual held point window differs from RAW")?;
                if owner>=3073{require(expected.iter().any(|b|*b)&&raw==native.raw(3073)?,"role3 nonzero last-header padding")?;}
                let mut point=vec![Fr::zero();25];let set=expected.iter().position(|b|*b).ok_or("role3 honest point has no set input")?;
                for bit in 0..13{point[bit]=Fr::from(((set>>bit)&1)as u64);}for bit in 0..12{point[13+bit]=Fr::from(((owner>>bit)&1)as u64);}
                let projected=plan.project_claim(3,&point)?;let global=plan.point_global_wire(owner,set)?;
                require(eq_index(&projected,global)==Fr::one()&&actual[set]==Fr::one(),"role3 projection basis witness")?;
                for bit in 13..20{let mut wrong=projected.clone();wrong[bit]=Fr::one()-wrong[bit];require(eq_index(&wrong,global).is_zero(),"role3 isolated bank-bit basis mutant")?;}
                let mut wrong=projected;wrong.swap(20,21);
                if (owner&1)!=((owner>>1)&1){require(eq_index(&wrong,global).is_zero(),"role3 owner bit-order basis mutant")?;}
            }Ok(())}
        fn consumer_controls(plan:&NativePrefixAuthPlan<'_>,ctx:&NativeRole3DiagnosticContext,proof:&GkrProof,claim:&InputClaim,source_value:Fr)->Result<(),String>{
            let mut changed=proof.clone();changed.layers[0].rounds[0][1]+=Fr::one();let mut t=ctx.transcript();let before=fingerprint(&t);let mut working=t.clone();
            let binds=Cell::new(0usize);let wires=Cell::new(0usize);let prepared=plan.prepare_role3_binding_for_test(&working,ctx)?;
            let error=gkr::verify_with_wiring(&[25],1usize<<26,&changed,&mut working,|t|{binds.set(binds.get()+1);*t=prepared;},|_,_,_,_|{wires.set(wires.get()+1);Ok([Fr::zero();4])}).unwrap_err();
            require(error==GkrError::SumcheckIdentity&&working.challenges()==26&&binds.get()==1&&wires.get()==0&&fingerprint(&t)==before,"role3 changed-round reached first message")?;
            let wrong=Transcript::new(b"native-prefix-role0-diagnostic-proof-v1");let wrong=plan.prepare_role3_binding_for_test(&wrong,ctx)?;
            let mut probe=wrong.clone();for _ in 0..26{probe.challenge_scalar(b"gkr-output-coordinate");}gkr::append_usize(&mut probe,b"gkr-layer-index",0);
            let p=&proof.layers[0].rounds;require(p[0][0]+gkr::eval_polynomial(&p[0],Fr::one())==Fr::zero(),"role3 original first identity")?;
            gkr::append_polynomial(&mut probe,b"gkr-sumcheck-polynomial",&p[0]);let z=probe.challenge_scalar(b"gkr-sumcheck-challenge");
            require(gkr::eval_polynomial(&p[0],z)!=p[1][0]+gkr::eval_polynomial(&p[1],Fr::one()),"role3 wrong-domain prerequisite not observable")?;
            let mut working=t.clone();binds.set(0);wires.set(0);
            let error=gkr::verify_with_wiring(&[25],1usize<<26,proof,&mut working,|t|{binds.set(binds.get()+1);*t=wrong;},|_,_,_,_|{wires.set(wires.get()+1);Ok([Fr::zero();4])}).unwrap_err();
            require(error==GkrError::SumcheckIdentity&&working.challenges()==27&&binds.get()==1&&wires.get()==0&&fingerprint(&t)==before,"role3 wrong-domain reached second message")?;
            require(claim.value==source_value&&claim.value+Fr::one()!=source_value,"role3 changed-claim source discrepancy")?;
            let mut roster=plan.descriptors().to_vec();roster[3].input_log-=1;require(plan.validate_roster(&roster).is_err(),"role3 isolated descriptor guard")?;
            let mut late=ctx.transcript();late.challenge_scalar(b"late-role3-bind");let before=fingerprint(&late);
            let error=plan.prepare_role3_binding_for_test(&late,ctx).err().ok_or("role3 late binder accepted")?;
            require(error=="native role3 binding after challenge"&&fingerprint(&late)==before,"role3 reached late-binding rollback")?;Ok(())
        }
        fn run(dir:&Path)->Result<(),String>{
            // Static reservations precede artifact/report allocations. The
            // producer later computes its exact native scoped preflight; parent
            // construction remains separately bounded by the whole-process Job.
            require(512usize*1024*1024+32*1024*1024+EXPORT_BOUND+869449<2usize*1024*1024*1024,"role3 initial Job reservation")?;
            let mut raw=pinned_artifact("NIPOPOW_NATIVE_AUTH_FIXTURE",869449,RAW_SHA)?;raw.bytes=Vec::new();
            let key=pinned_artifact("NIPOPOW_ROLE4_KEY_PATH",33264,"D11220A1CBB08BE2C84F6B854EC2A932B3FCEC49C217963D079DD8053F7B31B2")?;
            let commitment=pinned_artifact("NIPOPOW_NATIVE_ROLE0_COMMITMENT_PATH",384,"2739A3353D579A7FA0F19B06EFDD26A625CDB80009C65707D8B96E7D8C0C9C90")?;
            let path=PathBuf::from(std::env::var_os("NIPOPOW_NATIVE_U_SEQUENCE_WITNESS").ok_or("role3 witness env absent")?);require(path.is_absolute(),"role3 witness absolute path")?;
            let held=u0_open_bytes(&path)?;let identity=u0_file_info(&held)?;let source=PackedFile::open_with_limit(&path,32,32)?;
            let ctx=NativeRole3DiagnosticContext::admit(&key.bytes,&commitment.bytes,held.try_clone().map_err(|e|e.to_string())?)?;
            owned_capacity(&raw,&key,&commitment,&path,dir,None,None,None)?;
            let (packet,report_bytes)=with_plan(|_parent,plan,candidate|->Result<(Vec<u8>,Vec<u8>),String>{
                source.reset_io_metrics();window_controls(plan,&source)?;let window_io=Io::new(source.io_metrics_snapshot())?;
                require(window_io.read_calls==5&&window_io.read_bytes==5120,"role3 window check IO census")?;generic_denial()?;
                let view=source.native_role0_view()?;let detached=PackedFile::open_with_limit(&path,32,32)?;
                require(view.require_same_source(&detached).is_err(),"role3 detached held-source view rejected")?;drop(detached);
                let mut bad=key.bytes.clone();bad[0]^=1;
                require(NativeRole3DiagnosticContext::admit(&bad,&commitment.bytes,held.try_clone().map_err(|e|e.to_string())?).is_err(),"role3 changed-key admission")?;drop(bad);
                let mut bad=commitment.bytes.clone();bad[0]^=1;
                require(NativeRole3DiagnosticContext::admit(&key.bytes,&bad,held.try_clone().map_err(|e|e.to_string())?).is_err(),"role3 changed-commitment admission")?;drop(bad);
                let mut late=ctx.transcript();late.challenge_scalar(b"late-before-native3");let before=fingerprint(&late);
                let error=plan.prove_role3_packed_for_test(&source,&mut late,&ctx).err().ok_or("role3 challenged producer accepted")?;
                require(error=="native role3 proof transcript already challenged"&&fingerprint(&late)==before&&source.io_metrics_snapshot().read_calls==5,"role3 native preflight no-read rollback")?;
                let mut outer=ctx.transcript();let original=fingerprint(&outer);let mut staged=outer.clone();
                let (proof,producer_claim,grouped,boolean)=plan.prove_role3_packed_for_test(&source,&mut staged,&ctx)?;
                require(fingerprint(&outer)==original,"role3 outer transcript committed before consumers")?;
                let (admission_io,producer_io)=ctx.io_for_report();
                require(admission_io.read_calls==4096&&admission_io.read_bytes==536870912&&producer_io.read_calls==73728&&producer_io.read_bytes==75497472,"role3 native IO census")?;
                require(grouped.baseline_term_callbacks==1_180_295_168&&grouped.template_term_count==288158&&grouped.bank_term_callbacks==288158&&grouped.handoff_term_callbacks==0
                    &&grouped.group_owner_counts==[4096]&&grouped.group_term_counts==[288158]&&grouped.owner_handoff_count==4096&&grouped.local_rounds==13
                    &&boolean.prefix_builds==14&&boolean.shared_term_iterations==4034212&&boolean.owner_term_selections==16_524_132_352
                    &&boolean.boolean_checked_loads==73728&&boolean.boolean_checked_fields==603_979_776&&boolean.zero_anchor_sweep_skipped,"role3 full owner/callback census")?;
                let began=Instant::now();let packet=gkr::encode_proof(&proof)?;let expected=(7usize*25+3).checked_mul(Fr::zero().compressed_size()).ok_or("role3 codec overflow")?;
                require(expected==5696&&packet.len()==expected&&packet.capacity()<=8192&&proof.layers.len()==1&&proof.layers[0].rounds.len()==50&&proof.layers[0].line_coefficients.len()==26,"role3 codec178Fr shape")?;
                let decoded=gkr::decode_dimensions(&[25],&packet)?;require(decoded==proof&&gkr::encode_proof(&decoded)?==packet,"role3 canonical scalar stream")?;let codec=ns(began)?;
                let began=Instant::now();let (claim,verifier)=plan.verify_role3_for_test(&decoded,&ctx)?;
                require(claim==producer_claim&&claim.point.len()==25&&staged.challenges()==77&&counters(&staged)==counters(&verifier)&&fingerprint(&staged)==fingerprint(&verifier),"role3 independent consumer/transcript")?;let verify=ns(began)?;
                source.reset_io_metrics();let began=Instant::now();let projected=plan.project_claim(3,&claim.point)?;
                require(projected.len()==32&&projected[..13]==claim.point[..13]&&projected[20..]==claim.point[13..]
                    &&projected[13..20]==[0u64,0,0,0,0,1,1].map(Fr::from),"role3 exact bank96 claim projection")?;
                let value=source.evaluate(&projected)?;require(value==claim.value,"role3 held-source projected MLE")?;let source_mle=ns(began)?;let mle_io=Io::new(source.io_metrics_snapshot())?;
                let began=Instant::now();consumer_controls(plan,&ctx,&decoded,&claim,value)?;let negative_controls=ns(began)?;
                source.reset_io_metrics();let began=Instant::now();
                require(u0_file_info(&held)?==identity&&u0_file_info(&raw.file)?==raw.identity&&u0_file_info(&key.file)?==key.identity&&u0_file_info(&commitment.file)?==commitment.identity,"role3 final immutable held custody")?;
                let custody=ns(began)?;let custody_io=Io::new(source.io_metrics_snapshot())?;ctx.mark("consumer_complete")?;
                let began=Instant::now();let mut owned=owned_capacity(&raw,&key,&commitment,&path,dir,Some(&proof),Some(&packet),Some(&projected))?;
                owned=add(owned,mul(add(producer_claim.point.capacity(),claim.point.capacity())?,size_of::<Fr>())?)?;
                owned=add(owned,mul(add(grouped.group_owner_counts.capacity(),grouped.group_term_counts.capacity())?,size_of::<usize>())?)?;
                owned=add(owned,mul(add(grouped.group_weight_sums.capacity(),grouped.group_d_local_contributions.capacity())?,size_of::<Fr>())?)?;
                require(owned<=EXPORT_BOUND,"role3 complete returned/export overlap")?;
                let hash=crate::native_prefix_auth_plan::role0_sha256(&packet)?;let (key_id,commitment_id,setup)=ctx.artifact_ids();let memory=ctx.memory_for_report()?;
                require(memory.extra_live_capacity_bytes.checked_add(196132592)==Some(boolean.u_preflight_capacity_bound_bytes),"role3 exact source-derived native prebound")?;
                let export_preparation=ns(began)?;let total=ctx.elapsed_ns()?;ctx.mark("export_ready")?;let marks=ctx.marks_for_report()?;
                let report=Report{schema:"native-role3-boolean-grouped-diagnostic-v1",state:"ROLE3_NATIVE25_GKR_PASS",
                    scope:Scope{input_log:25,row_log:26,owners:4096,active_headers:3073,local_input_log:13,local_row_log:14,terms_per_owner:288158,point_bank:96,
                        producer_limit_bytes:512*1024*1024,job_limit_bytes:2*1024*1024*1024,deadline_seconds:1800,native_diagnostic:true,all_seven_claims:false,common_opening:false,production:false},
                    inputs:Inputs{raw_sha256:RAW_SHA,witness_sha256:WITNESS_SHA,witness_blake2b256:WITNESS_BLAKE,key_sha256:Hex(&key_id),commitment_sha256:Hex(&commitment_id),setup_id:Hex(&setup),
                        parent_root:Hex(&candidate.root),candidate_tip:Hex(&candidate.tip),candidate_total:Hex(&candidate.total),candidate_tip_time:candidate.tip_time},
                    producer:Producer{loads:boolean.boolean_checked_loads,reconstructed_fields:boolean.boolean_checked_fields,canonical_visitors:4096,canonical_terms:grouped.baseline_term_callbacks,
                        grouped:Grouped(&grouped),boolean_u:Boolean(&boolean),memory,io:IoStages{window_checks:window_io,admission:Io::new(admission_io)?,producer:Io::new(producer_io)?,source_mle:mle_io,custody:custody_io}},
                    proof:Proof{scalars:178,bytes:5696,rounds:50,line_coefficients:26,sha256:Hex(&hash),canonical_roundtrip:true},claim:Claim{point_hex:Scalars(&claim.point),projected_point_hex:Scalars(&projected),value_hex:Scalar(claim.value)},
                    transcript:TranscriptRecord{producer_counters:counters(&staged),verifier_counters:counters(&verifier),continuation_hex:Scalar(staged.clone().challenge_scalar(CONTINUATION))},
                    checks:Checks{independent_verify:true,source_mle:true,projection_basis:true,negative_controls:true,custody_unchanged:true},phase_marks:marks,
                    timing_ns:Timing{admission:marks[1].elapsed_ns,producer:ctx.producer_elapsed_ns(),codec,verify,source_mle,negative_controls,custody,export_preparation,total_before_export:total}};
                let report=encode_report(&report)?;require(fingerprint(&outer)==original,"role3 late outer rollback boundary")?;
                // The local outer transaction commits only after every consumer,
                // negative, custody and export-admissibility check has succeeded.
                outer=staged;require(counters(&outer)==counters(&verifier),"role3 final outer commit")?;Ok((packet,report))
            })?;export(dir,&packet,&report_bytes)
        }
        #[test]fn native_role3_export_and_callback_boundaries(){
            generic_denial().unwrap();assert!(add(usize::MAX,1).is_err());assert!(size_of::<Report<'_>>()+REPORT_CAP+8192*6+131072<EXPORT_BOUND);
            let small=Hold{state:"HOLD",stage:"bounded"};let bytes=encode_report(&small).unwrap();assert!(bytes.len()<128);
            let mut w=ReportWriter{bytes:Vec::new()};assert!(w.write_all(&vec![0;REPORT_CAP+1]).is_err());assert!(w.bytes.is_empty());
            let base=std::env::temp_dir().join(format!("r3-export-{}-{}",std::process::id(),std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
            std::fs::create_dir(&base).unwrap();save(&base.join("result.json.part"),&bytes,true).unwrap();save(&base.join("result.json"),b"existing",true).unwrap();
            assert!(export(&base,&vec![0;5696],&bytes).is_err());retain_hold(&base).unwrap();
            assert_eq!(std::fs::read(base.join("result.json")).unwrap(),b"existing");assert_eq!(std::fs::read(base.join("result.json.part")).unwrap(),bytes);
            assert_eq!(std::fs::read(base.join("role3.gkr")).unwrap().len(),5696);
            for name in ["result.json","result.json.part","role3.gkr"]{std::fs::remove_file(base.join(name)).unwrap();}std::fs::remove_dir(base).unwrap();
        }
        #[test]
        #[ignore="one sealed native25 role3 proof; reviewed1800s/Job2GiB/Rayon4 controller required"]
        fn native_role3_boolean_grouped_gkr_claim_bounded(){let dir=output().unwrap();if let Err(error)=run(&dir){let retained=retain_hold(&dir);panic!("native role3 HOLD:{error};retention:{retained:?}");}}

// Integrate this module inside role0_diagnostic::role3_diagnostic.
// Generic24 differential controls only; this module cannot mint native admission.
mod ordinary {
    use ark_bn254::Fr;
    use ark_ff::{One, Zero};
    use ark_serialize::CanonicalSerialize;
    use std::cell::Cell;
    use std::mem::size_of;
    use crate::gkr::{self, GkrError, GkrProof, InputClaim};
    use crate::point_membership::{self as point, Compiled, POINT_WIDTH, TERM_COUNT};
    use crate::sparse::{self, Term};
    use crate::sparse_stream_roster::{self as stream, BooleanUPreweightStats, GroupedVAdmission, GroupedVStats};
    use crate::transcript::Transcript;

    const DOMAIN: &[u8] = b"role3-two-four-owner-differential-v1";
    const CONTINUATION: &[u8] = b"role3-ordinary-continuation";
    const PRODUCER: usize = 512 * 1024 * 1024;
    const JOB: usize = 2 * 1024 * 1024 * 1024;
    const SMALL_RESERVATION: usize = 16 * 1024 * 1024;

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum Arm { Direct, Boolean }
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum Fault { None, CountLow, CountHigh, Endpoint, WrongOwner, WrongWindow,
        Read { call: usize, kind: u8 }, Coefficient, PermuteValidRows }

    fn add(a: usize, b: usize) -> usize { a.checked_add(b).expect("ordinary capacity overflow") }
    fn mul(a: usize, b: usize) -> usize { a.checked_mul(b).expect("ordinary capacity overflow") }
    fn counters(t: &Transcript) -> [u64;3] { [t.challenges(), t.raw_queries(), t.bytes_absorbed()] }
    fn continuation(t: &Transcript) -> Fr { t.clone().challenge_scalar(CONTINUATION) }
    fn unchanged(a: &Transcript, b: &Transcript) {
        assert_eq!(counters(a), counters(b)); assert_eq!(continuation(a), continuation(b));
    }
    fn generator(prefix: u8) -> [u8;33] {
        let text = "79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798";
        let mut out = [0;33]; out[0] = prefix;
        for i in 0..32 { out[i+1] = u8::from_str_radix(&text[2*i..2*i+2],16).unwrap(); }
        out
    }
    fn compiled() -> Compiled {
        // Reserve a conservative two-template allocation envelope before build;
        // check the observed original Vec capacity before constructing witnesses.
        assert!(add(add(mul(2*TERM_COUNT,size_of::<Term>()),64352),
            add(PRODUCER,SMALL_RESERVATION))<=JOB);
        let c=point::build().unwrap();
        assert!(c.circuit.terms.capacity()<=2*TERM_COUNT);
        assert_eq!(c.circuit.terms.len(),TERM_COUNT);
        c
    }
    fn preflight(c: &Compiled, rows: &Vec<Vec<Fr>>, retained: usize) {
        assert_eq!((size_of::<Fr>(),size_of::<Term>()),(32,152));
        let mut external = add(size_of::<Compiled>(), mul(c.circuit.terms.capacity(),size_of::<Term>()));
        external = add(external,64352); // All point-layout boxed index arrays.
        external = add(external,mul(rows.capacity(),size_of::<Vec<Fr>>()));
        for row in rows { external = add(external,mul(row.capacity(),size_of::<Fr>())); }
        // The producer's independent 512MiB reservation does not include borrowed
        // template/witness ownership. The separate Job model covers those plus
        // held first proof/claim/packet/stats and bounded verifier/MLE/export scratch.
        assert!(add(add(add(external,retained),PRODUCER),SMALL_RESERVATION) <= JOB);
        assert!(retained <= 1024*1024, "first outcome exceeded reserved overlap");
    }
    fn witnesses(c: &Compiled, owners: usize, mixed: bool) -> Vec<Vec<Fr>> {
        assert!(matches!(owners,2|4));
        // Preflight before rows, witness conversion or residual tables allocate.
        let bound = add(add(mul(c.circuit.terms.capacity(),size_of::<Term>()),64352),
            add(mul(owners,POINT_WIDTH*32),SMALL_RESERVATION));
        assert!(add(bound,PRODUCER) <= JOB);
        let mut rows = Vec::new(); rows.try_reserve_exact(owners).unwrap();
        assert_eq!(rows.capacity(),owners);
        for owner in 0..owners {
            let pair = if owner+1 == owners { ([0;33],[0;33]) }
                else if mixed && owner%2 == 0 { (generator(2),[0;33]) }
                else if owner%2 == 0 { (generator(2),generator(3)) }
                else { (generator(3),generator(2)) };
            let bits = point::witness(pair.0,pair.1).unwrap();
            assert_eq!(bits.len(),POINT_WIDTH);
            let mut row = Vec::new(); row.try_reserve_exact(POINT_WIDTH).unwrap();
            assert_eq!(row.capacity(),POINT_WIDTH);
            row.extend(bits.iter().map(|bit|Fr::from(u64::from(*bit))));
            assert!(row.iter().any(|x|!x.is_zero()),"padding is a full nonzero auxiliary witness");
            let mut residuals = vec![Fr::zero();c.circuit.row_count];
            for term in &c.circuit.terms { residuals[term.row] += term.gate.evaluate(&row); }
            assert!(residuals.iter().all(Zero::is_zero));
            rows.push(row);
        }
        assert_ne!(rows[0],rows[owners-1],"source permutation prerequisite");
        preflight(c,&rows,0); rows
    }
    fn prepared(c: &Compiled, copy_bits: usize, wrong: bool) -> Transcript {
        let mut t = Transcript::new(if wrong { b"role3-wrong-ordinary-domain-v1" } else { DOMAIN });
        sparse::bind(&c.circuit,copy_bits,&mut t); t
    }
    fn fault_tag(kind: u8) -> &'static str {
        match kind { 0=>"r3 ordinary injected read", 1=>"r3 ordinary short row",
            2=>"r3 ordinary non-Boolean row", 3=>"r3 ordinary overcapacity row", _=>panic!("fault kind") }
    }
    fn checked_load(rows: &[Vec<Fr>], owner: usize, call: usize, fault: Fault, hit: &Cell<bool>) -> Result<Vec<Fr>,String> {
        let observed = if fault==Fault::WrongOwner && call==1 { hit.set(true);rows.len() } else { owner };
        if observed>=rows.len() { return Err("r3 ordinary owner outside source".into()); }
        let expected_start = observed.checked_mul(POINT_WIDTH).ok_or("r3 ordinary window overflow")?;
        let start = if fault==Fault::WrongWindow && call==1 { hit.set(true);expected_start+1 } else { expected_start };
        if start!=owner*POINT_WIDTH { return Err("r3 ordinary source window differs".into()); }
        let physical = if fault==Fault::PermuteValidRows { rows.len()-1-owner } else { owner };
        let mut values = rows[physical].clone();
        if let Fault::Read{call:target,kind}=fault {
            if target==call { hit.set(true); match kind {
                0=>return Err(fault_tag(kind).into()),
                1=>{ values.pop(); },
                2=>values[0]=Fr::from(2u64),
                3=>values.reserve_exact(1),
                _=>panic!("fault kind")
            }}
        }
        if values.len()!=POINT_WIDTH { return Err(fault_tag(1).into()); }
        if values.capacity()!=POINT_WIDTH { return Err(fault_tag(3).into()); }
        if values.iter().any(|x|!x.is_zero()&&!x.is_one()) { return Err(fault_tag(2).into()); }
        Ok(values)
    }
    struct Outcome {
        proof: GkrProof, claim: InputClaim, packet: Vec<u8>, transcript: Transcript,
        grouped: GroupedVStats, boolean: Option<BooleanUPreweightStats>,
        loads: usize, visitors: usize, terms: usize, binds: usize, wires: usize,
    }
    impl Outcome {
        fn capacity(&self) -> usize {
            let mut n = add(size_of::<Self>(),self.packet.capacity());
            n = add(n,mul(self.claim.point.capacity(),size_of::<Fr>()));
            n = add(n,mul(self.proof.layers.capacity(),size_of::<gkr::LayerProof>()));
            for layer in &self.proof.layers {
                n = add(n,mul(layer.rounds.capacity(),size_of::<Vec<Fr>>()));
                n = add(n,mul(layer.line_coefficients.capacity(),size_of::<Fr>()));
                for round in &layer.rounds { n = add(n,mul(round.capacity(),size_of::<Fr>())); }
            }
            n=add(n,mul(add(self.grouped.group_owner_counts.capacity(),self.grouped.group_term_counts.capacity()),size_of::<usize>()));
            n=add(n,mul(add(self.grouped.group_weight_sums.capacity(),self.grouped.group_d_local_contributions.capacity()),size_of::<Fr>()));
            n
        }
    }
    #[derive(Debug)]
    struct Failure { tag:String, loads:usize, visitors:usize, terms:usize, binds:usize,
        wires:usize, hit:bool, working_counters:[u64;3] }
    fn run(c:&Compiled, rows:&Vec<Vec<Fr>>, prefix:&Transcript, caller:&mut Transcript,
        arm:Arm, fault:Fault, retained:usize) -> Result<Outcome,Failure> {
        preflight(c,rows,retained);
        let owners=rows.len(); let copy_bits=owners.trailing_zeros() as usize;
        let count=match fault{Fault::CountLow=>TERM_COUNT-1,Fault::CountHigh=>TERM_COUNT+1,_=>TERM_COUNT};
        let map=vec![0;owners]; let admission=GroupedVAdmission::try_new(copy_bits,&map,&[count]).unwrap();
        let shape=sparse::validate(&c.circuit,copy_bits).unwrap();
        let loads=Cell::new(0usize);let visits=Cell::new(0usize);let terms=Cell::new(0usize);
        let binds=Cell::new(0usize);let wires=Cell::new(0usize);let hit=Cell::new(false);
        let mut working=caller.clone();
        let loader=|owner|{let call=add(loads.get(),1);loads.set(call);checked_load(rows,owner,call,fault,&hit)};
        let binder=|t:&mut Transcript|{binds.set(add(binds.get(),1));*t=prefix.clone();};
        let visitor=|owner,sink:&mut dyn FnMut(Term)->Result<(),String>|{
            if owner>=owners{return Err("r3 ordinary visitor owner outside source".into());}
            visits.set(add(visits.get(),1));
            for (index,term) in c.circuit.terms.iter().enumerate(){
                terms.set(add(terms.get(),1));let mut term=term.clone();
                if fault==Fault::Endpoint&&index==0{term.gate.left=POINT_WIDTH;hit.set(true);}
                sink(term)?;
            } Ok(())
        };
        let wiring=|r:&[Fr],u:&[Fr],v:&[Fr]|{
            wires.set(add(wires.get(),1));
            let mut coefficients=sparse::wiring(&c.circuit,&shape,r,u,v).map_err(|e|e.to_string())?;
            if fault==Fault::Coefficient{coefficients[0]+=Fr::one();hit.set(true);}
            Ok(coefficients)
        };
        let produced=match arm {
            Arm::Direct=>stream::prove_with_direct_u_grouped_v_for_test(13,copy_bits,14,0,&[14],Some(0),&admission,
                loader,&mut working,binder,visitor,wiring).map(|(p,q,g)|(p,q,g,None)),
            Arm::Boolean=>stream::prove_with_boolean_u_grouped_v_for_test(13,copy_bits,14,0,&[14],Some(0),&admission,
                loader,&mut working,binder,visitor,wiring).map(|(p,q,g,b)|(p,q,g,Some(b)))
        };
        let failure=|tag:String|Failure{tag,loads:loads.get(),visitors:visits.get(),terms:terms.get(),
            binds:binds.get(),wires:wires.get(),hit:hit.get(),working_counters:counters(&working)};
        let (proof,claim,grouped,boolean)=produced.map_err(failure)?;
        let packet=gkr::encode_proof(&proof).map_err(failure)?;
        if packet.capacity()>65536{return Err(failure("r3 ordinary packet reservation".into()));}
        let outcome=Outcome{proof,claim,packet,transcript:working,grouped,boolean,
            loads:loads.get(),visitors:visits.get(),terms:terms.get(),binds:binds.get(),wires:wires.get()};
        assert!(outcome.capacity()<=1024*1024);
        *caller=outcome.transcript.clone(); Ok(outcome)
    }
    fn flattened(rows:&Vec<Vec<Fr>>) -> Vec<Fr> {
        let count=mul(rows.len(),POINT_WIDTH);
        assert!(mul(count,32)*2<=SMALL_RESERVATION);
        let mut flat=Vec::new();flat.try_reserve_exact(count).unwrap();assert_eq!(flat.capacity(),count);
        for row in rows { flat.extend_from_slice(row); } flat
    }
    fn source_check(flat:&[Fr],claim:&InputClaim) -> Result<(),String> {
        if gkr::mle(flat,&claim.point).map_err(|e|e.to_string())? != claim.value {
            return Err("r3 ordinary original source MLE differs".into());
        } Ok(())
    }
    fn verify(c:&Compiled,owners:usize,prefix:&Transcript,proof:&GkrProof, coefficient_fault:bool)
        -> (Result<InputClaim,GkrError>,Transcript,usize,usize) {
        let bits=owners.trailing_zeros() as usize;let shape=sparse::validate(&c.circuit,bits).unwrap();
        let mut t=Transcript::new(DOMAIN);let binds=Cell::new(0usize);let wires=Cell::new(0usize);
        let answer=gkr::verify_with_wiring(&[13+bits],16384*owners,proof,&mut t,
            |t|{binds.set(binds.get()+1);*t=prefix.clone();},
            |layer,r,u,v|{
                assert_eq!(layer,0);wires.set(wires.get()+1);
                let mut coefficients=sparse::wiring(&c.circuit,&shape,r,u,v)?;
                if coefficient_fault {coefficients[0]+=Fr::one();}
                Ok(coefficients)
            });
        (answer,t,binds.get(),wires.get())
    }
    fn consume(c:&Compiled,rows:&Vec<Vec<Fr>>,prefix:&Transcript,outcome:&Outcome) {
        let dimension=13+rows.len().trailing_zeros() as usize;
        let encoded_bytes=(7*dimension+3).checked_mul(Fr::zero().compressed_size()).unwrap();
        assert_eq!(outcome.packet.len(),encoded_bytes);
        let decoded=gkr::decode_dimensions(&[dimension],&outcome.packet).unwrap();
        assert_eq!(decoded,outcome.proof);assert_eq!(gkr::encode_proof(&decoded).unwrap(),outcome.packet);
        let (claim,verifier,binds,wires)=verify(c,rows.len(),prefix,&decoded,false);
        assert_eq!(claim.unwrap(),outcome.claim);assert_eq!((binds,wires),(1,1));
        assert_eq!(counters(&verifier),counters(&outcome.transcript));
        assert_eq!(continuation(&verifier),continuation(&outcome.transcript));
        let flat=flattened(rows);source_check(&flat,&outcome.claim).unwrap();
    }
    fn projected_source(rows:&Vec<Vec<Fr>>,claim:&InputClaim) {
        // Two bank bits are the small analogue of the seven bank96 coordinates.
        // Every unused bank, including padding-owner banks, remains nonzero.
        let count=mul(mul(rows.len(),4),POINT_WIDTH);
        assert!(mul(count,32)*2<=SMALL_RESERVATION);
        let mut all=Vec::new();all.try_reserve_exact(count).unwrap();assert_eq!(all.capacity(),count);
        for row in rows {for bank in 0..4 {
            if bank==2 {all.extend_from_slice(row);}
            else {all.extend(std::iter::repeat_n(Fr::from((23+bank) as u64),POINT_WIDTH));}
        }}
        let mut point=Vec::with_capacity(claim.point.len()+2);
        point.extend_from_slice(&claim.point[..13]);point.extend([Fr::zero(),Fr::one()]);
        point.extend_from_slice(&claim.point[13..]);
        assert_eq!(gkr::mle(&all,&point).unwrap(),claim.value);
        let mut wrong=point.clone();wrong[13]=Fr::one();wrong[14]=Fr::zero();
        let observed=gkr::mle(&all,&wrong).unwrap();
        assert_ne!(observed,claim.value,"wrong bank/order must be observable before rejection");
        let wrong_claim=InputClaim{point:wrong,value:claim.value};
        assert_eq!(source_check(&all,&wrong_claim).unwrap_err(),"r3 ordinary original source MLE differs");
    }
    fn assert_success_census(out:&Outcome,owners:usize,arm:Arm) {
        let direct=arm==Arm::Direct;
        assert_eq!((out.loads,out.binds,out.wires),((if direct{19}else{18})*owners,1,1));
        assert_eq!(out.visitors,(if direct{16}else{1})*owners);
        assert_eq!(out.terms,(if direct{16}else{1})*owners*TERM_COUNT);
        assert_eq!(out.transcript.challenges(),(41+3*owners.trailing_zeros() as usize) as u64);
        assert_eq!(out.grouped.group_owner_counts,vec![owners]);assert_eq!(out.grouped.group_term_counts,vec![TERM_COUNT]);
        assert_eq!((out.grouped.baseline_term_callbacks,out.grouped.bank_term_callbacks,
            out.grouped.handoff_term_callbacks,out.grouped.local_rounds,out.grouped.owner_handoff_count),
            (owners*TERM_COUNT,TERM_COUNT,0,13,owners));
        assert!(out.grouped.grouped_state_peak_capacity_bytes<=PRODUCER);
        if let Some(stats)=&out.boolean {
            assert_eq!((stats.prefix_builds,stats.shared_term_iterations,stats.owner_term_selections),
                (14,14*TERM_COUNT,14*TERM_COUNT*owners));
            assert_eq!((stats.boolean_checked_loads,stats.boolean_checked_fields),(18*owners,18*owners*POINT_WIDTH));
            assert!(stats.zero_anchor_sweep_skipped);
            assert_eq!(stats.u_phase_peak_capacity_bytes.iter().copied().max(),Some(stats.u_state_peak_capacity_bytes));
            assert!(stats.u_state_peak_capacity_bytes<=stats.u_preflight_capacity_bound_bytes
                &&stats.u_preflight_capacity_bound_bytes<=PRODUCER);
        } else {assert!(direct);}
    }

    #[test]
    fn role3_two_four_owner_messages_consumers_and_projection() {
        let c=compiled();
        for owners in [2usize,4] {for mixed in [false,true] {
            let rows=witnesses(&c,owners,mixed);let prefix=prepared(&c,owners.trailing_zeros() as usize,false);
            let mut direct_t=Transcript::new(DOMAIN);let mut boolean_t=direct_t.clone();
            let direct=run(&c,&rows,&prefix,&mut direct_t,Arm::Direct,Fault::None,0).unwrap();
            preflight(&c,&rows,direct.capacity());
            let boolean=run(&c,&rows,&prefix,&mut boolean_t,Arm::Boolean,Fault::None,direct.capacity()).unwrap();
            assert_eq!(direct.proof.layers[0].rounds,boolean.proof.layers[0].rounds);
            assert_eq!(direct.proof,boolean.proof);assert_eq!(direct.packet,boolean.packet);
            assert_eq!(direct.claim,boolean.claim);assert_eq!(counters(&direct_t),counters(&boolean_t));
            assert_eq!(continuation(&direct_t),continuation(&boolean_t));
            assert_success_census(&direct,owners,Arm::Direct);assert_success_census(&boolean,owners,Arm::Boolean);
            consume(&c,&rows,&prefix,&direct);consume(&c,&rows,&prefix,&boolean);
            projected_source(&rows,&boolean.claim);
        }}
    }

    #[test]
    fn role3_two_four_owner_reached_faults() {
        let c=compiled();let rows=witnesses(&c,2,true);let owners=rows.len();
        let copy_bits=owners.trailing_zeros() as usize;let prefix=prepared(&c,copy_bits,false);
        for arm in [Arm::Direct,Arm::Boolean] {
            for fault in [Fault::CountLow,Fault::CountHigh,Fault::Endpoint,Fault::WrongOwner,Fault::WrongWindow] {
                let mut caller=Transcript::new(DOMAIN);caller.append_bytes(b"outer",b"preserve");let before=caller.clone();
                let e=run(&c,&rows,&prefix,&mut caller,arm,fault,0).err().expect("reached admission fault");
                let expected=match fault {
                    Fault::CountLow=>"grouped V owner exceeded its admitted topology count",
                    Fault::CountHigh=>"grouped V owner census differs from its admitted topology",
                    Fault::Endpoint=>"grouped V rejects sentinel or out-of-range endpoints",
                    Fault::WrongOwner=>"r3 ordinary owner outside source",
                    Fault::WrongWindow=>"r3 ordinary source window differs",_=>unreachable!()
                };
                assert_eq!(e.tag,expected);assert_eq!((e.loads,e.binds,e.wires),(1,0,0));
                assert_eq!(e.working_counters[0],0);unchanged(&before,&caller);
                if matches!(fault,Fault::CountLow|Fault::CountHigh){assert_eq!((e.visitors,e.terms),(1,TERM_COUNT));}
                else if fault==Fault::Endpoint{assert!(e.hit);assert_eq!((e.visitors,e.terms),(1,1));}
                else {assert!(e.hit);assert_eq!((e.visitors,e.terms),(0,0));}
            }
            for call in [1usize,owners+1] {for kind in 0u8..4 {
                let mut caller=Transcript::new(DOMAIN);let before=caller.clone();
                let e=run(&c,&rows,&prefix,&mut caller,arm,Fault::Read{call,kind},0).err().expect("reached read fault");
                assert_eq!(e.tag,fault_tag(kind));assert!(e.hit);assert_eq!(e.loads,call);
                assert_eq!((e.binds,e.wires),(usize::from(call>owners),0));
                let mut expected=if call==1{before.clone()}else{prefix.clone()};
                if call>owners {
                    for _ in 0..14+copy_bits{expected.challenge_scalar(b"gkr-output-coordinate");}
                    gkr::append_usize(&mut expected,b"gkr-layer-index",0);
                    assert_eq!((e.visitors,e.terms),(owners,owners*TERM_COUNT));
                } else {assert_eq!((e.visitors,e.terms),(0,0));}
                assert_eq!(e.working_counters,counters(&expected));unchanged(&before,&caller);
            }}
            let mut caller=Transcript::new(DOMAIN);let before=caller.clone();
            let e=run(&c,&rows,&prefix,&mut caller,arm,Fault::Coefficient,0).err().expect("reached coefficient fault");
            assert_eq!(e.tag,GkrError::TerminalExpression.to_string());assert!(e.hit);
            assert_eq!((e.binds,e.wires),(1,1));assert_eq!(e.working_counters[0],(40+3*copy_bits) as u64);
            unchanged(&before,&caller);
            let good=run(&c,&rows,&prefix,&mut caller,arm,Fault::None,0).unwrap();
            consume(&c,&rows,&prefix,&good);
            let (bad,_,binds,wires)=verify(&c,owners,&prefix,&good.proof,true);
            assert_eq!(bad.unwrap_err(),GkrError::TerminalExpression);assert_eq!((binds,wires),(1,1));

            let wrong_prefix=prepared(&c,copy_bits,true);
            let first=&good.proof.layers[0].rounds[0];let second=&good.proof.layers[0].rounds[1];
            let mut probe=wrong_prefix.clone();
            for _ in 0..14+copy_bits{probe.challenge_scalar(b"gkr-output-coordinate");}
            gkr::append_usize(&mut probe,b"gkr-layer-index",0);
            assert_eq!(gkr::eval_polynomial(first,Fr::zero())+gkr::eval_polynomial(first,Fr::one()),Fr::zero());
            gkr::append_polynomial(&mut probe,b"gkr-sumcheck-polynomial",first);
            let q=probe.challenge_scalar(b"gkr-sumcheck-challenge");
            assert_ne!(gkr::eval_polynomial(first,q),
                gkr::eval_polynomial(second,Fr::zero())+gkr::eval_polynomial(second,Fr::one()),
                "wrong domain must be observable at second message");
            let (bad,t,binds,wires)=verify(&c,owners,&wrong_prefix,&good.proof,false);
            assert_eq!(bad.unwrap_err(),GkrError::SumcheckIdentity);
            assert_eq!((binds,wires),(1,0));assert_eq!(t.challenges(),(15+copy_bits) as u64);

            let mut permuted_t=Transcript::new(DOMAIN);
            let permuted=run(&c,&rows,&prefix,&mut permuted_t,arm,Fault::PermuteValidRows,good.capacity()).unwrap();
            let (verified,_,_,_)=verify(&c,owners,&prefix,&permuted.proof,false);
            assert_eq!(verified.unwrap(),permuted.claim,"valid row permutation still satisfies the relation");
            let flat=flattened(&rows);let observed=gkr::mle(&flat,&permuted.claim.point).unwrap();
            assert_ne!(observed,permuted.claim.value,"wrong logical source must be observable");
            assert_eq!(source_check(&flat,&permuted.claim).unwrap_err(),"r3 ordinary original source MLE differs");
        }
    }
}

    }
}

// Native role3 diagnostic lives under the existing locked-input helpers.
// No public producer dimensions or production point code are changed.
mod role3_native_types {
    use ark_bn254::Fr;
    use ark_serialize::CanonicalSerialize;
    use serde::{Serialize,Serializer,ser::{SerializeMap,SerializeSeq}};
    use crate::sparse_stream_roster::{GroupedVStats,BooleanUPreweightStats};
    pub(super) struct Hex<'a>(pub(super) &'a[u8]);
    impl Serialize for Hex<'_>{fn serialize<S:Serializer>(&self,s:S)->Result<S::Ok,S::Error>{
        if self.0.len()>32{return Err(serde::ser::Error::custom("role3 hex bound"));}let mut bytes=[0u8;64];let digits=b"0123456789ABCDEF";
        for(i,b)in self.0.iter().enumerate(){bytes[2*i]=digits[(b>>4)as usize];bytes[2*i+1]=digits[(b&15)as usize];}
        s.serialize_str(std::str::from_utf8(&bytes[..self.0.len()*2]).map_err(serde::ser::Error::custom)?)} }
    pub(super) struct Scalar(pub(super) Fr);
    impl Serialize for Scalar{fn serialize<S:Serializer>(&self,s:S)->Result<S::Ok,S::Error>{let mut bytes=[0u8;32];
        self.0.serialize_compressed(&mut bytes[..]).map_err(serde::ser::Error::custom)?;Hex(&bytes).serialize(s)}}
    pub(super) struct Scalars<'a>(pub(super) &'a[Fr]);
    impl Serialize for Scalars<'_>{fn serialize<S:Serializer>(&self,s:S)->Result<S::Ok,S::Error>{let mut seq=s.serialize_seq(Some(self.0.len()))?;
        for x in self.0{seq.serialize_element(&Scalar(*x))?;}seq.end()}}
    pub(super) struct Grouped<'a>(pub(super) &'a GroupedVStats);
    impl Serialize for Grouped<'_>{fn serialize<S:Serializer>(&self,s:S)->Result<S::Ok,S::Error>{let g=self.0;let mut m=s.serialize_map(Some(17))?;
        m.serialize_entry("group_count",&g.group_count)?;m.serialize_entry("group_owner_counts",&g.group_owner_counts)?;
        m.serialize_entry("group_term_counts",&g.group_term_counts)?;m.serialize_entry("group_weight_sums",&Scalars(&g.group_weight_sums))?;
        m.serialize_entry("group_d_local_contributions",&Scalars(&g.group_d_local_contributions))?;
        m.serialize_entry("baseline_term_callbacks",&g.baseline_term_callbacks)?;m.serialize_entry("template_term_count",&g.template_term_count)?;
        m.serialize_entry("template_capacity_bytes",&g.template_capacity_bytes)?;m.serialize_entry("bank_term_callbacks",&g.bank_term_callbacks)?;
        m.serialize_entry("handoff_term_callbacks",&g.handoff_term_callbacks)?;m.serialize_entry("grouped_state_peak_capacity_bytes",&g.grouped_state_peak_capacity_bytes)?;
        m.serialize_entry("local_rounds",&g.local_rounds)?;m.serialize_entry("owner_handoff_count",&g.owner_handoff_count)?;
        m.serialize_entry("baseline_elapsed_ns",&g.baseline_elapsed_ns)?;m.serialize_entry("bank_build_elapsed_ns",&g.bank_build_elapsed_ns)?;
        m.serialize_entry("local_v_elapsed_ns",&g.local_v_elapsed_ns)?;m.serialize_entry("owner_handoff_elapsed_ns",&g.owner_handoff_elapsed_ns)?;m.end()}}
    pub(super) struct Boolean<'a>(pub(super) &'a BooleanUPreweightStats);
    impl Serialize for Boolean<'_>{fn serialize<S:Serializer>(&self,s:S)->Result<S::Ok,S::Error>{let b=self.0;let mut m=s.serialize_map(Some(14))?;
        m.serialize_entry("prefix_builds",&b.prefix_builds)?;m.serialize_entry("shared_term_iterations",&b.shared_term_iterations)?;
        m.serialize_entry("owner_term_selections",&b.owner_term_selections)?;m.serialize_entry("boolean_checked_loads",&b.boolean_checked_loads)?;
        m.serialize_entry("boolean_checked_fields",&b.boolean_checked_fields)?;m.serialize_entry("zero_anchor_sweep_skipped",&b.zero_anchor_sweep_skipped)?;
        m.serialize_entry("preweight_entry_size_bytes",&b.preweight_entry_size_bytes)?;m.serialize_entry("preweight_peak_capacity_bytes",&b.preweight_peak_capacity_bytes)?;
        m.serialize_entry("u_state_peak_capacity_bytes",&b.u_state_peak_capacity_bytes)?;m.serialize_entry("u_preflight_capacity_bound_bytes",&b.u_preflight_capacity_bound_bytes)?;
        m.serialize_entry("u_prefix_preweight_elapsed_ns",&b.u_prefix_preweight_elapsed_ns)?;m.serialize_entry("u_owner_selection_elapsed_ns",&b.u_owner_selection_elapsed_ns)?;
        m.serialize_entry("u_x_fold_elapsed_ns",&b.u_x_fold_elapsed_ns)?;m.serialize_entry("u_phase_peak_capacity_bytes",&b.u_phase_peak_capacity_bytes)?;m.end()}}
}

fn general(n:usize,seed:u64)->Vec<Fr> {(0..n).map(|i|Fr::from(seed+3*i as u64+2)).collect()}
fn owner_at(p:&mut[Fr],start:usize,h:usize,owner:usize) {
    for j in 0..h {p[start+j]=Fr::from(((owner>>j)&1) as u64);}
}
/// Low tables bounded by 2^20; the remaining coordinates are small owner/tag tables.
struct Weights {low:Vec<Fr>,high:Vec<Fr>,bits:usize}
impl Weights {
    fn new(p:&[Fr])->Self {let bits=p.len().min(20);
        Self{low:crate::gkr::eq_weights(&p[..bits]),high:crate::gkr::eq_weights(&p[bits..]),bits}}
    fn at(&self,i:usize)->Fr {self.low[i&((1<<self.bits)-1)]*self.high[i>>self.bits]}
}
struct Reference {r:Weights,u:Weights,v:Weights,c:[Fr;4],count:usize}
impl Reference {
    fn new(r:&[Fr],u:&[Fr],v:&[Fr])->Self {Self{r:Weights::new(r),u:Weights::new(u),v:Weights::new(v),c:[Fr::zero();4],count:0}}
    fn add(&mut self,t:Term)->Result<(),String> {
        self.count+=1;let a=self.r.at(t.row);if a.is_zero(){return Ok(());}
        let w=a*self.u.at(t.gate.left)*self.v.at(t.gate.right);
        for (s,c) in self.c.iter_mut().zip([t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3]) {*s+=w*c;}Ok(())
    }
}
fn compare(plan:&NativePrefixAuthPlan<'_>,role:usize,owner:usize,r:&[Fr],u:&[Fr],v:&[Fr])->usize {
    let mut reference=Reference::new(r,u,v);
    let count=plan.visit_role_owner_terms(role,owner as u64,|t|reference.add(t)).unwrap();
    assert_eq!(count,reference.count);
    assert_eq!(plan.coefficients(role,r,u,v).unwrap(),reference.c,"all channels role{role}, owner{owner}");count
}

fn complete_s2() -> usize {
    let public=crate::historical_prefix_public::expected(3).unwrap();
    let parent=WorkTreeHistoryPlan::compile(3,2,public.root,public.total).unwrap();
    let height=HeightWork::compile_history(&parent).unwrap();let daa=DaaHistoryRoster::compile(&parent).unwrap();
    let r=general(22,5);let u=general(22,13);let v=general(22,29);
    let mut reference=Reference::new(&r,&u,&v);
    for owner in 0..4 {visit_composite_owner(&height,&daa,owner,|t|reference.add(t)).unwrap();}
    assert_eq!(reference.count,329122);
    assert_eq!(composite_coefficients(&height,&daa,&r,&u,&v).unwrap(),reference.c);
    assert_ne!(reference.c,[Fr::zero();4]);
    let expected=reference.c;let count=reference.count;drop(reference);
    // Wrong outer row base, isolated from coefficient/challenge changes.
    let mut shifted=Reference::new(&r,&u,&v);
    for owner in 0..4 {height.visit_owner_terms(owner,|t|shifted.add(t)).unwrap();
        daa.visit_owner_terms(owner,|mut t|{t.row+=1<<20;shifted.add(t)}).unwrap();}
    assert_ne!(shifted.c,expected);drop(shifted);
    let mut wrong_tag=r.clone();wrong_tag.swap(20,21);
    assert_ne!(composite_coefficients(&height,&daa,&wrong_tag,&u,&v).unwrap(),expected);
    // General input points remain general even when challenge coordinates are 0/1.
    for tag in [Fr::zero(),Fr::one()] {let mut q=r.clone();q[21]=tag;
        let mut refs=Reference::new(&q,&u,&v);for owner in 0..4 {visit_composite_owner(&height,&daa,owner,|t|refs.add(t)).unwrap();}
        assert_eq!(composite_coefficients(&height,&daa,&q,&u,&v).unwrap(),refs.c);}
    count
}

fn descriptors_and_identity(plan:&NativePrefixAuthPlan<'_>,candidate:&Candidate) {
    plan.validate_roster(plan.descriptors()).unwrap();
    for role in 0..7 {
        let d=&plan.descriptors()[role];assert_eq!((d.input_log,d.row_log),(INPUT_LOGS[role],ROW_LOGS[role]));
        for fault in 0..9 {let mut x=d.clone();match fault {0=>x.role=(role+1)%7,1=>x.name="forged-role",
            2=>x.source="other-source",3=>x.input_log+=1,4=>x.row_log+=1,5=>x.mapping="foreign-owner",
            6=>x.ordered_tags.reverse(),7=>x.public_dependency="unbound-public",_=>x.zero_extension=Some((17,30))};
            // Singleton tag lists need a real isolated tag mutation.
            if fault==6 && x.ordered_tags==d.ordered_tags {x.ordered_tags[0].push_str("-forged");}
            assert!(plan.validate_descriptor(role,&x).is_err());}
    }
    for fault in 0..4 {let mut roster=plan.descriptors().to_vec();match fault {
        0=>{roster.pop();},1=>roster.push(roster[0].clone()),2=>roster.swap(0,1),_=>roster[1]=roster[0].clone()};
        assert!(plan.validate_roster(&roster).is_err());}
    for field in 0..5 {let mut x=candidate.clone();match field {0=>x.n+=1,1=>x.root[0]^=1,
        2=>x.total[0]^=1,3=>x.tip[0]^=1,_=>x.tip_time+=1};assert!(plan.validate_candidate(&x).is_err());}
    for field in 0..9 {let mut s=Selection::s12();match field {0=>s.source=SourceRevision::Unsupported,
        1=>s.rules=Rules::Unsupported,2=>s.genesis[0]^=1,3=>s.query_h-=1,4=>s.ell+=1,
        5=>s.verifier=Verifier::Unsupported,6=>s.encoding=Encoding::Unsupported,7=>s.slot_log+=1,_=>s.point_bank+=1};
        assert!(s.validate().is_err());}
    let base=plan.bound_transcript().unwrap();assert_eq!(base.challenges(),0);
    let mut a=base.clone();let mut b=plan.bound_transcript().unwrap();
    assert_eq!(a.challenge_scalar(b"identity-probe"),b.challenge_scalar(b"identity-probe"));
    assert!(plan.bind_plan_identity(&mut a).is_err());
    for role in 0..7 {let r=general(ROW_LOGS[role],3);let u=general(INPUT_LOGS[role],7);let v=general(INPUT_LOGS[role],19);
        assert!(plan.coefficients(role,&r[..r.len()-1],&u,&v).is_err());
        assert!(plan.coefficients(role,&r,&u[..u.len()-1],&v).is_err());
        assert!(plan.coefficients(role,&r,&u,&v[..v.len()-1]).is_err());
        let mut callbacks=0;assert!(plan.visit_role_owner_terms(role,4096,|_|{callbacks+=1;Ok(())}).is_err());assert_eq!(callbacks,0);}
    assert!(plan.project_claim(7,&[]).is_err());
}

fn raw_point_check(l:&crate::point_membership::Layout,bits:&[bool],pk:[u8;33],w:[u8;33])->Result<(),String> {
    if bits.len()!=8192 {return Err("RAW point assignment width".into());}
    for (role,bytes) in [pk,w].iter().enumerate() {for byte in 0..33 {for bit in 0..8 {
        if bits[l.points[role].bytes[byte][bit]]!=((bytes[byte]>>bit)&1!=0) {
            return Err("RAW point source assignment mismatch".into());
        }
    }}}Ok(())
}

fn projection_and_raw(plan:&NativePrefixAuthPlan<'_>,input:&NativePrefix)->usize {
    let p=general(25,17);let projected=plan.project_claim(3,&p).unwrap();
    assert_eq!(projected.len(),32);assert_eq!(&projected[..13],&p[..13]);assert_eq!(&projected[20..],&p[13..]);
    for bits in [24,26] {assert!(plan.project_claim(3,&general(bits,17)).is_err());}
    let fixed=[0u64,0,0,0,0,1,1].map(Fr::from);assert_eq!(&projected[13..20],&fixed);
    for i in 0..7 {let mut bad=projected.clone();bad[13+i]=Fr::one()-bad[13+i];
        assert_ne!(eq_index(&projected[13..20],96),eq_index(&bad[13..20],96));}
    let compiled=crate::point_membership::build().unwrap();let mut checks=0;
    for owner in [0usize,1,3072,3073,4095] {
        let (height,previous)=plan.padding_heights(owner).unwrap();
        assert_eq!(height,(owner+1).min(3073));assert_eq!(previous,if height==1 {None}else{Some(height-1)});
        let raw=input.raw(height).unwrap();let header=ergo_header_core::Header::decode(raw,None).unwrap();
        assert_eq!(header.encode().unwrap().as_slice(),raw);
        let (pk,w)=match &header.pow {ergo_header_core::PowSolution::V1{pk,w,..}=>(*pk.as_bytes(),*w.as_bytes()),
            _=>panic!("selected legacy point assignment requires V1")};
        let bits=crate::point_membership::witness(pk,w).unwrap();
        raw_point_check(&compiled.layout,&bits,pk,w).unwrap();
        for (role,bytes) in [pk,w].iter().enumerate() {for byte in 0..33 {for bit in 0..8 {
            let local=compiled.layout.points[role].bytes[byte][bit];let expected=(bytes[byte]>>bit)&1!=0;
            assert_eq!(bits[local],expected);assert_eq!(plan.point_global_wire(owner,local).unwrap(),owner*(1<<20)+786432+local);
            // Isolated source-assignment mutants, not a cryptographic rejection.
            let mut mutant=bits.clone();mutant[local]=!mutant[local];
            assert!(raw_point_check(&compiled.layout,&mutant,pk,w).is_err());checks+=1;
        }}}
        if owner>=3073 {assert_eq!(raw,input.raw(3073).unwrap());assert_eq!(previous,Some(3072));
            assert!(pk.iter().any(|x|*x!=0));assert_ne!(pk,[0;33]);
            assert!(raw_point_check(&compiled.layout,&vec![false;8192],pk,w).is_err());
            assert_ne!(plan.point_global_wire(owner,1).unwrap(),plan.point_global_wire(owner-1,1).unwrap());}
    }
    assert!(plan.padding_heights(4096).is_err());assert!(plan.point_global_wire(4096,0).is_err());
    assert!(plan.point_global_wire(0,8192).is_err());checks
}

fn mask_controls() {
    for h in [2usize,12] {
        let hr=6+h;let dr=19+h;let base=vec![Fr::zero();20+h];
        assert_eq!(composite_height_mask(h,&base).unwrap(),Fr::one());
        for bit in hr..dr {
            let mut q=base.clone();q[bit]=Fr::one();
            assert_eq!(composite_height_mask(h,&q).unwrap(),Fr::zero(),"isolated zero-extension bit{bit}");
            q[bit]=Fr::from(2u64);assert_eq!(composite_height_mask(h,&q).unwrap(),-Fr::one());
            q[bit]=Fr::zero();assert_eq!(composite_height_mask(h,&q).unwrap(),Fr::one());
        }
        let mut q=base.clone();q[dr]=Fr::one();assert_eq!(composite_height_mask(h,&q).unwrap(),Fr::zero());
        q[dr]=Fr::from(5u64);assert_eq!(composite_height_mask(h,&q).unwrap(),-Fr::from(4u64));
        q=base.clone();q[hr-1]=Fr::from(9u64);assert_eq!(composite_height_mask(h,&q).unwrap(),Fr::one());
        assert!(composite_height_mask(h,&base[..base.len()-1]).is_err());
    }
}

fn member_range(f:&crate::work_tree_wiring::Family,d:&crate::work_tree_wiring::Descriptor)->(usize,usize) {
    use crate::work_tree_wiring::Mapping;
    match f.mapping {
        Mapping::Same{lo,hi}|Mapping::HeaderSuccessor{lo,hi}|Mapping::FixedRight{lo,hi,..}=>(lo,hi),
        Mapping::Child{level,..}=>{let (lo,n)=d.level(level).unwrap();(lo,lo+n)},
    }
}
fn family_owner_count(f:&crate::work_tree_wiring::Family,d:&crate::work_tree_wiring::Descriptor,owner:usize)->usize {
    let (lo,hi)=member_range(f,d);let c=f.count(d).unwrap();
    assert_eq!(c.endpoint_bits,f.left_wires.len());assert_eq!(c.name,f.name);
    assert_eq!(c.terms,(hi-lo) as u64*c.endpoint_bits as u64);
    if (lo..hi).contains(&owner) {c.endpoint_bits} else {0}
}
fn member_census(plan:&NativePrefixAuthPlan<'_>,parent:&WorkTreeHistoryPlan) {
    use crate::{work_tree_fixed_hash as fixed,work_tree_leaf_hash as leaf,work_tree_work as work};
    let topology=parent.topology();let d=&topology.descriptor;let engine=fixed::engine().unwrap();
    let fixed_count=fixed::count(engine,parent.fixed_profile()).unwrap();
    let leaf_count=leaf::count(engine,parent.leaf_boundary()).unwrap();
    let work_count=work::count(parent.work_boundary()).unwrap();
    let mut global=[0u64;40];let mut owners=std::collections::BTreeSet::from([0usize,1,3071,3072,3073,4095]);
    let mut names=Vec::new();
    for (tag,f) in topology.families.iter().enumerate() {
        global[tag]=f.count(d).unwrap().terms;names.push(f.name.clone());
        let (lo,hi)=member_range(f,d);if lo<hi {owners.insert(lo);owners.insert(hi-1);}
    }
    global[34]=fixed_count.total_boundary_terms;
    global[35]=leaf_count["new_boundary_terms"].as_u64().unwrap();
    global[36]=work_count["new_local_terms"].as_u64().unwrap();
    names.extend(["fixed".into(),"leaf".into(),"work-local".into()]);
    for (index,f) in parent.work_boundary().links().iter().enumerate() {
        global[37+index]=f.count(d).unwrap().terms;names.push(f.name.clone());
        let (lo,hi)=member_range(f,d);if lo<hi {owners.insert(lo);owners.insert(hi-1);}
    }
    assert_eq!(names,plan.descriptors()[2].ordered_tags);
    assert_eq!(global[37..].iter().sum::<u64>(),work_count["new_link_terms"].as_u64().unwrap());
    assert!(owners.len()<=80);let mut covered=[false;40];
    for owner in owners {
        assert!(owner<4096);let mut expected=[0usize;40];
        for (tag,f) in topology.families.iter().enumerate() {expected[tag]=family_owner_count(f,d,owner);}
        // Source-owned local emitters are independently counted, without retaining Terms.
        fixed::emit_slot(engine,parent.fixed_profile(),owner,|_|expected[34]+=1).unwrap();
        parent.leaf_boundary().emit_slot(owner,|_|expected[35]+=1).unwrap();
        parent.work_boundary().emit_slot(owner,|_|expected[36]+=1).unwrap();
        let work_templates=&work_count["local_literal_templates"];
        let work_expected=if owner<d.genuine {work_templates["genuine_terms"].as_u64().unwrap()}
            else if owner<d.leaves {work_templates["padding_terms"].as_u64().unwrap()} else {0};
        assert_eq!(expected[36] as u64,work_expected);
        for (i,f) in parent.work_boundary().links().iter().enumerate() {expected[37+i]=family_owner_count(f,d,owner);}
        let mut observed=[0usize;40];let total=plan.visit_role_owner_terms(2,owner as u64,|t| {
            let tag=t.row>>26;if tag>=40 {return Err("unexpected full-roster tag".into());}
            observed[tag]+=1;Ok(())
        }).unwrap();
        assert_eq!(observed,expected,"source member census owner{owner}");assert_eq!(total,expected.iter().sum::<usize>());
        for tag in 0..40 {if observed[tag]>0 {covered[tag]=true;
            let mut missing=observed;missing[tag]=0;assert_ne!(missing,expected,"omitted member tag{tag}");}}
    }
    for tag in 0..40 {if global[tag]>0 {assert!(covered[tag],"live source member{tag} has no census control");}}
}

fn live_infallible_members(plan:&NativePrefixAuthPlan<'_>,u:&[Fr],v:&[Fr])->usize {
    let mut windows=0;
    for (tag,local) in [(34usize,11usize),(35,14),(36,11)] {
        let mut r=general(32,5);owner_at(&mut r,local,12,1);r[local+12..26].fill(Fr::zero());
        owner_at(&mut r,26,6,tag);
        let mut reference=Reference::new(&r,u,v);let mut selected=0usize;
        plan.visit_role_owner_terms(2,1,|t|{if t.row>>26==tag {selected+=1;}reference.add(t)}).unwrap();
        assert!(selected>0,"infallible member must be live");assert_ne!(reference.c,[Fr::zero();4]);
        assert_eq!(plan.coefficients(2,&r,u,v).unwrap(),reference.c,"live member all channels tag{tag}");
        drop(reference);windows+=1;
        let sentinel=format!("isolated infallible member sink {tag}");let mut selected_invokes=0;
        let result=plan.visit_role_owner_terms(2,1,|t| {
            if t.row>>26==tag {selected_invokes+=1;return Err(sentinel.clone());}Ok(())
        });
        assert_eq!(result.unwrap_err(),sentinel);assert_eq!(selected_invokes,1);
    }
    windows
}

#[test]
#[ignore = "bounded native source-plan differential; one 2GiB/120s group"]
fn source_plan_matches_seven_roles_and_bounded_references() {
    mask_controls();
    let s2_terms=complete_s2(); // All S2 owned templates dropped before S12 construction.
    let input=input();let candidate=Candidate{n:3073,root:input.root(),total:input.total_be28(),
        tip:ergo_header_core::blake2b256(input.raw(3073).unwrap()),tip_time:input.timestamp(3073).unwrap()};
    let parent=WorkTreeHistoryPlan::compile(3073,12,candidate.root,candidate.total).unwrap();
    let plan=NativePrefixAuthPlan::compile(&parent,Selection::s12(),candidate.clone()).unwrap();
    descriptors_and_identity(&plan,&candidate);
    let raw_checks=projection_and_raw(&plan,&input);
    let u=general(32,23);let v=general(32,47);let mut windows=0usize;
    let named=[(0,OwnerClass::Genesis),(1,OwnerClass::Initial),(2,OwnerClass::Carry),
        (1023,OwnerClass::Carry),(1024,OwnerClass::Singleton),(2048,OwnerClass::M1),
        (3072,OwnerClass::Short(crate::short_daa_layout::Profile::M2)),(3073,OwnerClass::Padding),(4095,OwnerClass::Padding)];
    let mut counts=[0usize;8];for owner in 0..4096 {let c=plan.daa().owner_class(owner).unwrap();match c {
        OwnerClass::Genesis=>counts[0]+=1,OwnerClass::Initial=>counts[1]+=1,OwnerClass::Carry=>counts[2]+=1,
        OwnerClass::Singleton=>counts[3]+=1,OwnerClass::M1=>counts[4]+=1,OwnerClass::Short(_)=>counts[5]+=1,
        OwnerClass::Padding=>counts[6]+=1,_=>counts[7]+=1}}
    assert_eq!(counts,[1,1,3068,1,1,1,1023,0]);
    for (owner,class) in named {
        assert_eq!(plan.daa().owner_class(owner as u64).unwrap(),class);
        let mut r=general(32,11);owner_at(&mut r,19,12,owner);r[31]=Fr::one();
        compare(&plan,4,owner,&r,&u,&v);windows+=1;
        let mut r=general(32,11);owner_at(&mut r,5,12,owner);r[17..].fill(Fr::zero());
        compare(&plan,4,owner,&r,&u,&v);windows+=1;
        let mut r=general(32,11);owner_at(&mut r,0,12,owner);r[12..].fill(Fr::zero());r[17]=Fr::one();
        compare(&plan,4,owner,&r,&u,&v);windows+=1;
    }
    // One restricted owner/reference for each remaining role, all four channels.
    let mut r=general(33,5);owner_at(&mut r,17,12,1);compare(&plan,0,1,&r,&u,&v);windows+=1;
    let mut r=general(31,5);owner_at(&mut r,19,12,3072);compare(&plan,1,3072,&r,&u,&v);windows+=1;
    let family=&parent.topology().families[0];let stride=family.left_wires.len().next_power_of_two().trailing_zeros() as usize;
    let mut r=general(32,5);owner_at(&mut r,stride,12,1);r[stride+12..].fill(Fr::zero());
    compare(&plan,2,1,&r,&u,&v);windows+=1;
    let pu=general(25,23);let pv=general(25,47);let mut r=general(26,5);owner_at(&mut r,14,12,4095);
    compare(&plan,3,4095,&r,&pu,&pv);windows+=1;
    for (role,local) in [(5,9),(6,12)] {let mut r=general(ROW_LOGS[role],5);owner_at(&mut r,local,12,3072);
        compare(&plan,role,3072,&r,&u,&v);windows+=1;
        assert_eq!(plan.visit_role_owner_terms(role,3073,|_|Err("padding must not emit".into())).unwrap(),0);}
    windows+=live_infallible_members(&plan,&u,&v);
    member_census(&plan,&parent);
    let mut r=general(32,5);r[31]=Fr::zero();r[18]=Fr::one();
    let h=plan.height().coefficients(&r[..18],&u,&v).unwrap();assert_ne!(h,[Fr::zero();4]);
    assert_eq!(plan.coefficients(4,&r,&u,&v).unwrap(),[Fr::zero();4]); // omitted mask would fail
    let mut invoked=0;assert!(plan.visit_role_owner_terms(2,1,|_|{invoked+=1;Err("isolated sink failure".into())}).is_err());assert_eq!(invoked,1);
    // Isolate wrong helper-owner placement and removal of the foreign import.
    // These are emitted-source differentials, not admitted proof rejections.
    let mut foreign=None;
    plan.daa().visit_owner_terms(3072,|t|{if foreign.is_none() && !t.gate.c1.is_zero() && !t.gate.c2.is_zero()
        && t.gate.left/(1<<20)!=t.gate.right/(1<<20) {foreign=Some(t);}Ok(())}).unwrap();
    let original=foreign.expect("M2 must contain a foreign alias");let mut forged=original.clone();
    forged.gate.right=(original.gate.left/(1<<20))*(1<<20)+forged.gate.right% (1<<20);
    assert_ne!(forged.gate.right/(1<<20),original.gate.right/(1<<20));
    assert_ne!(forged.gate.right,original.gate.right);
    let a=eq_index(&v,original.gate.right);let b=eq_index(&v,forged.gate.right);
    assert_ne!(a*original.gate.c2,b*forged.gate.c2);
    let mut forged_left=original.clone();
    forged_left.gate.left=(original.gate.right/(1<<20))*(1<<20)+original.gate.left% (1<<20);
    assert_ne!(forged_left.gate.left/(1<<20),original.gate.left/(1<<20));
    assert_ne!(forged_left.gate.left,original.gate.left);
    let a=eq_index(&u,original.gate.left);let b=eq_index(&u,forged_left.gate.left);
    assert_ne!(a*original.gate.c1,b*forged_left.gate.c1);
    println!("native_prefix_auth_plan {{\"schema\":\"native-prefix-source-plan-s12-v1\",\"roles\":7,\"input_log\":32,\"owners\":4096,\"s2_terms\":{s2_terms},\"s12_windows\":{windows},\"raw_bit_checks\":{raw_checks},\"full_s12_equivalence\":false,\"proof_verified\":false}}");
}

type EndpointKey=(usize,usize,usize,[[u64;4];4]);
fn endpoint_key(t:&Term)->EndpointKey {
    (t.row,t.gate.left,t.gate.right,[t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3].map(|c|c.into_bigint().0))
}
fn endpoint_sum(reference:&Reference,t:&Term,sum:&mut[Fr;4]) {
    let weight=reference.r.at(t.row)*reference.u.at(t.gate.left)*reference.v.at(t.gate.right);
    for (out,c) in sum.iter_mut().zip([t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3]) {*out+=weight*c;}
}
fn exact_endpoint_sequence(expected:&[EndpointKey],actual:&[EndpointKey])->Result<(),String> {
    if expected!=actual {return Err("endpoint source sequence mismatch".into());}Ok(())
}

fn endpoint_complete_s2() {
    let public=crate::historical_prefix_public::expected(3).unwrap();
    let parent=WorkTreeHistoryPlan::compile(3,2,public.root,public.total).unwrap();
    let height=HeightWork::compile_history(&parent).unwrap();let daa=DaaHistoryRoster::compile(&parent).unwrap();
    let second_parent=WorkTreeHistoryPlan::compile(3,2,public.root,public.total).unwrap();
    let second_height=HeightWork::compile_history(&second_parent).unwrap();
    assert_eq!(second_height.slots(),height.slots());
    assert_eq!(second_height.input_log(),height.input_log());
    assert!(!std::ptr::eq(second_height.endpoint_parent(),daa.endpoint_parent()));
    assert_eq!(Role4EndpointAdapter::new(&second_height,&daa,Role4EndpointScope::CompleteS2)
        .err().expect("distinct equal-geometry parent must reject"),"role4 endpoint parent identity rejected");
    drop(second_height);drop(second_parent);
    let adapter=Role4EndpointAdapter::new(&height,&daa,Role4EndpointScope::CompleteS2).unwrap();
    let binding=adapter.binding();let r=general(22,5);let u=general(22,13);let v=general(22,29);
    let mut reference=Reference::new(&r,&u,&v);let mut canonical=Vec::with_capacity(329122);
    for owner in 0..4 {visit_composite_owner(&height,&daa,owner,|t| {
        canonical.push(endpoint_key(&t));reference.add(t)
    }).unwrap();}
    assert_eq!(reference.count,329122);canonical.sort_unstable();
    assert_eq!(adapter.coefficients(&r,&u,&v).unwrap(),reference.c);
    for left in [true,false] {
        let mut actual=Vec::with_capacity(329122);let mut sum=[Fr::zero();4];let mut total=0;
        for owner in 0..4 {let count=adapter.visit_endpoint(&binding,left,owner,|edge| {
            adapter.check_edge(left,owner,&edge)?;
            actual.push(endpoint_key(&edge.term));endpoint_sum(&reference,&edge.term,&mut sum);Ok(())
        }).unwrap();total+=count;}
        assert_eq!(total,329122);assert_eq!(actual.len(),329122);
        actual.sort_unstable();assert_eq!(actual,canonical,"source multiset with multiplicity, side{left}");
        assert_eq!(sum,reference.c,"all four general-Fr channels, side{left}");
    }
    drop(canonical);drop(reference);
    // Boolean tag boundaries leave both endpoint point vectors general.
    for tag in [Fr::zero(),Fr::one()] {
        let mut q=r.clone();q[21]=tag;let mut reference=Reference::new(&q,&u,&v);
        for owner in 0..4 {visit_composite_owner(&height,&daa,owner,|t|reference.add(t)).unwrap();}
        assert_eq!(adapter.coefficients(&q,&u,&v).unwrap(),reference.c);
        for left in [true,false] {let mut sum=[Fr::zero();4];let mut count=0;
            for owner in 0..4 {count+=adapter.visit_endpoint(&binding,left,owner,|e| {
                endpoint_sum(&reference,&e.term,&mut sum);Ok(())
            }).unwrap();}assert_eq!(count,329122);assert_eq!(sum,reference.c);
        }
    }
    // GLOBAL0 numeric terms remain present separately in Height and DAA rows.
    let mut rows=std::collections::BTreeMap::new();
    adapter.visit_endpoint(&binding,false,0,|e| {
        if e.term.gate.left==0 && !e.term.gate.c0.is_zero() {*rows.entry(e.term.row).or_insert(0usize)+=1;}Ok(())
    }).unwrap();
    assert_eq!(rows.get(&129),Some(&1));assert_eq!(rows.get(&((1<<21)+(1<<19)+(2<<17))),Some(&1));
    let mut calls=0;assert!(adapter.visit_endpoint(&binding,true,4,|_|{calls+=1;Ok(())}).is_err());assert_eq!(calls,0);
    assert!(Role4EndpointAdapter::new(&height,&daa,Role4EndpointScope::NamedM2Aliases).is_err());
}

fn endpoint_named_m2() {
    let input=input();let parent=WorkTreeHistoryPlan::compile(3073,12,input.root(),input.total_be28()).unwrap();
    drop(input);let height=HeightWork::compile_history(&parent).unwrap();let daa=DaaHistoryRoster::compile(&parent).unwrap();
    let adapter=Role4EndpointAdapter::new(&height,&daa,Role4EndpointScope::NamedM2Aliases).unwrap();
    let binding=adapter.binding();let r=general(32,7);let u=general(32,17);let v=general(32,31);
    let mut original=Vec::with_capacity(288);
    daa.visit_owner_terms(3072,|mut t| {
        if (t.row&((1<<19)-1))>>17==1 {t.row+=1usize<<31;original.push(t);}Ok(())
    }).unwrap();assert_eq!(original.len(),288);
    let first=&original[0];assert_eq!(first.row,3758227456);
    assert_eq!(first.gate.left/(1<<20),1023);assert_eq!(first.gate.right/(1<<20),3072);
    assert_eq!([first.gate.c0,first.gate.c1,first.gate.c2,first.gate.c3],[Fr::zero(),Fr::one(),-Fr::one(),Fr::zero()]);
    let mut reference=Reference::new(&r,&u,&v);
    for t in &original {reference.add(t.clone()).unwrap();}
    assert!(!reference.c[1].is_zero() && !reference.c[2].is_zero());
    assert_eq!(adapter.coefficients(&r,&u,&v).unwrap(),reference.c);
    let mut canonical=original.iter().map(endpoint_key).collect::<Vec<_>>();canonical.sort_unstable();
    for left in [true,false] {
        let mut all=Vec::with_capacity(288);let mut sum=[Fr::zero();4];let mut count=0;
        // This is the fixed endpoint-owner roster, not a caller subset of ports.
        for owner in [0usize,1023,2047,3071,3072,4095] {
            let expected=original.iter().filter(|t|if left {t.gate.left/(1<<20)==owner}else{t.gate.right/(1<<20)==owner})
                .map(endpoint_key).collect::<Vec<_>>();
            let mut actual=Vec::new();count+=adapter.visit_endpoint(&binding,left,owner,|e| {
                actual.push(endpoint_key(&e.term));endpoint_sum(&reference,&e.term,&mut sum);Ok(())
            }).unwrap();exact_endpoint_sequence(&expected,&actual).unwrap();all.extend(actual);
        }
        assert_eq!(count,288);all.sort_unstable();assert_eq!(all,canonical);assert_eq!(sum,reference.c);
    }
    // Both first-error paths identify the same original index0 alias.
    for (left,owner,needle) in [(true,1023,"left-source-sentinel"),(false,3072,"right-source-sentinel")] {
        let mut calls=0;let error=adapter.visit_endpoint(&binding,left,owner,|e| {
            calls+=1;assert_eq!(endpoint_key(&e.term),endpoint_key(first));Err(needle.into())
        }).unwrap_err();assert_eq!(error,needle);assert_eq!(calls,1);
    }
    // A source token with one stale field rejects before either side's sink.
    for field in 0..8 {let mut bad=binding.clone();match field {
        0=>bad.scope=Role4EndpointScope::CompleteS2,1=>bad.source="wrong-source",2=>bad.parent_object^=1,
        3=>bad.headers+=1,4=>bad.slot_log-=1,5=>bad.map.as_mut().unwrap()[0]^=1,
        6=>bad.descriptor.as_mut().unwrap()[0]^=1,_=>bad.scope=Role4EndpointScope::WholeS12,
    };for left in [true,false] {let mut calls=0;
        assert!(adapter.visit_endpoint(&bad,left,3072,|_|{calls+=1;Ok(())}).is_err());assert_eq!(calls,0);
    }}
    let index=daa.named_m2_alias_endpoints().unwrap();let (map,descriptor)=index.identity();
    let mut calls=0;assert!(index.visit(crate::short_daa_layout::Profile::M3,map,descriptor,true,1023,|_,_|{calls+=1;Ok(())}).is_err());assert_eq!(calls,0);
    let mut edge=None;adapter.visit_endpoint(&binding,true,1023,|e|{if edge.is_none(){edge=Some(e);}Ok(())}).unwrap();
    let edge=edge.unwrap();
    for field in 0..6 {let mut bad=edge.clone();match field {
        0=>bad.source_slot^=1,1=>bad.family_row^=1<<19,2=>bad.family_row^=1,
        3=>bad.term.row^=1usize<<31,4=>bad.term.gate.left=1usize<<32,_=>bad.term.gate.right=1usize<<32,
    };assert!(adapter.check_edge(true,1023,&bad).is_err());}
    assert!(adapter.check_edge(false,1023,&edge).is_err());
    let mut wrong_right=first.clone();wrong_right.gate.right=(first.gate.left/(1<<20))*(1<<20)+first.gate.right%(1<<20);
    assert_ne!(wrong_right.gate.right,first.gate.right);
    assert_ne!(eq_index(&v,wrong_right.gate.right)*wrong_right.gate.c2,eq_index(&v,first.gate.right)*first.gate.c2);
    let mut wrong_left=first.clone();wrong_left.gate.left=(first.gate.right/(1<<20))*(1<<20)+first.gate.left%(1<<20);
    assert_ne!(wrong_left.gate.left,first.gate.left);
    assert_ne!(eq_index(&u,wrong_left.gate.left)*wrong_left.gate.c1,eq_index(&u,first.gate.left)*first.gate.c1);
    // Transport tuple faults are checked against the independent retained emitter order.
    let expected=original.iter().map(endpoint_key).collect::<Vec<_>>();
    for fault in 0..3 {let mut bad=expected.clone();match fault {
        0=>{bad.remove(0);},1=>bad.insert(0,bad[0]),_=>bad.swap(0,1),
    };assert!(exact_endpoint_sequence(&expected,&bad).is_err());}
    let mut calls=0;assert!(adapter.visit_endpoint(&binding,true,4096,|_|{calls+=1;Ok(())}).is_err());assert_eq!(calls,0);
    let whole=Role4EndpointAdapter::new(&height,&daa,Role4EndpointScope::WholeS12);
    assert!(whole.is_ok()); // Exact generic same-parent3073/S12 scope is now admitted.
    assert_eq!(calls,0);
    assert!(Role4EndpointAdapter::new(&height,&daa,Role4EndpointScope::CompleteS2).is_err());
}

#[test]
#[ignore = "source-only endpoint differential; one bounded 2GiB/120s aggregate"]
fn role4_endpoint_adapter_matches_complete_s2_and_named_m2_window() {
    source_plan_matches_seven_roles_and_bounded_references();
    endpoint_complete_s2(); // All S2 constructors, tuple vectors and weights drop here.
    endpoint_named_m2();
    println!("role4_endpoint_adapter {{\"schema\":\"role4-source-endpoint-s2-m2-v1\",\"s2_terms_per_side\":329122,\"m2_aliases_per_side\":288,\"full_s12_equivalence\":false,\"proof_verified\":false}}");
}

fn endpoint_named_m1() {
    {
        let public=crate::historical_prefix_public::expected(3).unwrap();
        let small=WorkTreeHistoryPlan::compile(3,2,public.root,public.total).unwrap();
        let small_height=HeightWork::compile_history(&small).unwrap();let small_daa=DaaHistoryRoster::compile(&small).unwrap();
        let mut wrong_scope=Role4EndpointAdapter::new(&small_height,&small_daa,Role4EndpointScope::NamedM1Aliases);
        assert_eq!(wrong_scope.as_ref().err().expect("M1 requires its fixed geometry"),"role4 endpoint relation scope unsupported");
        let mut calls=0;if let Ok(ref mut source)=wrong_scope {source.visit_endpoint(&source.binding(),true,0,|_|{calls+=1;Ok(())}).unwrap();}
        assert_eq!(calls,0);
    } // Wrong-geometry constructors drop before the full S12 parent.
    let input=input();let root=input.root();let total=input.total_be28();
    let parent=WorkTreeHistoryPlan::compile(3073,12,root,total).unwrap();drop(input);
    let height=HeightWork::compile_history(&parent).unwrap();let daa=DaaHistoryRoster::compile(&parent).unwrap();
    let adapter=Role4EndpointAdapter::new(&height,&daa,Role4EndpointScope::NamedM1Aliases).unwrap();
    let binding=adapter.binding();
    // The retained S2 test exercises the common pre-dispatch guard with two
    // equal-geometry parent objects; no second full S12 parent is retained here.
    {
        let wrong_geometry=crate::one_daa_layout::OneDaaLayout::compile(2049,12).unwrap();
        assert!(wrong_geometry.m1_endpoint_index().is_err());
        assert!(crate::one_daa_layout::OneDaaLayout::compile(3073,13).is_err());
    }
    assert_eq!(daa.owner_class(2048),Ok(OwnerClass::M1));
    let mut original=Vec::with_capacity(192);
    daa.visit_owner_terms(2048,|mut t| {
        if (t.row&((1<<19)-1))>>17==1 {t.row+=1usize<<31;original.push(t);}Ok(())
    }).unwrap();assert_eq!(original.len(),192);
    let first=&original[0];assert_eq!(first.row,3221356544);
    assert_eq!(first.gate.left/(1<<20),1023);assert_eq!(first.gate.right/(1<<20),2048);
    for (i,t) in original.iter().enumerate() {
        assert_eq!(t.row,3221356544+i);assert_eq!(t.gate.right/(1<<20),2048);
        let owner=if i<64 {1023}else if i<160 {2047}else{2048};
        assert_eq!(t.gate.left/(1<<20),owner);
        assert_eq!([t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3],[Fr::zero(),Fr::one(),-Fr::one(),Fr::zero()]);
    }
    let r=general(32,7);let u=general(32,17);let v=general(32,31);
    let mut reference=Reference::new(&r,&u,&v);
    for t in &original {reference.add(t.clone()).unwrap();}
    assert!(!reference.c[1].is_zero() && !reference.c[2].is_zero());
    assert_eq!(reference.c[0],Fr::zero());assert_eq!(reference.c[3],Fr::zero());
    assert_eq!(adapter.coefficients(&r,&u,&v).unwrap(),reference.c);
    let mut canonical=original.iter().map(endpoint_key).collect::<Vec<_>>();canonical.sort_unstable();
    for left in [true,false] {
        let mut all=Vec::with_capacity(192);let mut sum=[Fr::zero();4];let mut count=0;
        for owner in [0usize,1023,2047,2048,4095] {
            let expected=original.iter().filter(|t|if left {t.gate.left/(1<<20)==owner}else{t.gate.right/(1<<20)==owner})
                .map(endpoint_key).collect::<Vec<_>>();
            let mut actual=Vec::new();let seen=adapter.visit_endpoint(&binding,left,owner,|e| {
                assert_eq!(e.source_slot,2048);assert_eq!(e.family_row,(1<<19)+(1<<17)+(e.term.row&255));
                actual.push(endpoint_key(&e.term));endpoint_sum(&reference,&e.term,&mut sum);Ok(())
            }).unwrap();
            let expected_count=if left {match owner {1023=>64,2047=>96,2048=>32,_=>0}}
                else if owner==2048 {192}else{0};
            assert_eq!(seen,expected_count);exact_endpoint_sequence(&expected,&actual).unwrap();
            count+=seen;all.extend(actual);
        }
        assert_eq!(count,192);all.sort_unstable();assert_eq!(all,canonical);assert_eq!(sum,reference.c);
    }
    // Direct scalar sums exercise 0/1 points without allocating further weight tables.
    let scalar=|q:&[Fr]| {
        let mut sum=[Fr::zero();4];for t in &original {
            let w=eq_index(q,t.row)*eq_index(&u,t.gate.left)*eq_index(&v,t.gate.right);
            for (s,c) in sum.iter_mut().zip([t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3]) {*s+=w*c;}
        }sum
    };
    for bit in [Fr::zero(),Fr::one()] {let q=vec![bit;32];assert_eq!(adapter.coefficients(&q,&u,&v).unwrap(),scalar(&q));}
    let mut active=r.clone();for x in &mut active[8..17] {*x=Fr::zero();}
    active[17]=Fr::one();active[18]=Fr::zero();active[31]=Fr::one();
    assert!(!scalar(&active)[1].is_zero());assert_eq!(adapter.coefficients(&active,&u,&v).unwrap(),scalar(&active));
    for bit in 8..17 {let mut padded=active.clone();padded[bit]=Fr::one();
        assert_eq!(scalar(&padded),[Fr::zero();4]);assert_eq!(adapter.coefficients(&padded,&u,&v).unwrap(),[Fr::zero();4]);}
    let mut unused=active.clone();owner_at(&mut unused,0,8,192);owner_at(&mut unused,19,12,2048);
    assert_eq!(scalar(&unused),[Fr::zero();4]);assert_eq!(adapter.coefficients(&unused,&u,&v).unwrap(),[Fr::zero();4]);
    for dimension in 0..3 {for length in [31usize,33] {
        let mut qr=r.clone();let mut qu=u.clone();let mut qv=v.clone();
        match dimension {0=>qr.resize(length,Fr::one()),1=>qu.resize(length,Fr::one()),_=>qv.resize(length,Fr::one())};
        assert!(adapter.coefficients(&qr,&qu,&qv).is_err());
    }}
    for (left,owner,needle) in [(true,1023,"M1-left-source-sentinel"),(false,2048,"M1-right-source-sentinel")] {
        let mut calls=0;let error=adapter.visit_endpoint(&binding,left,owner,|e| {
            calls+=1;assert_eq!(endpoint_key(&e.term),endpoint_key(first));Err(needle.into())
        }).unwrap_err();assert_eq!(error,needle);assert_eq!(calls,1);
    }
    for field in 0..9 {let mut bad=binding.clone();match field {
        0=>bad.scope=Role4EndpointScope::CompleteS2,1=>bad.source="wrong-source",2=>bad.parent_object^=1,
        3=>bad.headers+=1,4=>bad.slot_log-=1,5=>bad.map.as_mut().unwrap()[0]^=1,
        6=>bad.descriptor.as_mut().unwrap()[0]^=1,7=>bad.scope=Role4EndpointScope::NamedM2Aliases,
        _=>bad.scope=Role4EndpointScope::WholeS12,
    };for left in [true,false] {let mut calls=0;
        assert!(adapter.visit_endpoint(&bad,left,2048,|_|{calls+=1;Ok(())}).is_err());assert_eq!(calls,0);
    }}
    let index=daa.named_m1_alias_endpoints().unwrap();let (map,descriptor)=index.identity();
    for i in 0..192 {let mut expected=index.term(i).unwrap();expected.row+= (1usize<<31)+(2048usize<<19)+(1<<17)-(2048<<8);
        assert_eq!(endpoint_key(&expected),endpoint_key(&original[i]));}
    assert_eq!(index.term(192).err().expect("out-of-range alias"),"M1 alias index outside source");
    for field in 0..4 {let mut wrong_map=map;let mut wrong_descriptor=descriptor;
        let profile=if field==0 {b"wrong-profile".as_slice()}else{crate::one_daa_layout::M1_ENDPOINT_PROFILE};
        if field==1 {wrong_map[0]^=1;}if field==2 {wrong_descriptor[0]^=1;}
        let owner=if field==3 {4096}else{1023};
        for left in [true,false] {let mut calls=0;
            assert!(index.visit(profile,wrong_map,wrong_descriptor,left,owner,|_,_|{calls+=1;Ok(())}).is_err());assert_eq!(calls,0);
        }
    }
    let mut edge=None;adapter.visit_endpoint(&binding,true,1023,|e|{if edge.is_none(){edge=Some(e);}Ok(())}).unwrap();
    let edge=edge.unwrap();
    for field in 0..6 {let mut bad=edge.clone();match field {
        0=>bad.source_slot^=1,1=>bad.family_row^=1<<19,2=>bad.family_row^=1,
        3=>bad.term.row^=1usize<<31,4=>bad.term.gate.left=1usize<<32,_=>bad.term.gate.right=1usize<<32,
    };assert!(adapter.check_edge(true,1023,&bad).is_err());}
    assert!(adapter.check_edge(false,1023,&edge).is_err());
    let mut wrong_left=first.clone();wrong_left.gate.left=(first.gate.right/(1<<20))*(1<<20)+first.gate.left%(1<<20);
    assert_ne!(wrong_left.gate.left,first.gate.left);assert_ne!(wrong_left.gate.left/(1<<20),first.gate.left/(1<<20));
    assert_eq!(wrong_left.gate.left%(1<<20),first.gate.left%(1<<20));
    assert_ne!(eq_index(&u,wrong_left.gate.left)*wrong_left.gate.c1,eq_index(&u,first.gate.left)*first.gate.c1);
    let mut wrong_right=first.clone();wrong_right.gate.right=(first.gate.left/(1<<20))*(1<<20)+first.gate.right%(1<<20);
    assert_ne!(wrong_right.gate.right,first.gate.right);assert_ne!(wrong_right.gate.right/(1<<20),first.gate.right/(1<<20));
    assert_eq!(wrong_right.gate.right%(1<<20),first.gate.right%(1<<20));
    assert_ne!(eq_index(&v,wrong_right.gate.right)*wrong_right.gate.c2,eq_index(&v,first.gate.right)*first.gate.c2);
    let expected=original.iter().map(endpoint_key).collect::<Vec<_>>();
    for fault in 0..3 {let mut bad=expected.clone();match fault {
        0=>{bad.remove(0);},1=>bad.insert(0,bad[0]),_=>bad.swap(0,1),
    };assert!(exact_endpoint_sequence(&expected,&bad).is_err());}
    let mut calls=0;assert!(adapter.visit_endpoint(&binding,true,4096,|_|{calls+=1;Ok(())}).is_err());assert_eq!(calls,0);
    let whole=Role4EndpointAdapter::new(&height,&daa,Role4EndpointScope::WholeS12);
    assert!(whole.is_ok()); // Exact generic same-parent3073/S12 scope is now admitted.
    assert_eq!(calls,0);
    assert!(Role4EndpointAdapter::new(&height,&daa,Role4EndpointScope::CompleteS2).is_err());
}

#[test]
#[ignore = "source-only M1 plus retained dispatch; one bounded 2GiB/120s aggregate"]
fn role4_m1_endpoint_adapter_matches_named_window_and_retained_dispatch() {
    role4_endpoint_adapter_matches_complete_s2_and_named_m2_window();
    endpoint_named_m1(); // Parent/reference/index allocations drop before the scoped report.
    println!("role4_m1_endpoint_adapter {{\"schema\":\"role4-source-endpoint-m1-v1\",\"m1_aliases_per_side\":192,\"full_s12_equivalence\":false,\"proof_verified\":false}}");
}


// Whole S12: source membership and multiplicity only; no witness or proof.
const WHOLE_BATCH:usize=1024;
const WHOLE_STACK:usize=8*1024*1024;
const WHOLE_CONTROL_NAMES:[&str;23]=[
    "missing","duplicate","constant_missing","constant_duplicate","coefficient",
    "foreign_endpoint","row","family","binding_scope","binding_source","binding_parent",
    "binding_headers","binding_slot_log","binding_map","binding_descriptor",
    "binding_m1_map","binding_m1_descriptor","binding_m2_map","binding_m2_descriptor",
    "owner_bound","subset_routing","worker_error","receiver_drop",
];
#[derive(Clone,Debug,PartialEq,Eq)]
struct OracleTuple {
    source_slot:usize,family_row:usize,row:usize,left:usize,right:usize,c:[Fr;4],
}
impl OracleTuple {
    fn canonical(family:usize,t:Term)->Result<Self,String> {
        if family>1 || t.row>=1usize<<32 || t.gate.left>=1usize<<32 || t.gate.right>=1usize<<32 {
            return Err("oracle canonical tuple dimensions".into());
        }
        let low=t.row.checked_sub(family*(1usize<<31)).filter(|x|*x<1usize<<31)
            .ok_or("oracle canonical family row")?;
        // ROW owner, deliberately independent of canonical header visitor owner.
        Ok(Self{source_slot:low>>19,family_row:(family<<19)|(low&((1<<19)-1)),
            row:t.row,left:t.gate.left,right:t.gate.right,
            c:[t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3]})
    }
    fn candidate(e:crate::sparse_stream_roster::EdgeTerm)->Self {
        Self{source_slot:e.source_slot,family_row:e.family_row,row:e.term.row,
            left:e.term.gate.left,right:e.term.gate.right,
            c:[e.term.gate.c0,e.term.gate.c1,e.term.gate.c2,e.term.gate.c3]}
    }
}
fn whole_require(ok:bool,message:&str)->Result<(),String> {
    if ok {Ok(())} else {Err(message.into())}
}
fn whole_sequence(expected:&[OracleTuple],actual:&[OracleTuple])->Result<(),String> {
    // Tiny controls use the SAME batched reader/EOF and worker cleanup as census.
    whole_joined(|tx| {
        whole_send(tx,WholeMessage::Begin(true,0))?;
        let mut batch=WholeBatcher::new(tx);
        for t in expected {batch.add(t.clone())?;}
        batch.finish()?;whole_send(tx,WholeMessage::Done)
    },|reader| {
        reader.begin(true,0)?;
        for t in actual {reader.compare(t)?;}
        reader.end(actual.len())?;reader.done()
    })
}
fn whole_aliases(daa:&DaaHistoryRoster<'_>)->Result<Vec<OracleTuple>,String> {
    let mut out=Vec::with_capacity(480);
    for (owner,required) in [(2048u64,192usize),(3072,288)] {
        let before=out.len();
        daa.visit_owner_terms(owner,|mut t| {
            if ((t.row&((1<<19)-1))>>17)==1 {
                whole_require(out.len()<480,"canonical alias cache overflow")?;
                t.row+=1usize<<31;out.push(OracleTuple::canonical(1,t)?);
            }
            Ok(())
        })?;
        whole_require(out.len()-before==required,"canonical alias occurrence count")?;
    }
    whole_require(out.len()==480 && out.capacity()<=480,"canonical alias cache capacity")?;
    Ok(out)
}
fn whole_numeric(numeric:&crate::daa_work_actions::DaaWorkActions<'_>,left:bool,owner:usize,
    mut sink:impl FnMut(Term)->Result<(),String>)->Result<(),String> {
    // Only canonical visit_owner, never the candidate inverse visitor.
    if !left {
        if owner==0 {for source in 1..3073 {numeric.visit_owner(source,&mut sink)?;}}
    } else {
        for delta in [1usize,2] {
            if let Some(source)=owner.checked_add(delta).filter(|x|*x<4096) {
                numeric.visit_owner(source,|t| {
                    if t.gate.left!=0 && t.gate.left/(1<<20)==owner {sink(t)?;}
                    Ok(())
                })?;
            }
        }
        if owner==0 {numeric.visit_owner(1,|t| {if t.gate.left==0 {sink(t)?;}Ok(())})?;}
    }
    Ok(())
}
fn whole_oracle_partition(height:&HeightWork<'_>,daa:&DaaHistoryRoster<'_>,
    numeric:&crate::daa_work_actions::DaaWorkActions<'_>,aliases:&[OracleTuple],
    left:bool,owner:usize,mut sink:impl FnMut(OracleTuple)->Result<(),String>)->Result<(),String> {
    height.visit_owner_terms(owner as u64,|t| {
        if t.row<32*4096 {sink(OracleTuple::canonical(0,t)?)?;}Ok(())
    })?;
    whole_numeric(numeric,left,owner,|mut t| {
        t.row+=32*4096;sink(OracleTuple::canonical(0,t)?)
    })?;
    // One canonical local-owner traversal. Insert the foreign alias/numeric
    // fragments at the arithmetic/inactive boundary, without buffering locals.
    let mut middle=false;
    let mut emit_middle=|sink:&mut dyn FnMut(OracleTuple)->Result<(),String>| {
        for t in aliases {
            if (if left {t.left}else{t.right})/(1<<20)==owner {sink(t.clone())?;}
        }
        whole_numeric(numeric,left,owner,|mut t| {
            t.row=(1usize<<31)+(t.row<<19)+(2<<17);
            sink(OracleTuple::canonical(1,t)?)
        })
    };
    daa.visit_owner_terms(owner as u64,|mut t| {
        let lane=(t.row&((1<<19)-1))>>17;
        if lane!=0 && !middle {emit_middle(&mut sink)?;middle=true;}
        if lane==0 || lane==3 {t.row+=1usize<<31;sink(OracleTuple::canonical(1,t)?)?;}
        Ok(())
    })?;
    if !middle {emit_middle(&mut sink)?;}
    Ok(())
}
fn whole_source_census(height:&HeightWork<'_>,daa:&DaaHistoryRoster<'_>,
    aliases:&[OracleTuple],a2:usize)->Result<u64,String> {
    let mut height_count=0u64;let mut height_numeric=0u64;let mut lanes=[0u64;4];
    let mut alias_cursor=0usize;
    for owner in 0..4096usize {
        height.visit_owner_terms(owner as u64,|t| {
            if t.row<32*4096 {
                whole_require(t.row/32==owner && t.gate.left/(1<<20)==owner
                    && t.gate.right/(1<<20)==owner,"canonical height owner subset")?;
                height_count+=1;
            } else {
                whole_require(t.row==32*4096+owner && t.gate.right==0
                    && (t.gate.left==0 && owner==1 || t.gate.left!=0
                        && matches!(owner.checked_sub(t.gate.left/(1<<20)),Some(1)|Some(2))),
                    "canonical height numeric owner subset")?;
                height_numeric+=1;
            }
            Ok(())
        })?;
        daa.visit_owner_terms(owner as u64,|mut t| {
            whole_require(t.row>>19==owner,"canonical DAA row owner")?;
            let lane=(t.row&((1<<19)-1))>>17;lanes[lane]+=1;
            match lane {
                0|3=>whole_require(t.gate.left/(1<<20)==owner && t.gate.right/(1<<20)==owner,
                    "canonical local DAA owner subset")?,
                1=>{
                    whole_require(matches!(owner,2048|3072),"canonical alias source universe")?;
                    t.row+=1usize<<31;
                    let tuple=OracleTuple::canonical(1,t)?;
                    whole_require(aliases.get(alias_cursor)==Some(&tuple),"canonical global alias cache coverage")?;
                    alias_cursor+=1;
                },
                2=>whole_require(t.gate.right==0 && (t.gate.left==0 && owner==1
                    || t.gate.left!=0 && matches!(owner.checked_sub(t.gate.left/(1<<20)),Some(1)|Some(2))),
                    "canonical DAA numeric owner subset")?,
                _=>return Err("canonical DAA lane".into()),
            }
            Ok(())
        })?;
    }
    whole_require(height_count==98336 && height_numeric==1375137
        && lanes==[44729+a2 as u64,480,1375137,335454208] && alias_cursor==480,
        "canonical global family counts")?;
    Ok(height_count+height_numeric+lanes.iter().sum::<u64>())
}

enum WholeMessage {CanonicalTotal(u64),Begin(bool,usize),Batch(Vec<OracleTuple>),End(u64),Done}
fn whole_send(tx:&std::sync::mpsc::SyncSender<WholeMessage>,message:WholeMessage)->Result<(),String> {
    tx.send(message).map_err(|_|"whole S12 receiver closed".into())
}
struct WholeBatcher<'a> {
    tx:&'a std::sync::mpsc::SyncSender<WholeMessage>,batch:Vec<OracleTuple>,count:u64,
}
impl<'a> WholeBatcher<'a> {
    fn new(tx:&'a std::sync::mpsc::SyncSender<WholeMessage>)->Self {
        Self{tx,batch:Vec::with_capacity(WHOLE_BATCH),count:0}
    }
    fn flush(&mut self)->Result<(),String> {
        if self.batch.is_empty() {return Ok(());}
        whole_require(self.batch.capacity()<=WHOLE_BATCH,"producer batch capacity")?;
        // take leaves ZERO capacity while send blocks. Allocate only on return.
        let outgoing=std::mem::take(&mut self.batch);
        whole_send(self.tx,WholeMessage::Batch(outgoing))?;
        self.batch=Vec::with_capacity(WHOLE_BATCH);Ok(())
    }
    fn add(&mut self,t:OracleTuple)->Result<(),String> {
        whole_require(self.batch.len()<WHOLE_BATCH,"producer batch size")?;
        self.batch.push(t);self.count+=1;
        if self.batch.len()==WHOLE_BATCH {self.flush()?;}Ok(())
    }
    fn finish(mut self)->Result<(),String> {
        self.flush()?;whole_send(self.tx,WholeMessage::End(self.count))
    }
}
struct WholeReader {
    rx:std::sync::mpsc::Receiver<WholeMessage>,batch:Vec<OracleTuple>,offset:usize,max_capacity:usize,
}
impl WholeReader {
    fn message(&self)->Result<WholeMessage,String> {
        self.rx.recv().map_err(|_|"whole S12 unexpected producer EOF".into())
    }
    fn begin(&mut self,left:bool,owner:usize)->Result<(),String> {
        whole_require(self.batch.is_empty(),"retained partition batch")?;
        match self.message()? {
            WholeMessage::Begin(a,b) if (a,b)==(left,owner)=>Ok(()),
            _=>Err("whole S12 partition order".into()),
        }
    }
    fn compare(&mut self,actual:&OracleTuple)->Result<(),String> {
        if self.offset==self.batch.len() {
            // Drop consumed capacity BEFORE recv can unblock the producer.
            self.batch=Vec::new();self.offset=0;
            match self.message()? {
                WholeMessage::Batch(batch)=>{
                    whole_require(!batch.is_empty() && batch.len()<=WHOLE_BATCH
                        && batch.capacity()<=WHOLE_BATCH,"receiver batch capacity")?;
                    self.max_capacity=self.max_capacity.max(batch.capacity());self.batch=batch;
                },
                _=>return Err("whole S12 unexpected end/missing expected tuple".into()),
            }
        }
        whole_require(self.batch[self.offset]==*actual,"whole S12 exact tuple mismatch")?;
        self.offset+=1;Ok(())
    }
    fn end(&mut self,count:usize)->Result<(),String> {
        whole_require(self.offset==self.batch.len(),"whole S12 extra expected tuples")?;
        self.batch=Vec::new();self.offset=0;
        match self.message()? {
            WholeMessage::End(n) if n==count as u64=>Ok(()),
            _=>Err("whole S12 partition count/EOF mismatch".into()),
        }
    }
    fn done(&mut self)->Result<(),String> {
        match self.message()? {WholeMessage::Done=>(),_=>return Err("whole S12 missing completion".into())}
        whole_require(self.rx.recv().is_err(),"whole S12 trailing producer message")
    }
}
fn whole_joined<P,C,T>(producer:P,consumer:C)->Result<T,String>
where P:FnOnce(&std::sync::mpsc::SyncSender<WholeMessage>)->Result<(),String>+Send,
    C:FnOnce(&mut WholeReader)->Result<T,String> {
    std::thread::scope(|scope| {
        let (tx,rx)=std::sync::mpsc::sync_channel(2);
        let worker=std::thread::Builder::new().name("whole-s12-oracle".into()).stack_size(WHOLE_STACK)
            .spawn_scoped(scope,move||producer(&tx)).map_err(|_|"whole S12 worker spawn")?;
        let mut reader=WholeReader{rx,batch:Vec::new(),offset:0,max_capacity:0};
        let result=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||consumer(&mut reader)))
            .unwrap_or_else(|_|Err("whole S12 consumer panic".into()));
        // Always destroy ALL receiver/buffer ownership before join, even on panic.
        drop(reader);
        let joined=worker.join().unwrap_or_else(|_|Err("whole S12 producer panic".into()));
        match (result,joined) {
            (Ok(value),Ok(()))=>Ok(value),
            (Err(a),Err(b))=>Err(format!("{a}; producer:{b}")),
            (Err(a),_)=>Err(a),(_,Err(b))=>Err(b),
        }
    })
}
fn whole_weight(t:&OracleTuple,r:&[Fr],u:&[Fr],v:&[Fr])->Fr {
    eq_index(r,t.row)*eq_index(u,t.left)*eq_index(v,t.right)
}
fn whole_controls(height:&HeightWork<'_>,daa:&DaaHistoryRoster<'_>,
    adapter:&Role4EndpointAdapter<'_,'_>,aliases:&[OracleTuple],
    results:&mut std::collections::BTreeMap<&'static str,bool>)->Result<(),String> {
    macro_rules! passed {($name:expr,$condition:expr)=>{{
        whole_require($condition,concat!("whole S12 control ",$name))?;
        results.insert($name,true);
    }}}
    whole_require(aliases.len()==480,"controls alias baseline")?;
    let baseline=aliases[..2].to_vec();whole_sequence(&baseline,&baseline)?;
    passed!("missing",whole_sequence(&baseline,&baseline[..1]).is_err());
    let mut duplicate=baseline.clone();duplicate.insert(0,baseline[0].clone());
    passed!("duplicate",whole_sequence(&baseline,&duplicate).is_err());
    let numeric=crate::daa_work_actions::DaaWorkActions::new(height.endpoint_parent())?;
    let mut constant=None;
    numeric.visit_owner(1,|mut t| {
        if t.gate.left==0 {t.row+=32*4096;constant=Some(OracleTuple::canonical(0,t)?);}Ok(())
    })?;
    let constant=constant.ok_or("canonical genesis constant absent")?;
    whole_sequence(std::slice::from_ref(&constant),std::slice::from_ref(&constant))?;
    passed!("constant_missing",whole_sequence(std::slice::from_ref(&constant),&[]).is_err());
    passed!("constant_duplicate",whole_sequence(std::slice::from_ref(&constant),
        &[constant.clone(),constant.clone()]).is_err());
    let r=general(32,5);let u=general(32,13);let v=general(32,29);
    let first=aliases.iter().find(|t|t.left/(1<<20)!=t.right/(1<<20)
        && !t.c[1].is_zero() && !t.c[2].is_zero()).ok_or("nonvacuous foreign alias absent")?;
    let mut coefficient=first.clone();coefficient.c[1]+=Fr::one();
    passed!("coefficient",whole_sequence(std::slice::from_ref(first),&[coefficient.clone()]).is_err()
        && whole_weight(first,&r,&u,&v)*first.c[1]!=whole_weight(&coefficient,&r,&u,&v)*coefficient.c[1]);
    let mut foreign=first.clone();foreign.right=(first.left/(1<<20))*(1<<20)+first.right%(1<<20);
    passed!("foreign_endpoint",foreign.right!=first.right
        && whole_sequence(std::slice::from_ref(first),&[foreign.clone()]).is_err()
        && whole_weight(first,&r,&u,&v)*first.c[2]!=whole_weight(&foreign,&r,&u,&v)*foreign.c[2]);
    let mut row=first.clone();row.row^=1;
    passed!("row",whole_sequence(std::slice::from_ref(first),&[row.clone()]).is_err()
        && whole_weight(first,&r,&u,&v)*first.c[1]!=whole_weight(&row,&r,&u,&v)*row.c[1]);
    let mut family=first.clone();family.family_row^=1<<19;
    passed!("family",whole_sequence(std::slice::from_ref(first),&[family]).is_err());
    let binding=adapter.binding();
    let binding_names=["binding_scope","binding_source","binding_parent","binding_headers","binding_slot_log",
        "binding_map","binding_descriptor","binding_m1_map","binding_m1_descriptor","binding_m2_map","binding_m2_descriptor"];
    for (fault,name) in binding_names.into_iter().enumerate() {
        let mut bad=binding.clone();
        match fault {
            0=>bad.scope=Role4EndpointScope::NamedM1Aliases,1=>bad.source="wrong-source",2=>bad.parent_object^=1,
            3=>bad.headers+=1,4=>bad.slot_log+=1,
            5=>bad.map.as_mut().ok_or("whole binding map absent")?[0]^=1,
            6=>bad.descriptor.as_mut().ok_or("whole binding descriptor absent")?[0]^=1,
            7..=10=>{let index=fault-7;bad.whole_alias_identities.as_mut().ok_or("whole identities absent")?
                [index/2][index%2][0]^=1;},
            _=>unreachable!(),
        }
        let mut calls=0;
        whole_require(adapter.visit_endpoint(&bad,true,0,|_|{calls+=1;Ok(())}).is_err() && calls==0,
            "whole S12 binding guard/zero callbacks")?;
        results.insert(name,true);
    }
    let mut calls=0;
    passed!("owner_bound",adapter.visit_endpoint(&binding,true,4096,|_|{calls+=1;Ok(())}).is_err() && calls==0);
    // Exhaust the cheap numeric source universe and every schedule class, rather
    // than assuming the samples enumerate possible foreign source owners.
    let mut numeric_count=0usize;let mut constants=0;let mut classes=[0usize;7];
    for owner in 0..4096usize {
        let class=match daa.owner_class(owner as u64)? {
            OwnerClass::Genesis=>0,OwnerClass::Initial=>1,OwnerClass::Carry=>2,
            OwnerClass::Singleton=>3,OwnerClass::M1=>4,
            OwnerClass::Short(crate::short_daa_layout::Profile::M2)=>5,OwnerClass::Padding=>6,
            _=>return Err("whole S12 unexpected source owner class".into()),
        };classes[class]+=1;
        numeric_count+=numeric.visit_owner(owner,|t| {
            whole_require(t.row==owner && t.gate.right==0 && t.gate.c2.is_zero() && t.gate.c3.is_zero(),
                "numeric canonical row/right/channel subset")?;
            if t.gate.left==0 {
                whole_require(owner==1 && !t.gate.c0.is_zero() && t.gate.c1.is_zero(),"numeric constant universe")?;
                constants+=1;
            } else {
                whole_require(t.gate.left<(1usize<<32)
                    && matches!(owner.checked_sub(t.gate.left/(1<<20)),Some(1)|Some(2)),
                    "numeric foreign owner universe")?;
            }
            Ok(())
        })?;
    }
    // Constructor rejects wrong geometry and distinct immutable parent objects.
    {
        let public=crate::historical_prefix_public::expected(3)?;
        let small=WorkTreeHistoryPlan::compile(3,2,public.root,public.total)?;
        let small_height=HeightWork::compile_history(&small)?;
        let small_daa=DaaHistoryRoster::compile(&small)?;
        whole_require(Role4EndpointAdapter::new(&small_height,&small_daa,Role4EndpointScope::WholeS12).is_err()
            && Role4EndpointAdapter::new(&small_height,daa,Role4EndpointScope::WholeS12).is_err(),
            "whole S12 constructor geometry/parent guards")?;
    }
    passed!("subset_routing",numeric_count==1375137 && constants==1
        && classes==[1,1,3068,1,1,1,1023] && aliases.iter().all(|t|
            t.left<(1usize<<32) && t.right<(1usize<<32) && matches!(t.source_slot,2048|3072)));
    let worker_error=whole_joined(|_|Err("worker-error-sentinel".into()),
        |reader|reader.begin(true,0)).err().ok_or("worker error accepted")?;
    passed!("worker_error",worker_error.contains("worker-error-sentinel"));
    let receiver_drop=whole_joined(|tx| {
        for _ in 0..8 {whole_send(tx,WholeMessage::Begin(true,0))?;}Ok(())
    },|_|Err::<(),String>("receiver-drop-sentinel".into())).err().ok_or("receiver drop accepted")?;
    passed!("receiver_drop",receiver_drop.contains("receiver-drop-sentinel") && receiver_drop.contains("receiver closed"));
    whole_require(results.len()==23 && results.values().all(|v|*v),"whole S12 incomplete controls")
}
fn whole_execute(sample:bool,report:&mut serde_json::Value)->Result<(),String> {
    fn needs_sync<T:Sync>() {}
    needs_sync::<WorkTreeHistoryPlan>();needs_sync::<HeightWork<'_>>();needs_sync::<DaaHistoryRoster<'_>>();
    let prior=if sample {
        whole_require(std::env::var_os("NIPOPOW_WHOLE_S12_SAMPLE_RECEIPT_SHA256").is_none(),
            "sample must not reuse census receipt token")?;None
    } else {
        let token=std::env::var("NIPOPOW_WHOLE_S12_SAMPLE_RECEIPT_SHA256")
            .map_err(|_|"census requires admitted sample receipt binding")?;
        whole_require(token.len()==64 && token.bytes().all(|x|x.is_ascii_digit() || (b'A'..=b'F').contains(&x)),
            "census sample receipt binding encoding")?;
        Some(token)
    };
    report["prior_control_receipt_sha256"]=serde_json::json!(prior);
    let native=input();
    let parent=WorkTreeHistoryPlan::compile(3073,12,native.root(),native.total_be28())?;
    drop(native);
    let height=HeightWork::compile_history(&parent)?;
    let daa=DaaHistoryRoster::compile(&parent)?;
    let adapter=Role4EndpointAdapter::new(&height,&daa,Role4EndpointScope::WholeS12)?;
    let binding=adapter.binding();
    let aliases=whole_aliases(&daa)?;
    let a2=daa.s12_m2_arithmetic_terms()?;
    let expected=338348027u64.checked_add(a2 as u64).ok_or("whole S12 count overflow")?;
    report["a2"]=serde_json::json!(a2);report["expected_terms"]=serde_json::json!(expected);
    report["alias_count"]=serde_json::json!(aliases.len());report["alias_capacity"]=serde_json::json!(aliases.capacity());
    if sample {
        report["controls_executed"]=serde_json::json!(true);
        let mut controls=WHOLE_CONTROL_NAMES.into_iter().map(|k|(k,false)).collect();
        let result=whole_controls(&height,&daa,&adapter,&aliases,&mut controls);
        report["controls"]=serde_json::json!(controls);result?;
    }
    for (rs,us,vs) in [(5,13,29),(7,17,31)] {
        let r=general(32,rs);let u=general(32,us);let v=general(32,vs);
        whole_require(adapter.coefficients(&r,&u,&v)?==composite_coefficients(&height,&daa,&r,&u,&v)?,
            "whole S12 canonical composite coefficient API mismatch")?;
    }
    report["coefficients_equal"]=serde_json::json!(true);
    let mut selected=[!sample;4096];
    if sample {
        for owner in [0usize,1,2,1023,1024,2048,3072,3073,4095] {selected[owner]=true;}
        for t in &aliases {selected[t.left/(1<<20)]=true;selected[t.right/(1<<20)]=true;}
    }
    let numeric=crate::daa_work_actions::DaaWorkActions::new(&parent)?;
    let mut counts=[[0u64;4096];2];let mut checked=[0usize;2];let mut totals=[0u64;2];
    let capacity=whole_joined(|tx| {
        if !sample {
            let total=whole_source_census(&height,&daa,&aliases,a2)?;
            whole_require(total==expected,"canonical whole S12 total")?;
            whole_send(tx,WholeMessage::CanonicalTotal(total))?;
        }
        for left in [true,false] {for owner in 0..4096 {
            if !selected[owner] {continue;}
            whole_send(tx,WholeMessage::Begin(left,owner))?;
            let mut batch=WholeBatcher::new(tx);
            whole_oracle_partition(&height,&daa,&numeric,&aliases,left,owner,|t|batch.add(t))?;
            batch.finish()?;
        }}
        whole_send(tx,WholeMessage::Done)
    },|reader| {
        if !sample {match reader.message()? {
            WholeMessage::CanonicalTotal(n) if n==expected=>(),
            _=>return Err("canonical census count message".into()),
        }}
        for (side,left) in [true,false].into_iter().enumerate() {for owner in 0..4096 {
            if !selected[owner] {continue;}
            reader.begin(left,owner)?;
            let count=adapter.visit_endpoint(&binding,left,owner,|edge| {
                reader.compare(&OracleTuple::candidate(edge))
            })?;
            reader.end(count)?;counts[side][owner]=count as u64;checked[side]+=1;totals[side]+=count as u64;
        }}
        reader.done()?;Ok(reader.max_capacity)
    });
    report["checked_left"]=serde_json::json!(checked[0]);report["checked_right"]=serde_json::json!(checked[1]);
    report["total_left"]=serde_json::json!(totals[0]);report["total_right"]=serde_json::json!(totals[1]);
    let capacity=capacity?;
    report["batch_capacity_max"]=serde_json::json!(capacity);
    report["batch_storage_bound_bytes"]=serde_json::json!(4*capacity*std::mem::size_of::<OracleTuple>());
    whole_require(counts[1][0]==2832226,"GLOBAL0-right concentrated partition count")?;
    if !sample {
        whole_require(checked==[4096,4096] && totals==[expected,expected],
            "whole S12 incomplete both-side census")?;
        report["full_coverage"]=serde_json::json!(true);
    }
    Ok(())
}
fn whole_bounded(sample:bool) {
    let start=std::time::Instant::now();
    let mut report=serde_json::json!({
        "schema":"whole-s12-endpoint-source-v1","version":1,
        "phase":if sample {"sample"} else {"census"},"source_candidate_result":"HOLD",
        "elapsed_seconds":0.0,"headers":3073,"slots":4096,"input_log":32,"row_log":32,
        "a2":null,"expected_terms":null,"checked_left":0,"checked_right":0,"total_left":0,"total_right":0,
        "alias_count":0,"tuple_size_bytes":std::mem::size_of::<OracleTuple>(),"batch_capacity_max":0,
        "alias_capacity":0,"max_live_batch_buffers":4,"batch_storage_bound_bytes":0,
        "counter_bytes":std::mem::size_of::<[[u64;4096];2]>(),"worker_stack_bytes":WHOLE_STACK,
        "coefficient_scope":"canonical_composite","coefficients_equal":false,"controls_executed":false,
        "controls_provenance":if sample {"executed"} else {"admitted_sample"},
        "controls":if sample {serde_json::json!(WHOLE_CONTROL_NAMES.into_iter().map(|k|(k,false))
            .collect::<std::collections::BTreeMap<_,_>>())} else {serde_json::Value::Null},
        "prior_control_receipt_sha256":null,"full_coverage":false,"reason":""
    });
    let result=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||whole_execute(sample,&mut report)))
        .unwrap_or_else(|_|Err("whole S12 source panic".into()));
    report["elapsed_seconds"]=serde_json::json!(start.elapsed().as_secs_f64());
    if let Err(reason)=&result {
        let mut end=reason.len().min(2048);while !reason.is_char_boundary(end){end-=1;}
        report["reason"]=serde_json::json!(&reason[..end]);
    } else {report["source_candidate_result"]=serde_json::json!(if sample {"SAMPLE_PASS"} else {"FULL_PASS"});}
    let payload=serde_json::to_string(&report).expect("bounded source payload serialization");
    assert!(payload.len()<65536);
    println!("\nWHOLE_S12_REPORT {payload}");
    assert!(result.is_ok(),"whole S12 source candidate HOLD");
}

#[test]
fn whole_s12_endpoint_controls() {
    let native=input();
    let parent=WorkTreeHistoryPlan::compile(3073,12,native.root(),native.total_be28()).unwrap();drop(native);
    let height=HeightWork::compile_history(&parent).unwrap();let daa=DaaHistoryRoster::compile(&parent).unwrap();
    let adapter=Role4EndpointAdapter::new(&height,&daa,Role4EndpointScope::WholeS12).unwrap();
    let aliases=whole_aliases(&daa).unwrap();
    let mut controls=WHOLE_CONTROL_NAMES.into_iter().map(|k|(k,false)).collect();
    whole_controls(&height,&daa,&adapter,&aliases,&mut controls).unwrap();
}
#[test]
#[ignore="source-only S12 samples; separate120s/2GiB controller"]
fn whole_s12_endpoint_sample_bounded() {whole_bounded(true);}
#[test]
#[ignore="source-only S12 complete census; requires admitted same-source sample; separate120s/2GiB"]
fn whole_s12_endpoint_census_bounded() {whole_bounded(false);}

const SCREEN_OWNERS:[usize;6]=[0,2,1023,2048,3072,4095];
const SCREEN_WIDTH:usize=1<<20;
const SCREEN_CLASSES:[OwnerClass;6]=[OwnerClass::Genesis,OwnerClass::Carry,OwnerClass::Carry,
    OwnerClass::M1,OwnerClass::Short(crate::short_daa_layout::Profile::M2),OwnerClass::Padding];
const SCREEN_CLASS_NAMES:[&str;6]=["Genesis","Carry","Carry","M1","M2","Padding"];
fn screen_ns(start:std::time::Instant)->u64 {u64::try_from(start.elapsed().as_nanos()).unwrap_or(u64::MAX)}
fn screen_hex(bytes:&[u8])->String {bytes.iter().map(|b|format!("{b:02X}")).collect()}
fn screen_position(report:&mut serde_json::Value,stage:&str,left:Option<bool>,owner:Option<usize>,prefix:Option<usize>) {
    report["stage"]=serde_json::json!(stage);
    report["side"]=serde_json::json!(left.map(|x|if x {"u"}else{"v"}));
    report["owner"]=serde_json::json!(owner);report["prefix"]=serde_json::json!(prefix);
}
fn screen_marker(stage:&str,left:Option<bool>,owner:Option<usize>,state:&str)->Result<(),String> {
    use std::io::Write;
    let payload=serde_json::json!({"stage":stage,"side":left.map(|x|if x {"u"}else{"v"}),"owner":owner,"state":state});
    let mut out=std::io::stdout().lock();
    writeln!(out,"\nNATIVE_FALLBACK_STAGE {payload}").map_err(|e|e.to_string())?;
    out.flush().map_err(|e|e.to_string())
}
// PackedFile has no historical owner tag. Bind each immutable handle to the
// original native producer owner/class/parent and generated packed-byte digest.
struct ScreenRow {
    owner:usize,class:OwnerClass,root:[u8;32],total:[u8;28],digest:String,
    source:Box<crate::packed::PackedFile>,source_identity:usize,packed:Vec<u8>,
}
fn screen_load(rows:&[ScreenRow],requested:usize,root:&[u8;32],total:&[u8;28],
    replacement:Option<usize>)->Result<Vec<Fr>,String> {
    let index=SCREEN_OWNERS.iter().position(|x|*x==requested).ok_or("native screen unknown owner")?;
    let expected=&rows[index];
    // Retain every expected descriptor field; replace ONLY the source handle.
    let source=if let Some(index)=replacement {
        &rows.get(index).ok_or("native screen replacement index")?.source
    }else{&expected.source};
    let identity=(&**source as *const crate::packed::PackedFile) as usize;
    whole_require(expected.owner==requested && expected.class==SCREEN_CLASSES[index]
        && expected.root==*root && expected.total==*total && expected.digest.len()==64
        && identity==expected.source_identity && source.input_len()==SCREEN_WIDTH,
        "native screen row source identity mismatch")?;
    let values=crate::packed_rows::read_row(source,SCREEN_WIDTH,0)?;
    whole_require(values.len()==SCREEN_WIDTH,"native screen decoded width")?;Ok(values)
}
fn screen_bit(rows:&[ScreenRow],wire:usize)->Result<Fr,String> {
    let owner=wire/SCREEN_WIDTH;let local=wire%SCREEN_WIDTH;
    let row=rows.iter().find(|r|r.owner==owner).ok_or("canonical oracle unknown row owner")?;
    Ok(Fr::from(((row.packed[local/8]>>(local%8))&1) as u64))
}
fn screen_row_metadata(path:&std::path::Path,bytes:Option<u64>)->Result<(),String> {
    let metadata=std::fs::symlink_metadata(path).map_err(|e|e.to_string())?;
    whole_require(metadata.is_file() && !metadata.file_type().is_symlink()
        && bytes.is_none_or(|n|metadata.len()==n),"native screen regular row extent")
}
fn screen_tuple_partition(height:&HeightWork<'_>,daa:&DaaHistoryRoster<'_>,
    numeric:&crate::daa_work_actions::DaaWorkActions<'_>,aliases:&[OracleTuple],
    adapter:&Role4EndpointAdapter<'_,'_>,left:bool,owner:usize)
    ->Result<(usize,Vec<usize>),String> {
    let binding=adapter.binding();
    whole_joined(|tx| {
        whole_send(tx,WholeMessage::Begin(left,owner))?;
        let mut batch=WholeBatcher::new(tx);
        whole_oracle_partition(height,daa,numeric,aliases,left,owner,|t|batch.add(t))?;
        batch.finish()?;whole_send(tx,WholeMessage::Done)
    },|reader| {
        let mut actual_opposite=std::collections::BTreeSet::new();
        reader.begin(left,owner)?;
        let count=adapter.visit_endpoint(&binding,left,owner,|edge| {
            if left {actual_opposite.insert(edge.term.gate.right/SCREEN_WIDTH);}
            reader.compare(&OracleTuple::candidate(edge))
        })?;
        reader.end(count)?;reader.done()?;
        Ok((count,actual_opposite.into_iter().collect()))
    })
}
fn screen_execute(report:&mut serde_json::Value)->Result<(),String> {
    use std::io::Write;
    use crate::sparse_stream_roster::{EdgeFallbackWeightsForTest,edge_fallback_prefix_for_test};
    whole_require(std::mem::size_of::<Fr>()==32,"native screen Fr width")?;
    let output=std::path::PathBuf::from(std::env::var_os("NIPOPOW_NATIVE_FALLBACK_ROUND_DIR")
        .ok_or("native screen fresh output required")?);
    let meta=std::fs::symlink_metadata(&output).map_err(|e|e.to_string())?;
    whole_require(meta.is_dir() && !meta.file_type().is_symlink()
        && std::fs::read_dir(&output).map_err(|e|e.to_string())?.next().is_none(),
        "native screen output must be empty regular directory")?;
    let output=output.canonicalize().map_err(|e|e.to_string())?;
    let temp=std::path::PathBuf::from(std::env::var_os("TEMP").ok_or("native screen TEMP required")?)
        .canonicalize().map_err(|e|e.to_string())?;
    whole_require(!output.starts_with(&temp),"native rows must remain outside TEMP")?;
    let row_dir=output.join("native-rows");
    std::fs::create_dir(&row_dir).map_err(|e|e.to_string())?;
    screen_marker("construction",None,None,"begin")?;
    let started=std::time::Instant::now();
    let native=input();let root=native.root();let total=native.total_be28();
    let parent=WorkTreeHistoryPlan::compile(3073,12,root,total)?;
    report["parent"]=serde_json::json!({"root_hex":screen_hex(&root),"total_hex":screen_hex(&total)});
    let producer=crate::packed_owner_assembly::NativeOwnerProducer::new_for_history(&parent,&native)?;
    report["construction_ns"]=serde_json::json!(screen_ns(started));
    screen_marker("construction",None,None,"end")?;
    let mut rows=Vec::with_capacity(6);
    for (index,owner) in SCREEN_OWNERS.into_iter().enumerate() {
        screen_position(report,"row-production",None,Some(owner),None);
        screen_marker("row-production",None,Some(owner),"begin")?;
        let started=std::time::Instant::now();
        let row=producer.produce(owner)?;
        whole_require(row.owner()==owner && row.class()==SCREEN_CLASSES[index]
            && row.packed_bytes().len()==SCREEN_WIDTH/8,"native screen generated row binding")?;
        let filename=format!("owner-{owner}.bits");let path=row_dir.join(&filename);
        // create_new never overwrites; ordinary writes retain incomplete files
        // on HOLD. PackedFileWriter's inherited deletion-on-drop is not used.
        let mut file=OpenOptions::new().write(true).create_new(true).share_mode(0)
            .open(&path).map_err(|e|e.to_string())?;
        file.write_all(row.packed_bytes()).map_err(|e|e.to_string())?;
        file.sync_all().map_err(|e|e.to_string())?;drop(file);
        screen_row_metadata(&path,Some((SCREEN_WIDTH/8) as u64))?;
        let source=Box::new(crate::packed::PackedFile::open(&path,20)?);
        let mut checked=vec![0u8;SCREEN_WIDTH/8];
        let mut reader=OpenOptions::new().read(true).share_mode(1).open(&path).map_err(|e|e.to_string())?;
        reader.read_exact(&mut checked).map_err(|e|e.to_string())?;
        let mut tail=[0u8;1];
        whole_require(reader.read(&mut tail).map_err(|e|e.to_string())?==0,"native screen packed trailing bytes")?;
        drop(reader);
        whole_require(checked==row.packed_bytes() && checked.capacity()<=SCREEN_WIDTH/8,
            "native screen immutable packed ledger mismatch/capacity")?;
        let digest=layout::hash_bytes(&checked).to_ascii_uppercase();
        let source_identity=(&*source as *const crate::packed::PackedFile) as usize;
        rows.push(ScreenRow{owner,class:row.class(),root,total,digest:digest.clone(),
            source,source_identity,packed:checked});
        drop(row);
        let elapsed=screen_ns(started);
        report["rows"].as_array_mut().ok_or("screen rows report")?.push(serde_json::json!({
            "owner":owner,"class":SCREEN_CLASS_NAMES[index],"file":filename,"bytes":SCREEN_WIDTH/8,"blake2b256":digest}));
        report["row_production_ns"].as_array_mut().ok_or("screen row timers")?.push(serde_json::json!(elapsed));
        screen_marker("row-production",None,Some(owner),"end")?;
    }
    // Native parsing/producer state must not overlap the relation/oracle banks.
    drop(producer);drop(native);
    let packed_capacity=rows.iter().map(|r|r.packed.capacity()).sum::<usize>();
    whole_require(packed_capacity<1024*1024,"native screen packed ledger bound")?;
    report["memory"]["packed_capacity_bytes"]=serde_json::json!(packed_capacity);
    screen_position(report,"relation",None,None,None);screen_marker("relation",None,None,"begin")?;
    let height=HeightWork::compile_history(&parent)?;let daa=DaaHistoryRoster::compile(&parent)?;
    let adapter=Role4EndpointAdapter::new(&height,&daa,Role4EndpointScope::WholeS12)?;
    let aliases=whole_aliases(&daa)?;
    report["memory"]["alias_capacity"]=serde_json::json!(aliases.capacity());
    report["memory"]["alias_storage_bytes"]=serde_json::json!(aliases.capacity()*std::mem::size_of::<OracleTuple>());
    let numeric=crate::daa_work_actions::DaaWorkActions::new(&parent)?;
    let r=general(32,5);let u=general(32,13);let v=general(32,29);let left_value=Fr::from(17);
    screen_marker("relation",None,None,"end")?;
    // Controls are isolated and run once. Keep owner0's entire descriptor and
    // substitute ONLY owner2's same-width underlying handle. Every other loader
    // predicate remains valid, so removing handle identity breaks this control.
    screen_position(report,"control",None,None,None);
    let expected=&rows[0];let foreign=&rows[1];
    let foreign_identity=(&*foreign.source as *const crate::packed::PackedFile) as usize;
    whole_require(expected.owner==0 && expected.class==SCREEN_CLASSES[0]
        && expected.root==root && expected.total==total && expected.digest.len()==64
        && expected.source.input_len()==SCREEN_WIDTH && foreign.source.input_len()==SCREEN_WIDTH
        && foreign_identity!=expected.source_identity,"foreign handle control preconditions")?;
    whole_require(screen_load(&rows,0,&root,&total,Some(1)).err().as_deref()
        ==Some("native screen row source identity mismatch"),"foreign row control accepted")?;
    report["controls"]["foreign_row_rejected"]=serde_json::json!(true);
    whole_require(screen_load(&rows,1,&root,&total,None).err().as_deref()
        ==Some("native screen unknown owner"),"extra owner control accepted")?;
    report["controls"]["extra_owner_rejected"]=serde_json::json!(true);
    let mut total_messages=0u64;let mut total_terminals=0u64;let mut total_tuples=0u64;
    let mut oracle_total=0u64;let mut candidate_total=0u64;
    for left in [true,false] {
        // Independently constructed canonical weights; candidate lookup/tables
        // are never used to accumulate the dense reference.
        let row_weights=Weights::new(&r);
        let left_weights=if left {None}else{Some(Weights::new(&u))};
        let weights=EdgeFallbackWeightsForTest::new(&r,&u,20);
        let weight_bytes=weights.capacity_bytes()
            +(row_weights.low.capacity()+row_weights.high.capacity())*std::mem::size_of::<Fr>()
            +left_weights.as_ref().map_or(0,|w|(w.low.capacity()+w.high.capacity())*std::mem::size_of::<Fr>());
        report["memory"]["weights_capacity_peak_bytes"]=serde_json::json!(weight_bytes);
        for owner in SCREEN_OWNERS {
            screen_marker("partition",Some(left),Some(owner),"begin")?;
            screen_position(report,"tuple-compare",Some(left),Some(owner),None);
            let (count,opposite)=screen_tuple_partition(&height,&daa,&numeric,&aliases,&adapter,left,owner)?;
            whole_require(count>0 && opposite.iter().all(|x|SCREEN_OWNERS.contains(x)),
                "native screen canonical required-row closure")?;
            let started=std::time::Instant::now();
            screen_position(report,"oracle",Some(left),Some(owner),None);
            let mut a=vec![Fr::zero();SCREEN_WIDTH];let mut b=vec![Fr::zero();SCREEN_WIDTH];
            let mut canonical_opposite=std::collections::BTreeSet::new();let mut canonical_count=0usize;
            whole_oracle_partition(&height,&daa,&numeric,&aliases,left,owner,|t| {
                canonical_count+=1;
                let mut weight=row_weights.at(t.row);
                let wire=if left {t.left%SCREEN_WIDTH}else{t.right%SCREEN_WIDTH};
                if left {
                    canonical_opposite.insert(t.right/SCREEN_WIDTH);
                    // This read is unconditional, including formal zero terms.
                    let right=screen_bit(&rows,t.right)?;
                    a[wire]+=weight*(t.c[1]+t.c[3]*right);
                    b[wire]+=weight*(t.c[0]+t.c[2]*right);
                } else {
                    weight*=left_weights.as_ref().ok_or("canonical V weights")?.at(t.left);
                    a[wire]+=weight*(t.c[2]+t.c[3]*left_value);
                    b[wire]+=weight*(t.c[0]+t.c[1]*left_value);
                }
                Ok(())
            })?;
            whole_require(canonical_count==count
                && canonical_opposite.into_iter().collect::<Vec<_>>()==opposite,
                "native screen independent required-row closure/count")?;
            let mut oracle_x=(0..SCREEN_WIDTH).map(|wire|screen_bit(&rows,owner*SCREEN_WIDTH+wire))
                .collect::<Result<Vec<_>,_>>()?;
            let oracle_capacity=(a.capacity()+b.capacity()+oracle_x.capacity())*std::mem::size_of::<Fr>();
            let mut oracle_ns=screen_ns(started);let mut candidate_ns=0u64;
            let mut prefix_ns=Vec::with_capacity(21);
            let mut visits=0u64;let mut loads=0u64;let mut decode_ns=0u64;
            let mut gets=0u64;let mut clones=0u64;let mut folds=0u64;let mut x_fields=0u64;let mut bank_entries=0u64;
            let mut bank_peak=0usize;let mut cache_peak=0usize;let mut bank_modes=std::collections::BTreeSet::new();
            let challenges=if left {&u[..20]}else{&v[..20]};
            let binding=adapter.binding();
            for prefix in 0..=20 {
                screen_position(report,"candidate",Some(left),Some(owner),Some(prefix));
                let mut prefix_loads=0u64;let mut prefix_decode=0u64;
                let mut ledger=std::collections::BTreeSet::new();
                let started=std::time::Instant::now();
                let result=edge_fallback_prefix_for_test(left,owner,20,12,19,1,&[19,19],count,
                    &weights,left_value,&challenges[..prefix],
                    |l,o,sink|adapter.visit_endpoint(&binding,l,o,|e|sink(e)).map(|_|()),
                    |requested| {
                        whole_require(requested==owner || opposite.contains(&requested),"native screen unexpected callback owner")?;
                        ledger.insert(requested);let start=std::time::Instant::now();
                        let values=screen_load(&rows,requested,&root,&total,None)?;
                        prefix_decode+=screen_ns(start);prefix_loads+=1;Ok(values)
                    },None)?;
                let elapsed=screen_ns(started);prefix_ns.push(elapsed);candidate_ns+=elapsed;
                whole_require(ledger.contains(&owner)
                    && opposite.iter().all(|required|ledger.contains(required)),
                    "native screen exhaustive callback owner ledger")?;
                if prefix<20 {
                    let started=std::time::Instant::now();
                    let expected=crate::gkr::quadratic_message(&a,&b,&oracle_x);
                    oracle_ns+=screen_ns(started);
                    whole_require(result.message==expected,"native screen exact fallback message mismatch")?;
                    total_messages+=1;
                    if !report["controls"]["row_bit_rejected"].as_bool().unwrap_or(false) {
                        if let Some(wire)=a.iter().position(|value|!value.is_zero()) {
                            // A nonzero canonical A/C coefficient makes this
                            // Boolean decoded-X flip sensitive in the message.
                            whole_require(oracle_x[wire]==Fr::zero() || oracle_x[wire]==Fr::one(),
                                "native screen canonical witness bit")?;
                            report["controls"]["row_bit_sensitive"]=serde_json::json!(true);
                            screen_position(report,"control",Some(left),Some(owner),Some(prefix));
                            whole_require(prefix==0,"native screen first sensitivity must precede folding")?;
                            let mutant=edge_fallback_prefix_for_test(left,owner,20,12,19,1,&[19,19],count,
                                &weights,left_value,&[],
                                |l,o,sink|adapter.visit_endpoint(&binding,l,o,|e|sink(e)).map(|_|()),
                                |requested| {
                                    whole_require(requested==owner || opposite.contains(&requested),"control callback owner")?;
                                    screen_load(&rows,requested,&root,&total,None)
                                },Some(wire))?;
                            whole_require(mutant.message!=expected,"native screen decoded row bit mutant accepted")?;
                            report["controls"]["row_bit_rejected"]=serde_json::json!(true);
                        }
                    }
                    let started=std::time::Instant::now();
                    crate::gkr::fold(&mut a,challenges[prefix]);crate::gkr::fold(&mut b,challenges[prefix]);
                    crate::gkr::fold(&mut oracle_x,challenges[prefix]);oracle_ns+=screen_ns(started);
                } else {
                    whole_require(result.terminal==(a[0],b[0]) && result.folded_x==oracle_x[0],
                        "native screen terminal bank/X mismatch")?;total_terminals+=1;
                }
                visits+=result.metrics.visits;gets+=result.metrics.cache_gets;
                clones+=result.metrics.vector_clones;folds+=result.metrics.replay_folds;
                x_fields+=result.metrics.x_fold_fields;bank_entries+=result.metrics.bank_fold_entries;
                bank_peak=bank_peak.max(result.metrics.bank_capacity_peak_bytes);
                cache_peak=cache_peak.max(result.metrics.cache_capacity_peak_bytes);
                bank_modes.insert(if result.metrics.dense {"dense"}else{"sparse"});
                loads+=prefix_loads;decode_ns+=prefix_decode;
            }
            whole_require(visits==21*count as u64 && clones==21 && folds==210 && gets>=loads,
                "native screen replay accounting")?;
            total_tuples+=1;oracle_total+=oracle_ns;candidate_total+=candidate_ns;
            let partition=serde_json::json!({"side":if left {"u"}else{"v"},"owner":owner,"terms":count,
                "opposite_owners":opposite,"tuple_count":count,"message_count":20,"terminal_count":1,
                "oracle_ns":oracle_ns,"candidate_ns":candidate_ns,"prefix_ns":prefix_ns,"visits":visits,
                "loads":loads,"decoded_bytes":loads*(SCREEN_WIDTH*std::mem::size_of::<Fr>()) as u64,
                "decode_ns":decode_ns,"cache_gets":gets,"cache_hits":gets-loads,"vector_clones":clones,
                "replay_folds":folds,"x_fold_fields":x_fields,"bank_fold_entries":bank_entries,
                "bank_modes":bank_modes,"bank_capacity_peak_bytes":bank_peak,
                "cache_capacity_peak_bytes":cache_peak,"oracle_capacity_bytes":oracle_capacity});
            report["partitions"].as_array_mut().ok_or("screen partitions report")?.push(partition);
            report["completed_partitions"]=serde_json::json!(total_tuples);
            report["tuple_partitions"]=serde_json::json!(total_tuples);
            report["message_comparisons"]=serde_json::json!(total_messages);
            report["terminal_comparisons"]=serde_json::json!(total_terminals);
            report["oracle_ns"]=serde_json::json!(oracle_total);report["candidate_ns"]=serde_json::json!(candidate_total);
            for (key,observed) in [("cache_capacity_peak_bytes",cache_peak),
                ("bank_capacity_peak_bytes",bank_peak),("oracle_capacity_peak_bytes",oracle_capacity)] {
                let prior=report["memory"][key].as_u64().ok_or("screen memory counter")?;
                report["memory"][key]=serde_json::json!(prior.max(observed as u64));
            }
            // Only this owner/side's oracle banks survive its21 prefixes.
            drop(a);drop(b);drop(oracle_x);
            screen_marker("partition",Some(left),Some(owner),"end")?;
        }
    }
    whole_require(total_tuples==12 && total_messages==240 && total_terminals==12
        && report["controls"].as_object().ok_or("screen controls report")?.values().all(|x|x.as_bool()==Some(true)),
        "native screen incomplete comparisons/controls")?;
    screen_position(report,"final",None,None,None);
    // Packed handles close normally; completed rows remain for controller custody.
    drop(rows);Ok(())
}
#[test]
#[ignore="native W20/S12 selected fallback kernel; separate120s/2GiB controller"]
fn native_s12_fallback_round_screen_bounded() {
    let start=std::time::Instant::now();
    let mut report=serde_json::json!({
        "schema":"native-s12-fallback-round-source-v1","version":1,"source_candidate_result":"HOLD",
        "elapsed_seconds":0.0,"stage":"construction","side":null,"owner":null,"prefix":null,
        "geometry":{"headers":3073,"slots":4096,"width":SCREEN_WIDTH,"input_log":32,"row_log":32},
        "owners":SCREEN_OWNERS,"parent":{"root_hex":null,"total_hex":null},"rows":[],
        "completed_partitions":0,"message_comparisons":0,"terminal_comparisons":0,"tuple_partitions":0,
        "controls":{"row_bit_sensitive":false,"row_bit_rejected":false,"foreign_row_rejected":false,"extra_owner_rejected":false},
        "cold_cache":true,"construction_ns":0,"row_production_ns":[],"oracle_ns":0,"candidate_ns":0,
        "partitions":[],"memory":{"packed_capacity_bytes":0,"cache_capacity_peak_bytes":0,
            "bank_capacity_peak_bytes":0,"oracle_capacity_peak_bytes":0,"weights_capacity_peak_bytes":0,
            "alias_capacity":0,"alias_storage_bytes":0},"reason":""
    });
    let result=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||screen_execute(&mut report)))
        .unwrap_or_else(|_|Err("native fallback screen source panic".into()));
    report["elapsed_seconds"]=serde_json::json!(start.elapsed().as_secs_f64());
    if let Err(reason)=&result {
        let mut end=reason.len().min(2048);while !reason.is_char_boundary(end) {end-=1;}
        report["reason"]=serde_json::json!(&reason[..end]);
    } else {report["source_candidate_result"]=serde_json::json!("SCREEN_PASS");}
    let payload=serde_json::to_string(&report).expect("native screen bounded report serialization");
    assert!(payload.len()<=16384,"native screen report exceeds bound");
    println!("\nNATIVE_FALLBACK_REPORT {payload}");
    assert!(result.is_ok(),"native fallback screen source HOLD");
}

// Complete first local U round. This diagnostic never constructs a full prover
// or a full decoded witness; its independent oracle reads packed Boolean rows.
const U0_TERMS:u64=338580202;
const U0_FIXTURE_SHA:&str="ABB3D74AE75256CED63110B72C2E0D5EBA1B90B09889E45EA327BDA1C9A640D2";
const U0_FIXTURE_BLAKE:&str="8CDB90DA475E646280113D97C9469BE7EB86A1D04F20404C64239187284FC009";
const U0_WITNESS_SHA:&str="C1CC1CF72FF539F259A3BDEF756332BA52CB8AFF26C11AB4116D1B2F9D17ED43";
const U0_WITNESS_BLAKE:&str="725D7B1215E1185C52C1012D9294260612653ACAD53A02429B8EAAFD0F0770C8";
const U0_ROOT:&str="DF3C1D555FCF6D2A5BA620422D1007A85CA5F8968D6F608C9856CE326C448913";
const U0_TOTAL:&str="000000000000000000000000000000000000000000564F0B9B000000";
const U0_SOURCE:&str="8995ff243b140e7fe716bd3204423dd35690c2e4";
const U0_CONTROL_NAMES:[&str;6]=["positive_exact","omission_rejected","duplicate_rejected",
    "decoded_bit_rejected","bad_sumcheck_rejected","weight_orientation_exact"];

fn u0_hex_fr(x:&Fr)->Result<String,String> {
    use ark_serialize::CanonicalSerialize;
    let mut bytes=Vec::with_capacity(32);x.serialize_compressed(&mut bytes).map_err(|e|e.to_string())?;
    whole_require(bytes.len()==32,"U0 canonical scalar width")?;Ok(screen_hex(&bytes))
}
fn u0_digest(hex:&str)->Result<[u8;32],String> {
    whole_require(hex.len()==64,"U0 digest width")?;let mut out=[0u8;32];
    for (i,byte) in out.iter_mut().enumerate() {
        *byte=u8::from_str_radix(&hex[2*i..2*i+2],16).map_err(|_|"U0 digest encoding")?;
    }Ok(out)
}
fn u0_counters(t:&crate::transcript::Transcript)->[u64;3] {
    [t.challenges(),t.raw_queries(),t.bytes_absorbed()]
}
fn u0_marker(start:std::time::Instant,stage:&str,edge:&str,owners:Option<usize>)->Result<(),String> {
    use std::io::Write;
    let data=serde_json::json!({"stage":stage,"edge":edge,"elapsed_ns":screen_ns(start),"completed_owners":owners});
    let mut out=std::io::stdout().lock();writeln!(out,"\nNATIVE_U0_STAGE {data}").map_err(|e|e.to_string())?;
    out.flush().map_err(|e|e.to_string())
}
fn u0_begin(report:&mut serde_json::Value,start:std::time::Instant,stage:&str)->Result<std::time::Instant,String> {
    report["stage"]=serde_json::json!(stage);
    u0_marker(start,stage,"begin",if matches!(stage,"census"|"candidate"|"oracle"){Some(0)}else{None})?;
    Ok(std::time::Instant::now())
}
fn u0_end(report:&mut serde_json::Value,start:std::time::Instant,stage:&str,began:std::time::Instant)->Result<(),String> {
    report["timings_ns"][stage.replace('-',"_")]=serde_json::json!(screen_ns(began));
    u0_marker(start,stage,"end",if matches!(stage,"census"|"candidate"|"oracle"){Some(4096)}else{None})
}
fn u0_progress(report:&mut serde_json::Value,start:std::time::Instant,stage:&str,
    completed:usize,terms:u64)->Result<(),String> {
    whole_require(completed<=4096 && terms<=U0_TERMS,"U0 progress bounds")?;
    report["completed_owners"][stage]=serde_json::json!(completed);
    report["terms"][stage]=serde_json::json!(terms);
    if completed%64==0 {u0_marker(start,stage,"progress",Some(completed))?;}Ok(())
}

fn u0_direct_weight(point:&[Fr],index:usize)->Fr {
    point.iter().enumerate().fold(Fr::one(),|w,(bit,x)|
        w*if (index>>bit)&1==1 {*x}else{Fr::one()-x})
}
struct U0OracleWeights {low:Vec<Fr>,high:Vec<Fr>}
impl U0OracleWeights {
    fn new(r:&[Fr])->Result<Self,String> {
        whole_require(r.len()==32,"U0 independent weight geometry")?;
        let mut low=Vec::with_capacity(65536);let mut high=Vec::with_capacity(65536);
        for index in 0..65536 {low.push(u0_direct_weight(&r[..16],index));
            high.push(u0_direct_weight(&r[16..],index));}
        whole_require(low.capacity()==65536 && high.capacity()==65536,"U0 independent weight capacity")?;
        Ok(Self{low,high})
    }
    fn at(&self,row:usize)->Result<Fr,String> {
        whole_require(row<1usize<<32,"U0 canonical row outside domain")?;
        Ok(self.low[row&65535]*self.high[row>>16])
    }
    fn capacity_bytes(&self)->usize {(self.low.capacity()+self.high.capacity())*std::mem::size_of::<Fr>()}
}
// Independently expanded single-gate monomial formula. No candidate banks or
// message code is consulted, including for the cheap fault controls.
fn u0_oracle_term(t:&Term,x0:Fr,x1:Fr,y:Fr,w:Fr)->[Fr;3] {
    let b=Fr::from((t.gate.left&1) as u64);let s=Fr::from(2u64)*b-Fr::one();
    let a=t.gate.c1+t.gate.c3*y;let c=t.gate.c0+t.gate.c2*y;let dx=x1-x0;
    let a0=(Fr::one()-b)*w*a;let da=s*w*a;
    let b0=(Fr::one()-b)*w*c;let db=s*w*c;
    [a0*x0+b0,a0*dx+da*x0+db,da*dx]
}
fn u0_reference_send(poly:[Fr;3],t:&mut crate::transcript::Transcript)->Result<(Fr,Fr),String> {
    whole_require(poly[0]+poly[0]+poly[1]+poly[2]==Fr::zero(),"U0 independent zero identity")?;
    crate::gkr::append_polynomial(t,b"gkr-sumcheck-polynomial",&poly);
    let q=t.challenge_scalar(b"gkr-sumcheck-challenge");
    Ok((q,poly[0]+q*poly[1]+q*q*poly[2]))
}
fn u0_toy_round(terms:&[Term],input:&[Fr],r:&[Fr],flip:bool)->Result<[Fr;3],String> {
    use crate::sparse_stream_roster as stream;
    let visit=|left:bool,owner:usize,sink:&mut dyn FnMut(stream::EdgeTerm)->Result<(),String>|{
        whole_require(left,"U0 toy left endpoint only")?;
        for t in terms {if t.gate.left/4==owner {
            sink(stream::EdgeTerm{source_slot:t.row,family_row:0,term:t.clone()})?;
        }}Ok(())
    };
    let counts=stream::edge_u0_census_for_test(2,3,0,&[0],visit,|_,_|Ok(()))?;
    let mut loads=Vec::new();
    let result=stream::edge_u0_round_for_test(2,3,0,0,&[0],&counts,r,visit,|owner|{
        loads.push(owner);
        let mut row=input[4*owner..4*(owner+1)].to_vec();
        if flip && owner==2 {whole_require(row[1]==Fr::one(),"U0 decoded toy fault precondition")?;row[1]=Fr::zero();}
        Ok(row)
    },|_,_|Ok(())).map(|x|x.0)?;
    if terms.len()==9 && !flip {
        // The last formal-zero gate must cause the otherwise absent owner0
        // reload between owner7's opposite row4 and its own row7.
        whole_require(loads.ends_with(&[4,0,7]),"U0 formal-zero right load omitted")?;
    }
    Ok(result)
}
fn u0_controls(results:&mut serde_json::Value)->Result<(),String> {
    use crate::{gkr::Gate,transcript::Transcript,sparse_stream_roster as stream};
    whole_require(Fr::MODULUS.to_string()=="21888242871839275222246405745257275088548364400416034343698204186575808495617"
        && u0_hex_fr(&Fr::one())?==format!("01{}", "00".repeat(31)),"U0 canonical scalar parser agreement")?;
    let input=(0..8).flat_map(|s|[Fr::from((s&1) as u64),Fr::from(((s>>1)&1) as u64),
        Fr::from(((s>>2)&1) as u64),Fr::one()]).collect::<Vec<_>>();
    let mut terms=Vec::new();
    for s in 0..8 {
        let left=4*s;let right=4*((s+5)%8)+3;
        let (c1,c2,c3)=(Fr::from(2u64),Fr::from(3u64),Fr::from(5u64));
        terms.push(Term{row:s,gate:Gate{left,right,c0:-(c1*input[left]+c2*input[right]+c3*input[left]*input[right]),c1,c2,c3}});
    }
    terms.push(Term{row:7,gate:Gate{left:28,right:0,c0:Fr::zero(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}});
    let mut t=Transcript::new(b"native-u0-eight-owner-control-v1");
    let r=crate::gkr::output_point(8,&mut t);crate::gkr::append_usize(&mut t,b"gkr-layer-index",0);
    let mut expected=[Fr::zero();3];
    for term in &terms {let j=term.gate.left&!1;let v=u0_oracle_term(term,input[j],input[j+1],input[term.gate.right],
        u0_direct_weight(&r,term.row));for (sum,x) in expected.iter_mut().zip(v){*sum+=x;}}
    let actual=u0_toy_round(&terms,&input,&r,false)?;
    whole_require(actual==expected,"U0 toy exact polynomial")?;
    let mut candidate=t.clone();let mut reference=t.clone();
    whole_require(stream::edge_u0_send_for_test(actual,&mut candidate)?==u0_reference_send(expected,&mut reference)?
        && u0_counters(&candidate)==u0_counters(&reference)
        && candidate.clone().challenge_scalar(b"native-u0-continuation")
            ==reference.clone().challenge_scalar(b"native-u0-continuation"),"U0 toy sender transcript")?;
    results["positive_exact"]=serde_json::json!(true);
    let w=u0_direct_weight(&r,2);let contribution=u0_oracle_term(&terms[2],input[8],input[9],input[terms[2].gate.right],w);
    whole_require(!w.is_zero() && contribution==[Fr::zero(),Fr::from(7u64)*w,-Fr::from(7u64)*w]
        && contribution!=[Fr::zero();3],"U0 toy owner2 nonzero sensitivity")?;
    let mut missing=terms.clone();missing.remove(2);
    whole_require(u0_toy_round(&missing,&input,&r,false)?!=expected,"U0 omission accepted")?;
    results["omission_rejected"]=serde_json::json!(true);
    let mut duplicate=terms.clone();duplicate.insert(2,terms[2].clone());
    whole_require(u0_toy_round(&duplicate,&input,&r,false)?!=expected,"U0 duplicate accepted")?;
    results["duplicate_rejected"]=serde_json::json!(true);
    whole_require(u0_toy_round(&terms,&input,&r,true)?!=expected,"U0 decoded bit accepted")?;
    results["decoded_bit_rejected"]=serde_json::json!(true);
    let mut bad=actual;bad[0]+=Fr::one();
    whole_require(stream::edge_u0_send_for_test(bad,&mut t.clone()).err().as_deref()
        ==Some(crate::gkr::GkrError::SumcheckIdentity.to_string().as_str()),"U0 bad sumcheck accepted")?;
    results["bad_sumcheck_rejected"]=serde_json::json!(true);
    let asym=general(32,37);let tables=U0OracleWeights::new(&asym)?;
    for row in [0usize,1,65535,65536,(1usize<<32)-1] {
        whole_require(tables.at(row)?==u0_direct_weight(&asym,row),"U0 weight orientation")?;
    }
    whole_require(tables.at(1)?!=tables.at(65536)?,"U0 asymmetric orientation sensitivity")?;
    results["weight_orientation_exact"]=serde_json::json!(true);
    whole_require(U0_CONTROL_NAMES.iter().all(|name|results[*name]==true),"U0 incomplete controls")
}
#[test]
fn native_u0_aggregate_controls() {
    let mut results=serde_json::json!({});u0_controls(&mut results).unwrap();
}

// Windows handle identity, link count and reparse status; avoids path-only
// admission and keeps all independent readers locked against writes/deletion.
#[repr(C)]
#[derive(Default,Debug,PartialEq,Eq)]
struct U0FileInfo {attributes:u32,created:[u32;2],accessed:[u32;2],written:[u32;2],
    volume:u32,size_high:u32,size_low:u32,links:u32,index_high:u32,index_low:u32}
fn u0_file_info(file:&std::fs::File)->Result<U0FileInfo,String> {
    use std::os::windows::io::AsRawHandle;
    #[link(name="kernel32")]
    extern "system" {fn GetFileInformationByHandle(handle:*mut std::ffi::c_void,info:*mut U0FileInfo)->i32;}
    let mut info=U0FileInfo::default();
    if unsafe {GetFileInformationByHandle(file.as_raw_handle(),&mut info)}==0 {return Err(std::io::Error::last_os_error().to_string());}
    whole_require(info.attributes&0x400==0 && info.attributes&0x10==0 && info.links==1,
        "U0 regular single-link immutable source")?;
    // Reads may update access time; identity, extent and write time stay bound.
    info.accessed=[0;2];Ok(info)
}
fn u0_open_bytes(path:&std::path::Path)->Result<std::fs::File,String> {
    use std::os::windows::fs::MetadataExt;
    let md=std::fs::symlink_metadata(path).map_err(|e|e.to_string())?;
    whole_require(md.is_file() && md.file_attributes()&0x400==0 && md.len()==536870912,
        "U0 packed source extent/type")?;
    let file=OpenOptions::new().read(true).share_mode(1).open(path).map_err(|e|e.to_string())?;
    u0_file_info(&file)?;Ok(file)
}
struct U0ByteCache {file:std::fs::File,rows:std::collections::VecDeque<(usize,Vec<u8>)>,
    loads:u64,bytes:u64,capacity_peak:usize}
impl U0ByteCache {
    fn bit(&mut self,wire:usize)->Result<Fr,String> {
        use std::io::{Seek,SeekFrom};
        whole_require(wire<1usize<<32,"U0 oracle wire domain")?;let owner=wire>>20;
        if let Some(position)=self.rows.iter().position(|(o,_)|*o==owner) {
            let row=self.rows.remove(position).ok_or("U0 byte cache position")?;self.rows.push_front(row);
        } else {
            if self.rows.len()==4 {self.rows.pop_back();}
            let mut bytes=vec![0u8;1<<17];
            whole_require(bytes.capacity()==1<<17,"U0 packed byte row capacity")?;
            self.file.seek(SeekFrom::Start((owner as u64)<<17)).map_err(|e|e.to_string())?;
            self.file.read_exact(&mut bytes).map_err(|e|e.to_string())?;
            self.loads+=1;self.bytes+=bytes.len() as u64;self.rows.push_front((owner,bytes));
            self.capacity_peak=self.capacity_peak.max(self.rows.iter().map(|(_,v)|v.capacity()).sum());
        }
        let row=&self.rows.front().ok_or("U0 byte cache empty")?.1;let local=wire&((1<<20)-1);
        Ok(Fr::from(((row[local>>3]>>(local&7))&1) as u64))
    }
}

fn u0_execute(report:&mut serde_json::Value,start:std::time::Instant)->Result<(),String> {
    use crate::{sparse_stream_roster as stream,transcript::Transcript};
    use blake2::{Blake2b,Digest,digest::consts::U32};
    use std::io::{Seek,SeekFrom};
    let began=u0_begin(report,start,"controls")?;u0_controls(&mut report["controls"])?;
    u0_end(report,start,"controls",began)?;
    let began=u0_begin(report,start,"construction")?;
    let native=input();let root=native.root();let total=native.total_be28();
    whole_require(screen_hex(&root)==U0_ROOT && screen_hex(&total)==U0_TOTAL,"U0 native parent identity")?;
    let parent=WorkTreeHistoryPlan::compile(3073,12,root,total)?;drop(native);
    let height=HeightWork::compile_history(&parent)?;let daa=DaaHistoryRoster::compile(&parent)?;
    whole_require(parent.headers()==3073 && parent.slots()==4096 && height.input_log()==32
        && height.row_log()==18 && daa.input_log()==32 && daa.row_log()==31,"U0 relation geometry")?;
    let adapter=Role4EndpointAdapter::new(&height,&daa,Role4EndpointScope::WholeS12)?;
    let binding=adapter.binding();let aliases=binding.whole_alias_identities.ok_or("U0 alias identities missing")?;
    report["identities"]["parent_root"]=serde_json::json!(screen_hex(&root));
    report["identities"]["parent_total"]=serde_json::json!(screen_hex(&total));
    report["identities"]["aliases"]=serde_json::json!(aliases.iter().flat_map(|x|x.iter()).map(|x|screen_hex(x)).collect::<Vec<_>>());
    u0_end(report,start,"construction",began)?;

    let began=u0_begin(report,start,"source-validation")?;
    let path=std::path::PathBuf::from(std::env::var_os("NIPOPOW_NATIVE_U0_WITNESS").ok_or("U0 witness env absent")?);
    let mut held=u0_open_bytes(&path)?;let before=u0_file_info(&held)?;
    let source=crate::packed::PackedFile::open_with_limit(&path,32,32)?;
    whole_require(source.input_len()==1usize<<32,"U0 packed geometry")?;
    let mut hash=Blake2b::<U32>::new();let mut scratch=vec![0u8;1<<20];let mut read=0u64;
    loop {let n=held.read(&mut scratch).map_err(|e|e.to_string())?;if n==0 {break;}hash.update(&scratch[..n]);read+=n as u64;}
    whole_require(read==536870912 && screen_hex(&hash.finalize())==U0_WITNESS_BLAKE,"U0 held witness BLAKE")?;
    drop(scratch);
    let check=u0_open_bytes(&path)?;
    whole_require(u0_file_info(&held)?==before && u0_file_info(&check)?==before,"U0 witness stable handle/path identity")?;
    drop(check);held.seek(SeekFrom::Start(0)).map_err(|e|e.to_string())?;
    u0_end(report,start,"source-validation",began)?;

    let began=u0_begin(report,start,"census")?;
    let counts=stream::edge_u0_census_for_test(20,12,19,&[19,19],
        |left,owner,sink|adapter.visit_endpoint(&binding,left,owner,|edge|sink(edge)).map(|_|()),
        |owners,terms|u0_progress(report,start,"census",owners,terms))?;
    whole_require(counts.len()==4096 && counts.iter().map(|x|*x as u64).sum::<u64>()==U0_TERMS,
        "U0 complete endpoint census")?;
    report["storage"]["counts_capacity_bytes"]=serde_json::json!(counts.capacity()*std::mem::size_of::<usize>());
    u0_end(report,start,"census",began)?;

    let mut candidate_t=Transcript::new(b"native-s12-role4-u0-aggregate-diagnostic-v1");
    candidate_t.append_bytes(b"source-revision",U0_SOURCE.as_bytes());
    for (label,digest) in [(b"native-fixture-sha256".as_slice(),U0_FIXTURE_SHA),
        (b"native-fixture-blake2b256".as_slice(),U0_FIXTURE_BLAKE),(b"witness-sha256".as_slice(),U0_WITNESS_SHA),
        (b"witness-blake2b256".as_slice(),U0_WITNESS_BLAKE)] {candidate_t.append_bytes(label,&u0_digest(digest)?);}
    candidate_t.append_bytes(b"parent-root",&root);candidate_t.append_bytes(b"parent-total-work-be28",&total);
    for (label,value) in [(b"headers".as_slice(),3073),(b"slot-log".as_slice(),12),
        (b"input-log".as_slice(),32),(b"row-log".as_slice(),32),(b"role-index".as_slice(),4),
        (b"local-input-log".as_slice(),20),(b"base-row-log".as_slice(),19),(b"family-log".as_slice(),1),
        (b"height-member-row-log".as_slice(),19),(b"daa-member-row-log".as_slice(),19)] {
        candidate_t.append_u64(label,value);
    }
    for (label,digest) in [b"m1-map".as_slice(),b"m1-descriptor",b"m2-map",b"m2-descriptor"].into_iter()
        .zip(aliases.iter().flat_map(|x|x.iter())) {candidate_t.append_bytes(label,digest);}
    parent.bind(&mut candidate_t);height.bind(&mut candidate_t);daa.bind(&mut candidate_t);
    let r=crate::gkr::output_point(1usize<<32,&mut candidate_t);
    crate::gkr::append_usize(&mut candidate_t,b"gkr-layer-index",0);
    let mut reference_t=candidate_t.clone();

    let began=u0_begin(report,start,"candidate")?;source.reset_io_metrics();
    let mut ledger=[false;4096];let mut loads=0u64;let mut decode_ns=0u64;
    let (candidate,m)=stream::edge_u0_round_for_test(20,12,19,1,&[19,19],&counts,&r,
        |left,owner,sink|adapter.visit_endpoint(&binding,left,owner,|edge|sink(edge)).map(|_|()),
        |owner| {
            whole_require(owner<4096,"U0 loader owner domain")?;ledger[owner]=true;
            let loaded=std::time::Instant::now();let values=crate::packed_rows::read_row(&source,1<<20,owner)?;
            decode_ns+=screen_ns(loaded);loads+=1;
            whole_require(values.len()==1<<20 && values.capacity()==1<<20,"U0 decoded row capacity")?;Ok(values)
        },|owners,terms|u0_progress(report,start,"candidate",owners,terms))?;
    let f=m.fallback;let io=source.io_metrics_snapshot();
    report["candidate_polynomial"]=serde_json::json!(candidate.iter().map(u0_hex_fr).collect::<Result<Vec<_>,_>>()?);
    report["candidate_metrics"]=serde_json::json!({"visits":f.visits,"cache_gets":f.cache_gets,
        "vector_clones":f.vector_clones,"replay_folds":f.replay_folds,"x_fold_fields":f.x_fold_fields,
        "bank_fold_entries":f.bank_fold_entries,"bank_capacity_peak_bytes":f.bank_capacity_peak_bytes,
        "cache_capacity_peak_bytes":f.cache_capacity_peak_bytes,"x_capacity_peak_bytes":m.x_capacity_peak_bytes,
        "message_ns":m.message_ns,"weights_capacity_bytes":m.weights_capacity_bytes,
        "loads":loads,"decoded_fields":loads*(1<<20),
        "decoded_bytes":loads*(1<<20)*32,"decode_ns":decode_ns,"unique_loaded_owners":ledger.iter().filter(|x|**x).count(),
        "io_read_calls":io.read_calls,"io_read_bytes":io.read_bytes,
        "io_read_ns":u64::try_from(io.read_ns).map_err(|_|"U0 IO timer overflow")?});
    whole_require(ledger.iter().all(|x|*x) && f.visits==U0_TERMS && f.vector_clones==4096
        && f.replay_folds==0 && f.x_fold_fields==0 && f.bank_fold_entries==0,"U0 candidate complete ledger")?;
    drop(counts);
    u0_end(report,start,"candidate",began)?;

    let began=u0_begin(report,start,"oracle")?;let weights=U0OracleWeights::new(&r)?;
    let mut bytes=U0ByteCache{file:held,rows:std::collections::VecDeque::new(),loads:0,bytes:0,capacity_peak:0};
    let mut oracle=[Fr::zero();3];let mut terms=0u64;
    for owner in 0..4096 {
        visit_composite_owner(&height,&daa,owner,|term| {
            let j=term.gate.left&!1;
            let x0=bytes.bit(j)?;let x1=bytes.bit(j+1)?;let y=bytes.bit(term.gate.right)?;
            let contribution=u0_oracle_term(&term,x0,x1,y,weights.at(term.row)?);
            for (sum,x) in oracle.iter_mut().zip(contribution){*sum+=x;}
            terms=terms.checked_add(1).ok_or("U0 oracle count overflow")?;Ok(())
        })?;
        u0_progress(report,start,"oracle",owner as usize+1,terms)?;
    }
    report["oracle_polynomial"]=serde_json::json!(oracle.iter().map(u0_hex_fr).collect::<Result<Vec<_>,_>>()?);
    report["oracle_metrics"]=serde_json::json!({"visits":terms,"row_loads":bytes.loads,"read_bytes":bytes.bytes,
        "cache_capacity_peak_bytes":bytes.capacity_peak,"weights_capacity_bytes":weights.capacity_bytes()});
    whole_require(terms==U0_TERMS && oracle==candidate,"U0 complete canonical polynomial mismatch")?;
    report["equalities"]["polynomial"]=serde_json::json!(true);
    whole_require(candidate[0]+candidate[0]+candidate[1]+candidate[2]==Fr::zero(),"U0 native zero claim")?;
    report["equalities"]["zero_identity"]=serde_json::json!(true);
    whole_require(u0_file_info(&bytes.file)?==before,"U0 final immutable file identity")?;
    drop(bytes);drop(weights);
    u0_end(report,start,"oracle",began)?;

    let began=u0_begin(report,start,"send-round")?;
    let (challenge,claim)=stream::edge_u0_send_for_test(candidate,&mut candidate_t)?;
    whole_require((challenge,claim)==u0_reference_send(oracle,&mut reference_t)?
        && u0_counters(&candidate_t)==u0_counters(&reference_t),"U0 actual sender mismatch")?;
    report["equalities"]["sender"]=serde_json::json!(true);
    let continuation=candidate_t.clone().challenge_scalar(b"native-u0-continuation");
    whole_require(continuation==reference_t.clone().challenge_scalar(b"native-u0-continuation"),"U0 continuation mismatch")?;
    report["equalities"]["continuation"]=serde_json::json!(true);
    report["challenge"]=serde_json::json!(u0_hex_fr(&challenge)?);report["claim"]=serde_json::json!(u0_hex_fr(&claim)?);
    report["continuation"]=serde_json::json!(u0_hex_fr(&continuation)?);
    report["transcript_counters"]=serde_json::json!(u0_counters(&candidate_t));
    u0_end(report,start,"send-round",began)?;
    Ok(())
}

// The V-prefix fixture contains selected reviewed U fields only. It is replayed
// against a fresh canonical pre-U frame and is never imported as live state.
#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct VGeometry {headers:u32,slots:u32,width:u32,input_log:u32,row_log:u32,role:u32}
#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct VCapture {
    source_manifest_sha256:String,join_review_sha256:String,u20_closure_sha256:String,
    join_observations_sha256:String,candidate_round_sha256:[String;20],source_revision:String,
    closure_schema:String,closure_state:String,closure_oracle_pending:bool,local_schema:String,
    local_version:u32,local_mode:String,source_candidate_result:String,completed_rounds:u32,
    oracle_checked_rounds:u32,terminal_checked:bool,geometry:VGeometry,join_schema:String,
    join_version:u32,join_state:String,k20_closure_sha256:String,
}
#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct VTranscriptInput {
    fixture_sha256:String,fixture_blake2b256:String,witness_sha256:String,witness_blake2b256:String,
    parent_root:String,parent_total:String,aliases:[String;4],
}
#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct VLocalRound {
    round:u8,previous_claim:String,polynomial:[String;3],challenge:String,claim:String,
    continuation:String,transcript_counters:[u64;3],
}
#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct VHighRound {
    round:u8,candidate_polynomial:[String;3],oracle_polynomial:[String;3],
    candidate_challenge:String,oracle_challenge:String,candidate_claim:String,oracle_claim:String,
    candidate_continuation:String,oracle_continuation:String,
    candidate_counters:[u64;3],oracle_counters:[u64;3],
}
#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct VInput {
    schema:String,version:u32,capture:VCapture,transcript:VTranscriptInput,
    local_rounds:[VLocalRound;20],local_oracle_polynomials:[[String;3];20],
    high_rounds:[VHighRound;12],high_u:[String;12],left_value:String,oracle_left_value:String,
    initial_counters:[u64;3],final_counters:[u64;3],
}

fn v_hex(bytes:&[u8])->Result<Vec<u8>,String>{
    whole_require(!bytes.is_empty() && bytes.len()%2==0,"V hex extent")?;
    let mut out=Vec::with_capacity(bytes.len()/2);
    for pair in bytes.chunks_exact(2){
        whole_require(pair[0].is_ascii_hexdigit() && pair[1].is_ascii_hexdigit()
            && !pair.iter().any(u8::is_ascii_lowercase),"V uppercase hex")?;
        out.push(u8::from_str_radix(std::str::from_utf8(pair).map_err(|e|e.to_string())?,16)
            .map_err(|e|e.to_string())?);
    }Ok(out)
}
fn v_fr(text:&str)->Result<Fr,String>{
    whole_require(text.len()==64 && text.bytes().all(|b|b.is_ascii_digit()||(b'A'..=b'F').contains(&b)),
        "V canonical LE32 scalar syntax")?;
    let bytes=v_hex(text.as_bytes())?;let value=Fr::from_le_bytes_mod_order(&bytes);
    whole_require(u0_hex_fr(&value)?==text,"V scalar noncanonical or above modulus")?;Ok(value)
}
fn v_poly(values:&[String;3])->Result<[Fr;3],String>{
    Ok([v_fr(&values[0])?,v_fr(&values[1])?,v_fr(&values[2])?])
}
fn v_check_hash(s:&str)->bool{s.len()==64 && s.bytes().all(|b|b.is_ascii_digit()||(b'A'..=b'F').contains(&b))}
fn v_read_input()->Result<(VInput,Vec<u8>),String>{
    let path=std::env::var_os("NIPOPOW_NATIVE_V_PREFIX_INPUT").map(std::path::PathBuf::from)
        .ok_or("V input environment absent")?;
    let mut file=OpenOptions::new().read(true).share_mode(1).open(path).map_err(|e|e.to_string())?;
    let mut bytes=Vec::new();file.take(65537).read_to_end(&mut bytes).map_err(|e|e.to_string())?;
    whole_require(!bytes.is_empty() && bytes.len()<=65536,"V input byte cap")?;
    let input:VInput=serde_json::from_slice(&bytes).map_err(|e|format!("V typed input: {e}"))?;
    whole_require(input.schema=="native-s12-v-prefix-input-v1" && input.version==1,
        "V input schema/version")?;
    let c=&input.capture;
    whole_require(c.source_manifest_sha256=="87E48141F828DD84B5D11460587F92649FF96AAB733166CA912BF6E87E1CAAB6"
        && c.join_review_sha256=="3C82D496738343D8AAA9957B8591F2E231EACC407ADFBF779905C27BB6B0CA43"
        && c.u20_closure_sha256=="8D1E5DAE7FBE30A369F9AE7FAF32B59310CC8D54AB34A7CDBA0A631C118A0D2F"
        && c.join_observations_sha256=="C3693654894E0B7E213EB384DD9CEB053F60D0F829479C9751B6B1E8DB44E008"
        && c.source_revision==U0_SOURCE && c.closure_schema=="native-u-high-k20-closure-v1"
        && c.closure_state=="U20_SOURCE_COMPLETE" && !c.closure_oracle_pending
        && c.local_schema=="native-s12-u-sequence-source-v1" && c.local_version==1
        && c.local_mode=="sequence" && c.source_candidate_result=="SEQUENCE_PASS"
        && c.completed_rounds==20 && c.oracle_checked_rounds==20 && c.terminal_checked
        && (c.geometry.headers,c.geometry.slots,c.geometry.width,c.geometry.input_log,c.geometry.row_log,c.geometry.role)
            ==(3073,4096,1048576,32,32,4)
        && c.join_schema=="native-u-high-join-observations-v1" && c.join_version==1
        && c.join_state=="JOIN_SOURCE_COMPLETE" && c.k20_closure_sha256==c.u20_closure_sha256
        && c.candidate_round_sha256.iter().all(|x|v_check_hash(x)),"V capture provenance pins/states")?;
    let tr=&input.transcript;
    whole_require(tr.fixture_sha256==U0_FIXTURE_SHA && tr.fixture_blake2b256==U0_FIXTURE_BLAKE
        && tr.witness_sha256==U0_WITNESS_SHA && tr.witness_blake2b256==U0_WITNESS_BLAKE
        && tr.parent_root==U0_ROOT && tr.parent_total==U0_TOTAL
        && tr.aliases.iter().all(|x|v_check_hash(x)),"V transcript binding syntax")?;
    for (i,round) in input.local_rounds.iter().enumerate(){
        whole_require(round.round as usize==i,"V local round order")?;
        let _=v_fr(&round.previous_claim)?;let _=v_poly(&round.polynomial)?;let _=v_fr(&round.challenge)?;
        let _=v_fr(&round.claim)?;let _=v_fr(&round.continuation)?;
    }
    for (i,round) in input.high_rounds.iter().enumerate(){
        whole_require(round.round as usize==i,"V high round order")?;
        let _=v_poly(&round.candidate_polynomial)?;let _=v_poly(&round.oracle_polynomial)?;
        for scalar in [&round.candidate_challenge,&round.oracle_challenge,&round.candidate_claim,&round.oracle_claim,
            &round.candidate_continuation,&round.oracle_continuation]{let _=v_fr(scalar)?;}
    }
    for p in &input.local_oracle_polynomials{let _=v_poly(p)?;}
    for q in &input.high_u{let _=v_fr(q)?;}
    let _=v_fr(&input.left_value)?;let _=v_fr(&input.oracle_left_value)?;
    Ok((input,bytes))
}

#[derive(Clone,Copy)]
struct VOwnerRecord {count:usize,polynomial:[Fr;3]}
fn v_owner_digest(records:&[VOwnerRecord])->Result<String,String>{
    use ark_serialize::CanonicalSerialize;
    use blake2::{Blake2b,Digest,digest::consts::U32};
    let mut hash=Blake2b::<U32>::new();
    for (owner,record) in records.iter().enumerate(){
        hash.update((owner as u64).to_le_bytes());
        hash.update(u64::try_from(record.count).map_err(|_|"V owner count overflow")?.to_le_bytes());
        for value in record.polynomial {let mut bytes=Vec::with_capacity(32);
            value.serialize_compressed(&mut bytes).map_err(|e|e.to_string())?;
            whole_require(bytes.len()==32,"V digest scalar width")?;hash.update(bytes);}
    }Ok(screen_hex(&hash.finalize()))
}
fn v_sum_polys(records:&[VOwnerRecord])->[Fr;3]{
    let mut total=[Fr::zero();3];for record in records{for (a,b) in total.iter_mut().zip(record.polynomial){*a+=b;}}total
}
fn v_sum_counts(records:&[VOwnerRecord])->Result<u64,String>{
    records.iter().try_fold(0u64,|a,r|{
        let count=u64::try_from(r.count).map_err(|_|"V owner count overflow")?;
        a.checked_add(count).ok_or_else(||"V count sum overflow".into())
    })
}
fn v_sum_usize_counts(records:&[usize])->Result<u64,String>{
    records.iter().try_fold(0u64,|a,count|a.checked_add(u64::try_from(*count).map_err(|_|"V census count overflow")?)
        .ok_or_else(||"V census total overflow".into()))
}
fn v_owner_compare(expected_count:usize,expected_poly:[Fr;3],observed_count:usize,observed_poly:[Fr;3])->Result<(),String>{
    whole_require(observed_count==expected_count,"V candidate/canonical RIGHT owner count mismatch")?;
    whole_require(observed_poly==expected_poly,"V candidate/canonical RIGHT owner polynomial mismatch")
}
fn v_sender_record_guard(previous:Fr,expected_previous:Fr,challenge:Fr,expected_challenge:Fr,
    claim:Fr,expected_claim:Fr,continuation:Fr,expected_continuation:Fr,
    counters:[u64;3],expected_counters:[u64;3])->Result<(),String>{
    whole_require(previous==expected_previous,"V sender previous-claim mismatch")?;
    whole_require(challenge==expected_challenge,"V sender challenge mismatch")?;
    whole_require(claim==expected_claim,"V sender claim mismatch")?;
    whole_require(continuation==expected_continuation,"V sender continuation mismatch")?;
    whole_require(counters==expected_counters,"V sender counters mismatch")
}
fn v_read_output()->Result<std::path::PathBuf,String>{
    use std::os::windows::fs::MetadataExt;
    let path=std::env::var_os("NIPOPOW_NATIVE_V_PREFIX_OUTPUT_DIR").map(std::path::PathBuf::from)
        .ok_or("V output environment absent")?;
    let md=std::fs::symlink_metadata(&path).map_err(|e|e.to_string())?;
    whole_require(md.is_dir() && md.file_attributes()&0x400==0
        && std::fs::read_dir(&path).map_err(|e|e.to_string())?.next().is_none(),
        "V output not fresh regular directory")?;
    whole_require(!path.canonicalize().map_err(|e|e.to_string())?.starts_with(
        std::env::temp_dir().canonicalize().map_err(|e|e.to_string())?),"V output inside TEMP")?;
    Ok(path)
}
fn v_event(stage:&str,edge:&str,round:Option<usize>,owners:Option<usize>,start:std::time::Instant)->Result<(),String>{
    use std::io::Write;
    let value=serde_json::json!({"stage":stage,"edge":edge,"round":round,"completed_owners":owners,
        "elapsed_ns":screen_ns(start)});
    let line=format!("NATIVE_V_PREFIX_EVENT {value}\n");
    whole_require(line.len()<=1024,"V progress line cap")?;
    let mut out=std::io::stdout().lock();out.write_all(line.as_bytes()).map_err(|e|e.to_string())?;
    out.flush().map_err(|e|e.to_string())
}
fn v_validate_prefix(fixture:&VInput)->Result<(Vec<Fr>,Vec<Fr>,Fr,Fr,[u64;3],String,Fr,
    crate::transcript::Transcript,crate::transcript::Transcript),String>{
    use crate::transcript::Transcript;
    let native=input();let root=native.root();let total=native.total_be28();
    whole_require(screen_hex(&root)==U0_ROOT && screen_hex(&total)==U0_TOTAL,"V fresh RAW identity")?;
    let parent=WorkTreeHistoryPlan::compile(3073,12,root,total)?;drop(native);
    let height=HeightWork::compile_history(&parent)?;let daa=DaaHistoryRoster::compile(&parent)?;
    whole_require(height.input_log()==32 && daa.input_log()==32,"V fresh relation geometry")?;
    let adapter=Role4EndpointAdapter::new(&height,&daa,Role4EndpointScope::WholeS12)?;
    let binding=adapter.binding();let aliases=binding.whole_alias_identities.ok_or("V alias identities")?;
    let actual_aliases=aliases.iter().flat_map(|x|x.iter()).map(|x|screen_hex(x)).collect::<Vec<_>>();
    whole_require(actual_aliases.as_slice()==fixture.transcript.aliases,"V binding aliases")?;
    let mut transcript=Transcript::new(b"native-s12-role4-u-sequence-diagnostic-v1");
    transcript.append_bytes(b"source-revision",U0_SOURCE.as_bytes());
    for (label,digest) in [(b"native-fixture-sha256".as_slice(),U0_FIXTURE_SHA),(b"native-fixture-blake2b256".as_slice(),U0_FIXTURE_BLAKE),
        (b"witness-sha256".as_slice(),U0_WITNESS_SHA),(b"witness-blake2b256".as_slice(),U0_WITNESS_BLAKE)]{
        transcript.append_bytes(label,&u0_digest(digest)?);}
    transcript.append_bytes(b"parent-root",&root);transcript.append_bytes(b"parent-total-work-be28",&total);
    for (label,value) in [(b"headers".as_slice(),3073),(b"slot-log".as_slice(),12),(b"input-log".as_slice(),32),
        (b"row-log".as_slice(),32),(b"role-index".as_slice(),4),(b"local-input-log".as_slice(),20),
        (b"base-row-log".as_slice(),19),(b"family-log".as_slice(),1),(b"height-member-row-log".as_slice(),19),
        (b"daa-member-row-log".as_slice(),19)]{transcript.append_u64(label,value);}
    for (label,digest) in [b"m1-map".as_slice(),b"m1-descriptor",b"m2-map",b"m2-descriptor"].into_iter()
        .zip(aliases.iter().flat_map(|x|x.iter())){transcript.append_bytes(label,digest);}
    parent.bind(&mut transcript);height.bind(&mut transcript);daa.bind(&mut transcript);
    let r=crate::gkr::output_point(1usize<<32,&mut transcript);crate::gkr::append_usize(&mut transcript,b"gkr-layer-index",0);
    let mut reference=transcript.clone();let mut claim=Fr::zero();
    for (i,round) in fixture.local_rounds.iter().enumerate(){
        let candidate=v_poly(&round.polynomial)?;let oracle=v_poly(&fixture.local_oracle_polynomials[i])?;
        whole_require(candidate==oracle,"V local independent oracle polynomial mismatch")?;
        whole_require(v_fr(&round.previous_claim)?==claim,"V local previous claim")?;
        let (candidate_q,candidate_next)=crate::sparse_stream_roster::edge_u_sequence_send_for_test(candidate,claim,&mut transcript)?;
        let (oracle_q,oracle_next)=useq_reference_send(oracle,claim,&mut reference)?;
        let candidate_cont=transcript.clone().challenge_scalar(b"native-u-sequence-continuation");
        let oracle_cont=reference.clone().challenge_scalar(b"native-u-sequence-continuation");
        let expected_previous=v_fr(&round.previous_claim)?;
        v_sender_record_guard(claim,expected_previous,candidate_q,v_fr(&round.challenge)?,
            candidate_next,v_fr(&round.claim)?,candidate_cont,v_fr(&round.continuation)?,
            u0_counters(&transcript),round.transcript_counters)?;
        whole_require(candidate_q==oracle_q && candidate_next==oracle_next && oracle_cont==candidate_cont
            && u0_counters(&reference)==round.transcript_counters,"V local sender reference mismatch")?;
        claim=candidate_next;
    }
    whole_require(u0_counters(&transcript)==fixture.initial_counters
        && u0_counters(&reference)==fixture.initial_counters,"V U20 initial counters")?;
    let mut candidate_claim=claim;let mut oracle_claim=claim;let mut oracle_u=Vec::with_capacity(32);
    for round in &fixture.local_rounds{oracle_u.push(v_fr(&round.challenge)?);}
    let mut candidate_u=oracle_u.clone();
    for i in 0..12{
        let row=&fixture.high_rounds[i];let cp=v_poly(&row.candidate_polynomial)?;let op=v_poly(&row.oracle_polynomial)?;
        let (cq,cn)=crate::sparse_stream_roster::edge_u_sequence_send_for_test(cp,candidate_claim,&mut transcript)?;
        let (oq,on)=useq_reference_send(op,oracle_claim,&mut reference)?;
        let cc=transcript.clone().challenge_scalar(JH_CONTINUATION);let oc=reference.clone().challenge_scalar(JH_CONTINUATION);
        v_sender_record_guard(candidate_claim,oracle_claim,cq,v_fr(&row.candidate_challenge)?,
            cn,v_fr(&row.candidate_claim)?,cc,v_fr(&row.candidate_continuation)?,
            u0_counters(&transcript),row.candidate_counters)?;
        v_sender_record_guard(oracle_claim,candidate_claim,oq,v_fr(&row.oracle_challenge)?,
            on,v_fr(&row.oracle_claim)?,oc,v_fr(&row.oracle_continuation)?,
            u0_counters(&reference),row.oracle_counters)?;
        whole_require(cp==op && cq==oq && cn==on && cc==oc
            && oc==v_fr(&row.oracle_continuation)? && u0_counters(&reference)==row.oracle_counters
            && row.candidate_counters==row.oracle_counters && cq==v_fr(&fixture.high_u[i])?,
            "V high-U replay record mismatch")?;
        candidate_claim=cn;oracle_claim=on;candidate_u.push(cq);oracle_u.push(oq);
    }
    whole_require(candidate_u==oracle_u && candidate_claim==oracle_claim
        && u0_counters(&transcript)==fixture.final_counters
        && u0_counters(&reference)==fixture.final_counters,"V final U transcript mismatch")?;
    let left=v_fr(&fixture.left_value)?;let oracle_left=v_fr(&fixture.oracle_left_value)?;
    whole_require(left==oracle_left,"V captured left-value consistency")?;
    let final_continuation=u0_hex_fr(&transcript.clone().challenge_scalar(JH_CONTINUATION))?;
    let final_claim=candidate_claim;
    Ok((candidate_u,r,left,oracle_left,u0_counters(&transcript),final_continuation,final_claim,transcript,reference))
}

struct VOraclePass {
    polynomial:[Fr;3],first_owner_polynomial:[Fr;3],term_visits:u64,semantic_owner_calls:u64,row_loads:u64,
    io_read_calls:u64,io_read_bytes:u64,scratch_peak_bytes:usize,duration_ns:u64,
    count_matches:u64,polynomial_matches:u64,digest:String,
}
fn v_hash_owner(hash:&mut blake2::Blake2b<blake2::digest::consts::U32>,owner:usize,count:usize,poly:[Fr;3])
    ->Result<(),String>{
    use ark_serialize::CanonicalSerialize;
    use blake2::Digest;hash.update((owner as u64).to_le_bytes());
    hash.update(u64::try_from(count).map_err(|_|"V owner count overflow")?.to_le_bytes());
    for value in poly {let mut bytes=Vec::with_capacity(32);value.serialize_compressed(&mut bytes).map_err(|e|e.to_string())?;
        whole_require(bytes.len()==32,"V digest scalar width")?;hash.update(bytes);}Ok(())
}
fn v_part(output:&std::path::Path,stage:&str,round:Option<usize>,completed:usize,digest:Option<String>)->Result<(),String>{
    let path=output.join("v-prefix.part");let value=serde_json::json!({"schema":"native-s12-v-prefix-part-v1",
        "version":1,"state":"PARTIAL","stage":stage,"round":round,"completed_owners":completed,
        "owner_digest_blake2b256":digest});
    useq_save(&path,&value,16384,!path.exists())
}
#[allow(clippy::too_many_arguments)]
fn v_oracle_pass(
    round:usize,prefix:&[Fr],right_counts:&[usize],candidate:&[VOwnerRecord],
    height:&HeightWork<'_>,daa:&DaaHistoryRoster<'_>,numeric:&crate::daa_work_actions::DaaWorkActions<'_>,
    aliases:&[OracleTuple],rows:&U0OracleWeights,uweights:&U0OracleWeights,oracle_left_value:Fr,
    source:&crate::packed::PackedFile,bytes:&mut U0ByteCache,output:&std::path::Path,
    start:std::time::Instant,active:&std::cell::RefCell<Option<(String,usize,usize)>>,
)->Result<VOraclePass,String>{
    use blake2::{Blake2b,Digest,digest::consts::U32};
    whole_require(round<2 && prefix.len()==round && right_counts.len()==4096 && candidate.len()==4096,
        "V oracle pass extent")?;
    let before=source.io_metrics_snapshot();let bytes_before=(bytes.loads,bytes.bytes);
    let mut digest=Blake2b::<U32>::new();let mut polynomial=[Fr::zero();3];let mut terms=0u64;
    let mut row_loads=0u64;let mut scratch_peak=0usize;let mut count_matches=0u64;let mut polynomial_matches=0u64;
    let mut first_owner_polynomial=None;
    let began=std::time::Instant::now();let width=1usize<<20;
    for owner in 0..4096 {
        let mut a=vec![Fr::zero();width];let mut b=vec![Fr::zero();width];
        let x=useq_legacy_row(source,owner)?;
        whole_require(x.len()==width && x.capacity()==width,"V oracle owner row width/capacity")?;row_loads+=1;
        scratch_peak=scratch_peak.max((a.capacity()+b.capacity()+x.capacity())*std::mem::size_of::<Fr>());
        let mut count=0usize;
        whole_oracle_partition(height,daa,numeric,aliases,false,owner,|term|{
            whole_require(term.right/width==owner,"V canonical RIGHT owner")?;
            let weight=rows.at(term.row)?*uweights.at(term.left)?;
            let wire=term.right%width;
            a[wire]+=weight*(term.c[2]+term.c[3]*oracle_left_value);
            b[wire]+=weight*(term.c[0]+term.c[1]*oracle_left_value);
            count=count.checked_add(1).ok_or("V canonical owner count overflow")?;
            terms=terms.checked_add(1).ok_or("V canonical term total overflow")?;Ok(())
        })?;
        whole_require(count==right_counts[owner],"V candidate/canonical RIGHT census mismatch")?;
        for q in prefix {useq_fold(&mut a,*q);useq_fold(&mut b,*q);}
        let mut folded_x=x;for q in prefix{useq_fold(&mut folded_x,*q);}
        let message=useq_message(&a,&b,&folded_x);
        if owner==0{first_owner_polynomial=Some(message);}
        for (sum,value) in polynomial.iter_mut().zip(message){*sum+=value;}
        let expected=candidate[owner];
        if expected.count==count{count_matches+=1;}
        if expected.polynomial==message{polynomial_matches+=1;}
        v_owner_compare(expected.count,expected.polynomial,count,message)?;
        v_hash_owner(&mut digest,owner,count,message)?;
        if let Some((_,_,completed))=active.borrow_mut().as_mut(){*completed=owner+1;}
        if (owner+1)%1024==0{
            v_event(if round==0{"oracle-v0"}else{"oracle-v1"},"progress",Some(round),Some(owner+1),start)?;
            v_part(output,if round==0{"oracle-v0"}else{"oracle-v1"},Some(round),owner+1,None)?;
        }
    }
    let io=source.io_metrics_snapshot();
    Ok(VOraclePass{polynomial,first_owner_polynomial:first_owner_polynomial.ok_or("V oracle owner zero absent")?,
        term_visits:terms,semantic_owner_calls:4096,
        row_loads:row_loads+bytes.loads-bytes_before.0,
        io_read_calls:io.read_calls-before.read_calls+bytes.loads-bytes_before.0,
        io_read_bytes:io.read_bytes-before.read_bytes+bytes.bytes-bytes_before.1,
        scratch_peak_bytes:scratch_peak.max(bytes.capacity_peak),duration_ns:screen_ns(began),
        count_matches,polynomial_matches,digest:screen_hex(&digest.finalize())})
}

fn v_oracle_rawbit_owner(
    owner:usize,prefix:&[Fr],right_count:usize,height:&HeightWork<'_>,daa:&DaaHistoryRoster<'_>,
    numeric:&crate::daa_work_actions::DaaWorkActions<'_>,aliases:&[OracleTuple],rows:&U0OracleWeights,
    uweights:&U0OracleWeights,source:&crate::packed::PackedFile,bytes:&mut U0ByteCache,
)->Result<(usize,[Fr;3]),String>{
    let width=1usize<<20;let mut a=vec![Fr::zero();width];let mut b=vec![Fr::zero();width];
    let x=useq_legacy_row(source,owner)?;let mut count=0usize;
    whole_oracle_partition(height,daa,numeric,aliases,false,owner,|term|{
        whole_require(term.right/width==owner,"V raw-bit mutant RIGHT owner")?;
        let weight=rows.at(term.row)?*uweights.at(term.left)?;let left=bytes.bit(term.left)?;let wire=term.right%width;
        a[wire]+=weight*(term.c[2]+term.c[3]*left);b[wire]+=weight*(term.c[0]+term.c[1]*left);
        count=count.checked_add(1).ok_or("V raw-bit mutant count overflow")?;Ok(())
    })?;
    whole_require(count==right_count,"V raw-bit mutant owner count")?;
    for q in prefix{useq_fold(&mut a,*q);useq_fold(&mut b,*q);}
    let mut folded_x=x;for q in prefix{useq_fold(&mut folded_x,*q);}
    Ok((count,useq_message(&a,&b,&folded_x)))
}

// Independent owner-local baseline used only before the complete V sweeps.
// The full canonical oracle above remains separate and unchanged.
fn v_oracle_fixed_owner(
    owner:usize,right_count:usize,height:&HeightWork<'_>,daa:&DaaHistoryRoster<'_>,
    numeric:&crate::daa_work_actions::DaaWorkActions<'_>,aliases:&[OracleTuple],
    rows:&U0OracleWeights,uweights:&U0OracleWeights,left_value:Fr,source:&crate::packed::PackedFile,
)->Result<(usize,[Fr;3]),String>{
    whole_require(owner<4096,"V preflight canonical owner bounds")?;
    let width=1usize<<20;let mut a=vec![Fr::zero();width];let mut b=vec![Fr::zero();width];
    let x=useq_legacy_row(source,owner)?;let mut count=0usize;
    whole_require(x.len()==width,"V preflight canonical owner geometry")?;
    whole_oracle_partition(height,daa,numeric,aliases,false,owner,|term|{
        whole_require(term.right/width==owner,"V preflight canonical RIGHT owner")?;
        let weight=rows.at(term.row)?*uweights.at(term.left)?;let wire=term.right%width;
        a[wire]+=weight*(term.c[2]+term.c[3]*left_value);
        b[wire]+=weight*(term.c[0]+term.c[1]*left_value);
        count=count.checked_add(1).ok_or("V preflight canonical count overflow")?;Ok(())
    })?;
    whole_require(count==right_count,"V preflight canonical owner count")?;
    Ok((count,useq_message(&a,&b,&x)))
}
fn v_c2_observable(weight:Fr,wire:usize,x:&[Fr])->Result<bool,String>{
    whole_require(x.len()>=2 && x.len()%2==0 && wire<x.len(),"V c2 support pair bounds")?;
    Ok(!weight.is_zero() && (!x[wire&!1].is_zero() || !x[wire|1].is_zero()))
}

fn v_toy_edge(owner:usize)->crate::sparse_stream_roster::EdgeTerm{
    let source=(owner+1)%4;
    crate::sparse_stream_roster::EdgeTerm{source_slot:source,family_row:0,term:Term{row:0,gate:crate::gkr::Gate{
        left:source*4+(owner+1)%4,right:owner*4+(owner+2)%4,
        c0:Fr::from((owner+3) as u64),c1:Fr::from(2u64),c2:Fr::from(5u64),c3:Fr::from(7u64)}}}
}
fn v_toy_candidate(weights:&crate::sparse_stream_roster::EdgeFallbackWeightsForTest,left_value:Fr,
    prefix:&[Fr],counts:&[usize],fault:u8)->Result<Vec<VOwnerRecord>,String>{
    use crate::sparse_stream_roster as s;
    let mut expected=counts.to_vec();if fault==3{expected[0]=0;}
    let mut output=Vec::with_capacity(4);
    let mut candidate=s::EdgeVPrefixCandidateForTest::new(|owner|{
        Ok((0..4).map(|wire|Fr::from((owner*4+wire+1) as u64)).collect())},4,4)?;
    candidate.round(2,1,1,&[1,1],&expected,weights,left_value,prefix,
        |left,owner,sink|{
            whole_require(!left,"V toy candidate RIGHT endpoint")?;
            if owner==0 && fault==1{return Ok(());}
            let mut edge=v_toy_edge(owner);
            match fault {
                2 if owner==0=>{sink(edge.clone())?;sink(edge)?;return Ok(());}
                4 if owner==0=>edge.term.gate.right=4,
                5 if owner==0=>edge.term.gate.left=9,
                6 if owner==0=>edge.term.gate.right+=1,
                7 if owner==0=>edge.family_row=1,
                _=>{}
            }
            sink(edge)
        },|owner,count,polynomial|{output.push(VOwnerRecord{count,polynomial});Ok(())})?;
    Ok(output)
}

fn v_toy_controls()->Result<(),String>{
    use crate::{sparse_stream_roster as s,transcript::Transcript};
    use ark_ff::Field;
    // Compare support selection with an independently expanded polynomial,
    // including both wire parities and individually vanishing X coordinates.
    for weight in [Fr::zero(),Fr::from(3u64),-Fr::one()] {
        for pair in [[0u64,0],[1,0],[0,1],[1,1],[2,5]] {
            let x=pair.map(Fr::from);
            for wire in 0..2 {
                let mut a=[Fr::zero();2];a[wire]=weight;
                let delta=useq_message(&a,&[Fr::zero();2],&x);
                whole_require(v_c2_observable(weight,wire,&x)?==(delta!=[Fr::zero();3]),
                    "V c2 support disagrees with independent polynomial effect")?;
                whole_require(crate::gkr::quadratic_message(&a,&[Fr::zero();2],&x).as_slice()==delta.as_slice(),
                    "V c2 support candidate/reference polynomial mismatch")?;
            }
        }
    }
    let pairs=[Fr::zero(),Fr::zero(),Fr::one(),Fr::zero()];
    whole_require(!v_c2_observable(Fr::one(),0,&pairs)? && v_c2_observable(Fr::one(),3,&pairs)?,
        "V c2 support must use the selected adjacent pair")?;
    for (wire,x) in [(2,&pairs[..2]),(0,&pairs[..1]),(0,&pairs[..0])] {
        whole_require(v_c2_observable(Fr::one(),wire,x).err().as_deref()==Some("V c2 support pair bounds"),
            "V c2 invalid pair missed bounds guard")?;
    }
    let r=vec![Fr::from(2u64),Fr::from(3u64),Fr::from(5u64),Fr::from(17u64)];
    let u=vec![Fr::from(2u64),Fr::from(5u64),Fr::from(7u64),Fr::from(11u64)];
    let weights=s::EdgeFallbackWeightsForTest::new(&r,&u,2);let left=Fr::from(13u64);
    let counts=s::edge_v_census_for_test(2,2,1,1,&[1,1],|is_left,owner,sink|{
        whole_require(!is_left,"V toy census must enumerate RIGHT owners")?;sink(v_toy_edge(owner))
    },|_,_|Ok(()))?;
    whole_require(counts==vec![1;4],"V toy census owner counts")?;
    let baseline=v_toy_candidate(&weights,left,&[],&counts,0)?;
    for (fault,expected) in [(1,"edge endpoint source count changed between passes"),
        (2,"edge endpoint source exceeded its baseline count"),
        (3,"edge endpoint source exceeded its baseline count"),
        (4,"edge endpoint wire or row outside declared slot")]{
        let result=v_toy_candidate(&weights,left,&[],&counts,fault);
        whole_require(result.err().as_deref()==Some(expected),"V toy structural fault missed its source guard")?;
    }
    whole_require(v_owner_compare(1,baseline[0].polynomial,0,baseline[0].polynomial)
        .err().as_deref()==Some("V candidate/canonical RIGHT owner count mismatch"),
        "V toy owner count fault missed shared count guard")?;
    for fault in [5,6,7]{
        let mutant=v_toy_candidate(&weights,left,&[],&counts,fault)?;
        whole_require(mutant[0].polynomial!=baseline[0].polynomial,"V toy arithmetic mutant insensitive")?;
        let rejection=v_owner_compare(baseline[0].count,baseline[0].polynomial,mutant[0].count,mutant[0].polynomial);
        whole_require(rejection.err().as_deref()==Some("V candidate/canonical RIGHT owner polynomial mismatch"),
            "V toy arithmetic mutant did not reach owner polynomial guard")?;
    }
    let bad_left=v_toy_candidate(&weights,left+Fr::one(),&[],&counts,0)?;
    whole_require(bad_left[0].polynomial!=baseline[0].polynomial,"V toy left-value mutant insensitive")?;
    let bad_left_rejection=v_owner_compare(baseline[0].count,baseline[0].polynomial,
        bad_left[0].count,bad_left[0].polynomial);
    whole_require(bad_left_rejection.err().as_deref()==Some("V candidate/canonical RIGHT owner polynomial mismatch"),
        "V toy left-value mutant bypassed owner guard")?;
    let mut bad_u=u.clone();bad_u[0]+=Fr::one();
    let bad_u_weights=s::EdgeFallbackWeightsForTest::new(&r,&bad_u,2);
    let bad_u_result=v_toy_candidate(&bad_u_weights,left,&[],&counts,0)?;
    whole_require(bad_u_result[0].polynomial!=baseline[0].polynomial,"V toy U-weight mutant insensitive")?;
    let bad_u_rejection=v_owner_compare(baseline[0].count,baseline[0].polynomial,
        bad_u_result[0].count,bad_u_result[0].polynomial);
    whole_require(bad_u_rejection.err().as_deref()==Some("V candidate/canonical RIGHT owner polynomial mismatch"),
        "V toy U-weight mutant bypassed owner guard")?;
    let bad_r_weights=s::EdgeFallbackWeightsForTest::new(&u,&u,2);
    let bad_r_result=v_toy_candidate(&bad_r_weights,left,&[],&counts,0)?;
    whole_require(bad_r_result[0].polynomial!=baseline[0].polynomial,"V toy r-to-U row-weight mutant insensitive")?;
    let bad_r_rejection=v_owner_compare(baseline[0].count,baseline[0].polynomial,
        bad_r_result[0].count,bad_r_result[0].polynomial);
    whole_require(bad_r_rejection.err().as_deref()==Some("V candidate/canonical RIGHT owner polynomial mismatch"),
        "V toy row-point mutant bypassed owner guard")?;

    let v0=v_sum_polys(&baseline);let previous=v0[0]+v0[0]+v0[1]+v0[2];
    let mut candidate=Transcript::new(b"native-v-toy-sender-control-v1");let mut reference=candidate.clone();
    let (oracle_q0,oracle_claim0)=useq_reference_send(v0,previous,&mut reference)?;
    let (candidate_q0,candidate_claim0)=s::edge_u_sequence_send_for_test(v0,previous,&mut candidate)?;
    whole_require(candidate_q0==oracle_q0 && candidate_claim0==oracle_claim0,"V toy V0 sender/reference")?;
    let correct_v1=v_toy_candidate(&weights,left,&[candidate_q0],&counts,0)?;
    let stale_v1=v_toy_candidate(&weights,left,&[candidate_q0+Fr::one()],&counts,0)?;
    whole_require(correct_v1[0].polynomial!=stale_v1[0].polynomial,"V toy stale V0 q insensitive")?;
    let stale_rejection=v_owner_compare(correct_v1[0].count,correct_v1[0].polynomial,
        stale_v1[0].count,stale_v1[0].polynomial);
    whole_require(stale_rejection.err().as_deref()==Some("V candidate/canonical RIGHT owner polynomial mismatch"),
        "V toy stale V0 q bypassed owner guard")?;
    let p1=[candidate_claim0*Fr::from(2u64).inverse().ok_or("V toy inverse two")?,Fr::zero(),Fr::zero()];
    let (oracle_q1,oracle_claim1)=useq_reference_send(p1,oracle_claim0,&mut reference)?;
    let (candidate_q1,candidate_claim1)=s::edge_u_sequence_send_for_test(p1,candidate_claim0,&mut candidate)?;
    whole_require(candidate_q1==oracle_q1 && candidate_claim1==oracle_claim1,"V toy V1 q0 handoff")?;
    let reset=s::edge_u_sequence_send_for_test(p1,Fr::zero(),&mut candidate.clone());
    whole_require(reset.is_err(),"V toy reset prior claim accepted")?;
    let stale_challenge=oracle_q1+Fr::one();
    whole_require(stale_challenge!=oracle_q1,"V toy stale sender challenge sensitivity")?;
    let counters=u0_counters(&candidate);
    let continuation_fr=candidate.clone().challenge_scalar(b"native-u-high-join-continuation-v1");
    let guard=v_sender_record_guard(candidate_claim0,oracle_claim0,candidate_q1,oracle_q1,
        candidate_claim1,oracle_claim1,continuation_fr,continuation_fr,counters,u0_counters(&reference));
    whole_require(guard.is_ok(),"V toy sender record baseline")?;
    whole_require(v_sender_record_guard(candidate_claim0+Fr::one(),oracle_claim0,candidate_q1,oracle_q1,
        candidate_claim1,oracle_claim1,continuation_fr,continuation_fr,counters,counters)
        .err().as_deref()==Some("V sender previous-claim mismatch"),"V toy previous-claim guard")?;
    whole_require(v_sender_record_guard(candidate_claim0,oracle_claim0,candidate_q1,stale_challenge,
        candidate_claim1,oracle_claim1,continuation_fr,continuation_fr,counters,counters)
        .err().as_deref()==Some("V sender challenge mismatch"),"V toy challenge guard")?;
    whole_require(v_sender_record_guard(candidate_claim0,oracle_claim0,candidate_q1,oracle_q1,
        candidate_claim1+Fr::one(),oracle_claim1,continuation_fr,continuation_fr,counters,counters)
        .err().as_deref()==Some("V sender claim mismatch"),"V toy claim guard")?;
    whole_require(v_sender_record_guard(candidate_claim0,oracle_claim0,candidate_q1,oracle_q1,
        candidate_claim1,oracle_claim1,continuation_fr+Fr::one(),continuation_fr,counters,counters)
        .err().as_deref()==Some("V sender continuation mismatch"),"V toy continuation guard")?;
    for index in 0..3{
        let mut bad_counters=counters;bad_counters[index]+=1;
        whole_require(v_sender_record_guard(candidate_claim0,oracle_claim0,candidate_q1,oracle_q1,
            candidate_claim1,oracle_claim1,continuation_fr,continuation_fr,bad_counters,counters)
            .err().as_deref()==Some("V sender counters mismatch"),"V toy counter guard")?;
    }
    Ok(())
}

fn v_execute(output:&std::path::Path,start:std::time::Instant,
    active:&std::cell::RefCell<Option<(String,usize,usize)>>)->Result<serde_json::Value,String>{
    use crate::{sparse_stream_roster as s,transcript::Transcript};
    use blake2::{Blake2b,Digest,digest::consts::U32};
    active.replace(Some(("prefix".to_owned(),0,0)));
    let (fixture,input_bytes)=v_read_input()?;
    whole_require(input_bytes.len()<=32768,"V input exceeds SHA ABI bound")?;
    let input_sha=jh_sha(&input_bytes)?;
    let preflight_start=std::time::Instant::now();
    let (u,r,left_value,oracle_left_value,final_counters,final_continuation,final_claim,mut candidate_sender,mut oracle_sender)=
        v_validate_prefix(&fixture)?;
    let prefix_ns=screen_ns(preflight_start);
    whole_require(u.len()==32,"V composed U extent")?;
    whole_require(r.len()==32,"V reconstructed output point extent")?;
    let native=input();let root=native.root();let total=native.total_be28();
    let parent=WorkTreeHistoryPlan::compile(3073,12,root,total)?;drop(native);
    let height=HeightWork::compile_history(&parent)?;let daa=DaaHistoryRoster::compile(&parent)?;
    let adapter=Role4EndpointAdapter::new(&height,&daa,Role4EndpointScope::WholeS12)?;
    let binding=adapter.binding();let _binding_aliases=binding.whole_alias_identities.ok_or("V alias identities")?;
    let canonical_aliases=whole_aliases(&daa)?;
    let numeric=crate::daa_work_actions::DaaWorkActions::new(&parent)?;
    let (source,held,identity)=useq_admit()?;
    active.replace(Some(("right-census".to_owned(),0,0)));
    let census_start=std::time::Instant::now();
    let right_counts=s::edge_v_census_for_test(20,12,19,1,&[19,19],
        |right,owner,sink|adapter.visit_endpoint(&binding,right,owner,|term|sink(term)).map(|_|()),|_,_|Ok(()))?;
    let right_visits=v_sum_usize_counts(&right_counts)?;
    whole_require(right_counts.len()==4096 && right_visits==338580202,"V RIGHT census total")?;
    let census_ns=screen_ns(census_start);
    let candidate_weights=s::EdgeFallbackWeightsForTest::new(&r,&u,20);
    let oracle_rows=U0OracleWeights::new(&r)?;
    let oracle_u=U0OracleWeights::new(&u)?;
    let mut bytes=U0ByteCache{file:held,rows:std::collections::VecDeque::new(),loads:0,bytes:0,capacity_peak:0};
    let mut native_term_sensitivity=None;let mut native_row_sensitivity=None;let mut native_rawbit_sensitivity=None;
    active.replace(Some(("sensitivity".to_owned(),0,0)));
    {
        let sensitivity_start=std::time::Instant::now();
        let (baseline_count,baseline_poly)=v_oracle_fixed_owner(0,right_counts[0],&height,&daa,&numeric,
            &canonical_aliases,&oracle_rows,&oracle_u,oracle_left_value,&source)?;
        let baseline=s::edge_fallback_prefix_for_test(false,0,20,12,19,1,&[19,19],right_counts[0],
            &candidate_weights,left_value,&[],
            |right,owner,sink|adapter.visit_endpoint(&binding,right,owner,|term|sink(term)).map(|_|()),
            |owner|crate::packed_rows::read_row(&source,1<<20,owner),None)?;
        let candidate_baseline:[Fr;3]=baseline.message.as_slice().try_into()
            .map_err(|_|"V preflight candidate polynomial extent")?;
        v_owner_compare(baseline_count,baseline_poly,
            usize::try_from(baseline.metrics.visits).map_err(|_|"V preflight candidate count extent")?,candidate_baseline)?;
        let c2_owner=2048usize;
        whole_require(right_counts[c2_owner]==118681,"V c2 owner census")?;
        let (c2_baseline_count,c2_baseline_poly)=v_oracle_fixed_owner(c2_owner,right_counts[c2_owner],&height,&daa,&numeric,
            &canonical_aliases,&oracle_rows,&oracle_u,oracle_left_value,&source)?;
        let c2_baseline=s::edge_fallback_prefix_for_test(false,c2_owner,20,12,19,1,&[19,19],right_counts[c2_owner],
            &candidate_weights,left_value,&[],
            |right,owner,sink|adapter.visit_endpoint(&binding,right,owner,|term|sink(term)).map(|_|()),
            |owner|crate::packed_rows::read_row(&source,1<<20,owner),None)?;
        let c2_candidate_baseline:[Fr;3]=c2_baseline.message.as_slice().try_into()
            .map_err(|_|"V c2 preflight candidate polynomial extent")?;
        v_owner_compare(c2_baseline_count,c2_baseline_poly,
            usize::try_from(c2_baseline.metrics.visits).map_err(|_|"V c2 preflight candidate count extent")?,c2_candidate_baseline)?;
        let selection_x=useq_legacy_row(&source,c2_owner)?;
        let mut selected=None;let mut ordinal=0usize;
        let mutation=s::edge_fallback_prefix_for_test(false,c2_owner,20,12,19,1,&[19,19],right_counts[c2_owner],
            &candidate_weights,left_value,&[],
            |right,owner,sink|adapter.visit_endpoint(&binding,right,owner,|mut term|{
                whole_require(term.term.gate.right/(1<<20)==c2_owner,"V c2 selection RIGHT owner")?;
                if selected.is_none() {
                    let wire=term.term.gate.right%(1<<20);
                    let weight=oracle_rows.at(term.term.row)?*oracle_u.at(term.term.gate.left)?;
                    if v_c2_observable(weight,wire,&selection_x)? {
                        term.term.gate.c2+=Fr::one();selected=Some((ordinal,wire));
                    }
                }
                ordinal=ordinal.checked_add(1).ok_or("V c2 selection ordinal overflow")?;
                sink(term)
            }).map(|_|()),
            |owner|crate::packed_rows::read_row(&source,1<<20,owner),None)?;
        let (selected_term_ordinal,selected_wire)=selected.ok_or("V native owner 2048 has no observable c2 term")?;
        whole_require(ordinal==right_counts[c2_owner] && selected_term_ordinal<ordinal && mutation.message.len()==3,
            "V native selected mutation count/extent")?;
        let mutant_poly:[Fr;3]=mutation.message.as_slice().try_into().map_err(|_|"V native c2 mutant polynomial extent")?;
        let delta_nonzero=mutant_poly!=c2_baseline_poly;
        whole_require(delta_nonzero,"V native term mutation had no canonical-owner polynomial effect")?;
        let rejection=v_owner_compare(c2_baseline_count,c2_baseline_poly,
            usize::try_from(mutation.metrics.visits).map_err(|_|"V c2 mutant count extent")?,mutant_poly);
        let rejected_at_owner_polynomial_boundary=rejection.err().as_deref()
            ==Some("V candidate/canonical RIGHT owner polynomial mismatch");
        whole_require(rejected_at_owner_polynomial_boundary,"V native c2 mutant bypassed owner polynomial guard")?;
        native_term_sensitivity=Some(serde_json::json!({"kind":"native-fixture-first-observable-right-term-c2-plus-one",
            "owner":c2_owner,"selected_term_ordinal":selected_term_ordinal,"selected_wire":selected_wire,
            "delta_nonzero":delta_nonzero,"rejected_at_owner_polynomial_boundary":rejected_at_owner_polynomial_boundary,
            "duration_ns":screen_ns(sensitivity_start)}));
        drop(selection_x);drop(c2_baseline);drop(baseline);drop(mutation);

        let row_sensitivity_start=std::time::Instant::now();
        let wrong_row_weights=s::EdgeFallbackWeightsForTest::new(&u,&u,20);
        let wrong_row=s::edge_fallback_prefix_for_test(false,0,20,12,19,1,&[19,19],right_counts[0],
            &wrong_row_weights,left_value,&[],
            |right,owner,sink|adapter.visit_endpoint(&binding,right,owner,|term|sink(term)).map(|_|()),
            |owner|crate::packed_rows::read_row(&source,1<<20,owner),None)?;
        let wrong_row_poly:[Fr;3]=wrong_row.message.as_slice().try_into().map_err(|_|"V native row-point mutant polynomial extent")?;
        let row_delta_nonzero=wrong_row_poly!=baseline_poly;
        whole_require(row_delta_nonzero,"V native r-to-U row-point mutant insensitive")?;
        let row_rejection=v_owner_compare(baseline_count,baseline_poly,
            usize::try_from(wrong_row.metrics.visits).map_err(|_|"V row-point mutant count extent")?,wrong_row_poly);
        let row_rejected=row_rejection.err().as_deref()
            ==Some("V candidate/canonical RIGHT owner polynomial mismatch");
        whole_require(row_rejected,"V native r-to-U row-point mutant bypassed owner guard")?;
        native_row_sensitivity=Some(serde_json::json!({"kind":"native-fixture-row-point-u-instead-of-r",
            "owner":0,"delta_nonzero":row_delta_nonzero,"rejected_at_owner_polynomial_boundary":row_rejected,
            "duration_ns":screen_ns(row_sensitivity_start)}));
        drop(wrong_row);drop(wrong_row_weights);

        let rawbit_sensitivity_start=std::time::Instant::now();
        let rawbit_file=bytes.file.try_clone().map_err(|e|e.to_string())?;
        let mut rawbit_bytes=U0ByteCache{file:rawbit_file,rows:std::collections::VecDeque::new(),
            loads:0,bytes:0,capacity_peak:0};
        let (rawbit_count,rawbit_poly)=v_oracle_rawbit_owner(0,&[],right_counts[0],&height,&daa,&numeric,
            &canonical_aliases,&oracle_rows,&oracle_u,&source,&mut rawbit_bytes)?;
        let rawbit_delta_nonzero=rawbit_poly!=baseline_poly;
        whole_require(rawbit_delta_nonzero,"V native raw-bit left-value mutant insensitive")?;
        let rawbit_rejection=v_owner_compare(baseline_count,baseline_poly,rawbit_count,rawbit_poly);
        let rawbit_rejected=rawbit_rejection.err().as_deref()
            ==Some("V candidate/canonical RIGHT owner polynomial mismatch");
        whole_require(rawbit_rejected,"V native raw-bit left-value mutant bypassed owner guard")?;
        native_rawbit_sensitivity=Some(serde_json::json!({"kind":"native-fixture-raw-bit-instead-of-oracle-left-value",
            "owner":0,"delta_nonzero":rawbit_delta_nonzero,"rejected_at_owner_polynomial_boundary":rawbit_rejected,
            "duration_ns":screen_ns(rawbit_sensitivity_start)}));
    }
    let load_owners=std::cell::RefCell::new(vec![false;4096]);let physical_loads=std::cell::Cell::new(0u64);
    let mut candidate=s::EdgeVPrefixCandidateForTest::new(|owner|{
        whole_require(owner<4096,"V candidate owner load bounds")?;
        physical_loads.set(physical_loads.get().checked_add(1).ok_or("V physical load overflow")?);
        load_owners.borrow_mut()[owner]=true;
        crate::packed_rows::read_row(&source,1<<20,owner)
    },1<<20,4096)?;
    let mut round_results=Vec::with_capacity(2);let mut candidate_totals=[0u64;10];let mut oracle_totals=[0u64;8];
    let mut timing_ns=[0u64;4];let mut sender_ns=[[0u64;2];2];let mut ledger_peak=0usize;
    let mut cache_capacity_peak=0usize;let mut oracle_scratch_peak=0usize;
    let mut candidate_prior=final_claim;let mut oracle_prior=final_claim;
    let mut candidate_v0_q=None;let mut oracle_v0_q=None;
    for round in 0..2 {
        let stage=if round==0{"candidate-v0"}else{"candidate-v1"};
        active.replace(Some((stage.to_owned(),round,0)));
        v_event(stage,"begin",Some(round),Some(0),start)?;
        load_owners.borrow_mut().fill(false);let load_baseline=physical_loads.get();let candidate_io_before=source.io_metrics_snapshot();
        let mut ledger=Vec::<VOwnerRecord>::new();ledger.try_reserve_exact(4096).map_err(|e|e.to_string())?;
        let mut aggregate=[Fr::zero();3];let candidate_began=std::time::Instant::now();
        let prefix=if round==0{Vec::new()}else{vec![candidate_v0_q.ok_or("V candidate V0 challenge missing")?]};
        let candidate_metrics=candidate.round(12,19,1,&[19,19],&right_counts,&candidate_weights,left_value,&prefix,
            |right,owner,sink|adapter.visit_endpoint(&binding,right,owner,|term|sink(term)).map(|_|()),
            |owner,count,poly|{
                whole_require(owner==ledger.len(),"V candidate owner order")?;
                ledger.push(VOwnerRecord{count,polynomial:poly});for (a,b) in aggregate.iter_mut().zip(poly){*a+=b;}
                active.replace(Some((stage.to_owned(),round,owner+1)));
                if (owner+1)%1024==0{
                    v_event(stage,"progress",Some(round),Some(owner+1),start)?;
                    v_part(output,stage,Some(round),owner+1,Some(v_owner_digest(&ledger)?))?;
                }Ok(())
            })?;
        timing_ns[round*2]=screen_ns(candidate_began);
        let candidate_io=source.io_metrics_snapshot();let loaded=physical_loads.get()-load_baseline;
        let candidate_term_visits=candidate_metrics.visits;
        whole_require(ledger.len()==4096 && loaded==4096 && load_owners.borrow().iter().all(|x|*x)
            && candidate_metrics.vector_clones==4096 && candidate_metrics.cache_gets==4096
            && candidate_term_visits==338580202,"V candidate full RIGHT ledger/cache metrics")?;
        whole_require(v_sum_counts(&ledger)?==right_visits,"V candidate census reconciliation")?;
        let candidate_digest=v_owner_digest(&ledger)?;
        let candidate_ledger_bytes=ledger.capacity()*std::mem::size_of::<VOwnerRecord>();
        ledger_peak=ledger_peak.max(candidate_ledger_bytes);
        cache_capacity_peak=cache_capacity_peak.max(candidate_metrics.cache_capacity_peak_bytes);
        whole_require(std::mem::size_of::<VOwnerRecord>()==104 && candidate_ledger_bytes>=425984,
            "V candidate RAM ledger capacity")?;
        active.replace(Some((stage.to_owned(),round,4096)));
        v_event(stage,"end",Some(round),Some(4096),start)?;
        let oracle_stage=if round==0{"oracle-v0"}else{"oracle-v1"};
        active.replace(Some((oracle_stage.to_owned(),round,0)));
        v_event(oracle_stage,"begin",Some(round),Some(0),start)?;
        let oracle_prefix=if round==0{Vec::new()}else{vec![oracle_v0_q.ok_or("V oracle V0 challenge missing")?]};
        let oracle=v_oracle_pass(round,&oracle_prefix,&right_counts,&ledger,&height,&daa,&numeric,&canonical_aliases,
            &oracle_rows,&oracle_u,oracle_left_value,&source,&mut bytes,output,start,active)?;
        oracle_scratch_peak=oracle_scratch_peak.max(oracle.scratch_peak_bytes);
        timing_ns[round*2+1]=oracle.duration_ns;
        whole_require(oracle.polynomial==aggregate && oracle.term_visits==338580202
            && oracle.semantic_owner_calls==4096 && oracle.count_matches==4096
            && oracle.polynomial_matches==4096,"V independent RIGHT owner/polynomial differential")?;
        whole_require(candidate_digest==oracle.digest,"V independent owner digest mismatch")?;
        active.replace(Some((oracle_stage.to_owned(),round,4096)));
        v_event(oracle_stage,"end",Some(round),Some(4096),start)?;
        active.replace(Some(("sender".to_owned(),round,4096)));
        let oracle_sender_start=std::time::Instant::now();
        let (oracle_q,oracle_claim)=useq_reference_send(oracle.polynomial,oracle_prior,&mut oracle_sender)?;
        sender_ns[round][1]=screen_ns(oracle_sender_start);
        let candidate_sender_start=std::time::Instant::now();
        let (candidate_q,candidate_claim)=s::edge_u_sequence_send_for_test(aggregate,candidate_prior,&mut candidate_sender)?;
        sender_ns[round][0]=screen_ns(candidate_sender_start);
        let candidate_cont=candidate_sender.clone().challenge_scalar(b"native-u-high-join-continuation-v1");
        let oracle_cont=oracle_sender.clone().challenge_scalar(b"native-u-high-join-continuation-v1");
        whole_require(candidate_q==oracle_q && candidate_claim==oracle_claim && candidate_cont==oracle_cont
            && u0_counters(&candidate_sender)==u0_counters(&oracle_sender),"V actual/reference sender mismatch")?;
        candidate_prior=candidate_claim;oracle_prior=oracle_claim;
        if round==0{candidate_v0_q=Some(candidate_q);oracle_v0_q=Some(oracle_q);}
        active.replace(None);
        let candidate_counts=candidate_metrics.visits;let oracle_count=oracle.term_visits;
        candidate_totals[0]+=candidate_counts;candidate_totals[1]+=4096;candidate_totals[2]+=loaded;
        candidate_totals[3]+=candidate_io.read_calls-candidate_io_before.read_calls;
        candidate_totals[4]+=candidate_io.read_bytes-candidate_io_before.read_bytes;
        candidate_totals[5]+=candidate_metrics.cache_gets;candidate_totals[6]+=candidate_metrics.vector_clones;
        candidate_totals[7]+=candidate_metrics.replay_folds;candidate_totals[8]+=candidate_metrics.x_fold_fields;
        candidate_totals[9]+=candidate_metrics.bank_fold_entries;
        oracle_totals[0]+=oracle_count;oracle_totals[1]+=oracle.semantic_owner_calls;oracle_totals[2]+=oracle.row_loads;
        oracle_totals[3]+=oracle.io_read_calls;oracle_totals[4]+=oracle.io_read_bytes;
        let scalar_poly=|p:[Fr;3]|->Result<[String;3],String>{Ok([u0_hex_fr(&p[0])?,u0_hex_fr(&p[1])?,u0_hex_fr(&p[2])?])};
        let mut rec=serde_json::json!({"round":round,"candidate_polynomial":scalar_poly(aggregate)?,
            "oracle_polynomial":scalar_poly(oracle.polynomial)?,"owner_count_matches":oracle.count_matches,
            "owner_polynomial_matches":oracle.polynomial_matches,"candidate_owner_count_sum":v_sum_counts(&ledger)?,
            "oracle_owner_count_sum":right_visits,"candidate_owner_digest_blake2b256":candidate_digest,
            "oracle_owner_digest_blake2b256":oracle.digest,"candidate_term_visits":candidate_metrics.visits,
            "oracle_term_visits":oracle.term_visits,"candidate_semantic_owner_calls":candidate_metrics.vector_clones,
            "oracle_semantic_owner_calls":oracle.semantic_owner_calls,"candidate_physical_row_loads":loaded,
            "oracle_row_loads":oracle.row_loads,"candidate_io_read_calls":candidate_io.read_calls-candidate_io_before.read_calls,
            "candidate_io_read_bytes":candidate_io.read_bytes-candidate_io_before.read_bytes,
            "oracle_io_read_calls":oracle.io_read_calls,"oracle_io_read_bytes":oracle.io_read_bytes});
        let rec_tail=serde_json::json!({"candidate_cache_gets":candidate_metrics.cache_gets,"candidate_vector_clones":candidate_metrics.vector_clones,
            "candidate_replay_folds":candidate_metrics.replay_folds,"candidate_x_fold_fields":candidate_metrics.x_fold_fields,
            "candidate_bank_fold_entries":candidate_metrics.bank_fold_entries,
            "candidate_bank_capacity_peak_bytes":candidate_metrics.bank_capacity_peak_bytes,
            "candidate_cache_capacity_peak_bytes":candidate_metrics.cache_capacity_peak_bytes,
            "candidate_weights_capacity_bytes":candidate_weights.capacity_bytes(),
            "candidate_ledger_nominal_bytes":4096*104,"candidate_ledger_capacity_bytes":candidate_ledger_bytes,
            "oracle_weights_capacity_bytes":oracle_rows.capacity_bytes()+oracle_u.capacity_bytes(),
            "oracle_scratch_capacity_peak_bytes":oracle.scratch_peak_bytes,
            "candidate_duration_ns":timing_ns[round*2],"oracle_duration_ns":timing_ns[round*2+1],
            "candidate_sender_duration_ns":sender_ns[round][0],"oracle_sender_duration_ns":sender_ns[round][1],
            "candidate_challenge":u0_hex_fr(&candidate_q)?,"oracle_challenge":u0_hex_fr(&oracle_q)?,
            "candidate_claim":u0_hex_fr(&candidate_claim)?,"oracle_claim":u0_hex_fr(&oracle_claim)?,
            "candidate_counters":u0_counters(&candidate_sender),"oracle_counters":u0_counters(&oracle_sender),
            "candidate_continuation":u0_hex_fr(&candidate_cont)?,"oracle_continuation":u0_hex_fr(&oracle_cont)?,"sender_equal":true});
        rec.as_object_mut().ok_or("V round JSON object")?
            .extend(rec_tail.as_object().ok_or("V round JSON tail")?.clone());
        round_results.push(rec);drop(ledger);
    }
    whole_require(u0_file_info(&bytes.file)?==identity,
        "V final packed source identity")?;
    whole_require(candidate_totals[0]==677160404 && oracle_totals[0]==677160404
        && candidate_totals[2]==8192 && candidate_totals[5]==8192 && candidate_totals[6]==8192,
        "V aggregate candidate/oracle metrics")?;
    let result=serde_json::json!({"schema":"native-s12-v-prefix-result-v1","version":1,
        "state":"V_PREFIX_COMPONENT_PASS","input_sha256":input_sha,"prefix":{
            "local_round_matches":20,"local_oracle_matches":20,"high_round_matches":12,"high_u_matches":12,
            "initial_counters":fixture.initial_counters,"final_counters":final_counters,
            "final_continuation":final_continuation,"left_value_equal":left_value==oracle_left_value},
        "rounds":round_results,"sensitivity":{
            "native_fixture_term_c2":native_term_sensitivity.ok_or("V native c2 sensitivity missing")?,
            "native_fixture_row_point_u_for_r":native_row_sensitivity.ok_or("V native row-point sensitivity missing")?,
            "native_fixture_raw_bit_for_left_value":native_rawbit_sensitivity.ok_or("V native raw-bit sensitivity missing")?},
        "totals":{"candidate_term_visits":candidate_totals[0],
            "oracle_term_visits":oracle_totals[0],"candidate_semantic_owner_calls":candidate_totals[1],
            "oracle_semantic_owner_calls":oracle_totals[1],"candidate_physical_row_loads":candidate_totals[2],
            "oracle_row_loads":oracle_totals[2],"candidate_io_read_calls":candidate_totals[3],
            "candidate_io_read_bytes":candidate_totals[4],"oracle_io_read_calls":oracle_totals[3],
            "oracle_io_read_bytes":oracle_totals[4],"candidate_cache_gets":candidate_totals[5],
            "candidate_vector_clones":candidate_totals[6],"candidate_replay_folds":candidate_totals[7],
            "candidate_x_fold_fields":candidate_totals[8],"candidate_bank_fold_entries":candidate_totals[9]},
        "capacity":{"fr_bytes":std::mem::size_of::<Fr>(),"owner_record_size_bytes":std::mem::size_of::<VOwnerRecord>(),
            "ledger_nominal_bytes":425984,"candidate_ledger_capacity_peak_bytes":ledger_peak,
            "candidate_cache_capacity_peak_bytes":cache_capacity_peak,"candidate_weights_capacity_bytes":candidate_weights.capacity_bytes(),
            "oracle_weights_capacity_bytes":oracle_rows.capacity_bytes()+oracle_u.capacity_bytes(),
            "oracle_scratch_capacity_peak_bytes":oracle_scratch_peak},
        "preflight":{"prefix_replay_duration_ns":prefix_ns,"right_census_duration_ns":census_ns,
            "right_census_owners":right_counts.len(),"right_census_term_visits":right_visits},
        "timings_ns":timing_ns});
    let encoded=serde_json::to_vec(&result).map_err(|e|e.to_string())?;
    whole_require(encoded.len()<=16384,"V result artifact cap")?;
    let part=output.join("v-prefix.part");useq_save(&part,&result,16384,!part.exists())?;
    useq_finalize_checkpoint(&part,&output.join("v-prefix.json"))?;
    Ok(result)
}

fn v_run(){
    use std::io::Write;
    let start=std::time::Instant::now();let output=v_read_output().expect("V fresh output directory");
    let active=std::cell::RefCell::new(None);
    let result=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||v_execute(&output,start,&active)))
        .unwrap_or_else(|_|Err("V component panic".into()));
    let (status,failed_stage,reason,input_sha)=match &result{
        Ok(value)=>("V_PREFIX_COMPONENT_PASS",None,String::new(),value["input_sha256"].as_str().map(str::to_owned)),
        Err(reason)=>{
            let state=active.borrow().clone();
            if let Some((stage,round,owners))=state{
                if matches!(stage.as_str(),"candidate-v0"|"oracle-v0"|"candidate-v1"|"oracle-v1"){
                    v_event(&stage,"hold",Some(round),Some(owners),start).expect("V HOLD event");
                }
                v_part(&output,&stage,Some(round),owners,None).expect("V HOLD partial");
            }
            let end=reason.len().min(256);let mut end=end;while !reason.is_char_boundary(end){end-=1;}
            ("HOLD",active.borrow().as_ref().map(|x|x.0.clone()),reason[..end].to_owned(),None)
        }
    };
    let result_hash=if let Ok(value)=&result{Some(jh_sha(&serde_json::to_vec(value).expect("V result encode")).expect("V result hash"))}else{None};
    let completed=if status=="V_PREFIX_COMPONENT_PASS"{[4096u64,4096]}else{[0u64,0]};
    let summary=serde_json::json!({"schema":"native-s12-v-prefix-summary-v1","version":1,
        "result":status,"failed_stage":failed_stage,"reason":reason,"input_sha256":input_sha,
        "v_prefix_sha256":result_hash,"completed_candidate_owners":completed,
        "completed_oracle_owners":completed,"elapsed_ns":screen_ns(start)});
    let bytes=serde_json::to_vec(&summary).expect("V summary encode");assert!(bytes.len()<=4096,"V summary cap");
    let mut file=OpenOptions::new().write(true).create_new(true).open(output.join("summary.json")).expect("V exclusive summary");
    file.write_all(&bytes).expect("V summary write");file.sync_all().expect("V summary sync");drop(file);
    let footer=serde_json::json!({"result":status,"failed_stage":failed_stage,"elapsed_ns":screen_ns(start)});
    let line=format!("NATIVE_V_PREFIX_REPORT {footer}\n");assert!(line.len()<=1024,"V footer cap");
    let mut stdout=std::io::stdout().lock();stdout.write_all(line.as_bytes()).expect("V footer stdout");
    stdout.flush().expect("V footer flush");drop(stdout);
    assert!(result.is_ok(),"native V-prefix component HOLD");
}

#[test]
fn native_v_prefix_controls(){
    use ark_ff::BigInteger;
    assert!(v_fr(&format!("01{}","00".repeat(31))).is_ok());
    assert!(v_fr(&screen_hex(&Fr::MODULUS.to_bytes_le())).is_err());
    assert!(v_fr(&"FF".repeat(32)).is_err());
    assert!(v_fr(&"0a".repeat(32)).is_err());
    assert!(v_fr(&format!("{}00","00".repeat(32))).is_err());
    let zero=u0_hex_fr(&Fr::zero()).expect("canonical zero");
    let valid=serde_json::json!({"round":0,"previous_claim":zero,
        "polynomial":vec![zero.clone();3],"challenge":zero,"claim":zero,
        "continuation":zero,"transcript_counters":[0,0,0]});
    assert!(serde_json::from_value::<VLocalRound>(valid.clone()).is_ok());
    let trailing=serde_json::from_str::<VLocalRound>(&format!("{valid} trailing"))
        .err().expect("trailing data rejected").to_string();
    assert!(trailing.contains("trailing characters"),"trailing guard: {trailing}");
    let mut unknown=valid.clone();unknown["unexpected"]=serde_json::json!(0);
    let unknown=serde_json::from_value::<VLocalRound>(unknown)
        .err().expect("unknown field rejected").to_string();
    assert!(unknown.contains("unknown field"),"unknown-field guard: {unknown}");
    let duplicate=serde_json::from_str::<VInput>("{\"schema\":\"x\",\"schema\":\"y\"}").err()
        .expect("duplicate field rejected by typed parser").to_string();
    assert!(duplicate.contains("duplicate field"),"typed parser must reject duplicate keys: {duplicate}");
    assert!(serde_json::from_str::<VInput>("{\"schema\":false}").is_err());
    assert!(serde_json::from_str::<VLocalRound>("{\"round\":0,\"previous_claim\":\"\",\"polynomial\":[\"\",\"\"],\"challenge\":\"\",\"claim\":\"\",\"continuation\":\"\",\"transcript_counters\":[0,0,0]}").is_err());
    assert!(serde_json::from_str::<VLocalRound>("{\"round\":true,\"previous_claim\":\"\",\"polynomial\":[\"\",\"\",\"\"],\"challenge\":\"\",\"claim\":\"\",\"continuation\":\"\",\"transcript_counters\":[0,0,0]}").is_err());
    v_toy_controls().expect("V toy owner and sender boundary mutants");
}
#[test]
#[ignore="native RIGHT V0/V1 component; controller cap1200s/2GiB; fixture replay is not live-prefix authentication"]
fn native_s12_v_prefix_bounded(){v_run();}

#[test]
#[ignore="complete native U0 aggregate; separate1200s/2GiB controller"]
fn native_s12_u0_aggregate_bounded() {
    use std::io::Write;
    use std::os::windows::fs::MetadataExt;
    let start=std::time::Instant::now();
    let mut report=serde_json::json!({"schema":"native-s12-u0-aggregate-source-v1","version":1,
        "source_candidate_result":"HOLD","stage":"controls","reason":"","elapsed_ns":0,
        "geometry":{"headers":3073,"slots":4096,"width":1048576,"input_log":32,"row_log":32,"role":4},
        "identities":{"source_revision":U0_SOURCE,"fixture_sha256":U0_FIXTURE_SHA,"fixture_blake2b256":U0_FIXTURE_BLAKE,
            "witness_sha256":U0_WITNESS_SHA,"witness_blake2b256":U0_WITNESS_BLAKE,"parent_root":null,"parent_total":null,"aliases":null},
        "expected_terms":U0_TERMS,"controls":U0_CONTROL_NAMES.into_iter().map(|k|(k,false)).collect::<std::collections::BTreeMap<_,_>>(),
        "completed_owners":{"census":0,"candidate":0,"oracle":0},"terms":{"census":0,"candidate":0,"oracle":0},
        "candidate_polynomial":null,"oracle_polynomial":null,"challenge":null,"claim":null,"continuation":null,
        "transcript_counters":null,"equalities":{"polynomial":false,"zero_identity":false,"sender":false,"continuation":false},
        "candidate_metrics":null,"oracle_metrics":null,
        "storage":{"fr_bytes":std::mem::size_of::<Fr>(),"counts_capacity_bytes":0,"row_decoder_chunk_fields":65536,
            "row_decoder_chunk_bytes":65536*std::mem::size_of::<Fr>(),"cache_slots":4},
        "timings_ns":{"controls":0,"construction":0,"source_validation":0,"census":0,"candidate":0,"oracle":0,"send_round":0}});
    let output=std::env::var_os("NIPOPOW_NATIVE_U0_OUTPUT_DIR").map(std::path::PathBuf::from)
        .expect("U0 fresh output directory required");
    let md=std::fs::symlink_metadata(&output).expect("U0 output metadata");
    assert!(md.is_dir() && md.file_attributes()&0x400==0 && std::fs::read_dir(&output).unwrap().next().is_none(),
        "U0 output must be regular fresh empty directory");
    assert!(!output.canonicalize().unwrap().starts_with(std::env::temp_dir().canonicalize().unwrap()),"U0 output outside TEMP");
    let result=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||u0_execute(&mut report,start)))
        .unwrap_or_else(|_|Err("U0 source panic".into()));
    if let Err(reason)=&result {
        let mut end=reason.len().min(2048);while !reason.is_char_boundary(end){end-=1;}
        report["reason"]=serde_json::json!(&reason[..end]);
    } else {report["source_candidate_result"]=serde_json::json!("U0_PASS");report["stage"]=serde_json::json!("final-report");}
    u0_marker(start,"final-report","begin",None).expect("U0 final marker");
    report["elapsed_ns"]=serde_json::json!(screen_ns(start));
    let payload=serde_json::to_string(&report).expect("U0 report serialization");assert!(payload.len()<=65536,"U0 report cap");
    let mut summary=OpenOptions::new().write(true).create_new(true).open(output.join("summary.json")).expect("U0 exclusive summary");
    summary.write_all(payload.as_bytes()).expect("U0 summary write");summary.sync_all().expect("U0 summary sync");drop(summary);
    let mut out=std::io::stdout().lock();writeln!(out,"\nNATIVE_U0_REPORT {payload}").expect("U0 report stdout");
    out.flush().expect("U0 report flush");drop(out);
    u0_marker(start,"final-report","end",None).expect("U0 final marker");
    assert!(result.is_ok(),"native U0 source HOLD");
}

// Candidate-only aggregation diagnostic. The complete canonical R4 reference
// is reused; six whole-owner reference computations per round remain fresh.
const VG_PRIOR_RESULT:&str="265514133AF4191E7BACE982B3C6814A05489973473A49E13E3F670ABC5B0B11";
const VG_OWNERS:[usize;6]=[0,2,1023,2048,3072,4095];
fn vg_family_compare(actual:(usize,Fr),expected:(usize,Fr))->Result<(),String>{
    whole_require(actual.0==expected.0,"grouped family count mismatch")?;
    whole_require(actual.1==expected.1,"grouped family bank mismatch")
}
fn vg_family_controls()->Result<(),String>{
    use crate::sparse_stream_roster as s;
    let parent=WorkTreeHistoryPlan::compile(3073,12,[0u8;32],[0u8;28])?;
    let height=HeightWork::compile_history(&parent)?;
    let daa=DaaHistoryRoster::compile(&parent)?;
    let adapter=Role4EndpointAdapter::new(&height,&daa,Role4EndpointScope::WholeS12)?;
    let r=general(32,5);let u=general(32,103);let v=general(32,211);let q=general(20,43);
    let width=1usize<<20;
    for left in [Fr::from(37u64),Fr::zero()] {
        let ctx=s::EdgeGroupedVContextForTest::new(&adapter,&r,&u,left)?;
        whole_require(ctx.template_visits()==155648,"grouped local template census")?;
        for owner in [0usize,2048,3072,4095] {
            let (count,b0)=ctx.family_owner(owner)?;
            let mut canonical_b=vec![Fr::zero();width];let mut canonical_count=0usize;
            let mut coefficient=Fr::zero();let mut wrong_row_b=Fr::zero();
            daa.visit_owner_terms(owner as u64,|term|{
                if (term.row&((1<<19)-1))>>17!=3{return Ok(());}
                whole_require(term.gate.left/width==owner && term.gate.right==owner*width
                    && [term.gate.c0,term.gate.c1,term.gate.c2,term.gate.c3]
                        ==[Fr::zero(),Fr::one(),Fr::zero(),Fr::zero()],"grouped canonical family shape")?;
                let composite_row=term.row+(1usize<<31);
                let weight=u0_direct_weight(&r,composite_row)*u0_direct_weight(&u,term.gate.left);
                canonical_b[0]+=left*weight;
                coefficient+=weight*u0_direct_weight(&v,term.gate.right);
                canonical_count+=1;
                // A deliberately wrong complement keeps the full template's
                // row numbers after the removed M1 image instead of renumbering.
                let bad_row=if owner==2048 && term.gate.left%width>=827392 {
                    composite_row+8192
                }else{composite_row};
                wrong_row_b+=left*u0_direct_weight(&r,bad_row)*u0_direct_weight(&u,term.gate.left);
                Ok(())
            })?;
            vg_family_compare((count,b0),(canonical_count,canonical_b[0]))?;
            whole_require(count==match owner{2048=>73728,3072=>0,_=>81920},"grouped family owner class")?;
            whole_require(b0*u0_direct_weight(&v,owner*width)==left*coefficient,
                "grouped family general-v coefficient")?;
            let mut candidate_b=vec![Fr::zero();width];candidate_b[0]=b0;
            whole_require(candidate_b==canonical_b,"grouped complete B bank")?;
            let mut candidate_a=vec![Fr::zero();width];let mut canonical_a=candidate_a.clone();
            let mut x=vec![Fr::from(17u64);width];let mut reference_x=x.clone();
            let mut factor=Fr::one();
            for k in 0..=20 {
                if matches!(k,0|1|19) {
                    let actual:[Fr;3]=crate::gkr::quadratic_message(&candidate_a,&candidate_b,&x)
                        .as_slice().try_into().map_err(|_|"grouped family message extent")?;
                    let expected=useq_message(&canonical_a,&canonical_b,&reference_x);
                    v_owner_compare(count,expected,canonical_count,actual)?;
                    whole_require(actual==[b0*factor,-b0*factor,Fr::zero()],"grouped prefix factor")?;
                    if owner==2048 && !left.is_zero() && k==1 {
                        let omitted=[b0,-b0,Fr::zero()];
                        whole_require(omitted!=expected && v_owner_compare(count,expected,count,omitted).is_err(),
                            "grouped omitted-prefix mutant insensitive")?;
                    }
                }
                if k==20 {
                    whole_require(candidate_a.len()==1 && candidate_b.len()==1 && x.len()==1,
                        "grouped terminal extent")?;
                    whole_require(candidate_a==canonical_a && candidate_b==canonical_b && x==reference_x
                        && candidate_a[0].is_zero() && candidate_b[0]==b0*factor,"grouped terminal differential")?;
                    break;
                }
                crate::gkr::fold(&mut candidate_a,q[k]);crate::gkr::fold(&mut candidate_b,q[k]);
                crate::gkr::fold(&mut x,q[k]);
                useq_fold(&mut canonical_a,q[k]);useq_fold(&mut canonical_b,q[k]);useq_fold(&mut reference_x,q[k]);
                factor*=Fr::one()-q[k];
            }
            if owner==2048 && !left.is_zero() {
                whole_require(!b0.is_zero(),"grouped family fault support")?;
                for fault in [(count,Fr::zero()),(count,b0+b0),(count,wrong_row_b),(count+1,b0)] {
                    whole_require(fault!=(count,b0) && vg_family_compare(fault,(count,b0)).is_err(),
                        "grouped isolated bank/count mutant")?;
                }
                let mut wrong_owner_u=u.clone();wrong_owner_u[20]+=Fr::one();
                let owner_ctx=s::EdgeGroupedVContextForTest::new(&adapter,&r,&wrong_owner_u,left)?;
                let mut wrong_tag_r=r.clone();wrong_tag_r[31]=Fr::one()-wrong_tag_r[31];
                let tag_ctx=s::EdgeGroupedVContextForTest::new(&adapter,&wrong_tag_r,&u,left)?;
                for fault in [owner_ctx.family_owner(owner)?,tag_ctx.family_owner(owner)?] {
                    whole_require(fault!=(count,b0) && vg_family_compare(fault,(count,b0)).is_err(),
                        "grouped isolated owner/tag mutant")?;
                }
            }
        }
        whole_require(ctx.family_owner(4096).is_err(),"grouped owner bound accepted")?;
    }
    whole_require(s::EdgeGroupedVContextForTest::new(&adapter,&r[..31],&u,Fr::one()).is_err()
        && s::EdgeGroupedVContextForTest::new(&adapter,&r,&u[..31],Fr::one()).is_err(),
        "grouped point dimensions accepted")?;
    let binding=adapter.binding();let mut wrong_binding=binding.clone();wrong_binding.headers+=1;
    whole_require(adapter.grouped_v_context_for_test(&wrong_binding,&r,&u,Fr::one()).is_err(),
        "grouped wrong binding accepted")?;
    let ctx=s::EdgeGroupedVContextForTest::new(&adapter,&r,&u,Fr::one())?;
    let loads=std::cell::Cell::new(0usize);
    let mut candidate=s::EdgeGroupedVCandidateForTest::new(|_|{loads.set(loads.get()+1);Ok(vec![Fr::zero();width])},width,4096)?;
    whole_require(candidate.owner(&ctx,4096,81920,&[]).err().as_deref()
        ==Some("grouped V owner context or geometry rejected"),"grouped invalid owner guard")?;
    whole_require(candidate.owner(&ctx,0,0,&[]).err().as_deref()
        ==Some("grouped V inactive occurrences exceed canonical owner count"),"grouped isolated count underflow guard")?;
    let weights=s::EdgeFallbackWeightsForTest::new(&r,&u,20);
    for owner in [0usize,2048,3072] {
        let canonical_count=adapter.visit_endpoint(&binding,false,owner,|_|Ok(()))?;
        whole_require(candidate.owner(&ctx,owner,canonical_count,&vec![Fr::one();21]).err().as_deref()
            ==Some("grouped V owner context or geometry rejected"),"grouped isolated prefix guard")?;
        let loads_before=loads.get();
        whole_require(candidate.owner(&ctx,owner,canonical_count+1,&[]).is_err()
            && loads.get()==loads_before,"grouped physical census drift reached X loader")?;
        for k in [0usize,1,19,20] {
            // This positive path exercises the actual endpoint-side flag,
            // injection, bank folding and terminal, not only error guards.
            let grouped=candidate.owner(&ctx,owner,canonical_count,&q[..k])?;
            let canonical=s::edge_fallback_prefix_for_test(false,owner,20,12,19,1,&[19,19],
                canonical_count,&weights,Fr::one(),&q[..k],
                |left,slot,sink|adapter.visit_endpoint(&binding,left,slot,|edge|sink(edge)).map(|_|()),
                |_|Ok(vec![Fr::zero();width]),None)?;
            whole_require(grouped.message==canonical.message && grouped.terminal==canonical.terminal
                && grouped.folded_x==canonical.folded_x
                && grouped.metrics.logical_occurrences==canonical.metrics.visits
                && grouped.metrics.physical_visits+grouped.metrics.inactive_occurrences==canonical.metrics.visits,
                "grouped positive complete-owner/terminal differential")?;
        }
    }
    let daa_other=DaaHistoryRoster::compile(&parent)?;
    let daa_ctx=daa.grouped_v_context_for_test(&r,&u,Fr::one())?;
    whole_require(daa_other.grouped_v_owner_for_test(&daa_ctx,0).is_err(),"grouped foreign roster accepted")?;
    Ok(())
}

#[test]
fn native_v_grouped_controls(){vg_family_controls().expect("native grouped family/guard controls");}

fn vg_oracle_owner(owner:usize,prefix:&[Fr],right_count:usize,height:&HeightWork<'_>,daa:&DaaHistoryRoster<'_>,
    numeric:&crate::daa_work_actions::DaaWorkActions<'_>,aliases:&[OracleTuple],rows:&U0OracleWeights,
    uweights:&U0OracleWeights,left_value:Fr,source:&crate::packed::PackedFile,
)->Result<(usize,[Fr;3],usize),String>{
    whole_require(owner<4096 && prefix.len()<20,"grouped fresh reference geometry")?;
    let width=1usize<<20;let mut a=vec![Fr::zero();width];let mut b=vec![Fr::zero();width];
    let mut x=useq_legacy_row(source,owner)?;let mut count=0usize;
    let capacity=(a.capacity()+b.capacity()+x.capacity())*std::mem::size_of::<Fr>();
    whole_oracle_partition(height,daa,numeric,aliases,false,owner,|term|{
        whole_require(term.right/width==owner,"grouped fresh reference RIGHT owner")?;
        let weight=rows.at(term.row)?*uweights.at(term.left)?;let wire=term.right%width;
        a[wire]+=weight*(term.c[2]+term.c[3]*left_value);
        b[wire]+=weight*(term.c[0]+term.c[1]*left_value);
        count=count.checked_add(1).ok_or("grouped reference count overflow")?;Ok(())
    })?;
    whole_require(count==right_count,"grouped reference count")?;
    for q in prefix {useq_fold(&mut a,*q);useq_fold(&mut b,*q);useq_fold(&mut x,*q);}
    Ok((count,useq_message(&a,&b,&x),capacity))
}

fn vg_reference(round:usize)->Result<([Fr;3],Fr,Fr,[u64;3],Fr,&'static str),String>{
    let (poly,q,claim,counters,continuation,digest)=match round {
        0=>([
            "3597489CD6A8DD7876CEAE149F715E799DDB45CA1158C3E82DB8574D2362DF29",
            "99CD7DC3EDE8A8F14380DD112FD9B91E6F27AD1599729B59BF15B0C082BC3A14",
            "7460F3887741D9C597B9F95D649F77433D26D4CB9BEDB55A55DA3F25EFA5402F"],
            "2714E50AE48C3B15EAEBCE447DDC5DDF4158205C15723C0F58536624DC7AB304",
            "0301B58B055CAA72FA6867D31FB1AE77C2BBCC985C8635CB7AB81D9B289F792B",[65,88,34954],
            "D49BF2BF8752C12C355A0865217F1009DA94ADB99E02937B6354559F943BA321",
            "EE9CFBE192140C31032409ACB0EB7FA01A49E9B5CB6A5DA90B12D18CDC5901FE"),
        1=>([
            "1EEC20F22877D6E9C7AE4EF3C417470B44159E21D7BBFA593BA17DA377CF2F19",
            "6A62C14BDF9455179E57152CEA53B5BB877BAC3632199913997C847330BEEB2C",
            "5FC6B13BFCC36B0FEF9427B43CFED2F56CC6E621E9804774BE3901A3EEDEF62C"],
            "265D863156ECFE4910B43349CA72D6A26F8469B8F5B1145BF2AC39A3A2BA352A",
            "9D63BC7A67FC4208BE84514A4AE84C512EDA5153C8BEACC9C6C7395EDBAC0C27",[66,91,35314],
            "6FDBF022135A593803D6BA728F44BDC945E0AE814019F4BB6BFF074A5F98250A",
            "6DEA72188121888F9E7C5668C84F0188B779B422E883B12F9E0E36E00A09ACDF"),
        _=>return Err("grouped reference round".into()),
    };
    Ok(([v_fr(poly[0])?,v_fr(poly[1])?,v_fr(poly[2])?],v_fr(q)?,v_fr(claim)?,counters,v_fr(continuation)?,digest))
}
fn vg_event(stage:&str,edge:&str,round:usize,completed:usize,start:std::time::Instant)->Result<(),String>{
    use std::io::Write;
    let event=serde_json::json!({"stage":stage,"edge":edge,"round":round,"completed_owners":completed,
        "elapsed_ns":screen_ns(start)});
    let line=format!("NATIVE_V_GROUPED_EVENT {event}\n");whole_require(line.len()<=1024,"grouped event cap")?;
    let mut stdout=std::io::stdout().lock();stdout.write_all(line.as_bytes()).map_err(|e|e.to_string())?;
    stdout.flush().map_err(|e|e.to_string())
}
fn vg_part(output:&std::path::Path,stage:&str,round:usize,completed:usize)->Result<(),String>{
    let path=output.join("v-grouped.part");
    useq_save(&path,&serde_json::json!({"stage":stage,"round":round,"completed_owners":completed}),32768,!path.exists())
}
fn vg_execute(output:&std::path::Path,start:std::time::Instant,
    active:&std::cell::RefCell<Option<(String,usize,usize)>>)->Result<serde_json::Value,String>{
    use crate::sparse_stream_roster as s;
    active.replace(Some(("prefix".into(),0,0)));
    let (fixture,input_bytes)=v_read_input()?;let input_sha=jh_sha(&input_bytes)?;
    whole_require(input_sha=="4EFE157A2D04C2B95431D699AB20B38F6713321DDFC35D41640891A733329AD4",
        "grouped reference prefix identity")?;
    let replay_start=std::time::Instant::now();
    let (u,r,left,oracle_left,final_counters,final_continuation,final_claim,mut sender,mut reference_sender)=v_validate_prefix(&fixture)?;
    let prefix_ns=screen_ns(replay_start);
    let native=input();let parent=WorkTreeHistoryPlan::compile(3073,12,native.root(),native.total_be28())?;drop(native);
    let height=HeightWork::compile_history(&parent)?;let daa=DaaHistoryRoster::compile(&parent)?;
    let adapter=Role4EndpointAdapter::new(&height,&daa,Role4EndpointScope::WholeS12)?;let binding=adapter.binding();
    let aliases=whole_aliases(&daa)?;let numeric=crate::daa_work_actions::DaaWorkActions::new(&parent)?;
    active.replace(Some(("right-census".into(),0,0)));
    let census_start=std::time::Instant::now();
    let counts=s::edge_v_census_for_test(20,12,19,1,&[19,19],
        |side,owner,sink|adapter.visit_endpoint(&binding,side,owner,|term|sink(term)).map(|_|()),|_,_|Ok(()))?;
    whole_require(counts.len()==4096 && v_sum_usize_counts(&counts)?==338580202,"grouped canonical census")?;
    let census_ns=screen_ns(census_start);
    active.replace(Some(("summary".into(),0,0)));
    let summary_start=std::time::Instant::now();let ctx=s::EdgeGroupedVContextForTest::new(&adapter,&r,&u,left)?;
    whole_require(ctx.template_visits()==155648,"grouped template evaluations")?;
    let summary_ns=screen_ns(summary_start);
    let (source,held,identity)=useq_admit()?;
    let rows=U0OracleWeights::new(&r)?;let uweights=U0OracleWeights::new(&u)?;
    let weights_capacity=ctx.capacity_bytes();let reference_weights=rows.capacity_bytes()+uweights.capacity_bytes();
    let loads=std::cell::Cell::new(0u64);let seen=std::cell::RefCell::new(vec![false;4096]);
    let mut candidate=s::EdgeGroupedVCandidateForTest::new(|owner|{
        whole_require(owner<4096,"grouped loader owner")?;loads.set(loads.get()+1);seen.borrow_mut()[owner]=true;
        crate::packed_rows::read_row(&source,1<<20,owner)
    },1<<20,4096)?;
    let mut rounds=Vec::new();let mut timings=[0u64;4];let mut prior=final_claim;let mut reference_prior=final_claim;
    let mut candidate_q0=None;let mut reference_q0=None;
    let mut ledger_peak=0usize;let mut bank_peak=0usize;let mut cache_peak=0usize;let mut scratch_peak=0usize;
    for round in 0..2 {
        let stage=if round==0{"candidate-v0"}else{"candidate-v1"};
        active.replace(Some((stage.into(),round,0)));vg_event(stage,"begin",round,0,start)?;
        let prefix=if round==0{Vec::new()}else{vec![candidate_q0.ok_or("grouped fresh V0 absent")?]};
        let reference_prefix=if round==0{Vec::new()}else{vec![reference_q0.ok_or("grouped reference V0 absent")?]};
        let (expected_poly,expected_q,expected_claim,expected_counters,expected_continuation,expected_digest)=vg_reference(round)?;
        seen.borrow_mut().fill(false);let loads_before=loads.get();let io_before=source.io_metrics_snapshot();
        let mut ledger=Vec::<VOwnerRecord>::new();ledger.try_reserve_exact(4096).map_err(|e|e.to_string())?;
        let mut aggregate=[Fr::zero();3];let began=std::time::Instant::now();
        let metrics=candidate.round(&ctx,&counts,&prefix,|owner,total,physical,inactive,polynomial|{
            whole_require(owner==ledger.len() && physical.checked_add(inactive)==Some(total),"grouped ledger order/counts")?;
            ledger.push(VOwnerRecord{count:total,polynomial});for (a,b) in aggregate.iter_mut().zip(polynomial){*a+=b;}
            active.replace(Some((stage.into(),round,owner+1)));
            if (owner+1)%1024==0 {vg_event(stage,"progress",round,owner+1,start)?;vg_part(output,stage,round,owner+1)?;}
            Ok(())
        })?;
        timings[round*2]=screen_ns(began);let io_after=source.io_metrics_snapshot();let loaded=loads.get()-loads_before;
        let digest=v_owner_digest(&ledger)?;
        whole_require(ledger.len()==4096 && v_sum_counts(&ledger)?==338580202 && digest==expected_digest
            && aggregate==expected_poly,"grouped complete retained canonical reference mismatch")?;
        let m=&metrics.fallback;
        whole_require(metrics.physical_visits==3125994 && metrics.inactive_occurrences==335454208
            && metrics.logical_occurrences==338580202 && metrics.family_contributions==4095
            && metrics.nonzero_injections<=4095 && m.visits==metrics.physical_visits
            && m.cache_gets==4096 && m.vector_clones==4096 && loaded==4096
            && seen.borrow().iter().all(|x|*x) && m.replay_folds==4096*round as u64
            && m.x_fold_fields==4294967296*round as u64,"grouped measured accounting")?;
        whole_require(io_after.read_calls-io_before.read_calls==65536
            && io_after.read_bytes-io_before.read_bytes==536870912,"grouped candidate IO")?;
        let ledger_bytes=ledger.capacity()*std::mem::size_of::<VOwnerRecord>();ledger_peak=ledger_peak.max(ledger_bytes);
        bank_peak=bank_peak.max(m.bank_capacity_peak_bytes);cache_peak=cache_peak.max(m.cache_capacity_peak_bytes);
        vg_event(stage,"end",round,4096,start)?;
        let ref_stage=if round==0{"reference-v0"}else{"reference-v1"};
        active.replace(Some((ref_stage.into(),round,0)));vg_event(ref_stage,"begin",round,0,start)?;
        let reference_start=std::time::Instant::now();let mut fresh=Vec::new();let mut round_scratch=0usize;
        for owner in VG_OWNERS {
            let (oracle_count,oracle_poly,scratch)=vg_oracle_owner(owner,&reference_prefix,counts[owner],&height,&daa,
                &numeric,&aliases,&rows,&uweights,oracle_left,&source)?;
            let record=ledger[owner];v_owner_compare(oracle_count,oracle_poly,record.count,record.polynomial)?;
            round_scratch=round_scratch.max(scratch);
            fresh.push(serde_json::json!({"owner":owner,"candidate_count":record.count,"oracle_count":oracle_count,
                "candidate_polynomial":useq_poly(record.polynomial)?,"oracle_polynomial":useq_poly(oracle_poly)?}));
            active.replace(Some((ref_stage.into(),round,fresh.len())));
        }
        timings[round*2+1]=screen_ns(reference_start);scratch_peak=scratch_peak.max(round_scratch);
        vg_event(ref_stage,"end",round,6,start)?;active.replace(Some(("sender".into(),round,6)));
        let reference_send_start=std::time::Instant::now();
        let (oracle_q,oracle_claim)=useq_reference_send(expected_poly,reference_prior,&mut reference_sender)?;
        let oracle_sender_ns=screen_ns(reference_send_start);let sender_start=std::time::Instant::now();
        let (q,claim)=s::edge_u_sequence_send_for_test(aggregate,prior,&mut sender)?;let sender_ns=screen_ns(sender_start);
        let continuation=sender.clone().challenge_scalar(JH_CONTINUATION);
        let oracle_continuation=reference_sender.clone().challenge_scalar(JH_CONTINUATION);
        whole_require(q==oracle_q && q==expected_q && claim==oracle_claim && claim==expected_claim
            && continuation==oracle_continuation && continuation==expected_continuation
            && u0_counters(&sender)==expected_counters && u0_counters(&reference_sender)==expected_counters,
            "grouped actual/reference retained sender mismatch")?;
        if round==0{candidate_q0=Some(q);reference_q0=Some(oracle_q);}
        prior=claim;reference_prior=oracle_claim;active.replace(None);
        let mut rec=serde_json::json!({"round":round,"candidate_polynomial":useq_poly(aggregate)?,
            "oracle_polynomial":useq_poly(expected_poly)?,"candidate_challenge":u0_hex_fr(&q)?,"oracle_challenge":u0_hex_fr(&oracle_q)?,
            "candidate_claim":u0_hex_fr(&claim)?,"oracle_claim":u0_hex_fr(&oracle_claim)?,
            "candidate_counters":u0_counters(&sender),"oracle_counters":u0_counters(&reference_sender),
            "candidate_continuation":u0_hex_fr(&continuation)?,"oracle_continuation":u0_hex_fr(&oracle_continuation)?,
            "candidate_owner_digest_blake2b256":digest,"oracle_owner_digest_blake2b256":expected_digest,"sender_equal":true,
            "owner_count_matches":fresh.len(),"owner_polynomial_matches":fresh.len(),"candidate_owner_count_sum":v_sum_counts(&ledger)?,
            "candidate_term_visits":m.visits,"candidate_semantic_owner_calls":m.vector_clones,"candidate_physical_row_loads":loaded,
            "candidate_io_read_calls":io_after.read_calls-io_before.read_calls,"candidate_io_read_bytes":io_after.read_bytes-io_before.read_bytes});
        let tail=serde_json::json!({"candidate_cache_gets":m.cache_gets,"candidate_vector_clones":m.vector_clones,
            "candidate_replay_folds":m.replay_folds,"candidate_x_fold_fields":m.x_fold_fields,"candidate_bank_fold_entries":m.bank_fold_entries,
            "candidate_bank_capacity_peak_bytes":m.bank_capacity_peak_bytes,"candidate_cache_capacity_peak_bytes":m.cache_capacity_peak_bytes,
            "candidate_weights_capacity_bytes":weights_capacity,"candidate_ledger_nominal_bytes":425984,"candidate_ledger_capacity_bytes":ledger_bytes,
            "physical_term_visits":metrics.physical_visits,"represented_inactive_terms":metrics.inactive_occurrences,
            "logical_term_count":metrics.logical_occurrences,"family_owners":metrics.family_contributions,"nonzero_injections":metrics.nonzero_injections,
            "fresh_reference":fresh,"fresh_reference_weights_capacity_bytes":reference_weights,"fresh_reference_scratch_capacity_peak_bytes":round_scratch,
            "candidate_duration_ns":timings[round*2],"fresh_reference_duration_ns":timings[round*2+1],
            "candidate_sender_duration_ns":sender_ns,"oracle_sender_duration_ns":oracle_sender_ns});
        rec.as_object_mut().ok_or("grouped round object")?.extend(tail.as_object().ok_or("grouped tail object")?.clone());rounds.push(rec);
    }
    whole_require(u0_file_info(&held)?==identity,"grouped witness final identity")?;
    let result=serde_json::json!({"schema":"native-s12-v-grouped-result-v1","version":1,"state":"V_GROUPED_COMPONENT_PASS",
        "input_sha256":input_sha,"reference_sha256":VG_PRIOR_RESULT,"prefix":{
            "local_round_matches":20,"local_oracle_matches":20,"high_round_matches":12,"high_u_matches":12,
            "initial_counters":fixture.initial_counters,"final_counters":final_counters,"final_continuation":final_continuation,"left_value_equal":left==oracle_left},
        "template":{"local_template_visits":ctx.template_visits(),"owner_decisions":4096,"family_contributions":4095},
        "rounds":rounds,"capacity":{"fr_bytes":std::mem::size_of::<Fr>(),"owner_record_size_bytes":std::mem::size_of::<VOwnerRecord>(),
            "ledger_nominal_bytes":425984,"candidate_ledger_capacity_peak_bytes":ledger_peak,"candidate_bank_capacity_peak_bytes":bank_peak,
            "candidate_cache_capacity_peak_bytes":cache_peak,"candidate_weights_capacity_bytes":weights_capacity,
            "fresh_reference_weights_capacity_bytes":reference_weights,"fresh_reference_scratch_capacity_peak_bytes":scratch_peak},
        "preflight":{"prefix_replay_duration_ns":prefix_ns,"right_census_duration_ns":census_ns,"right_census_owners":counts.len(),
            "right_census_term_visits":338580202,"summary_duration_ns":summary_ns,"template_term_evaluations":ctx.template_visits()},"timings_ns":timings});
    let part=output.join("v-grouped.part");useq_save(&part,&result,32768,!part.exists())?;
    useq_finalize_checkpoint(&part,&output.join("v-grouped.json"))?;Ok(result)
}
fn vg_run(){
    use std::io::Write;
    let start=std::time::Instant::now();
    let output=std::path::PathBuf::from(std::env::var_os("NIPOPOW_NATIVE_V_GROUPED_OUTPUT_DIR").expect("grouped output required"));
    assert!(output.is_dir() && !std::fs::read_dir(&output).expect("grouped output inventory").next().is_some(),"grouped output not fresh");
    let active=std::cell::RefCell::new(None);
    let result=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||vg_execute(&output,start,&active)))
        .unwrap_or_else(|_|Err("grouped component panic".into()));
    let (status,failed_stage,reason,input_sha)=match &result {
        Ok(value)=>("V_GROUPED_COMPONENT_PASS",None,String::new(),value["input_sha256"].as_str().map(str::to_owned)),
        Err(reason)=>{
            if let Some((stage,round,owners))=active.borrow().clone(){
                if matches!(stage.as_str(),"candidate-v0"|"reference-v0"|"candidate-v1"|"reference-v1") {
                    vg_event(&stage,"hold",round,owners,start).expect("grouped HOLD event");
                }
                vg_part(&output,&stage,round,owners).expect("grouped HOLD partial");
            }
            let mut end=reason.len().min(256);while !reason.is_char_boundary(end){end-=1;}
            ("HOLD",active.borrow().as_ref().map(|x|x.0.clone()),reason[..end].to_owned(),None)
        }
    };
    let result_sha=if let Ok(value)=&result{Some(jh_sha(&serde_json::to_vec(value).expect("grouped result encoding")).expect("grouped result SHA"))}else{None};
    let summary=serde_json::json!({"schema":"native-s12-v-grouped-summary-v1","version":1,"result":status,
        "failed_stage":failed_stage,"reason":reason,"input_sha256":input_sha,"v_grouped_sha256":result_sha,
        "completed_candidate_owners":if result.is_ok(){[4096usize,4096]}else{[0,0]},
        "completed_reference_owners":if result.is_ok(){[6usize,6]}else{[0,0]},"elapsed_ns":screen_ns(start)});
    useq_save(&output.join("summary.json"),&summary,4096,true).expect("grouped summary");
    let footer=serde_json::json!({"result":status,"failed_stage":failed_stage,"elapsed_ns":screen_ns(start)});
    let line=format!("NATIVE_V_GROUPED_REPORT {footer}\n");assert!(line.len()<=1024);
    let mut stdout=std::io::stdout().lock();stdout.write_all(line.as_bytes()).expect("grouped footer write");
    stdout.flush().expect("grouped footer flush");drop(stdout);
    assert!(result.is_ok(),"native V-grouped component HOLD");
}
#[test]
#[ignore="native grouped V0/V1 reference-reuse diagnostic; separate300s/2GiB controller"]
fn native_s12_v_grouped_bounded(){vg_run();}


// Complete V remains a fixture-conditioned diagnostic. Every new helper is
// isolated here; the retained source above and production primitives are literal.
const VC_REFERENCE:&str="FBFB9EE28CBB33A1D4A4D445AAB877E619985A3F436EC4B9F2831F5F6252D7A7";
const VC_LOCAL_KEYS:&str="semantic_owner_calls physical_term_visits represented_inactive_terms logical_term_count family_contributions nonzero_injections zero_a_owners nonzero_a_owners physical_row_loads cache_gets vector_clones io_read_calls io_read_bytes replay_folds x_fold_fields bank_fold_entries fold_ns duration_ns";
const VC_TERMINAL_KEYS:&str="semantic_owner_calls real_x_owners physical_term_visits represented_inactive_terms logical_term_count family_contributions nonzero_injections physical_row_loads cache_gets vector_clones io_read_calls io_read_bytes replay_folds x_fold_fields bank_fold_entries fold_ns";
const VC_ORACLE_KEYS:&str="owner_bank_builds canonical_term_visits canonical_count row_decodes physical_row_loads io_read_calls io_read_bytes owner_round_comparisons owner_terminal_comparisons x_fold_fields bank_fold_entries channel_owner_count channel_field_count";
const VC_LINE_KEYS:&str="owners candidate_row_decodes oracle_row_decodes fr_value_comparisons local_point_coordinate_comparisons local_primitive_calls global_coefficient_comparisons endpoint_comparisons candidate_io_read_calls candidate_io_read_bytes oracle_io_read_calls oracle_io_read_bytes local_primitive_pair_degree_cells_source_count";
const VC_CAP_KEYS:&str="fr_bytes owner_record_size_bytes candidate_ledgers_nominal_bytes candidate_ledgers_capacity_bytes candidate_terminal_nominal_bytes candidate_terminal_capacity_bytes oracle_terminal_capacity_bytes canonical_channels_nominal_bytes canonical_channels_capacity_bytes candidate_bank_peak_bytes candidate_cache_peak_bytes candidate_weights_capacity_bytes oracle_bank_peak_bytes oracle_weights_capacity_bytes line_candidate_row_peak_bytes line_legacy_row_peak_bytes line_local_coefficients_capacity_peak_bytes line_global_candidate_capacity_bytes line_global_oracle_capacity_bytes proof_capacity_bytes line_primitive_peak_bytes line_primitive_peak_status line_primitive_source_bound_bytes";
const VC_TIME_KEYS:&str="prefix_replay census family_summary local_candidate terminal_candidate canonical_oracle oracle_sender_replay high_v line wiring codec verify total";

fn vc_sha_len(n:usize)->Result<u32,String>{
    whole_require(n<=393216,"complete SHA input cap")?;
    u32::try_from(n).map_err(|_|"complete SHA length conversion".into())
}
fn vc_sha(bytes:&[u8])->Result<String,String>{
    use std::ffi::c_void;
    #[link(name="crypt32")]
    extern "system"{fn CryptHashCertificate2(alg:*const u16,flags:u32,reserved:*mut c_void,
        data:*const u8,len:u32,out:*mut u8,out_len:*mut u32)->i32;}
    let n=vc_sha_len(bytes.len())?;let alg=[83u16,72,65,50,53,54,0];
    let mut out=[0u8;32];let mut size=32u32;
    // Synchronous Windows ABI; all buffers are live, bounded and nonaliasing.
    let ok=unsafe{CryptHashCertificate2(alg.as_ptr(),0,std::ptr::null_mut(),bytes.as_ptr(),n,out.as_mut_ptr(),&mut size)};
    jh_hash_result(ok,size,out)
}
fn vc_field_bytes(values:&[Fr])->Result<Vec<u8>,String>{
    use ark_serialize::CanonicalSerialize;
    let mut out=Vec::with_capacity(values.len()*32);
    for value in values{value.serialize_compressed(&mut out).map_err(|e|e.to_string())?;}
    whole_require(out.len()==values.len()*32,"complete field encoding width")?;Ok(out)
}
fn vc_fields_sha(values:&[Fr])->Result<String,String>{vc_sha(&vc_field_bytes(values)?)}
fn vc_triplet_sha(values:&[[Fr;3]])->Result<String,String>{
    whole_require(values.len()==4096,"complete terminal digest extent")?;
    let mut data=Vec::with_capacity(393216);
    for value in values{data.extend(vc_field_bytes(value)?);}
    whole_require(data.len()==393216,"complete terminal digest width")?;vc_sha(&data)
}
fn vc_uint_object(names:&str)->serde_json::Value{
    let mut map=serde_json::Map::new();for name in names.split_whitespace(){map.insert(name.into(),serde_json::json!(0u64));}
    serde_json::Value::Object(map)
}
fn vc_hex_vec(values:&[Fr])->Result<Vec<String>,String>{values.iter().map(u0_hex_fr).collect()}
fn vc_eval(coefficients:&[Fr],q:Fr)->Fr{
    coefficients.iter().rev().fold(Fr::zero(),|a,c|a*q+c)
}
fn vc_terminal_guard(actual:[Fr;3],expected:[Fr;3])->Result<(),String>{
    whole_require(actual==expected,"complete canonical terminal triplet mismatch")
}
fn vc_line_guard(actual:&[Fr],expected:&[Fr])->Result<(),String>{
    whole_require(actual.len()==expected.len() && actual==expected,"complete line coefficient mismatch")
}
fn vc_line_inputs(owner:usize,candidate_owner:usize,oracle_owner:usize,candidate:&[Fr],oracle:&[Fr],
    u:&[Fr],v:&[Fr],ou:&[Fr],ov:&[Fr])->Result<(),String>{
    whole_require(owner==candidate_owner && owner==oracle_owner,"complete line decoder owner mismatch")?;
    whole_require(!candidate.is_empty() && candidate.len().is_power_of_two() && candidate.len()==oracle.len()
        && u.len()==candidate.len().trailing_zeros() as usize && v.len()==u.len()
        && ou.len()==u.len() && ov.len()==v.len(),"complete line input geometry")?;
    whole_require(u==ou && v==ov,"complete line local point mismatch")?;
    whole_require(candidate==oracle,"complete line decoded Fr mismatch")
}
fn vc_reference_contribution(owner:usize,local:&[Fr],u:&[Fr],v:&[Fr])->Result<Vec<Fr>,String>{
    whole_require(owner<4096 && local.len()==21 && u.len()==12 && v.len()==12,"complete reference line geometry")?;
    let mut selector=vec![Fr::one()];
    for bit in 0..12{
        let (constant,slope)=if owner&(1<<bit)==0{(Fr::one()-u[bit],u[bit]-v[bit])}else{(u[bit],v[bit]-u[bit])};
        let mut next=vec![Fr::zero();selector.len()+1];
        for degree in 0..selector.len(){next[degree]+=selector[degree]*constant;next[degree+1]+=selector[degree]*slope;}
        selector=next;
    }
    let mut result=vec![Fr::zero();33];
    for i in 0..21{for j in 0..13{result[i+j]+=local[i]*selector[j];}}Ok(result)
}
fn vc_metric_add(total:&mut crate::sparse_stream_roster::EdgeGroupedVMetricsForTest,
    value:&crate::sparse_stream_roster::EdgeGroupedVMetricsForTest)->Result<(),String>{
    macro_rules! add {($a:expr,$b:expr)=>{$a=$a.checked_add($b).ok_or("complete metric overflow")?};}
    add!(total.physical_visits,value.physical_visits);add!(total.inactive_occurrences,value.inactive_occurrences);
    add!(total.logical_occurrences,value.logical_occurrences);add!(total.family_contributions,value.family_contributions);
    add!(total.nonzero_injections,value.nonzero_injections);
    let a=&mut total.fallback;let b=&value.fallback;
    add!(a.visits,b.visits);add!(a.cache_gets,b.cache_gets);add!(a.vector_clones,b.vector_clones);
    add!(a.replay_folds,b.replay_folds);add!(a.x_fold_fields,b.x_fold_fields);add!(a.bank_fold_entries,b.bank_fold_entries);
    add!(a.fold_ns,b.fold_ns);a.bank_capacity_peak_bytes=a.bank_capacity_peak_bytes.max(b.bank_capacity_peak_bytes);
    a.cache_capacity_peak_bytes=a.cache_capacity_peak_bytes.max(b.cache_capacity_peak_bytes);a.dense|=b.dense;Ok(())
}
fn vc_metric_json(m:&crate::sparse_stream_roster::EdgeGroupedVMetricsForTest,loads:u64,calls:u64,bytes:u64)->serde_json::Value{
    let f=&m.fallback;let mut result=vc_uint_object(VC_TERMINAL_KEYS);
    for (k,v) in [("semantic_owner_calls",4096),("real_x_owners",f.vector_clones),
        ("physical_term_visits",m.physical_visits),("represented_inactive_terms",m.inactive_occurrences),
        ("logical_term_count",m.logical_occurrences),("family_contributions",m.family_contributions),
        ("nonzero_injections",m.nonzero_injections),("physical_row_loads",loads),("cache_gets",f.cache_gets),
        ("vector_clones",f.vector_clones),("io_read_calls",calls),("io_read_bytes",bytes),
        ("replay_folds",f.replay_folds),("x_fold_fields",f.x_fold_fields),("bank_fold_entries",f.bank_fold_entries),("fold_ns",f.fold_ns)]{
        result[k]=serde_json::json!(v);
    }result
}
fn vc_census_guard(m:&crate::sparse_stream_roster::EdgeGroupedVMetricsForTest)->Result<(),String>{
    whole_require(m.physical_visits==3125994 && m.inactive_occurrences==335454208
        && m.logical_occurrences==338580202 && m.family_contributions==4095 && m.nonzero_injections<=4095
        && m.fallback.visits==m.physical_visits,"complete physical/represented census")
}

struct VcProgress{stage:&'static str,round:Option<usize>,completed:usize,active:bool,events:usize}
fn vc_progress_json(p:&VcProgress)->serde_json::Value{
    serde_json::json!({"stage":p.stage,"round":p.round,"completed":p.completed})
}
fn vc_emit(progress:&std::cell::RefCell<VcProgress>,edge:&str,completed:usize,start:std::time::Instant)->Result<(),String>{
    use std::io::Write;
    let mut p=progress.borrow_mut();p.completed=completed;
    let value=serde_json::json!({"stage":p.stage,"edge":edge,"round":p.round,"completed":completed,"elapsed_ns":screen_ns(start)});
    let line=format!("NATIVE_V_COMPLETE_EVENT {value}\n");
    whole_require(p.events<169 && line.len()<=224,"complete source event budget")?;p.events+=1;
    if edge=="end" || edge=="hold"{p.active=false;}
    let mut stdout=std::io::stdout().lock();stdout.write_all(line.as_bytes()).map_err(|e|e.to_string())?;
    stdout.flush().map_err(|e|e.to_string())
}
fn vc_begin(progress:&std::cell::RefCell<VcProgress>,stage:&'static str,round:Option<usize>,start:std::time::Instant)->Result<(),String>{
    {let mut p=progress.borrow_mut();p.stage=stage;p.round=round;p.completed=0;p.active=true;}
    vc_emit(progress,"begin",0,start)
}
fn vc_pending(output:&std::path::Path,progress:&std::cell::RefCell<VcProgress>)->Result<(),String>{
    let p=output.join("v-complete.part");useq_save(&p,&vc_progress_json(&progress.borrow()),65536,!p.exists())
}
fn vc_hold_part(path:&std::path::Path,progress:&std::cell::RefCell<VcProgress>)->Result<(),String>{
    match std::fs::symlink_metadata(path){
        Ok(_)=>Ok(()),
        Err(error) if error.kind()==std::io::ErrorKind::NotFound=>
            useq_save(path,&vc_progress_json(&progress.borrow()),65536,true),
        Err(error)=>Err(error.to_string()),
    }
}
fn vc_owner_progress(output:&std::path::Path,progress:&std::cell::RefCell<VcProgress>,owner:usize,start:std::time::Instant)->Result<(),String>{
    progress.borrow_mut().completed=owner;
    if owner%1024==0{vc_emit(progress,"progress",owner,start)?;vc_pending(output,progress)?;}Ok(())
}
fn vc_bind(t:&mut crate::transcript::Transcript,parent:&WorkTreeHistoryPlan,height:&HeightWork<'_>,daa:&DaaHistoryRoster<'_>,
    root:&[u8;32],total:&[u8;28],hashes:&[[u8;32];4],aliases:&[[[u8;32];2];2]){
    t.append_bytes(b"source-revision",U0_SOURCE.as_bytes());
    for (label,hash) in [b"native-fixture-sha256".as_slice(),b"native-fixture-blake2b256",b"witness-sha256",b"witness-blake2b256"].into_iter().zip(hashes){t.append_bytes(label,hash);}
    t.append_bytes(b"parent-root",root);t.append_bytes(b"parent-total-work-be28",total);
    for (label,value) in [(b"headers".as_slice(),3073),(b"slot-log".as_slice(),12),(b"input-log".as_slice(),32),
        (b"row-log".as_slice(),32),(b"role-index".as_slice(),4),(b"local-input-log".as_slice(),20),
        (b"base-row-log".as_slice(),19),(b"family-log".as_slice(),1),(b"height-member-row-log".as_slice(),19),
        (b"daa-member-row-log".as_slice(),19)]{t.append_u64(label,value);}
    for (label,digest) in [b"m1-map".as_slice(),b"m1-descriptor",b"m2-map",b"m2-descriptor"].into_iter().zip(aliases.iter().flat_map(|x|x.iter())){t.append_bytes(label,digest);}
    parent.bind(t);height.bind(t);daa.bind(t);
}
fn vc_compare_trace(poly:[Fr;3],q:Fr,claim:Fr,t:&crate::transcript::Transcript,
    expected_poly:[Fr;3],expected_q:Fr,expected_claim:Fr,reference:&crate::transcript::Transcript)->Result<(),String>{
    whole_require(poly==expected_poly && q==expected_q && claim==expected_claim
        && u0_counters(t)==u0_counters(reference)
        && t.clone().challenge_scalar(JH_CONTINUATION)==reference.clone().challenge_scalar(JH_CONTINUATION),
        "complete independent sender sequence mismatch")
}

fn vc_execute(output:&std::path::Path,start:std::time::Instant,progress:&std::cell::RefCell<VcProgress>)->Result<serde_json::Value,String>{
    use crate::{sparse_stream_roster as s,transcript::Transcript};
    use blake2::{Blake2b,Digest,digest::consts::U32};
    use ark_serialize::CanonicalSerialize;
    let mut times=vc_uint_object(VC_TIME_KEYS);let mut capacities=vc_uint_object(VC_CAP_KEYS);
    capacities["fr_bytes"]=serde_json::json!(32);capacities["owner_record_size_bytes"]=serde_json::json!(104);
    capacities["candidate_ledgers_nominal_bytes"]=serde_json::json!(8519680);
    capacities["candidate_terminal_nominal_bytes"]=serde_json::json!(393216);
    capacities["canonical_channels_nominal_bytes"]=serde_json::json!(524288);
    capacities["line_primitive_peak_bytes"]=serde_json::Value::Null;
    capacities["line_primitive_peak_status"]=serde_json::json!("UNMEASURED");
    capacities["line_primitive_source_bound_bytes"]=serde_json::json!(67108864);

    vc_begin(progress,"prefix",None,start)?;let began=std::time::Instant::now();
    let (fixture,input_bytes)=v_read_input()?;let input_sha=vc_sha(&input_bytes)?;
    whole_require(input_sha=="4EFE157A2D04C2B95431D699AB20B38F6713321DDFC35D41640891A733329AD4","complete prefix identity")?;
    let (u,r,left,oracle_left,final_counters,final_continuation,final_claim,mut sender,mut reference_sender)=v_validate_prefix(&fixture)?;
    let native=input();let root=native.root();let total=native.total_be28();
    let parent=WorkTreeHistoryPlan::compile(3073,12,root,total)?;drop(native);
    let height=HeightWork::compile_history(&parent)?;let daa=DaaHistoryRoster::compile(&parent)?;
    let adapter=Role4EndpointAdapter::new(&height,&daa,Role4EndpointScope::WholeS12)?;let binding=adapter.binding();
    let aliases=whole_aliases(&daa)?;let numeric=crate::daa_work_actions::DaaWorkActions::new(&parent)?;
    let alias_bindings=binding.whole_alias_identities.ok_or("complete alias bindings")?;
    let hashes=[u0_digest(U0_FIXTURE_SHA)?,u0_digest(U0_FIXTURE_BLAKE)?,u0_digest(U0_WITNESS_SHA)?,u0_digest(U0_WITNESS_BLAKE)?];
    let mut fresh=Transcript::new(b"native-s12-role4-u-sequence-diagnostic-v1");
    vc_bind(&mut fresh,&parent,&height,&daa,&root,&total,&hashes,&alias_bindings);
    let oracle_r=crate::gkr::output_point(1usize<<32,&mut fresh);crate::gkr::append_usize(&mut fresh,b"gkr-layer-index",0);
    let mut oracle_u=fixture.local_rounds.iter().map(|x|v_fr(&x.challenge)).collect::<Result<Vec<_>,_>>()?;
    oracle_u.extend(fixture.high_rounds.iter().map(|x|v_fr(&x.oracle_challenge)).collect::<Result<Vec<_>,_>>()?);
    whole_require(oracle_r==r && oracle_u==u && left==oracle_left,"complete independent frame points/scalar")?;
    let (source,held,identity)=useq_admit()?;
    times["prefix_replay"]=serde_json::json!(screen_ns(began));vc_emit(progress,"end",1,start)?;

    vc_begin(progress,"census",None,start)?;let began=std::time::Instant::now();
    let counts=s::edge_v_census_for_test(20,12,19,1,&[19,19],
        |side,owner,sink|adapter.visit_endpoint(&binding,side,owner,|term|sink(term)).map(|_|()),
        |owners,_|vc_owner_progress(output,progress,owners,start))?;
    whole_require(counts.len()==4096 && v_sum_usize_counts(&counts)?==338580202,"complete RIGHT census")?;
    times["census"]=serde_json::json!(screen_ns(began));vc_emit(progress,"end",4096,start)?;
    vc_begin(progress,"family-summary",None,start)?;let began=std::time::Instant::now();
    let ctx=s::EdgeGroupedVContextForTest::new(&adapter,&r,&u,left)?;
    whole_require(ctx.template_visits()==155648,"complete family template census")?;
    capacities["candidate_weights_capacity_bytes"]=serde_json::json!(ctx.capacity_bytes());
    times["family_summary"]=serde_json::json!(screen_ns(began));vc_emit(progress,"end",1,start)?;

    let loads=std::cell::Cell::new(0u64);
    let mut candidate=s::EdgeGroupedVCandidateForTest::new(|owner|{
        whole_require(owner<4096,"complete candidate X owner")?;
        loads.set(loads.get().checked_add(1).ok_or("complete candidate load overflow")?);
        crate::packed_rows::read_row(&source,1<<20,owner)
    },1<<20,4096)?;
    let mut ledgers=Vec::with_capacity(20);let mut polys=Vec::with_capacity(20);let mut qs=Vec::with_capacity(20);
    let mut traces=Vec::with_capacity(20);let mut local_rows=Vec::with_capacity(20);let mut claim=final_claim;
    let mut bank_peak=0usize;let mut cache_peak=0usize;let local_start=std::time::Instant::now();
    for round in 0..20{
        vc_begin(progress,"local-v",Some(round),start)?;let began=std::time::Instant::now();
        let observed_prefix=traces.iter().map(|trace:&(Fr,Fr,Fr,[u64;3],String)|trace.0).collect::<Vec<_>>();
        vc_bound_guard(&r,&u,left,&qs,&oracle_r,&oracle_u,oracle_left,&observed_prefix)?;
        let before=source.io_metrics_snapshot();let load_before=loads.get();
        let mut ledger=Vec::with_capacity(4096);let mut aggregate=[Fr::zero();3];
        let mut metrics=s::EdgeGroupedVMetricsForTest::default();let mut zeros=0u64;let mut real=0u64;
        for owner in 0..4096{
            let result=candidate.local_owner_deferred(&ctx,owner,counts[owner],&qs)?;
            if result.x_observation.is_none(){
                whole_require(result.metrics.fallback.cache_gets==0 && result.metrics.fallback.vector_clones==0
                    && result.metrics.fallback.x_fold_fields==0,"complete deferred X observation/counters")?;zeros+=1;
            }else{real+=1;}
            vc_metric_add(&mut metrics,&result.metrics)?;
            ledger.push(VOwnerRecord{count:counts[owner],polynomial:result.message});
            for i in 0..3{aggregate[i]+=result.message[i];}
            vc_owner_progress(output,progress,owner+1,start)?;
        }
        let after=source.io_metrics_snapshot();let mut measured=vc_metric_json(&metrics,loads.get()-load_before,
            after.read_calls-before.read_calls,after.read_bytes-before.read_bytes);
        measured.as_object_mut().ok_or("complete local metrics")?.remove("real_x_owners");
        measured["zero_a_owners"]=serde_json::json!(zeros);measured["nonzero_a_owners"]=serde_json::json!(real);
        measured["duration_ns"]=serde_json::json!(screen_ns(began));local_rows.push(measured);
        vc_census_guard(&metrics)?;
        whole_require(zeros==4094 && real==2 && metrics.fallback.cache_gets==2 && metrics.fallback.vector_clones==2
            && metrics.fallback.replay_folds==4096*round as u64,"complete exact-A branches/folds")?;
        let digest=v_owner_digest(&ledger)?;
        if round<2{let (expected,_,_,_,_,expected_digest)=vg_reference(round)?;
            whole_require(aggregate==expected && digest==expected_digest,"complete first-two retained grouped comparison")?;}
        let (q,next)=s::edge_u_sequence_send_for_test(aggregate,claim,&mut sender)?;claim=next;
        let continuation=sender.clone().challenge_scalar(JH_CONTINUATION);
        traces.push((q,claim,continuation,u0_counters(&sender),digest));qs.push(q);polys.push(aggregate);ledgers.push(ledger);
        bank_peak=bank_peak.max(metrics.fallback.bank_capacity_peak_bytes);cache_peak=cache_peak.max(metrics.fallback.cache_capacity_peak_bytes);
        vc_emit(progress,"end",4096,start)?;
    }
    times["local_candidate"]=serde_json::json!(screen_ns(local_start));
    capacities["candidate_ledgers_capacity_bytes"]=serde_json::json!(ledgers.capacity()*std::mem::size_of::<Vec<VOwnerRecord>>()
        +ledgers.iter().map(|x|x.capacity()*std::mem::size_of::<VOwnerRecord>()).sum::<usize>());

    vc_begin(progress,"terminal",None,start)?;let began=std::time::Instant::now();
    let observed_prefix=traces.iter().map(|trace|trace.0).collect::<Vec<_>>();
    vc_bound_guard(&r,&u,left,&qs,&oracle_r,&oracle_u,oracle_left,&observed_prefix)?;
    let before=source.io_metrics_snapshot();let load_before=loads.get();let mut terminals=Vec::with_capacity(4096);
    let mut terminal_metrics=s::EdgeGroupedVMetricsForTest::default();
    for owner in 0..4096{
        let result=candidate.terminal_owner(&ctx,owner,counts[owner],&qs)?;
        whole_require(result.message.is_empty(),"complete terminal returned local message")?;
        terminals.push([result.terminal.0,result.terminal.1,result.folded_x]);vc_metric_add(&mut terminal_metrics,&result.metrics)?;
        vc_owner_progress(output,progress,owner+1,start)?;
    }
    let after=source.io_metrics_snapshot();let terminal_json=vc_metric_json(&terminal_metrics,loads.get()-load_before,
        after.read_calls-before.read_calls,after.read_bytes-before.read_bytes);
    vc_census_guard(&terminal_metrics)?;whole_require(terminal_metrics.fallback.vector_clones==4096
        && terminal_metrics.fallback.cache_gets==4096 && terminal_metrics.fallback.replay_folds==4096*20,"complete mandatory terminal X")?;
    bank_peak=bank_peak.max(terminal_metrics.fallback.bank_capacity_peak_bytes);cache_peak=cache_peak.max(terminal_metrics.fallback.cache_capacity_peak_bytes);
    capacities["candidate_bank_peak_bytes"]=serde_json::json!(bank_peak);capacities["candidate_cache_peak_bytes"]=serde_json::json!(cache_peak);
    capacities["candidate_terminal_capacity_bytes"]=serde_json::json!(terminals.capacity()*std::mem::size_of::<[Fr;3]>());
    let candidate_terminal_sha=vc_triplet_sha(&terminals)?;
    times["terminal_candidate"]=serde_json::json!(screen_ns(began));vc_emit(progress,"end",4096,start)?;
    drop(candidate);

    vc_begin(progress,"canonical-oracle",None,start)?;let began=std::time::Instant::now();
    let rows=U0OracleWeights::new(&oracle_r)?;let uweights=U0OracleWeights::new(&oracle_u)?;
    let mut padded=qs.clone();padded.resize(32,Fr::zero());let vweights=U0OracleWeights::new(&padded)?;
    capacities["oracle_weights_capacity_bytes"]=serde_json::json!(rows.capacity_bytes()+uweights.capacity_bytes()+vweights.capacity_bytes());
    let mut oracle_hashes=(0..20).map(|_|Blake2b::<U32>::new()).collect::<Vec<_>>();
    let mut oracle_polys=vec![[Fr::zero();3];20];let mut oracle_terminals=Vec::with_capacity(4096);
    let mut channels=Vec::with_capacity(4096);let mut canonical_terms=0u64;let mut x_folds=0u64;let mut bank_folds=0u64;
    let mut oracle_bank_peak=0usize;let mut nonzero_sources=[false;2];let before=source.io_metrics_snapshot();
    for owner in 0..4096{
        let width=1usize<<20;let mut a=vec![Fr::zero();width];let mut b=vec![Fr::zero();width];
        let mut x=useq_legacy_row(&source,owner)?;let mut count=0usize;let mut owner_channels=[Fr::zero();4];
        oracle_bank_peak=oracle_bank_peak.max((a.capacity()+b.capacity()+x.capacity())*32);
        whole_oracle_partition(&height,&daa,&numeric,&aliases,false,owner,|term|{
            whole_require(term.right/width==owner,"complete canonical RIGHT association")?;
            if !term.c[2].is_zero() || !term.c[3].is_zero(){
                whole_require(matches!(owner,2048|3072),"complete canonical nonzero-A source owner")?;
                nonzero_sources[if owner==2048{0}else{1}]=true;
            }
            let weight=rows.at(term.row)?*uweights.at(term.left)?;let wire=term.right%width;
            a[wire]+=weight*(term.c[2]+term.c[3]*oracle_left);b[wire]+=weight*(term.c[0]+term.c[1]*oracle_left);
            let projected=weight*vweights.at(wire)?;
            for i in 0..4{owner_channels[i]+=projected*term.c[i];}
            count=count.checked_add(1).ok_or("complete canonical count overflow")?;Ok(())
        })?;
        whole_require(count==counts[owner],"complete canonical owner census mismatch")?;
        canonical_terms=canonical_terms.checked_add(count as u64).ok_or("complete canonical total overflow")?;
        for round in 0..20{
            let poly=useq_message(&a,&b,&x);let candidate_record=ledgers[round][owner];
            v_owner_compare(count,poly,candidate_record.count,candidate_record.polynomial)?;
            for i in 0..3{oracle_polys[round][i]+=poly[i];}
            oracle_hashes[round].update((owner as u64).to_le_bytes());oracle_hashes[round].update((count as u64).to_le_bytes());
            for coefficient in poly{let mut bytes=Vec::with_capacity(32);coefficient.serialize_compressed(&mut bytes).map_err(|e|e.to_string())?;oracle_hashes[round].update(bytes);}
            x_folds+=x.len() as u64;bank_folds+=(a.len()+b.len()) as u64;
            useq_fold(&mut a,qs[round]);useq_fold(&mut b,qs[round]);useq_fold(&mut x,qs[round]);
        }
        let terminal=[a[0],b[0],x[0]];vc_terminal_guard(terminals[owner],terminal)?;
        whole_require(owner_channels[2]+owner_channels[3]*oracle_left==a[0]
            && owner_channels[0]+owner_channels[1]*oracle_left==b[0],"complete four-channel local combination")?;
        channels.push(owner_channels);oracle_terminals.push(terminal);
        vc_owner_progress(output,progress,owner+1,start)?;
    }
    let after=source.io_metrics_snapshot();whole_require(canonical_terms==338580202 && nonzero_sources==[true,true],"complete canonical structural census")?;
    let oracle_terminal_sha=vc_triplet_sha(&oracle_terminals)?;whole_require(oracle_terminal_sha==candidate_terminal_sha,"complete terminal SHA mismatch")?;
    let mut oracle_metrics=vc_uint_object(VC_ORACLE_KEYS);
    for (key,value) in [("owner_bank_builds",4096),("canonical_term_visits",canonical_terms),("canonical_count",canonical_terms),
        ("row_decodes",4096),("physical_row_loads",4096),("io_read_calls",after.read_calls-before.read_calls),
        ("io_read_bytes",after.read_bytes-before.read_bytes),("owner_round_comparisons",81920),("owner_terminal_comparisons",4096),
        ("x_fold_fields",x_folds),("bank_fold_entries",bank_folds),("channel_owner_count",4096),("channel_field_count",16384)]{oracle_metrics[key]=serde_json::json!(value);}
    capacities["oracle_bank_peak_bytes"]=serde_json::json!(oracle_bank_peak);
    capacities["oracle_terminal_capacity_bytes"]=serde_json::json!(oracle_terminals.capacity()*96);
    capacities["canonical_channels_capacity_bytes"]=serde_json::json!(channels.capacity()*128);
    times["canonical_oracle"]=serde_json::json!(screen_ns(began));vc_emit(progress,"end",4096,start)?;

    vc_begin(progress,"oracle-replay",None,start)?;let began=std::time::Instant::now();let mut reference_claim=final_claim;
    let mut local_trace=Vec::with_capacity(20);let mut reference_qs=Vec::with_capacity(20);
    for (round,hash) in oracle_hashes.into_iter().enumerate(){
        let digest=screen_hex(&hash.finalize());whole_require(digest==traces[round].4,"complete canonical owner digest")?;
        let (q,next)=useq_reference_send(oracle_polys[round],reference_claim,&mut reference_sender)?;reference_claim=next;
        let continuation=reference_sender.clone().challenge_scalar(JH_CONTINUATION);let trace=&traces[round];
        whole_require(polys[round]==oracle_polys[round] && trace.0==q && trace.1==next && trace.2==continuation
            && trace.3==u0_counters(&reference_sender),"complete local independent sender mismatch")?;
        local_trace.push(serde_json::json!([u0_hex_fr(&q)?,u0_hex_fr(&next)?,u0_hex_fr(&continuation)?,trace.3,
            vc_fields_sha(&oracle_polys[round])?,trace.4,digest]));reference_qs.push(q);
    }
    whole_require(reference_qs==qs && reference_claim==claim && u0_counters(&sender)==u0_counters(&reference_sender)
        && sender.clone().challenge_scalar(JH_CONTINUATION)==reference_sender.clone().challenge_scalar(JH_CONTINUATION),"complete local live/reference closure")?;
    times["oracle_sender_replay"]=serde_json::json!(screen_ns(began));vc_emit(progress,"end",1,start)?;

    vc_begin(progress,"high-v",None,start)?;let began=std::time::Instant::now();
    let mut proof_rounds=fixture.local_rounds.iter().map(|x|v_poly(&x.polynomial).map(|x|x.to_vec())).collect::<Result<Vec<_>,_>>()?;
    proof_rounds.extend(fixture.high_rounds.iter().map(|x|v_poly(&x.candidate_polynomial).map(|x|x.to_vec())).collect::<Result<Vec<_>,_>>()?);
    proof_rounds.extend(polys.iter().map(|x|x.to_vec()));
    let pre_high=sender.clone();let pre_high_claim=claim;
    let (high_qs,right)=crate::gkr::prove_phase(terminals.iter().map(|x|x[0]).collect(),terminals.iter().map(|x|x[1]).collect(),
        &terminals.iter().map(|x|x[2]).collect::<Vec<_>>(),&mut claim,&mut proof_rounds,&mut sender).map_err(|e|e.to_string())?;
    whole_require(high_qs.len()==12 && proof_rounds.len()==64,"complete actual high-V shape")?;
    let mut ca=oracle_terminals.iter().map(|x|x[0]).collect::<Vec<_>>();let mut cb=oracle_terminals.iter().map(|x|x[1]).collect::<Vec<_>>();
    let mut cx=oracle_terminals.iter().map(|x|x[2]).collect::<Vec<_>>();let mut replay=pre_high;let mut replay_claim=pre_high_claim;
    let mut high_trace=Vec::with_capacity(12);let mut oracle_high=Vec::with_capacity(12);
    for round in 0..12{
        let canonical=useq_message(&ca,&cb,&cx);let actual:[Fr;3]=proof_rounds[52+round].as_slice().try_into().map_err(|_|"complete actual high polynomial")?;
        let (oq,on)=useq_reference_send(canonical,reference_claim,&mut reference_sender)?;reference_claim=on;
        let (rq,rn)=s::edge_u_sequence_send_for_test(actual,replay_claim,&mut replay)?;replay_claim=rn;
        vc_compare_trace(actual,rq,rn,&replay,canonical,oq,on,&reference_sender)?;
        whole_require(rq==high_qs[round],"complete actual high challenge replay")?;
        high_trace.push(serde_json::json!([u0_hex_fr(&oq)?,u0_hex_fr(&on)?,
            u0_hex_fr(&reference_sender.clone().challenge_scalar(JH_CONTINUATION))?,u0_counters(&reference_sender),vc_fields_sha(&canonical)?]));
        oracle_high.push(oq);useq_fold(&mut ca,oq);useq_fold(&mut cb,oq);useq_fold(&mut cx,oq);
        vc_emit(progress,"progress",round+1,start)?;
    }
    whole_require(high_qs==oracle_high && right==cx[0] && replay_claim==claim && reference_claim==claim
        && u0_counters(&sender)==u0_counters(&replay) && u0_counters(&sender)==u0_counters(&reference_sender)
        && sender.clone().challenge_scalar(JH_CONTINUATION)==replay.clone().challenge_scalar(JH_CONTINUATION)
        && sender.clone().challenge_scalar(JH_CONTINUATION)==reference_sender.clone().challenge_scalar(JH_CONTINUATION),"complete high live/reference terminal")?;
    let mut v=qs.clone();v.extend_from_slice(&high_qs);let mut oracle_v=reference_qs;oracle_v.extend_from_slice(&oracle_high);
    let terminal_claim=claim;times["high_v"]=serde_json::json!(screen_ns(began));vc_emit(progress,"end",12,start)?;

    vc_begin(progress,"line",None,start)?;let began=std::time::Instant::now();let mut line=vec![Fr::zero();33];let mut oracle_line=line.clone();
    let mut candidate_calls=0u64;let mut candidate_bytes=0u64;let mut oracle_calls=0u64;let mut oracle_bytes=0u64;
    let mut candidate_row_peak=0usize;let mut legacy_row_peak=0usize;let mut local_peak=0usize;
    for owner in 0..4096{
        let before=source.io_metrics_snapshot();let candidate_x=crate::packed_rows::read_row(&source,1<<20,owner)?;
        let middle=source.io_metrics_snapshot();let canonical_x=useq_legacy_row(&source,owner)?;let after=source.io_metrics_snapshot();
        candidate_calls+=middle.read_calls-before.read_calls;candidate_bytes+=middle.read_bytes-before.read_bytes;
        oracle_calls+=after.read_calls-middle.read_calls;oracle_bytes+=after.read_bytes-middle.read_bytes;
        candidate_row_peak=candidate_row_peak.max(candidate_x.capacity()*32);legacy_row_peak=legacy_row_peak.max(canonical_x.capacity()*32);
        vc_line_inputs(owner,owner,owner,&candidate_x,&canonical_x,&u[..20],&v[..20],&oracle_u[..20],&oracle_v[..20])?;
        drop(canonical_x);
        // Equality above permits one shared literal local primitive. Composition
        // below is independent; no second local-algorithm claim is made.
        let local=crate::gkr::line_polynomial(&candidate_x,&u[..20],&v[..20]);
        whole_require(local.len()==21,"complete local line extent")?;local_peak=local_peak.max(local.capacity()*32);
        let contribution=s::edge_line_owner_contribution_for_test(owner,&local,&u[20..],&v[20..])?;
        let canonical=vc_reference_contribution(owner,&local,&oracle_u[20..],&oracle_v[20..])?;
        vc_line_guard(&contribution,&canonical)?;
        for i in 0..33{line[i]+=contribution[i];oracle_line[i]+=canonical[i];}
        vc_owner_progress(output,progress,owner+1,start)?;
    }
    vc_line_guard(&line,&oracle_line)?;let endpoints=[line[0],vc_eval(&line,Fr::one())];
    let oracle_endpoints=[oracle_line[0],vc_eval(&oracle_line,Fr::one())];
    whole_require(endpoints==[left,right] && endpoints==oracle_endpoints,"complete independent line endpoints")?;
    sender.append_scalar(b"gkr-left-value",&left);sender.append_scalar(b"gkr-right-value",&right);
    crate::gkr::append_polynomial(&mut sender,b"gkr-line-polynomial",&line);
    reference_sender.append_scalar(b"gkr-left-value",&oracle_left);reference_sender.append_scalar(b"gkr-right-value",&cx[0]);
    reference_sender.append_bytes(b"gkr-line-polynomial",&33u64.to_le_bytes());
    for c in &oracle_line{reference_sender.append_scalar(b"gkr-polynomial-coefficient",c);}
    let line_q=sender.challenge_scalar(b"gkr-line-challenge");let oracle_line_q=reference_sender.challenge_scalar(b"gkr-line-challenge");
    let input_claim=crate::gkr::InputClaim{point:crate::gkr::line_point(&u,&v,line_q),value:crate::gkr::eval_polynomial(&line,line_q)};
    let oracle_claim=crate::gkr::InputClaim{point:oracle_u.iter().zip(&oracle_v).map(|(a,b)|*a+oracle_line_q*(*b-*a)).collect(),value:vc_eval(&oracle_line,oracle_line_q)};
    whole_require(line_q==oracle_line_q && input_claim==oracle_claim && u0_counters(&sender)==u0_counters(&reference_sender)
        && sender.clone().challenge_scalar(JH_CONTINUATION)==reference_sender.clone().challenge_scalar(JH_CONTINUATION),"complete line InputClaim/transcript mismatch")?;
    let mut line_metrics=vc_uint_object(VC_LINE_KEYS);
    for (key,value) in [("owners",4096),("candidate_row_decodes",4096),("oracle_row_decodes",4096),("fr_value_comparisons",4294967296),
        ("local_point_coordinate_comparisons",163840),("local_primitive_calls",4096),("global_coefficient_comparisons",33),("endpoint_comparisons",2),
        ("candidate_io_read_calls",candidate_calls),("candidate_io_read_bytes",candidate_bytes),("oracle_io_read_calls",oracle_calls),
        ("oracle_io_read_bytes",oracle_bytes),("local_primitive_pair_degree_cells_source_count",8589844480)]{line_metrics[key]=serde_json::json!(value);}
    for (key,value) in [("line_candidate_row_peak_bytes",candidate_row_peak),("line_legacy_row_peak_bytes",legacy_row_peak),
        ("line_local_coefficients_capacity_peak_bytes",local_peak),("line_global_candidate_capacity_bytes",line.capacity()*32),
        ("line_global_oracle_capacity_bytes",oracle_line.capacity()*32)]{capacities[key]=serde_json::json!(value);}
    times["line"]=serde_json::json!(screen_ns(began));vc_emit(progress,"end",4096,start)?;

    vc_begin(progress,"wiring",None,start)?;let began=std::time::Instant::now();let mut coefficients=[Fr::zero();4];
    for owner in 0..4096{let selector=u0_direct_weight(&oracle_v[20..],owner);
        for i in 0..4{coefficients[i]+=channels[owner][i]*selector;}}
    whole_require(coefficients[0]+coefficients[1]*left+coefficients[2]*right+coefficients[3]*left*right==terminal_claim,
        "complete canonical wiring terminal relation")?;
    times["wiring"]=serde_json::json!(screen_ns(began));vc_emit(progress,"end",1,start)?;

    vc_begin(progress,"proof",None,start)?;let began=std::time::Instant::now();
    let proof=crate::gkr::GkrProof{layers:vec![crate::gkr::LayerProof{rounds:proof_rounds,left_value:left,right_value:right,line_coefficients:line.clone()}]};
    let encoded=crate::gkr::encode_proof(&proof)?;whole_require(encoded.len()==7264,"complete codec proof extent")?;
    let decoded=crate::gkr::decode_dimensions(&[32],&encoded)?;
    whole_require(crate::gkr::encode_proof(&decoded)?==encoded,"complete canonical codec roundtrip")?;
    capacities["proof_capacity_bytes"]=serde_json::json!(encoded.capacity());times["codec"]=serde_json::json!(screen_ns(began));
    let began=std::time::Instant::now();let requested=std::cell::Cell::new(false);
    let mut verifier=Transcript::new(b"native-s12-role4-u-sequence-diagnostic-v1");
    let verified=crate::gkr::verify_with_wiring(&[32],1usize<<32,&decoded,&mut verifier,
        |t|vc_bind(t,&parent,&height,&daa,&root,&total,&hashes,&alias_bindings),
        |layer,rr,uu,vv|{
            vc_requested_guard(layer,rr,uu,vv,&oracle_r,&oracle_u,&oracle_v)?;
            requested.set(true);Ok(coefficients)
        }).map_err(|e|e.to_string())?;
    whole_require(requested.get() && verified==input_claim && u0_counters(&verifier)==u0_counters(&sender)
        && verifier.clone().challenge_scalar(JH_CONTINUATION)==sender.clone().challenge_scalar(JH_CONTINUATION),"complete fresh verifier closure")?;
    times["verify"]=serde_json::json!(screen_ns(began));
    use std::io::Write;
    let mut proof_file=OpenOptions::new().write(true).create_new(true).open(output.join("proof.bin")).map_err(|e|e.to_string())?;
    proof_file.write_all(&encoded).map_err(|e|e.to_string())?;proof_file.sync_all().map_err(|e|e.to_string())?;drop(proof_file);
    whole_require(u0_file_info(&held)?==identity,"complete final held witness identity")?;
    let proof_sha=vc_sha(&encoded)?;vc_emit(progress,"end",1,start)?;

    let mut columns=serde_json::Map::new();
    for key in VC_LOCAL_KEYS.split_whitespace(){columns.insert(key.into(),serde_json::Value::Array(local_rows.iter().map(|row|row[key].clone()).collect()));}
    let mut claim_fields=input_claim.point.clone();claim_fields.push(input_claim.value);
    let mut report=serde_json::json!({"schema":"native-s12-v-complete-result-v1","version":1,"state":"V_COMPLETE_COMPONENT_PASS",
        "input_sha256":input_sha,"reference_sha256":VC_REFERENCE,"prefix":{
            "local_round_matches":20,"local_oracle_matches":20,"high_round_matches":12,"high_u_matches":12,
            "initial_counters":fixture.initial_counters,"final_counters":final_counters,"final_continuation":final_continuation,"left_value_equal":left==oracle_left},
        "local":{"trace":local_trace,"oracle_owner_comparisons":81920,"oracle_terminal_comparisons":4096,"oracle_sequence_equal":true},
        "terminal":{"owners":4096,"candidate_triplets_sha256":candidate_terminal_sha,"oracle_triplets_sha256":oracle_terminal_sha,"comparisons":4096,"checked":true},
        "high":{"trace":high_trace,"final_right_value":u0_hex_fr(&right)?,"sequence_equal":true}});
    report["wiring"]=serde_json::json!({"coefficients":vc_hex_vec(&coefficients)?,"claim":u0_hex_fr(&terminal_claim)?,
        "canonical_term_count":canonical_terms,"channel_owners":4096,"channel_combination_equal":true,"requested_point_equal":requested.get(),
        "r_sha256":vc_fields_sha(&oracle_r)?,"u_sha256":vc_fields_sha(&oracle_u)?,"v_sha256":vc_fields_sha(&oracle_v)?});
    report["line"]=serde_json::json!({"coefficients":vc_hex_vec(&line)?,"oracle_coefficients_sha256":vc_fields_sha(&oracle_line)?,
        "endpoint_values":vc_hex_vec(&endpoints)?,"oracle_endpoint_values":vc_hex_vec(&oracle_endpoints)?,"challenge":u0_hex_fr(&line_q)?,
        "transcript_counters":u0_counters(&sender),"continuation":u0_hex_fr(&sender.clone().challenge_scalar(JH_CONTINUATION))?,
        "coefficients_equal":true,"endpoints_equal":true});
    report["input_claim"]=serde_json::json!({"point":vc_hex_vec(&input_claim.point)?,"value":u0_hex_fr(&input_claim.value)?});
    report["proof"]=serde_json::json!({"bytes":encoded.len(),"scalar_count":227,"sha256":proof_sha,"codec_roundtrip":true});
    report["verification"]=serde_json::json!({"dimensions":[32],"output_width":4294967296u64,"input_claim_sha256":vc_fields_sha(&claim_fields)?,
        "transcript_counters":u0_counters(&verifier),"continuation":u0_hex_fr(&verifier.clone().challenge_scalar(JH_CONTINUATION))?,
        "claim_equal":true,"transcript_equal":true,"requested_point_equal":requested.get()});
    report["metrics"]=serde_json::json!({"local":columns,"terminal":terminal_json,"oracle":oracle_metrics,"line":line_metrics});
    report["capacities"]=capacities;times["total"]=serde_json::json!(screen_ns(start));report["timings_ns"]=times;
    let bytes=serde_json::to_vec(&report).map_err(|e|e.to_string())?;whole_require(bytes.len()<=65536,"complete final result cap")?;
    let part=output.join("v-complete.part");useq_save(&part,&report,65536,!part.exists())?;
    useq_finalize_checkpoint(&part,&output.join("v-complete.json"))?;Ok(report)
}

fn vc_requested_guard(layer:usize,r:&[Fr],u:&[Fr],v:&[Fr],er:&[Fr],eu:&[Fr],ev:&[Fr])->Result<(),crate::gkr::GkrError>{
    if layer!=0 || r.len()!=32 || u.len()!=32 || v.len()!=32 || r!=er || u!=eu || v!=ev{
        return Err(crate::gkr::GkrError::PointDimension);
    }Ok(())
}
fn vc_bound_guard(r:&[Fr],u:&[Fr],left:Fr,prefix:&[Fr],er:&[Fr],eu:&[Fr],el:Fr,ep:&[Fr])->Result<(),String>{
    whole_require(r==er && u==eu && left==el && prefix==ep,"complete context point/scalar/prefix mismatch")
}
fn vc_wrapper_controls()->Result<(),String>{
    use crate::sparse_stream_roster as s;
    s::edge_grouped_v_deferred_controls_for_test()?;
    let parent=WorkTreeHistoryPlan::compile(3073,12,[0;32],[0;28])?;
    let height=HeightWork::compile_history(&parent)?;let daa=DaaHistoryRoster::compile(&parent)?;
    let adapter=Role4EndpointAdapter::new(&height,&daa,Role4EndpointScope::WholeS12)?;let binding=adapter.binding();
    let r=general(32,7);let u=general(32,113);let qs=general(20,59);let width=1usize<<20;
    for left in [Fr::zero(),Fr::from(37u64)]{
        let ctx=s::EdgeGroupedVContextForTest::new(&adapter,&r,&u,left)?;
        let weights=s::EdgeFallbackWeightsForTest::new(&r,&u,20);let loads=std::cell::Cell::new(0usize);
        let mut candidate=s::EdgeGroupedVCandidateForTest::new(|owner|{
            loads.set(loads.get()+1);Ok(vec![Fr::from((owner+1) as u64);width])
        },width,4096)?;
        for owner in [0usize,2048,3072]{
            let count=adapter.visit_endpoint(&binding,false,owner,|_|Ok(()))?;
            for k in [0usize,1,19]{
                vc_bound_guard(&r,&u,left,&qs[..k],&r,&u,left,&qs[..k])?;
                let before=loads.get();let actual=candidate.local_owner_deferred(&ctx,owner,count,&qs[..k])?;
                let expected=s::edge_fallback_prefix_for_test(false,owner,20,12,19,1,&[19,19],count,&weights,left,&qs[..k],
                    |side,slot,sink|adapter.visit_endpoint(&binding,side,slot,|term|sink(term)).map(|_|()),
                    |slot|Ok(vec![Fr::from((slot+1) as u64);width]),None)?;
                whole_require(actual.message.as_slice()==expected.message.as_slice(),"complete actual deferred/fallback polynomial")?;
                if owner==0{
                    whole_require(actual.x_observation.is_none() && loads.get()==before
                        && actual.metrics.fallback.cache_gets==0 && actual.metrics.fallback.vector_clones==0
                        && actual.metrics.fallback.x_fold_fields==0,"complete native deferred wrapper loaded X")?;
                }
            }
            let actual=candidate.terminal_owner(&ctx,owner,count,&qs)?;
            let expected=s::edge_fallback_prefix_for_test(false,owner,20,12,19,1,&[19,19],count,&weights,left,&qs,
                |side,slot,sink|adapter.visit_endpoint(&binding,side,slot,|term|sink(term)).map(|_|()),
                |slot|Ok(vec![Fr::from((slot+1) as u64);width]),None)?;
            vc_terminal_guard([actual.terminal.0,actual.terminal.1,actual.folded_x],
                [expected.terminal.0,expected.terminal.1,expected.folded_x])?;
            whole_require(actual.metrics.fallback.cache_gets==1 && actual.metrics.fallback.vector_clones==1
                && actual.folded_x==Fr::from((owner+1) as u64),"complete mandatory native terminal X")?;
            let before=loads.get();
            whole_require(candidate.local_owner_deferred(&ctx,owner,count,&qs).is_err()
                && candidate.terminal_owner(&ctx,owner,count,&qs[..19]).is_err()
                && candidate.local_owner_deferred(&ctx,owner,count+1,&[]).is_err()
                && loads.get()==before,"complete isolated prefix/count loader guard")?;
        }
        whole_require(candidate.local_owner_deferred(&ctx,4096,81920,&[]).is_err(),"complete owner bound guard")?;
    }
    let mut bad_r=r.clone();bad_r[0]+=Fr::one();let mut bad_u=u.clone();bad_u[31]+=Fr::one();
    let prefix=&qs[..1];let mut bad_prefix=prefix.to_vec();bad_prefix[0]+=Fr::one();
    for result in [vc_bound_guard(&bad_r,&u,Fr::one(),prefix,&r,&u,Fr::one(),prefix),
        vc_bound_guard(&r,&bad_u,Fr::one(),prefix,&r,&u,Fr::one(),prefix),
        vc_bound_guard(&r,&u,Fr::from(2u64),prefix,&r,&u,Fr::one(),prefix),
        vc_bound_guard(&r,&u,Fr::one(),&bad_prefix,&r,&u,Fr::one(),prefix)]{
        whole_require(result.err().as_deref()==Some("complete context point/scalar/prefix mismatch"),"complete isolated context predicate")?;
    }Ok(())
}
fn vc_toy_banks(owner:usize,terms:&[Term],input:&[Fr],r:&[Fr],u:&[Fr])->(Vec<Fr>,Vec<Fr>,Vec<Fr>){
    let mut a=vec![Fr::zero();4];let mut b=a.clone();
    for term in terms.iter().filter(|t|t.gate.right/4==owner){
        let w=u0_direct_weight(r,term.row)*u0_direct_weight(u,term.gate.left);let wire=term.gate.right%4;
        a[wire]+=w*term.gate.c2;b[wire]+=w*term.gate.c0;
    }(a,b,input[owner*4..owner*4+4].to_vec())
}
fn vc_sequence_controls()->Result<(),String>{
    use crate::{gkr::Gate,sparse_stream_roster as s,transcript::Transcript};
    let input=(0..8).map(|i|Fr::from((2*i+3) as u64)).collect::<Vec<_>>();let r=general(3,11);let u=general(3,41);
    let terms=(0..8).map(|i|{let c=Fr::from((i+2) as u64);
        Term{row:i,gate:Gate{left:(i+3)%8,right:i,c0:-c*input[i],c1:Fr::zero(),c2:c,c3:Fr::zero()}}}).collect::<Vec<_>>();
    let mut candidate=(0..2).map(|owner|vc_toy_banks(owner,&terms,&input,&r,&u)).collect::<Vec<_>>();
    let mut sender=Transcript::new(b"complete-owner-major-control-v1");let initial=sender.clone();let mut claim=Fr::zero();
    let mut ledgers=Vec::new();let mut polys=Vec::new();let mut qs=Vec::new();let mut traces=Vec::new();
    for _round in 0..2{
        let mut ledger=Vec::new();let mut aggregate=[Fr::zero();3];
        for (a,b,x) in &candidate{let poly=crate::gkr::quadratic_message(a,b,x);
            let poly:[Fr;3]=poly.as_slice().try_into().map_err(|_|"complete toy message")?;
            for i in 0..3{aggregate[i]+=poly[i];}ledger.push(poly);}
        let (q,next)=s::edge_u_sequence_send_for_test(aggregate,claim,&mut sender)?;claim=next;
        traces.push((q,next,u0_counters(&sender),sender.clone().challenge_scalar(JH_CONTINUATION)));
        for (a,b,x) in &mut candidate{crate::gkr::fold(a,q);crate::gkr::fold(b,q);crate::gkr::fold(x,q);}
        ledgers.push(ledger);polys.push(aggregate);qs.push(q);
    }
    let mut reference_polys=vec![[Fr::zero();3];2];let mut terminals=Vec::new();
    for owner in 0..2{
        let (mut a,mut b,mut x)=vc_toy_banks(owner,&terms,&input,&r,&u);
        for round in 0..2{
            let poly=useq_message(&a,&b,&x);v_owner_compare(4,poly,4,ledgers[round][owner])?;
            for i in 0..3{reference_polys[round][i]+=poly[i];}
            useq_fold(&mut a,qs[round]);useq_fold(&mut b,qs[round]);useq_fold(&mut x,qs[round]);
        }
        let terminal=[a[0],b[0],x[0]];vc_terminal_guard([candidate[owner].0[0],candidate[owner].1[0],candidate[owner].2[0]],terminal)?;
        let mut wrong=terminal;wrong[2]+=Fr::one();whole_require(vc_terminal_guard(wrong,terminal).is_err(),"complete sensitive scalar terminal X")?;
        terminals.push(terminal);
    }
    let mut foreign_terminal=terminals[0];foreign_terminal[2]=terminals[1][2];
    whole_require(foreign_terminal[2]!=terminals[0][2]
        && vc_terminal_guard(foreign_terminal,terminals[0]).is_err(),"complete sensitive foreign owner terminal X")?;
    let mut reference=initial;let mut previous=Fr::zero();
    for round in 0..2{
        let (q,next)=useq_reference_send(reference_polys[round],previous,&mut reference)?;previous=next;
        whole_require(reference_polys[round]==polys[round] && q==traces[round].0 && next==traces[round].1
            && u0_counters(&reference)==traces[round].2 && reference.clone().challenge_scalar(JH_CONTINUATION)==traces[round].3,
            "complete toy owner/round-major sender")?;
    }
    let mut bad=ledgers[0].clone();bad[0][0]+=Fr::one();bad[1][0]-=Fr::one();
    whole_require((0..3).all(|i|bad[0][i]+bad[1][i]==ledgers[0][0][i]+ledgers[0][1][i])
        && v_owner_compare(4,ledgers[0][0],4,bad[0]).err().as_deref()==Some("V candidate/canonical RIGHT owner polynomial mismatch"),
        "complete cancelling owner fault escaped ledger")?;
    let before=sender.clone();let wrong_claim=polys[0][0]+polys[0][0]+polys[0][1]+polys[0][2]+Fr::one();
    whole_require(s::edge_u_sequence_send_for_test(polys[0],wrong_claim,&mut sender.clone()).is_err(),"complete stale prior claim accepted")?;
    whole_require(vc_compare_trace(polys[1],qs[1]+Fr::one(),claim,&before,polys[1],qs[1],claim,&reference)
        .err().as_deref()==Some("complete independent sender sequence mismatch"),"complete stale challenge predicate")?;
    let mut terminal_zero=terminals[0];terminal_zero[2]=Fr::zero();
    whole_require(!terminals[0][2].is_zero() && vc_terminal_guard(terminal_zero,terminals[0]).is_err(),"complete zero terminal insensitive")?;
    Ok(())
}
fn vc_line_controls()->Result<(),String>{
    use crate::sparse_stream_roster as s;
    let u=general(12,3);let v=general(12,71);let local=general(21,139);
    for owner in [0usize,2,1023,2048,3072,4095]{
        let actual=s::edge_line_owner_contribution_for_test(owner,&local,&u,&v)?;
        let expected=vc_reference_contribution(owner,&local,&u,&v)?;vc_line_guard(&actual,&expected)?;
        let mut wrong=actual.clone();wrong[1]+=Fr::one();wrong[2]-=Fr::one();
        whole_require(wrong[0]==actual[0] && vc_eval(&wrong,Fr::one())==vc_eval(&actual,Fr::one())
            && vc_line_guard(&wrong,&expected).err().as_deref()==Some("complete line coefficient mismatch"),"complete interior-line fault")?;
        let mut wrong_sign_u=u.clone();wrong_sign_u[0]=Fr::one()-wrong_sign_u[0];
        let sign=vc_reference_contribution(owner,&local,&wrong_sign_u,&v)?;
        let owner_fault=vc_reference_contribution(owner^1,&local,&u,&v)?;
        let mut degree=actual.clone();degree.rotate_right(1);
        for fault in [sign,owner_fault,degree]{
            whole_require(fault!=expected && vc_line_guard(&fault,&expected).is_err(),"complete sensitive selector/convolution mutant")?;
        }
    }
    let values=general(4,13);let ul=general(2,7);let vl=general(2,41);
    vc_line_inputs(0,0,0,&values,&values,&ul,&vl,&ul,&vl)?;
    let mut changed=values.clone();changed[1]+=Fr::one();let mut point=ul.clone();point[0]+=Fr::one();
    for (failure,reason) in [
        (vc_line_inputs(0,0,0,&changed,&values,&ul,&vl,&ul,&vl),"complete line decoded Fr mismatch"),
        (vc_line_inputs(0,1,0,&values,&values,&ul,&vl,&ul,&vl),"complete line decoder owner mismatch"),
        (vc_line_inputs(0,0,0,&values,&values,&point,&vl,&ul,&vl),"complete line local point mismatch")]{
        whole_require(failure.err().as_deref()==Some(reason),"complete isolated line decoder predicate")?;
    }
    whole_require(s::edge_line_owner_contribution_for_test(4096,&local,&u,&v).is_err()
        && s::edge_line_owner_contribution_for_test(0,&local[..20],&u,&v).is_err(),"complete line geometry accepted")?;
    Ok(())
}
fn vc_codec_controls()->Result<(),String>{
    use crate::{gkr,transcript::Transcript};
    let proof=gkr::GkrProof{layers:vec![gkr::LayerProof{rounds:vec![vec![Fr::zero();3];64],
        left_value:Fr::zero(),right_value:Fr::zero(),line_coefficients:vec![Fr::zero();33]}]};
    let bytes=gkr::encode_proof(&proof)?;whole_require(bytes.len()==7264,"complete toy proof shape")?;
    let decoded=gkr::decode_dimensions(&[32],&bytes)?;whole_require(gkr::encode_proof(&decoded)?==bytes,"complete toy codec equality")?;
    let mut extended=bytes.clone();extended.push(0);let mut noncanonical=bytes.clone();noncanonical[..32].fill(255);
    for input in [&bytes[..7263],extended.as_slice(),noncanonical.as_slice()]{whole_require(gkr::decode_dimensions(&[32],input).is_err(),"complete joined codec fault accepted")?;}
    let requested=std::cell::RefCell::new(None);
    let mut transcript=Transcript::new(b"complete-internal-verifier-control-v1");
    let claim=gkr::verify_with_wiring(&[32],1usize<<32,&decoded,&mut transcript,|_|{},|_,r,u,v|{
        requested.replace(Some((r.to_vec(),u.to_vec(),v.to_vec())));Ok([Fr::zero();4])
    }).map_err(|e|e.to_string())?;
    whole_require(claim.point.len()==32 && claim.value.is_zero(),"complete internal InputClaim geometry")?;
    let points=requested.into_inner().ok_or("complete verifier callback absent")?;
    vc_requested_guard(0,&points.0,&points.1,&points.2,&points.0,&points.1,&points.2).map_err(|e|e.to_string())?;
    for component in 0..3{
        let mut wrong=points.clone();match component{0=>wrong.0[0]+=Fr::one(),1=>wrong.1[0]+=Fr::one(),_=>wrong.2[0]+=Fr::one()};
        whole_require(vc_requested_guard(0,&wrong.0,&wrong.1,&wrong.2,&points.0,&points.1,&points.2)
            .err()==Some(gkr::GkrError::PointDimension),"complete verifier exact-point guard")?;
    }Ok(())
}
fn vc_max_result()->serde_json::Value{
    let h="F".repeat(64);let n=u64::MAX;let counters=vec![n;3];
    let local_trace=(0..20).map(|_|serde_json::json!([h,h,h,counters,h,h,h])).collect::<Vec<_>>();
    let high_trace=(0..12).map(|_|serde_json::json!([h,h,h,counters,h])).collect::<Vec<_>>();
    let mut local=serde_json::Map::new();for k in VC_LOCAL_KEYS.split_whitespace(){local.insert(k.into(),serde_json::json!(vec![n;20]));}
    let mut terminal=vc_uint_object(VC_TERMINAL_KEYS);for value in terminal.as_object_mut().unwrap().values_mut(){*value=serde_json::json!(n);}
    let mut oracle=vc_uint_object(VC_ORACLE_KEYS);for value in oracle.as_object_mut().unwrap().values_mut(){*value=serde_json::json!(n);}
    let mut line_metrics=vc_uint_object(VC_LINE_KEYS);for value in line_metrics.as_object_mut().unwrap().values_mut(){*value=serde_json::json!(n);}
    let mut capacities=vc_uint_object(VC_CAP_KEYS);for value in capacities.as_object_mut().unwrap().values_mut(){*value=serde_json::json!(n);}
    capacities["line_primitive_peak_bytes"]=serde_json::Value::Null;capacities["line_primitive_peak_status"]=serde_json::json!("UNMEASURED");
    let mut times=vc_uint_object(VC_TIME_KEYS);for value in times.as_object_mut().unwrap().values_mut(){*value=serde_json::json!(n);}
    let mut result=serde_json::json!({"schema":"native-s12-v-complete-result-v1","version":n,"state":"V_COMPLETE_COMPONENT_PASS",
        "input_sha256":h,"reference_sha256":h,"prefix":{"local_round_matches":n,"local_oracle_matches":n,"high_round_matches":n,
            "high_u_matches":n,"initial_counters":counters,"final_counters":counters,"final_continuation":h,"left_value_equal":false},
        "local":{"trace":local_trace,"oracle_owner_comparisons":n,"oracle_terminal_comparisons":n,"oracle_sequence_equal":false},
        "terminal":{"owners":n,"candidate_triplets_sha256":h,"oracle_triplets_sha256":h,"comparisons":n,"checked":false},
        "high":{"trace":high_trace,"final_right_value":h,"sequence_equal":false}});
    result["wiring"]=serde_json::json!({"coefficients":vec![h.clone();4],"claim":h,"canonical_term_count":n,"channel_owners":n,
        "channel_combination_equal":false,"requested_point_equal":false,"r_sha256":h,"u_sha256":h,"v_sha256":h});
    result["line"]=serde_json::json!({"coefficients":vec![h.clone();33],"oracle_coefficients_sha256":h,
        "endpoint_values":vec![h.clone();2],"oracle_endpoint_values":vec![h.clone();2],"challenge":h,
        "transcript_counters":counters,"continuation":h,"coefficients_equal":false,"endpoints_equal":false});
    result["input_claim"]=serde_json::json!({"point":vec![h.clone();32],"value":h});
    result["proof"]=serde_json::json!({"bytes":n,"scalar_count":n,"sha256":h,"codec_roundtrip":false});
    result["verification"]=serde_json::json!({"dimensions":[n],"output_width":n,"input_claim_sha256":h,"transcript_counters":counters,
        "continuation":h,"claim_equal":false,"transcript_equal":false,"requested_point_equal":false});
    result["metrics"]=serde_json::json!({"local":local,"terminal":terminal,"oracle":oracle,"line":line_metrics});
    result["capacities"]=capacities;result["timings_ns"]=times;result
}
fn vc_size_controls()->Result<(),String>{
    whole_require(serde_json::to_vec(&vc_max_result()).map_err(|e|e.to_string())?.len()<=65536,"complete maximum result bound")?;
    let h="F".repeat(64);let summary=serde_json::json!({"schema":"native-s12-v-complete-summary-v1","version":u64::MAX,
        "result":"HOLD","failed_stage":"canonical-oracle","reason":"\u{0001}".repeat(256),"input_sha256":h,
        "result_sha256":h,"proof_sha256":h,"progress":{"stage":"canonical-oracle","round":u64::MAX,"completed":u64::MAX},"elapsed_ns":u64::MAX});
    whole_require(serde_json::to_vec(&summary).map_err(|e|e.to_string())?.len()<=4096,"complete escaped summary bound")?;
    whole_require(vc_sha(b"")==Ok("E3B0C44298FC1C149AFBF4C8996FB92427AE41E4649B934CA495991B7852B855".into())
        && vc_sha(b"abc")==Ok("BA7816BF8F01CFEA414140DE5DAE2223B00361A396177A9CB410FF61F20015AD".into())
        && vc_sha(&vec![0u8;393216])==Ok("A6619F482FEE91A315F76CDCD8705D39B6CE11077C435CCC696142E130C27762".into())
        && vc_sha_len(393217).is_err(),"complete SHA known-answer/boundary controls")?;
    Ok(())
}
fn vc_retention_controls()->Result<(),String>{
    let nonce=std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map_err(|e|e.to_string())?.as_nanos();
    let path=std::env::temp_dir().join(format!("native-v-complete-{}-{nonce}.part",std::process::id()));
    let progress=std::cell::RefCell::new(VcProgress{stage:"proof",round:None,completed:1,active:false,events:168});
    let ready=serde_json::json!({"state":"V_COMPLETE_COMPONENT_PASS","publication_ready":true});
    useq_save(&path,&ready,65536,true)?;let before=std::fs::read(&path).map_err(|e|e.to_string())?;
    vc_hold_part(&path,&progress)?;
    whole_require(std::fs::read(&path).map_err(|e|e.to_string())?==before,"complete caught HOLD rewrote ready opaque part")?;
    whole_require(vc_hold_part(&path.join("invalid-child"),&progress).is_err(),"complete HOLD metadata IO failure swallowed")?;
    std::fs::remove_file(&path).map_err(|e|e.to_string())?;
    vc_hold_part(&path,&progress)?;
    let observed:serde_json::Value=serde_json::from_slice(&std::fs::read(&path).map_err(|e|e.to_string())?).map_err(|e|e.to_string())?;
    whole_require(observed==vc_progress_json(&progress.borrow()),"complete absent HOLD part not created")?;
    std::fs::remove_file(&path).map_err(|e|e.to_string())?;
    whole_require(vc_hold_part(&path.join("missing-parent"),&progress).is_err(),"complete HOLD creation IO failure swallowed")?;
    Ok(())
}
#[test]
fn native_v_complete_controls(){
    vc_size_controls().expect("complete byte/ABI controls");
    vc_retention_controls().expect("complete caught HOLD part retention controls");
    vc_wrapper_controls().expect("complete real grouped/deferred wrapper controls");
    vc_sequence_controls().expect("complete owner-major/sequence controls");
    vc_line_controls().expect("complete line joining controls");
    vc_codec_controls().expect("complete codec/consumer controls");
}
fn vc_run(){
    use std::io::Write;use std::os::windows::fs::MetadataExt;
    let start=std::time::Instant::now();let output=std::path::PathBuf::from(
        std::env::var_os("NIPOPOW_NATIVE_V_COMPLETE_OUTPUT_DIR").expect("complete output env"));
    let info=std::fs::symlink_metadata(&output).expect("complete output metadata");
    assert!(info.is_dir() && info.file_attributes()&0x400==0 && std::fs::read_dir(&output).unwrap().next().is_none(),"complete output not fresh regular directory");
    assert!(!output.canonicalize().unwrap().starts_with(std::env::temp_dir().canonicalize().unwrap()),"complete output inside TEMP");
    let progress=std::cell::RefCell::new(VcProgress{stage:"prefix",round:None,completed:0,active:false,events:0});
    let result=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||vc_execute(&output,start,&progress)))
        .unwrap_or_else(|_|Err("complete component panic".into()));
    let (status,failed,reason,input_sha,result_sha,proof_sha)=match &result{
        Ok(report)=>("V_COMPLETE_COMPONENT_PASS",None,String::new(),report["input_sha256"].as_str().map(str::to_owned),
            Some(vc_sha(&serde_json::to_vec(report).unwrap()).expect("complete result SHA")),report["proof"]["sha256"].as_str().map(str::to_owned)),
        Err(reason)=>{
            let active=progress.borrow().active;let completed=progress.borrow().completed;
            if active{vc_emit(&progress,"hold",completed,start).expect("complete HOLD event");}
            vc_hold_part(&output.join("v-complete.part"),&progress).expect("complete retained partial");
            let mut end=reason.len().min(256);while !reason.is_char_boundary(end){end-=1;}
            ("HOLD",Some(progress.borrow().stage),reason[..end].to_owned(),None,None,None)
        }
    };
    let summary=serde_json::json!({"schema":"native-s12-v-complete-summary-v1","version":1,"result":status,"failed_stage":failed,
        "reason":reason,"input_sha256":input_sha,"result_sha256":result_sha,"proof_sha256":proof_sha,
        "progress":vc_progress_json(&progress.borrow()),"elapsed_ns":screen_ns(start)});
    useq_save(&output.join("summary.json"),&summary,4096,true).expect("complete summary save");
    let footer=serde_json::json!({"result":status,"failed_stage":failed,"elapsed_ns":screen_ns(start)});
    let line=format!("NATIVE_V_COMPLETE_REPORT {footer}\n");assert!(line.len()<=224);
    let mut stdout=std::io::stdout().lock();stdout.write_all(line.as_bytes()).expect("complete footer write");stdout.flush().expect("complete footer flush");drop(stdout);
    assert!(result.is_ok(),"native complete V diagnostic HOLD");
}
#[test]
#[ignore="fixture-bound native V20/high-V12/line/InputClaim; separate1800s/2GiB controller"]
fn native_s12_v_complete_bounded(){vc_run();}

#[path = "native_role4_live_tests.rs"]
mod live_join;


// A canonical row-source residual diagnostic, deliberately independent of proof production.
#[cfg(test)]
mod role2_residual_diagnostic {
    use super::*;
    use crate::{gkr::Gate,packed::{PackedFile,PackedOwnerBits,PackedReaderFault},
        work_tree_fixed_hash as fixed,work_tree_leaf_hash as leaf,work_tree_work as work,
        work_tree_wiring::{Descriptor,Family,Mapping}};
    use serde::Serialize;
    use std::{fs::File,io::{Seek,SeekFrom,Write},mem::size_of,path::PathBuf,time::Instant};

    const OWNERS:usize=4096;
    const MEMBERS:usize=40;
    const OWNER_BYTES:usize=131072;
    const AUX:usize=4*1024*1024;
    const REPORT_CAP:usize=16384;
    const DEADLINE:u64=300_000_000_000;
    const RAW_SHA:&str="ABB3D74AE75256CED63110B72C2E0D5EBA1B90B09889E45EA327BDA1C9A640D2";
    const WITNESS_SHA:&str="C1CC1CF72FF539F259A3BDEF756332BA52CB8AFF26C11AB4116D1B2F9D17ED43";
    const WITNESS_BLAKE:&str="725D7B1215E1185C52C1012D9294260612653ACAD53A02429B8EAAFD0F0770C8";

    #[derive(Debug,Clone,Copy,PartialEq,Eq,Serialize)]
    pub(super) struct Failure {code:&'static str,slot:usize,member:usize,row:usize}
    type Result<T>=std::result::Result<T,Failure>;
    fn fail(code:&'static str,slot:usize,member:usize,row:usize)->Failure{Failure{code,slot,member,row}}
    fn require(ok:bool,code:&'static str)->Result<()> {if ok{Ok(())}else{Err(fail(code,0,0,0))}}
    fn add(a:usize,b:usize)->Result<usize>{a.checked_add(b).ok_or(fail("size_overflow",0,0,0))}
    fn mul(a:usize,b:usize)->Result<usize>{a.checked_mul(b).ok_or(fail("size_overflow",0,0,0))}
    fn increment(n:&mut u64,slot:usize,tag:usize,row:usize)->Result<()> {
        *n=n.checked_add(1).ok_or(fail("counter_overflow",slot,tag,row))?;Ok(())
    }
    #[derive(Default,Clone,Copy,Debug,PartialEq,Eq)]
    pub(super) struct Count {pub(super) terms:u64,pub(super) rows:u64}
    fn census(expected:&[Count;MEMBERS],actual:&[Count;MEMBERS],slots:usize)->Result<()> {
        require(slots==OWNERS,"incomplete_slots")?;
        for tag in 0..MEMBERS {if actual[tag]!=expected[tag]{return Err(fail("census",slots,tag,0));}}Ok(())
    }
    fn evaluate(g:&Gate,x:bool,y:bool)->Fr {
        let mut value=g.c0;if x{value+=g.c1;}if y{value+=g.c2;}if x&&y{value+=g.c3;}value
    }
    struct Rows<'a> {
        slot:usize,strides:&'a [usize;MEMBERS],counts:[Count;MEMBERS],last:Option<usize>,sum:Fr,
    }
    impl<'a> Rows<'a> {
        fn new(slot:usize,strides:&'a [usize;MEMBERS])->Self {
            Self{slot,strides,counts:[Count::default();MEMBERS],last:None,sum:Fr::zero()}
        }
        fn flush(&self)->Result<()> {
            if let Some(row)=self.last {if !self.sum.is_zero(){return Err(fail("residual",self.slot,row>>26,row));}}Ok(())
        }
        fn term(&mut self,t:Term,mut read:impl FnMut(usize,bool)->Result<bool>)->Result<()> {
            let tag=t.row>>26;let slot=self.slot;let row=t.row;let at=|code|fail(code,slot,tag,row);
            if t.row>=1usize<<32{return Err(at("row_domain"));}
            if tag>=MEMBERS{return Err(at("member_tag"));}
            let stride=self.strides[tag];if stride>14{return Err(at("stride"));}
            let local=t.row&((1usize<<26)-1);
            if local>>(stride+12)!=0{return Err(at("zero_extension"));}
            if local>>stride!=self.slot{return Err(at("source_slot"));}
            if t.gate.left>=1usize<<32||t.gate.right>=1usize<<32{return Err(at("endpoint_domain"));}
            if self.last.is_some_and(|row|t.row<row){return Err(at("row_order"));}
            if self.last!=Some(t.row){self.flush()?;self.last=Some(t.row);self.sum=Fr::zero();
                increment(&mut self.counts[tag].rows,self.slot,tag,t.row)?;}
            increment(&mut self.counts[tag].terms,self.slot,tag,t.row)?;
            let g=&t.gate;
            let x=if !g.c1.is_zero()||!g.c3.is_zero(){read(g.left,true).map_err(|e|at(e.code))?}else{false};
            let y=if !g.c2.is_zero()||!g.c3.is_zero(){read(g.right,false).map_err(|e|at(e.code))?}else{false};
            self.sum+=evaluate(g,x,y);Ok(())
        }
        fn close(self)->Result<[Count;MEMBERS]>{self.flush()?;Ok(self.counts)}
    }
    #[derive(Default,Serialize)]
    struct CacheStats {max_owners:usize,payload_peak_bytes:usize,loads:u64,left_reads:u64,right_reads:u64}
    struct Cache {owners:[usize;5],packets:[Option<PackedOwnerBits>;5],len:usize}
    fn insert(support:&mut [usize;5],len:&mut usize,owner:usize)->Result<()> {
        require(owner<OWNERS,"support_owner")?;
        if !support[..*len].contains(&owner){require(*len<5,"support_capacity")?;support[*len]=owner;*len+=1;}Ok(())
    }
    fn family_support(f:&Family,d:&Descriptor,slot:usize,s:&mut [usize;5],n:&mut usize)->Result<()> {
        let (lo,hi)=match f.mapping {Mapping::Same{lo,hi}|Mapping::HeaderSuccessor{lo,hi}|
            Mapping::FixedRight{lo,hi,..}=>(lo,hi),Mapping::Child{level,..}=>{
                let (lo,count)=d.level(level).map_err(|_|fail("support_level",slot,0,0))?;(lo,add(lo,count)?)} };
        if !(lo..hi).contains(&slot)||f.constants.is_some(){return Ok(());}
        let owner=match f.mapping {Mapping::Same{..}=>slot,Mapping::HeaderSuccessor{..}=>
                slot.checked_sub(1).ok_or(fail("support_predecessor",slot,0,0))?,
            Mapping::FixedRight{target,..}=>{require(target==d.profile_node_slot&&target==4095,"support_profile")?;target},Mapping::Child{level,branch}=>{
                require(branch<2,"support_branch")?;
                let base=if level==1{0}else{d.level(level-1).map_err(|_|fail("support_level",slot,0,0))?.0};
                add(add(base,mul(slot-lo,2)?)?,branch)?}};
        insert(s,n,owner)
    }
    fn support(parent:&WorkTreeHistoryPlan,slot:usize)->Result<([usize;5],usize)> {
        let mut s=[0;5];let mut n=0;insert(&mut s,&mut n,slot)?;
        let topology=parent.topology();for f in topology.families.iter().chain(parent.work_boundary().links()){
            family_support(f,&topology.descriptor,slot,&mut s,&mut n)?;}
        require(n<=5,"support_capacity")?;Ok((s,n))
    }
    impl Cache {
        fn load(source:&PackedFile,owners:[usize;5],len:usize,stats:&mut CacheStats)->Result<Self> {
            require((1..=5).contains(&len),"cache_capacity")?;
            require(mul(len,OWNER_BYTES)?<=655360,"cache_payload_bound")?;
            require(add(mul(len,OWNER_BYTES)?,size_of::<Self>()+2*size_of::<[Count;MEMBERS]>()+REPORT_CAP+32768)?<=AUX,"aux_preflight")?;
            let view=source.native_role0_view().map_err(|_|fail("native_view",0,0,0))?;
            view.require_same_source(source).map_err(|_|fail("same_source",0,0,0))?;
            let mut out=Self{owners,packets:std::array::from_fn(|_|None),len};let mut payload=0;
            for index in 0..len {
                let packet=view.read_copy(owners[index]).map_err(|_|fail("packet_read",owners[index],0,0))?;
                require(packet.len()==1usize<<20&&packet.capacity_bytes()==OWNER_BYTES,"packet_capacity")?;
                payload=add(payload,packet.capacity_bytes())?;out.packets[index]=Some(packet);
                increment(&mut stats.loads,owners[index],0,0)?;
            }
            stats.max_owners=stats.max_owners.max(len);stats.payload_peak_bytes=stats.payload_peak_bytes.max(payload);
            require(add(payload,size_of::<Self>()+2*size_of::<[Count;MEMBERS]>()+REPORT_CAP+32768)?<=AUX,"aux_capacity")?;
            Ok(out)
        }
        fn bit(&self,wire:usize,left:bool,stats:&mut CacheStats,flip:Option<usize>)->Result<bool> {
            require(wire<1usize<<32,"endpoint_domain")?;
            let index=self.owners[..self.len].iter().position(|o|*o==wire>>20)
                .ok_or(fail("missing_owner",0,0,0))?;
            let packet=self.packets[index].as_ref().ok_or(fail("missing_packet",0,0,0))?;
            increment(if left{&mut stats.left_reads}else{&mut stats.right_reads},0,0,0)?;
            Ok(packet.bit_at(wire&((1usize<<20)-1)) ^ (flip==Some(wire)))
        }
    }
    // Recursive capacity model for the bounded count-report Value. BTreeMap nodes
    // are private to serde_json: reserve512 bytes per entry in addition to strings.
    fn value_capacity(v:&serde_json::Value)->Result<usize> {
        use serde_json::Value;
        match v {Value::String(s)=>Ok(add(size_of::<Value>(),s.capacity())?),Value::Array(a)=>{
            let mut n=mul(a.capacity(),size_of::<Value>())?;for x in a{n=add(n,value_capacity(x)?)?;}Ok(n)},
            Value::Object(m)=>{let mut n=mul(m.len(),512)?;for(k,x)in m{n=add(n,add(k.capacity(),value_capacity(x)?)?)?;}Ok(n)},
            _=>Ok(size_of::<Value>())}
    }
    pub(super) fn expectations(parent:&WorkTreeHistoryPlan,plan:&NativePrefixAuthPlan<'_>)->Result<([Count;MEMBERS],[usize;MEMBERS])> {
        let d=&parent.topology().descriptor;let descriptor=&plan.descriptors()[2];
        require((descriptor.input_log,descriptor.row_log,descriptor.ordered_tags.len())==(32,32,40),"descriptor_geometry")?;
        require((d.headers,d.genuine,d.leaves,d.slots,d.profile_node_slot)==(3073,3072,4096,4096,4095),"native_geometry")?;
        let mut counts=[Count::default();MEMBERS];let mut strides=[0;MEMBERS];
        require(parent.topology().families.len()==34&&parent.work_boundary().links().len()==3,"member_geometry")?;
        for (tag,f) in parent.topology().families.iter().enumerate().chain(
            parent.work_boundary().links().iter().enumerate().map(|(i,f)|(37+i,f))) {
            let c=f.count(d).map_err(|_|fail("family_count",0,tag,0))?;
            require(c.row_log>=12&&c.row_log<=26&&c.name==descriptor.ordered_tags[tag],"family_identity")?;
            counts[tag]=Count{terms:c.terms,rows:c.live_rows};strides[tag]=c.row_log-12;
        }
        require(descriptor.ordered_tags[34..37]==["fixed","leaf","work-local"],"local_identity")?;
        for (index,name) in descriptor.ordered_tags.iter().enumerate(){
            require(!name.is_empty()&&name.len()<=96&&name.bytes().enumerate().all(|(i,b)|
                b.is_ascii_lowercase()||b.is_ascii_digit()||b==b'_'||(i>0&&b==b'-'))&&
                !descriptor.ordered_tags[..index].contains(name),"member_name")?;}
        let engine=fixed::engine().map_err(|_|fail("fixed_engine",0,34,0))?;
        let c=fixed::count(engine,parent.fixed_profile()).map_err(|_|fail("fixed_count",0,34,0))?;
        counts[34]=Count{terms:c.total_boundary_terms,rows:c.materialized_live_rows};strides[34]=11;
        // Work count clones exactly its private local templates. The disjoint
        // genuine/padding masks make these two streaming counts an exact bound.
        let mut work_terms=0usize;
        for slot in [0,d.genuine] {parent.work_boundary().emit_slot(slot,|_|work_terms+=1)
            .map_err(|_|fail("work_count_preflight",slot,36,0))?;}
        let clone_bound=mul(work_terms,size_of::<Term>())?;
        require(add(clone_bound,256*1024)?<=2*1024*1024,"count_clone_bound")?;
        let lc=leaf::count(engine,parent.leaf_boundary()).map_err(|_|fail("leaf_count",0,35,0))?;
        require(value_capacity(&lc)?<=128*1024,"leaf_count_capacity")?;
        let wc=work::count(parent.work_boundary()).map_err(|_|fail("work_count",0,36,0))?;
        require(add(add(value_capacity(&lc)?,value_capacity(&wc)?)?,clone_bound)?<=2*1024*1024,"count_capacity")?;
        let number=|v:&serde_json::Value,key:&str|v[key].as_u64().ok_or(fail("count_field",0,0,0));
        counts[35]=Count{terms:number(&lc,"new_boundary_terms")?,rows:number(&lc,"new_boundary_rows")?};strides[35]=14;
        counts[36]=Count{terms:number(&wc,"new_local_terms")?,rows:number(&wc,"new_local_rows")?};strides[36]=11;
        require(counts[37..].iter().map(|c|c.terms).sum::<u64>()==number(&wc,"new_link_terms")?,"link_count")?;
        require(counts[37..].iter().map(|c|c.rows).sum::<u64>()==number(&wc,"new_link_rows")?,"link_rows")?;
        drop(wc);drop(lc);drop(c);
        let terms=counts.iter().try_fold(0u64,|a,c|a.checked_add(c.terms).ok_or(fail("counter_overflow",0,0,0)))?;
        let rows=counts.iter().try_fold(0u64,|a,c|a.checked_add(c.rows).ok_or(fail("counter_overflow",0,0,0)))?;
        require(terms==129277400&&rows==76211168,"static_crosscheck")?;Ok((counts,strides))
    }
    fn stream(plan:&NativePrefixAuthPlan<'_>,slot:usize,strides:&[usize;MEMBERS],cache:&Cache,
        stats:&mut CacheStats,omit:Option<usize>,flip:Option<usize>)->Result<[Count;MEMBERS]> {
        let mut rows=Rows::new(slot,strides);let mut skipped=0usize;let mut failure=None;
        let emitted=plan.visit_role_owner_terms(2,slot as u64,|t|{
            if omit==Some(t.row)&&!t.gate.c0.is_zero()&&t.gate.left==0&&t.gate.right==0 {
                skipped+=1;return Ok(());}
            match rows.term(t,|wire,left|cache.bit(wire,left,stats,flip)){
                Ok(())=>Ok(()),Err(e)=>{failure=Some(e);Err("role2 diagnostic sink".into())}}
        });
        if let Some(e)=failure{return Err(e);}
        let emitted=emitted.map_err(|_|fail("canonical_visitor",slot,0,0))?;
        require(skipped==usize::from(omit.is_some()),"omit_hit")?;
        let counts=rows.close()?;
        require(counts.iter().map(|c|c.terms).sum::<u64>()+skipped as u64==emitted as u64,"visitor_count")?;Ok(counts)
    }
    fn ordinary()->Result<()> {
        let strides=[2;MEMBERS];let gate=Gate{left:0,right:1,c0:Fr::from(7),c1:Fr::from(2),c2:Fr::from(3),c3:Fr::from(5)};
        for x in [false,true]{for y in [false,true]{let a=Fr::from(u64::from(x));let b=Fr::from(u64::from(y));
            require(evaluate(&gate,x,y)==gate.c0+gate.c1*a+gate.c2*b+gate.c3*a*b,"boolean_evaluation")?;}}
        let zero=|row|Term{row,gate:Gate{left:0,right:0,c0:Fr::zero(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}};
        let run=|slot,terms:Vec<Term>,bits:[bool;2],s:&[usize;MEMBERS]|->Result<[Count;MEMBERS]>{
            let mut rows=Rows::new(slot,s);for t in terms{rows.term(t,|w,_|bits.get(w).copied().ok_or(fail("missing_owner",0,0,0)))?;}rows.close()};
        let mut plus=zero(0);plus.gate.c0=Fr::one();let mut minus=plus.clone();minus.gate.c0=-Fr::one();
        let count=run(0,vec![plus.clone(),minus.clone(),zero(1)],[false;2],&strides)?;
        require(count[0]==Count{terms:3,rows:2},"repeated_row")?;
        require(run(0,vec![plus],[false;2],&strides).unwrap_err()==fail("residual",0,0,0),"nonzero_negative")?;
        run(1,vec![zero(4)],[false;2],&strides)?;run(0,vec![zero(0)],[false;2],&strides)?;
        let cases=[(zero(40usize<<26),"member_tag"),(zero(1<<32),"row_domain"),
            (zero(1<<(2+12)),"zero_extension"),(zero(4),"source_slot")];
        for (t,code) in cases {let expected=fail(code,0,t.row>>26,t.row);
            require(run(0,vec![t],[false;2],&strides).unwrap_err()==expected,"isolated_row_negative")?;}
        let mut bad=strides;bad[0]=15;
        require(run(0,vec![zero(0)],[false;2],&bad).unwrap_err()==fail("stride",0,0,0),"stride_negative")?;
        let mut endpoint=zero(0);endpoint.gate.left=1usize<<32;
        require(run(0,vec![endpoint],[false;2],&strides).unwrap_err()==fail("endpoint_domain",0,0,0),"endpoint_negative")?;
        let mut endpoint=zero(0);endpoint.gate.right=1usize<<32;
        require(run(0,vec![endpoint],[false;2],&strides).unwrap_err()==fail("endpoint_domain",0,0,0),"right_endpoint_negative")?;
        require(run(0,vec![zero(1),zero(0)],[false;2],&strides).unwrap_err()==fail("row_order",0,0,0),"order_negative")?;
        let empty=Cache{owners:[0;5],packets:std::array::from_fn(|_|None),len:0};let mut missing=zero(0);missing.gate.c1=Fr::one();
        let mut rows=Rows::new(0,&strides);
        require(rows.term(missing,|w,left|empty.bit(w,left,&mut CacheStats::default(),None)).unwrap_err()
            ==fail("missing_owner",0,0,0),"missing_cache_negative")?;
        let expected=run(0,vec![zero(0)],[false;2],&strides)?;
        let doubled=run(0,vec![zero(0),zero(0)],[false;2],&strides)?;
        require(census(&expected,&doubled,4096).unwrap_err()==fail("census",4096,0,0),"zero_duplicate_negative")?;
        require(census(&expected,&expected,4095).unwrap_err()==fail("incomplete_slots",0,0,0),"coverage_negative")?;
        let mut over=u64::MAX;require(increment(&mut over,1,2,3).unwrap_err()==fail("counter_overflow",1,2,3),"counter_negative")?;
        require(add(usize::MAX,1).unwrap_err().code=="size_overflow"&&mul(usize::MAX,2).unwrap_err().code=="size_overflow","size_negative")?;
        let mut writer=Bounded::new()?;require(writer.write_all(&[0;REPORT_CAP+1]).is_err()&&writer.bytes.is_empty(),"report_negative")?;
        Ok(())
    }
    fn elapsed(start:Instant)->Result<u64>{let ns=u64::try_from(start.elapsed().as_nanos()).map_err(|_|fail("clock_overflow",0,0,0))?;
        require(ns<=DEADLINE,"deadline")?;Ok(ns)}
    fn mark(stage:&str,slot:usize,ns:u64)->Result<()> {
        let mut out=std::io::stderr().lock();writeln!(out,"NATIVE_ROLE2_RESIDUAL_STAGE {stage} slot={slot} elapsed_ns={ns}")
            .map_err(|_|fail("progress_write",slot,0,0))?;out.flush().map_err(|_|fail("progress_flush",slot,0,0))
    }
    struct Bounded{bytes:Vec<u8>}
    impl Bounded{fn new()->Result<Self>{let mut bytes=Vec::new();bytes.try_reserve_exact(REPORT_CAP).map_err(|_|fail("report_allocation",0,0,0))?;
        require(bytes.capacity()==REPORT_CAP,"report_capacity")?;Ok(Self{bytes})}}
    impl Write for Bounded {
        fn write(&mut self,bytes:&[u8])->std::io::Result<usize>{
            if self.bytes.len().checked_add(bytes.len()).is_none_or(|n|n>REPORT_CAP){return Err(std::io::Error::other("role2 report bound"));}
            self.bytes.extend_from_slice(bytes);Ok(bytes.len())}
        fn flush(&mut self)->std::io::Result<()>{Ok(())}
    }
    #[derive(Serialize)]
    struct Scope {input_log:usize,row_log:usize,owners:usize,active_headers:usize,members:usize,residual_only:bool,
        gkr:bool,pcs:bool,all_seven_roles:bool,production:bool,deadline_seconds:usize,auxiliary_limit_bytes:usize}
    #[derive(Serialize)]
    struct Inputs {raw_sha256:&'static str,witness_sha256:&'static str,witness_blake2b256:&'static str}
    #[derive(Serialize)]
    struct Member<'a>{tag:usize,name:&'a str,stride_log:usize,expected_terms:u64,expected_rows:u64,observed_terms:u64,observed_rows:u64}
    #[derive(Serialize)]
    struct CountMember<'a>{tag:usize,name:&'a str,stride_log:usize,terms:u64,rows:u64}
    #[derive(Serialize)]
    struct CountReport<'a>{schema:&'static str,state:&'static str,input_log:usize,row_log:usize,owners:usize,
        active_headers:usize,count_only:bool,native_inputs:bool,members:&'a [CountMember<'a>],canonical_terms:u64,occupied_rows:u64}
    #[derive(Default,Serialize)]
    struct Checks {ordinary_boundaries:bool,honest_slot1:bool,omitted_global0:bool,flipped_final_flag:bool,typed_io:bool,
        typed_short:bool,typed_short_by_one_byte:bool,detached_source:bool,census:bool,coverage:bool,custody_unchanged:bool}
    #[derive(Serialize)]
    struct Report<'a>{schema:&'static str,state:&'static str,stage:&'static str,error:Option<Failure>,scope:Scope,inputs:Inputs,
        members:&'a [Member<'a>],completed_slots:usize,canonical_terms:u64,occupied_rows:u64,cache:CacheStats,checks:Checks,elapsed_ns:u64}
    pub(super) fn raw_hold()->Result<(File,U0FileInfo,PathBuf)> {
        use std::os::windows::fs::MetadataExt;
        let path=PathBuf::from(std::env::var_os("NIPOPOW_NATIVE_AUTH_FIXTURE").ok_or(fail("raw_env",0,0,0))?);
        let md=std::fs::symlink_metadata(&path).map_err(|_|fail("raw_metadata",0,0,0))?;
        require(path.is_absolute()&&md.is_file()&&md.file_attributes()&0x400==0&&md.len()==869449,"raw_extent")?;
        let file=OpenOptions::new().read(true).share_mode(1).open(&path).map_err(|_|fail("raw_open",0,0,0))?;
        let identity=u0_file_info(&file).map_err(|_|fail("raw_identity",0,0,0))?;
        raw_hash(&file)?;Ok((file,identity,path))
    }
    pub(super) fn raw_hash(file:&File)->Result<()> {
        let mut reader=file.try_clone().map_err(|_|fail("raw_clone",0,0,0))?;
        reader.seek(SeekFrom::Start(0)).map_err(|_|fail("raw_seek",0,0,0))?;
        let mut bytes=Vec::new();bytes.try_reserve_exact(869450).map_err(|_|fail("raw_allocation",0,0,0))?;
        require(bytes.capacity()==869450,"raw_capacity")?;
        reader.take(869450).read_to_end(&mut bytes).map_err(|_|fail("raw_read",0,0,0))?;
        require(bytes.len()==869449,"raw_extent")?;
        require(screen_hex(&crate::native_prefix_auth_plan::role0_sha256(&bytes).map_err(|_|fail("raw_sha",0,0,0))?)==RAW_SHA,"raw_sha")
    }
    pub(super) fn packed_hash(file:&mut File)->Result<()> {
        use blake2::{Blake2b,Digest,digest::consts::U32};
        file.seek(SeekFrom::Start(0)).map_err(|_|fail("packed_seek",0,0,0))?;
        let mut hash=Blake2b::<U32>::new();let mut scratch=Vec::new();scratch.try_reserve_exact(1<<20).map_err(|_|fail("hash_allocation",0,0,0))?;
        require(scratch.capacity()==1<<20,"hash_capacity")?;scratch.resize(1<<20,0);let mut size=0usize;
        loop{let n=file.read(&mut scratch).map_err(|_|fail("packed_hash_read",0,0,0))?;if n==0{break;}
            size=add(size,n)?;require(size<=536870912,"packed_extent")?;hash.update(&scratch[..n]);}
        require(size==536870912&&screen_hex(&hash.finalize())==WITNESS_BLAKE,"packed_hash")
    }
    fn execute(start:Instant,stage:&mut &'static str)->Result<Vec<u8>> {
        *stage="admission";mark(stage,0,elapsed(start)?)?;
        ordinary()?;let mut checks=Checks{ordinary_boundaries:true,..Checks::default()};
        let (raw,raw_identity,raw_path)=raw_hold()?;
        let path=PathBuf::from(std::env::var_os("NIPOPOW_NATIVE_U_SEQUENCE_WITNESS").ok_or(fail("packed_env",0,0,0))?);
        require(path.is_absolute(),"packed_path")?;
        let (source,mut held,identity)=useq_admit().map_err(|_|fail("packed_admission",0,0,0))?;
        let view=source.native_role0_view().map_err(|_|fail("native_view",0,0,0))?;
        view.require_same_source(&source).map_err(|_|fail("same_source",0,0,0))?;
        *stage="plan";mark(stage,0,elapsed(start)?)?;
        let native=input();let candidate=Candidate{n:3073,root:native.root(),total:native.total_be28(),
            tip:ergo_header_core::blake2b256(native.raw(3073).map_err(|_|fail("raw_tip",0,0,0))?),
            tip_time:native.timestamp(3073).map_err(|_|fail("raw_tip_time",0,0,0))?};
        // Parent/templates and the retained fixed engine use the existing native
        // construction path under the Job cap; they are outside the auxiliary4MiB.
        let parent=WorkTreeHistoryPlan::compile(3073,12,candidate.root,candidate.total).map_err(|_|fail("parent",0,0,0))?;drop(native);
        let plan=NativePrefixAuthPlan::compile(&parent,Selection::s12(),candidate).map_err(|_|fail("plan",0,0,0))?;
        *stage="counts";mark(stage,0,elapsed(start)?)?;let (expected,strides)=expectations(&parent,&plan)?;
        *stage="sensitization";mark(stage,1,elapsed(start)?)?;
        let detached=PackedFile::open_with_limit(&path,32,32).map_err(|_|fail("detached_open",1,0,0))?;
        require(view.require_same_source(&detached).unwrap_err()=="native role0 detached packed source","detached_negative")?;
        drop(detached);checks.detached_source=true;
        for (fault,kind) in [(PackedReaderFault::Short,0),(PackedReaderFault::ShortByOneByte,1),(PackedReaderFault::Io,2)] {
            let error=view.reader_fault_for_test(1,fault).err().ok_or(fail("typed_fault_accepted",1,0,0))?;
            let expected=if kind==2{"native role0 owner read: isolated native role0 reader fault"}
                else{"native role0 owner read: failed to fill whole buffer"};
            require(error==expected,"typed_fault_identity")?;
            match kind{0=>checks.typed_short=true,1=>checks.typed_short_by_one_byte=true,_=>checks.typed_io=true}
        }
        let (owners,len)=support(&parent,1)?;let mut negative_stats=CacheStats::default();let cache=Cache::load(&source,owners,len,&mut negative_stats)?;
        stream(&plan,1,&strides,&cache,&mut negative_stats,None,None)?;checks.honest_slot1=true;
        let target=(34usize<<26)+(1<<11)+1600;
        let flip=(1usize<<20)+fixed::NODE_CORE+fixed::engine().map_err(|_|fail("fixed_engine",1,34,target))?.base.compression.final_flag;
        let mut constant_hits=0;let mut flag_hits=0;
        plan.visit_role_owner_terms(2,1,|t|{if t.row==target {
            if t.gate.left==0&&t.gate.right==0&&!t.gate.c0.is_zero(){constant_hits+=1;}
            if t.gate.left==flip&&!t.gate.c1.is_zero(){flag_hits+=1;}}Ok(())})
            .map_err(|_|fail("sensitization_visit",1,34,target))?;
        require(constant_hits==1&&flag_hits==1,"sensitization_source")?;
        require(stream(&plan,1,&strides,&cache,&mut negative_stats,Some(target),None).unwrap_err()
            ==fail("residual",1,34,target),"omit_negative")?;checks.omitted_global0=true;
        require(stream(&plan,1,&strides,&cache,&mut negative_stats,None,Some(flip)).unwrap_err()
            ==fail("residual",1,34,target),"flip_negative")?;checks.flipped_final_flag=true;
        drop(cache);drop(negative_stats);
        *stage="scan";mark(stage,0,elapsed(start)?)?;
        let mut stats=CacheStats::default();let mut observed=[Count::default();MEMBERS];let mut completed=0usize;
        for slot in 0..OWNERS {
            let (owners,len)=support(&parent,slot)?;let cache=Cache::load(&source,owners,len,&mut stats)?;
            let current=stream(&plan,slot,&strides,&cache,&mut stats,None,None)?;drop(cache);
            for tag in 0..MEMBERS {
                observed[tag].terms=observed[tag].terms.checked_add(current[tag].terms).ok_or(fail("counter_overflow",slot,tag,0))?;
                observed[tag].rows=observed[tag].rows.checked_add(current[tag].rows).ok_or(fail("counter_overflow",slot,tag,0))?;
            }
            completed=add(completed,1)?;if completed%256==0{mark(stage,completed,elapsed(start)?)?;}
        }
        census(&expected,&observed,completed)?;checks.census=true;checks.coverage=true;
        let terms=observed.iter().map(|c|c.terms).sum::<u64>();let occupied_rows=observed.iter().map(|c|c.rows).sum::<u64>();
        require(stats.loads<=5*4096&&stats.max_owners<=5&&stats.payload_peak_bytes<=655360&&
            stats.left_reads<=terms&&stats.right_reads<=terms&&stats.left_reads>0&&stats.right_reads>0,"cache_closure")?;
        *stage="custody";mark(stage,completed,elapsed(start)?)?;
        raw_hash(&raw)?;packed_hash(&mut held)?;
        require(u0_file_info(&raw).map_err(|_|fail("raw_identity",0,0,0))?==raw_identity,"raw_custody")?;
        let raw_check=OpenOptions::new().read(true).share_mode(1).open(raw_path).map_err(|_|fail("raw_reopen",0,0,0))?;
        require(u0_file_info(&raw_check).map_err(|_|fail("raw_identity",0,0,0))?==raw_identity,"raw_path_custody")?;
        let check=u0_open_bytes(&path).map_err(|_|fail("packed_reopen",0,0,0))?;
        require(u0_file_info(&held).map_err(|_|fail("packed_identity",0,0,0))?==identity&&
            u0_file_info(&check).map_err(|_|fail("packed_identity",0,0,0))?==identity,"packed_custody")?;
        view.require_same_source(&source).map_err(|_|fail("same_source",0,0,0))?;checks.custody_unchanged=true;
        let members:[Member<'_>;MEMBERS]=std::array::from_fn(|tag|Member{tag,name:&plan.descriptors()[2].ordered_tags[tag],stride_log:strides[tag],
            expected_terms:expected[tag].terms,expected_rows:expected[tag].rows,observed_terms:observed[tag].terms,observed_rows:observed[tag].rows});
        let ns=elapsed(start)?;
        let report=Report{schema:"native-role2-residual-diagnostic-v1",state:"ROLE2_NATIVE_RESIDUAL_PASS",stage:"complete",error:None,
            scope:Scope{input_log:32,row_log:32,owners:4096,active_headers:3073,members:40,residual_only:true,gkr:false,pcs:false,
                all_seven_roles:false,production:false,deadline_seconds:300,auxiliary_limit_bytes:AUX},
            inputs:Inputs{raw_sha256:RAW_SHA,witness_sha256:WITNESS_SHA,witness_blake2b256:WITNESS_BLAKE},
            members:&members,completed_slots:completed,canonical_terms:terms,occupied_rows,cache:stats,checks,elapsed_ns:ns};
        let mut writer=Bounded::new()?;serde_json::to_writer(&mut writer,&report).map_err(|_|fail("report_encode",0,0,0))?;
        elapsed(start)?;*stage="complete";mark(stage,completed,ns)?;Ok(writer.bytes)
    }
    #[test]
    pub(super) fn ordinary_boundaries(){
        ordinary().unwrap(); // Pure negatives and their buffers close before the count-only parent.
        let parent=WorkTreeHistoryPlan::compile(3073,12,[0;32],[0;28]).unwrap();
        let candidate=Candidate{n:3073,root:[0;32],total:[0;28],tip:[0;32],tip_time:0};
        let plan=NativePrefixAuthPlan::compile(&parent,Selection::s12(),candidate).unwrap();
        let (counts,strides)=expectations(&parent,&plan).unwrap();
        let members:[CountMember<'_>;MEMBERS]=std::array::from_fn(|tag|CountMember{
            tag,name:&plan.descriptors()[2].ordered_tags[tag],stride_log:strides[tag],terms:counts[tag].terms,rows:counts[tag].rows});
        let report=CountReport{schema:"native-role2-counts-v1",state:"COUNT_APIS_PASS",input_log:32,row_log:32,owners:4096,
            active_headers:3073,count_only:true,native_inputs:false,members:&members,canonical_terms:129277400,occupied_rows:76211168};
        let mut writer=Bounded::new().unwrap();serde_json::to_writer(&mut writer,&report).unwrap();
        let mut out=std::io::stdout().lock();out.write_all(b"\nNATIVE_ROLE2_COUNTS_REPORT ").unwrap();
        out.write_all(&writer.bytes).unwrap();out.write_all(b"\n").unwrap();out.flush().unwrap();
    }
    #[test]
    #[ignore="canonical native role2 residuals only; reviewed300s/Job2GiB/Rayon4 controller required"]
    fn native_role2_residuals_bounded(){
        let start=Instant::now();let mut stage="admission";
        let result=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||execute(start,&mut stage)))
            .unwrap_or_else(|_|Err(fail("panic",0,0,0)));
        let bytes=match &result {Ok(bytes)=>bytes.clone(),Err(error)=>{
            let _=mark("hold",error.slot,screen_ns(start));
            serde_json::to_vec(&serde_json::json!({"schema":"native-role2-residual-diagnostic-v1","state":"HOLD", "stage":stage,"error":error}))
                .expect("bounded HOLD report")}};
        assert!(bytes.len()<=REPORT_CAP);
        let mut out=std::io::stdout().lock();out.write_all(b"\nNATIVE_ROLE2_RESIDUAL_REPORT ").unwrap();
        out.write_all(&bytes).unwrap();out.write_all(b"\n").unwrap();out.flush().unwrap();drop(out);
        assert!(result.is_ok(),"native role2 residual HOLD");
    }
}



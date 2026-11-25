//! Private source plan, without MAX, proof admission or an authenticated receipt.
pub(crate) use crate::checkpoint_role4_internal::{check_term, composite_coefficients,
    composite_height_mask, visit_composite_owner, HistoricalRole4Endpoints, HistoricalRole4Counts};
#[cfg(test)]
pub(crate) use native_role5_common::NativeRole5DiagnosticContext;
#[cfg(test)]
pub(crate) use native_role5_common::{NativeRole5Admission,NativeRole5Mark,emit_role5_mark};
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use crate::{daa_history_roster::DaaHistoryRoster,
    gkr::{GkrProof, InputClaim},
    header_adjacency_layout::HeaderAdjacencyLayout,
    header_metadata_order_layout::HeaderMetadataOrderLayout,
    historical_prefix_height_work::HeightWork, point_membership,
    sparse::{self, Shape, Term}, transcript::Transcript,
    work_tree_fixed_hash as fixed, work_tree_history_plan::WorkTreeHistoryPlan,
    work_tree_layout as layout, work_tree_wiring};

/// Private role5 diagnostic framing, consumers and computed source capability.
/// This admits an exact held fixture, not a PCS opening or a production proof.
#[cfg(test)]
mod native_role5_common {
    use super::*;

    pub(crate) struct NativeRole5DiagnosticContext {
        artifacts: NativeRole0DiagnosticContext,
    }

    impl NativeRole5DiagnosticContext {
        const DOMAIN: &'static [u8] = b"native-prefix-role5-diagnostic-proof-v1";

        pub(crate) fn admit(key: &[u8], commitment: &[u8]) -> Result<Self, String> {
            Ok(Self { artifacts: NativeRole0DiagnosticContext::admit(key, commitment)? })
        }

        pub(crate) fn admit_with_setup_id(key: &[u8], commitment: &[u8], setup: [u8;32])
            -> Result<Self, String>
        {
            Ok(Self { artifacts: NativeRole0DiagnosticContext::admit_with_setup_id(key, commitment, setup)? })
        }
        pub(super) fn from_admitted_artifacts(artifacts:NativeRole0DiagnosticContext)->Self{Self{artifacts}}

        pub(crate) fn transcript(&self) -> Transcript { Transcript::new(Self::DOMAIN) }
        pub(crate) fn setup_id_for_report(&self) -> [u8;32] { self.artifacts.setup_id_for_report() }
        pub(crate) fn key_sha256_for_report(&self) -> [u8;32] { self.artifacts.key_sha256_for_report() }
        pub(crate) fn commitment_sha256_for_report(&self) -> [u8;32] {
            self.artifacts.commitment_sha256_for_report()
        }
    }

    fn require_roster(descriptors: &[Descriptor;7]) -> Result<(), String> {
        if descriptors.iter().enumerate().any(|(role,d)| d.role != role
            || d.name != NAMES[role] || d.source != SOURCE
            || d.input_log != INPUT_LOGS[role] || d.row_log != ROW_LOGS[role])
        {
            return Err("native role5 complete descriptor roster identity".into());
        }
        let d=&descriptors[5];
        if d.ordered_tags.len()!=1 || d.ordered_tags[0]!=NAMES[5]
            || d.mapping != "active owner row9; terminal tip" || d.zero_extension.is_some()
            || d.public_dependency != "genesis-parent-zero/candidate-tip"
        {
            return Err("native role5 canonical descriptor fields".into());
        }
        Ok(())
    }

    fn require_layout(adjacency: &HeaderAdjacencyLayout, tip: &[u8;32]) -> Result<(), String> {
        if adjacency.n()!=N || adjacency.slot_log()!=H || adjacency.input_log()!=32
            || adjacency.row_log()!=21 || adjacency.input_len()!=1usize<<32
            || adjacency.row_count()!=1usize<<21 || adjacency.term_count()!=786_944
        {
            return Err("native role5 canonical adjacency geometry".into());
        }
        // Maps/profile are compiler-owned and immutable. Check the public
        // endpoints against the actual emitted gates without a full term sweep.
        let genesis=adjacency.visit_slot_terms(0, |row,gate| {
            if row>=256 || gate.right!=0 || !gate.c0.is_zero()
                || gate.c1!=Fr::one() || !gate.c2.is_zero() || !gate.c3.is_zero()
            { return Err("native role5 genesis endpoint differs".into()); }
            Ok(())
        })?;
        let mut terminal=0usize;
        let last=adjacency.visit_slot_terms(N-1, |row,gate| {
            let local=row.checked_sub((N as usize-1)<<9).ok_or("native role5 terminal row underflow")?;
            if local>=256 {
                let bit=local-256;
                if bit>=256 || gate.right!=0 || gate.c1!=Fr::one()
                    || !gate.c2.is_zero() || !gate.c3.is_zero()
                    || gate.c0 != -Fr::from(((tip[bit/8]>>(bit%8))&1) as u64)
                { return Err("native role5 candidate tip endpoint differs".into()); }
                terminal+=1;
            }
            Ok(())
        })?;
        if (genesis,last,terminal)!=(256,512,256) {
            return Err("native role5 endpoint census differs".into());
        }
        Ok(())
    }

    fn append_descriptor(t: &mut Transcript, d: &Descriptor) {
        t.append_bytes(b"native-role5-descriptor",d.name.as_bytes());
        t.append_bytes(b"native-role5-source",d.source.as_bytes());
        t.append_u64(b"native-role5-role-index",5);
        t.append_u64(b"native-role5-input-log",32);
        t.append_u64(b"native-role5-output-log",21);
    }

    fn prepare_binding(t: &Transcript, bind: impl FnOnce(&mut Transcript)->Result<(),String>)
        -> Result<Transcript,String>
    {
        if t.challenges()!=0 { return Err("native role5 binding after challenge".into()); }
        let mut prepared=t.clone();
        bind(&mut prepared)?;
        if prepared.challenges()!=0 {
            return Err("native role5 binder sampled a challenge".into());
        }
        Ok(prepared)
    }

    fn require_mle_shape(source_len: usize, claim: &InputClaim) -> Result<(),String> {
        if source_len!=1usize<<32 || claim.point.len()!=32 {
            return Err("native role5 full-coordinate source MLE shape".into());
        }
        Ok(())
    }

    impl NativePrefixAuthPlan<'_> {
        pub(crate) fn require_role5_native_plan(&self) -> Result<(),String> {
            self.selection.validate()?;
            require_roster(&self.descriptors)?;
            if self.parent.headers()!=N || self.parent.slot_log()!=H || self.parent.slots()!=4096
                || self.candidate.n!=N || self.candidate.root!=self.parent.descriptor().root
                || self.candidate.total!=self.parent.work_profile().total_be28
            { return Err("native role5 borrowed parent/candidate identity".into()); }
            if self.parent.fixed_profile().genesis!=self.selection.genesis
                || self.parent.fixed_profile().prefix.as_slice()!=fixed::PROFILE_PREFIX
            { return Err("native role5 parent source profile".into()); }
            require_layout(&self.adjacency,&self.candidate.tip)
        }

        pub(crate) fn prepare_role5_binding_for_test(&self,t:&Transcript,
            context:&NativeRole5DiagnosticContext) -> Result<Transcript,String>
        {
            prepare_binding(t, |prepared| {
                self.require_role5_native_plan()?;
                context.artifacts.validate()?;
                context.artifacts.bind_admission(prepared)?;
                append_descriptor(prepared,&self.descriptors[5]);
                self.bind_plan_identity(prepared)
            })
        }

        /// Verifies the relation statement; this does not authenticate a witness
        /// file or provide the common PCS opening. Domain creation stays here.
        pub(crate) fn verify_role5_for_test(&self,proof:&GkrProof,
            context:&NativeRole5DiagnosticContext) -> Result<(InputClaim,Transcript),String>
        {
            let mut transcript=context.transcript();
            let prepared=self.prepare_role5_binding_for_test(&transcript,context)?;
            // verify_with_wiring validates proof lengths, then calls this unit
            // binder before its first append/challenge. Installation loses no prefix.
            let claim=crate::gkr::verify_with_wiring(&[32],1usize<<21,proof,&mut transcript,
                move |t| *t=prepared,
                |layer,r,u,v| {
                    if layer!=0 { return Err(crate::gkr::GkrError::PointDimension); }
                    self.coefficients(5,r,u,v).map_err(|_|crate::gkr::GkrError::PointDimension)
                }).map_err(|error|error.to_string())?;
            Ok((claim,transcript))
        }

        /// Equality on a supplied immutable handle only. The future native
        /// harness must first establish its admitted digest and held-file custody.
        pub(crate) fn check_role5_source_mle_for_test(&self,source:&crate::packed::PackedFile,
            claim:&InputClaim) -> Result<(),String>
        {
            self.require_role5_native_plan()?;
            require_mle_shape(source.input_len(),claim)?;
            if source.evaluate(&claim.point)?!=claim.value {
                return Err("native role5 held-source MLE differs from claim".into());
            }
            Ok(())
        }
    }

    const ROLE5_JSON_LIMIT: usize = 8 * 1024 * 1024;
    const ROLE5_BINDING_OVERLAP: usize = 32 * 1024 * 1024;
    const ROLE5_OWNER_BYTES: usize = 131072;
    const ROLE5_WITNESS_BLAKE: [u8;32] = [
        0x72,0x5d,0x7b,0x12,0x15,0xe1,0x18,0x5c,0x52,0xc1,0x01,0x2d,0x92,0x94,0x26,0x06,
        0x12,0x65,0x3a,0xca,0xd5,0x3a,0x02,0x42,0x9b,0x8e,0xaa,0xfd,0x0f,0x07,0x70,0xc8,
    ];

    struct JsonCounter { bytes: usize, limit: usize }
    impl std::io::Write for JsonCounter {
        fn write(&mut self, bytes:&[u8])->std::io::Result<usize>{
            let next=self.bytes.checked_add(bytes.len()).ok_or_else(||std::io::Error::other("role5 JSON count overflow"))?;
            if next>self.limit{return Err(std::io::Error::other("role5 JSON object exceeds8MiB"));}
            self.bytes=next;Ok(bytes.len())
        }
        fn flush(&mut self)->std::io::Result<()>{Ok(())}
    }
    fn count_json<T:serde::Serialize>(value:&T)->Result<usize,String>{
        let mut counter=JsonCounter{bytes:0,limit:ROLE5_JSON_LIMIT};
        serde_json::to_writer(&mut counter,value).map_err(|e|e.to_string())?;Ok(counter.bytes)
    }
    pub(super) fn binding_json_preflight(plan:&NativePrefixAuthPlan<'_>)->Result<[usize;5],String>{
        let topology=plan.parent.topology();
        // Count the EXACT tuple used by Topology::validate, before that method
        // or full_roster_shape can allocate its serialization.
        Ok([count_json(&(&topology.descriptor,&topology.families))?,
            count_json(&topology.descriptor)?,count_json(plan.parent.fixed_profile())?,
            count_json(plan.parent.leaf_profile())?,count_json(plan.parent.work_profile())?])
    }
    pub(super) fn compare_reference<R:std::io::Read+std::io::Seek>(reference:&mut R,owners:usize,
        mut compare:impl FnMut(usize,&[u8])->Result<(),String>)->Result<[u8;32],String>{
        use blake2::{Blake2b,Digest,digest::consts::U32};
        use std::io::SeekFrom;
        if owners==0||owners>4096{return Err("role5 reference owner bound".into());}
        let expected=owners.checked_mul(ROLE5_OWNER_BYTES).ok_or("role5 reference extent overflow")?;
        if reference.seek(SeekFrom::End(0)).map_err(|e|e.to_string())?!=expected as u64{
            return Err("role5 reference exact extent".into());
        }
        reference.seek(SeekFrom::Start(0)).map_err(|e|e.to_string())?;
        let mut bytes=Vec::new();bytes.try_reserve_exact(ROLE5_OWNER_BYTES).map_err(|e|e.to_string())?;
        if bytes.capacity()!=ROLE5_OWNER_BYTES{return Err("role5 reference buffer capacity".into());}
        bytes.resize(ROLE5_OWNER_BYTES,0);let mut hash=Blake2b::<U32>::new();
        for owner in 0..owners{
            reference.read_exact(&mut bytes).map_err(|e|e.to_string())?;
            compare(owner,&bytes)?;hash.update(&bytes);
        }
        let mut tail=[0u8;1];
        if reference.read(&mut tail).map_err(|e|e.to_string())?!=0{return Err("role5 reference trailing bytes".into());}
        let digest=hash.finalize();let mut out=[0u8;32];out.copy_from_slice(&digest);Ok(out)
    }
    pub(super) fn require_witness_digest(digest:[u8;32])->Result<(),String>{
        if digest!=ROLE5_WITNESS_BLAKE{return Err("role5 fixed native witness BLAKE2b256".into());}Ok(())
    }

    #[derive(Clone,Copy,Debug,serde::Serialize)]
    pub(crate) struct NativeRole5Mark {pub(crate) stage:&'static str,pub(crate) round:Option<usize>,pub(crate) elapsed_ns:u64}
    const EMPTY_MARK:NativeRole5Mark=NativeRole5Mark{stage:"",round:None,elapsed_ns:0};

    /// Immutable source/plan association. Only the plan factory below can mint
    /// this token; neither a caller callback nor a descriptor admits native32.
    pub(crate) struct NativeRole5Admission<'p,'s> {
        plan:&'p NativePrefixAuthPlan<'s>,source:&'p crate::packed::PackedFile,
        context:&'p NativeRole5DiagnosticContext,json_bytes:[usize;5],
        started:std::time::Instant,marks:std::cell::RefCell<[NativeRole5Mark;67]>,
        completed:std::cell::Cell<usize>,
    }
    impl<'s> NativePrefixAuthPlan<'s> {
        pub(crate) fn admit_role5_linear_for_test<'p,R:std::io::Read+std::io::Seek>(
            &'p self,source:&'p crate::packed::PackedFile,context:&'p NativeRole5DiagnosticContext,
            reference:&mut R)->Result<NativeRole5Admission<'p,'s>,String>{
            let started=std::time::Instant::now();
            self.require_role5_native_plan()?;context.artifacts.validate()?;
            let view=source.native_role0_view()?;view.require_same_source(source)?;
            let json_bytes=binding_json_preflight(self)?;
            let digest=compare_reference(reference,4096,|owner,expected|{
                let actual=view.read_copy(owner)?;
                if actual.len()!=1usize<<20||actual.capacity_bytes()!=ROLE5_OWNER_BYTES||!actual.matches_bytes(expected){
                    return Err("role5 original packed handle differs from reference".into());
                }Ok(())
            })?;
            require_witness_digest(digest)?;
            Ok(NativeRole5Admission{plan:self,source,context,json_bytes,started,
                marks:std::cell::RefCell::new([EMPTY_MARK;67]),completed:std::cell::Cell::new(0)})
        }
    }
    impl NativeRole5Admission<'_, '_> {
        pub(crate) fn require_layout(&self,layout:&HeaderAdjacencyLayout)->Result<(),String>{
            if !std::ptr::eq(layout,&self.plan.adjacency){return Err("role5 foreign layout capability".into());}
            self.plan.require_role5_native_plan()?;self.context.artifacts.validate()?;
            self.source.native_role0_view()?.require_same_source(self.source)
        }
        pub(crate) fn descriptor(&self)->Result<crate::header_adjacency_layout::linear_for_test::Descriptor<'_>,String>{
            self.plan.adjacency.native_role5_descriptor_for_test(self)
        }
        pub(crate) fn load_chunk(&self,chunk:usize)->Result<Vec<Fr>,String>{
            if self.source.input_len()!=1usize<<32||chunk>=65536{return Err("role5 fixed chunk loader bound".into());}
            self.source.read_copy(65536,chunk)
        }
        pub(crate) fn prepare_binding(&self,t:&Transcript)->Result<Transcript,String>{
            self.require_layout(&self.plan.adjacency)?;
            // Immutable borrowed objects were counted before admission; their
            // JSON cannot change between the preflight and this exact binder.
            self.plan.prepare_role5_binding_for_test(t,self.context)
        }
        pub(crate) fn fixed_retained_capacity_bytes(&self)->Result<usize,String>{
            // Conservative overlap also covers both admission byte buffers and
            // packed read_copy's8192B scratch. Parent/context heaps are external.
            ROLE5_BINDING_OVERLAP.checked_add(2*ROLE5_OWNER_BYTES).and_then(|x|x.checked_add(8192))
                .and_then(|x|x.checked_add(std::mem::size_of_val(self))).ok_or("role5 capability inventory overflow".into())
        }
        pub(crate) fn json_bytes_for_report(&self)->[usize;5]{self.json_bytes}
        pub(crate) fn check_source_mle(&self,claim:&InputClaim)->Result<(),String>{
            self.plan.check_role5_source_mle_for_test(self.source,claim)
        }
        pub(crate) fn elapsed_ns(&self)->Result<u64,String>{
            u64::try_from(self.started.elapsed().as_nanos()).map_err(|_|"role5 clock overflow".into())
        }
        pub(crate) fn marks_for_report(&self)->Result<[NativeRole5Mark;67],String>{
            if self.completed.get()!=67{return Err("role5 incomplete producer marks".into());}Ok(*self.marks.borrow())
        }
        pub(crate) fn progress(&self,event:crate::segment_adjacency::linear_for_test::Native5Progress)->Result<(),String>{
            use crate::segment_adjacency::linear_for_test::{Native5Progress as E,Native5Side as S};
            let index=self.completed.get();
            let (expected,stage,round)=match index{
                0=>(E::ValidationComplete,"validation",None),
                1..=32=>(E::Round{side:S::U,completed:index},"u",Some(index)),
                33..=64=>(E::Round{side:S::V,completed:index-32},"v",Some(index-32)),
                65=>(E::LineComplete,"line",None),66=>(E::ProducerComplete,"producer_complete",None),
                _=>return Err("role5 progress extent".into()),
            };
            if event!=expected{return Err("role5 progress order".into());}
            let mark=NativeRole5Mark{stage,round,elapsed_ns:self.elapsed_ns()?};
            emit_role5_mark(mark)?;self.marks.borrow_mut()[index]=mark;self.completed.set(index+1);Ok(())
        }
    }
    pub(crate) fn emit_role5_mark(mark:NativeRole5Mark)->Result<(),String>{
        use std::io::Write;
        let bytes=serde_json::to_vec(&mark).map_err(|e|e.to_string())?;
        if bytes.len()>220{return Err("role5 progress byte cap".into());}
        let mut out=std::io::stdout().lock();out.write_all(b"R5_NATIVE_PHASE ").map_err(|e|e.to_string())?;
        out.write_all(&bytes).map_err(|e|e.to_string())?;out.write_all(b"\n").map_err(|e|e.to_string())?;
        out.flush().map_err(|e|e.to_string())
    }

    impl NativePrefixAuthPlan<'_> {
        /// Eight isolated verifier-prefix faults. This does not mint a source
        /// capability or expose a producer binder replacement.
        pub(crate) fn verify_role5_fault_for_test(&self,proof:&GkrProof,
            context:&NativeRole5DiagnosticContext,fault:usize)->Result<(),String>{
            if fault>=8{return Err("role5 verifier fault ordinal".into());}
            self.require_role5_native_plan()?;context.artifacts.validate()?;
            binding_json_preflight(self)?;
            let mut t=if fault==7{Transcript::new(b"native-prefix-role0-diagnostic-proof-v1")}
                else{context.transcript()};
            let prepared=prepare_binding(&t,|p|{
                if fault==3{self.bind_plan_identity(p)?;}
                if fault!=0{context.artifacts.bind_admission(p)?;}
                if fault!=2{
                    let d=&self.descriptors[5];
                    p.append_bytes(b"native-role5-descriptor",d.name.as_bytes());
                    p.append_bytes(b"native-role5-source",d.source.as_bytes());
                    p.append_u64(b"native-role5-role-index",if fault==4{4}else{5});
                    p.append_u64(b"native-role5-input-log",if fault==5{31}else{32});
                    p.append_u64(b"native-role5-output-log",if fault==6{20}else{21});
                }
                if fault!=1&&fault!=3{self.bind_plan_identity(p)?;}Ok(())
            })?;
            crate::gkr::verify_with_wiring(&[32],1usize<<21,proof,&mut t,move|t|*t=prepared,
                |layer,r,u,v|if layer==0{self.coefficients(5,r,u,v).map_err(|_|crate::gkr::GkrError::PointDimension)}
                else{Err(crate::gkr::GkrError::PointDimension)}).map_err(|e|e.to_string())?;Ok(())
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn role5_native_json_and_reference_preflights_are_closed(){
            use std::io::{Cursor,Write,Read,Seek,SeekFrom};
            let value=(&[1usize,2,3],"native");
            assert_eq!(count_json(&value).unwrap(),serde_json::to_vec(&value).unwrap().len());
            let exact="x".repeat(ROLE5_JSON_LIMIT-2);
            assert_eq!(count_json(&exact).unwrap(),ROLE5_JSON_LIMIT);
            assert!(count_json(&(exact+"x")).is_err());
            let mut overflow=JsonCounter{bytes:usize::MAX,limit:usize::MAX};
            assert!(overflow.write_all(&[0]).is_err());
            let bytes=vec![0xA5;ROLE5_OWNER_BYTES];let mut calls=0;
            let digest=compare_reference(&mut Cursor::new(&bytes),1,|owner,actual|{
                assert_eq!(owner,0);assert_eq!(actual,bytes);calls+=1;Ok(())
            }).unwrap();assert_eq!(calls,1);assert!(require_witness_digest(digest).is_err());
            assert!(require_witness_digest(ROLE5_WITNESS_BLAKE).is_ok());
            assert!(compare_reference(&mut Cursor::new(&bytes[..bytes.len()-1]),1,|_,_|panic!("short extent before comparison")).is_err());
            for at in [0,65536,ROLE5_OWNER_BYTES-1]{
                assert!(compare_reference(&mut Cursor::new(&bytes),1,|_,actual|{
                    let mut expected=bytes.clone();expected[at]^=1;
                    if actual!=expected{return Err("one changed byte".into());}Ok(())
                }).is_err());
            }
            struct HiddenTail(Cursor<Vec<u8>>);
            impl Read for HiddenTail{fn read(&mut self,out:&mut[u8])->std::io::Result<usize>{self.0.read(out)}}
            impl Seek for HiddenTail{fn seek(&mut self,p:SeekFrom)->std::io::Result<u64>{
                if p==SeekFrom::End(0){Ok(ROLE5_OWNER_BYTES as u64)}else{self.0.seek(p)}
            }}
            let mut trailing=bytes.clone();trailing.push(0);
            assert!(compare_reference(&mut HiddenTail(Cursor::new(trailing)),1,|_,_|Ok(())).is_err());
            struct FailedRead(Cursor<Vec<u8>>);
            impl Read for FailedRead{fn read(&mut self,_:&mut[u8])->std::io::Result<usize>{Err(std::io::Error::other("isolated transport read"))}}
            impl Seek for FailedRead{fn seek(&mut self,p:SeekFrom)->std::io::Result<u64>{self.0.seek(p)}}
            assert!(compare_reference(&mut FailedRead(Cursor::new(bytes)),1,|_,_|panic!("read error before comparison")).is_err());
            for owners in [0,4097,usize::MAX]{
                assert!(compare_reference(&mut Cursor::new(Vec::<u8>::new()),owners,|_,_|panic!("owner bound before comparison")).is_err());
            }
        }

        fn descriptors() -> [Descriptor;7] {
            std::array::from_fn(|role| Descriptor { role,name:NAMES[role],source:SOURCE,
                input_log:INPUT_LOGS[role],row_log:ROW_LOGS[role],
                ordered_tags:vec![NAMES[role].to_owned()],zero_extension:None,
                mapping:if role==5 {"active owner row9; terminal tip"} else {"fixture"},
                public_dependency:if role==5 {"genesis-parent-zero/candidate-tip"} else {"fixture"} })
        }

        fn fingerprint(t:&Transcript) -> ([u64;3],Fr) {
            ([t.challenges(),t.raw_queries(),t.bytes_absorbed()],
                t.clone().challenge_scalar(b"native-role5-common-control"))
        }

        #[test]
        fn role5_native_layout_and_descriptor_identity_are_closed() {
            let base=descriptors();require_roster(&base).unwrap();
            for role in 0..7 {
                for field in 0..5 {
                    let mut bad=base.clone();
                    match field {0=>bad[role].role=(role+1)%7,1=>bad[role].name="wrong",
                        2=>bad[role].source="wrong",3=>bad[role].input_log+=1,_=>bad[role].row_log+=1}
                    assert!(require_roster(&bad).is_err());
                }
            }
            for field in 0..4 {
                let mut bad=base.clone();
                match field {0=>bad[5].ordered_tags.push("extra".into()),1=>bad[5].mapping="wrong",
                    2=>bad[5].zero_extension=Some((18,31)),_=>bad[5].public_dependency="wrong"}
                assert!(require_roster(&bad).is_err());
            }
            let mut swapped=base.clone();swapped.swap(4,5);assert!(require_roster(&swapped).is_err());
            let tip=[0x96;32];let layout=HeaderAdjacencyLayout::compile(N,H,[0;32],tip).unwrap();
            require_layout(&layout,&tip).unwrap();
            let mut wrong_tip=tip;wrong_tip[0]^=1;
            assert!(require_layout(&layout,&wrong_tip).is_err());
            let wrong_start=HeaderAdjacencyLayout::compile(N,H,[1;32],tip).unwrap();
            assert!(require_layout(&wrong_start,&tip).is_err());
            let wrong_n=HeaderAdjacencyLayout::compile(N-1,H,[0;32],tip).unwrap();
            assert!(require_layout(&wrong_n,&tip).is_err());
            let metadata=HeaderAdjacencyLayout::compile_metadata(N,H,0).unwrap();
            assert!(require_layout(&metadata,&tip).is_err());
        }

        #[test]
        fn role5_native_prepared_binding_preserves_prefix_and_errors() {
            let mut caller=Transcript::new(NativeRole5DiagnosticContext::DOMAIN);
            caller.append_bytes(b"existing-prefix",b"retained verbatim");
            let before=fingerprint(&caller);let d=descriptors();
            // These are framing fixtures, not admitted artifact or native-source authority.
            let bind=|t:&mut Transcript| {
                t.append_bytes(b"fixture-artifact-admission",b"artifact");
                append_descriptor(t,&d[5]);
                t.append_bytes(b"fixture-full-plan",b"plan");Ok(())
            };
            let prepared=prepare_binding(&caller,bind).unwrap();
            assert_eq!(fingerprint(&caller),before);
            let mut direct=caller.clone();bind(&mut direct).unwrap();
            let install=move |t:&mut Transcript| *t=prepared;
            let mut installed=caller.clone();install(&mut installed);
            assert_eq!(fingerprint(&installed),fingerprint(&direct));
            assert_ne!(fingerprint(&installed),before);
            let failed=prepare_binding(&caller,|t| {
                t.append_bytes(b"partial-bind",b"never committed");Err("isolated binder failure".into())
            });
            assert!(failed.is_err());assert_eq!(fingerprint(&caller),before);
            assert!(prepare_binding(&caller,|t|{t.challenge_scalar(b"forbidden");Ok(())}).is_err());
            assert_eq!(fingerprint(&caller),before);
            caller.challenge_scalar(b"already challenged");let late=fingerprint(&caller);
            let calls=std::cell::Cell::new(0);
            assert!(prepare_binding(&caller,|_|{calls.set(calls.get()+1);Ok(())}).is_err());
            assert_eq!(calls.get(),0);assert_eq!(fingerprint(&caller),late);
            for domain in [NativeRole0DiagnosticContext::DOMAIN,
                b"native-prefix-role1-diagnostic-proof-v1".as_slice(),
                b"native-prefix-source-plan-identity-only-v1".as_slice()]
            {
                assert_ne!(fingerprint(&Transcript::new(NativeRole5DiagnosticContext::DOMAIN)).1,
                    fingerprint(&Transcript::new(domain)).1);
            }
        }

        #[test]
        fn role5_native_artifact_extents_and_mle_dimensions_are_closed() {
            let key=vec![0u8;33_264];let commitment=vec![0u8;384];
            for (key_len,commitment_len,setup) in [(33_263,384,NativeRole0DiagnosticContext::SETUP_ID),
                (33_264,383,NativeRole0DiagnosticContext::SETUP_ID),(33_264,384,[0;32])]
            {
                let error=NativeRole5DiagnosticContext::admit_with_setup_id(
                    &key[..key_len],&commitment[..commitment_len],setup).err().unwrap();
                assert!(error.contains("artifact extent/setup identity"));
            }
            let claim=InputClaim {point:vec![Fr::from(2u64);32],value:Fr::zero()};
            require_mle_shape(1usize<<32,&claim).unwrap();
            assert!(require_mle_shape(1usize<<31,&claim).is_err());
            let mut short=claim.clone();short.point.pop();
            assert!(require_mle_shape(1usize<<32,&short).is_err());
            let mut long=claim.clone();long.point.push(Fr::one());
            assert!(require_mle_shape(1usize<<32,&long).is_err());
        }
    }
}

pub(crate) const N: u64 = 3073;
pub(crate) const H: usize = 12;
pub(crate) const INPUT_LOGS: [usize; 7] = [32,32,32,25,32,32,32];
pub(crate) const ROW_LOGS: [usize; 7] = [33,31,32,26,32,21,24];
const NAMES: [&str; 7] = ["corepool11", "retained-header", "worktree-roster",
    "point-membership", "height-work-and-daa-roster-v2", "header-id", "metadata-order"];
const SOURCE: &str = "8995ff243b140e7fe716bd3204423dd35690c2e4";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SourceRevision { Ergo8995ff, Unsupported }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Rules { NativePrefixEll2NoMax, Unsupported }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Verifier { SourcePlanOnly, Unsupported }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Encoding { CanonicalNativeRaw, Unsupported }
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Selection {
    pub(crate) source: SourceRevision, pub(crate) rules: Rules,
    pub(crate) genesis: [u8;32], pub(crate) query_h: u64, pub(crate) ell: u64,
    pub(crate) verifier: Verifier, pub(crate) encoding: Encoding,
    pub(crate) slot_log: usize, pub(crate) point_bank: usize,
}
impl Selection {
    pub(crate) fn s12() -> Self { Self { source: SourceRevision::Ergo8995ff,
        rules: Rules::NativePrefixEll2NoMax, genesis: crate::header_order::MAINNET_GENESIS,
        query_h: N, ell: 2, verifier: Verifier::SourcePlanOnly,
        encoding: Encoding::CanonicalNativeRaw, slot_log: H, point_bank: 96 } }
    pub(crate) fn validate(&self) -> Result<(),String> {
        if *self != Self::s12() { return Err("unsupported closed native prefix selection".into()); }
        Ok(())
    }
}
/// Untrusted output claims, fixed before future challenges. Not a recent-root oracle.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Candidate {
    pub(crate) n: u64, pub(crate) root: [u8;32], pub(crate) total: [u8;28],
    pub(crate) tip: [u8;32], pub(crate) tip_time: i64,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Descriptor {
    pub(crate) role: usize, pub(crate) name: &'static str,
    pub(crate) source: &'static str, pub(crate) input_log: usize, pub(crate) row_log: usize,
    pub(crate) ordered_tags: Vec<String>, pub(crate) mapping: &'static str,
    pub(crate) zero_extension: Option<(usize,usize)>,
    pub(crate) public_dependency: &'static str,
}

#[cfg(test)]
pub(crate) struct NativeRole0DiagnosticContext {
    key: crate::verifier_key::AdmittedVerifierKey,
    key_sha256: [u8; 32],
    setup_id: [u8; 32],
    commitment: Vec<u8>,
    commitment_sha256: [u8; 32],
}

#[cfg(test)]
impl NativeRole0DiagnosticContext {
    const DOMAIN: &'static [u8] = b"native-prefix-role0-diagnostic-proof-v1";
    const KEY_SHA256: [u8; 32] = [
        0xd1,0x12,0x20,0xa1,0xcb,0xb0,0x8b,0xe2,0xc8,0x4f,0x6b,0x85,0x4e,0xc2,0xa9,0x32,
        0xb3,0xfc,0xec,0x49,0xc2,0x17,0x96,0x3d,0x07,0x9d,0xd8,0x05,0x3f,0x7b,0x31,0xb2,
    ];
    const SETUP_ID: [u8; 32] = [
        0x1a,0xe7,0xba,0xdc,0x1e,0x52,0x9c,0x7a,0x5c,0xda,0x70,0x9a,0xd1,0xb4,0x18,0xaf,
        0x6a,0xe2,0xef,0xb6,0xb7,0xb4,0xd9,0x09,0x81,0x6d,0x09,0x1c,0x32,0x60,0xa5,0x1b,
    ];
    const COMMITMENT_SHA256: [u8; 32] = [
        0x27,0x39,0xa3,0x35,0x3d,0x57,0x9a,0x7f,0xa0,0xf1,0x9b,0x06,0xef,0xdd,0x26,0xa6,
        0x25,0xcd,0xb8,0x00,0x09,0xc6,0x57,0x07,0xd8,0xb9,0x6e,0x7d,0x8c,0x0c,0x9c,0x90,
    ];

    pub(crate) fn admit(key_bytes: &[u8], commitment_bytes: &[u8]) -> Result<Self, String> {
        Self::admit_with_setup_id(key_bytes, commitment_bytes, Self::SETUP_ID)
    }

    pub(crate) fn admit_with_setup_id(
        key_bytes: &[u8], commitment_bytes: &[u8], setup_id: [u8; 32],
    ) -> Result<Self, String> {
        if key_bytes.len() != 33_264 || commitment_bytes.len() != 384 || setup_id != Self::SETUP_ID {
            return Err("native role0 admitted artifact extent/setup identity".into());
        }
        let key_sha256 = role0_sha256(key_bytes)?;
        if key_sha256 != Self::KEY_SHA256 {
            return Err("native role0 code-owned verifier-key SHA-256 mismatch".into());
        }
        let key = crate::verifier_key::admit_generated_test_key(32, key_bytes, setup_id)?;
        if key.log_n() != 32 || key.id() != &setup_id {
            return Err("native role0 admitted verifier-key identity mismatch".into());
        }
        let decoded = crate::pcs::decode_commitment(commitment_bytes)?;
        if crate::pcs::encode_commitment(&decoded)? != commitment_bytes {
            return Err("native role0 commitment is not canonical".into());
        }
        let commitment_sha256 = role0_sha256(commitment_bytes)?;
        if commitment_sha256 != Self::COMMITMENT_SHA256 {
            return Err("native role0 code-owned commitment SHA-256 mismatch".into());
        }
        Ok(Self { key, key_sha256, setup_id, commitment: commitment_bytes.to_vec(), commitment_sha256 })
    }

    pub(crate) fn transcript(&self) -> Transcript { Transcript::new(Self::DOMAIN) }
    pub(crate) fn setup_id_for_report(&self) -> [u8; 32] { self.setup_id }
    pub(crate) fn key_sha256_for_report(&self) -> [u8; 32] { self.key_sha256 }
    pub(crate) fn commitment_sha256_for_report(&self) -> [u8; 32] { self.commitment_sha256 }

    fn validate(&self) -> Result<(), String> {
        if self.key.log_n() != 32 || self.key.id() != &self.setup_id
            || self.setup_id != Self::SETUP_ID || self.key_sha256 != Self::KEY_SHA256
            || self.commitment.len() != 384 || self.commitment_sha256 != Self::COMMITMENT_SHA256 {
            return Err("native role0 admitted context identity changed".into());
        }
        Ok(())
    }

    pub(crate) fn bind_admission(&self, t: &mut Transcript) -> Result<(), String> {
        self.validate()?;
        t.append_bytes(b"pcs-vendor", crate::pcs::VENDOR_PIN);
        t.append_bytes(b"pcs-mode", b"Transparent-dory-v1");
        t.append_bytes(b"pcs-setup-id", &self.setup_id);
        t.append_bytes(b"pcs-verifier-key-sha256", &self.key_sha256);
        t.append_u64(b"pcs-log-n", 32);
        t.append_bytes(b"pcs-commitment-canonical", &self.commitment);
        t.append_bytes(b"pcs-commitment-sha256", &self.commitment_sha256);
        Ok(())
    }
}

#[cfg(test)]
pub(crate) fn role0_sha256(bytes: &[u8]) -> Result<[u8; 32], String> {
    use std::ffi::c_void;
    #[link(name = "crypt32")]
    extern "system" {
        fn CryptHashCertificate2(algorithm: *const u16, flags: u32, reserved: *mut c_void,
            data: *const u8, length: u32, output: *mut u8, output_length: *mut u32) -> i32;
    }
    let length = u32::try_from(bytes.len()).map_err(|_| "native role0 SHA-256 length")?;
    let algorithm = [83u16,72,65,50,53,54,0];
    let mut digest = [0u8; 32];
    let mut output_length = 32u32;
    let ok = unsafe { CryptHashCertificate2(algorithm.as_ptr(), 0, std::ptr::null_mut(),
        bytes.as_ptr(), length, digest.as_mut_ptr(), &mut output_length) };
    if ok == 0 || output_length != 32 { return Err("native role0 SHA-256 failed".into()); }
    Ok(digest)
}

/// The artifact admission is shared; the role1 statement and transcript are not.
#[cfg(test)]
pub(crate) struct NativeRole1DiagnosticContext {
    artifacts: NativeRole0DiagnosticContext,
}

#[cfg(test)]
impl NativeRole1DiagnosticContext {
    pub(crate) fn admit(key: &[u8], commitment: &[u8]) -> Result<Self,String> {
        Ok(Self { artifacts: NativeRole0DiagnosticContext::admit(key,commitment)? })
    }
    pub(crate) fn admit_with_setup_id(key:&[u8],commitment:&[u8],setup:[u8;32])->Result<Self,String>{
        Ok(Self { artifacts: NativeRole0DiagnosticContext::admit_with_setup_id(key,commitment,setup)? })
    }
    pub(crate) fn transcript(&self)->Transcript{
        Transcript::new(b"native-prefix-role1-diagnostic-proof-v1")
    }
    pub(crate) fn bind_admission(&self,t:&mut Transcript)->Result<(),String>{self.artifacts.bind_admission(t)}
    pub(crate) fn setup_id_for_report(&self)->[u8;32]{self.artifacts.setup_id_for_report()}
    pub(crate) fn key_sha256_for_report(&self)->[u8;32]{self.artifacts.key_sha256_for_report()}
    pub(crate) fn commitment_sha256_for_report(&self)->[u8;32]{self.artifacts.commitment_sha256_for_report()}
}

/// Only the plan-owned proof entry constructs this capability. Neither numeric
/// geometry nor caller callbacks can detach its source, relation or statement.
#[cfg(test)]
pub(crate) struct NativeRole1Admission<'p,'s> {
    plan: &'p NativePrefixAuthPlan<'s>,
    source: &'p crate::packed::PackedFile,
    context: &'p NativeRole1DiagnosticContext,
    grouped: crate::sparse_stream_roster::GroupedVAdmission,
    next_canonical_owner: std::cell::Cell<usize>,
    canonical_terms: std::cell::Cell<usize>,
}

#[cfg(test)]
impl NativeRole1Admission<'_,'_> {
    pub(crate) fn validate_for_use(&self)->Result<(),String>{
        self.plan.require_role1_native_plan()?;
        self.context.artifacts.validate()?;
        if self.source.input_len()!=1usize<<32{return Err("native role1 packed source width".into());}
        Ok(())
    }
    pub(crate) fn grouped_admission(&self)->&crate::sparse_stream_roster::GroupedVAdmission{&self.grouped}
    pub(crate) fn load_owner(&self,owner:usize)->Result<Vec<Fr>,String>{
        if owner>=4096||self.source.input_len()!=1usize<<32{return Err("native role1 source owner window".into());}
        crate::packed_rows::read_row(self.source,1usize<<20,owner)
    }
    pub(crate) fn visit_owner_terms(&self,owner:usize,sink:&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String>{
        if owner>=4096||owner!=self.next_canonical_owner.get(){
            return Err("native role1 canonical baseline owner order or replay".into());
        }
        let row_base=owner.checked_mul(1usize<<19).ok_or("native role1 row base overflow")?;
        let input_base=owner.checked_mul(1usize<<20).ok_or("native role1 input base overflow")?;
        let row_end=row_base.checked_add(1usize<<19).ok_or("native role1 row end overflow")?;
        let input_end=input_base.checked_add(1usize<<20).ok_or("native role1 input end overflow")?;
        let counts=self.plan.daa.visit_header_terms(owner as u64,|mut term|{
            if !(row_base..row_end).contains(&term.row)
                ||!(input_base..input_end).contains(&term.gate.left)
                ||!(input_base..input_end).contains(&term.gate.right){
                return Err("native role1 canonical term escapes owner window".into());
            }
            term.row-=row_base;term.gate.left-=input_base;term.gate.right-=input_base;
            sink(term)?;
            self.canonical_terms.set(self.canonical_terms.get().checked_add(1).ok_or("native role1 term counter overflow")?);
            Ok(())
        })?;
        let short=owner==3072;
        if counts.emitted!=if short{388_369}else{396_561}||counts.omitted_worktree!=78_194
            ||counts.omitted_mature_a4!=0||counts.omitted_short_a4!=if short{8192}else{0}{
            return Err("native role1 complete canonical header census".into());
        }
        self.next_canonical_owner.set(owner+1);Ok(())
    }
    pub(crate) fn bind_statement(&self,t:&mut Transcript)->Result<(),String>{
        self.plan.bind_role1_diagnostic_context(t,self.context)
    }
    pub(crate) fn coefficients(&self,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String>{
        self.plan.coefficients(1,r,u,v)
    }
    pub(crate) fn extra_live_capacity_bytes(&self)->Result<usize,String>{
        // GroupedVAdmission's boxed map/count payload is already in the sparse
        // ledger. The token has no other heap allocation; count its full struct.
        Ok(std::mem::size_of::<Self>())
    }
}

#[cfg(test)]
impl NativePrefixAuthPlan<'_> {
    fn require_role1_native_plan(&self)->Result<(),String>{
        self.selection.validate()?;
        if self.parent.headers()!=N||self.parent.slot_log()!=H||self.parent.slots()!=4096
            ||self.candidate.n!=N||self.candidate.root!=self.parent.descriptor().root
            ||self.candidate.total!=self.parent.work_profile().total_be28
            ||self.daa.headers()!=N||self.daa.slot_log()!=H||self.daa.input_log()!=32||self.daa.row_log()!=31
            ||self.descriptors.iter().enumerate().any(|(i,d)|d.role!=i||d.input_log!=INPUT_LOGS[i]
                ||d.row_log!=ROW_LOGS[i]||d.name!=NAMES[i]||d.source!=SOURCE){
            return Err("native role1 borrowed plan/complete descriptor geometry".into());
        }
        let mut short=0usize;
        for owner in 0..4096{
            match self.daa.owner_class(owner)?{
                crate::daa_history_roster::OwnerClass::Short(crate::short_daa_layout::Profile::M2) if owner==3072=>short+=1,
                crate::daa_history_roster::OwnerClass::Genesis|crate::daa_history_roster::OwnerClass::Initial
                |crate::daa_history_roster::OwnerClass::Carry|crate::daa_history_roster::OwnerClass::Singleton
                |crate::daa_history_roster::OwnerClass::M1|crate::daa_history_roster::OwnerClass::Padding=>(),
                _=>return Err("native role1 owner topology differs from N3073".into()),
            }
        }
        if short!=1{return Err("native role1 unique short-M2 owner census".into());}Ok(())
    }
    pub(crate) fn bind_role1_descriptor_fields_for_test(&self,t:&mut Transcript,context:&NativeRole1DiagnosticContext,
        role:usize,input:usize,rows:usize)->Result<(),String>{
        if t.challenges()!=0{return Err("native role1 binding after challenge".into());}
        self.require_role1_native_plan()?;context.artifacts.validate()?;
        if (role,input,rows)!=(1,32,31){return Err("native role1 exact descriptor fields".into());}
        let descriptor=&self.descriptors[1];
        t.append_bytes(b"native-role1-descriptor",descriptor.name.as_bytes());
        t.append_bytes(b"native-role1-source",descriptor.source.as_bytes());
        t.append_u64(b"native-role1-role-index",role as u64);
        t.append_u64(b"native-role1-input-log",input as u64);
        t.append_u64(b"native-role1-output-log",rows as u64);Ok(())
    }
    pub(crate) fn bind_role1_diagnostic_context(&self,t:&mut Transcript,context:&NativeRole1DiagnosticContext)->Result<(),String>{
        if t.challenges()!=0{return Err("native role1 binding after challenge".into());}
        self.require_role1_native_plan()?;context.artifacts.validate()?;
        context.bind_admission(t)?;
        self.bind_role1_descriptor_fields_for_test(t,context,1,32,31)?;
        self.bind_plan_identity(t)
    }
    pub(crate) fn prove_role1_packed_for_test(&self,source:&crate::packed::PackedFile,transcript:&mut Transcript,
        context:&NativeRole1DiagnosticContext)->Result<(GkrProof,InputClaim,crate::sparse_stream_roster::GroupedVStats,
            crate::sparse_stream_roster::BooleanUPreweightStats),String>{
        if transcript.challenges()!=0{return Err("native role1 proof transcript already challenged".into());}
        self.require_role1_native_plan()?;context.artifacts.validate()?;
        if source.input_len()!=1usize<<32{return Err("native role1 packed source width".into());}
        // Initialization-only overlap: original map, copied map and possible
        // boxed successor, three two-word count buffers, and bounded headers.
        // This temporary is gone before the sparse baseline; do not add it to
        // every live U/V phase. The returned baseline inventory must dominate it.
        let construction_bound=4096usize.checked_mul(3).and_then(|n|n.checked_add(6))
            .and_then(|n|n.checked_mul(std::mem::size_of::<usize>()))
            .and_then(|n|n.checked_add(std::mem::size_of::<NativeRole1Admission<'_, '_>>()))
            .and_then(|n|n.checked_add(1024)).ok_or("native role1 constructor capacity overflow")?;
        if construction_bound>512*1024*1024{return Err("native role1 constructor exceeds scoped cap".into());}
        let grouped={
            let mut map=vec![0usize;4096];map[3072]=1;
            if map.capacity()!=4096{return Err("native role1 constructor map capacity".into());}
            crate::sparse_stream_roster::GroupedVAdmission::try_new(12,&map,&[396_561,388_369])?
        };
        let admission=NativeRole1Admission{plan:self,source,context,grouped,
            next_canonical_owner:std::cell::Cell::new(0),canonical_terms:std::cell::Cell::new(0)};
        let result=crate::sparse_stream_roster::prove_native_role1_boolean_grouped_for_test(&admission,transcript)?;
        if admission.next_canonical_owner.get()!=4096||admission.canonical_terms.get()!=1_624_305_664{
            return Err("native role1 complete one-sweep canonical baseline".into());
        }
        if result.3.u_phase_peak_capacity_bytes[0]<construction_bound{
            return Err("native role1 baseline inventory must cover constructor peak".into());
        }
        Ok(result)
    }
}

#[cfg(test)]
pub(crate) use native_role3::{NativeRole3Admission,NativeRole3DiagnosticContext,NativeRole3Mark,NativeRole3Memory,
    emit_role3_mark,ROLE3_STAGES};

#[cfg(test)]
mod native_role3 {
    use super::*;
    use std::{cell::{Cell,RefCell},mem::{size_of,size_of_val},io::Write,time::Instant};
    const LIMIT:usize=512*1024*1024;
    const BINDING:usize=32*1024*1024;
    const EXPORT:usize=1024*1024;
    const TERMS:usize=288158;
    pub(crate) const ROLE3_STAGES:[&str;17]=["admission_start","admission_complete","baseline_start","baseline_done",
        "u_cache_streamed","u_anchor_done","u_local_done","u_handoff_done","v_cache_grouped","v_anchor_done",
        "v_local_done","v_handoff_done","terminal_wiring_done","line_start","line_done","consumer_complete","export_ready"];
    #[derive(Clone,Copy,Debug,serde::Serialize)]
    pub(crate) struct NativeRole3Mark{pub(crate) stage:&'static str,pub(crate) elapsed_ns:u64}
    const EMPTY:NativeRole3Mark=NativeRole3Mark{stage:"",elapsed_ns:0};
    #[derive(Clone,Copy,Debug,serde::Serialize)]
    pub(crate) struct NativeRole3Memory{
        pub(crate) original_template_capacity_bytes:usize,pub(crate) layout_box_bytes:usize,pub(crate) token_inline_bytes:usize,
        pub(crate) context_owned_capacity_bytes:usize,pub(crate) constructor_bound_bytes:usize,pub(crate) json_object_bytes:[usize;5],
        pub(crate) binding_overlap_bound_bytes:usize,pub(crate) observer_export_bound_bytes:usize,pub(crate) extra_live_capacity_bytes:usize,
        pub(crate) producer_preflight_bound_bytes:usize,pub(crate) producer_peak_capacity_bytes:usize,pub(crate) external_parent_heap_measured:bool,
    }
    fn add(a:usize,b:usize)->Result<usize,String>{a.checked_add(b).ok_or("native role3 capacity overflow".into())}
    fn mul(a:usize,b:usize)->Result<usize,String>{a.checked_mul(b).ok_or("native role3 capacity overflow".into())}
    struct FixedWriter<'a>{bytes:&'a mut[u8],len:usize}
    impl Write for FixedWriter<'_>{
        fn write(&mut self,b:&[u8])->std::io::Result<usize>{let next=self.len.checked_add(b.len()).ok_or_else(||std::io::Error::other("role3 mark overflow"))?;
            if next>self.bytes.len(){return Err(std::io::Error::other("role3 mark cap"));}self.bytes[self.len..next].copy_from_slice(b);self.len=next;Ok(b.len())}
        fn flush(&mut self)->std::io::Result<()>{Ok(())}
    }
    pub(crate) fn emit_role3_mark(mark:NativeRole3Mark)->Result<(),String>{
        let mut bytes=[0u8;256];let mut writer=FixedWriter{bytes:&mut bytes,len:0};
        serde_json::to_writer(&mut writer,&mark).map_err(|e|e.to_string())?;let len=writer.len;
        let mut out=std::io::stdout().lock();
        if mark.stage==ROLE3_STAGES[0]{out.write_all(b"\n").map_err(|e|e.to_string())?;}
        out.write_all(b"R3_NATIVE_PHASE ").and_then(|_|out.write_all(&bytes[..len])).and_then(|_|out.write_all(b"\n"))
            .and_then(|_|out.flush()).map_err(|e|e.to_string())
    }
    pub(crate) struct NativeRole3DiagnosticContext{
        artifacts:NativeRole0DiagnosticContext,reference:RefCell<std::fs::File>,started:Instant,
        marks:RefCell<[NativeRole3Mark;17]>,completed:Cell<usize>,memory:RefCell<Option<NativeRole3Memory>>,
        admission_io:Cell<crate::packed::PackedIoSnapshot>,producer_io:Cell<crate::packed::PackedIoSnapshot>,
        producer_elapsed:Cell<u64>,
    }
    impl NativeRole3DiagnosticContext{
        pub(crate) fn admit(key:&[u8],commitment:&[u8],reference:std::fs::File)->Result<Self,String>{
            Ok(Self{artifacts:NativeRole0DiagnosticContext::admit(key,commitment)?,reference:RefCell::new(reference),
                started:Instant::now(),marks:RefCell::new([EMPTY;17]),completed:Cell::new(0),memory:RefCell::new(None),
                admission_io:Cell::new(Default::default()),producer_io:Cell::new(Default::default()),producer_elapsed:Cell::new(0)})
        }
        pub(crate) fn transcript(&self)->Transcript{Transcript::new(b"native-prefix-role3-diagnostic-proof-v1")}
        pub(crate) fn elapsed_ns(&self)->Result<u64,String>{u64::try_from(self.started.elapsed().as_nanos()).map_err(|_|"native role3 clock overflow".into())}
        pub(crate) fn mark(&self,stage:&'static str)->Result<(),String>{let index=self.completed.get();
            if ROLE3_STAGES.get(index)!=Some(&stage){return Err("native role3 outer marker order".into());}
            let mark=NativeRole3Mark{stage,elapsed_ns:if index==0{0}else{self.elapsed_ns()?}};emit_role3_mark(mark)?;
            self.marks.borrow_mut()[index]=mark;self.completed.set(index+1);Ok(())}
        pub(crate) fn marks_for_report(&self)->Result<[NativeRole3Mark;17],String>{
            if self.completed.get()!=17{return Err("native role3 incomplete marker roster".into());}Ok(*self.marks.borrow())}
        pub(crate) fn memory_for_report(&self)->Result<NativeRole3Memory,String>{self.memory.borrow().as_ref().copied().ok_or("native role3 memory not complete".into())}
        pub(crate) fn io_for_report(&self)->(crate::packed::PackedIoSnapshot,crate::packed::PackedIoSnapshot){(self.admission_io.get(),self.producer_io.get())}
        pub(crate) fn producer_elapsed_ns(&self)->u64{self.producer_elapsed.get()}
        pub(crate) fn artifact_ids(&self)->([u8;32],[u8;32],[u8;32]){
            (self.artifacts.key_sha256_for_report(),self.artifacts.commitment_sha256_for_report(),self.artifacts.setup_id_for_report())}
        fn capacity(&self)->Result<usize,String>{let mut n=add(size_of_val(self),self.artifacts.commitment.capacity())?;
            let v=self.artifacts.key.verifier();for values in [&v.delta_1l,&v.delta_1r,&v.delta_2l,&v.delta_2r,&v.chi]{
                n=add(n,mul(values.capacity(),size_of::<dory_pcs::backends::arkworks::ArkGT>())?)?;}Ok(n)}
    }
    /// The plan factory authenticates the actual locked source against a held
    /// reference and fixed digest before minting this nonforgeable capability.
    pub(crate) struct NativeRole3Admission<'p,'s>{
        plan:&'p NativePrefixAuthPlan<'s>,source:&'p crate::packed::PackedFile,context:&'p NativeRole3DiagnosticContext,
        grouped:crate::sparse_stream_roster::GroupedVAdmission,next:Cell<usize>,terms:Cell<usize>,extra:usize,
    }
    impl NativeRole3Admission<'_,'_>{
        pub(crate) fn validate_for_use(&self)->Result<(),String>{self.plan.require_role3_native_plan()?;self.context.artifacts.validate()?;
            if self.source.input_len()!=1usize<<32{return Err("native role3 source width".into());}Ok(())}
        pub(crate) fn grouped_admission(&self)->&crate::sparse_stream_roster::GroupedVAdmission{&self.grouped}
        pub(crate) fn extra_live_capacity_bytes(&self)->usize{self.extra}
        pub(crate) fn started(&self)->Instant{self.context.started}
        pub(crate) fn load_owner(&self,owner:usize)->Result<Vec<Fr>,String>{
            let copy=role3_owner_window(owner)?;self.source.read_copy(8192,copy)
        }
        pub(crate) fn visit_owner_terms(&self,owner:usize,sink:&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String>{
            if owner>=4096||owner!=self.next.get(){return Err("native role3 baseline owner order or replay".into());}
            let row=owner.checked_mul(16384).ok_or("native role3 row window overflow")?;
            let input=owner.checked_mul(8192).ok_or("native role3 input window overflow")?;let mut count=0usize;
            self.plan.visit_role_owner_terms(3,owner as u64,|mut t|{
                if !(row..row+16384).contains(&t.row)||!(input..input+8192).contains(&t.gate.left)||!(input..input+8192).contains(&t.gate.right){
                    return Err("native role3 term escapes canonical owner window".into());}
                t.row-=row;t.gate.left-=input;t.gate.right-=input;
                // This immutable plan visitor walks the original template in
                // order; grouped baseline checks exact normalized equality.
                sink(t)?;count=count.checked_add(1).ok_or("native role3 owner census overflow")?;Ok(())
            })?;
            if count!=TERMS{return Err("native role3 owner term census".into());}
            self.terms.set(self.terms.get().checked_add(count).ok_or("native role3 baseline census overflow")?);self.next.set(owner+1);Ok(())
        }
        pub(crate) fn prepare_binding(&self,t:&Transcript)->Result<Transcript,String>{self.validate_for_use()?;self.plan.prepare_role3_binding_for_test(t,self.context)}
        pub(crate) fn coefficients(&self,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String>{self.plan.coefficients(3,r,u,v)}
        pub(crate) fn complete(&self,marks:[NativeRole3Mark;13],g:&crate::sparse_stream_roster::GroupedVStats,b:&crate::sparse_stream_roster::BooleanUPreweightStats)->Result<(),String>{
            if self.next.get()!=4096||self.terms.get()!=1_180_295_168||self.context.completed.get()!=2{return Err("native role3 complete baseline/observer census".into());}
            for (i,m) in marks.iter().enumerate(){if m.stage!=ROLE3_STAGES[i+2]{return Err("native role3 producer marker order".into());}}
            let mut memory=self.context.memory_for_report()?;memory.producer_preflight_bound_bytes=b.u_preflight_capacity_bound_bytes;
            memory.producer_peak_capacity_bytes=b.u_state_peak_capacity_bytes.max(g.grouped_state_peak_capacity_bytes);
            if memory.producer_peak_capacity_bytes>memory.producer_preflight_bound_bytes||memory.producer_preflight_bound_bytes>LIMIT
                ||b.u_phase_peak_capacity_bytes[0]<memory.constructor_bound_bytes{return Err("native role3 complete producer capacity".into());}
            self.context.marks.borrow_mut()[2..15].copy_from_slice(&marks);self.context.completed.set(15);
            *self.context.memory.borrow_mut()=Some(memory);Ok(())
        }
    }
    fn role3_owner_window(owner:usize)->Result<usize,String>{
        if owner>=4096{return Err("native role3 source owner window".into());}
        owner.checked_mul(128).and_then(|x|x.checked_add(96)).ok_or("native role3 source window overflow".into())
    }
    fn role3_hex<const N:usize>(s:&str)->[u8;N]{std::array::from_fn(|i|u8::from_str_radix(&s[2*i..2*i+2],16).expect("code-owned role3 identity"))}
    fn require_role3_candidate(c:&Candidate)->Result<(),String>{
        if c.n!=3073||c.root!=role3_hex::<32>("DF3C1D555FCF6D2A5BA620422D1007A85CA5F8968D6F608C9856CE326C448913")
            ||c.total!=role3_hex::<28>("000000000000000000000000000000000000000000564F0B9B000000")
            ||c.tip!=role3_hex::<32>("CC394AC0D406F45679111927B422B454EFA97648015FE5AEC52EA9B54EAF53DC")||c.tip_time!=1562018269889{
            return Err("native role3 fixed RAW candidate identity".into());}Ok(())
    }
    impl NativePrefixAuthPlan<'_>{
        fn require_role3_native_plan(&self)->Result<(),String>{self.selection.validate()?;require_role3_candidate(&self.candidate)?;
            if self.parent.headers()!=N||self.parent.slot_log()!=H||self.parent.slots()!=4096||self.candidate.n!=N
                ||self.candidate.root!=self.parent.descriptor().root||self.candidate.total!=self.parent.work_profile().total_be28
                ||self.parent.fixed_profile().genesis!=self.selection.genesis||self.parent.fixed_profile().prefix.as_slice()!=fixed::PROFILE_PREFIX
                ||self.descriptors.iter().enumerate().any(|(i,d)|d.role!=i||d.input_log!=INPUT_LOGS[i]||d.row_log!=ROW_LOGS[i]||d.name!=NAMES[i]||d.source!=SOURCE)
                ||self.points.circuit.input_len!=8192||self.points.circuit.row_count!=16384||self.points.circuit.terms.len()!=TERMS
                ||self.points.stats.used_bits!=8061||self.points.stats.residual_rows!=10502||self.point_shape.input_bits!=13||self.point_shape.row_bits!=14{
                return Err("native role3 borrowed plan/complete descriptor geometry".into());}
            let d=&self.descriptors[3];if d.ordered_tags.as_slice()!=[NAMES[3]]||d.mapping!="row14+owner12; input13+owner12; bank96"
                ||d.zero_extension.is_some()||d.public_dependency!="same parent n/root/total/source profile"{return Err("native role3 canonical descriptor identity".into());}Ok(())}
        pub(crate) fn prepare_role3_binding_for_test(&self,t:&Transcript,context:&NativeRole3DiagnosticContext)->Result<Transcript,String>{
            prepare_role3_artifact_binding(self,t,&context.artifacts)
        }
        pub(crate) fn prove_role3_packed_for_test(&self,source:&crate::packed::PackedFile,t:&mut Transcript,context:&NativeRole3DiagnosticContext)
            ->Result<(GkrProof,InputClaim,crate::sparse_stream_roster::GroupedVStats,crate::sparse_stream_roster::BooleanUPreweightStats),String>{
            if t.challenges()!=0{return Err("native role3 proof transcript already challenged".into());}self.require_role3_native_plan()?;context.artifacts.validate()?;
            if context.completed.get()!=0{return Err("native role3 context already used".into());}
            let json=native_role5_common::binding_json_preflight(self)?;
            let original=mul(self.points.circuit.terms.capacity(),size_of::<Term>())?;let boxes=mul(2*(11*256+18*67),size_of::<usize>())?;
            if boxes!=64352{return Err("native role3 typed layout ABI".into());}
            let context_owned=context.capacity()?;let inline=size_of::<NativeRole3Admission<'_, '_>>();
            let extra=add(add(add(add(add(original,boxes)?,inline)?,context_owned)?,BINDING)?,EXPORT)?;
            let construction=add(extra,add(mul(4096*3+6,size_of::<usize>())?,1024)?)?;
            if construction>LIMIT{return Err("native role3 constructor exceeds512MiB".into());}
            let view=source.native_role0_view()?;view.require_same_source(source)?;
            context.mark("admission_start")?;source.reset_io_metrics();
            let digest=native_role5_common::compare_reference(&mut *context.reference.borrow_mut(),4096,|owner,expected|{
                let actual=view.read_copy(owner)?;if actual.len()!=1usize<<20||actual.capacity_bytes()!=131072||!actual.matches_bytes(expected){
                    return Err("native role3 original packed handle differs from held reference".into());}Ok(())})?;
            native_role5_common::require_witness_digest(digest)?;context.admission_io.set(source.io_metrics_snapshot());
            let grouped={let map=vec![0usize;4096];if map.capacity()!=4096{return Err("native role3 map actual capacity".into());}
                crate::sparse_stream_roster::GroupedVAdmission::try_new(12,&map,&[TERMS])?};
            let admission=NativeRole3Admission{plan:self,source,context,grouped,next:Cell::new(0),terms:Cell::new(0),extra};
            *context.memory.borrow_mut()=Some(NativeRole3Memory{original_template_capacity_bytes:original,layout_box_bytes:boxes,token_inline_bytes:inline,
                context_owned_capacity_bytes:context_owned,constructor_bound_bytes:construction,json_object_bytes:json,binding_overlap_bound_bytes:BINDING,
                observer_export_bound_bytes:EXPORT,extra_live_capacity_bytes:extra,producer_preflight_bound_bytes:0,producer_peak_capacity_bytes:0,external_parent_heap_measured:false});
            // Real sealed-boundary faults are checked before any point-owner load.
            if admission.load_owner(4096).is_ok(){return Err("native role3 invalid owner accepted".into());}
            context.mark("admission_complete")?;source.reset_io_metrics();let mut working=t.clone();
            let began=Instant::now();let result=crate::sparse_stream_roster::prove_native_role3_boolean_grouped_for_test(&admission,&mut working)?;
            context.producer_elapsed.set(u64::try_from(began.elapsed().as_nanos()).map_err(|_|"native role3 producer clock overflow")?);
            context.producer_io.set(source.io_metrics_snapshot());*t=working;Ok(result)
        }
        pub(crate) fn verify_role3_for_test(&self,proof:&GkrProof,context:&NativeRole3DiagnosticContext)->Result<(InputClaim,Transcript),String>{
            let mut t=context.transcript();let prepared=self.prepare_role3_binding_for_test(&t,context)?;
            let claim=crate::gkr::verify_with_wiring(&[25],1usize<<26,proof,&mut t,move|t|*t=prepared,
                |layer,r,u,v|if layer==0{self.coefficients(3,r,u,v).map_err(|_|crate::gkr::GkrError::PointDimension)}else{Err(crate::gkr::GkrError::PointDimension)})
                .map_err(|e|e.to_string())?;Ok((claim,t))
        }
    }
    pub(super) fn prepare_role3_artifact_binding(plan:&NativePrefixAuthPlan<'_>,t:&Transcript,
        artifacts:&NativeRole0DiagnosticContext)->Result<Transcript,String>{
        if t.challenges()!=0{return Err("native role3 binding after challenge".into());}plan.require_role3_native_plan()?;
        artifacts.validate()?;native_role5_common::binding_json_preflight(plan)?;
        let mut prepared=t.clone();artifacts.bind_admission(&mut prepared)?;
        let d=&plan.descriptors[3];prepared.append_bytes(b"native-role3-descriptor",d.name.as_bytes());prepared.append_bytes(b"native-role3-source",d.source.as_bytes());
        for (label,value) in [(b"native-role3-role-index".as_slice(),3u64),(b"native-role3-input-log".as_slice(),25),(b"native-role3-output-log".as_slice(),26)]{prepared.append_u64(label,value);}
        plan.bind_plan_identity(&mut prepared)?;Ok(prepared)
    }
    #[cfg(test)] mod tests{
        use super::*;
        #[test] fn native_role3_window_projection_and_fixed_observer_bounds(){
            for owner in [0,1,3072,3073,4095]{let c=role3_owner_window(owner).unwrap();assert_eq!(c*8192,owner*(1<<20)+786432);}
            assert_eq!(role3_owner_window(4096).unwrap_err(),"native role3 source owner window");
            assert_eq!(ROLE3_STAGES.len(),17);let mut bytes=[0u8;256];let mut w=FixedWriter{bytes:&mut bytes,len:0};
            serde_json::to_writer(&mut w,&NativeRole3Mark{stage:"terminal_wiring_done",elapsed_ns:u64::MAX}).unwrap();assert!(w.len<256);
            assert!(w.write_all(&[0u8;256]).is_err());assert!(add(usize::MAX,1).is_err());
            let bits=[0u64,0,0,0,0,1,1];assert_eq!(bits.iter().enumerate().map(|(i,b)|(*b as usize)<<i).sum::<usize>(),96);
            let candidate=Candidate{n:3073,root:role3_hex("DF3C1D555FCF6D2A5BA620422D1007A85CA5F8968D6F608C9856CE326C448913"),
                total:role3_hex("000000000000000000000000000000000000000000564F0B9B000000"),
                tip:role3_hex("CC394AC0D406F45679111927B422B454EFA97648015FE5AEC52EA9B54EAF53DC"),tip_time:1562018269889};
            require_role3_candidate(&candidate).unwrap();for fault in 0..5{let mut bad=candidate.clone();
                match fault{0=>bad.n-=1,1=>bad.root[0]^=1,2=>bad.total[0]^=1,3=>bad.tip[0]^=1,_=>bad.tip_time+=1}
                assert_eq!(require_role3_candidate(&bad).unwrap_err(),"native role3 fixed RAW candidate identity");}
        }
    }
}

#[cfg(test)]
pub(crate) struct Role2EndpointAdapter<'p,'s>{plan:&'p NativePrefixAuthPlan<'s>,source:&'p crate::packed::PackedFile}
#[cfg(test)]
fn role2_endpoint_descriptor(role:usize,input:usize,row:usize,slots:usize,h:usize,tags:&[String],canonical:&[String])->Result<(),String>{
    if (role,input,row,slots,h)!=(2,32,32,4096,12){return Err("role2 endpoint descriptor geometry".into());}
    if tags.len()!=40||canonical.len()!=40||tags!=canonical{return Err("role2 endpoint descriptor tag order".into());}Ok(())
}
#[cfg(test)]
pub(crate) fn role2_endpoint_admission_controls()->Result<(),String>{
    let names=(0..40).map(|i|format!("member_{i}")).collect::<Vec<_>>();
    role2_endpoint_descriptor(2,32,32,4096,12,&names,&names)?;
    for (role,input,row,slots,h) in [(1,32,32,4096,12),(2,31,32,4096,12),(2,32,31,4096,12),
        (2,32,32,2048,12),(2,32,32,4096,11)]{
        if role2_endpoint_descriptor(role,input,row,slots,h,&names,&names).unwrap_err()!="role2 endpoint descriptor geometry"{
            return Err("role2 descriptor isolated negative".into());}
    }
    let mut reordered=names.clone();reordered.swap(34,35);
    if role2_endpoint_descriptor(2,32,32,4096,12,&reordered,&names).unwrap_err()!="role2 endpoint descriptor tag order"{
        return Err("role2 descriptor order negative".into());}
    if role2_endpoint_descriptor(2,32,32,4096,12,&names[..39],&names).unwrap_err()!="role2 endpoint descriptor tag order"{
        return Err("role2 descriptor omission negative".into());}Ok(())
}
#[cfg(test)]
impl<'s> NativePrefixAuthPlan<'s>{
    pub(crate) fn role2_endpoints<'p>(&'p self,source:&'p crate::packed::PackedFile,
        reference:&mut std::fs::File,started:std::time::Instant)->Result<Role2EndpointAdapter<'p,'s>,String>{
        self.selection.validate()?;
        let canonical=self.parent.topology().families.iter().map(|f|f.name.clone())
            .chain(["fixed".into(),"leaf".into(),"work-local".into()])
            .chain(self.parent.work_boundary().links().iter().map(|f|f.name.clone())).collect::<Vec<_>>();
        let d=&self.descriptors[2];role2_endpoint_descriptor(d.role,d.input_log,d.row_log,self.parent.slots(),self.parent.slot_log(),&d.ordered_tags,&canonical)?;
        if self.parent.headers()!=3073||self.parent.slot_log()!=12||self.parent.slots()!=4096
            ||self.descriptors[2].input_log!=32||self.descriptors[2].row_log!=32
            ||self.descriptors[2].ordered_tags.len()!=40||self.parent.topology().families.len()!=34
            ||self.candidate.root!=self.parent.descriptor().root||self.candidate.total!=self.parent.work_profile().total_be28{
            return Err("role2 native admission geometry".into());}
        let decode=|s:&str|->Vec<u8>{(0..s.len()/2).map(|i|u8::from_str_radix(&s[2*i..2*i+2],16).expect("code-owned role2 pin")).collect()};
        if self.candidate.n!=3073||self.candidate.root.as_slice()!=decode("DF3C1D555FCF6D2A5BA620422D1007A85CA5F8968D6F608C9856CE326C448913")
            ||self.candidate.total.as_slice()!=decode("000000000000000000000000000000000000000000564F0B9B000000")
            ||self.candidate.tip.as_slice()!=decode("CC394AC0D406F45679111927B422B454EFA97648015FE5AEC52EA9B54EAF53DC")
            ||self.candidate.tip_time!=1562018269889||self.descriptors.iter().enumerate().any(|(i,d)|
                d.role!=i||d.input_log!=INPUT_LOGS[i]||d.row_log!=ROW_LOGS[i]||d.name!=NAMES[i]||d.source!=SOURCE){
            return Err("role2 native candidate/descriptor identity".into());}
        let view=source.native_role0_view()?;view.require_same_source(source)?;
        let digest=native_role5_common::compare_reference(reference,4096,|owner,expected|{
            if started.elapsed()>std::time::Duration::from_secs(300){return Err("role2 admission deadline".into());}
            let actual=view.read_copy(owner)?;
            if actual.len()!=1usize<<20||actual.capacity_bytes()!=131072||!actual.matches_bytes(expected){
                return Err("role2 original packed handle differs from held reference".into());}Ok(())})?;
        native_role5_common::require_witness_digest(digest)?;
        Ok(Role2EndpointAdapter{plan:self,source})
    }
}
#[cfg(test)]
impl Role2EndpointAdapter<'_,'_>{
    pub(crate) fn visit(&self,left:bool,owner:usize,sink:&mut dyn FnMut(crate::sparse_stream_roster::EdgeTerm)->Result<(),String>)->Result<(),String>{
        self.source.native_role0_view()?.require_same_source(self.source)?;
        crate::work_tree_wiring::visit_full_roster_endpoint(self.plan.parent.topology(),fixed::engine()?,
            self.plan.parent.fixed_profile(),self.plan.parent.leaf_boundary(),self.plan.parent.work_boundary(),left,owner,sink)
    }
    pub(crate) fn require_source(&self,source:&crate::packed::PackedFile)->Result<(),String>{
        self.source.native_role0_view()?.require_same_source(source)
    }
}


#[cfg(test)]
pub(crate) use native_role2_full::{role2_full_binding_controls_for_test,role2_full_transaction_controls_for_test};

/// Exact diagnostic framing and transactional consumers for the native role2 lot.
#[cfg(test)]
mod native_role2_full {
    use super::*;
    const DOMAIN:&[u8]=b"native-prefix-role2-direct-full-diagnostic-v1";
    const CONTINUE:&[u8]=b"native-role2-direct-full-continuation-v1";
    const GEOMETRY:[u64;9]=[2,3073,12,32,32,20,14,6,40];
    const PINS:[&str;4]=[
        "ABB3D74AE75256CED63110B72C2E0D5EBA1B90B09889E45EA327BDA1C9A640D2",
        "8CDB90DA475E646280113D97C9469BE7EB86A1D04F20404C64239187284FC009",
        "C1CC1CF72FF539F259A3BDEF756332BA52CB8AFF26C11AB4116D1B2F9D17ED43",
        "725D7B1215E1185C52C1012D9294260612653ACAD53A02429B8EAAFD0F0770C8"];
    const MEMBERS:[(&str,usize,u64,u64);40]=[
        ("header_to_leaf_raw_length_nbits_height",13,12859392,12859392),
        ("node_profile_output_core_alias",8,1048576,1048576),
        ("node_message_child_0",8,1048320,1048320),("node_message_child_1",8,1048320,1048320),
        ("profile_digest_fanout",8,1048576,1048576),
        ("level_1_child_0",8,524288,524288),("level_1_child_1",8,524288,524288),
        ("level_2_child_0",8,262144,262144),("level_2_child_1",8,262144,262144),
        ("level_3_child_0",8,131072,131072),("level_3_child_1",8,131072,131072),
        ("level_4_child_0",8,65536,65536),("level_4_child_1",8,65536,65536),
        ("level_5_child_0",8,32768,32768),("level_5_child_1",8,32768,32768),
        ("level_6_child_0",8,16384,16384),("level_6_child_1",8,16384,16384),
        ("level_7_child_0",8,8192,8192),("level_7_child_1",8,8192,8192),
        ("level_8_child_0",8,4096,4096),("level_8_child_1",8,4096,4096),
        ("level_9_child_0",8,2048,2048),("level_9_child_1",8,2048,2048),
        ("level_10_child_0",8,1024,1024),("level_10_child_1",8,1024,1024),
        ("level_11_child_0",8,512,512),("level_11_child_1",8,512,512),
        ("level_12_child_0",8,256,256),("level_12_child_1",8,256,256),
        ("public_root",8,256,256),("inactive_tree_endpoints",13,0,0),
        ("padding_leaf_unused_header_aliases",13,4286464,4286464),
        ("profile_slot_unused_child_endpoints",9,512,512),("endpoint_bank_padding",11,6152192,6152192),
        ("fixed",11,11944440,7606272),("leaf",14,75845632,32739328),
        ("work-local",11,11209728,5587968),("work_first_lower_zero",8,224,224),
        ("work_interval_continuity",8,687904,687904),("work_public_total",8,224,224)];
    fn bytes32(text:&str)->Result<[u8;32],String>{
        if text.len()!=64||!text.bytes().all(|b|b.is_ascii_hexdigit()){return Err("role2 full pin encoding".into());}
        let mut bytes=[0;32];for (i,out) in bytes.iter_mut().enumerate(){
            *out=u8::from_str_radix(&text[2*i..2*i+2],16).map_err(|_|"role2 full pin encoding")?;}Ok(bytes)
    }
    fn pins()->Result<[[u8;32];4],String>{Ok([bytes32(PINS[0])?,bytes32(PINS[1])?,bytes32(PINS[2])?,bytes32(PINS[3])?])}
    fn counters(t:&Transcript)->[u64;3]{[t.challenges(),t.raw_queries(),t.bytes_absorbed()]}
    fn fingerprint(t:&Transcript)->Result<([u64;3],Fr),String>{
        Ok((counters(t),t.clone().try_challenge_scalar(CONTINUE)?))
    }
    fn require_fresh(t:&Transcript)->Result<(),String>{
        if t.challenges()!=0||t.raw_queries()!=0{return Err("role2 full binding after challenge".into());}
        if fingerprint(t)?!=fingerprint(&Transcript::new(DOMAIN))?{return Err("role2 full diagnostic domain/prefix".into());}Ok(())
    }
    fn metadata(pre:&Transcript,geometry:&[u64;9],tags:&[String],counts:&[(u64,u64)],
        strides:&[usize],admitted:&[[u8;32];4])->Result<Transcript,String>{
        require_fresh(pre)?;
        if geometry!=&GEOMETRY{return Err("role2 full metadata geometry".into());}
        if tags.len()!=40||counts.len()!=40||strides.len()!=40{return Err("role2 full metadata count".into());}
        if admitted!=&pins()?{return Err("role2 full admitted pins".into());}
        for i in 0..40{
            if tags[i]!=MEMBERS[i].0{return Err("role2 full metadata tag order".into());}
            if strides[i]!=MEMBERS[i].1{return Err("role2 full metadata stride".into());}
            if counts[i]!=(MEMBERS[i].2,MEMBERS[i].3){return Err("role2 full metadata term/row count".into());}
        }
        let mut prepared=pre.clone();
        prepared.append_bytes(b"source-revision",b"source26-role2-direct-full-diagnostic-v1");
        for (label,pin) in [b"native-fixture-sha256".as_slice(),b"native-fixture-blake2b256",
            b"witness-sha256",b"witness-blake2b256"].into_iter().zip(admitted){prepared.append_bytes(label,pin);}
        for (label,value) in [b"role-index".as_slice(),b"headers",b"slot-log",b"input-log",
            b"row-log",b"local-input-log",b"base-row-log",b"family-log",b"member-count"].into_iter().zip(geometry){
            prepared.append_u64(label,*value);
        }
        for i in 0..40{
            prepared.append_u64(b"member-tag",i as u64);prepared.append_bytes(b"member-name",tags[i].as_bytes());
            prepared.append_u64(b"member-stride-log",strides[i]as u64);
            prepared.append_u64(b"member-terms",counts[i].0);prepared.append_u64(b"member-rows",counts[i].1);
        }
        prepared.append_bytes(b"left-counts-sha256",&bytes32("30EF6B91BEFDCDE58C543CC6566FDFDB99A87BC30C7EDFC801D4E1D5F877961B")?);
        Ok(prepared)
    }
    fn transaction<R>(caller:&mut Transcript,working:&Transcript,close:impl FnOnce()->Result<R,String>)->Result<R,String>{
        let result=close()?;*caller=working.clone();Ok(result)
    }
    fn close_consumers<R>(proof:&GkrProof,claim:&InputClaim,prepared:&Transcript,working:&Transcript,
        caller:&mut Transcript,observe:&mut impl FnMut(&'static str,bool)->Result<(),String>,
        wiring:impl Fn(&[Fr],&[Fr],&[Fr])->Result<[Fr;4],String>,
        evaluate:impl FnOnce(&[Fr])->Result<Fr,String>,
        consumer:impl FnOnce(&[u8],&InputClaim,Fr,&Transcript)->Result<R,String>,
    )->Result<(R,Vec<u8>),String>{
        require_fresh(caller)?;
        if prepared.challenges()!=0||prepared.raw_queries()!=0{return Err("role2 full prepared prefix advanced".into());}
        observe("codec",true)?;
        if proof.layers.len()!=1||proof.layers[0].rounds.len()!=64
            ||proof.layers[0].rounds.iter().any(|r|r.len()!=3)||proof.layers[0].line_coefficients.len()!=33{
            return Err("role2 full proof shape".into());
        }
        let encoded=crate::gkr::encode_proof(proof)?;
        if encoded.len()!=7264{return Err("role2 full proof extent".into());}
        let decoded=crate::gkr::decode_dimensions(&[32],&encoded)?;
        if crate::gkr::encode_proof(&decoded)?!=encoded{return Err("role2 full canonical re-encode".into());}
        observe("codec",false)?;observe("verify",true)?;
        let mut verifier=Transcript::new(DOMAIN);let prefix=prepared.clone();
        let verified=crate::gkr::verify_with_wiring(&[32],1usize<<32,&decoded,&mut verifier,move|t|*t=prefix,
            |layer,r,u,v|if layer==0{wiring(r,u,v).map_err(|_|crate::gkr::GkrError::PointDimension)}
                else{Err(crate::gkr::GkrError::PointDimension)}).map_err(|e|e.to_string())?;
        if &verified!=claim{return Err("role2 full verified claim differs".into());}
        if verifier.challenges()!=97||fingerprint(&verifier)?!=fingerprint(working)?{
            return Err("role2 full verified transcript differs".into());
        }
        observe("verify",false)?;observe("mle",true)?;
        let source_mle=evaluate(&verified.point)?;
        if source_mle!=verified.value{return Err("role2 full held-source MLE differs".into());}
        observe("mle",false)?;
        let result=transaction(caller,working,||consumer(&encoded,&verified,source_mle,&verifier))?;
        Ok((result,encoded))
    }
    fn native_plan_identity(candidate:&Candidate,descriptors:&[Descriptor],geometry:[u64;5],
        parent_root:&[u8],parent_total:&[u8])->Result<(),String>{
        if geometry!=[3073,4096,12,34,3]||descriptors.len()!=7||candidate.n!=3073
            ||candidate.root!=bytes32("DF3C1D555FCF6D2A5BA620422D1007A85CA5F8968D6F608C9856CE326C448913")?
            ||candidate.root.as_slice()!=parent_root||candidate.total.as_slice()!=parent_total
            ||candidate.total.as_slice()!=&bytes32(concat!("00000000","000000000000000000000000000000000000000000564F0B9B000000"))?[4..]
            ||candidate.tip!=bytes32("CC394AC0D406F45679111927B422B454EFA97648015FE5AEC52EA9B54EAF53DC")?
            ||candidate.tip_time!=1562018269889{return Err("role2 full native plan identity".into());}
        let d=&descriptors[2];
        if descriptors.iter().enumerate().any(|(i,d)|d.role!=i||d.input_log!=INPUT_LOGS[i]
            ||d.row_log!=ROW_LOGS[i]||d.name!=NAMES[i]||d.source!=SOURCE)
            ||d.mapping!="source member local26+tag6; original endpoints"||d.zero_extension.is_some()
            ||d.public_dependency!="same parent n/root/total/source profile"{
            return Err("role2 full native plan identity".into());}Ok(())
    }
    fn prepared_identity(prepared:&Transcript,expected:&Transcript)->Result<(),String>{
        if fingerprint(prepared)?!=fingerprint(expected)?{return Err("role2 full prepared identity differs".into());}Ok(())
    }
    impl NativePrefixAuthPlan<'_>{
        fn require_role2_full_plan(&self)->Result<(),String>{
            self.selection.validate()?;
            native_plan_identity(&self.candidate,&self.descriptors,[self.parent.headers(),self.parent.slots()as u64,
                self.parent.slot_log()as u64,self.parent.topology().families.len()as u64,
                self.parent.work_boundary().links().len()as u64],&self.parent.descriptor().root,&self.parent.work_profile().total_be28)
        }
        pub(crate) fn prepare_role2_full_binding_for_test(&self,pre:&Transcript,counts:&[(u64,u64);40],
            strides:&[usize;40])->Result<Transcript,String>{
            prepare_role2_full_artifact_binding(self,pre,counts,strides)
        }
        pub(crate) fn close_role2_full_for_test<R>(&self,source:&crate::packed::PackedFile,
            proof:&GkrProof,claim:&InputClaim,prepared:&Transcript,working:&Transcript,caller:&mut Transcript,
            observe:&mut impl FnMut(&'static str,bool)->Result<(),String>,
            consumer:impl FnOnce(&[u8],&InputClaim,Fr,&Transcript)->Result<R,String>,
        )->Result<(R,Vec<u8>),String>{
            if source.input_len()!=1usize<<32{return Err("role2 full source dimension".into());}
            source.native_role0_view()?.require_same_source(source)?;
            let counts=std::array::from_fn(|i|(MEMBERS[i].2,MEMBERS[i].3));
            let strides=std::array::from_fn(|i|MEMBERS[i].1);
            let expected=self.prepare_role2_full_binding_for_test(caller,&counts,&strides)?;
            prepared_identity(prepared,&expected)?;
            close_consumers(proof,claim,prepared,working,caller,observe,|r,u,v|self.coefficients(2,r,u,v),
                |point|source.evaluate(point),consumer)
        }
    }
    pub(super) fn role2_full_transcript()->Transcript{Transcript::new(DOMAIN)}
    pub(super) fn prepare_role2_full_artifact_binding(plan:&NativePrefixAuthPlan<'_>,pre:&Transcript,
        counts:&[(u64,u64);40],strides:&[usize;40])->Result<Transcript,String>{
        require_fresh(pre)?;plan.require_role2_full_plan()?;native_role5_common::binding_json_preflight(plan)?;
        let mut prepared=metadata(pre,&GEOMETRY,&plan.descriptors[2].ordered_tags,counts,strides,&pins()?)?;
        plan.bind_plan_identity(&mut prepared)?;
        if prepared.challenges()!=0||prepared.raw_queries()!=0{return Err("role2 full binding sampled challenge".into());}
        Ok(prepared)
    }
    pub(super) fn prepare_role2_full_verifier_binding(plan:&NativePrefixAuthPlan<'_>,pre:&Transcript)->Result<Transcript,String>{
        let counts=std::array::from_fn(|i|(MEMBERS[i].2,MEMBERS[i].3));
        let strides=std::array::from_fn(|i|MEMBERS[i].1);
        prepare_role2_full_artifact_binding(plan,pre,&counts,&strides)
    }
    pub(crate) fn role2_full_binding_controls_for_test()->Result<(),String>{
        let pre=Transcript::new(DOMAIN);let before=fingerprint(&pre)?;
        let tags:Vec<String>=MEMBERS.iter().map(|m|m.0.to_owned()).collect();
        let counts:Vec<_>=MEMBERS.iter().map(|m|(m.2,m.3)).collect();
        let strides:Vec<_>=MEMBERS.iter().map(|m|m.1).collect();let admitted=pins()?;
        let prepared=metadata(&pre,&GEOMETRY,&tags,&counts,&strides,&admitted)?;
        if prepared.challenges()!=0||prepared.raw_queries()!=0||fingerprint(&pre)?!=before
            ||prepared.bytes_absorbed()<=pre.bytes_absorbed(){return Err("role2 full binding positive".into());}
        for i in 0..GEOMETRY.len(){let mut bad=GEOMETRY;bad[i]^=1;
            if metadata(&pre,&bad,&tags,&counts,&strides,&admitted).err().unwrap_or_default()!="role2 full metadata geometry"{
                return Err("role2 full geometry negative".into());}}
        let mut wrong=tags.clone();wrong.swap(34,35);
        if metadata(&pre,&GEOMETRY,&wrong,&counts,&strides,&admitted).err().unwrap_or_default()!="role2 full metadata tag order"{
            return Err("role2 full tag negative".into());}
        for kind in 0..3{
            let error=match kind{0=>metadata(&pre,&GEOMETRY,&tags[..39],&counts,&strides,&admitted).err(),
                1=>metadata(&pre,&GEOMETRY,&tags,&counts[..39],&strides,&admitted).err(),
                _=>metadata(&pre,&GEOMETRY,&tags,&counts,&strides[..39],&admitted).err()};
            if error.as_deref()!=Some("role2 full metadata count"){return Err("role2 full count negative".into());}
        }
        for i in 0..40{
            let mut wrong=strides.clone();wrong[i]^=1;
            if metadata(&pre,&GEOMETRY,&tags,&counts,&wrong,&admitted).err().unwrap_or_default()!="role2 full metadata stride"{
                return Err("role2 full stride negative".into());}
            for field in 0..2{let mut wrong=counts.clone();if field==0{wrong[i].0^=1;}else{wrong[i].1^=1;}
                if metadata(&pre,&GEOMETRY,&tags,&wrong,&strides,&admitted).err().unwrap_or_default()!="role2 full metadata term/row count"{
                    return Err("role2 full term/row negative".into());}}
        }
        for i in 0..4{let mut wrong=admitted;wrong[i][0]^=1;
            if metadata(&pre,&GEOMETRY,&tags,&counts,&strides,&wrong).err().unwrap_or_default()!="role2 full admitted pins"{
                return Err("role2 full pin negative".into());}}
        let wrong=Transcript::new(b"native-prefix-role2-u0-diagnostic-v1");
        if metadata(&wrong,&GEOMETRY,&tags,&counts,&strides,&admitted).err().unwrap_or_default()!="role2 full diagnostic domain/prefix"{
            return Err("role2 full domain negative".into());}
        let mut late=pre.clone();late.try_challenge_scalar(b"late")?;let late_before=fingerprint(&late)?;
        if metadata(&late,&GEOMETRY,&tags,&counts,&strides,&admitted).err().unwrap_or_default()!="role2 full binding after challenge"
            ||fingerprint(&late)?!=late_before||fingerprint(&pre)?!=before{return Err("role2 full binding rollback negative".into());}
        let candidate=Candidate{n:3073,root:bytes32("DF3C1D555FCF6D2A5BA620422D1007A85CA5F8968D6F608C9856CE326C448913")?,
            total:bytes32(concat!("00000000","000000000000000000000000000000000000000000564F0B9B000000"))?[4..].try_into().map_err(|_|"role2 fixture total extent")?,
            tip:bytes32("CC394AC0D406F45679111927B422B454EFA97648015FE5AEC52EA9B54EAF53DC")?,tip_time:1562018269889};
        let descriptors:[Descriptor;7]=std::array::from_fn(|role|Descriptor{role,name:NAMES[role],source:SOURCE,
            input_log:INPUT_LOGS[role],row_log:ROW_LOGS[role],ordered_tags:Vec::new(),
            mapping:if role==2{"source member local26+tag6; original endpoints"}else{"fixture"},
            zero_extension:None,public_dependency:"same parent n/root/total/source profile"});
        let shape=[3073,4096,12,34,3];
        native_plan_identity(&candidate,&descriptors,shape,&candidate.root,&candidate.total)?;
        for fault in 0..50{
            let mut c=candidate.clone();let mut d=descriptors.clone();let mut g=shape;
            let mut root=candidate.root;let mut total=candidate.total;
            match fault{
                0=>c.n-=1,1=>c.root[0]^=1,2=>c.total[0]^=1,3=>c.tip[0]^=1,4=>c.tip_time+=1,
                5..=9=>g[fault-5]^=1,10=>root[0]^=1,11=>total[0]^=1,
                12=>d[2].mapping="wrong",13=>d[2].zero_extension=Some((0,1)),14=>d[2].public_dependency="wrong",
                _=>{let index=(fault-15)/5;match (fault-15)%5{
                    0=>d[index].role^=1,1=>d[index].input_log^=1,2=>d[index].row_log^=1,
                    3=>d[index].name="wrong",_=>d[index].source="wrong"}}
            }
            if native_plan_identity(&c,&d,g,&root,&total).err().as_deref()!=Some("role2 full native plan identity"){
                return Err(format!("role2 full identity fault{fault}"));}
        }
        if native_plan_identity(&candidate,&descriptors[..6],shape,&candidate.root,&candidate.total).is_ok(){
            return Err("role2 full missing descriptor accepted".into());}
        prepared_identity(&prepared,&prepared)?;
        let mut wrong=prepared.clone();wrong.append_bytes(b"changed",b"prefix");
        if prepared_identity(&wrong,&prepared).err().as_deref()!=Some("role2 full prepared identity differs")
            ||fingerprint(&pre)?!=before{return Err("role2 full prepared prefix negative".into());}
        Ok(())
    }
    pub(crate) fn role2_full_transaction_controls_for_test()->Result<(),String>{
        let initial=Transcript::new(DOMAIN);let before=fingerprint(&initial)?;
        let mut prepared=initial.clone();prepared.append_bytes(b"fixture",b"zero relation; consumer boundary only");
        let proof=GkrProof{layers:vec![crate::gkr::LayerProof{rounds:vec![vec![Fr::zero();3];64],
            left_value:Fr::zero(),right_value:Fr::zero(),line_coefficients:vec![Fr::zero();33]}]};
        let mut working=initial.clone();let prefix=prepared.clone();
        let claim=crate::gkr::verify_with_wiring(&[32],1usize<<32,&proof,&mut working,move|t|*t=prefix,
            |_,_,_,_|Ok([Fr::zero();4])).map_err(|e|e.to_string())?;
        let mut caller=initial.clone();let mut marks=Vec::new();
        let (value,bytes)=close_consumers(&proof,&claim,&prepared,&working,&mut caller,&mut|s,b|{marks.push((s,b));Ok(())},
            |_,_,_|Ok([Fr::zero();4]),|_|Ok(Fr::zero()),|_,_,_,_|Ok(7usize))?;
        if value!=7||bytes.len()!=7264||fingerprint(&caller)?!=fingerprint(&working)?
            ||marks!=vec![("codec",true),("codec",false),("verify",true),("verify",false),("mle",true),("mle",false)]{
            return Err("role2 full consumer positive".into());}
        // Each independent late boundary uses the real consumer pipeline and commit helper.
        for fault in 0..11{
            let mut caller=initial.clone();let mut p=proof.clone();let mut c=claim.clone();let mut w=working.clone();
            match fault{0=>{p.layers[0].rounds.pop();},1=>{p.layers[0].rounds[5][1]+=Fr::one();},
                2=>{p.layers[0].left_value+=Fr::one();},3=>{p.layers[0].line_coefficients[4]+=Fr::one();},
                4=>{c.point[3]+=Fr::one();},5=>{c.value+=Fr::one();},6=>{w.append_bytes(b"fault",b"late");},_=>{}}
            let result=close_consumers(&p,&c,&prepared,&w,&mut caller,
                &mut|s,b|if fault==7&&s=="mle"&&!b{Err("observer late failure".into())}else{Ok(())},
                |_,_,_|Ok([Fr::zero();4]),
                |_|if fault==8{Err("held source failure".into())}else if fault==9{Ok(Fr::one())}else{Ok(Fr::zero())},
                |_,_,_,_|if fault==10{Err("custody/consumer late failure".into())}else{Ok(())});
            let expected=["role2 full proof shape","GKR error: SumcheckIdentity","GKR error: LineEndpoints",
                "GKR error: LineEndpoints","role2 full verified claim differs","role2 full verified claim differs",
                "role2 full verified transcript differs","observer late failure","held source failure",
                "role2 full held-source MLE differs","custody/consumer late failure"][fault];
            if result.err().as_deref()!=Some(expected)||fingerprint(&caller)?!=before{
                return Err(format!("role2 full isolated rollback fault{fault}"));}
        }
        Ok(())
    }
}

// source28-role6-admission-BEGIN
#[cfg(test)]
pub(crate) use native_role6_full::{NativeRole6Admission,role6_full_controls_for_test};
#[cfg(test)]
mod native_role6_full {
    use super::*;
    const DOMAIN:&[u8]=b"native-prefix-role6-direct-full-diagnostic-v1";
    const NEXT:&[u8]=b"native-role6-direct-full-continuation-v1";
    const SHAPE:[u64;9]=[6,3073,4096,12,32,24,20,12,0];
    fn hex(s:&str)->Result<Vec<u8>,String>{if s.len()%2!=0{return Err("role6 pin encoding".into());}
        (0..s.len()).step_by(2).map(|i|u8::from_str_radix(&s[i..i+2],16).map_err(|_|"role6 pin encoding".into())).collect()}
    fn fingerprint(t:&Transcript)->Result<([u64;3],Fr),String>{Ok(([t.challenges(),t.raw_queries(),t.bytes_absorbed()],t.clone().try_challenge_scalar(NEXT)?))}
    fn fresh(t:&Transcript)->Result<(),String>{if fingerprint(t)?!=fingerprint(&Transcript::new(DOMAIN))?{
        return Err("role6 binding domain/prefix".into());}Ok(())}
    fn prepared_equal(prepared:&Transcript,expected:&Transcript)->Result<(),String>{
        if fingerprint(prepared)?!=fingerprint(expected)?{return Err("role6 prepared identity".into());}Ok(())}
    fn fields(shape:&[u64;9],candidate:&Candidate,descriptors:&[Descriptor],root:&[u8],total:&[u8])->Result<(),String>{
        if shape!=&SHAPE||candidate.n!=3073||candidate.root.as_slice()!=root||candidate.total.as_slice()!=total
            ||candidate.root.as_slice()!=hex("DF3C1D555FCF6D2A5BA620422D1007A85CA5F8968D6F608C9856CE326C448913")?
            ||candidate.total.as_slice()!=hex("000000000000000000000000000000000000000000564F0B9B000000")?
            ||candidate.tip.as_slice()!=hex("CC394AC0D406F45679111927B422B454EFA97648015FE5AEC52EA9B54EAF53DC")?
            ||candidate.tip_time!=1562018269889||descriptors.len()!=7{
            return Err("role6 native identity".into());}
        for (i,d)in descriptors.iter().enumerate(){if d.role!=i||d.name!=NAMES[i]||d.source!=SOURCE||d.input_log!=INPUT_LOGS[i]||d.row_log!=ROW_LOGS[i]{
            return Err("role6 native descriptor".into());}}
        let d=&descriptors[6];if d.mapping!="active owner row12; terminal time"||d.zero_extension.is_some()
            ||d.public_dependency!="candidate-tip-time"||d.ordered_tags.len()!=1||d.ordered_tags[0]!="metadata-order"{
            return Err("role6 native descriptor".into());}Ok(())
    }
    pub(crate) struct NativeRole6Admission<'p,'s>{plan:&'p NativePrefixAuthPlan<'s>,source:&'p crate::packed::PackedFile,
        context:&'p NativeRole0DiagnosticContext,shape:[u64;9]}
    impl<'s> NativePrefixAuthPlan<'s>{
        fn role6_identity(&self,shape:&[u64;9])->Result<(),String>{self.selection.validate()?;
            fields(shape,&self.candidate,&self.descriptors,&self.parent.descriptor().root,&self.parent.work_profile().total_be28)?;
            if self.parent.headers()!=3073||self.parent.slots()!=4096||self.parent.slot_log()!=12||self.parent.topology().families.len()!=34
                ||self.parent.work_boundary().links().len()!=3||self.metadata.n()!=3073||self.metadata.slot_log()!=12||self.metadata.input_log()!=32
                ||self.metadata.row_log()!=24||self.metadata.term_count()!=7181857{return Err("role6 native parent geometry".into());}
            self.metadata.role6_endpoint_shape_for_test()
        }
        pub(crate) fn admit_role6_for_test<'p,R:std::io::Read+std::io::Seek>(&'p self,source:&'p crate::packed::PackedFile,
            context:&'p NativeRole0DiagnosticContext,reference:&mut R)->Result<NativeRole6Admission<'p,'s>,String>{
            self.role6_identity(&SHAPE)?;context.validate()?;native_role5_common::binding_json_preflight(self)?;
            let view=source.native_role0_view()?;view.require_same_source(source)?;
            let digest=native_role5_common::compare_reference(reference,4096,|owner,expected|{
                let packet=view.read_copy(owner)?;if packet.capacity_bytes()!=131072||!packet.matches_bytes(expected){return Err("role6 held source/reference mismatch".into());}Ok(())})?;
            native_role5_common::require_witness_digest(digest)?;
            Ok(NativeRole6Admission{plan:self,source,context,shape:SHAPE})
        }
    }
    impl NativeRole6Admission<'_,'_>{
        pub(crate) fn require_source(&self,source:&crate::packed::PackedFile)->Result<(),String>{
            if !std::ptr::eq(source,self.source){return Err("role6 detached source".into());}
            self.validate()?;self.source.native_role0_view()?.require_same_source(source)
        }
        fn validate(&self)->Result<(),String>{self.plan.role6_identity(&self.shape)?;self.context.validate()?;
            if self.source.input_len()!=1usize<<32{return Err("role6 native source width".into());}Ok(())}
        pub(crate) fn visit(&self,left:bool,owner:usize,stats:&mut crate::header_metadata_order_layout::Role6EndpointStats,
            sink:&mut dyn FnMut(crate::sparse_stream_roster::EdgeTerm)->Result<(),String>)->Result<(),String>{
            self.validate()?;self.plan.metadata.visit_endpoint_for_test(left,owner,stats,sink)
        }
        pub(crate) fn prepare(&self,caller:&Transcript)->Result<Transcript,String>{
            fresh(caller)?;self.validate()?;Self::prepare_role6_artifact_binding(self.plan,self.context,&self.shape,caller)
        }
        pub(super) fn role6_full_transcript()->Transcript{Transcript::new(DOMAIN)}
        pub(super) fn prepare_role6_artifact_binding(plan:&NativePrefixAuthPlan<'_>,context:&NativeRole0DiagnosticContext,
            shape:&[u64;9],caller:&Transcript)->Result<Transcript,String>{
            fresh(caller)?;plan.role6_identity(shape)?;context.validate()?;native_role5_common::binding_json_preflight(plan)?;
            let mut prepared=caller.clone();context.bind_admission(&mut prepared)?;
            for n in shape{prepared.append_u64(b"role6-geometry",*n);}
            for (label,n)in [(b"terms".as_slice(),7181857u64),(b"rows",6499651),(b"nonlinear",3933440)]{prepared.append_u64(label,n);}
            for pin in ["ABB3D74AE75256CED63110B72C2E0D5EBA1B90B09889E45EA327BDA1C9A640D2","8CDB90DA475E646280113D97C9469BE7EB86A1D04F20404C64239187284FC009",
                "C1CC1CF72FF539F259A3BDEF756332BA52CB8AFF26C11AB4116D1B2F9D17ED43","725D7B1215E1185C52C1012D9294260612653ACAD53A02429B8EAAFD0F0770C8",
                "8CA65C0B38F5E600ABA12C728F98F02D1B34A1056EAC79C75E7EFF324EF2F1A1"]{prepared.append_bytes(b"role6-identity-pin",&hex(pin)?);}
            plan.bind_plan_identity(&mut prepared)?;
            if prepared.challenges()!=0||prepared.raw_queries()!=0{return Err("role6 prepared challenge".into());}Ok(prepared)
        }
        pub(crate) fn close<R>(&self,source:&crate::packed::PackedFile,proof:&GkrProof,claim:&InputClaim,prepared:&Transcript,
            working:&Transcript,caller:&mut Transcript,observe:&mut impl FnMut(&'static str,bool)->Result<(),String>,
            consumer:impl FnOnce(&[u8],&InputClaim,Fr,&Transcript)->Result<R,String>)->Result<(R,Vec<u8>),String>{
            self.require_source(source)?;prepared_equal(prepared,&self.prepare(caller)?)?;
            consumers(proof,claim,prepared,working,caller,observe,|r,u,v|self.plan.coefficients(6,r,u,v),|p|source.evaluate(p),consumer)
        }
        pub(crate) fn native_controls(&self,detached:&crate::packed::PackedFile)->Result<(),String>{
            self.require_source(self.source)?;if self.require_source(detached).err().as_deref()!=Some("role6 detached source"){return Err("role6 detached control".into());}
            for i in 0..9{let mut wrong=Self{plan:self.plan,source:self.source,context:self.context,shape:self.shape};wrong.shape[i]^=1;
                if wrong.validate().err().as_deref()!=Some("role6 native identity"){return Err(format!("role6 actual admission shape{i}"));}}
            let caller=Transcript::new(DOMAIN);let before=fingerprint(&caller)?;let prepared=self.prepare(&caller)?;
            let mut foreign=prepared.clone();foreign.append_bytes(b"foreign",b"prepared");
            if prepared_equal(&foreign,&prepared).err().as_deref()!=Some("role6 prepared identity"){return Err("role6 actual prepared control".into());}
            let mut advanced=caller.clone();advanced.try_challenge_scalar(b"late")?;
            if self.prepare(&advanced).err().as_deref()!=Some("role6 binding domain/prefix"){return Err("role6 late control".into());}
            let mut prior=caller.clone();prior.append_bytes(b"prior",b"append");
            if self.prepare(&prior).err().as_deref()!=Some("role6 binding domain/prefix")||fingerprint(&caller)?!=before||prepared.challenges()!=0{return Err("role6 binding controls".into());}
            let mut stats=crate::header_metadata_order_layout::Role6EndpointStats::default();
            if self.visit(true,4096,&mut stats,&mut |_|Ok(())).err().as_deref()!=Some("role6 endpoint owner range")||stats.source_emitter_calls!=0{return Err("role6 owner control".into());}Ok(())
        }
    }
    fn consumers<R>(proof:&GkrProof,claim:&InputClaim,prepared:&Transcript,working:&Transcript,caller:&mut Transcript,
        observe:&mut impl FnMut(&'static str,bool)->Result<(),String>,wiring:impl Fn(&[Fr],&[Fr],&[Fr])->Result<[Fr;4],String>,
        evaluate:impl FnOnce(&[Fr])->Result<Fr,String>,consumer:impl FnOnce(&[u8],&InputClaim,Fr,&Transcript)->Result<R,String>)->Result<(R,Vec<u8>),String>{
        fresh(caller)?;if prepared.challenges()!=0||prepared.raw_queries()!=0{return Err("role6 prepared advanced".into());}observe("codec",true)?;
        if proof.layers.len()!=1||proof.layers[0].rounds.len()!=64||proof.layers[0].rounds.iter().any(|r|r.len()!=3)
            ||proof.layers[0].line_coefficients.len()!=33{return Err("role6 full proof shape".into());}
        let encoded=crate::gkr::encode_proof(proof)?;if encoded.len()!=7264{return Err("role6 full proof extent".into());}
        let decoded=crate::gkr::decode_dimensions(&[32],&encoded)?;if crate::gkr::encode_proof(&decoded)?!=encoded{return Err("role6 canonical codec".into());}
        observe("codec",false)?;observe("verify",true)?;let mut verifier=Transcript::new(DOMAIN);let prefix=prepared.clone();
        let verified=crate::gkr::verify_with_wiring(&[32],1usize<<24,&decoded,&mut verifier,move|t|*t=prefix,
            |layer,r,u,v|if layer==0{wiring(r,u,v).map_err(|_|crate::gkr::GkrError::PointDimension)}else{Err(crate::gkr::GkrError::PointDimension)}).map_err(|e|e.to_string())?;
        if &verified!=claim{return Err("role6 verified claim differs".into());}
        if verifier.challenges()!=89||fingerprint(&verifier)?!=fingerprint(working)?{return Err("role6 verified transcript differs".into());}
        observe("verify",false)?;observe("mle",true)?;let value=evaluate(&verified.point)?;
        if value!=verified.value{return Err("role6 held MLE differs".into());}observe("mle",false)?;
        let result=consumer(&encoded,&verified,value,&verifier)?;*caller=working.clone();Ok((result,encoded))
    }
    pub(crate) fn role6_full_controls_for_test()->Result<(),String>{
        let candidate=Candidate{n:3073,root:hex("DF3C1D555FCF6D2A5BA620422D1007A85CA5F8968D6F608C9856CE326C448913")?.try_into().map_err(|_|"role6 fixture root")?,
            total:hex("000000000000000000000000000000000000000000564F0B9B000000")?.try_into().map_err(|_|"role6 fixture total")?,
            tip:hex("CC394AC0D406F45679111927B422B454EFA97648015FE5AEC52EA9B54EAF53DC")?.try_into().map_err(|_|"role6 fixture tip")?,tip_time:1562018269889};
        let descriptors:[Descriptor;7]=std::array::from_fn(|role|Descriptor{role,name:NAMES[role],source:SOURCE,input_log:INPUT_LOGS[role],row_log:ROW_LOGS[role],
            ordered_tags:if role==6{vec!["metadata-order".into()]}else{Vec::new()},mapping:if role==6{"active owner row12; terminal time"}else{"fixture"},
            zero_extension:None,public_dependency:if role==6{"candidate-tip-time"}else{"fixture"}});
        fields(&SHAPE,&candidate,&descriptors,&candidate.root,&candidate.total)?;
        for fault in 0..56{let mut c=candidate.clone();let mut d=descriptors.clone();let mut shape=SHAPE;let mut root=candidate.root;let mut total=candidate.total;
            let expected=if fault<16{"role6 native identity"}else{"role6 native descriptor"};
            match fault{0..=8=>shape[fault]^=1,9=>c.n-=1,10=>c.root[0]^=1,11=>c.total[0]^=1,12=>c.tip[0]^=1,13=>c.tip_time+=1,
                14=>root[0]^=1,15=>total[0]^=1,16=>d[6].mapping="wrong",17=>d[6].public_dependency="wrong",18=>d[6].zero_extension=Some((0,1)),
                19=>d[6].ordered_tags[0].push_str("-wrong"),20=>d[6].ordered_tags.clear(),
                _=>{let i=(fault-21)/5;match(fault-21)%5{0=>d[i].role^=1,1=>d[i].input_log^=1,2=>d[i].row_log^=1,3=>d[i].name="wrong",_=>d[i].source="wrong"}}}
            if fields(&shape,&c,&d,&root,&total).err().as_deref()!=Some(expected){return Err(format!("role6 fields fault{fault}"));}}
        if fields(&SHAPE,&candidate,&descriptors[..6],&candidate.root,&candidate.total).err().as_deref()!=Some("role6 native identity"){return Err("role6 missing descriptor control".into());}
        let initial=Transcript::new(DOMAIN);let before=fingerprint(&initial)?;let mut prepared=initial.clone();prepared.append_bytes(b"fixture",b"zero relation; consumer only");
        prepared_equal(&prepared,&prepared)?;let mut foreign=prepared.clone();foreign.append_bytes(b"changed",b"prefix");
        if prepared_equal(&foreign,&prepared).err().as_deref()!=Some("role6 prepared identity"){return Err("role6 prepared control".into());}
        let proof=GkrProof{layers:vec![crate::gkr::LayerProof{rounds:vec![vec![Fr::zero();3];64],left_value:Fr::zero(),right_value:Fr::zero(),line_coefficients:vec![Fr::zero();33]}]};
        let bytes=crate::gkr::encode_proof(&proof)?;
        for size in [bytes.len()-1,bytes.len()+1]{let mut wrong=bytes.clone();wrong.resize(size,0);
            let expected=format!("GKR proof length: expected 7264, received {size}");
            if crate::gkr::decode_dimensions(&[32],&wrong).err().as_deref()!=Some(expected.as_str()){return Err("role6 codec size control".into());}}
        let mut noncanonical=bytes.clone();noncanonical[..32].fill(255);
        use ark_serialize::CanonicalDeserialize;
        let expected=Fr::deserialize_compressed(&noncanonical[..32]).err().ok_or("role6 noncanonical fixture")?.to_string();
        if crate::gkr::decode_dimensions(&[32],&noncanonical).err().as_deref()!=Some(expected.as_str()){return Err("role6 codec scalar control".into());}
        let mut working=initial.clone();let prefix=prepared.clone();let claim=crate::gkr::verify_with_wiring(&[32],1usize<<24,&proof,&mut working,
            move|t|*t=prefix,|_,_,_,_|Ok([Fr::zero();4])).map_err(|e|e.to_string())?;
        let mut caller=initial.clone();consumers(&proof,&claim,&prepared,&working,&mut caller,&mut|_,_|Ok(()),|_,_,_|Ok([Fr::zero();4]),|_|Ok(Fr::zero()),|_,_,_,_|Ok(()))?;
        if fingerprint(&caller)?!=fingerprint(&working)?{return Err("role6 consumer positive".into());}
        for fault in 0..11{let mut caller=initial.clone();let mut p=proof.clone();let mut c=claim.clone();let mut w=working.clone();
            match fault{0=>{p.layers[0].rounds.pop();},1=>p.layers[0].rounds[5][1]+=Fr::one(),2=>p.layers[0].left_value+=Fr::one(),
                3=>p.layers[0].line_coefficients[4]+=Fr::one(),4=>c.point[3]+=Fr::one(),5=>c.value+=Fr::one(),6=>w.append_bytes(b"changed",b"sender"),_=>{}}
            let result=consumers(&p,&c,&prepared,&w,&mut caller,&mut|s,b|if fault==7&&s=="mle"&&!b{Err("role6 late observer".into())}else{Ok(())},
                |_,_,_|Ok([Fr::zero();4]),|_|if fault==8{Err("role6 source read".into())}else if fault==9{Ok(Fr::one())}else{Ok(Fr::zero())},
                |_,_,_,_|if fault==10{Err("role6 custody/export".into())}else{Ok(())});
            let expected=["role6 full proof shape","GKR error: SumcheckIdentity","GKR error: LineEndpoints","GKR error: LineEndpoints",
                "role6 verified claim differs","role6 verified claim differs","role6 verified transcript differs","role6 late observer","role6 source read","role6 held MLE differs","role6 custody/export"][fault];
            if result.err().as_deref()!=Some(expected)||fingerprint(&caller)?!=before{return Err(format!("role6 rollback fault{fault}"));}}
        let mut prior=initial.clone();prior.append_bytes(b"prior",b"bytes");if fresh(&prior).err().as_deref()!=Some("role6 binding domain/prefix"){return Err("role6 prior prefix control".into());}
        Ok(())
    }
}
// source28-role6-admission-END

pub(crate) struct NativePrefixAuthPlan<'a> {
    parent: &'a WorkTreeHistoryPlan,
    height: HeightWork<'a>, daa: DaaHistoryRoster<'a>,
    adjacency: HeaderAdjacencyLayout, metadata: HeaderMetadataOrderLayout,
    points: point_membership::Compiled, point_shape: Shape,
    selection: Selection, candidate: Candidate, descriptors: [Descriptor;7],
}
impl<'a> NativePrefixAuthPlan<'a> {
    pub(crate) fn compile(parent: &'a WorkTreeHistoryPlan, selection: Selection,
        candidate: Candidate) -> Result<Self,String> {
        selection.validate()?; // Before any factory.
        if candidate.n != N || parent.headers()!=N || parent.slot_log()!=H || parent.slots()!=4096
            || parent.descriptor().root!=candidate.root
            || parent.work_profile().total_be28!=candidate.total {
            return Err("native prefix candidate/borrowed parent mismatch".into());
        }
        parent.fixed_profile().validate()?;
        if parent.fixed_profile().genesis!=selection.genesis
            || parent.fixed_profile().prefix.as_slice()!=fixed::PROFILE_PREFIX {
            return Err("native prefix source profile mismatch".into());
        }
        let height=HeightWork::compile_history(parent)?;
        let daa=DaaHistoryRoster::compile(parent)?;
        let adjacency=HeaderAdjacencyLayout::compile(N,H,[0;32],candidate.tip)?;
        let metadata=HeaderMetadataOrderLayout::compile(N,H,candidate.tip_time)?;
        let points=point_membership::build()?;
        let point_shape=sparse::validate(&points.circuit,0).map_err(|e|e.to_string())?;
        if points.circuit.input_len!=8192 || points.circuit.row_count!=16384
            || points.circuit.terms.len()!=288158 || parent.core_pool().copy_bits()!=H
            || parent.core_pool().input_log()!=32 || parent.core_pool().row_log()!=33
            || parent.core_pool().term_count()!=7_771_258_880
            || height.row_log()!=18 || daa.row_log()!=31 || daa.input_log()!=32
            || adjacency.row_log()!=21 || metadata.row_log()!=24
            || adjacency.term_count()!=786944 || metadata.term_count()!=7181857
            || work_tree_wiring::full_roster_shape(parent.topology())?!=(26,6,32,32)
            || parent.topology().families.len()!=34 || parent.work_boundary().links().len()!=3 {
            return Err("native prefix reconstructed geometry drift".into());
        }
        let descriptors=std::array::from_fn(|role| {
            let ordered_tags=match role {
                0 => layout::CORE_OFFSETS.iter().map(|o|format!("core@{o}")).collect(),
                2 => parent.topology().families.iter().map(|f|f.name.clone())
                    .chain(["fixed".into(),"leaf".into(),"work-local".into()])
                    .chain(parent.work_boundary().links().iter().map(|f|f.name.clone())).collect(),
                4 => vec!["height+numeric".into(),"daa:arithmetic,aliases,numeric,inactive".into()],
                _ => vec![NAMES[role].into()],
            };
            Descriptor {role,name:NAMES[role],source:SOURCE,input_log:INPUT_LOGS[role],
                row_log:ROW_LOGS[role],ordered_tags,
                mapping:match role {0=>"row17+owner12+family4; input20+owner12",
                    2=>"source member local26+tag6; original endpoints",
                    3=>"row14+owner12; input13+owner12; bank96",
                    4=>"height18; daa31+base2^31; original endpoints",
                    5=>"active owner row9; terminal tip",6=>"active owner row12; terminal time",
                    _=>"retained owner row19; input20; source retirement"},
                zero_extension:if role==4 {Some((18,31))} else {None},
                public_dependency:match role {5=>"genesis-parent-zero/candidate-tip",
                    6=>"candidate-tip-time",_=>"same parent n/root/total/source profile"},}
        });
        Ok(Self {parent,height,daa,adjacency,metadata,points,point_shape,selection,candidate,descriptors})
    }
    pub(crate) fn descriptors(&self) -> &[Descriptor;7] { &self.descriptors }
    pub(crate) fn height(&self) -> &HeightWork<'a> { &self.height }
    pub(crate) fn daa(&self) -> &DaaHistoryRoster<'a> { &self.daa }
    pub(crate) fn validate_descriptor(&self, role: usize, claimed: &Descriptor) -> Result<(),String> {
        if self.descriptors.get(role)!=Some(claimed) {return Err("reconstructed role descriptor mismatch".into());}
        Ok(())
    }
    pub(crate) fn validate_roster(&self, claimed: &[Descriptor]) -> Result<(),String> {
        if claimed!=self.descriptors.as_slice() {return Err("missing/duplicate/reordered/trailing role record".into());}
        Ok(())
    }
    pub(crate) fn validate_candidate(&self, claimed: &Candidate) -> Result<(),String> {
        if claimed!=&self.candidate {return Err("candidate changed after plan binding".into());} Ok(())
    }
    pub(crate) fn project_claim(&self, role: usize, point: &[Fr]) -> Result<Vec<Fr>,String> {
        let descriptor=self.descriptors.get(role).ok_or("unknown native prefix role")?;
        if point.len()!=descriptor.input_log {return Err("native prefix claim dimension".into());}
        if role!=3 {return Ok(point.to_vec());}
        let mut out=point[..13].to_vec();
        out.extend([0u64,0,0,0,0,1,1].map(Fr::from)); out.extend_from_slice(&point[13..]);
        Ok(out)
    }
    pub(crate) fn point_global_wire(&self,owner:usize,local:usize)->Result<usize,String> {
        if owner>=4096 || local>=8192 {return Err("point owner/local outside source bank".into());}
        owner.checked_mul(layout::WIDTH).and_then(|x|x.checked_add(786432))
            .and_then(|x|x.checked_add(local)).ok_or_else(||"point global coordinate overflow".into())
    }
    pub(crate) fn padding_heights(&self,owner:usize)->Result<(usize,Option<usize>),String> {
        if owner>=4096 {return Err("header padding owner outside source domain".into());}
        let height=(owner+1).min(N as usize);
        Ok((height,height.checked_sub(1).filter(|h|*h>0)))
    }
    /// Internal framing only. It is neither Encode(S) nor an admitted proof domain.
    pub(crate) fn bind_plan_identity(&self, t: &mut Transcript) -> Result<(),String> {
        if t.challenges()!=0 {return Err("native prefix binding after challenge".into());}
        self.selection.validate()?;
        t.append_bytes(b"native-source-plan",b"native-prefix-source-only-s12-seven-no-max-v1");
        t.append_bytes(b"source-revision",SOURCE.as_bytes());
        t.append_bytes(b"rules",b"draft-0.8/native-prefix-ell2/no-max");
        t.append_bytes(b"verifier",b"source-plan-only/no-key-admission");
        t.append_bytes(b"encoding",b"canonical-native-raw");
        t.append_bytes(b"genesis",&self.selection.genesis);
        for x in [self.selection.query_h,self.selection.ell,H as u64,96,self.candidate.n] {t.append_u64(b"selection",x);}
        t.append_bytes(b"candidate-root",&self.candidate.root);t.append_bytes(b"candidate-total",&self.candidate.total);
        t.append_bytes(b"candidate-tip",&self.candidate.tip);t.append_bytes(b"candidate-tip-time",&self.candidate.tip_time.to_le_bytes());
        for d in &self.descriptors {
            for x in [d.role,d.input_log,d.row_log,d.ordered_tags.len()] {t.append_u64(b"role-dimension",x as u64);}
            for s in [d.name,d.source,d.mapping,d.public_dependency] {t.append_bytes(b"role-string",s.as_bytes());}
            for s in &d.ordered_tags {t.append_bytes(b"ordered-tag",s.as_bytes());}
            if let Some((a,b))=d.zero_extension {t.append_u64(b"mask-count",2);t.append_u64(b"mask-start",a as u64);t.append_u64(b"mask-end",b as u64);}
            else {t.append_u64(b"mask-count",0);}
        }
        self.parent.bind(t);self.height.bind(t);self.daa.bind(t);
        work_tree_wiring::bind_full_roster(self.parent.topology(),self.parent.fixed_profile(),
            self.parent.leaf_profile(),self.parent.work_profile(),t);
        self.adjacency.bind(t);self.metadata.bind(t);
        t.append_bytes(b"actual-point-template",layout::hash_terms(&self.points.circuit.terms).as_bytes());
        Ok(())
    }
    #[cfg(test)]
    pub(crate) fn bind_role0_diagnostic_context(
        &self, t: &mut Transcript, context: &NativeRole0DiagnosticContext,
    ) -> Result<(),String> {
        self.bind_role0_diagnostic_context_with_fields(t, context, 0, 32, 33)
    }
    #[cfg(test)]
    pub(crate) fn bind_role0_diagnostic_context_with_fields(
        &self, t: &mut Transcript, context: &NativeRole0DiagnosticContext,
        role_index: usize, input_log: usize, output_log: usize,
    ) -> Result<(),String> {
        if t.challenges()!=0 {return Err("native role0 binding after challenge".into());}
        context.bind_admission(t)?;
        self.bind_role0_descriptor_fields_for_test(t, context, role_index, input_log, output_log)?;
        self.bind_plan_identity(t)
    }
    #[cfg(test)]
    pub(crate) fn bind_role0_descriptor_fields_for_test(
        &self, t: &mut Transcript, context: &NativeRole0DiagnosticContext,
        role_index: usize, input_log: usize, output_log: usize,
    ) -> Result<(),String> {
        if t.challenges()!=0 {return Err("native role0 binding after challenge".into());}
        context.validate()?;
        if self.descriptors.len()!=7 || self.descriptors.iter().enumerate().any(|(index,d)|
            d.role!=index || d.input_log!=INPUT_LOGS[index] || d.row_log!=ROW_LOGS[index]) {
            return Err("native role0 complete descriptor roster shape".into());
        }
        let role=&self.descriptors[0];
        if role.name!="corepool11" || role.role!=0 || role.input_log!=32 || role.row_log!=33 {
            return Err("native role0 diagnostic admission shape".into());
        }
        t.append_bytes(b"native-role0-descriptor",role.name.as_bytes());
        t.append_bytes(b"native-role0-source",role.source.as_bytes());
        t.append_u64(b"native-role0-role-index",role_index as u64);
        t.append_u64(b"native-role0-input-log",input_log as u64);
        t.append_u64(b"native-role0-output-log",output_log as u64);
        Ok(())
    }
    #[cfg(test)]
    pub(crate) fn prove_role0_packed_for_test(
        &self, source:&crate::packed::PackedFile, transcript:&mut Transcript,
        context:&NativeRole0DiagnosticContext,
    )->Result<(GkrProof,InputClaim),String>{
        if transcript.challenges()!=0 {
            return Err("native role0 proof transcript already challenged".into());
        }
        context.validate()?;
        if self.descriptors.iter().enumerate().any(|(index,d)|
            d.role!=index || d.input_log!=INPUT_LOGS[index] || d.row_log!=ROW_LOGS[index])
            || self.descriptors[0].name!="corepool11" {
            return Err("native role0 complete descriptor roster shape".into());
        }
        let mut preflight=context.transcript();
        self.bind_role0_diagnostic_context(&mut preflight,context)?;
        self.parent.core_pool().prove_packed_native_role0_for_test(
            source,transcript,
            |t|self.bind_role0_diagnostic_context(t,context),
            |r,u,v|self.coefficients(0,r,u,v),
        )
    }
    pub(crate) fn bound_transcript(&self) -> Result<Transcript,String> {
        let mut t=Transcript::new(b"native-prefix-source-plan-identity-only-v1");
        self.bind_plan_identity(&mut t)?; Ok(t)
    }
    pub(crate) fn coefficients(&self,role:usize,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String> {
        let d=self.descriptors.get(role).ok_or("unknown native prefix role")?;
        if r.len()!=d.row_log || u.len()!=d.input_log || v.len()!=d.input_log {return Err("native prefix coefficient dimensions".into());}
        match role {
            0=>self.parent.core_pool().coefficients(r,u,v).map_err(|e|e.to_string()),
            1=>self.daa.header_coefficients(r,u,v),
            2=>work_tree_wiring::full_roster_coefficients(self.parent.topology(),fixed::engine()?,
                self.parent.fixed_profile(),self.parent.leaf_boundary(),self.parent.work_boundary(),r,u,v),
            3=>{let mut c=sparse::wiring(&self.points.circuit,&self.point_shape,&r[..14],&u[..13],&v[..13]).map_err(|e|e.to_string())?;
                let f=joint(&r[14..],&u[13..],&v[13..]);for x in &mut c {*x*=f;}Ok(c)},
            4=>composite_coefficients(&self.height,&self.daa,r,u,v),
            5=>self.adjacency.coefficients(r,u,v),6=>self.metadata.coefficients(r,u,v),_=>unreachable!(),
        }
    }
    pub(crate) fn visit_role_owner_terms(&self,role:usize,owner:u64,
        mut sink:impl FnMut(Term)->Result<(),String>)->Result<usize,String> {
        let d=self.descriptors.get(role).ok_or("unknown native prefix role")?;
        if owner>=4096 {return Err("native prefix owner outside domain".into());}
        let owner=usize::try_from(owner).map_err(|_|"owner overflow")?;
        let mut count=0usize;
        let mut checked=|term:Term| {check_term(d.row_log,d.input_log,&term)?;
            sink(term)?;count=count.checked_add(1).ok_or("visitor count overflow")?;Ok(())};
        match role {
            0=>{let core=&fixed::engine()?.core;
                for (family,offset) in layout::CORE_OFFSETS.iter().enumerate() {
                    let rb=owner.checked_mul(1<<17).and_then(|a|a.checked_add(family*(1<<(17+H)))).ok_or("core row overflow")?;
                    let ib=owner.checked_mul(layout::WIDTH).and_then(|a|a.checked_add(*offset)).ok_or("core input overflow")?;
                    for term in &core.terms {checked(translate(term,rb,ib)?)?;}
                }},
            1=>{self.daa.visit_header_terms(owner as u64,&mut checked)?;},
            2=>{self.visit_worktree(owner,&mut checked)?;},
            3=>{for term in &self.points.circuit.terms {checked(translate(term,owner*(1<<14),owner*8192)?)?;}},
            4=>{visit_composite_owner(&self.height,&self.daa,owner as u64,&mut checked)?;},
            5=>{if owner<N as usize {self.adjacency.visit_slot_terms(owner as u64,|row,gate|checked(Term{row,gate}))?;}},
            6=>{if owner<N as usize {self.metadata.visit_slot_terms(owner as u64,|row,gate|checked(Term{row,gate}))?;}},
            _=>unreachable!(),
        }
        Ok(count)
    }
    fn visit_worktree(&self,owner:usize,mut sink:impl FnMut(Term)->Result<(),String>)->Result<(),String> {
        let topology=self.parent.topology();let local=26;
        let mut index=0usize;
        let tag=|mut term:Term,index:usize|->Result<Term,String>{
            if term.row>=1usize<<local || index>=40 {return Err("full roster local/tag overflow".into());}
            term.row=term.row.checked_add(index.checked_shl(local as u32).ok_or("tag shift overflow")?).ok_or("tag addition overflow")?;Ok(term)};
        for family in &topology.families {
            family.emit_endpoint_terms(&topology.descriptor,true,owner,|_,_,t|sink(tag(t,index)?))?; index+=1;
        }
        // Existing three emitters have infallible callbacks. Preserve the FIRST checked error.
        for member in 0..3 {
            let mut first_error=None;
            let mut cb=|t| {if first_error.is_none() {if let Err(e)=tag(t,index).and_then(&mut sink) {first_error=Some(e);}}};
            match member {0=>fixed::emit_slot(fixed::engine()?,self.parent.fixed_profile(),owner,&mut cb)?,
                1=>self.parent.leaf_boundary().emit_slot(owner,&mut cb)?,
                _=>self.parent.work_boundary().emit_slot(owner,&mut cb)?,}
            if let Some(e)=first_error {return Err(e);}index+=1;
        }
        for family in self.parent.work_boundary().links() {
            family.emit_endpoint_terms(&topology.descriptor,true,owner,|_,_,t|sink(tag(t,index)?))?;index+=1;
        }
        if index!=40 {return Err("full roster incomplete member order".into());}Ok(())
    }
}

fn translate(t:&Term,row_base:usize,input_base:usize)->Result<Term,String> {
    let mut out=t.clone();out.row=out.row.checked_add(row_base).ok_or("translated row overflow")?;
    out.gate.left=out.gate.left.checked_add(input_base).ok_or("translated left overflow")?;
    out.gate.right=out.gate.right.checked_add(input_base).ok_or("translated right overflow")?;Ok(out)
}
fn joint(r:&[Fr],u:&[Fr],v:&[Fr])->Fr {
    r.iter().zip(u).zip(v).fold(Fr::one(),|a,((r,u),v)|a*((Fr::one()-r)*(Fr::one()-u)*(Fr::one()-v)+*r*u*v))
}

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) enum Role4EndpointScope { CompleteS2, NamedM2Aliases, NamedM1Aliases, WholeS12 }

/// Separate internal diagnostic identity. It cannot widen Selection::s12.
#[cfg(test)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DiagnosticCheckpointRole4Descriptor {
    pub(crate) tag: &'static str,
    pub(crate) parent_object: usize,
    pub(crate) checkpoint: crate::checkpoint_output_layout::CheckpointRole4Descriptor,
}

#[cfg(test)]
pub(crate) struct DiagnosticCheckpointRole4Relation<'a> {
    height: HeightWork<'a>,
    daa: DaaHistoryRoster<'a>,
    lane: crate::checkpoint_output_layout::CheckpointRole4Lane<'a>,
    descriptor: DiagnosticCheckpointRole4Descriptor,
}

#[cfg(test)]
impl<'a> DiagnosticCheckpointRole4Relation<'a> {
    /// h is an expected verifier input, never taken from a prover descriptor.
    pub(crate) fn new(parent: &'a WorkTreeHistoryPlan, h: u64,
        public: crate::checkpoint_output_layout::CheckpointPublic) -> Result<Self, String>
    {
        let lane = crate::checkpoint_output_layout::CheckpointRole4Lane::new(parent, h, public)?;
        let height = HeightWork::compile_history(parent)?;
        let daa = DaaHistoryRoster::compile(parent)?;
        HistoricalRole4Endpoints::new(&height, &daa)?;
        let descriptor = DiagnosticCheckpointRole4Descriptor {
            tag: "role4-height-daa-checkpoint-internal-diagnostic-k64-v1",
            parent_object: parent as *const _ as usize, checkpoint: lane.descriptor() };
        Ok(Self { height, daa, lane, descriptor })
    }

    pub(crate) fn descriptor(&self) -> DiagnosticCheckpointRole4Descriptor { self.descriptor.clone() }

    fn validate_descriptor(&self, requested: &DiagnosticCheckpointRole4Descriptor) -> Result<(), String> {
        if requested != &self.descriptor { return Err("diagnostic checkpoint role4 descriptor mismatch".into()); }
        self.lane.validate_descriptor(&requested.checkpoint)
    }

    pub(crate) fn bind(&self, requested: &DiagnosticCheckpointRole4Descriptor, t: &mut Transcript)
        -> Result<(), String>
    {
        self.validate_descriptor(requested)?;
        if t.challenges() != 0 { return Err("diagnostic checkpoint role4 binding after challenge".into()); }
        t.append_bytes(b"diagnostic-checkpoint-role4", self.descriptor.tag.as_bytes());
        t.append_bytes(b"diagnostic-checkpoint-role4-order", b"height+numeric;daa;checkpoint");
        self.height.bind(t); self.daa.bind(t); self.lane.bind(t)
    }

    pub(crate) fn coefficients(&self, requested: &DiagnosticCheckpointRole4Descriptor,
        r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String>
    {
        self.validate_descriptor(requested)?;
        let old = composite_coefficients(&self.height, &self.daa, r, u, v)?;
        let extra = self.lane.coefficients(r, u, v)?;
        Ok(std::array::from_fn(|i| old[i] + extra[i]))
    }

    pub(crate) fn visit_owner_terms(&self, requested: &DiagnosticCheckpointRole4Descriptor, owner: usize,
        mut sink: impl FnMut(Term) -> Result<(), String>) -> Result<usize, String>
    {
        self.validate_descriptor(requested)?;
        if owner >= self.height.slots() { return Err("diagnostic checkpoint role4 row owner".into()); }
        let d = &self.descriptor.checkpoint;
        let mut count = 0usize;
        let mut checked = |term: Term| {
            check_term(d.row_log, d.input_log, &term)?;
            sink(term)?; count = count.checked_add(1).ok_or("diagnostic checkpoint role4 count")?; Ok(())
        };
        visit_composite_owner(&self.height, &self.daa, owner as u64, &mut checked)?;
        self.lane.visit_owner_terms(d, owner, checked)?;
        Ok(count)
    }

    pub(crate) fn visit_endpoint(&self, requested: &DiagnosticCheckpointRole4Descriptor, left: bool, owner: usize,
        mut sink: impl FnMut(crate::sparse_stream_roster::EdgeTerm) -> Result<(), String>)
        -> Result<usize, String>
    {
        self.validate_descriptor(requested)?;
        if owner >= self.height.slots() { return Err("diagnostic checkpoint role4 endpoint owner".into()); }
        let old = HistoricalRole4Endpoints::new(&self.height, &self.daa)?.visit(left, owner, &mut sink)?.total()?;
        let extra = self.lane.visit_endpoint(&requested.checkpoint, left, owner, sink)?;
        old.checked_add(extra).ok_or_else(|| "diagnostic checkpoint role4 endpoint count".into())
    }
}


/// An internal source-context token, not an authentication or proof receipt.
#[derive(Clone,Debug,PartialEq,Eq)]
pub(crate) struct Role4EndpointBinding {
    pub(crate) scope:Role4EndpointScope,
    pub(crate) source:&'static str,
    pub(crate) parent_object:usize,
    pub(crate) headers:u64,
    pub(crate) slot_log:usize,
    pub(crate) map:Option<[u8;32]>,
    pub(crate) descriptor:Option<[u8;32]>,
    pub(crate) whole_alias_identities:Option<[[[u8;32];2];2]>,
}

pub(crate) struct Role4EndpointAdapter<'a,'p> {
    height:&'a HeightWork<'p>,
    daa:&'a DaaHistoryRoster<'p>,
    binding:Role4EndpointBinding,
    m2:Option<crate::short_daa_layout::M2AliasEndpointIndex<'a>>,
    m1:Option<crate::one_daa_layout::M1AliasEndpointIndex<'a>>,
}
impl<'a,'p> Role4EndpointAdapter<'a,'p> {
    pub(crate) fn new(height:&'a HeightWork<'p>,daa:&'a DaaHistoryRoster<'p>,
        scope:Role4EndpointScope)->Result<Self,String> {
        let parent=height.endpoint_parent();
        if !std::ptr::eq(parent,daa.endpoint_parent()) || height.slots()!=parent.slots()
            || height.input_log()!=daa.input_log() {
            return Err("role4 endpoint parent identity rejected".into());
        }
        let (m2,m1)=match scope {
            Role4EndpointScope::CompleteS2 if parent.headers()==3 && parent.slot_log()==2=>(None,None),
            Role4EndpointScope::NamedM2Aliases if parent.headers()==3073 && parent.slot_log()==12=>(Some(daa.named_m2_alias_endpoints()?),None),
            Role4EndpointScope::NamedM1Aliases if parent.headers()==3073 && parent.slot_log()==12=>(None,Some(daa.named_m1_alias_endpoints()?)),
            Role4EndpointScope::WholeS12 if parent.headers()==3073 && parent.slot_log()==12=>{
                height.check_s12_endpoint_scope()?;
                (Some(daa.named_m2_alias_endpoints()?),Some(daa.named_m1_alias_endpoints()?))
            },
            _=>return Err("role4 endpoint relation scope unsupported".into()),
        };
        let identity=m2.as_ref().map(|index|index.identity()).or_else(||m1.as_ref().map(|index|index.identity()));
        let (map,descriptor)=match identity {Some((m,d))=>(Some(m),Some(d)),None=>(None,None)};
        let whole_alias_identities=if scope==Role4EndpointScope::WholeS12 {
            let (m1map,m1descriptor)=m1.as_ref().ok_or("S12 M1 index absent")?.identity();
            let (m2map,m2descriptor)=m2.as_ref().ok_or("S12 M2 index absent")?.identity();
            Some([[m1map,m1descriptor],[m2map,m2descriptor]])
        } else {None};
        let binding=Role4EndpointBinding{scope,source:SOURCE,parent_object:parent as *const _ as usize,
            headers:parent.headers(),slot_log:parent.slot_log(),map,descriptor,whole_alias_identities};
        Ok(Self{height,daa,binding,m2,m1})
    }
    pub(crate) fn binding(&self)->Role4EndpointBinding {self.binding.clone()}

    pub(crate) fn coefficients(&self,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String> {
        match self.binding.scope {
            Role4EndpointScope::CompleteS2=>composite_coefficients(self.height,self.daa,r,u,v),
            Role4EndpointScope::NamedM2Aliases=>self.daa.named_m2_alias_coefficients(r,u,v),
            Role4EndpointScope::NamedM1Aliases=>self.daa.named_m1_alias_coefficients(r,u,v),
            Role4EndpointScope::WholeS12=>composite_coefficients(self.height,self.daa,r,u,v),
        }
    }

    /// Checks dimensions, row packing and selected endpoint owner only.
    /// Canonical source membership is established by the source visitor, not this check.
    pub(crate) fn check_edge(&self,left:bool,slot:usize,edge:&crate::sparse_stream_roster::EdgeTerm)->Result<(),String> {
        let h=self.binding.slot_log;let slots=1usize.checked_shl(h as u32).ok_or("role4 endpoint slots overflow")?;
        if slot>=slots {return Err("role4 endpoint requested owner outside domain".into());}
        check_term(20+h,20+h,&edge.term)?;
        let row=crate::sparse_stream_roster::global_edge_row(edge.source_slot,edge.family_row,h,19,1,&[19,19])?;
        let endpoint=if left{edge.term.gate.left}else{edge.term.gate.right};
        if row!=edge.term.row || endpoint/(1<<20)!=slot {
            return Err("role4 endpoint canonical row or side mismatch".into());
        }
        Ok(())
    }
    fn pack(&self,family:usize,term:Term,left:bool,slot:usize)->Result<crate::sparse_stream_roster::EdgeTerm,String> {
        if family>1 {return Err("role4 endpoint family outside composite".into());}
        let base=1usize.checked_shl((19+self.binding.slot_log) as u32).ok_or("role4 endpoint row base overflow")?;
        let low=term.row.checked_sub(family*base).filter(|row|*row<base).ok_or("role4 endpoint family row mismatch")?;
        let edge=crate::sparse_stream_roster::EdgeTerm{source_slot:low>>19,
            family_row:(family<<19)|(low&((1<<19)-1)),term};
        self.check_edge(left,slot,&edge)?;Ok(edge)
    }
    pub(crate) fn visit_endpoint(&self,requested:&Role4EndpointBinding,left:bool,slot:usize,
        mut sink:impl FnMut(crate::sparse_stream_roster::EdgeTerm)->Result<(),String>)->Result<usize,String> {
        if requested!=&self.binding || slot>=self.height.slots() {
            return Err("role4 endpoint request identity or owner rejected".into());
        }
        match self.binding.scope {
            Role4EndpointScope::CompleteS2=>{
                let mut count=self.height.visit_complete_s2_endpoint_terms(left,slot,|t|sink(self.pack(0,t,left,slot)?))?;
                let base=1usize<<self.daa.row_log();
                count+=self.daa.visit_complete_s2_endpoint_terms(left,slot,|mut t| {
                    t.row=t.row.checked_add(base).ok_or("role4 endpoint DAA outer row overflow")?;
                    sink(self.pack(1,t,left,slot)?)
                })?;
                Ok(count)
            }
            Role4EndpointScope::NamedM2Aliases=>{
                let index=self.m2.as_ref().ok_or("role4 M2 index absent")?;
                let map=requested.map.ok_or("role4 M2 map absent")?;
                let descriptor=requested.descriptor.ok_or("role4 M2 descriptor absent")?;
                index.visit(crate::short_daa_layout::Profile::M2,map,descriptor,left,slot,|port,mut t| {
                    if t.row!=(3072<<10)+port {return Err("role4 M2 original alias row mismatch".into());}
                    t.row=(1usize<<31)+(3072usize<<19)+(1<<17)+port;
                    sink(self.pack(1,t,left,slot)?)
                })
            }
            Role4EndpointScope::NamedM1Aliases=>{
                let index=self.m1.as_ref().ok_or("role4 M1 index absent")?;
                let map=requested.map.ok_or("role4 M1 map absent")?;
                let descriptor=requested.descriptor.ok_or("role4 M1 descriptor absent")?;
                index.visit(crate::one_daa_layout::M1_ENDPOINT_PROFILE,map,descriptor,left,slot,|port,mut t| {
                    if t.row!=(2048<<8)+port {return Err("role4 M1 original alias row mismatch".into());}
                    t.row=(1usize<<31)+(2048usize<<19)+(1<<17)+port;
                    sink(self.pack(1,t,left,slot)?)
                })
            }
            Role4EndpointScope::WholeS12=>{
                let identities=requested.whole_alias_identities.ok_or("S12 alias identities absent")?;
                let mut count=self.height.visit_s12_endpoint_terms(left,slot,|t|sink(self.pack(0,t,left,slot)?))?;
                let base=1usize<<31;
                count+=self.daa.visit_s12_local_endpoint_terms(slot,0,|mut t| {
                    t.row+=base;sink(self.pack(1,t,left,slot)?)
                })?;
                count+=self.m1.as_ref().ok_or("S12 M1 index absent")?.visit(
                    crate::one_daa_layout::M1_ENDPOINT_PROFILE,identities[0][0],identities[0][1],left,slot,|port,mut t| {
                        if t.row!=(2048<<8)+port {return Err("S12 M1 original row mismatch".into());}
                        t.row=base+(2048usize<<19)+(1<<17)+port;sink(self.pack(1,t,left,slot)?)
                    })?;
                count+=self.m2.as_ref().ok_or("S12 M2 index absent")?.visit(
                    crate::short_daa_layout::Profile::M2,identities[1][0],identities[1][1],left,slot,|port,mut t| {
                        if t.row!=(3072<<10)+port {return Err("S12 M2 original row mismatch".into());}
                        t.row=base+(3072usize<<19)+(1<<17)+port;sink(self.pack(1,t,left,slot)?)
                    })?;
                count+=self.daa.visit_s12_numeric_endpoint_terms(left,slot,|mut t| {
                    t.row+=base;sink(self.pack(1,t,left,slot)?)
                })?;
                count+=self.daa.visit_s12_local_endpoint_terms(slot,3,|mut t| {
                    t.row+=base;sink(self.pack(1,t,left,slot)?)
                })?;
                Ok(count)
            },
        }
    }

    #[cfg(test)]
    pub(crate) fn grouped_v_context_for_test(
        &self,
        requested: &Role4EndpointBinding,
        r: &[Fr],
        u: &[Fr],
        left_value: Fr,
    ) -> Result<crate::daa_history_roster::DaaGroupedVContextForTest<'a, 'p>, String> {
        if requested != &self.binding
            || self.binding.scope != Role4EndpointScope::WholeS12
            || self.binding.headers != 3073
            || self.binding.slot_log != 12
            || !std::ptr::eq(self.height.endpoint_parent(), self.daa.endpoint_parent())
            || requested.whole_alias_identities.is_none()
        {
            return Err("grouped V inactive context binding or scope rejected".into());
        }
        self.daa.grouped_v_context_for_test(r, u, left_value)
    }

    #[cfg(test)]
    pub(crate) fn grouped_v_owner_for_test(
        &self,
        requested: &Role4EndpointBinding,
        context: &crate::daa_history_roster::DaaGroupedVContextForTest<'a, 'p>,
        owner: usize,
    ) -> Result<(usize, Fr), String> {
        if requested != &self.binding
            || self.binding.scope != Role4EndpointScope::WholeS12
            || requested.whole_alias_identities.is_none()
        {
            return Err("grouped V inactive owner binding or scope rejected".into());
        }
        self.daa.grouped_v_owner_for_test(context, owner)
    }

    /// RIGHT-only diagnostic visitor. It preserves the canonical WholeS12
    /// dispatch order and omits only the final local inactive lane-3 source.
    #[cfg(test)]
    pub(crate) fn visit_right_noninactive_for_test(
        &self,
        requested: &Role4EndpointBinding,
        slot: usize,
        mut sink: impl FnMut(crate::sparse_stream_roster::EdgeTerm) -> Result<(), String>,
    ) -> Result<usize, String> {
        if requested != &self.binding
            || self.binding.scope != Role4EndpointScope::WholeS12
            || slot >= self.height.slots()
        {
            return Err("grouped V RIGHT noninactive request identity, scope, or owner rejected".into());
        }
        let identities = requested.whole_alias_identities.ok_or("S12 alias identities absent")?;
        let mut count = self.height.visit_s12_endpoint_terms(false, slot, |term| {
            sink(self.pack(0, term, false, slot)?)
        })?;
        let base = 1usize << 31;
        count = count.checked_add(self.daa.visit_s12_local_endpoint_terms(slot, 0, |mut term| {
            term.row = term.row.checked_add(base).ok_or("grouped V lane-0 row overflow")?;
            sink(self.pack(1, term, false, slot)?)
        })?).ok_or("grouped V RIGHT count overflow")?;
        count = count.checked_add(self.m1.as_ref().ok_or("S12 M1 index absent")?.visit(
            crate::one_daa_layout::M1_ENDPOINT_PROFILE,
            identities[0][0],
            identities[0][1],
            false,
            slot,
            |port, mut term| {
                if term.row != (2048 << 8) + port {
                    return Err("S12 M1 original row mismatch".into());
                }
                term.row = base + (2048usize << 19) + (1 << 17) + port;
                sink(self.pack(1, term, false, slot)?)
            },
        )?).ok_or("grouped V RIGHT count overflow")?;
        count = count.checked_add(self.m2.as_ref().ok_or("S12 M2 index absent")?.visit(
            crate::short_daa_layout::Profile::M2,
            identities[1][0],
            identities[1][1],
            false,
            slot,
            |port, mut term| {
                if term.row != (3072 << 10) + port {
                    return Err("S12 M2 original row mismatch".into());
                }
                term.row = base + (3072usize << 19) + (1 << 17) + port;
                sink(self.pack(1, term, false, slot)?)
            },
        )?).ok_or("grouped V RIGHT count overflow")?;
        count = count.checked_add(self.daa.visit_s12_numeric_endpoint_terms(false, slot, |mut term| {
            term.row = term.row.checked_add(base).ok_or("grouped V numeric row overflow")?;
            sink(self.pack(1, term, false, slot)?)
        })?).ok_or("grouped V RIGHT count overflow")?;
        Ok(count)
    }
}

#[cfg(test)]
fn decode_native_role_packet(proof_bytes:&[u8],input_log:usize)->Result<GkrProof,String>{
    let decoded=crate::gkr::decode_dimensions(&[input_log],proof_bytes)?;
    if crate::gkr::encode_proof(&decoded)?!=proof_bytes{return Err("native join proof is not canonical".into());}
    Ok(decoded)
}

#[cfg(test)]
fn verify_native_role_packet(plan:&NativePrefixAuthPlan<'_>,role:usize,input_log:usize,output_log:usize,
    proof:&GkrProof,initial:Transcript,prepared:Transcript)->Result<(InputClaim,Transcript),String>{
    let mut transcript=initial;
    let claim=crate::gkr::verify_with_wiring(&[input_log],1usize<<output_log,proof,&mut transcript,
        move|t|*t=prepared,
        |layer,r,u,v|if layer==0{plan.coefficients(role,r,u,v).map_err(|_|crate::gkr::GkrError::PointDimension)}
            else{Err(crate::gkr::GkrError::PointDimension)}).map_err(|error|error.to_string())?;
    Ok((claim,transcript))
}

#[cfg(test)]
impl NativePrefixAuthPlan<'_>{
    /// Test-only fingerprint of the code-owned, pre-challenge role prefix.
    /// The continuation challenge is sampled on a clone and never returned as
    /// caller-owned transcript state.
    pub(crate) fn native_role_prefix_control_for_join(&self,role:usize,key_bytes:&[u8],commitment_bytes:&[u8])
        ->Result<([u64;3],Fr),String>{
        let artifacts=NativeRole0DiagnosticContext::admit(key_bytes,commitment_bytes)?;
        let (prepared,label)=match role{
            0=>{let mut t=artifacts.transcript();self.bind_role0_diagnostic_context(&mut t,&artifacts)?;
                (t,b"native-role-join-prefix-control-v1".as_slice())}
            1=>{let context=NativeRole1DiagnosticContext{artifacts};let mut t=context.transcript();
                self.bind_role1_diagnostic_context(&mut t,&context)?;(t,b"native-role-join-prefix-control-v1".as_slice())}
            2=>{let t=native_role2_full::role2_full_transcript();let p=native_role2_full::prepare_role2_full_verifier_binding(self,&t)?;
                (p,b"native-role2-direct-full-continuation-v1".as_slice())}
            3=>{let t=Transcript::new(b"native-prefix-role3-diagnostic-proof-v1");
                (native_role3::prepare_role3_artifact_binding(self,&t,&artifacts)?,b"native-role-join-prefix-control-v1".as_slice())}
            4=>return Err("native join role4 requires opaque receiver".into()),
            5=>{let context=NativeRole5DiagnosticContext::from_admitted_artifacts(artifacts);
                (self.prepare_role5_binding_for_test(&context.transcript(),&context)?,b"native-role5-common-control".as_slice())}
            6=>{let t=NativeRole6Admission::role6_full_transcript();let shape=[6,3073,4096,12,32,24,20,12,0];
                (NativeRole6Admission::prepare_role6_artifact_binding(self,&artifacts,&shape,&t)?,
                    b"native-role6-direct-full-continuation-v1".as_slice())}
            _=>return Err("unknown native join role".into()),
        };
        if prepared.challenges()!=0||prepared.raw_queries()!=0{return Err("native join prepared prefix advanced".into());}
        let counters=[prepared.challenges(),prepared.raw_queries(),prepared.bytes_absorbed()];
        let continuation=prepared.clone().try_challenge_scalar(label)?;
        Ok((counters,continuation))
    }

    /// Verify one retained native packet using its original producer domain and
    /// statement binder. This receiver accepts artifacts and proof bytes only;
    /// it has no packed-file, witness, or prover-setup input.
    pub(crate) fn verify_native_role_packet_for_join(&self,role:usize,proof_bytes:&[u8],key_bytes:&[u8],
        commitment_bytes:&[u8])->Result<(InputClaim,Transcript),String>{
        let (input_log,output_log)=match role{
            0=>(32,33),1=>(32,31),2=>(32,32),3=>(25,26),4=>return Err("native join role4 requires opaque receiver".into()),
            5=>(32,21),6=>(32,24),_=>return Err("unknown native join role".into()),
        };
        let artifacts=NativeRole0DiagnosticContext::admit(key_bytes,commitment_bytes)?;
        let proof=decode_native_role_packet(proof_bytes,input_log)?;
        match role{
            0=>{
                let initial=artifacts.transcript();let mut prepared=initial.clone();
                self.bind_role0_diagnostic_context(&mut prepared,&artifacts)?;
                verify_native_role_packet(self,role,input_log,output_log,&proof,initial,prepared)
            }
            1=>{
                let context=NativeRole1DiagnosticContext{artifacts};let initial=context.transcript();let mut prepared=initial.clone();
                self.bind_role1_diagnostic_context(&mut prepared,&context)?;
                verify_native_role_packet(self,role,input_log,output_log,&proof,initial,prepared)
            }
            2=>{
                let initial=native_role2_full::role2_full_transcript();
                let prepared=native_role2_full::prepare_role2_full_verifier_binding(self,&initial)?;
                verify_native_role_packet(self,role,input_log,output_log,&proof,initial,prepared)
            }
            3=>{
                let initial=Transcript::new(b"native-prefix-role3-diagnostic-proof-v1");
                let prepared=native_role3::prepare_role3_artifact_binding(self,&initial,&artifacts)?;
                verify_native_role_packet(self,role,input_log,output_log,&proof,initial,prepared)
            }
            5=>{
                let context=NativeRole5DiagnosticContext::from_admitted_artifacts(artifacts);
                self.verify_role5_for_test(&proof,&context)
            }
            6=>{
                let initial=NativeRole6Admission::role6_full_transcript();
                let shape=[6,3073,4096,12,32,24,20,12,0];
                let prepared=NativeRole6Admission::prepare_role6_artifact_binding(self,&artifacts,&shape,&initial)?;
                verify_native_role_packet(self,role,input_log,output_log,&proof,initial,prepared)
            }
            _=>unreachable!(),
        }
    }
}

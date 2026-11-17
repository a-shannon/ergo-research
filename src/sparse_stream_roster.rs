//! Runtime-internal tensor GKR producer for slot-local roster terms.
//!
//! Input coordinates are local-bit first, slot-bit second. Output rows retain
//! the reviewed full-split order: local-row bits, slot bits, then family tags.
//! Only one slot's coefficient/input vectors are live during local rounds;
//! the handoff vectors are indexed by slot and family, never by the full input.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use std::collections::VecDeque;
use crate::{gkr::{self,GkrError,GkrProof,InputClaim,LayerProof},sparse::Term,transcript::Transcript};

#[cfg(test)]
#[derive(Clone,Debug)]
pub(crate) struct TestPhaseMark { pub(crate) name:String, pub(crate) elapsed_ns:u128 }
#[cfg(test)]
thread_local! {
    static TEST_GROUPED_V_MUTANT:std::cell::Cell<u8>=const { std::cell::Cell::new(0) };
    static TEST_PHASE_TRACE:std::cell::RefCell<Option<(std::time::Instant,Vec<TestPhaseMark>)>>=
        const { std::cell::RefCell::new(None) };
}

#[cfg(test)]
mod h21_capacity_only_tests {
    use super::*;
    use crate::{daa_history_roster::{DaaHistoryRoster,OwnerClass},work_tree_history_plan::WorkTreeHistoryPlan};

    const OWNER_COUNT:usize=1usize<<21;
    const RELEASED_OWNERS:usize=8_502;
    const BASE_OWNERS:usize=2_088_650;
    const BASE_TERMS:usize=396_561;
    const RELEASED_TERMS:usize=388_369;
    const POLICY_CAP:usize=1024*1024*1024;

    fn labels_match_roster(roster:&DaaHistoryRoster<'_>,labels:&[usize])->Result<(),String>{
        if labels.len()!=OWNER_COUNT{return Err("H21 capacity owner-label length".into());}
        for (owner,&actual) in labels.iter().enumerate(){
            let class=roster.owner_class(owner as u64)?;
            let expected=usize::from(matches!(class,OwnerClass::Short(_)|OwnerClass::Mature(_)));
            if actual!=expected{return Err(format!("H21 capacity owner label mismatch at {owner}"));}
        }
        Ok(())
    }

    #[test]
    fn h21_capacity_only_one_gib_policy_matches_actual_owner_roster(){
        assert_eq!(usize::BITS,64);
        assert_eq!(MAX_INCREMENTAL_CACHE_STATE_BYTES,512*1024*1024);
        let history=WorkTreeHistoryPlan::compile(1_827_840,21,[0x35;32],[0x35;28]).unwrap();
        let roster=DaaHistoryRoster::compile(&history).unwrap();
        assert_eq!(history.headers(),1_827_840);
        assert_eq!(history.slot_log(),21);

        let mut labels=Vec::with_capacity(OWNER_COUNT);
        for owner in 0..OWNER_COUNT{
            let class=roster.owner_class(owner as u64).unwrap();
            labels.push(usize::from(matches!(class,OwnerClass::Short(_)|OwnerClass::Mature(_))));
        }
        let released=labels.iter().filter(|group|**group==1).count();
        let base=labels.iter().filter(|group|**group==0).count();
        assert_eq!((released,base),(RELEASED_OWNERS,BASE_OWNERS));
        labels_match_roster(&roster,&labels).unwrap();

        // A same-count swap must be caught by the separate entrywise source check.
        let released_owner=labels.iter().position(|group|*group==1).unwrap();
        let base_owner=labels.iter().position(|group|*group==0).unwrap();
        let mut swapped=labels.clone();
        swapped[released_owner]=0;swapped[base_owner]=1;
        assert_eq!(swapped.iter().filter(|group|**group==1).count(),released);
        assert!(labels_match_roster(&roster,&swapped).is_err());
        drop(swapped);

        let admission=GroupedVAdmission::try_new(21,&labels,&[BASE_TERMS,RELEASED_TERMS]).unwrap();
        let policy=GroupedDimensionPolicy::H21CapacityOnly{limit_bytes:POLICY_CAP};
        assert!(policy.dimensions_allowed(20,21,19));
        assert!(policy.validate_census(&admission).is_ok());
        assert!(policy.validate_route(20,21,19,0,&[19],0,true,false,true,Some(&admission)).is_err(),
            "capacity-only permission cannot enter a producer route");

        let plan=UCapacityPlan::new(20,21,19,&admission,policy).unwrap();
        let phases=[("baseline",UPhase::Baseline),("row_build",UPhase::RowBuild),
            ("prefix",UPhase::Prefix),("bank",UPhase::Bank),("table",UPhase::Table),
            ("high_reserve",UPhase::HighReserve),("load",UPhase::Load),("apply",UPhase::Apply),
            ("send",UPhase::Send),("high",UPhase::High),("post_high",UPhase::PostHigh)];
        let phase_maxima:Vec<(&str,usize)>=phases.into_iter().map(|(name,phase)|
            (name,(0..=20).map(|k|plan.bound(phase,k).unwrap()).max().unwrap())).collect();
        let exact_u=phase_maxima.iter().map(|(_,bytes)|*bytes).max().unwrap();
        let raw_v=grouped_v_prebind_capacity_bound_with_policy(20,21,19,&admission,policy).unwrap();
        let v_u_reservation=boolean_u_v_reservation(plan.width).unwrap();
        let v_subset4_metadata=subset4_metadata_bytes().unwrap();
        let exact_v=raw_v.checked_add(v_u_reservation).and_then(|n|n.checked_add(v_subset4_metadata)).unwrap();
        let exact_component=exact_u.max(exact_v);
        assert_eq!(plan.u_max,exact_u);
        assert_eq!(plan.v_max,exact_v);
        assert_eq!(plan.component,exact_component);
        assert!(plan.u_max>MAX_INCREMENTAL_CACHE_STATE_BYTES&&plan.u_max<=POLICY_CAP);
        assert!(plan.v_max>MAX_INCREMENTAL_CACHE_STATE_BYTES&&plan.v_max<=POLICY_CAP);
        assert!(plan.component>MAX_INCREMENTAL_CACHE_STATE_BYTES&&plan.component<=POLICY_CAP);

        let wrong_terms=GroupedVAdmission::try_new(21,&labels,&[BASE_TERMS-1,RELEASED_TERMS+1]).unwrap();
        assert!(UCapacityPlan::new(20,21,19,&wrong_terms,policy).is_err());
        assert!(UCapacityPlan::new(20,20,19,&admission,policy).is_err());
        let below=GroupedDimensionPolicy::H21CapacityOnly{limit_bytes:plan.component-1};
        assert_eq!(UCapacityPlan::new(20,21,19,&admission,below).err().unwrap(),
            "H21 capacity-only component exceeds policy limit");
        let over_cap=GroupedDimensionPolicy::H21CapacityOnly{limit_bytes:POLICY_CAP+1};
        assert_eq!(UCapacityPlan::new(20,21,19,&admission,over_cap).err().unwrap(),
            "H21 capacity-only cap exceeds 1 GiB");

        println!("C305_H21_CAPACITY_ONLY {}",serde_json::json!({
            "schema":1,"dimensions":[20,21,19],"owner_count":OWNER_COUNT,
            "released_owners":released,"base_owners":base,
            "terms_per_group":[BASE_TERMS,RELEASED_TERMS],
            "u_phase_maxima_bytes":phase_maxima,"u_max_bytes":plan.u_max,
            "v_grouped_prebind_bytes":raw_v,"v_u_reservation_bytes":v_u_reservation,
            "v_subset4_metadata_bytes":v_subset4_metadata,"v_max_bytes":plan.v_max,
            "component_bytes":plan.component,"global_cap_bytes":MAX_INCREMENTAL_CACHE_STATE_BYTES,
            "policy_cap_bytes":POLICY_CAP,"roster_entrywise_check":true,"swapped_label_rejected":true,
            "wrong_terms_rejected":true,"wrong_dimensions_rejected":true,
            "cap_below_bound_rejected":true,"oversized_policy_cap_rejected":true,
            "grouped_u_owner_term_visits":false,"plan_source_template_build":true,
            "owner_value_loads":false,"transcript":false,"proof":false,
            "pcs":false,"grouped_u_template_vectors_allocated":false,"production_route":false
        }));
    }
}
#[cfg(test)]
pub(crate) fn begin_phase_trace_for_test(){
    TEST_PHASE_TRACE.with(|trace|*trace.borrow_mut()=Some((std::time::Instant::now(),Vec::new())));
}
#[cfg(test)]
pub(crate) fn take_phase_trace_for_test()->Vec<TestPhaseMark>{
    TEST_PHASE_TRACE.with(|trace|trace.borrow_mut().take().map(|(_,marks)|marks).unwrap_or_default())
}
#[cfg(test)]
fn phase_mark(name:&str)->Result<(),String>{
    native_role3_observe(name)?;
    let event=TEST_PHASE_TRACE.with(|trace|trace.borrow_mut().as_mut().map(|(started,marks)|{
        let mark=TestPhaseMark{name:name.to_owned(),elapsed_ns:started.elapsed().as_nanos()};
        marks.push(mark.clone());mark
    }));
    if let Some(mark)=event {
        use std::io::Write;
        println!("NIPOPOW_ROLE1_PHASE {}",serde_json::json!({"name":mark.name,"elapsed_ns":mark.elapsed_ns}));
        let _=std::io::stdout().flush();
    }
    Ok(())
}
#[cfg(not(test))]
fn phase_mark(_name:&str)->Result<(),String>{Ok(())}

// Separate from the legacy allocating trace. The only constructor is called
// by the sealed native role3 entry; inactive observers allocate nothing.
#[cfg(test)]
struct NativeRole3Observer{started:std::time::Instant,marks:[crate::native_prefix_auth_plan::NativeRole3Mark;13],count:usize}
#[cfg(test)]
thread_local!{static NATIVE_ROLE3_OBSERVER:std::cell::RefCell<Option<NativeRole3Observer>>=const{std::cell::RefCell::new(None)};}
#[cfg(test)]
fn native_role3_observe(name:&str)->Result<(),String>{NATIVE_ROLE3_OBSERVER.with(|cell|{
    let mut state=cell.borrow_mut();let Some(state)=state.as_mut() else{return Ok(())};
    let stage=*crate::native_prefix_auth_plan::ROLE3_STAGES.get(state.count+2).filter(|_|state.count<13).ok_or("native role3 observer extent")?;
    if name!=stage{return Err("native role3 observer phase order".into());}
    let mark=crate::native_prefix_auth_plan::NativeRole3Mark{stage,elapsed_ns:u64::try_from(state.started.elapsed().as_nanos()).map_err(|_|"native role3 observer clock")?};
    crate::native_prefix_auth_plan::emit_role3_mark(mark)?;state.marks[state.count]=mark;state.count+=1;Ok(())
})}
#[cfg(test)]
struct NativeRole3ObserverScope{armed:bool}
#[cfg(test)]
impl NativeRole3ObserverScope{
    fn begin(started:std::time::Instant)->Result<Self,String>{
        if TEST_PHASE_TRACE.with(|t|t.borrow().is_some()){return Err("native role3 legacy trace must be disabled".into());}
        NATIVE_ROLE3_OBSERVER.with(|cell|->Result<(),String>{let mut state=cell.borrow_mut();if state.is_some(){return Err("native role3 observer already active".into());}
            *state=Some(NativeRole3Observer{started,marks:[crate::native_prefix_auth_plan::NativeRole3Mark{stage:"",elapsed_ns:0};13],count:0});Ok(())})?;
        Ok(Self{armed:true})
    }
    fn finish(mut self)->Result<[crate::native_prefix_auth_plan::NativeRole3Mark;13],String>{
        let state=NATIVE_ROLE3_OBSERVER.with(|cell|cell.borrow_mut().take()).ok_or("native role3 observer missing")?;self.armed=false;
        if state.count!=13{return Err("native role3 observer incomplete".into());}Ok(state.marks)
    }
}
#[cfg(test)]
impl Drop for NativeRole3ObserverScope{fn drop(&mut self){if self.armed{NATIVE_ROLE3_OBSERVER.with(|cell|{cell.borrow_mut().take();});}}}

fn read_copy(load:&mut impl FnMut(usize)->Result<Vec<Fr>,String>,copy:usize,width:usize)->Result<Vec<Fr>,String>{
    let values=load(copy)?;if values.len()!=width{return Err(GkrError::InvalidInputWidth.to_string());}Ok(values)
}

/// Tiny LRU for cross-slot scalar lookups. Its capacity is fixed independently
/// of the history length. A vector() call additionally clones one slot as a
/// scratch input, so the caller's peak is capacity cached slots plus one.
struct CopyCache<F>{load:F,width:usize,capacity:usize,owners:usize,entries:VecDeque<(usize,Vec<Fr>)>}
impl<F> CopyCache<F> where F:FnMut(usize)->Result<Vec<Fr>,String>{
    fn new(load:F,width:usize,capacity:usize)->Self{assert!(capacity>0);Self{load,width,capacity,owners:usize::MAX,entries:VecDeque::new()}}
    fn declared(load:F,width:usize,owners:usize)->Self{let mut value=Self::new(load,width,4);value.owners=owners;value}
    fn get(&mut self,copy:usize)->Result<&[Fr],String>{
        if let Some(position)=self.entries.iter().position(|(index,_)|*index==copy){
            let entry=self.entries.remove(position).unwrap();self.entries.push_front(entry);
        }else{
            if self.entries.len()==self.capacity{self.entries.pop_back();}
            let mut values=(self.load)(copy)?;if values.len()!=self.width{return Err(GkrError::InvalidInputWidth.to_string());}
            if values.capacity()>self.width{values.shrink_to_fit();}
            if values.capacity()>self.width{return Err("input copy capacity exceeds declared width".into());}
            self.entries.push_front((copy,values));
        }
        Ok(&self.entries.front().unwrap().1)
    }
    fn value(&mut self,copy:usize,wire:usize)->Result<Fr,String>{
        if wire>=self.width{return Err(GkrError::InvalidWireIndex.to_string());}Ok(self.get(copy)?[wire])
    }
    fn vector(&mut self,copy:usize)->Result<Vec<Fr>,String>{Ok(self.get(copy)?.to_vec())}
    fn capacity_bytes(&self)->Option<usize>{
        self.entries.iter().try_fold(0usize,|total,(_,values)|
            total.checked_add(values.capacity().checked_mul(std::mem::size_of::<Fr>())?))
    }
}

/// Input representation shared by the complete edge prover and its replay kernels.
pub(crate) trait EdgeInput {
    fn width(&self)->usize;
    fn owners(&self)->usize;
    fn value(&mut self,copy:usize,wire:usize)->Result<Fr,String>;
    fn vector(&mut self,copy:usize)->Result<Vec<Fr>,String>;
    fn capacity_bytes(&self)->Option<usize>;
    fn cache_budget_bytes(&self)->Result<usize,String>;
    fn supports_packed_line(&self)->bool{false}
    fn packed_line(&mut self,_owner:usize,_plan:&mut PackedLinePlan)->Result<(Vec<Fr>,u64),String>{
        Err("packed line unsupported input".into())
    }
    fn projected(&mut self,copy:usize,plan:&EdgePrefixPlan)->Result<Vec<Fr>,String> where Self:Sized{
        let values=edge_input_vector(self,copy,plan.width)?;if plan.k==0{Ok(values)}else{plan.project_fields(&values)}
    }
    #[cfg(test)] fn vector_clone_increment(&self)->u64;
}
impl<F:FnMut(usize)->Result<Vec<Fr>,String>> EdgeInput for CopyCache<F>{
    fn width(&self)->usize{self.width}
    fn owners(&self)->usize{self.owners}
    fn value(&mut self,copy:usize,wire:usize)->Result<Fr,String>{CopyCache::value(self,copy,wire)}
    fn vector(&mut self,copy:usize)->Result<Vec<Fr>,String>{CopyCache::vector(self,copy)}
    fn capacity_bytes(&self)->Option<usize>{CopyCache::capacity_bytes(self)}
    fn cache_budget_bytes(&self)->Result<usize,String>{self.width.checked_mul(std::mem::size_of::<Fr>())
        .and_then(|n|n.checked_mul(self.capacity)).ok_or("edge input cache budget overflow".into())}
    #[cfg(test)] fn vector_clone_increment(&self)->u64{1}
}
fn edge_cache_check(input:&impl EdgeInput)->Result<(),String>{
    let budget=input.cache_budget_bytes()?;let live=input.capacity_bytes().ok_or("edge input cache capacity overflow")?;
    if live>budget{return Err("edge input live cache exceeds declared budget".into());}Ok(())
}
pub(crate) fn edge_input_geometry(input:&impl EdgeInput,width:usize,owners:usize)->Result<(),String>{
    if input.width()!=width{return Err("edge input declared width mismatch".into());}
    if input.owners()!=owners{return Err("edge input declared owners mismatch".into());}edge_cache_check(input)
}
fn edge_input_value(input:&mut impl EdgeInput,copy:usize,wire:usize)->Result<Fr,String>{
    let value=input.value(copy,wire)?;edge_cache_check(input)?;Ok(value)
}
fn edge_input_vector(input:&mut impl EdgeInput,copy:usize,width:usize)->Result<Vec<Fr>,String>{
    let values=input.vector(copy)?;
    if values.len()!=width{return Err("edge input vector width mismatch".into());}
    if values.capacity()!=width{return Err("edge input vector capacity mismatch".into());}edge_cache_check(input)?;Ok(values)
}

#[derive(Default,Clone)]
pub(crate) struct PackedEdgeMetrics{
    pub logical_gets:u64,pub scalar_gets:u64,pub successful_loads:u64,pub packed_bytes:u64,
    pub vector_expansions:u64,pub expanded_fields:u64,pub load_ns:u64,pub decode_ns:u64,
    pub packet_capacity_peak_bytes:usize,pub cache_capacity_peak_bytes:usize,pub metadata_capacity_bytes:usize,
    pub projection_calls:u64,pub projection_fields:u64,pub projection_ns:u64,
}
/// Four packed owners; expanded vectors are returned to the caller, never cached.
pub(crate) struct PackedEdgeInput<F>{load:F,width:usize,owners:usize,entries:VecDeque<(usize,Vec<u8>)>,
    boolean:[Fr;2],metrics:PackedEdgeMetrics}
impl<F:FnMut(usize)->Result<Vec<u8>,String>> PackedEdgeInput<F>{
    pub(crate) fn new(width:usize,owners:usize,load:F)->Result<Self,String>{
        if !(8..=1048576).contains(&width)||!width.is_power_of_two(){return Err("packed edge width".into());}
        if !(1..=4096).contains(&owners){return Err("packed edge owners".into());}
        if width.checked_mul(owners).is_none_or(|n|n as u64>1u64<<32){return Err("packed edge extent".into());}
        let mut entries=VecDeque::new();entries.try_reserve_exact(4).map_err(|_|"packed edge metadata allocation")?;
        if entries.capacity()!=4{return Err("packed edge metadata capacity".into());}
        let metadata=std::mem::size_of::<Self>().checked_add(entries.capacity().checked_mul(std::mem::size_of::<(usize,Vec<u8>)>())
            .ok_or("packed edge metadata overflow")?).ok_or("packed edge metadata overflow")?;
        let mut value=Self{load,width,owners,entries,boolean:[Fr::zero(),Fr::one()],metrics:PackedEdgeMetrics::default()};
        value.metrics.metadata_capacity_bytes=metadata;value.metrics.cache_capacity_peak_bytes=metadata;
        value.cache_budget_bytes()?;Ok(value)
    }
    pub(crate) fn metrics(&self)->PackedEdgeMetrics{self.metrics.clone()}
    fn add(value:u64,increment:u64)->Result<u64,String>{value.checked_add(increment).ok_or("packed edge counter overflow".into())}
    fn elapsed(start:std::time::Instant)->Result<u64,String>{u64::try_from(start.elapsed().as_nanos()).map_err(|_|"packed edge clock overflow".into())}
    fn get(&mut self,copy:usize)->Result<&[u8],String>{
        if copy>=self.owners{return Err("packed edge owner range".into());}
        if let Some(position)=self.entries.iter().position(|(owner,_)|*owner==copy){
            let entry=self.entries.remove(position).ok_or("packed edge LRU position")?;self.entries.push_front(entry);
        }else{
            if self.entries.len()==4{self.entries.pop_back();}
            let started=std::time::Instant::now();let packet=(self.load)(copy)?;
            if packet.len()!=self.width/8{return Err("packed edge packet length".into());}
            if packet.capacity()!=self.width/8{return Err("packed edge packet capacity".into());}
            let elapsed=Self::elapsed(started)?;
            let loads=Self::add(self.metrics.successful_loads,1)?;
            let bytes=Self::add(self.metrics.packed_bytes,packet.len() as u64)?;
            let ns=Self::add(self.metrics.load_ns,elapsed)?;
            self.metrics.packet_capacity_peak_bytes=self.metrics.packet_capacity_peak_bytes.max(packet.capacity());
            self.entries.push_front((copy,packet));edge_cache_check(self)?;
            self.metrics.successful_loads=loads;self.metrics.packed_bytes=bytes;self.metrics.load_ns=ns;
        }
        self.metrics.logical_gets=Self::add(self.metrics.logical_gets,1)?;
        self.metrics.cache_capacity_peak_bytes=self.metrics.cache_capacity_peak_bytes.max(self.capacity_bytes().ok_or("packed edge cache overflow")?);
        Ok(&self.entries.front().ok_or("packed edge empty LRU")?.1)
    }
}
impl<F:FnMut(usize)->Result<Vec<u8>,String>> EdgeInput for PackedEdgeInput<F>{
    fn width(&self)->usize{self.width}
    fn owners(&self)->usize{self.owners}
    fn supports_packed_line(&self)->bool{true}
    fn packed_line(&mut self,owner:usize,plan:&mut PackedLinePlan)->Result<(Vec<Fr>,u64),String>{
        if plan.width!=self.width{return Err("packed line input width".into());}
        let packet=self.get(owner)?;let began=std::time::Instant::now();
        let result=plan.apply(packet)?;Ok((result,EdgeFullStats::ns(began)?))
    }
    fn value(&mut self,copy:usize,wire:usize)->Result<Fr,String>{
        if wire>=self.width{return Err("packed edge wire range".into());}
        let bit=(self.get(copy)?[wire/8]>>(wire%8))&1;let value=self.boolean[bit as usize];
        self.metrics.scalar_gets=Self::add(self.metrics.scalar_gets,1)?;Ok(value)
    }
    fn vector(&mut self,copy:usize)->Result<Vec<Fr>,String>{
        let width=self.width;let boolean=self.boolean;let packet=self.get(copy)?;let started=std::time::Instant::now();
        let mut values=Vec::new();values.try_reserve_exact(width).map_err(|_|"packed edge vector allocation")?;
        if values.capacity()!=width{return Err("packed edge vector capacity".into());}
        for wire in 0..width{values.push(boolean[((packet[wire/8]>>(wire%8))&1)as usize]);}
        let elapsed=Self::elapsed(started)?;
        let expansions=Self::add(self.metrics.vector_expansions,1)?;
        let fields=Self::add(self.metrics.expanded_fields,width as u64)?;
        let ns=Self::add(self.metrics.decode_ns,elapsed)?;
        self.metrics.vector_expansions=expansions;self.metrics.expanded_fields=fields;self.metrics.decode_ns=ns;Ok(values)
    }
    fn capacity_bytes(&self)->Option<usize>{self.entries.iter().try_fold(self.metrics.metadata_capacity_bytes,|total,(_,packet)|total.checked_add(packet.capacity()))}
    fn projected(&mut self,copy:usize,plan:&EdgePrefixPlan)->Result<Vec<Fr>,String>{
        if self.width!=plan.width{return Err("edge prefix input width mismatch".into());}
        if plan.k==0{return self.vector(copy);}
        let packet=self.get(copy)?;let began=std::time::Instant::now();let values=plan.project_bits(packet)?;
        let ns=Self::elapsed(began)?;let calls=Self::add(self.metrics.projection_calls,1)?;
        let fields=Self::add(self.metrics.projection_fields,values.len() as u64)?;
        let time=Self::add(self.metrics.projection_ns,ns)?;
        self.metrics.projection_calls=calls;self.metrics.projection_fields=fields;self.metrics.projection_ns=time;Ok(values)
    }
    fn cache_budget_bytes(&self)->Result<usize,String>{(self.width/8).checked_mul(4)
        .and_then(|n|n.checked_add(self.metrics.metadata_capacity_bytes)).ok_or("edge input cache budget overflow".into())}
    #[cfg(test)] fn vector_clone_increment(&self)->u64{0}
}

/// Immutable LSB prefix weights; one instance serves an entire owner pass.
pub(crate) struct EdgePrefixPlan{width:usize,k:usize,weights:Vec<Fr>,suffix:Vec<Fr>,patterns:Vec<Fr>}
impl EdgePrefixPlan{
    fn new(width:usize,prefix:&[Fr])->Result<Self,String>{
        if width==0||!width.is_power_of_two()||width>1<<20||prefix.len()>width.trailing_zeros()as usize{
            return Err("edge prefix geometry".into());}
        let k=prefix.len();let mut weights=gkr::eq_weights(prefix);
        let mut suffix=if k>=3{gkr::eq_weights(&prefix[3..])}else{Vec::new()};
        // Vec's first growth may reserve four Fr for a two-entry table.
        if weights.capacity()!=weights.len(){weights.shrink_to_fit();}
        if suffix.capacity()!=suffix.len(){suffix.shrink_to_fit();}
        let mut patterns=Vec::new();if k>0{
            let bits=1usize<<k.min(3);let size=1usize<<bits;patterns.try_reserve_exact(size).map_err(|_|"edge prefix pattern allocation")?;
            if patterns.capacity()!=size{return Err("edge prefix pattern capacity".into());}
            let low=if k>=3{gkr::eq_weights(&prefix[..3])}else{weights.clone()};
            for pattern in 0..size{let mut value=Fr::zero();for(bit,weight)in low.iter().enumerate(){if pattern>>bit&1!=0{value+=weight;}}patterns.push(value);}
        }
        if weights.len()!=1usize<<k||weights.capacity()!=weights.len()
            ||(k>=3&&(suffix.len()!=1usize<<(k-3)||suffix.capacity()!=suffix.len())){
            return Err("edge prefix weight capacity".into());}
        Ok(Self{width,k,weights,suffix,patterns})
    }
    fn reduced(&self)->usize{self.width>>self.k}
    fn weight(&self,wire:usize)->Fr{self.weights[wire&(self.weights.len()-1)]}
    fn reserve(&self)->Result<Vec<Fr>,String>{let mut v=Vec::new();v.try_reserve_exact(self.reduced()).map_err(|_|"edge prefix X allocation")?;
        if v.capacity()!=self.reduced(){return Err("edge prefix X capacity".into());}Ok(v)}
    fn project_fields(&self,values:&[Fr])->Result<Vec<Fr>,String>{
        if values.len()!=self.width{return Err("edge prefix field width".into());}let mut out=self.reserve()?;
        for group in values.chunks_exact(self.weights.len()){let mut value=Fr::zero();for(x,w)in group.iter().zip(&self.weights){value+=*x * *w;}out.push(value);}Ok(out)
    }
    fn project_bits(&self,bytes:&[u8])->Result<Vec<Fr>,String>{
        if self.width<8||bytes.len()!=self.width/8{return Err("edge prefix packet width".into());}
        if self.k==0{return Err("edge prefix zero uses vector".into());}let mut out=self.reserve()?;
        if self.k<3{let bits=1usize<<self.k;for h in 0..self.reduced(){let bit=h*bits;
            let pattern=(bytes[bit/8]>>(bit%8))as usize&((1usize<<bits)-1);out.push(self.patterns[pattern]);}}
        else if self.k==3{for byte in bytes{out.push(self.patterns[*byte as usize]);}}
        else{for group in bytes.chunks_exact(self.suffix.len()){let mut value=Fr::zero();for(byte,w)in group.iter().zip(&self.suffix){value+=self.patterns[*byte as usize]*w;}out.push(value);}}
        if out.len()!=self.reduced(){return Err("edge prefix result width".into());}Ok(out)
    }
}

fn multiply(a:&[Fr],b:&[Fr])->Vec<Fr>{
    let mut out=vec![Fr::zero();a.len()+b.len()-1];
    for (i,x) in a.iter().enumerate(){for (j,y) in b.iter().enumerate(){out[i+j]+=*x * *y;}}
    out
}

/// Evaluate one Boolean equality weight without allocating the full table.
/// Indices use the same least-significant-coordinate-first order as eq_weights.
fn eq_weight_at(point:&[Fr],index:usize)->Fr{
    point.iter().enumerate().fold(Fr::one(),|weight,(bit,coordinate)|{
        weight*if (index>>bit)&1==1{*coordinate}else{Fr::one()-coordinate}
    })
}

/// Chunked equality lookup for a fixed point. A row weight over dozens of
/// coordinates then needs one table lookup and multiplication per 8 bits,
/// rather than one field multiplication per coordinate and term visit.
struct EqWeightLookup{chunks:Vec<(usize,Vec<Fr>)>}
impl EqWeightLookup{
    fn new(point:&[Fr])->Self{
        let chunks=point.chunks(8).enumerate().map(|(index,coordinates)|
            (index*8,gkr::eq_weights(coordinates))).collect();
        Self{chunks}
    }
    fn at(&self,index:usize)->Fr{
        self.chunks.iter().fold(Fr::one(),|weight,(offset,table)|{
            let mask=table.len()-1;
            weight*table[(index>>offset)&mask]
        })
    }
    fn capacity_bytes(&self)->Option<usize>{
        self.chunks.iter().try_fold(self.chunks.capacity().checked_mul(std::mem::size_of::<(usize,Vec<Fr>)>())?,|sum,(_,table)|
            sum.checked_add(table.capacity().checked_mul(std::mem::size_of::<Fr>())?))
    }
}

/// Reuses the row MLE factors across sparse-term replays. Local equality
/// tables are shared by families with the same row width; family/copy factors
/// are precomputed once. If either bounded table would be too large, retain
/// the chunked whole-row lookup instead.
struct TensorRowWeightLookup<'a>{
    fallback:Option<EqWeightLookup>,member_row_bits:&'a [usize],local_tables:Vec<Option<Vec<Fr>>>,
    family_copy_scales:Vec<Vec<Fr>>,base_row_bits:usize,copy_bits:usize,
}
impl<'a> TensorRowWeightLookup<'a>{
    const MAX_LOCAL_TABLE_BYTES:usize=64*1024*1024;
    const MAX_SCALE_BYTES:usize=32*1024*1024;

    fn new(point:&[Fr],copy_bits:usize,base_row_bits:usize,member_row_bits:&'a [usize])->Self{
        let copies=1usize.checked_shl(copy_bits as u32).expect("copy dimensions were checked by caller");
        let scale_entries=member_row_bits.len().checked_mul(copies);
        let scale_bytes=scale_entries.and_then(|count|count.checked_mul(std::mem::size_of::<Fr>()));
        let mut widths=vec![false;base_row_bits+1];
        for low in member_row_bits{widths[*low]=true;}
        let local_entries=widths.iter().enumerate().filter(|(_,used)|**used)
            .try_fold(0usize,|total,(low,_)|total.checked_add(1usize.checked_shl(low as u32)?));
        let local_bytes=local_entries.and_then(|count|count.checked_mul(std::mem::size_of::<Fr>()));
        if local_bytes.is_none_or(|bytes|bytes>Self::MAX_LOCAL_TABLE_BYTES)
            ||scale_bytes.is_none_or(|bytes|bytes>Self::MAX_SCALE_BYTES){
            return Self{fallback:Some(EqWeightLookup::new(point)),member_row_bits,local_tables:Vec::new(),
                family_copy_scales:Vec::new(),base_row_bits,copy_bits};
        }

        let row_family=EqWeightLookup::new(&point[base_row_bits+copy_bits..]);
        let mut local_tables=vec![None;base_row_bits+1];
        for (low,used) in widths.into_iter().enumerate(){if used{
            local_tables[low]=Some(gkr::eq_weights(&point[..low]));
        }}
        let mut family_copy_scales=Vec::with_capacity(member_row_bits.len());
        for (family,low) in member_row_bits.iter().copied().enumerate(){
            let unused=point[low+copy_bits..base_row_bits+copy_bits].iter()
                .fold(Fr::one(),|weight,coordinate|weight*(Fr::one()-coordinate));
            let mut scales=Vec::with_capacity(copies);
            for copy in 0..copies{
                scales.push(row_family.at(family)*unused*eq_weight_at(&point[low..low+copy_bits],copy));
            }
            family_copy_scales.push(scales);
        }
        Self{fallback:None,member_row_bits,local_tables,family_copy_scales,base_row_bits,copy_bits}
    }

    fn at(&self,copy:usize,row:usize)->Fr{
        if let Some(fallback)=&self.fallback{return fallback.at((row>>self.base_row_bits)<<(self.base_row_bits+self.copy_bits)
            |(copy<<self.member_row_bits[row>>self.base_row_bits])|(row&((1usize<<self.base_row_bits)-1)));}
        let family=row>>self.base_row_bits;let local=row&((1usize<<self.base_row_bits)-1);
        let low=self.member_row_bits[family];
        self.local_tables[low].as_ref().expect("family row width table was built")[local]
            *self.family_copy_scales[family][copy]
    }

    fn local_table(&self,low:usize)->Option<&Vec<Fr>>{
        self.local_tables.get(low).and_then(Option::as_ref)
    }
    fn capacity_bytes(&self)->Option<usize>{
        let mut bytes=self.local_tables.capacity().checked_mul(std::mem::size_of::<Option<Vec<Fr>>>())?
            .checked_add(self.family_copy_scales.capacity().checked_mul(std::mem::size_of::<Vec<Fr>>())?)?;
        for table in self.local_tables.iter().flatten(){bytes=bytes.checked_add(table.capacity().checked_mul(std::mem::size_of::<Fr>())?)?;}
        for scales in &self.family_copy_scales{bytes=bytes.checked_add(scales.capacity().checked_mul(std::mem::size_of::<Fr>())?)?;}
        if let Some(fallback)=&self.fallback{bytes=bytes.checked_add(fallback.capacity_bytes()?)?;}
        Some(bytes)
    }
}

/// Factors the slot equality scalar out of one-family fallback banks. The
/// local row table is retained once; slot equality is evaluated from bounded
/// 8-bit tables rather than an owner-sized scale vector.
struct OneFamilyRowFactor<'a>{local_weights:std::borrow::Cow<'a,[Fr]>,copy_weights:EqWeightLookup}
impl<'a> OneFamilyRowFactor<'a>{
    const MAX_LOCAL_TABLE_BYTES:usize=64*1024*1024;

    fn try_new(point:&[Fr],copy_bits:usize,base_row_bits:usize,family_bits:usize,member_row_bits:&[usize],
        existing_local:Option<&'a Vec<Fr>>)->Option<Self>{
        if family_bits!=0||member_row_bits.len()!=1||member_row_bits[0]!=base_row_bits{return None;}
        let local_len=1usize.checked_shl(base_row_bits as u32)?;
        let local_bytes=local_len.checked_mul(std::mem::size_of::<Fr>())?;
        if local_bytes>Self::MAX_LOCAL_TABLE_BYTES{return None;}
        let point_end=base_row_bits.checked_add(copy_bits)?;
        if point.len()!=point_end{return None;}
        let local_weights=if let Some(table)=existing_local{
            if table.len()!=local_len
                ||table.capacity().checked_mul(std::mem::size_of::<Fr>())? > Self::MAX_LOCAL_TABLE_BYTES{return None;}
            std::borrow::Cow::Borrowed(table.as_slice())
        }else{
            let mut table=Vec::new();
            table.try_reserve_exact(local_len).ok()?;
            if table.capacity().checked_mul(std::mem::size_of::<Fr>())? > Self::MAX_LOCAL_TABLE_BYTES{return None;}
            table.push(Fr::one());
            for coordinate in &point[..base_row_bits]{
                let old_len=table.len();let new_len=old_len.checked_mul(2)?;
                if new_len>local_len{return None;}
                table.resize(new_len,Fr::zero());
                for index in 0..old_len{
                    let old=table[index];
                    table[index]=old*(Fr::one()-coordinate);
                    table[index+old_len]=old * *coordinate;
                }
            }
            if table.len()!=local_len||table.capacity().checked_mul(std::mem::size_of::<Fr>())? > Self::MAX_LOCAL_TABLE_BYTES{return None;}
            std::borrow::Cow::Owned(table)
        };
        let copy_weights=EqWeightLookup::new(&point[base_row_bits..point_end]);
        Some(Self{local_weights,copy_weights})
    }

    fn local(&self,row:usize)->Fr{self.local_weights[row]}
    fn copy(&self,copy:usize)->Fr{self.copy_weights.at(copy)}
    fn anchor_after_prefix(anchor:Fr,prefix:&[Fr])->Fr{
        prefix.iter().fold(anchor,|value,coordinate|value*(Fr::one()-coordinate))
    }
    fn add_scaled_message(sum:&mut[Fr;3],a:&[Fr],b:&[Fr],x:&[Fr],copy_scale:Fr){
        for (target,value) in sum.iter_mut().zip(gkr::quadratic_message(a,b,x)){
            *target+=copy_scale*value;
        }
    }
    fn add_anchor_message(sum:&mut[Fr;3],anchor:Fr,prefix:&[Fr]){
        let value=Self::anchor_after_prefix(anchor,prefix);
        sum[0]+=value;sum[1]-=value;
    }
    fn handoff(local_value:Fr,copy_scale:Fr,global_anchor:Fr)->Fr{
        copy_scale*local_value+global_anchor
    }
}

/// Build the U coefficient vectors after folding their low `prefix.len()`
/// coordinates directly. This is the sparse-term equivalent of repeatedly
/// applying `gkr::fold` to full-width A/B vectors.
fn direct_u_prefix_coefficients(
    width:usize,prefix:&[Fr],prefix_weights:&[Fr],copy:usize,input:&[Fr],
    mut row_weight:impl FnMut(usize,usize)->Fr,
    mut visit:impl FnMut(&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String>,
)->Result<(Vec<Fr>,Vec<Fr>),String>{
    if width==0||!width.is_power_of_two()||input.len()!=width
        ||prefix.len()>width.trailing_zeros() as usize
        ||prefix.len()>=usize::BITS as usize
        ||prefix_weights.len()!=(1usize<<prefix.len()){
        return Err("direct U prefix geometry is invalid".into());
    }
    let folded_width=width>>prefix.len();
    let mask=prefix_weights.len()-1;
    let mut a=vec![Fr::zero();folded_width];
    let mut b=vec![Fr::zero();folded_width];
    visit(&mut |term|{
        let gate=&term.gate;
        if gate.right>width||(gate.right==width&&(!gate.c2.is_zero()||!gate.c3.is_zero())){
            return Err("active direct U right anchor".into());
        }
        if gate.left==width{
            if !gate.c1.is_zero()||!gate.c3.is_zero(){return Err("active direct U left anchor".into());}
            return Ok(());
        }
        if gate.left>=width{return Err("direct U left wire outside width".into());}
        let right=if gate.right==width{Fr::zero()}else{input[gate.right]};
        let weight=prefix_weights[gate.left&mask]*row_weight(copy,term.row);
        let bucket=gate.left>>prefix.len();
        a[bucket]+=weight*(gate.c1+gate.c3*right);
        b[bucket]+=weight*(gate.c0+gate.c2*right);
        Ok(())
    })?;
    Ok((a,b))
}

pub(crate) const MAX_FIXED_V_COMMON_STATE_BYTES:usize=16*1024*1024;

#[derive(Default,Clone,Copy)]
pub(crate) struct FixedCoreVProofStats{
    pub(crate) streamed_term_callbacks:usize,
    pub(crate) common_v_template_callbacks:usize,
    pub(crate) common_state_peak_capacity_bytes:usize,
    pub(crate) u:FixedCoreUProofStats,
}

#[derive(Default,Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) struct FixedCoreUProofStats{
    pub(crate) specialized_builders:usize,
    pub(crate) generic_builders:usize,
    pub(crate) descriptor_count:usize,
    pub(crate) common_u_capacity_bytes:usize,
}

const MAX_FIXED_U_INPUT_BITS:usize=16;
const MAX_FIXED_U_ROW_BITS:usize=17;
const FIXED_U_DESCRIPTOR_BYTES:usize=16;

#[derive(Clone,Copy)]
struct FixedUDescriptor{
    term_index:u32,
    row:u32,
    left:u16,
    right:u16,
    c2_code:i8,
    c3_code:i8,
    _reserved:[u8;2],
}

impl FixedUDescriptor{
    fn try_new(term_index:usize,term:&Term,width:usize,rows:usize)->Option<Self>{
        let row=u32::try_from(term.row).ok()?;
        let term_index=u32::try_from(term_index).ok()?;
        let left=u16::try_from(term.gate.left).ok()?;
        let right=u16::try_from(term.gate.right).ok()?;
        if term.row>=rows||term.gate.left>=width||term.gate.right>=width
            ||(term.gate.c2.is_zero()&&term.gate.c3.is_zero()){
            return None;
        }
        Some(Self{term_index,row,left,right,c2_code:fixed_u_coefficient_code(term.gate.c2),
            c3_code:fixed_u_coefficient_code(term.gate.c3),_reserved:[0;2]})
    }
}

fn fixed_u_coefficient_code(value:Fr)->i8{
    if value.is_zero(){0}else if value==Fr::one(){1}else if value==-Fr::one(){-1}
    else if value==Fr::from(2u64){2}else if value==-Fr::from(2u64){-2}else{i8::MIN}
}

fn fixed_u_weighted_coefficient(weight:Fr,code:i8,exact:Fr)->Fr{
    match code{
        0=>Fr::zero(),1=>weight,-1=>-weight,2=>weight+weight,-2=>-(weight+weight),
        i8::MIN=>weight*exact,_=>unreachable!("validated fixed-U coefficient code"),
    }
}

struct FixedCoreUWorkspace{
    a0:Vec<Fr>,b0:Vec<Fr>,descriptors:Vec<FixedUDescriptor>,capacity_bytes:usize,
}

fn record_fixed_u_builder(stats:Option<&std::cell::Cell<FixedCoreUProofStats>>,specialized:bool)->Result<(),String>{
    if let Some(stats)=stats{
        let mut value=stats.get();
        let count=if specialized{&mut value.specialized_builders}else{&mut value.generic_builders};
        *count=count.checked_add(1).ok_or("fixed U builder count overflow")?;
        stats.set(value);
    }
    Ok(())
}

impl FixedCoreUWorkspace{
    fn try_new(template:&FixedCoreVTemplate<'_>,row_weights:&[Fr],fixed_v_capacity_bytes:usize,budget:usize)->Option<Self>{
        let budget=budget.min(MAX_FIXED_V_COMMON_STATE_BYTES);
        if template.input_bits>MAX_FIXED_U_INPUT_BITS||template.row_bits>MAX_FIXED_U_ROW_BITS
            ||row_weights.len()!=template.rows||std::mem::size_of::<FixedUDescriptor>()!=FIXED_U_DESCRIPTOR_BYTES{
            return None;
        }
        let mut dynamic_count=0usize;
        for (term_index,term) in template.terms.iter().enumerate(){
            if term.row>=template.rows||term.gate.left>=template.width||term.gate.right>=template.width{return None;}
            if !term.gate.c2.is_zero()||!term.gate.c3.is_zero(){
                FixedUDescriptor::try_new(term_index,term,template.width,template.rows)?;
                dynamic_count=dynamic_count.checked_add(1)?;
            }
        }
        let metadata_bytes=std::mem::size_of::<Self>();
        let requested_tables=template.width.checked_mul(2)?.checked_mul(std::mem::size_of::<Fr>())?;
        let requested_descriptors=dynamic_count.checked_mul(FIXED_U_DESCRIPTOR_BYTES)?;
        let requested_common=requested_tables.checked_add(requested_descriptors)?.checked_add(metadata_bytes)?;
        if fixed_v_capacity_bytes.checked_add(requested_common)? > budget{return None;}

        let mut a0=Vec::new();let mut b0=Vec::new();let mut descriptors=Vec::new();
        a0.try_reserve_exact(template.width).ok()?;b0.try_reserve_exact(template.width).ok()?;
        descriptors.try_reserve_exact(dynamic_count).ok()?;
        if a0.capacity()<template.width||b0.capacity()<template.width||descriptors.capacity()<dynamic_count{return None;}
        a0.resize(template.width,Fr::zero());b0.resize(template.width,Fr::zero());
        for (term_index,term) in template.terms.iter().enumerate(){
            let weight=*row_weights.get(term.row)?;
            a0[term.gate.left]+=weight*term.gate.c1;
            b0[term.gate.left]+=weight*term.gate.c0;
            if !term.gate.c2.is_zero()||!term.gate.c3.is_zero(){
                descriptors.push(FixedUDescriptor::try_new(term_index,term,template.width,template.rows)?);
            }
        }
        if descriptors.len()!=dynamic_count{return None;}
        let actual_common=a0.capacity().checked_add(b0.capacity())?
            .checked_mul(std::mem::size_of::<Fr>())?
            .checked_add(descriptors.capacity().checked_mul(std::mem::size_of::<FixedUDescriptor>())?)?
            .checked_add(metadata_bytes)?;
        let combined=fixed_v_capacity_bytes.checked_add(actual_common)?;
        if combined>budget{return None;}
        Some(Self{a0,b0,descriptors,capacity_bytes:actual_common})
    }

    fn build_boolean(&self,terms:&[Term],row_weights:&[Fr],input:&[Fr])->Option<(Vec<Fr>,Vec<Fr>)>{
        if input.len()!=self.a0.len()||input.iter().any(|value|!value.is_zero()&&!value.is_one()){return None;}
        let mut a=self.a0.clone();let mut b=self.b0.clone();
        for descriptor in &self.descriptors{
            let right=usize::from(descriptor.right);
            if input[right].is_one(){
                let term=terms.get(descriptor.term_index as usize)?;
                let weight=*row_weights.get(descriptor.row as usize)?;
                let left=usize::from(descriptor.left);
                a[left]+=fixed_u_weighted_coefficient(weight,descriptor.c3_code,term.gate.c3);
                b[left]+=fixed_u_weighted_coefficient(weight,descriptor.c2_code,term.gate.c2);
            }
        }
        Some((a,b))
    }
}

/// Immutable local relation reused for every owner in the fixed-core V path.
/// The private constructor validates dimensions, sorted rows and all endpoints
/// before the producer can load a witness or bind a transcript.
pub(crate) struct FixedCoreVTemplate<'a>{
    terms:&'a [Term],input_bits:usize,owner_bits:usize,row_bits:usize,
    rows:usize,width:usize,owners:usize,
}
impl<'a> FixedCoreVTemplate<'a>{
    pub(crate) fn try_new(circuit:&'a crate::sparse::Circuit,input_bits:usize,owner_bits:usize,row_bits:usize)->Result<Self,String>{
        let shape=crate::sparse::validate(circuit,0).map_err(|error|error.to_string())?;
        let width=1usize.checked_shl(input_bits as u32).ok_or("fixed V input width overflow")?;
        let rows=1usize.checked_shl(row_bits as u32).ok_or("fixed V row count overflow")?;
        let owners=1usize.checked_shl(owner_bits as u32).ok_or("fixed V owner count overflow")?;
        input_bits.checked_add(owner_bits).filter(|bits|*bits<=24).ok_or("fixed V input dimensions exceed sparse verifier bound")?;
        row_bits.checked_add(owner_bits).filter(|bits|*bits<=24).ok_or("fixed V row dimensions exceed sparse verifier bound")?;
        if shape.input_bits!=input_bits||shape.row_bits!=row_bits||circuit.input_len!=width||circuit.row_count!=rows{
            return Err(GkrError::InvalidInputWidth.to_string());
        }
        let mut previous=None;
        for term in &circuit.terms{
            if previous.is_some_and(|row|term.row<row){return Err("fixed V rows are not in canonical nondecreasing order".into());}
            if term.gate.left>=width||term.gate.right>=width{return Err(GkrError::InvalidWireIndex.to_string());}
            previous=Some(term.row);
        }
        let point_bits=input_bits.checked_add(owner_bits).ok_or("fixed V point size overflow")?;
        let local_state_bytes=width.checked_mul(3).and_then(|count|count.checked_add(owners.checked_mul(3)?))
            .and_then(|count|count.checked_add(point_bits))
            .and_then(|count|count.checked_mul(std::mem::size_of::<Fr>()))
            .and_then(|bytes|bytes.checked_add(std::mem::size_of::<FixedVWorkspace>()))
            .ok_or("fixed V common-state size overflow")?;
        if local_state_bytes>MAX_FIXED_V_COMMON_STATE_BYTES{return Err("fixed V common-state cap exceeded".into());}
        Ok(Self{terms:&circuit.terms,input_bits,owner_bits,row_bits,rows,width,owners})
    }

    fn reserve_workspace(&self)->Result<FixedVWorkspace,String>{
        let mut c=Vec::new();let mut d=Vec::new();let mut x=Vec::new();
        let mut high_c=Vec::new();let mut high_d=Vec::new();let mut high_x=Vec::new();let mut point=Vec::new();
        for (values,length) in [(&mut c,self.width),(&mut d,self.width),(&mut x,self.width),
            (&mut high_c,self.owners),(&mut high_d,self.owners),(&mut high_x,self.owners)]{
            values.try_reserve_exact(length).map_err(|_|"fixed V common-state reservation failed")?;
            values.resize(length,Fr::zero());
            let bytes=values.capacity().checked_mul(std::mem::size_of::<Fr>()).ok_or("fixed V common-state capacity overflow")?;
            if bytes>MAX_FIXED_V_COMMON_STATE_BYTES{return Err("fixed V common-state cap exceeded after reservation".into());}
        }
        point.try_reserve_exact(self.input_bits+self.owner_bits).map_err(|_|"fixed V point reservation failed")?;
        let capacity_bytes=c.capacity().checked_add(d.capacity()).and_then(|n|n.checked_add(x.capacity()))
            .and_then(|n|n.checked_add(high_c.capacity())).and_then(|n|n.checked_add(high_d.capacity()))
            .and_then(|n|n.checked_add(high_x.capacity()))
            .and_then(|n|n.checked_add(point.capacity()))
            .and_then(|n|n.checked_mul(std::mem::size_of::<Fr>()))
            .and_then(|bytes|bytes.checked_add(std::mem::size_of::<FixedVWorkspace>()))
            .ok_or("fixed V common-state capacity overflow")?;
        if capacity_bytes>MAX_FIXED_V_COMMON_STATE_BYTES{return Err("fixed V common-state cap exceeded after reservation".into());}
        Ok(FixedVWorkspace{c,d,x,high_c,high_d,high_x,point,capacity_bytes})
    }
}

// Added common scratch only: all seven vector capacities and their descriptors.
// Existing generic row/U tables, loader vectors and GKR proof state are separate.
struct FixedVWorkspace{c:Vec<Fr>,d:Vec<Fr>,x:Vec<Fr>,high_c:Vec<Fr>,high_d:Vec<Fr>,high_x:Vec<Fr>,point:Vec<Fr>,capacity_bytes:usize}

fn fixed_v_cache_bound(owners:usize,width:usize,term_count:usize)->Option<usize>{
    let field_bytes=std::mem::size_of::<Fr>();let sparse_entry_bytes=std::mem::size_of::<(usize,Fr)>();
    let descriptors=owners.checked_mul(std::mem::size_of::<(SparseFieldVector,SparseFieldVector,Vec<Fr>)>())?;
    let retained_x=owners.checked_mul(width)?.checked_mul(field_bytes)?;
    let sparse=owners.checked_mul(term_count)?.checked_add(owners)?.checked_mul(2)?.checked_mul(sparse_entry_bytes)?;
    retained_x.checked_add(sparse.checked_mul(2)?)?.checked_add(descriptors)
}

pub(crate) fn prove_fixed_core_v(
    template:&FixedCoreVTemplate<'_>,load_copy:impl FnMut(usize)->Result<Vec<Fr>,String>,
    transcript:&mut Transcript,bind:impl FnOnce(&mut Transcript),
    wiring:impl Fn(&[Fr],&[Fr],&[Fr])->Result<[Fr;4],String>,
)->Result<(GkrProof,InputClaim,FixedCoreVProofStats),String>{
    prove_fixed_core_v_with_budget(template,MAX_INCREMENTAL_CACHE_STATE_BYTES,load_copy,transcript,bind,wiring)
}

pub(crate) fn prove_fixed_core_uv(
    template:&FixedCoreVTemplate<'_>,load_copy:impl FnMut(usize)->Result<Vec<Fr>,String>,
    transcript:&mut Transcript,bind:impl FnOnce(&mut Transcript),
    wiring:impl Fn(&[Fr],&[Fr],&[Fr])->Result<[Fr;4],String>,
)->Result<(GkrProof,InputClaim,FixedCoreVProofStats),String>{
    prove_fixed_core_uv_with_budget(template,MAX_INCREMENTAL_CACHE_STATE_BYTES,load_copy,transcript,bind,wiring,true,
        MAX_FIXED_V_COMMON_STATE_BYTES)
}

fn prove_fixed_core_v_with_budget(
    template:&FixedCoreVTemplate<'_>,cache_budget:usize,load_copy:impl FnMut(usize)->Result<Vec<Fr>,String>,
    transcript:&mut Transcript,bind:impl FnOnce(&mut Transcript),
    wiring:impl Fn(&[Fr],&[Fr],&[Fr])->Result<[Fr;4],String>,
)->Result<(GkrProof,InputClaim,FixedCoreVProofStats),String>{
    prove_fixed_core_uv_with_budget(template,cache_budget,load_copy,transcript,bind,wiring,false,
        MAX_FIXED_V_COMMON_STATE_BYTES)
}

fn prove_fixed_core_uv_with_budget(
    template:&FixedCoreVTemplate<'_>,cache_budget:usize,load_copy:impl FnMut(usize)->Result<Vec<Fr>,String>,
    transcript:&mut Transcript,bind:impl FnOnce(&mut Transcript),
    wiring:impl Fn(&[Fr],&[Fr],&[Fr])->Result<[Fr;4],String>,enable_u:bool,u_capacity_budget:usize,
)->Result<(GkrProof,InputClaim,FixedCoreVProofStats),String>{
    let mut workspace=Some(template.reserve_workspace()?);
    let mut stats=FixedCoreVProofStats::default();
    let streamed_callbacks=std::cell::Cell::new(0usize);let template_callbacks=std::cell::Cell::new(0usize);
    let u_stats=std::cell::Cell::new(FixedCoreUProofStats::default());
    let state_capacity=std::cell::Cell::new(workspace.as_ref().unwrap().capacity_bytes);
    let (proof,claim)=prove_inner(template.input_bits,template.owner_bits,template.row_bits,0,&[template.row_bits],
        None,None,None,cache_budget,false,Some(template),workspace.as_mut(),Some(&streamed_callbacks),Some(&template_callbacks),Some(&state_capacity),
        enable_u.then_some(&u_stats),u_capacity_budget,
        None,None,None,GroupedDimensionPolicy::Generic24,
        load_copy,transcript,|t|{bind(t);Ok(())},
        |_owner,sink|{for term in template.terms{sink(term.clone())?;}Ok(())},wiring)?;
    stats.streamed_term_callbacks=streamed_callbacks.get();
    stats.common_v_template_callbacks=template_callbacks.get();
    stats.common_state_peak_capacity_bytes=state_capacity.get();
    stats.u=u_stats.get();
    Ok((proof,claim,stats))
}

#[cfg(test)]
pub(crate) fn prove_fixed_core_v_with_cache_budget_for_test(
    template:&FixedCoreVTemplate<'_>,cache_budget_bytes:Option<usize>,
    load_copy:impl FnMut(usize)->Result<Vec<Fr>,String>,transcript:&mut Transcript,
    bind:impl FnOnce(&mut Transcript),wiring:impl Fn(&[Fr],&[Fr],&[Fr])->Result<[Fr;4],String>,
)->Result<(GkrProof,InputClaim,FixedCoreVProofStats),String>{
    prove_fixed_core_v_with_budget(template,cache_budget_bytes.unwrap_or(MAX_INCREMENTAL_CACHE_STATE_BYTES),
        load_copy,transcript,bind,wiring)
}

#[cfg(test)]
pub(crate) fn prove_fixed_core_uv_with_cache_budget_for_test(
    template:&FixedCoreVTemplate<'_>,cache_budget_bytes:Option<usize>,
    load_copy:impl FnMut(usize)->Result<Vec<Fr>,String>,transcript:&mut Transcript,
    bind:impl FnOnce(&mut Transcript),wiring:impl Fn(&[Fr],&[Fr],&[Fr])->Result<[Fr;4],String>,
)->Result<(GkrProof,InputClaim,FixedCoreVProofStats),String>{
    prove_fixed_core_uv_with_budget(template,cache_budget_bytes.unwrap_or(MAX_INCREMENTAL_CACHE_STATE_BYTES),
        load_copy,transcript,bind,wiring,true,MAX_FIXED_V_COMMON_STATE_BYTES)
}

#[cfg(test)]
fn prove_fixed_core_uv_with_u_budget_for_test(
    template:&FixedCoreVTemplate<'_>,cache_budget_bytes:Option<usize>,u_capacity_budget:usize,
    load_copy:impl FnMut(usize)->Result<Vec<Fr>,String>,transcript:&mut Transcript,
    bind:impl FnOnce(&mut Transcript),wiring:impl Fn(&[Fr],&[Fr],&[Fr])->Result<[Fr;4],String>,
)->Result<(GkrProof,InputClaim,FixedCoreVProofStats),String>{
    prove_fixed_core_uv_with_budget(template,cache_budget_bytes.unwrap_or(MAX_INCREMENTAL_CACHE_STATE_BYTES),
        load_copy,transcript,bind,wiring,true,u_capacity_budget)
}

type SparseFieldVector=Vec<(usize,Fr)>;
fn compact_nonzero(values:Vec<Fr>)->SparseFieldVector{
    let count=values.iter().filter(|value|!value.is_zero()).count();
    let mut sparse=Vec::with_capacity(count);
    sparse.extend(values.into_iter().enumerate().filter(|(_,value)|!value.is_zero()));
    sparse
}

/// Sort and combine a sparse coefficient bank without allocating a second
/// width-sized vector. Contributions to one wire are additive, so canonical
/// wire order retains the same field element as dense accumulation.
fn coalesce_nonzero_in_place(values:&mut SparseFieldVector){
    values.sort_unstable_by_key(|entry|entry.0);
    let mut write=0usize;let mut read=0usize;
    while read<values.len(){
        let wire=values[read].0;let mut value=Fr::zero();
        while read<values.len()&&values[read].0==wire{value+=values[read].1;read+=1;}
        if !value.is_zero(){values[write]=(wire,value);write+=1;}
    }
    values.truncate(write);
}

/// Fold a sparse MLE vector over its next low bit, preserving sorted indices.
fn sparse_fold(values:&SparseFieldVector,coordinate:Fr)->SparseFieldVector{
    let mut folded=Vec::with_capacity((values.len()+1)/2);let mut cursor=0;
    while cursor<values.len(){
        let pair=values[cursor].0>>1;let mut low=Fr::zero();let mut high=Fr::zero();
        while cursor<values.len()&&values[cursor].0>>1==pair{
            if values[cursor].0&1==0{low=values[cursor].1}else{high=values[cursor].1}
            cursor+=1;
        }
        let value=low+coordinate*(high-low);
        if !value.is_zero(){folded.push((pair,value));}
    }
    folded
}

fn sparse_value(values:&SparseFieldVector,index:usize)->Fr{
    values.binary_search_by_key(&index,|entry|entry.0).map_or_else(|_|Fr::zero(),|position|values[position].1)
}

/// Dense quadratic GKR message computed by merging the sorted sparse A/B
/// banks, without a width-sized or term-count-sized scratch allocation.
fn sparse_quadratic_message(a:&SparseFieldVector,b:&SparseFieldVector,x:&[Fr])->[Fr;3]{
    let(mut ia,mut ib)=(0usize,0usize);let mut coefficients=[Fr::zero();3];
    while ia<a.len()||ib<b.len(){
        let next_a=a.get(ia).map_or(usize::MAX,|(index,_)|index>>1);
        let next_b=b.get(ib).map_or(usize::MAX,|(index,_)|index>>1);
        let pair=next_a.min(next_b);
        let low=pair*2;let a_low=sparse_value(a,low);let a_high=sparse_value(a,low+1);
        let b_low=sparse_value(b,low);let b_high=sparse_value(b,low+1);
        while ia<a.len()&&a[ia].0>>1==pair{ia+=1;}
        while ib<b.len()&&b[ib].0>>1==pair{ib+=1;}
        let x_low=x[low];let x_high=x[low+1];let da=a_high-a_low;let dx=x_high-x_low;let db=b_high-b_low;
        coefficients[0]+=a_low*x_low+b_low;
        coefficients[1]+=a_low*dx+da*x_low+db;
        coefficients[2]+=da*dx;
    }
    coefficients
}

fn copy_line_selector(copy:usize,u:&[Fr],v:&[Fr])->Vec<Fr>{
    let mut out=vec![Fr::one()];
    for (bit,(left,right)) in u.iter().zip(v).enumerate(){
        let factor=if (copy>>bit)&1==1{[*left,*right-*left]}else{[Fr::one()-left,*left-*right]};
        out=multiply(&out,&factor);
    }
    out
}

fn send_round(poly:Vec<Fr>,claim:&mut Fr,rounds:&mut Vec<Vec<Fr>>,transcript:&mut Transcript)->Result<Fr,GkrError>{
    if poly[0]+gkr::eval_polynomial(&poly,Fr::one())!=*claim{return Err(GkrError::SumcheckIdentity);}
    gkr::append_polynomial(transcript,b"gkr-sumcheck-polynomial",&poly);
    let challenge=transcript.challenge_scalar(b"gkr-sumcheck-challenge");
    *claim=gkr::eval_polynomial(&poly,challenge);rounds.push(poly);Ok(challenge)
}

fn scaled_common_quadratic_message(c:&[Fr],d:&[Fr],x:&[Fr],scale:Fr)->[Fr;3]{
    let mut coefficients=[Fr::zero();3];
    for index in (0..c.len()).step_by(2){
        let c0=c[index];let c1=c[index+1];let d0=d[index];let d1=d[index+1];
        let x0=x[index];let x1=x[index+1];let dc=c1-c0;let dd=d1-d0;let dx=x1-x0;
        coefficients[0]+=c0*x0+scale*d0;
        coefficients[1]+=c0*dx+dc*x0+scale*dd;
        coefficients[2]+=dc*dx;
    }
    coefficients
}

fn prove_fixed_v_tail(
    template:&FixedCoreVTemplate<'_>,workspace:&mut FixedVWorkspace,input_bits:usize,owner_bits:usize,
    load_copy:&mut impl FnMut(usize)->Result<Vec<Fr>,String>,r:&[Fr],u:&[Fr],row_weights:&TensorRowWeightLookup,
    u_local_weights:&[Fr],claim:&mut Fr,
    rounds:&mut Vec<Vec<Fr>>,transcript:&mut Transcript,left_value:Fr,
    wiring:&impl Fn(&[Fr],&[Fr],&[Fr])->Result<[Fr;4],String>,
    template_callbacks:&std::cell::Cell<usize>,state_capacity_stats:&std::cell::Cell<usize>,
)->Result<(GkrProof,InputClaim),String>{
    let width=template.width;let copies=template.owners;
    if r.len()!=template.row_bits.checked_add(owner_bits).ok_or("fixed V row point dimensions overflow")?
        ||u.len()!=input_bits.checked_add(owner_bits).ok_or("fixed V input point dimensions overflow")?{
        return Err(GkrError::PointDimension.to_string());
    }
    let row_owner_point=&r[template.row_bits..];let u_owner_point=&u[input_bits..];
    if row_owner_point.len()!=owner_bits||u_owner_point.len()!=owner_bits||u_local_weights.len()!=width{
        return Err(GkrError::PointDimension.to_string());
    }
    state_capacity_stats.set(state_capacity_stats.get().max(workspace.capacity_bytes));
    let owner_scale=|owner:usize|eq_weight_at(row_owner_point,owner)*eq_weight_at(u_owner_point,owner);
    let sum_scale=(0..copies).fold(Fr::zero(),|sum,owner|sum+owner_scale(owner));
    workspace.c.fill(Fr::zero());workspace.d.fill(Fr::zero());workspace.x.fill(Fr::zero());
    for term in template.terms{
        let gate=&term.gate;
        let row_weight=if let Some(local)=row_weights.local_table(template.row_bits){
            *local.get(term.row).ok_or_else(||GkrError::InvalidWireIndex.to_string())?
        }else{eq_weight_at(&r[..template.row_bits],term.row)};
        let left_weight=*u_local_weights.get(gate.left).ok_or_else(||GkrError::InvalidWireIndex.to_string())?;
        let weight=row_weight*left_weight;
        workspace.c[gate.right]+=weight*(gate.c2+gate.c3*left_value);
        workspace.d[gate.right]+=weight*(gate.c0+gate.c1*left_value);
        template_callbacks.set(template_callbacks.get().checked_add(1).ok_or("fixed V callback count overflow")?);
    }
    for owner in 0..copies{
        let input=read_copy(load_copy,owner,width)?;
        let scale=owner_scale(owner);
        for (target,value) in workspace.x.iter_mut().zip(input){*target+=scale*value;}
    }
    let mut v_local=std::mem::take(&mut workspace.point);
    for _ in 0..input_bits{
        let polynomial=scaled_common_quadratic_message(&workspace.c,&workspace.d,&workspace.x,sum_scale);
        let challenge=send_round(polynomial.to_vec(),claim,rounds,transcript).map_err(|error|error.to_string())?;
        gkr::fold(&mut workspace.c,challenge);gkr::fold(&mut workspace.d,challenge);gkr::fold(&mut workspace.x,challenge);
        v_local.push(challenge);
    }
    workspace.high_c.fill(Fr::zero());workspace.high_d.fill(Fr::zero());workspace.high_x.fill(Fr::zero());
    for owner in 0..copies{
        let mut input=read_copy(load_copy,owner,width)?;
        for challenge in &v_local{gkr::fold(&mut input,*challenge);}
        let scale=owner_scale(owner);
        workspace.high_c[owner]=scale*workspace.c[0];workspace.high_d[owner]=scale*workspace.d[0];
        workspace.high_x[owner]=input[0];
    }
    let high_c=std::mem::take(&mut workspace.high_c);let high_d=std::mem::take(&mut workspace.high_d);
    let (v_high,right_value)=gkr::prove_phase(high_c,high_d,&workspace.high_x,
        claim,rounds,transcript).map_err(|error|error.to_string())?;
    let mut v=v_local;v.extend(v_high);
    let coefficients=wiring(r,u,&v)?;
    if coefficients[0]+coefficients[1]*left_value+coefficients[2]*right_value+coefficients[3]*left_value*right_value!=*claim{
        return Err(GkrError::TerminalExpression.to_string());
    }
    let mut line=vec![Fr::zero();input_bits+owner_bits+1];
    for owner in 0..copies{
        let input=read_copy(load_copy,owner,width)?;
        let local=gkr::line_polynomial(&input,&u[..input_bits],&v[..input_bits]);
        let selector=copy_line_selector(owner,&u[input_bits..],&v[input_bits..]);
        for (sum,value) in line.iter_mut().zip(multiply(&local,&selector)){*sum+=value;}
    }
    let left_endpoint=line[0];let right_endpoint=gkr::eval_polynomial(&line,Fr::one());
    if left_endpoint!=left_value||right_endpoint!=right_value{return Err(GkrError::LineEndpoints.to_string());}
    transcript.append_scalar(b"gkr-left-value",&left_value);transcript.append_scalar(b"gkr-right-value",&right_value);
    gkr::append_polynomial(transcript,b"gkr-line-polynomial",&line);
    let challenge=transcript.challenge_scalar(b"gkr-line-challenge");
    let point=gkr::line_point(u,&v,challenge);let value=gkr::eval_polynomial(&line,challenge);
    Ok((GkrProof{layers:vec![LayerProof{rounds:std::mem::take(rounds),left_value,right_value,line_coefficients:line}]},InputClaim{point,value}))
}

/// Per-path cache/state ceiling; this is not a whole-process memory budget.
pub(crate) const MAX_INCREMENTAL_CACHE_STATE_BYTES:usize=512*1024*1024;
#[cfg(test)]
const H21_CAPACITY_ONLY_MAX_BYTES:usize=1024*1024*1024;

/// Immutable, test-only owner grouping for the opt-in role1 grouped-V path.
/// The native caller derives group_by_copy from its admitted DAA owner classes.
#[derive(Clone,Debug)]
pub(crate) struct GroupedVAdmission{
    group_by_copy:Box<[usize]>,expected_terms_per_group:Box<[usize]>,
}
impl GroupedVAdmission{
    pub(crate) fn try_new(copy_bits:usize,group_by_copy:&[usize],expected_terms_per_group:&[usize])->Result<Self,String>{
        if copy_bits>24||copy_bits>=usize::BITS as usize{
            return Err("grouped V copy dimension exceeds the supported bound".into());
        }
        let copies=1usize.checked_shl(copy_bits as u32).ok_or("grouped V copy count overflow")?;
        if group_by_copy.len()!=copies||expected_terms_per_group.is_empty()||expected_terms_per_group.len()>2
            ||expected_terms_per_group.iter().any(|count|*count==0||*count>(1usize<<20)){
            return Err("grouped V admission dimensions or term counts are invalid".into());
        }
        let group_count=expected_terms_per_group.len();let mut owners=vec![0usize;group_count];
        for group in group_by_copy{if *group>=group_count{return Err("grouped V owner group is outside the admitted groups".into());}
            owners[*group]=owners[*group].checked_add(1).ok_or("grouped V owner count overflow")?;}
        if owners.iter().any(|count|*count==0){return Err("grouped V admission contains an empty group".into());}
        Ok(Self{group_by_copy:group_by_copy.to_vec().into_boxed_slice(),
            expected_terms_per_group:expected_terms_per_group.to_vec().into_boxed_slice()})
    }
}

/// Private to this producer. No public hook accepts this policy or numeric
/// permission. Only the sealed plan-owned test entry selects the native case.
#[derive(Clone,Copy,Debug)]
enum GroupedDimensionPolicy{Generic24,NativeRole1Exact{extra_capacity_bytes:usize},NativeRole3Exact{extra_capacity_bytes:usize},
    Historical50Role1{extra_capacity_bytes:usize},Historical50Role3{extra_capacity_bytes:usize},
    #[cfg(test)] H21CapacityOnly{limit_bytes:usize}}
impl GroupedDimensionPolicy{
    fn extra_capacity_bytes(self)->usize{match self{Self::Generic24=>0,Self::NativeRole1Exact{extra_capacity_bytes}|Self::NativeRole3Exact{extra_capacity_bytes}
        |Self::Historical50Role1{extra_capacity_bytes}|Self::Historical50Role3{extra_capacity_bytes}=>extra_capacity_bytes,
        #[cfg(test)] Self::H21CapacityOnly{..}=>0}}
    fn component_limit_bytes(self)->usize{match self{
        #[cfg(test)] Self::H21CapacityOnly{limit_bytes}=>limit_bytes,
        _=>MAX_INCREMENTAL_CACHE_STATE_BYTES}}
    fn component_limit_error(self)->&'static str{match self{
        #[cfg(test)] Self::H21CapacityOnly{..}=>"H21 capacity-only component exceeds policy limit",
        _=>"capacity46 component exceeds 512 MiB"}}
    fn dimensions_allowed(self,input_bits:usize,copy_bits:usize,base_row_bits:usize)->bool{
        match self{
            Self::Generic24=>input_bits<=24&&copy_bits<=24
                &&input_bits.checked_add(copy_bits).is_some_and(|bits|bits<=24)
                &&base_row_bits.checked_add(copy_bits).is_some_and(|bits|bits<=24),
            Self::NativeRole1Exact{..}=>(input_bits,copy_bits,base_row_bits)==(20,12,19),
            Self::NativeRole3Exact{..}=>(input_bits,copy_bits,base_row_bits)==(13,12,14),
            Self::Historical50Role1{..}=>(input_bits,copy_bits,base_row_bits)==(20,12,19),
            Self::Historical50Role3{..}=>(input_bits,copy_bits,base_row_bits)==(13,12,14),
            #[cfg(test)] Self::H21CapacityOnly{..}=>(input_bits,copy_bits,base_row_bits)==(20,21,19),
        }
    }
    fn validate_census(self,admission:&GroupedVAdmission)->Result<(),String>{
        match self{
            #[cfg(test)] Self::H21CapacityOnly{limit_bytes}=>{
                if limit_bytes>H21_CAPACITY_ONLY_MAX_BYTES{return Err("H21 capacity-only cap exceeds 1 GiB".into());}
                if admission.group_by_copy.len()!=(1usize<<21)
                    ||admission.expected_terms_per_group.as_ref()!=[396561,388369]{
                    return Err("H21 capacity-only topology or template terms rejected".into());
                }
                let mut counts=[0usize;2];
                for group in admission.group_by_copy.iter(){
                    if *group>=2{return Err("H21 capacity-only group label rejected".into());}
                    counts[*group]+=1;
                }
                if counts!=[2_088_650,8_502]{return Err("H21 capacity-only group census rejected".into());}
                return Ok(());
            }
            Self::Historical50Role1{extra_capacity_bytes}=>return Self::NativeRole1Exact{extra_capacity_bytes}.validate_census(admission),
            Self::Historical50Role3{extra_capacity_bytes}=>return Self::NativeRole3Exact{extra_capacity_bytes}.validate_census(admission),
            _=>(),
        }
        if matches!(self,Self::NativeRole1Exact{..})
            &&(admission.group_by_copy.len()!=4096||admission.expected_terms_per_group.as_ref()!=[396561,388369]
                ||admission.group_by_copy.iter().enumerate().any(|(owner,group)|*group!=usize::from(owner==3072))){
            return Err("native role1 grouped topology/count/order rejected".into());
        }
        if matches!(self,Self::NativeRole3Exact{..})&&(admission.group_by_copy.len()!=4096
            ||admission.expected_terms_per_group.as_ref()!=[288158]||admission.group_by_copy.iter().any(|group|*group!=0)){
            return Err("native role3 grouped topology/count/order rejected".into());}
        Ok(())
    }
    fn validate_route(self,input_bits:usize,copy_bits:usize,base_row_bits:usize,family_bits:usize,
        member_row_bits:&[usize],cache_budget:usize,direct_u:bool,fixed_v:bool,boolean_u:bool,
        admission:Option<&GroupedVAdmission>)->Result<(),String>{
        match self{
            #[cfg(test)] Self::H21CapacityOnly{..}=>return Err("H21 capacity-only policy cannot enter a producer route".into()),
            Self::Historical50Role1{extra_capacity_bytes}=>return Self::NativeRole1Exact{extra_capacity_bytes}
                .validate_route(input_bits,copy_bits,base_row_bits,family_bits,member_row_bits,cache_budget,direct_u,fixed_v,boolean_u,admission),
            Self::Historical50Role3{extra_capacity_bytes}=>return Self::NativeRole3Exact{extra_capacity_bytes}
                .validate_route(input_bits,copy_bits,base_row_bits,family_bits,member_row_bits,cache_budget,direct_u,fixed_v,boolean_u,admission),
            _=>(),
        }
        if matches!(self,Self::NativeRole1Exact{..}){
            if !self.dimensions_allowed(input_bits,copy_bits,base_row_bits)||family_bits!=0
                ||member_row_bits!=[19]||cache_budget!=0||!direct_u||fixed_v||!boolean_u{
                return Err("native role1 exact producer geometry/route rejected".into());
            }
            self.validate_census(admission.ok_or("native role1 grouped admission missing")?)?;
        }
        if matches!(self,Self::NativeRole3Exact{..}){
            if !self.dimensions_allowed(input_bits,copy_bits,base_row_bits)||family_bits!=0||member_row_bits!=[14]
                ||cache_budget!=0||!direct_u||fixed_v||!boolean_u{return Err("native role3 exact producer geometry/route rejected".into());}
            self.validate_census(admission.ok_or("native role3 grouped admission missing")?)?;
        }
        Ok(())
    }
}

#[derive(Clone,Debug,Default)]
pub(crate) struct GroupedVStats{
    pub(crate) group_count:usize,
    pub(crate) group_owner_counts:Vec<usize>,
    pub(crate) group_term_counts:Vec<usize>,
    pub(crate) group_weight_sums:Vec<Fr>,
    pub(crate) group_d_local_contributions:Vec<Fr>,
    pub(crate) baseline_term_callbacks:usize,
    pub(crate) template_term_count:usize,
    pub(crate) template_capacity_bytes:usize,
    pub(crate) bank_term_callbacks:usize,
    pub(crate) handoff_term_callbacks:usize,
    pub(crate) grouped_state_peak_capacity_bytes:usize,
    pub(crate) local_rounds:usize,
    pub(crate) owner_handoff_count:usize,
    pub(crate) baseline_elapsed_ns:u64,
    pub(crate) bank_build_elapsed_ns:u64,
    pub(crate) local_v_elapsed_ns:u64,
    pub(crate) owner_handoff_elapsed_ns:u64,
    // Extra retained state and native loader scratch for the Boolean test
    // hook. Zero preserves the existing grouped-V accounting by default.
    private_capacity_reservation_bytes:usize,
}

/// Statistics for the private Boolean-U experiment. Capacities include a
/// declared native packed-loader scratch reservation, independently of RSS.
#[derive(Clone,Debug,Default)]
pub(crate) struct BooleanUPreweightStats{
    pub(crate) prefix_builds:usize,
    pub(crate) shared_term_iterations:usize,
    pub(crate) owner_term_selections:usize,
    pub(crate) boolean_checked_loads:usize,
    pub(crate) boolean_checked_fields:usize,
    pub(crate) zero_anchor_sweep_skipped:bool,
    pub(crate) preweight_entry_size_bytes:usize,
    pub(crate) preweight_peak_capacity_bytes:usize,
    pub(crate) u_state_peak_capacity_bytes:usize,
    pub(crate) u_preflight_capacity_bound_bytes:usize,
    pub(crate) u_prefix_preweight_elapsed_ns:u64,
    pub(crate) u_owner_selection_elapsed_ns:u64,
    pub(crate) u_x_fold_elapsed_ns:u64,
    /// Baseline, row preparation, prefix preparation, owner banks, handoff,
    /// and the projected high-phase scratch, respectively.
    pub(crate) u_phase_peak_capacity_bytes:[usize;6],
}
impl BooleanUPreweightStats{
    fn record_capacity(&mut self,phase:usize,bytes:usize)->Result<(),String>{
        if phase>=self.u_phase_peak_capacity_bytes.len()
            ||bytes>MAX_INCREMENTAL_CACHE_STATE_BYTES
            ||bytes>self.u_preflight_capacity_bound_bytes{
            return Err("Boolean U phase capacity exceeds its preflight or 512 MiB limit".into());
        }
        self.u_phase_peak_capacity_bytes[phase]=self.u_phase_peak_capacity_bytes[phase].max(bytes);
        self.u_state_peak_capacity_bytes=self.u_state_peak_capacity_bytes.max(bytes);Ok(())
    }
}

// Private experiment; legacy entry points always select Legacy with no table stats.
#[derive(Clone,Copy,PartialEq,Eq)]
enum BooleanXFoldMode{Legacy,Subset4,#[cfg(test)] FusedPrefixK1}
#[derive(Default,Debug,Clone)]
pub(crate) struct BooleanSubset4Stats{
    pub(crate) builds:usize,pub(crate) values_built:usize,pub(crate) build_additions:usize,
    pub(crate) apply_calls:usize,pub(crate) lookups:usize,pub(crate) apply_additions:usize,
    pub(crate) mask_bits:usize,pub(crate) table_payload_peak_bytes:usize,
    pub(crate) extra_reserved_bytes:usize,pub(crate) component_reserved_peak_bytes:usize,
    pub(crate) preflight_bound_bytes:usize,pub(crate) build_ns:u64,pub(crate) apply_ns:u64,
}
struct BooleanSubset4Table{k:usize,values:Vec<Fr>}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
enum UPhase{Baseline,RowBuild,Prefix,Bank,Table,HighReserve,Load,Apply,Send,High,PostHigh}
#[derive(Default,Clone,Copy)]
struct ULive{prefix:Option<usize>,bank:bool,table:bool,owner:bool,coeff:bool}
#[derive(Clone)]
struct UCapacityPlan{
    bits:usize,copies:usize,rows:usize,width:usize,owners:usize,groups:usize,private:usize,
    templates:usize,row_live:usize,copy_lookup:usize,bank:usize,small:usize,loader:usize,
    u_max:usize,v_max:usize,component:usize,
}
fn u_sum(values:&[usize])->Result<usize,String>{values.iter().try_fold(0usize,|a,b|a.checked_add(*b))
    .ok_or("capacity46 arithmetic overflow".into())}
fn u_mul(a:usize,b:usize)->Result<usize,String>{a.checked_mul(b).ok_or("capacity46 arithmetic overflow".into())}
impl UCapacityPlan{
    fn metadata()->Result<usize,String>{u_sum(&[std::mem::size_of::<Self>(),std::mem::size_of::<Option<Self>>(),
        2*std::mem::size_of::<&Self>(),std::mem::size_of::<ULive>(),std::mem::size_of::<UPhase>(),
        // Bounded plan/check temporaries: no heap or owner-sized hidden cache.
        32*std::mem::size_of::<usize>(),8*std::mem::size_of::<Fr>()])}
    fn lookup(bits:usize)->Result<usize,String>{
        let mut bytes=0;for offset in (0..bits).step_by(8){let n=1usize.checked_shl((bits-offset).min(8) as u32)
            .ok_or("capacity46 arithmetic overflow")?;
            bytes=u_sum(&[bytes,u_mul(n.max(4),std::mem::size_of::<Fr>())?,std::mem::size_of::<(usize,Vec<Fr>)>()])?;}Ok(bytes)
    }
    fn new(bits:usize,copies:usize,rows:usize,a:&GroupedVAdmission,policy:GroupedDimensionPolicy)->Result<Self,String>{
        if bits>24||rows>21||!policy.dimensions_allowed(bits,copies,rows){return Err("capacity46 dimensions".into());}
        policy.validate_census(a)?;
        let width=1usize.checked_shl(bits as u32).ok_or("capacity46 arithmetic overflow")?;
        let owners=1usize.checked_shl(copies as u32).ok_or("capacity46 arithmetic overflow")?;
        if a.group_by_copy.len()!=owners{return Err("capacity46 owner roster".into());}
        let groups=a.expected_terms_per_group.len();
        if groups==0||groups>2||a.expected_terms_per_group.iter().any(|n|*n==0||*n>(1usize<<20))
            ||a.group_by_copy.iter().any(|g|*g>=groups)
            ||(0..groups).any(|g|!a.group_by_copy.contains(&g)){
            return Err("capacity46 group census".into());
        }
        let terms=u_sum(&a.expected_terms_per_group)?;
        let f=std::mem::size_of::<Fr>();let word=std::mem::size_of::<usize>();
        let templates=u_sum(&[u_mul(terms,std::mem::size_of::<Term>())?,u_mul(groups,std::mem::size_of::<Option<Vec<Term>>>())?])?;
        let bank=u_sum(&[u_mul(terms,std::mem::size_of::<BooleanUPreweight>())?,u_mul(groups,std::mem::size_of::<(usize,usize)>())?,std::mem::size_of::<BooleanUPreweightBank>()])?;
        let local=1usize.checked_shl(rows as u32).ok_or("capacity46 arithmetic overflow")?;
        let row_live=u_sum(&[u_mul(u_sum(&[local.max(4),owners])?,f)?,u_mul(rows+1,std::mem::size_of::<Option<Vec<Fr>>>())?,std::mem::size_of::<Vec<Fr>>()])?;
        let copy_lookup=Self::lookup(copies)?;
        // Bounds cover r, local/high points, cloned/extended u and their growth.
        // U has bits+copies messages; old/new outer descriptors and one next
        // 3-field polynomial coexist. gkr::prove_phase adds one cloned high X.
        let rounds=u_mul(u_mul(u_sum(&[bits,copies,1])?,2)?,u_sum(&[2*std::mem::size_of::<Vec<Fr>>(),3*f])?)?;
        let points=u_mul(u_sum(&[u_mul(rows+copies,2)?,u_mul(bits+copies+1,6)?])?,f)?;
        let small=u_sum(&[u_mul(owners,2*word)?,u_mul(groups,4*word+4*f)?,rounds,points,
            std::mem::size_of::<BooleanUPreweightStats>(),std::mem::size_of::<GroupedVStats>(),
            std::mem::size_of::<OneFamilyRowFactor<'_>>(),std::mem::size_of::<TensorRowWeightLookup<'_>>(),
            16*std::mem::size_of::<Vec<Fr>>(),subset4_metadata_bytes().ok_or("capacity46 arithmetic overflow")?,Self::metadata()?])?;
        let loader=boolean_u_loader_scratch_bound(width).ok_or("capacity46 arithmetic overflow")?;
        let mut p=Self{bits,copies,rows,width,owners,groups,private:policy.extra_capacity_bytes(),templates,row_live,copy_lookup,bank,small,loader,u_max:0,v_max:0,component:0};
        for k in 0..=bits{for phase in [UPhase::Baseline,UPhase::RowBuild,UPhase::Prefix,UPhase::Bank,UPhase::Table,UPhase::HighReserve,UPhase::Load,UPhase::Apply,UPhase::Send,UPhase::High,UPhase::PostHigh]{
            p.u_max=p.u_max.max(p.bound(phase,k)?);}}
        p.v_max=grouped_v_prebind_capacity_bound_with_policy(bits,copies,rows,a,policy)
            .and_then(|n|n.checked_add(boolean_u_v_reservation(width)?))
            .and_then(|n|n.checked_add(subset4_metadata_bytes()?)).ok_or("capacity46 V arithmetic")?;
        p.component=p.u_max.max(p.v_max);
        if p.component>policy.component_limit_bytes(){return Err(policy.component_limit_error().into());}Ok(p)
    }
    fn table(&self,k:usize)->Result<usize,String>{if k>self.bits{return Err("capacity46 prefix".into());}
        let n=if k==0{0}else if k==1{4}else{u_mul(1usize.checked_shl(k as u32).ok_or("capacity46 arithmetic overflow")?,4)?};
        u_mul(n,std::mem::size_of::<Fr>())}
    fn bound(&self,phase:UPhase,k:usize)->Result<usize,String>{
        if k>self.bits{return Err("capacity46 prefix".into());}
        let f=std::mem::size_of::<Fr>();let prefix=u_mul(1usize<<k,f)?;
        let common=u_sum(&[self.templates,self.private,self.small])?;
        if phase==UPhase::Baseline{return u_sum(&[common,u_mul(self.width,f)?,self.loader]);}
        if phase==UPhase::RowBuild{return u_sum(&[common,TensorRowWeightLookup::MAX_LOCAL_TABLE_BYTES,
            TensorRowWeightLookup::MAX_SCALE_BYTES,64*1024,u_mul(self.copy_lookup,2)?,self.loader]);}
        let base=u_sum(&[common,self.row_live,self.copy_lookup,self.loader])?;
        let high=if k==self.bits{u_mul(3*self.owners,f)?}else{0};
        match phase{
            UPhase::Prefix=>u_sum(&[base,prefix,high]),
            UPhase::Bank=>u_sum(&[base,prefix,self.bank,high]),
            UPhase::Table|UPhase::HighReserve=>u_sum(&[base,prefix,self.bank,self.table(k)?,high]),
            UPhase::Load=>u_sum(&[base,prefix,self.bank,self.table(k)?,high,u_mul(self.width,f)?]),
            // Retain the declared loader allowance in the actual inventory;
            // its transient is already dead when A/B are created.
            UPhase::Apply=>u_sum(&[base,prefix,self.bank,self.table(k)?,high,u_mul(self.width,f)?,u_mul(2*(self.width>>k),f)?,3*f]),
            UPhase::Send=>u_sum(&[base,3*f]),
            UPhase::High|UPhase::PostHigh=>u_sum(&[base,u_mul(self.width,f)?,u_mul(4*self.owners+5*self.copies,f)?]),
            _=>Err("capacity46 phase".into()),
        }
    }
    fn state(&self,phase:UPhase,k:usize,s:ULive)->Result<(),String>{
        let empty=!s.bank&&!s.table&&!s.owner&&!s.coeff;
        let ok=match phase{
            UPhase::Prefix|UPhase::Send|UPhase::High|UPhase::PostHigh|UPhase::Baseline|UPhase::RowBuild=>s.prefix.is_none()&&empty,
            UPhase::Bank=>s.prefix==Some(k)&&empty,
            UPhase::Table=>s.prefix==Some(k)&&s.bank&&!s.table&&!s.owner&&!s.coeff,
            UPhase::HighReserve=>s.prefix==Some(k)&&s.bank&&s.table&&!s.owner&&!s.coeff,
            UPhase::Load=>s.prefix==Some(k)&&s.bank&&s.table&&!s.owner&&!s.coeff,
            UPhase::Apply=>s.prefix==Some(k)&&s.bank&&s.table&&s.owner&&!s.coeff,
        };
        if !ok{return Err("capacity46 forbidden live overlap".into());}Ok(())
    }
    fn before(&self,phase:UPhase,k:usize,s:ULive)->Result<usize,String>{self.state(phase,k,s)?;
        let bytes=self.bound(phase,k)?;if bytes>self.u_max||bytes>self.component{return Err("capacity46 phase exceeds reservation".into());}Ok(bytes)}
    fn actual(&self,phase:UPhase,k:usize,bytes:usize,private:usize,table:usize,high:usize)->Result<(),String>{
        if private!=self.private{return Err("capacity46 private reservation drift".into());}
        let expected_table=if matches!(phase,UPhase::Table|UPhase::HighReserve|UPhase::Load|UPhase::Apply){self.table(k)?}else{0};
        if table!=expected_table{return Err("capacity46 table capacity drift".into());}
        let expected_high=if k==self.bits&&matches!(phase,UPhase::HighReserve|UPhase::Load|UPhase::Apply){3*self.owners}else{0};
        if high!=expected_high{return Err("capacity46 high capacity drift".into());}
        if bytes>self.bound(phase,k)?||bytes>self.component{return Err("capacity46 actual capacity exceeds reservation".into());}Ok(())
    }
    fn lookup_actual(&self,row:&TensorRowWeightLookup<'_>,factor:Option<&OneFamilyRowFactor<'_>>)->Result<(),String>{
        if row.fallback.is_some()||row.member_row_bits!=[self.rows]||row.base_row_bits!=self.rows||row.copy_bits!=self.copies
            ||row.capacity_bytes().is_none_or(|n|n>self.row_live){return Err("capacity46 row lookup capacity or shape".into());}
        if row.local_table(self.rows).is_none_or(|v|v.len()!=1usize<<self.rows){return Err("capacity46 borrowed row missing".into());}
        if let Some(factor)=factor{
            let local=row.local_table(self.rows).ok_or("capacity46 borrowed row missing")?;
            if !matches!(&factor.local_weights,std::borrow::Cow::Borrowed(x) if std::ptr::eq(x.as_ptr(),local.as_ptr())&&x.len()==local.len())
                ||factor.copy_weights.capacity_bytes().is_none_or(|n|n>self.copy_lookup){return Err("capacity46 row factor capacity or ownership".into());}
        }Ok(())
    }
    fn baseline_actual(&self,templates:&Vec<Option<Vec<Term>>>,counts:&Vec<usize>,stats:&GroupedVStats)->Result<(),String>{
        if templates.capacity()!=self.groups||counts.capacity()!=self.owners
            ||stats.group_owner_counts.capacity()!=self.groups||stats.group_term_counts.capacity()!=self.groups
            ||grouped_template_capacity_bytes(templates)?>self.templates{
            return Err("capacity46 baseline capacity drift".into());
        }Ok(())
    }
    fn high_actual(&self,rounds:&Vec<Vec<Fr>>,points:&[&Vec<Fr>])->Result<(),String>{
        // Fixed outer reservation prevents send_round from growing it. Each
        // high-point Vec is bounded after the literal gkr::prove_phase call.
        if rounds.capacity()!=2*(self.bits+self.copies)||rounds.iter().any(|p|p.capacity()!=3)
            ||points.iter().any(|p|p.capacity()>2*(self.bits+self.copies+1)){
            return Err("capacity46 high round or point capacity drift".into());
        }Ok(())
    }
    fn handoff_weights_actual(&self,local:&Vec<Fr>,copy:&Vec<Fr>)->Result<(),String>{
        if copy.capacity()>self.owners.max(4)||local.capacity()!=self.width{
            return Err("capacity46 handoff weight capacity drift".into());
        }Ok(())
    }
}
fn subset4_metadata_bytes()->Option<usize>{
    // Include both the table/optional-table descriptors, separate stats and its
    // optional borrow, plus bounded build/apply scalar scratch (no heap scratch).
    std::mem::size_of::<BooleanSubset4Table>().checked_add(std::mem::size_of::<Option<BooleanSubset4Table>>())?
        .checked_add(std::mem::size_of::<BooleanSubset4Stats>())?
        .checked_add(std::mem::size_of::<Option<&mut BooleanSubset4Stats>>())?
        .checked_add(std::mem::size_of::<BooleanXFoldMode>())?
        .checked_add(4*std::mem::size_of::<&[Fr]>())?.checked_add(2*std::mem::size_of::<std::time::Instant>())?
        .checked_add(16*std::mem::size_of::<usize>())?.checked_add(8*std::mem::size_of::<Fr>())
}
fn subset4_extra_bound(input_bits:usize)->Option<usize>{
    let width=1usize.checked_shl(u32::try_from(input_bits).ok()?)?;
    width.checked_mul(4)?.checked_mul(std::mem::size_of::<Fr>())?.checked_add(subset4_metadata_bytes()?)
}
impl BooleanSubset4Table{
    fn build(prefix:&[Fr],weights:&[Fr],width:usize,stats:&mut BooleanSubset4Stats)->Result<Self,String>{
        if !width.is_power_of_two()||prefix.len()>width.trailing_zeros() as usize
            ||1usize.checked_shl(u32::try_from(prefix.len()).map_err(|_|"subset4 prefix dimensions")?)!=Some(weights.len()){
            return Err("subset4 prefix dimensions".into());
        }
        let k=prefix.len();let entries=if k==0{0}else if k==1{4}else{weights.len().checked_mul(4).ok_or("subset4 table arithmetic")?};
        let payload=entries.checked_mul(std::mem::size_of::<Fr>()).ok_or("subset4 table arithmetic")?;
        if payload.checked_add(subset4_metadata_bytes().ok_or("subset4 metadata arithmetic")?)
            .is_none_or(|n|n>stats.extra_reserved_bytes){return Err("subset4 table exceeds reservation".into());}
        let started=std::time::Instant::now();let mut values=Vec::new();
        values.try_reserve_exact(entries).map_err(|_|"subset4 table allocation")?;
        if values.capacity()!=entries{return Err("subset4 table capacity drift".into());}
        values.resize(entries,Fr::zero());
        if k==1{values[1]=weights[0];values[2]=weights[1];values[3]=Fr::one();}
        else if k>=2{for q in 0..weights.len()/4{for mask in 1usize..16{
            let bit=mask.trailing_zeros() as usize;let rest=mask&(mask-1);
            values[q*16+mask]=values[q*16+rest]+weights[q*4+bit];
        }}}
        stats.builds=stats.builds.checked_add(usize::from(k!=0)).ok_or("subset4 counter arithmetic")?;
        stats.values_built=stats.values_built.checked_add(entries).ok_or("subset4 counter arithmetic")?;
        let adds=if k>=2{(weights.len()/4).checked_mul(15).ok_or("subset4 counter arithmetic")?}else{0};
        stats.build_additions=stats.build_additions.checked_add(adds).ok_or("subset4 counter arithmetic")?;
        stats.table_payload_peak_bytes=stats.table_payload_peak_bytes.max(payload);
        stats.build_ns=stats.build_ns.checked_add(elapsed_nanos(started)).ok_or("subset4 timer arithmetic")?;
        Ok(Self{k,values})
    }
    fn apply(&self,input:&mut Vec<Fr>,stats:&mut BooleanSubset4Stats)->Result<(),String>{
        let started=std::time::Instant::now();
        let width=input.len();
        if !width.is_power_of_two()||input.capacity()!=width||self.k>width.trailing_zeros() as usize{
            return Err("subset4 input dimensions or capacity".into());
        }
        // This check is intentionally before EVERY is_one conversion, even
        // though the enclosing checked loader also validates the original X.
        if input.iter().any(|x|!x.is_zero()&&!x.is_one()){return Err("subset4 input is not Boolean".into());}
        let block=1usize.checked_shl(self.k as u32).ok_or("subset4 apply arithmetic")?;
        let expected=if self.k==0{0}else if self.k==1{4}else{block.checked_mul(4).ok_or("subset4 apply arithmetic")?};
        if self.values.len()!=expected{return Err("subset4 table extent".into());}
        let outputs=width>>self.k;
        if self.k==1{for j in 0..outputs{let mask=usize::from(input[2*j].is_one())|usize::from(input[2*j+1].is_one())<<1;
            input[j]=self.values[mask];}}
        else if self.k>=2{for j in 0..outputs{let mut sum=Fr::zero();for q in 0..block/4{
            let base=(j<<self.k)+4*q;let mut mask=0usize;
            for b in 0..4{mask|=usize::from(input[base+b].is_one())<<b;}
            if q==0{sum=self.values[q*16+mask];}else{sum+=self.values[q*16+mask];}
        }input[j]=sum;}}
        input.truncate(outputs);
        let lookups=if self.k==0{0}else if self.k==1{outputs}else{width/4};
        let adds=if self.k>=2{lookups-outputs}else{0};
        stats.apply_calls=stats.apply_calls.checked_add(1).ok_or("subset4 counter arithmetic")?;
        stats.lookups=stats.lookups.checked_add(lookups).ok_or("subset4 counter arithmetic")?;
        stats.apply_additions=stats.apply_additions.checked_add(adds).ok_or("subset4 counter arithmetic")?;
        stats.mask_bits=stats.mask_bits.checked_add(if self.k==0{0}else{width}).ok_or("subset4 counter arithmetic")?;
        stats.apply_ns=stats.apply_ns.checked_add(elapsed_nanos(started)).ok_or("subset4 timer arithmetic")?;Ok(())
    }
}
#[derive(Clone)]
struct BooleanUPreweight{bucket:usize,right:usize,values:[Fr;4]}
#[derive(Clone)]
struct BooleanUPreweightBank{entries:Vec<BooleanUPreweight>,ranges:Vec<(usize,usize)>}
impl BooleanUPreweightBank{
    fn capacity_bytes(&self)->Option<usize>{
        self.entries.capacity().checked_mul(std::mem::size_of::<BooleanUPreweight>())?
            .checked_add(self.ranges.capacity().checked_mul(std::mem::size_of::<(usize,usize)>())?)?
            .checked_add(std::mem::size_of::<Self>())
    }
    fn build(templates:&Vec<Option<Vec<Term>>>,prefix:&[Fr],prefix_weights:&[Fr],
        factor:&OneFamilyRowFactor<'_>,width:usize,stats:&mut BooleanUPreweightStats)->Result<Self,String>{
        if prefix.len()>width.trailing_zeros() as usize||prefix.len()>=usize::BITS as usize
            ||prefix_weights.len()!=(1usize<<prefix.len()){
            return Err("Boolean U preweight prefix dimensions".into());
        }
        let count=templates.iter().try_fold(0usize,|sum,terms|sum.checked_add(terms.as_ref()?.len()))
            .ok_or("Boolean U captured template count overflow")?;
        let mut bank=Self{entries:Vec::new(),ranges:Vec::new()};
        bank.entries.try_reserve_exact(count).map_err(|_|"Boolean U preweight reservation failed")?;
        bank.ranges.try_reserve_exact(templates.len()).map_err(|_|"Boolean U range reservation failed")?;
        // Exact reservations must not acquire unaccounted spare capacity.
        if bank.entries.capacity()!=count||bank.ranges.capacity()!=templates.len(){
            return Err("Boolean U preweight reservation capacity drift".into());
        }
        let mask=prefix_weights.len()-1;
        for terms in templates{
            let start=bank.entries.len();
            for term in terms.as_ref().ok_or("Boolean U captured template missing")?{
                let gate=&term.gate;
                if gate.left>=width||gate.right>=width||term.row>=factor.local_weights.len(){
                    return Err("Boolean U captured endpoint or row outside admission".into());
                }
                let w=prefix_weights[gate.left&mask]*factor.local(term.row);
                bank.entries.push(BooleanUPreweight{bucket:gate.left>>prefix.len(),right:gate.right,
                    values:[w*gate.c1,w*(gate.c1+gate.c3),w*gate.c0,w*(gate.c0+gate.c2)]});
            }
            bank.ranges.push((start,bank.entries.len()));
        }
        stats.prefix_builds=stats.prefix_builds.checked_add(1).ok_or("Boolean U build counter overflow")?;
        stats.shared_term_iterations=stats.shared_term_iterations.checked_add(count)
            .ok_or("Boolean U shared iteration counter overflow")?;
        stats.preweight_peak_capacity_bytes=stats.preweight_peak_capacity_bytes.max(
            bank.capacity_bytes().ok_or("Boolean U bank capacity overflow")?);
        Ok(bank)
    }
    fn coefficients(&self,group:usize,input:&[Fr],folded_width:usize,
        stats:&mut BooleanUPreweightStats)->Result<(Vec<Fr>,Vec<Fr>),String>{
        let &(start,end)=self.ranges.get(group).ok_or("Boolean U owner group outside admission")?;
        let mut a=Vec::new();let mut b=Vec::new();
        a.try_reserve_exact(folded_width).map_err(|_|"Boolean U A reservation failed")?;
        b.try_reserve_exact(folded_width).map_err(|_|"Boolean U B reservation failed")?;
        if a.capacity()!=folded_width||b.capacity()!=folded_width{
            return Err("Boolean U coefficient reservation capacity drift".into());
        }
        a.resize(folded_width,Fr::zero());b.resize(folded_width,Fr::zero());
        for entry in &self.entries[start..end]{
            if entry.bucket>=folded_width||entry.right>=input.len(){return Err("Boolean U selector bounds".into());}
            // Every full input load was checked by the opt-in wrapper. X is
            // still original here; only the later polynomial input is folded.
            let selected=usize::from(input[entry.right].is_one());
            a[entry.bucket]+=entry.values[selected];b[entry.bucket]+=entry.values[2+selected];
        }
        stats.owner_term_selections=stats.owner_term_selections.checked_add(end-start)
            .ok_or("Boolean U selection counter overflow")?;
        Ok((a,b))
    }

    /// Fuse first-U selected-entry accumulation directly into the three
    /// quadratic-message coefficients. This is deliberately k=0: each bank
    /// bucket is the original left wire p, and the complete original X is
    /// still loaded and checked before this helper is called.
    #[cfg(test)]
    fn fused_u0_message(&self,group:usize,input:&[Fr])->Result<[Fr;3],String>{
        if input.iter().any(|value|!value.is_zero()&&!value.is_one()){
            return Err("Boolean U fused U0 input is not Boolean".into());
        }
        self.fused_u0_message_from_checked_boolean_input(group,input)
    }

    /// The caller must have just checked every value in the complete original
    /// X vector. Keeping that O(width) check outside this routine makes the
    /// fused timing comparable to C323's select/message interval.
    #[cfg(test)]
    fn fused_u0_message_from_checked_boolean_input(&self,group:usize,input:&[Fr])->Result<[Fr;3],String>{
        let &(start,end)=self.ranges.get(group).ok_or("Boolean U owner group outside admission")?;
        let width=input.len();
        if width==0||!width.is_power_of_two(){
            return Err("Boolean U fused U0 input dimensions".into());
        }
        let mut message=[Fr::zero();3];
        for entry in &self.entries[start..end]{
            let p=entry.bucket;
            if p>=width||entry.right>=width{return Err("Boolean U fused U0 selector bounds".into());}
            let selected=usize::from(input[entry.right].is_one());
            let alpha=entry.values[selected];
            let beta=entry.values[2+selected];
            if p&1==0{
                if p+1>=width{return Err("Boolean U fused U0 pair bounds".into());}
                let x0=input[p];let dx=input[p+1]-x0;
                message[0]+=alpha*x0+beta;
                message[1]+=alpha*(input[p+1]-Fr::from(2u64)*x0)-beta;
                message[2]-=alpha*dx;
            }else{
                let x0=input[p-1];
                // For an odd p, A[p] and B[p] have no constant-message
                // contribution. In particular, a B-only odd entry yields
                // [0, beta, 0], which is independently falsified below.
                message[1]+=alpha*x0+beta;
                message[2]+=alpha*(input[p]-x0);
            }
        }
        Ok(message)
    }

    /// Fuse a nonterminal-prefix U message. The right selector is read from
    /// the original, fully checked Boolean X, while pair values come from X
    /// after folding the first `prefix_len` coordinates.
    #[cfg(test)]
    fn fused_prefix_message_from_checked_boolean_input(&self,group:usize,original_x:&[Fr],
        folded_x:&[Fr],prefix_len:usize)->Result<[Fr;3],String>{
        if original_x.is_empty()||!original_x.len().is_power_of_two()
            ||prefix_len>=original_x.len().trailing_zeros() as usize
            ||prefix_len>=usize::BITS as usize
            ||folded_x.len()!=(original_x.len()>>prefix_len){
            return Err("Boolean U fused prefix dimensions".into());
        }
        let &(start,end)=self.ranges.get(group).ok_or("Boolean U owner group outside admission")?;
        let mut message=[Fr::zero();3];
        for entry in &self.entries[start..end]{
            let p=entry.bucket;
            if p>=folded_x.len()||entry.right>=original_x.len(){
                return Err("Boolean U fused prefix selector bounds".into());
            }
            let selected=usize::from(original_x[entry.right].is_one());
            let alpha=entry.values[selected];
            let beta=entry.values[2+selected];
            if p&1==0{
                if p+1>=folded_x.len(){return Err("Boolean U fused prefix pair bounds".into());}
                let x0=folded_x[p];let dx=folded_x[p+1]-x0;
                message[0]+=alpha*x0+beta;
                message[1]+=alpha*(folded_x[p+1]-Fr::from(2u64)*x0)-beta;
                message[2]-=alpha*dx;
            }else{
                let x0=folded_x[p-1];
                message[1]+=alpha*x0+beta;
                message[2]+=alpha*(folded_x[p]-x0);
            }
        }
        Ok(message)
    }

    /// Test-only producer path for k=1. Folded pair values are evaluated on
    /// demand from the checked original X and the real round-0 challenge, so
    /// this differential adds no input-sized allocation or capacity phase.
    fn fused_u1_message_from_checked_boolean_input(&self,group:usize,original_x:&[Fr],
        challenge:Fr)->Result<[Fr;3],String>{
        if original_x.len()<4||!original_x.len().is_power_of_two(){
            return Err("Boolean U fused U1 input dimensions".into());
        }
        let &(start,end)=self.ranges.get(group).ok_or("Boolean U owner group outside admission")?;
        let mut message=[Fr::zero();3];
        for entry in &self.entries[start..end]{
            let p=entry.bucket;
            if p>=original_x.len()/2||entry.right>=original_x.len(){
                return Err("Boolean U fused U1 selector bounds".into());
            }
            let selected=usize::from(original_x[entry.right].is_one());
            let alpha=entry.values[selected];
            let beta=entry.values[2+selected];
            let pair_value=|index:usize|{
                let x0=original_x[index*2];
                x0+challenge*(original_x[index*2+1]-x0)
            };
            if p&1==0{
                if p+1>=original_x.len()/2{return Err("Boolean U fused U1 pair bounds".into());}
                let x0=pair_value(p);let x1=pair_value(p+1);
                message[0]+=alpha*x0+beta;
                message[1]+=alpha*(x1-Fr::from(2u64)*x0)-beta;
                message[2]-=alpha*(x1-x0);
            }else{
                let x0=pair_value(p-1);let x1=pair_value(p);
                message[1]+=alpha*x0+beta;
                message[2]+=alpha*(x1-x0);
            }
        }
        Ok(message)
    }

}

/// Test-only entrypoint for cross-fixture prefix-U differentials. `local_row_weights`
/// supplies the row equality weight; the consumer applies any owner/copy scale
/// after this local message, matching the existing U handoff convention.
#[cfg(test)]
pub(crate) fn c325_fused_prefix_u_message_for_test(terms:&[Term],prefix:&[Fr],
    local_row_weights:&[Fr],original_x:&[Fr],folded_x:&[Fr])->Result<[Fr;3],String>{
    if original_x.is_empty()||!original_x.len().is_power_of_two()
        ||prefix.len()>=original_x.len().trailing_zeros() as usize
        ||prefix.len()>=usize::BITS as usize
        ||folded_x.len()!=(original_x.len()>>prefix.len())
        ||local_row_weights.is_empty()||!local_row_weights.len().is_power_of_two(){
        return Err("Boolean U fused prefix API dimensions".into());
    }
    if original_x.iter().any(|value|!value.is_zero()&&!value.is_one()){
        return Err("Boolean U fused prefix input is not Boolean".into());
    }
    let templates=vec![Some(terms.to_vec())];
    let factor=OneFamilyRowFactor{local_weights:std::borrow::Cow::Borrowed(local_row_weights),
        copy_weights:EqWeightLookup::new(&[])};
    let mut stats=BooleanUPreweightStats::default();
    let weights=gkr::eq_weights(prefix);
    let bank=BooleanUPreweightBank::build(&templates,prefix,&weights,&factor,original_x.len(),&mut stats)?;
    bank.fused_prefix_message_from_checked_boolean_input(0,original_x,folded_x,prefix.len())
}

#[cfg(test)]
mod c325_prefix_u_message_tests{
    use super::*;

    #[test]
    fn c325_prefix_u_message_uses_original_selector_and_folded_pair(){
        let terms=[Term{row:0,gate:crate::gkr::Gate{left:0,right:1,c0:Fr::zero(),
            c1:-Fr::one(),c2:Fr::zero(),c3:-Fr::from(2u64)}}];
        let original_x=[Fr::zero(),Fr::one(),Fr::zero(),Fr::one()];
        let folded_x=[Fr::from(2u64),Fr::from(2u64)];
        let message=c325_fused_prefix_u_message_for_test(&terms,&[Fr::from(2u64)],&[Fr::one()],
            &original_x,&folded_x).unwrap();
        assert_eq!(message,[Fr::from(6u64),-Fr::from(6u64),Fr::zero()]);

        let weights=gkr::eq_weights(&[Fr::from(2u64)]);
        let selected=usize::from(original_x[terms[0].gate.right].is_one());
        let dense_a=[weights[0]*[terms[0].gate.c1,terms[0].gate.c1+terms[0].gate.c3][selected],Fr::zero()];
        let dense_b=[weights[0]*[terms[0].gate.c0,terms[0].gate.c0+terms[0].gate.c2][selected],Fr::zero()];
        let mut dense_x=original_x.to_vec();gkr::fold(&mut dense_x,Fr::from(2u64));
        assert_eq!(dense_x.as_slice(),folded_x.as_slice(),"supplied folded X follows the existing LSB fold");
        let direct:[Fr;3]=gkr::quadratic_message(&dense_a,&dense_b,&dense_x).try_into().unwrap();
        assert_eq!(message,direct,"fused prefix message matches the direct dense message");

        let folded_selector=usize::from(folded_x[terms[0].gate.right].is_one());
        let wrong_alpha=weights[0]*[terms[0].gate.c1,terms[0].gate.c1+terms[0].gate.c3][folded_selector];
        assert_eq!([wrong_alpha*folded_x[0],
            wrong_alpha*(folded_x[1]-Fr::from(2u64)*folded_x[0]),Fr::zero()],
            [Fr::from(2u64),-Fr::from(2u64),Fr::zero()],"folded-selector mutant");
        assert_ne!(message,[Fr::from(2u64),-Fr::from(2u64),Fr::zero()]);

        let nonboolean=[Fr::zero(),Fr::from(2u64),Fr::zero(),Fr::one()];
        assert_eq!(c325_fused_prefix_u_message_for_test(&terms,&[Fr::from(2u64)],&[Fr::one()],
            &nonboolean,&folded_x).unwrap_err(),"Boolean U fused prefix input is not Boolean");
        assert_eq!(c325_fused_prefix_u_message_for_test(&terms,&[Fr::from(2u64)],&[Fr::one()],
            &original_x,&folded_x[..1]).unwrap_err(),"Boolean U fused prefix API dimensions");
        assert_eq!(c325_fused_prefix_u_message_for_test(&terms,&[Fr::from(2u64),Fr::one()],&[Fr::one()],
            &original_x,&folded_x[..1]).unwrap_err(),"Boolean U fused prefix API dimensions");
        assert_eq!(c325_fused_prefix_u_message_for_test(&terms,&[Fr::from(2u64)],
            &[Fr::one(),Fr::one(),Fr::one()],&original_x,&folded_x).unwrap_err(),
            "Boolean U fused prefix API dimensions");
        let bad_row=Term{row:1,gate:terms[0].gate.clone()};
        assert_eq!(c325_fused_prefix_u_message_for_test(&[bad_row],&[Fr::from(2u64)],
            &[Fr::one()],&original_x,&folded_x).unwrap_err(),
            "Boolean U captured endpoint or row outside admission");
    }
}

#[cfg(test)]
mod c326_two_round_prefix_u_transcript_tests{
    use super::*;

    #[test]
    fn c326_width4_two_round_prefix_u_transcript_composes(){
        let gate=crate::gkr::Gate{left:0,right:1,c0:Fr::from(5u64),c1:Fr::from(2u64),
            c2:Fr::from(7u64),c3:Fr::from(3u64)};
        let terms=vec![
            Term{row:0,gate:gate.clone()},
            Term{row:0,gate:crate::gkr::Gate{left:1,..gate}},
        ];
        let templates=vec![Some(terms)];
        let factor=OneFamilyRowFactor{local_weights:std::borrow::Cow::Owned(vec![Fr::one()]),
            copy_weights:EqWeightLookup::new(&[])};
        let original_x=vec![Fr::zero(),Fr::one(),Fr::zero(),Fr::zero()];
        let mut stats=BooleanUPreweightStats::default();
        let k0=BooleanUPreweightBank::build(&templates,&[],&[Fr::one()],&factor,4,&mut stats).unwrap();
        let (mut dense_a,mut dense_b)=k0.coefficients(0,&original_x,4,&mut stats).unwrap();
        let round0_message=gkr::quadratic_message(&dense_a,&dense_b,&original_x);
        let mut claim=(0..4).fold(Fr::zero(),|sum,index|sum+dense_a[index]*original_x[index]+dense_b[index]);
        let mut transcript=Transcript::new(b"c326-two-round-prefix-u");
        let mut rounds=Vec::new();
        let challenge0=send_round(round0_message,&mut claim,&mut rounds,&mut transcript).unwrap();
        assert_eq!(rounds.len(),1);

        gkr::fold(&mut dense_a,challenge0);
        gkr::fold(&mut dense_b,challenge0);
        let mut folded_x=original_x.clone();
        gkr::fold(&mut folded_x,challenge0);
        assert_eq!(original_x[1],Fr::one());
        assert_eq!(folded_x[1],Fr::zero(),"right selector differs for the actual round-0 challenge");

        let prefix=[challenge0];
        let prefix_weights=gkr::eq_weights(&prefix);
        let k1=BooleanUPreweightBank::build(&templates,&prefix,&prefix_weights,&factor,4,&mut stats).unwrap();
        let (bank_a,bank_b)=k1.coefficients(0,&original_x,2,&mut stats).unwrap();
        assert_eq!(bank_a,dense_a,"k=1 A coefficients equal folding dense k=0 A");
        assert_eq!(bank_b,dense_b,"k=1 B coefficients equal folding dense k=0 B");

        let dense1:[Fr;3]=gkr::quadratic_message(&dense_a,&dense_b,&folded_x).try_into().unwrap();
        let fused1=k1.fused_prefix_message_from_checked_boolean_input(0,&original_x,&folded_x,1).unwrap();
        assert_eq!(fused1,dense1,"fused prefix message uses original selector and folded X pair");
        let (wrong_a,wrong_b)=k1.coefficients(0,&folded_x,2,&mut stats).unwrap();
        let wrong_selector:[Fr;3]=gkr::quadratic_message(&wrong_a,&wrong_b,&folded_x).try_into().unwrap();
        assert_ne!(wrong_selector,dense1,"folded-selector mutant is discriminated without a fixed challenge");

        let claim_after_round0=claim;
        let mut dense_transcript=transcript.clone();
        let mut fused_transcript=transcript.clone();
        let mut dense_claim=claim_after_round0;
        let mut fused_claim=claim_after_round0;
        let mut dense_rounds=rounds.clone();
        let mut fused_rounds=rounds;
        let challenge1=send_round(dense1.to_vec(),&mut dense_claim,&mut dense_rounds,&mut dense_transcript).unwrap();
        let fused_challenge1=send_round(fused1.to_vec(),&mut fused_claim,&mut fused_rounds,&mut fused_transcript).unwrap();
        assert_eq!(dense1,fused1);
        assert_eq!(challenge1,fused_challenge1);
        assert_eq!(dense_claim,fused_claim);
        assert_eq!(dense_rounds,fused_rounds);

        let (mut dense_final_a,mut dense_final_b)=(dense_a.clone(),dense_b.clone());
        let (mut fused_final_a,mut fused_final_b)=(bank_a,bank_b);
        let (mut dense_final_x,mut fused_final_x)=(folded_x.clone(),folded_x);
        for values in [&mut dense_final_a,&mut dense_final_b,&mut dense_final_x,
            &mut fused_final_a,&mut fused_final_b,&mut fused_final_x]{
            gkr::fold(values,challenge1);
        }
        assert_eq!(dense_final_a,fused_final_a);
        assert_eq!(dense_final_b,fused_final_b);
        assert_eq!(dense_final_x,fused_final_x);

        let dense_sentinel=dense_transcript.challenge_scalar(b"c326-transcript-sentinel");
        let fused_sentinel=fused_transcript.challenge_scalar(b"c326-transcript-sentinel");
        assert_eq!(dense_sentinel,fused_sentinel,"transcript state agrees after both rounds");
        assert_eq!(dense_transcript.challenges(),fused_transcript.challenges());
        assert_eq!(dense_transcript.raw_queries(),fused_transcript.raw_queries());
        assert_eq!(dense_transcript.bytes_absorbed(),fused_transcript.bytes_absorbed());
    }
}

/// C322 test-only differential for the first U message over four admitted
/// Carry owners. The caller pins and compares the complete ordered templates
/// before entering this helper.
#[cfg(test)]
pub(crate) fn c322_u0_literal_template_differential(
    templates:&[Vec<Term>;4],owners:[usize;4],point:&[Fr],owner_factors:&[Fr;4],
    mut load_input:impl FnMut(usize)->Result<Vec<Fr>,String>,
    mut visit_literal:impl FnMut(usize,&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String>,
)->Result<(usize,usize,usize,usize,[usize;5]),String>{
    const WIDTH:usize=1<<20;
    if point.len()!=40{return Err("C322 point dimensions".into());}
    if templates.iter().any(|template|template!=&templates[0]){
        return Err("C322 Carry templates differ before U message".into());
    }
    let factor=OneFamilyRowFactor::try_new(point,21,19,0,&[19],None)
        .ok_or("C322 one-family row factor shape")?;
    // One common template is built once; each owner reuses bank group zero.
    let captured=vec![Some(templates[0].clone())];
    let mut stats=BooleanUPreweightStats::default();
    let bank=BooleanUPreweightBank::build(&captured,&[],&[Fr::one()],&factor,WIDTH,&mut stats)?;
    let mut aggregate_direct=[Fr::zero();3];
    let mut aggregate_shared=[Fr::zero();3];
    let mut direct_visits=0usize;
    let mut owner_messages=[[Fr::zero();3];4];
    let mut selector_states=[0usize;5];
    let mut mutation_capacity=0usize;
    for index in 0..4{
        let owner=owners[index];
        if factor.copy(owner)!=owner_factors[index]{
            return Err(format!("C322 owner {owner} OneFamilyRowFactor differs from independent 21-bit product"));
        }
        let input=load_input(index)?;
        if input.len()!=WIDTH{return Err(format!("C322 owner {owner} input width"));}
        if input.iter().any(|value|!value.is_zero()&&!value.is_one()){
            return Err(format!("C322 owner {owner} expanded X is nonboolean"));
        }
        let (direct_a,direct_b)=direct_u_prefix_coefficients(
            WIDTH,&[],&[Fr::one()],owner,&input,|_,row|factor.local(row),
            |sink|visit_literal(index,&mut |term|{
                direct_visits=direct_visits.checked_add(1).ok_or("C322 direct visit counter overflow")?;
                sink(term)
            }),
        )?;
        let (shared_a,shared_b)=bank.coefficients(0,&input,WIDTH,&mut stats)?;
        if direct_a!=shared_a||direct_b!=shared_b{
            return Err(format!("C322 owner {owner} k=0 A/B coefficient mismatch"));
        }
        let direct_message:[Fr;3]=gkr::quadratic_message(&direct_a,&direct_b,&input)
            .try_into().map_err(|_|"C322 direct message width")?;
        let shared_message:[Fr;3]=gkr::quadratic_message(&shared_a,&shared_b,&input)
            .try_into().map_err(|_|"C322 shared message width")?;
        let scale=factor.copy(owner);
        let direct_message=direct_message.map(|value|value*scale);
        let shared_message=shared_message.map(|value|value*scale);
        if direct_message!=shared_message{
            return Err(format!("C322 owner {owner} k=0 U-message mismatch"));
        }
        owner_messages[index]=direct_message;
        for coefficient in 0..3{
            aggregate_direct[coefficient]+=direct_message[coefficient];
            aggregate_shared[coefficient]+=shared_message[coefficient];
        }
        for term in &templates[index]{
            let selected=input[term.gate.right];
            if selected.is_zero(){selector_states[0]+=1;}else{selector_states[1]+=1;}
            if !term.gate.c2.is_zero(){selector_states[2]+=1;}
            if !term.gate.c3.is_zero(){selector_states[3]+=1;}
            if term.gate.right!=0{selector_states[4]+=1;}
        }
        if index==0{
            let selector_index=templates[0].iter().enumerate().find_map(|(term_index,term)|{
                let right=term.gate.right;
                (right<WIDTH&&input[right]!=input[right^1]
                    &&(!term.gate.c2.is_zero()||!term.gate.c3.is_zero())).then_some(term_index)
            }).ok_or("C322 no flipped selector-bit case in admitted terms/X")?;
            let mut selector_bank=bank.clone();
            let (start,end)=selector_bank.ranges[0];
            if start==end{return Err("C322 selector control needs a term".into());}
            selector_bank.entries[start+selector_index].right^=1;
            let mut control_stats=BooleanUPreweightStats::default();
            mutation_capacity=mutation_capacity.max(selector_bank.capacity_bytes().ok_or("C322 selector bank capacity overflow")?);
            let selector_coefficients=selector_bank.coefficients(0,&input,WIDTH,&mut control_stats)?;
            let selector_message:[Fr;3]=gkr::quadratic_message(&selector_coefficients.0,&selector_coefficients.1,&input)
                .try_into().map_err(|_|"C322 selector control message width")?;
            if selector_message.map(|value|value*scale)==direct_message{
                return Err("C322 flipped-selector control was not discriminating".into());
            }
            drop(selector_bank);
            let mut row_bank=bank.clone();
            let row_index=templates[0].iter().position(|term|{
                let active=[term.gate.c0,term.gate.c1,term.gate.c2,term.gate.c3]
                    .iter().any(|coefficient|!coefficient.is_zero());
                active&&factor.local(term.row)!=factor.local(term.row^1)
            }).ok_or("C322 no active row term with a differing row-index-bit weight")?;
            let term=&templates[0][row_index];
            let row=term.row^1;
            let w=factor.local(row);
            let gate=&term.gate;
            row_bank.entries[start+row_index].values=[w*gate.c1,w*(gate.c1+gate.c3),w*gate.c0,w*(gate.c0+gate.c2)];
            let mut control_stats=BooleanUPreweightStats::default();
            mutation_capacity=mutation_capacity.max(row_bank.capacity_bytes().ok_or("C322 row bank capacity overflow")?);
            let row_coefficients=row_bank.coefficients(0,&input,WIDTH,&mut control_stats)?;
            let row_message:[Fr;3]=gkr::quadratic_message(&row_coefficients.0,&row_coefficients.1,&input)
                .try_into().map_err(|_|"C322 row control message width")?;
            if row_message.map(|value|value*scale)==direct_message{
                return Err("C322 row-index-bit control was not discriminating".into());
            }
        }
    }
    if aggregate_direct!=aggregate_shared{return Err("C322 aggregate k=0 U-message mismatch".into());}

    // Independent single-fault controls must each change a concrete message.
    let wrong_scale=factor.copy(owners[0]^1);
    if wrong_scale==factor.copy(owners[0])
        ||owner_messages[0].map(|value|value*wrong_scale/factor.copy(owners[0]))==owner_messages[0]{
        return Err("C322 wrong-owner-factor control was not discriminating".into());
    }
    if selector_states[0]==0||selector_states[1]==0||selector_states[2]==0
        ||selector_states[3]==0||selector_states[4]==0{
        return Err(format!("C322 selector/right/coefficient coverage missing: {selector_states:?}"));
    }
    let capacity=bank.capacity_bytes().ok_or("C322 bank capacity overflow")?.max(mutation_capacity);
    let bank_visits=stats.shared_term_iterations;
    let selection_visits=stats.owner_term_selections;
    if bank_visits!=templates[0].len()
        ||direct_visits!=templates[0].len().checked_mul(4).ok_or("C322 expected visits overflow")?
        ||selection_visits!=direct_visits{
        return Err("C322 operation-site visit counts disagree".into());
    }
    Ok((direct_visits,bank_visits,selection_visits,capacity,selector_states))
}

/// Raw order-balanced C350 samples for exactly two native Carry rows.
#[cfg(test)]
pub(crate) struct C350U0Samples {
    pub(crate) factor_build_ns:u128,
    pub(crate) factor_build_cpu_ns:u128,
    pub(crate) bank_build_ns:u128,
    pub(crate) bank_build_cpu_ns:u128,
    pub(crate) source_literal_ns:[[u128;2];3],
    pub(crate) source_literal_cpu_ns:[[u128;2];3],
    pub(crate) cached_literal_ns:[[u128;2];3],
    pub(crate) cached_literal_cpu_ns:[[u128;2];3],
    pub(crate) shared_ns:[[u128;2];3],
    pub(crate) shared_cpu_ns:[[u128;2];3],
    pub(crate) messages:[[[[Fr;3];2];3];3],
    pub(crate) source_literal_visits:usize,
    pub(crate) cached_literal_visits:usize,
    pub(crate) shared_build_visits:usize,
    pub(crate) shared_selection_visits:usize,
    pub(crate) bank_capacity_bytes:usize,
}

#[cfg(test)]
#[repr(C)]
#[derive(Clone,Copy,Default)]
struct C350FileTime { low:u32, high:u32 }

#[cfg(test)]
#[link(name="kernel32")]
extern "system" {
    fn GetCurrentProcess()->*mut std::ffi::c_void;
    fn GetProcessTimes(process:*mut std::ffi::c_void,creation:*mut C350FileTime,
        exit:*mut C350FileTime,kernel:*mut C350FileTime,user:*mut C350FileTime)->i32;
}

#[cfg(test)]
fn c350_process_cpu_100ns()->Result<u64,String>{
    let(mut creation,mut exit,mut kernel,mut user)=(C350FileTime::default(),C350FileTime::default(),
        C350FileTime::default(),C350FileTime::default());
    let ok=unsafe{GetProcessTimes(GetCurrentProcess(),&mut creation,&mut exit,&mut kernel,&mut user)};
    if ok==0{return Err("C350 GetProcessTimes failed".into());}
    let ticks=|time:C350FileTime|((time.high as u64)<<32)|time.low as u64;
    ticks(kernel).checked_add(ticks(user)).ok_or_else(||"C350 process CPU counter overflow".into())
}

#[cfg(test)]
fn c350_cpu_delta_ns(before:u64)->Result<u128,String>{
    (c350_process_cpu_100ns()?.checked_sub(before).ok_or("C350 process CPU counter regressed")? as u128)
        .checked_mul(100).ok_or_else(||"C350 process CPU nanosecond overflow".into())
}

#[cfg(test)]
fn c350_literal_u0_message(
    owner:usize,input:&[Fr],factor:&OneFamilyRowFactor<'_>,
    visit:impl FnMut(&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String>,
)->Result<[Fr;3],String>{
    const WIDTH:usize=1<<20;
    let (a,b)=direct_u_prefix_coefficients(WIDTH,&[],&[Fr::one()],owner,input,
        |_,row|factor.local(row),visit)?;
    let message:[Fr;3]=gkr::quadratic_message(&a,&b,input)
        .try_into().map_err(|_|"C350 literal message width")?;
    Ok(message.map(|value|value*factor.copy(owner)))
}

#[cfg(test)]
fn c350_shared_u0_message(
    owner:usize,input:&[Fr],factor:&OneFamilyRowFactor<'_>,bank:&BooleanUPreweightBank,
    stats:&mut BooleanUPreweightStats,
)->Result<[Fr;3],String>{
    const WIDTH:usize=1<<20;
    let (a,b)=bank.coefficients(0,input,WIDTH,stats)?;
    let message:[Fr;3]=gkr::quadratic_message(&a,&b,input)
        .try_into().map_err(|_|"C350 shared message width")?;
    Ok(message.map(|value|value*factor.copy(owner)))
}

#[cfg(test)]
fn c351_literal_u1_message(
    owner:usize,input:&[Fr],folded_input:&[Fr],factor:&OneFamilyRowFactor<'_>,
    prefix:&[Fr],prefix_weights:&[Fr],
    visit:impl FnMut(&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String>,
)->Result<[Fr;3],String>{
    const WIDTH:usize=1<<20;
    let (a,b)=direct_u_prefix_coefficients(WIDTH,prefix,prefix_weights,owner,input,
        |_,row|factor.local(row),visit)?;
    let message:[Fr;3]=gkr::quadratic_message(&a,&b,folded_input)
        .try_into().map_err(|_|"C351 literal message width")?;
    Ok(message.map(|value|value*factor.copy(owner)))
}

#[cfg(test)]
fn c351_shared_u1_message(
    owner:usize,input:&[Fr],folded_input:&[Fr],factor:&OneFamilyRowFactor<'_>,bank:&BooleanUPreweightBank,
    stats:&mut BooleanUPreweightStats,
)->Result<[Fr;3],String>{
    const WIDTH:usize=1<<20;
    let (a,b)=bank.coefficients(0,input,WIDTH>>1,stats)?;
    let message:[Fr;3]=gkr::quadratic_message(&a,&b,folded_input)
        .try_into().map_err(|_|"C351 shared message width")?;
    Ok(message.map(|value|value*factor.copy(owner)))
}

#[cfg(test)]
pub(crate) struct C351U1Samples{
    pub(crate) bank_build_ns:u128,pub(crate) bank_build_cpu_ns:u128,
    pub(crate) folded_x_ns:[[u128;2];3],pub(crate) folded_x_cpu_ns:[[u128;2];3],
    pub(crate) source_ns:[[u128;2];3],pub(crate) source_cpu_ns:[[u128;2];3],
    pub(crate) cached_ns:[[u128;2];3],pub(crate) cached_cpu_ns:[[u128;2];3],
    pub(crate) shared_ns:[[u128;2];3],pub(crate) shared_cpu_ns:[[u128;2];3],
    pub(crate) messages:[[[[Fr;3];2];3];3],
    pub(crate) bank_capacity_bytes:usize,pub(crate) source_term_visits:usize,
    pub(crate) cached_term_visits:usize,pub(crate) bank_term_visits:usize,
    pub(crate) selection_visits:usize,
}

/// First nonempty Boolean prefix, retaining original X for selectors and
/// folding X only for the quadratic message.
#[cfg(test)]
pub(crate) fn c351_u1_literal_template_pairs(
    template:&[Term],owners:&[usize],point:&[Fr],owner_factors:&[Fr],prefix_point:Fr,
    mut load_input:impl FnMut(usize)->Result<Vec<Fr>,String>,
    mut visit_literal:impl FnMut(usize,&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String>,
)->Result<C351U1Samples,String>{
    const WIDTH:usize=1<<20;
    if owners.len()!=2||owner_factors.len()!=2||template.len()!=396_561||point.len()!=40{
        return Err("C351 U1 two-owner geometry".into());
    }
    let factor=OneFamilyRowFactor::try_new(point,21,19,0,&[19],None)
        .ok_or("C351 one-family row factor shape")?;
    for index in 0..2{
        if factor.copy(owners[index])!=owner_factors[index]{
            return Err(format!("C351 owner {} independent factor mismatch",owners[index]));
        }
    }
    let prefix=[prefix_point];
    let prefix_weights=[Fr::one()-prefix_point,prefix_point];
    let bank_cpu_before=c350_process_cpu_100ns()?;
    let bank_started=std::time::Instant::now();
    let captured=vec![Some(template.to_vec())];
    let mut stats=BooleanUPreweightStats::default();
    let bank=BooleanUPreweightBank::build(&captured,&prefix,&prefix_weights,&factor,WIDTH,&mut stats)?;
    let bank_build_ns=bank_started.elapsed().as_nanos();
    let bank_build_cpu_ns=c350_cpu_delta_ns(bank_cpu_before)?;
    let mut source_ns=[[0u128;2];3];let mut source_cpu_ns=[[0u128;2];3];
    let mut cached_ns=[[0u128;2];3];let mut cached_cpu_ns=[[0u128;2];3];
    let mut shared_ns=[[0u128;2];3];let mut shared_cpu_ns=[[0u128;2];3];
    let mut folded_x_ns=[[0u128;2];3];let mut folded_x_cpu_ns=[[0u128;2];3];
    let mut messages=[[[[Fr::zero();3];2];3];3];
    let mut source_term_visits=0usize;let mut cached_term_visits=0usize;
    for round in 0..3{
        for index in 0..2{
            let input=load_input(index)?;
            if input.len()!=WIDTH||input.iter().any(|v|!v.is_zero()&&!v.is_one()){
                return Err(format!("C351 owner {} X width/Boolean",owners[index]));
            }
            let fold_cpu=c350_process_cpu_100ns()?;let fold_started=std::time::Instant::now();
            let folded_input=(0..WIDTH/2).map(|i|
                (Fr::one()-prefix_point)*input[2*i]+prefix_point*input[2*i+1]
            ).collect::<Vec<_>>();
            folded_x_ns[round][index]=fold_started.elapsed().as_nanos();
            folded_x_cpu_ns[round][index]=c350_cpu_delta_ns(fold_cpu)?;
            let mut outputs=[None;3];
            for turn in 0..3{
                match (turn+round)%3{
                    0=>{let c=c350_process_cpu_100ns()?;let t=std::time::Instant::now();
                        outputs[0]=Some(c351_literal_u1_message(owners[index],&input,&folded_input,&factor,&prefix,&prefix_weights,
                            |sink|visit_literal(index,&mut |term|{
                                source_term_visits=source_term_visits.checked_add(1).ok_or("C351 source visit overflow")?;
                                sink(term)
                            }))?);
                        source_ns[round][index]=t.elapsed().as_nanos();source_cpu_ns[round][index]=c350_cpu_delta_ns(c)?;}
                    1=>{let c=c350_process_cpu_100ns()?;let t=std::time::Instant::now();
                        outputs[1]=Some(c351_literal_u1_message(owners[index],&input,&folded_input,&factor,&prefix,&prefix_weights,|sink|{
                            for term in template.iter().cloned(){
                                cached_term_visits=cached_term_visits.checked_add(1).ok_or("C351 cached visit overflow")?;
                                sink(term)?;
                            }Ok(())
                        })?);
                        cached_ns[round][index]=t.elapsed().as_nanos();cached_cpu_ns[round][index]=c350_cpu_delta_ns(c)?;}
                    2=>{let c=c350_process_cpu_100ns()?;let t=std::time::Instant::now();
                        outputs[2]=Some(c351_shared_u1_message(owners[index],&input,&folded_input,&factor,&bank,&mut stats)?);
                        shared_ns[round][index]=t.elapsed().as_nanos();shared_cpu_ns[round][index]=c350_cpu_delta_ns(c)?;}
                    _=>unreachable!(),
                }
            }
            if outputs[0]!=outputs[1]||outputs[0]!=outputs[2]{return Err("C351 three-path message mismatch".into());}
            for arm in 0..3{messages[round][arm][index]=outputs[arm].ok_or("C351 arm missing")?;}
        }
    }
    for arm in 0..3{for index in 0..2{
        if messages[0][arm][index]!=messages[1][arm][index]||messages[0][arm][index]!=messages[2][arm][index]{
            return Err("C351 order-balanced message mismatch".into());
        }
    }}
    let expected_visits=template.len().checked_mul(6).ok_or("C351 expected visits overflow")?;
    if source_term_visits!=expected_visits||cached_term_visits!=expected_visits
        ||stats.shared_term_iterations!=template.len()||stats.owner_term_selections!=expected_visits{
        return Err(format!("C351 observed visit census source={source_term_visits} cached={cached_term_visits} bank={} selected={}",
            stats.shared_term_iterations,stats.owner_term_selections));
    }
    Ok(C351U1Samples{bank_build_ns,bank_build_cpu_ns,folded_x_ns,folded_x_cpu_ns,source_ns,source_cpu_ns,cached_ns,cached_cpu_ns,
        shared_ns,shared_cpu_ns,messages,bank_capacity_bytes:bank.capacity_bytes().ok_or("C351 bank capacity overflow")?,
        source_term_visits,cached_term_visits,bank_term_visits:stats.shared_term_iterations,
        selection_visits:stats.owner_term_selections})
}

#[cfg(test)]
pub(crate) fn c351_u1_audit_coefficients(
    template:&[Term],owner:usize,point:&[Fr],input:&[Fr],prefix_point:Fr,
    mut visit_source:impl FnMut(&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String>,
)->Result<Vec<(Vec<Fr>,Vec<Fr>)>,String>{
    const WIDTH:usize=1<<20;
    if template.len()!=396_561||point.len()!=40||input.len()!=WIDTH
        ||input.iter().any(|v|!v.is_zero()&&!v.is_one()){
        return Err("C351 coefficient audit geometry/input".into());
    }
    let factor=OneFamilyRowFactor::try_new(point,21,19,0,&[19],None)
        .ok_or("C351 coefficient audit factor")?;
    let prefix=[prefix_point];let weights=[Fr::one()-prefix_point,prefix_point];
    let mut paths=Vec::with_capacity(3);
    let (mut a,mut b)=direct_u_prefix_coefficients(WIDTH,&prefix,&weights,owner,input,
        |_,row|factor.local(row),|sink|visit_source(sink))?;
    let captured=vec![Some(template.to_vec())];let mut stats=BooleanUPreweightStats::default();
    let bank=BooleanUPreweightBank::build(&captured,&prefix,&weights,&factor,WIDTH,&mut stats)?;
    let (mut ca,mut cb)=direct_u_prefix_coefficients(WIDTH,&prefix,&weights,owner,input,
        |_,row|factor.local(row),|sink|{for term in template.iter().cloned(){sink(term)?;}Ok(())})?;
    let (mut sa,mut sb)=bank.coefficients(0,input,WIDTH>>1,&mut stats)?;
    let copy=factor.copy(owner);
    for vector in [&mut a,&mut b,&mut ca,&mut cb,&mut sa,&mut sb]{
        for value in vector.iter_mut(){*value*=copy;}
    }
    if stats.shared_term_iterations!=template.len()||stats.owner_term_selections!=template.len(){
        return Err("C351 coefficient audit bank visit census".into());
    }
    paths.push((a,b));paths.push((ca,cb));paths.push((sa,sb));
    Ok(paths)
}

#[cfg(test)]
pub(crate) fn c351_u1_mutant_three_paths(
    template:&[Term],owner:usize,factor_owner:usize,point:&[Fr],input:&[Fr],prefix_point:Fr,
    mut visit_source:impl FnMut(&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String>,
)->Result<[[Fr;3];3],String>{
    const WIDTH:usize=1<<20;
    if template.len()!=396_561||point.len()!=40||input.len()!=WIDTH
        ||input.iter().any(|v|!v.is_zero()&&!v.is_one()){
        return Err("C351 mutant geometry/input".into());
    }
    let factor=OneFamilyRowFactor::try_new(point,21,19,0,&[19],None)
        .ok_or("C351 mutant factor shape")?;
    let prefix=[prefix_point];let weights=[Fr::one()-prefix_point,prefix_point];
    let folded=(0..WIDTH/2).map(|i|(Fr::one()-prefix_point)*input[2*i]+prefix_point*input[2*i+1]).collect::<Vec<_>>();
    let captured=vec![Some(template.to_vec())];let mut stats=BooleanUPreweightStats::default();
    let bank=BooleanUPreweightBank::build(&captured,&prefix,&weights,&factor,WIDTH,&mut stats)?;
    let source=c351_literal_u1_message(factor_owner,input,&folded,&factor,&prefix,&weights,|sink|visit_source(sink))?;
    let cached=c351_literal_u1_message(factor_owner,input,&folded,&factor,&prefix,&weights,|sink|{
        for term in template.iter().cloned(){sink(term)?;}Ok(())
    })?;
    let shared=c351_shared_u1_message(factor_owner,input,&folded,&factor,&bank,&mut stats)?;
    if source!=cached||source!=shared{return Err(format!("C351 {owner} mutant arms disagree"));}
    Ok([source,cached,shared])
}

/// Compare the same two rows with source literal, cached literal and shared
/// paths in three cyclic orders. The caller binds template identity and rows.
#[cfg(test)]
pub(crate) fn c350_u0_literal_template_pairs(
    template:&[Term],owners:&[usize],point:&[Fr],owner_factors:&[Fr],
    mut load_input:impl FnMut(usize)->Result<Vec<Fr>,String>,
    mut visit_literal:impl FnMut(usize,&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String>,
)->Result<C350U0Samples,String>{
    const WIDTH:usize=1<<20;
    if owners.len()!=2||owner_factors.len()!=2||template.len()!=396_561||point.len()!=40{
        return Err("C350 U0 two-owner geometry".into());
    }
    let factor_cpu_before=c350_process_cpu_100ns()?;
    let factor_started=std::time::Instant::now();
    let factor=OneFamilyRowFactor::try_new(point,21,19,0,&[19],None)
        .ok_or("C350 one-family row factor shape")?;
    let factor_build_ns=factor_started.elapsed().as_nanos();
    let factor_build_cpu_ns=c350_cpu_delta_ns(factor_cpu_before)?;
    for index in 0..2{
        if factor.copy(owners[index])!=owner_factors[index]{
            return Err(format!("C350 owner {} independent 21-bit factor mismatch",owners[index]));
        }
    }
    let mut bank_stats=BooleanUPreweightStats::default();
    let bank_cpu_before=c350_process_cpu_100ns()?;
    let bank_started=std::time::Instant::now();
    let captured=vec![Some(template.to_vec())];
    let bank=BooleanUPreweightBank::build(&captured,&[],&[Fr::one()],&factor,WIDTH,&mut bank_stats)?;
    let bank_build_ns=bank_started.elapsed().as_nanos();
    let bank_build_cpu_ns=c350_cpu_delta_ns(bank_cpu_before)?;
    let mut source_literal_ns=[[0u128;2];3];
    let mut source_literal_cpu_ns=[[0u128;2];3];
    let mut cached_literal_ns=[[0u128;2];3];
    let mut cached_literal_cpu_ns=[[0u128;2];3];
    let mut shared_ns=[[0u128;2];3];
    let mut shared_cpu_ns=[[0u128;2];3];
    let mut messages=[[[[Fr::zero();3];2];3];3];
    let mut source_literal_visits=0usize;
    let mut cached_literal_visits=0usize;
    let mut shared_selection_visits=0usize;
    for round in 0..3{
        for index in 0..2{
            let input=load_input(index)?;
            if input.len()!=WIDTH||input.iter().any(|value|!value.is_zero()&&!value.is_one()){
                return Err(format!("C350 owner {} native X width/Boolean check",owners[index]));
            }
            let mut arm_messages=[None;3];
            for turn in 0..3{
                let arm=(turn+round)%3;
                match arm{
                    0=>{
                    let cpu_before=c350_process_cpu_100ns()?;
                    let started=std::time::Instant::now();
                    let message=c350_literal_u0_message(owners[index],&input,&factor,|sink|{
                        visit_literal(index,&mut |term|{
                            source_literal_visits=source_literal_visits.checked_add(1)
                                .ok_or("C350 source literal visit overflow")?;
                            sink(term)
                        })
                    })?;
                    source_literal_ns[round][index]=started.elapsed().as_nanos();
                    source_literal_cpu_ns[round][index]=c350_cpu_delta_ns(cpu_before)?;
                    arm_messages[0]=Some(message);
                    }
                    1=>{
                    let cpu_before=c350_process_cpu_100ns()?;
                    let started=std::time::Instant::now();
                    let message=c350_literal_u0_message(owners[index],&input,&factor,|sink|{
                        for term in template.iter().cloned(){
                            cached_literal_visits=cached_literal_visits.checked_add(1)
                                .ok_or("C350 cached literal visit overflow")?;
                            sink(term)?;
                        }
                        Ok(())
                    })?;
                    cached_literal_ns[round][index]=started.elapsed().as_nanos();
                    cached_literal_cpu_ns[round][index]=c350_cpu_delta_ns(cpu_before)?;
                    arm_messages[1]=Some(message);
                    }
                    2=>{
                    let before=bank_stats.owner_term_selections;
                    let cpu_before=c350_process_cpu_100ns()?;
                    let started=std::time::Instant::now();
                    let message=c350_shared_u0_message(owners[index],&input,&factor,&bank,&mut bank_stats)?;
                    shared_ns[round][index]=started.elapsed().as_nanos();
                    shared_cpu_ns[round][index]=c350_cpu_delta_ns(cpu_before)?;
                    shared_selection_visits=shared_selection_visits.checked_add(
                        bank_stats.owner_term_selections.checked_sub(before)
                            .ok_or("C350 shared selection counter regression")?
                    ).ok_or("C350 shared selection visit overflow")?;
                    arm_messages[2]=Some(message);
                    }
                    _=>return Err("C350 invalid arm order".into()),
                }
            }
            if source_literal_ns[round][index]==0||cached_literal_ns[round][index]==0
                ||shared_ns[round][index]==0{
                return Err("C350 arm order did not measure all three paths".into());
            }
            let source_message=arm_messages[0].ok_or("C350 source literal result absent")?;
            let cached_message=arm_messages[1].ok_or("C350 cached literal result absent")?;
            let shared_message=arm_messages[2].ok_or("C350 shared result absent")?;
            if source_message!=cached_message||source_message!=shared_message{
                return Err(format!("C350 owner {} three-path U0 messages differ",owners[index]));
            }
            for arm in 0..3{
                messages[round][arm][index]=arm_messages[arm]
                    .ok_or("C350 order-balanced arm result absent")?;
            }
        }
    }
    for index in 0..2{
        for arm in 0..3{
            if messages[0][arm][index]!=messages[1][arm][index]
                ||messages[0][arm][index]!=messages[2][arm][index]{
                return Err(format!("C350 owner {} arm {arm} order-balanced messages differ",owners[index]));
            }
        }
    }
    let shared_build_visits=bank_stats.shared_term_iterations;
    if source_literal_visits!=template.len()*6||cached_literal_visits!=template.len()*6
        ||shared_build_visits!=template.len()||shared_selection_visits!=template.len()*6{
        return Err("C350 source/cached/build/selection visit census".into());
    }
    Ok(C350U0Samples{
        factor_build_ns,factor_build_cpu_ns,bank_build_ns,bank_build_cpu_ns,
        source_literal_ns,source_literal_cpu_ns,cached_literal_ns,cached_literal_cpu_ns,
        shared_ns,shared_cpu_ns,messages,source_literal_visits,cached_literal_visits,
        shared_build_visits,shared_selection_visits,
        bank_capacity_bytes:bank.capacity_bytes().ok_or("C350 bank capacity overflow")?,
    })
}

/// Evaluate one isolated C350 mutation with source literal, cached literal,
/// and shared bank paths. Mutation setup and execution remain outside timings.
#[cfg(test)]
pub(crate) fn c350_u0_mutant_three_paths(
    template:&[Term],factor_owner:usize,point:&[Fr],input:&[Fr],
    mut visit_source:impl FnMut(&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String>,
)->Result<[[Fr;3];3],String>{
    const WIDTH:usize=1<<20;
    if template.len()!=396_561||point.len()!=40||input.len()!=WIDTH
        ||input.iter().any(|value|!value.is_zero()&&!value.is_one()){
        return Err("C350 mutant three-path geometry/input".into());
    }
    let factor=OneFamilyRowFactor::try_new(point,21,19,0,&[19],None)
        .ok_or("C350 mutant one-family row factor shape")?;
    let captured=vec![Some(template.to_vec())];
    let mut stats=BooleanUPreweightStats::default();
    let bank=BooleanUPreweightBank::build(&captured,&[],&[Fr::one()],&factor,WIDTH,&mut stats)?;
    let source=c350_literal_u0_message(factor_owner,input,&factor,|sink|visit_source(sink))?;
    let cached=c350_literal_u0_message(factor_owner,input,&factor,|sink|{
        for term in template.iter().cloned(){sink(term)?;}
        Ok(())
    })?;
    let shared=c350_shared_u0_message(factor_owner,input,&factor,&bank,&mut stats)?;
    if source!=cached||source!=shared{
        return Err("C350 mutant source/cached/shared outputs differ".into());
    }
    Ok([source,cached,shared])
}

/// C323 test-only local producer cost split. No full-H21 input producer,
/// transcript, commitment or proof is exercised by this timing sample.
#[cfg(test)]
#[derive(Clone,Copy,Debug,Default)]
pub(crate) struct C323OwnerCost {
    pub(crate) load_check_ns:u64,
    pub(crate) select_ns:u64,
    pub(crate) message_ns:u64,
}

#[cfg(test)]
pub(crate) struct C323U0Cost {
    pub(crate) bank_build_ns:u64,
    pub(crate) bank_capacity_bytes:usize,
    pub(crate) direct_term_visits:usize,
    pub(crate) bank_build_term_visits:usize,
    pub(crate) owner_selection_visits:usize,
    pub(crate) measured:[[C323OwnerCost;4];2],
}

#[cfg(test)]
pub(crate) fn c323_u0_shared_cost_split(
    templates:&[Vec<Term>;4],owners:[usize;4],point:&[Fr],owner_factors:&[Fr;4],
    mut load_input:impl FnMut(usize)->Result<Vec<Fr>,String>,
    mut visit_literal:impl FnMut(usize,&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String>,
)->Result<C323U0Cost,String>{
    use std::{hint::black_box,time::Instant};
    const WIDTH:usize=1<<20;
    if point.len()!=40 || templates.iter().any(|template|template!=&templates[0]) {
        return Err("C323 point or common Carry template mismatch".into());
    }
    let factor=OneFamilyRowFactor::try_new(point,21,19,0,&[19],None)
        .ok_or("C323 one-family row factor shape")?;
    for (index,owner) in owners.iter().copied().enumerate(){
        if factor.copy(owner)!=owner_factors[index] || factor.copy(owner).is_zero(){
            return Err(format!("C323 owner {owner} factor mismatch"));
        }
    }
    let captured=vec![Some(templates[0].clone())];
    let mut stats=BooleanUPreweightStats::default();
    let bank_start=Instant::now();
    let bank=BooleanUPreweightBank::build(&captured,&[],&[Fr::one()],&factor,WIDTH,&mut stats)?;
    let bank_build_ns=u64::try_from(bank_start.elapsed().as_nanos())
        .map_err(|_|"C323 bank duration width")?;
    let bank_capacity_bytes=bank.capacity_bytes().ok_or("C323 bank capacity overflow")?;
    let mut direct_term_visits=0usize;
    let mut expected_messages=[[Fr::zero();3];4];

    // One untimed, independently re-enumerated literal baseline per owner.
    // Compare dense A/B exactly here, then retain only the three coefficients
    // of each scaled message before the warm-up and measured cycles.
    for (index,owner) in owners.iter().copied().enumerate(){
        let input=load_input(index)?;
        if input.len()!=WIDTH || input.iter().any(|value|!value.is_zero()&&!value.is_one()){
            return Err(format!("C323 owner {owner} baseline X is not Boolean/complete"));
        }
        let (direct_a,direct_b)=direct_u_prefix_coefficients(
            WIDTH,&[],&[Fr::one()],owner,&input,|_,row|factor.local(row),
            |sink|visit_literal(index,&mut |term|{
                direct_term_visits=direct_term_visits.checked_add(1)
                    .ok_or("C323 direct visit counter overflow")?;
                sink(term)
            }),
        )?;
        let (shared_a,shared_b)=bank.coefficients(0,&input,WIDTH,&mut stats)?;
        if direct_a!=shared_a || direct_b!=shared_b{
            return Err(format!("C323 owner {owner} direct/shared A/B mismatch"));
        }
        let direct_message:[Fr;3]=gkr::quadratic_message(&direct_a,&direct_b,&input)
            .try_into().map_err(|_|"C323 direct message width")?;
        let shared_message:[Fr;3]=gkr::quadratic_message(&shared_a,&shared_b,&input)
            .try_into().map_err(|_|"C323 shared message width")?;
        let scale=factor.copy(owner);
        expected_messages[index]=direct_message.map(|value|value*scale);
        if shared_message.map(|value|value*scale)!=expected_messages[index]{
            return Err(format!("C323 owner {owner} direct/shared U0 message mismatch"));
        }
        black_box(expected_messages[index]);
    }

    // Cycle zero warms the bank and fixture pages. Only cycles one/two enter
    // the reported sample. Dense X, A and B are dropped at each owner boundary.
    let mut measured=[[C323OwnerCost::default();4];2];
    for cycle in 0..3usize{
        for (index,owner) in owners.iter().copied().enumerate(){
            let load_start=Instant::now();
            let input=load_input(index)?;
            if input.len()!=WIDTH || input.iter().any(|value|!value.is_zero()&&!value.is_one()){
                return Err(format!("C323 owner {owner} timed X is not Boolean/complete"));
            }
            black_box(&input);
            let load_check_ns=u64::try_from(load_start.elapsed().as_nanos())
                .map_err(|_|"C323 load/check duration width")?;

            let select_start=Instant::now();
            let (a,b)=bank.coefficients(0,&input,WIDTH,&mut stats)?;
            black_box((&a,&b));
            let select_ns=u64::try_from(select_start.elapsed().as_nanos())
                .map_err(|_|"C323 selection duration width")?;

            let message_start=Instant::now();
            let message:[Fr;3]=gkr::quadratic_message(&a,&b,&input)
                .try_into().map_err(|_|"C323 measured message width")?;
            let scaled=message.map(|value|value*factor.copy(owner));
            black_box(scaled);
            let message_ns=u64::try_from(message_start.elapsed().as_nanos())
                .map_err(|_|"C323 message duration width")?;
            if scaled!=expected_messages[index]{
                return Err(format!("C323 owner {owner} measured U0 message mismatch in cycle {cycle}"));
            }
            if cycle>0{
                measured[cycle-1][index]=C323OwnerCost{load_check_ns,select_ns,message_ns};
            }
        }
    }
    let expected_direct=templates[0].len().checked_mul(4)
        .ok_or("C323 expected direct visits overflow")?;
    let expected_select=templates[0].len().checked_mul(4*4)
        .ok_or("C323 expected selection visits overflow")?;
    if direct_term_visits!=expected_direct || stats.shared_term_iterations!=templates[0].len()
        || stats.owner_term_selections!=expected_select {
        return Err("C323 literal/build/selection operation counts mismatch".into());
    }
    Ok(C323U0Cost{
        bank_build_ns,bank_capacity_bytes,direct_term_visits,
        bank_build_term_visits:stats.shared_term_iterations,
        owner_selection_visits:stats.owner_term_selections,measured,
    })
}

#[cfg(test)]
#[derive(Clone,Copy,Default)]
pub(crate) struct C324OwnerCost{pub(crate) load_check_ns:u64,pub(crate) fused_select_message_ns:u64}
#[cfg(test)]
pub(crate) struct C324U0FusedCost{
    pub(crate) bank_build_ns:u64,pub(crate) bank_capacity_bytes:usize,
    pub(crate) direct_term_visits:usize,pub(crate) bank_build_term_visits:usize,
    pub(crate) fused_entry_visits:usize,pub(crate) measured:[[C324OwnerCost;4];2],
}

/// C324 test-only first-U fusion differential. Direct and shared dense
/// coefficients/messages are independently retained as the baseline; only
/// the timed candidate path fuses selected-entry and message accumulation.
#[cfg(test)]
pub(crate) fn c324_u0_fused_cost_split(
    templates:&[Vec<Term>;4],owners:[usize;4],point:&[Fr],owner_factors:&[Fr;4],
    mut load_input:impl FnMut(usize)->Result<Vec<Fr>,String>,
    mut visit_literal:impl FnMut(usize,&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String>,
)->Result<C324U0FusedCost,String>{
    use std::{hint::black_box,time::Instant};
    const WIDTH:usize=1<<20;
    if point.len()!=40||templates.iter().any(|template|template!=&templates[0]){
        return Err("C324 point or common Carry template mismatch".into());
    }
    let factor=OneFamilyRowFactor::try_new(point,21,19,0,&[19],None)
        .ok_or("C324 one-family row factor shape")?;
    for (index,owner) in owners.iter().copied().enumerate(){
        if factor.copy(owner)!=owner_factors[index]||factor.copy(owner).is_zero(){
            return Err(format!("C324 owner {owner} factor mismatch"));
        }
    }
    let captured=vec![Some(templates[0].clone())];
    let mut stats=BooleanUPreweightStats::default();
    let bank_start=Instant::now();
    let bank=BooleanUPreweightBank::build(&captured,&[],&[Fr::one()],&factor,WIDTH,&mut stats)?;
    let bank_build_ns=u64::try_from(bank_start.elapsed().as_nanos()).map_err(|_|"C324 bank duration width")?;
    let bank_capacity_bytes=bank.capacity_bytes().ok_or("C324 bank capacity overflow")?;
    let mut direct_term_visits=0usize;
    let mut expected_messages=[[Fr::zero();3];4];

    // Compare the candidate to both existing dense routes before timing.
    for (index,owner) in owners.iter().copied().enumerate(){
        let input=load_input(index)?;
        if input.len()!=WIDTH||input.iter().any(|value|!value.is_zero()&&!value.is_one()){
            return Err(format!("C324 owner {owner} baseline X is not Boolean/complete"));
        }
        let (direct_a,direct_b)=direct_u_prefix_coefficients(WIDTH,&[],&[Fr::one()],owner,&input,
            |_,row|factor.local(row),|sink|visit_literal(index,&mut |term|{
                direct_term_visits=direct_term_visits.checked_add(1).ok_or("C324 direct visit counter overflow")?;
                sink(term)
            }))?;
        let (shared_a,shared_b)=bank.coefficients(0,&input,WIDTH,&mut stats)?;
        if direct_a!=shared_a||direct_b!=shared_b{return Err(format!("C324 owner {owner} direct/shared A/B mismatch"));}
        let direct_message:[Fr;3]=gkr::quadratic_message(&direct_a,&direct_b,&input)
            .try_into().map_err(|_|"C324 direct message width")?;
        let shared_message:[Fr;3]=gkr::quadratic_message(&shared_a,&shared_b,&input)
            .try_into().map_err(|_|"C324 shared message width")?;
        let fused_message=bank.fused_u0_message_from_checked_boolean_input(0,&input)?;
        let scale=factor.copy(owner);
        expected_messages[index]=direct_message.map(|value|value*scale);
        if shared_message.map(|value|value*scale)!=expected_messages[index]
            ||fused_message.map(|value|value*scale)!=expected_messages[index]{
            return Err(format!("C324 owner {owner} direct/shared/fused U0 message mismatch"));
        }
        black_box(expected_messages[index]);
    }

    // Cycle zero warms the full X load and fused path. At most two measured
    // cycles follow; the owner factor is applied after the fused local message.
    let mut measured=[[C324OwnerCost::default();4];2];
    let mut fused_entry_visits=0usize;
    for cycle in 0..3usize{
        for (index,owner) in owners.iter().copied().enumerate(){
            let load_start=Instant::now();let input=load_input(index)?;
            if input.len()!=WIDTH||input.iter().any(|value|!value.is_zero()&&!value.is_one()){
                return Err(format!("C324 owner {owner} timed X is not Boolean/complete"));
            }
            black_box(&input);
            let load_check_ns=u64::try_from(load_start.elapsed().as_nanos()).map_err(|_|"C324 load/check duration width")?;
            let fused_start=Instant::now();
            let local=bank.fused_u0_message_from_checked_boolean_input(0,&input)?;
            let scaled=local.map(|value|value*factor.copy(owner));black_box(scaled);
            let fused_select_message_ns=u64::try_from(fused_start.elapsed().as_nanos())
                .map_err(|_|"C324 fused selection/message duration width")?;
            if scaled!=expected_messages[index]{return Err(format!("C324 owner {owner} fused U0 mismatch in cycle {cycle}"));}
            fused_entry_visits=fused_entry_visits.checked_add(templates[0].len())
                .ok_or("C324 fused entry visit counter overflow")?;
            if cycle>0{measured[cycle-1][index]=C324OwnerCost{load_check_ns,fused_select_message_ns};}
        }
    }
    let expected_direct=templates[0].len().checked_mul(4).ok_or("C324 direct count overflow")?;
    let expected_fused=templates[0].len().checked_mul(4*3).ok_or("C324 fused count overflow")?;
    if direct_term_visits!=expected_direct||stats.shared_term_iterations!=templates[0].len()
        ||stats.owner_term_selections!=templates[0].len().checked_mul(4).ok_or("C324 dense selection count overflow")?
        ||fused_entry_visits!=expected_fused{
        return Err("C324 direct/build/dense/fused operation counts mismatch".into());
    }
    Ok(C324U0FusedCost{bank_build_ns,bank_capacity_bytes,direct_term_visits,
        bank_build_term_visits:stats.shared_term_iterations,fused_entry_visits,measured})
}

fn boolean_u_loader_scratch_bound(width:usize)->Option<usize>{
    // Native read_owner appends one 2^16-field bank at a time for a 2^20
    // owner. Its packed bank buffer is retained alongside that field bank.
    width.checked_div(16)?.checked_mul(std::mem::size_of::<Fr>())?
        .checked_add(width.checked_div(128)?)
}

fn boolean_u_v_reservation(width:usize)->Option<usize>{
    boolean_u_loader_scratch_bound(width)?.checked_add(std::mem::size_of::<BooleanUPreweightStats>())?
        .checked_add(2*std::mem::size_of::<std::cell::Cell<usize>>())
}

fn boolean_u_eq_weights(point:&[Fr])->Result<Vec<Fr>,String>{
    let len=1usize.checked_shl(u32::try_from(point.len()).map_err(|_|"Boolean U equality dimensions")?)
        .ok_or("Boolean U equality dimensions overflow")?;
    let mut weights=Vec::new();weights.try_reserve_exact(len).map_err(|_|"Boolean U equality reservation failed")?;
    if weights.capacity()!=len{return Err("Boolean U equality reservation capacity drift".into());}
    weights.push(Fr::one());
    for coordinate in point{
        let old_len=weights.len();weights.resize(old_len*2,Fr::zero());
        for index in 0..old_len{
            let old=weights[index];weights[index]=old*(Fr::one()-coordinate);weights[index+old_len]=old * *coordinate;
        }
    }
    Ok(weights)
}

fn boolean_u_prebind_capacity_bound(input_bits:usize,copy_bits:usize,base_row_bits:usize,
    admission:&GroupedVAdmission)->Option<usize>{
    boolean_u_prebind_capacity_bound_with_policy(input_bits,copy_bits,base_row_bits,admission,GroupedDimensionPolicy::Generic24)
}
fn boolean_u_prebind_capacity_bound_with_policy(input_bits:usize,copy_bits:usize,base_row_bits:usize,
    admission:&GroupedVAdmission,policy:GroupedDimensionPolicy)->Option<usize>{
    if input_bits>24||copy_bits>24||base_row_bits>21
        ||!policy.dimensions_allowed(input_bits,copy_bits,base_row_bits){return None;}
    policy.validate_census(admission).ok()?;
    let width=1usize.checked_shl(input_bits as u32)?;let copies=1usize.checked_shl(copy_bits as u32)?;
    let count=admission.expected_terms_per_group.iter().try_fold(0usize,|sum,n|sum.checked_add(*n))?;
    let field=std::mem::size_of::<Fr>();
    let templates=count.checked_mul(std::mem::size_of::<Term>())?;
    let weights=count.checked_mul(std::mem::size_of::<BooleanUPreweight>())?;
    let owner_banks=width.checked_mul(3)?.checked_mul(field)?;
    // Reserve the old/new equality-table growth, not a second preweight bank.
    let prefix_growth=width.checked_add(width/2)?.checked_mul(field)?;
    let row_tables=TensorRowWeightLookup::MAX_LOCAL_TABLE_BYTES.checked_add(TensorRowWeightLookup::MAX_SCALE_BYTES)?;
    let owner_metadata=copies.checked_mul(2*std::mem::size_of::<usize>()+4*field)?;
    templates.checked_add(weights)?.checked_add(owner_banks)?.checked_add(prefix_growth)?
        .checked_add(row_tables)?.checked_add(boolean_u_loader_scratch_bound(width)?)?
        .checked_add(owner_metadata)?.checked_add(8*1024*1024)?.checked_add(policy.extra_capacity_bytes())
}

fn boolean_u_row_preparation_capacity_bytes(
    templates:&Vec<Option<Vec<Term>>>,admission:&GroupedVAdmission,group_stats:&GroupedVStats,
    expected_counts_capacity:usize,r_capacity:usize,width:usize,
)->Option<usize>{
    // Local equality-table resize can retain its old allocation while the
    // replacement is allocated. The existing 64+32 MiB row allowance covers
    // either that 64+32 MiB overlap or the final local/copy tables. Reserve it
    // before TensorRowWeightLookup::new, plus bounded lookup metadata.
    let row_growth=TensorRowWeightLookup::MAX_LOCAL_TABLE_BYTES
        .checked_add(TensorRowWeightLookup::MAX_SCALE_BYTES)?.checked_add(64*1024)?;
    let words=expected_counts_capacity.checked_add(admission.group_by_copy.len())?
        .checked_add(admission.expected_terms_per_group.len())?.checked_add(group_stats.group_owner_counts.capacity())?
        .checked_add(group_stats.group_term_counts.capacity())?;
    let fields=r_capacity.checked_add(group_stats.group_weight_sums.capacity())?
        .checked_add(group_stats.group_d_local_contributions.capacity())?;
    grouped_template_capacity_bytes(templates).ok()?.checked_add(row_growth)?
        .checked_add(group_stats.private_capacity_reservation_bytes)?
        .checked_add(words.checked_mul(std::mem::size_of::<usize>())?)?
        .checked_add(fields.checked_mul(std::mem::size_of::<Fr>())?)?
        .checked_add(boolean_u_loader_scratch_bound(width)?)?
        .checked_add(std::mem::size_of::<BooleanUPreweightStats>())?
        .checked_add(std::mem::size_of::<GroupedVStats>())?
        .checked_add(16*std::mem::size_of::<Vec<Fr>>())
}

/// Checked live inventory plus explicitly declared scratch reservations. The
/// 8 MiB preflight headroom is not silently substituted for this inventory.
fn boolean_u_capacity_bytes(
    templates:&Vec<Option<Vec<Term>>>,admission:&GroupedVAdmission,row_lookup:&TensorRowWeightLookup<'_>,
    factor:&OneFamilyRowFactor<'_>,group_stats:&GroupedVStats,expected_counts_capacity:usize,
    rounds:&Vec<Vec<Fr>>,point_capacity:usize,prefix_capacity:usize,bank_capacity_bytes:usize,
    owner_capacity:usize,coefficient_capacity:usize,high_capacity:usize,extra_scratch_fields:usize,width:usize,
)->Option<usize>{
    let field=std::mem::size_of::<Fr>();
    let factor_owned=match &factor.local_weights{std::borrow::Cow::Owned(values)=>values.capacity(),_=>0};
    let mut bytes=grouped_template_capacity_bytes(templates).ok()?
        .checked_add(group_stats.private_capacity_reservation_bytes)?
        .checked_add(row_lookup.capacity_bytes()?)?.checked_add(factor.copy_weights.capacity_bytes()?)?
        .checked_add(bank_capacity_bytes)?.checked_add(boolean_u_loader_scratch_bound(width)?)?;
    let fields=point_capacity.checked_add(prefix_capacity)?.checked_add(owner_capacity)?
        .checked_add(coefficient_capacity)?.checked_add(high_capacity)?.checked_add(factor_owned)?
        .checked_add(extra_scratch_fields)?.checked_add(group_stats.group_weight_sums.capacity())?
        .checked_add(group_stats.group_d_local_contributions.capacity())?;
    bytes=bytes.checked_add(fields.checked_mul(field)?)?;
    let words=expected_counts_capacity.checked_add(admission.group_by_copy.len())?
        .checked_add(admission.expected_terms_per_group.len())?.checked_add(group_stats.group_owner_counts.capacity())?
        .checked_add(group_stats.group_term_counts.capacity())?;
    bytes=bytes.checked_add(words.checked_mul(std::mem::size_of::<usize>())?)?
        .checked_add(grouped_v_round_capacity_bytes(rounds).ok()?)?
        .checked_add(std::mem::size_of::<BooleanUPreweightStats>())?
        .checked_add(std::mem::size_of::<GroupedVStats>())?
        .checked_add(std::mem::size_of::<OneFamilyRowFactor<'_>>())?
        .checked_add(std::mem::size_of::<TensorRowWeightLookup<'_>>())?
        .checked_add(16*std::mem::size_of::<Vec<Fr>>())?;
    Some(bytes)
}

fn prove_boolean_u_prefixes(
    width:usize,input_bits:usize,copies:usize,templates:&Vec<Option<Vec<Term>>>,admission:&GroupedVAdmission,
    row_lookup:&TensorRowWeightLookup<'_>,factor:&OneFamilyRowFactor<'_>,group_stats:&GroupedVStats,
    expected_counts_capacity:usize,r_capacity:usize,load_copy:&mut impl FnMut(usize)->Result<Vec<Fr>,String>,
    claim:&mut Fr,rounds:&mut Vec<Vec<Fr>>,u_local:&mut Vec<Fr>,transcript:&mut Transcript,
    stats:&mut BooleanUPreweightStats,
)->Result<(Vec<Fr>,Vec<Fr>,Vec<Fr>,Vec<Fr>),String>{
    prove_boolean_u_prefixes_with_fold(width,input_bits,copies,templates,admission,row_lookup,factor,group_stats,
        expected_counts_capacity,r_capacity,load_copy,claim,rounds,u_local,transcript,stats,BooleanXFoldMode::Legacy,None,None)
}
fn prove_boolean_u_prefixes_with_fold(
    width:usize,input_bits:usize,copies:usize,templates:&Vec<Option<Vec<Term>>>,admission:&GroupedVAdmission,
    row_lookup:&TensorRowWeightLookup<'_>,factor:&OneFamilyRowFactor<'_>,group_stats:&GroupedVStats,
    expected_counts_capacity:usize,r_capacity:usize,load_copy:&mut impl FnMut(usize)->Result<Vec<Fr>,String>,
    claim:&mut Fr,rounds:&mut Vec<Vec<Fr>>,u_local:&mut Vec<Fr>,transcript:&mut Transcript,
    stats:&mut BooleanUPreweightStats,mode:BooleanXFoldMode,mut subset:Option<&mut BooleanSubset4Stats>,plan:Option<&UCapacityPlan>,
)->Result<(Vec<Fr>,Vec<Fr>,Vec<Fr>,Vec<Fr>),String>{
    let table_live=std::cell::Cell::new(0usize);
    let extra=if plan.is_some(){u_sum(&[subset4_metadata_bytes().ok_or("subset4 capacity arithmetic")?,UCapacityPlan::metadata()?])?}else{0};
    let inventory=|prefix_capacity,bank_capacity,owner_capacity,coefficient_capacity,high_capacity,
        extra_scratch,rounds:&Vec<Vec<Fr>>,u_capacity|{
        boolean_u_capacity_bytes(templates,admission,row_lookup,factor,group_stats,expected_counts_capacity,
            rounds,r_capacity+u_capacity,prefix_capacity,bank_capacity,owner_capacity,coefficient_capacity,
            high_capacity,extra_scratch,width).and_then(|n|n.checked_add(extra))
            .and_then(|n|n.checked_add(table_live.get()))
            .ok_or("Boolean U live capacity overflow".to_owned())
    };
    stats.record_capacity(1,inventory(0,0,0,0,0,0,rounds,u_local.capacity())?)?;
    let mut high_a=Vec::new();let mut high_b=Vec::new();let mut high_x=Vec::new();
    let mut handoff_weights=Vec::new();
    // Prefix banks are scoped to this iteration: no old/new bank overlap.
    for k in 0..=input_bits{
        let mut live=ULive::default();
        if k==input_bits{phase_mark("u_local_done")?;}
        let high_bound=if k==input_bits{copies.checked_mul(3).ok_or("Boolean U high capacity overflow")?}else{0};
        let prefix_len=1usize.checked_shl(k as u32).ok_or("Boolean U prefix table extent overflow")?;
        let prefix_growth=prefix_len.checked_add(prefix_len/2).ok_or("Boolean U prefix growth overflow")?;
        if let Some(p)=plan{p.before(UPhase::Prefix,k,live)?;}
        if plan.is_none(){stats.record_capacity(2,inventory(0,0,0,0,high_bound,prefix_growth,rounds,u_local.capacity())?)?;}
        let prefix_started=std::time::Instant::now();
        let prefix_weights=boolean_u_eq_weights(u_local)?;
        if prefix_weights.len()!=prefix_len||prefix_weights.capacity()!=prefix_len{
            return Err("Boolean U equality-table capacity drift".into());
        }
        live.prefix=Some(k);
        let term_count=admission.expected_terms_per_group.iter().try_fold(0usize,|sum,n|sum.checked_add(*n))
            .ok_or("Boolean U preweight count overflow")?;
        let bank_bound=term_count.checked_mul(std::mem::size_of::<BooleanUPreweight>())
            .and_then(|n|n.checked_add(templates.len()*std::mem::size_of::<(usize,usize)>()))
            .and_then(|n|n.checked_add(std::mem::size_of::<BooleanUPreweightBank>()))
            .ok_or("Boolean U preweight allocation overflow")?;
        if let Some(p)=plan{p.before(UPhase::Bank,k,live)?;}
        if plan.is_none(){stats.record_capacity(2,inventory(prefix_weights.capacity(),bank_bound,0,0,high_bound,0,rounds,u_local.capacity())?)?;}
        let bank=BooleanUPreweightBank::build(templates,u_local,&prefix_weights,factor,width,stats)?;
        live.bank=true;
        stats.u_prefix_preweight_elapsed_ns=stats.u_prefix_preweight_elapsed_ns.checked_add(elapsed_nanos(prefix_started))
            .ok_or("Boolean U prefix timing overflow")?;
        let bank_capacity=bank.capacity_bytes().ok_or("Boolean U preweight capacity overflow")?;
        if let Some(p)=plan{
            if bank_capacity>p.bank{return Err("capacity46 bank capacity drift".into());}
            p.before(UPhase::Table,k,live)?;
        }
        let table=if mode==BooleanXFoldMode::Subset4{Some(BooleanSubset4Table::build(u_local,&prefix_weights,width,
            subset.as_deref_mut().ok_or("subset4 statistics missing")?)?)}else{None};
        live.table=table.is_some();
        table_live.set(table.as_ref().map_or(0,|t|t.values.capacity()*std::mem::size_of::<Fr>()));
        if let Some(p)=plan{
            let n=inventory(prefix_weights.capacity(),bank_capacity,0,0,0,0,rounds,u_local.capacity())?;
            p.actual(UPhase::Table,k,n,group_stats.private_capacity_reservation_bytes,table_live.get(),0)?;
            stats.record_capacity(2,n)?;
        }
        if k==input_bits{
            if let Some(p)=plan{p.before(UPhase::HighReserve,k,live)?;}
            if plan.is_none(){stats.record_capacity(4,inventory(prefix_weights.capacity(),bank_capacity,0,0,high_bound,0,rounds,u_local.capacity())?)?;}
            for vector in [&mut high_a,&mut high_b,&mut high_x]{
                vector.try_reserve_exact(copies).map_err(|_|"Boolean U high handoff reservation failed")?;
                if vector.capacity()!=copies{return Err("Boolean U high handoff capacity drift".into());}
            }
        }
        let folded_width=width>>k;
        let coefficient_bound=folded_width.checked_mul(2).ok_or("Boolean U coefficient capacity overflow")?;
        let mut polynomial=[Fr::zero();3];
        for copy in 0..copies{
            let high_capacity=high_a.capacity()+high_b.capacity()+high_x.capacity();
            let phase=if k==input_bits{4}else{3};
            // This projection closes all allocations before loading X and
            // before reserving A/B. The loader wrapper enforces payload size.
            if let Some(p)=plan{p.before(UPhase::Load,k,live)?;}
            if plan.is_none(){stats.record_capacity(phase,inventory(prefix_weights.capacity(),bank_capacity,width,
                coefficient_bound,high_capacity,3,rounds,u_local.capacity())?)?;}
            let input=read_copy(load_copy,copy,width)?;
            live.owner=true;
            if let Some(p)=plan{
                let n=inventory(prefix_weights.capacity(),bank_capacity,input.capacity(),0,high_capacity,0,rounds,u_local.capacity())?;
                p.actual(UPhase::Load,k,n,group_stats.private_capacity_reservation_bytes,table_live.get(),high_capacity)?;
                p.before(UPhase::Apply,k,live)?;
            }
            #[cfg(test)]
            let fused_k1=mode==BooleanXFoldMode::FusedPrefixK1&&k==1&&k<input_bits;
            #[cfg(not(test))]
            let fused_k1=false;
            let selection_started=std::time::Instant::now();
            let (a,b)=if fused_k1{(Vec::new(),Vec::new())}else{
                bank.coefficients(admission.group_by_copy[copy],&input,folded_width,stats)?
            };
            if !fused_k1{
                stats.u_owner_selection_elapsed_ns=stats.u_owner_selection_elapsed_ns.checked_add(elapsed_nanos(selection_started))
                    .ok_or("Boolean U selection timing overflow")?;
            }
            live.coeff=!fused_k1;
            let n=inventory(prefix_weights.capacity(),bank_capacity,input.capacity(),
                a.capacity()+b.capacity(),high_capacity,3,rounds,u_local.capacity())?;
            if let Some(p)=plan{p.actual(UPhase::Apply,k,n,group_stats.private_capacity_reservation_bytes,table_live.get(),high_capacity)?;}
            stats.record_capacity(phase,n)?;
            let fold_started=std::time::Instant::now();
            let mut x=input;
            if fused_k1{
                let local=bank.fused_u1_message_from_checked_boolean_input(admission.group_by_copy[copy],&x,
                    *u_local.first().ok_or("Boolean U fused U1 challenge missing")?)?;
                stats.u_owner_selection_elapsed_ns=stats.u_owner_selection_elapsed_ns.checked_add(elapsed_nanos(selection_started))
                    .ok_or("Boolean U selection timing overflow")?;
                for (sum,value) in polynomial.iter_mut().zip(local){*sum+=factor.copy(copy)*value;}
                stats.owner_term_selections=stats.owner_term_selections.checked_add(
                    bank.ranges[admission.group_by_copy[copy]].1-bank.ranges[admission.group_by_copy[copy]].0)
                    .ok_or("Boolean U selection counter overflow")?;
                stats.u_x_fold_elapsed_ns=stats.u_x_fold_elapsed_ns.checked_add(elapsed_nanos(fold_started))
                    .ok_or("Boolean U fold timing overflow")?;
            }else{
                if let Some(table)=&table{table.apply(&mut x,subset.as_deref_mut().ok_or("subset4 statistics missing")?)?;}
                else{for challenge in u_local.iter(){gkr::fold(&mut x,*challenge);}}
                stats.u_x_fold_elapsed_ns=stats.u_x_fold_elapsed_ns.checked_add(elapsed_nanos(fold_started))
                    .ok_or("Boolean U fold timing overflow")?;
            }
            if k==input_bits{
                high_a.push(factor.copy(copy)*a[0]);high_b.push(factor.copy(copy)*b[0]);high_x.push(x[0]);
            }else if !fused_k1{OneFamilyRowFactor::add_scaled_message(&mut polynomial,&a,&b,&x,factor.copy(copy));}
            drop(a);drop(b);drop(x);live.owner=false;live.coeff=false;
        }
        // Both weights are destroyed before the next prefix or V allocation.
        drop(bank);
        drop(table);
        table_live.set(0);
        live=ULive::default();
        if k==input_bits{handoff_weights=prefix_weights;}else{drop(prefix_weights);}
        if k<input_bits{
            let descriptor_growth=rounds.capacity().checked_add(1).and_then(|n|n.checked_mul(2))
                .and_then(|n|n.checked_mul(std::mem::size_of::<Vec<Fr>>()))
                .ok_or("Boolean U round descriptor growth overflow")?;
            // Existing descriptors are already counted. Add the projected new
            // allocation and the current three-field message before push.
            let send_peak=inventory(0,0,0,0,0,3,rounds,u_local.capacity())?
                .checked_add(descriptor_growth).ok_or("Boolean U round allocation overflow")?;
            if let Some(p)=plan{
                p.before(UPhase::Send,k,live)?;
                p.high_actual(rounds,&[&*u_local])?;
                // Outer descriptors are already reserved by the opt-in caller.
                let n=inventory(0,0,0,0,0,3,rounds,u_local.capacity())?;
                p.actual(UPhase::Send,k,n,group_stats.private_capacity_reservation_bytes,0,0)?;
                stats.record_capacity(2,n)?;
            }else{stats.record_capacity(2,send_peak)?;}
            u_local.push(send_round(polynomial.to_vec(),claim,rounds,transcript).map_err(|e|e.to_string())?);
            if let Some(p)=plan{p.high_actual(rounds,&[&*u_local])?;}
        }
    }
    // prove_phase clones high X and grows point/round storage. Reserve its
    // explicit field allowance here; round descriptors are also bounded.
    let high_capacity=high_a.capacity()+high_b.capacity()+high_x.capacity();
    let copy_bits=copies.trailing_zeros() as usize;
    let high_scratch=copies.checked_add(5*copy_bits).ok_or("Boolean U high scratch overflow")?;
    let round_growth=rounds.capacity().checked_add(copy_bits).and_then(|n|n.checked_mul(2))
        .and_then(|n|n.checked_mul(std::mem::size_of::<Vec<Fr>>())).ok_or("Boolean U high round growth overflow")?;
    let high_peak=inventory(handoff_weights.capacity(),0,0,0,high_capacity,high_scratch,rounds,u_local.capacity())?
        .checked_add(round_growth).ok_or("Boolean U high phase overflow")?;
    if let Some(p)=plan{
        p.before(UPhase::High,input_bits,ULive::default())?;
        let n=inventory(handoff_weights.capacity(),0,0,0,high_capacity,high_scratch,rounds,u_local.capacity())?;
        p.actual(UPhase::High,input_bits,n,group_stats.private_capacity_reservation_bytes,0,0)?;
        stats.record_capacity(5,n)?;
    }else{stats.record_capacity(5,high_peak)?;}
    if let Some(s)=subset{s.component_reserved_peak_bytes=s.component_reserved_peak_bytes.max(stats.u_state_peak_capacity_bytes);}
    Ok((high_a,high_b,high_x,handoff_weights))
}

fn elapsed_nanos(start:std::time::Instant)->u64{start.elapsed().as_nanos().min(u64::MAX as u128) as u64}

struct GroupedVBank{c:Vec<Fr>,d:Vec<Fr>,x:Vec<Fr>}

fn grouped_template_capacity_bytes(templates:&Vec<Option<Vec<Term>>>)->Result<usize,String>{
    let mut bytes=templates.capacity().checked_mul(std::mem::size_of::<Option<Vec<Term>>>())
        .ok_or("grouped V template descriptor capacity overflow")?;
    for terms in templates.iter().flatten(){
        bytes=bytes.checked_add(terms.capacity().checked_mul(std::mem::size_of::<Term>())
            .ok_or("grouped V term-template capacity overflow")?)
            .ok_or("grouped V template capacity overflow")?;
    }
    Ok(bytes)
}

fn grouped_v_bank_capacity_bytes(banks:&Vec<GroupedVBank>)->Result<usize,String>{
    let mut bytes=banks.capacity().checked_mul(std::mem::size_of::<GroupedVBank>())
        .ok_or("grouped V bank descriptor capacity overflow")?;
    for bank in banks{
        for capacity in [bank.c.capacity(),bank.d.capacity(),bank.x.capacity()]{
            bytes=bytes.checked_add(capacity.checked_mul(std::mem::size_of::<Fr>())
                .ok_or("grouped V dense capacity overflow")?)
                .ok_or("grouped V dense capacity overflow")?;
        }
    }
    Ok(bytes)
}

fn grouped_v_round_capacity_bytes(rounds:&Vec<Vec<Fr>>)->Result<usize,String>{
    let mut bytes=rounds.capacity().checked_mul(std::mem::size_of::<Vec<Fr>>())
        .ok_or("grouped V round descriptor capacity overflow")?;
    for round in rounds{
        bytes=bytes.checked_add(round.capacity().checked_mul(std::mem::size_of::<Fr>())
            .ok_or("grouped V round capacity overflow")?)
            .ok_or("grouped V round capacity overflow")?;
    }
    Ok(bytes)
}

fn grouped_v_total_capacity_bytes(
    admission:&GroupedVAdmission,templates:&Vec<Option<Vec<Term>>>,banks:&Vec<GroupedVBank>,
    row_weights:&TensorRowWeightLookup<'_>,u_local_weights:&Vec<Fr>,u_copy_weights:&Vec<Fr>,
    group_weight_sums:&Vec<Fr>,local_row_weights:&EqWeightLookup,row_copy_weights:&EqWeightLookup,
    stats:&GroupedVStats,expected_counts_capacity:usize,rounds:&Vec<Vec<Fr>>,v_local_capacity:usize,
    point_capacity:usize,owner_input_capacity:usize,group_scalar_capacity:Option<[usize;2]>,high_capacity:Option<[usize;3]>,
    terminal_scratch_fr_capacity:usize,
)->Result<usize,String>{
    let mut bytes=grouped_template_capacity_bytes(templates)?;
    bytes=bytes.checked_add(stats.private_capacity_reservation_bytes).ok_or("grouped V extra capacity overflow")?;
    bytes=bytes.checked_add(grouped_v_bank_capacity_bytes(banks)?).ok_or("grouped V total capacity overflow")?;
    bytes=bytes.checked_add(admission.group_by_copy.len().checked_mul(std::mem::size_of::<usize>())
        .and_then(|n|n.checked_add(admission.expected_terms_per_group.len().checked_mul(std::mem::size_of::<usize>())?))
        .ok_or("grouped V admission capacity overflow")?).ok_or("grouped V total capacity overflow")?;
    for capacity in [u_local_weights.capacity(),u_copy_weights.capacity(),point_capacity,
        owner_input_capacity,v_local_capacity,terminal_scratch_fr_capacity]{
        bytes=bytes.checked_add(capacity.checked_mul(std::mem::size_of::<Fr>()).ok_or("grouped V scalar capacity overflow")?)
            .ok_or("grouped V total capacity overflow")?;
    }
    bytes=bytes.checked_add(expected_counts_capacity.checked_mul(std::mem::size_of::<usize>())
        .ok_or("grouped V count capacity overflow")?).ok_or("grouped V total capacity overflow")?;
    bytes=bytes.checked_add(group_weight_sums.capacity().checked_mul(std::mem::size_of::<Fr>())
        .ok_or("grouped V group-weight capacity overflow")?).ok_or("grouped V total capacity overflow")?;
    for capacity in [stats.group_owner_counts.capacity(),stats.group_term_counts.capacity()]{
        bytes=bytes.checked_add(capacity.checked_mul(std::mem::size_of::<usize>())
            .ok_or("grouped V statistics capacity overflow")?).ok_or("grouped V total capacity overflow")?;
    }
    for capacity in [stats.group_weight_sums.capacity(),stats.group_d_local_contributions.capacity()]{
        bytes=bytes.checked_add(capacity.checked_mul(std::mem::size_of::<Fr>())
            .ok_or("grouped V statistics capacity overflow")?).ok_or("grouped V total capacity overflow")?;
    }
    bytes=bytes.checked_add(row_weights.capacity_bytes().ok_or("grouped V row-weight capacity overflow")?)
        .and_then(|value|value.checked_add(local_row_weights.capacity_bytes()?))
        .and_then(|value|value.checked_add(row_copy_weights.capacity_bytes()?))
        .and_then(|value|value.checked_add(grouped_v_round_capacity_bytes(rounds).ok()?))
        .ok_or("grouped V weight capacity overflow")?;
    if let Some(capacities)=group_scalar_capacity{
        for capacity in capacities{bytes=bytes.checked_add(capacity.checked_mul(std::mem::size_of::<Fr>())
            .ok_or("grouped V group handoff capacity overflow")?).ok_or("grouped V total capacity overflow")?;}
    }
    if let Some(capacities)=high_capacity{
        for capacity in capacities{bytes=bytes.checked_add(capacity.checked_mul(std::mem::size_of::<Fr>())
            .ok_or("grouped V handoff capacity overflow")?).ok_or("grouped V total capacity overflow")?;}
    }
    Ok(bytes)
}

fn grouped_v_prebind_capacity_bound(input_bits:usize,copy_bits:usize,base_row_bits:usize,
    admission:&GroupedVAdmission)->Option<usize>{
    grouped_v_prebind_capacity_bound_with_policy(input_bits,copy_bits,base_row_bits,admission,GroupedDimensionPolicy::Generic24)
}
fn grouped_v_prebind_capacity_bound_with_policy(input_bits:usize,copy_bits:usize,base_row_bits:usize,
    admission:&GroupedVAdmission,policy:GroupedDimensionPolicy)->Option<usize>{
    if input_bits>24||copy_bits>24||!policy.dimensions_allowed(input_bits,copy_bits,base_row_bits){return None;}
    policy.validate_census(admission).ok()?;
    let width=1usize.checked_shl(input_bits as u32)?;let copies=1usize.checked_shl(copy_bits as u32)?;
    let term_count=admission.expected_terms_per_group.iter().try_fold(0usize,|sum,count|sum.checked_add(*count))?;
    let terms=term_count.checked_mul(std::mem::size_of::<Term>())?;
    let groups=admission.expected_terms_per_group.len();
    let banks=groups.checked_mul(3)?.checked_mul(width)?.checked_mul(std::mem::size_of::<Fr>())?
        .checked_add(groups.checked_mul(std::mem::size_of::<GroupedVBank>())?)?;
    let owner_vectors=width.checked_mul(2)?.checked_add(copies.checked_mul(4)?)?
        .checked_mul(std::mem::size_of::<Fr>())?;
    let row_tables=TensorRowWeightLookup::MAX_LOCAL_TABLE_BYTES
        .checked_add(TensorRowWeightLookup::MAX_SCALE_BYTES)?;
    let small_lookup=base_row_bits.checked_add(copy_bits)?.checked_add(7)?.checked_div(8)?.checked_mul(256)?
        .checked_mul(std::mem::size_of::<Fr>())?.checked_add(64*1024)?;
    let round_count=input_bits.checked_add(copy_bits)?.checked_add(1)?.checked_mul(2)?;
    let round_bound=round_count.checked_mul(std::mem::size_of::<Vec<Fr>>()
        .checked_add(3usize.checked_mul(std::mem::size_of::<Fr>())?)?)?;
    let metadata=copies.checked_mul(std::mem::size_of::<usize>())?
        .checked_add(copies.checked_mul(std::mem::size_of::<usize>())?)?
        .checked_add(groups.checked_mul(4*std::mem::size_of::<usize>()+7*std::mem::size_of::<Fr>())?)?
        .checked_add(round_bound)?;
    let template_descriptors=groups.checked_mul(std::mem::size_of::<Option<Vec<Term>>>())?;
    terms.checked_add(banks)?.checked_add(owner_vectors)?.checked_add(row_tables)?
        .checked_add(small_lookup)?.checked_add(metadata)?.checked_add(template_descriptors)?.checked_add(policy.extra_capacity_bytes())
}

/// Prove one relation whose terms vary by slot while keeping one global input
/// commitment and the resident GKR transcript. `term.row` packs family above
/// `base_row_bits`; the slot coordinate is supplied separately by `copy`.
pub(crate) fn prove(
    input_bits:usize,copy_bits:usize,base_row_bits:usize,family_bits:usize,member_row_bits:&[usize],
    load_copy:impl FnMut(usize)->Result<Vec<Fr>,String>,transcript:&mut Transcript,
    bind:impl FnOnce(&mut Transcript),
    visit_terms:impl FnMut(usize,&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String>,
    wiring:impl Fn(&[Fr],&[Fr],&[Fr])->Result<[Fr;4],String>,
)->Result<(GkrProof,InputClaim),String>{
    prove_inner(input_bits,copy_bits,base_row_bits,family_bits,member_row_bits,None,None,None,MAX_INCREMENTAL_CACHE_STATE_BYTES,false,
        None,None,None,None,None,None,MAX_FIXED_V_COMMON_STATE_BYTES,None,None,None,GroupedDimensionPolicy::Generic24,
        load_copy,transcript,|t|{bind(t);Ok(())},visit_terms,wiring)
}

/// Test-only hook for measuring the same producer with a different incremental
/// cache ceiling. `None` preserves the runtime default exactly.
#[cfg(test)]
pub(crate) fn prove_with_cache_budget_for_test(
    input_bits:usize,copy_bits:usize,base_row_bits:usize,family_bits:usize,member_row_bits:&[usize],
    cache_budget_bytes:Option<usize>,
    load_copy:impl FnMut(usize)->Result<Vec<Fr>,String>,transcript:&mut Transcript,
    bind:impl FnOnce(&mut Transcript),
    visit_terms:impl FnMut(usize,&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String>,
    wiring:impl Fn(&[Fr],&[Fr],&[Fr])->Result<[Fr;4],String>,
)->Result<(GkrProof,InputClaim),String>{
    prove_inner(input_bits,copy_bits,base_row_bits,family_bits,member_row_bits,None,None,None,
        cache_budget_bytes.unwrap_or(MAX_INCREMENTAL_CACHE_STATE_BYTES),
        false,None,None,None,None,None,None,MAX_FIXED_V_COMMON_STATE_BYTES,None,None,None,GroupedDimensionPolicy::Generic24,
        load_copy,transcript,|t|{bind(t);Ok(())},visit_terms,wiring)
}

#[cfg(test)]
pub(crate) fn prove_with_direct_u_prefix_for_test(
    input_bits:usize,copy_bits:usize,base_row_bits:usize,family_bits:usize,member_row_bits:&[usize],
    cache_budget_bytes:Option<usize>,
    load_copy:impl FnMut(usize)->Result<Vec<Fr>,String>,transcript:&mut Transcript,
    bind:impl FnOnce(&mut Transcript),
    visit_terms:impl FnMut(usize,&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String>,
    wiring:impl Fn(&[Fr],&[Fr],&[Fr])->Result<[Fr;4],String>,
)->Result<(GkrProof,InputClaim),String>{
    if cache_budget_bytes!=Some(0){return Err("direct U prefix test hook requires a zero cache budget".into());}
    prove_inner(input_bits,copy_bits,base_row_bits,family_bits,member_row_bits,None,None,None,0,true,
        None,None,None,None,None,None,MAX_FIXED_V_COMMON_STATE_BYTES,None,None,None,GroupedDimensionPolicy::Generic24,
        load_copy,transcript,|t|{bind(t);Ok(())},visit_terms,wiring)
}

#[cfg(test)]
pub(crate) fn prove_with_direct_u_grouped_v_for_test(
    input_bits:usize,copy_bits:usize,base_row_bits:usize,family_bits:usize,member_row_bits:&[usize],
    cache_budget_bytes:Option<usize>,admission:&GroupedVAdmission,
    load_copy:impl FnMut(usize)->Result<Vec<Fr>,String>,transcript:&mut Transcript,
    bind:impl FnOnce(&mut Transcript),
    visit_terms:impl FnMut(usize,&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String>,
    wiring:impl Fn(&[Fr],&[Fr],&[Fr])->Result<[Fr;4],String>,
)->Result<(GkrProof,InputClaim,GroupedVStats),String>{
    if cache_budget_bytes!=Some(0){return Err("grouped V test hook requires a zero cache budget".into());}
    let mut stats=GroupedVStats::default();
    let (proof,claim)=prove_inner(input_bits,copy_bits,base_row_bits,family_bits,member_row_bits,None,None,None,0,true,
        None,None,None,None,None,None,MAX_FIXED_V_COMMON_STATE_BYTES,Some(admission),Some(&mut stats),None,GroupedDimensionPolicy::Generic24,
        load_copy,transcript,|t|{bind(t);Ok(())},visit_terms,wiring)?;
    Ok((proof,claim,stats))
}

/// Private experiment: after baseline admission U consumes the frozen captured
/// relation. The callback is not reread to detect later mutation. The native
/// caller supplies its immutable plan and admitted packed-source boundary.
#[cfg(test)]
pub(crate) fn prove_with_boolean_u_grouped_v_for_test(
    input_bits:usize,copy_bits:usize,base_row_bits:usize,family_bits:usize,member_row_bits:&[usize],
    cache_budget_bytes:Option<usize>,admission:&GroupedVAdmission,
    load_copy:impl FnMut(usize)->Result<Vec<Fr>,String>,transcript:&mut Transcript,
    bind:impl FnOnce(&mut Transcript),
    visit_terms:impl FnMut(usize,&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String>,
    wiring:impl Fn(&[Fr],&[Fr],&[Fr])->Result<[Fr;4],String>,
)->Result<(GkrProof,InputClaim,GroupedVStats,BooleanUPreweightStats),String>{
    prove_boolean_u_grouped_with_policy_for_test(input_bits,copy_bits,base_row_bits,family_bits,member_row_bits,
        cache_budget_bytes,admission,GroupedDimensionPolicy::Generic24,load_copy,transcript,|t|{bind(t);Ok(())},visit_terms,wiring)
}

#[cfg(test)]
fn prove_boolean_u_grouped_with_policy_for_test(
    input_bits:usize,copy_bits:usize,base_row_bits:usize,family_bits:usize,member_row_bits:&[usize],
    cache_budget_bytes:Option<usize>,admission:&GroupedVAdmission,policy:GroupedDimensionPolicy,
    mut load_copy:impl FnMut(usize)->Result<Vec<Fr>,String>,transcript:&mut Transcript,
    bind:impl FnOnce(&mut Transcript)->Result<(),String>,
    visit_terms:impl FnMut(usize,&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String>,
    wiring:impl Fn(&[Fr],&[Fr],&[Fr])->Result<[Fr;4],String>,
)->Result<(GkrProof,InputClaim,GroupedVStats,BooleanUPreweightStats),String>{
    prove_boolean_u_grouped_with_fold_for_test(input_bits,copy_bits,base_row_bits,family_bits,member_row_bits,
        cache_budget_bytes,admission,policy,load_copy,transcript,bind,visit_terms,wiring,BooleanXFoldMode::Legacy,None)
}
#[cfg(test)]
fn prove_boolean_u_grouped_with_fold_for_test(
    input_bits:usize,copy_bits:usize,base_row_bits:usize,family_bits:usize,member_row_bits:&[usize],
    cache_budget_bytes:Option<usize>,admission:&GroupedVAdmission,policy:GroupedDimensionPolicy,
    mut load_copy:impl FnMut(usize)->Result<Vec<Fr>,String>,transcript:&mut Transcript,
    bind:impl FnOnce(&mut Transcript)->Result<(),String>,
    visit_terms:impl FnMut(usize,&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String>,
    wiring:impl Fn(&[Fr],&[Fr],&[Fr])->Result<[Fr;4],String>,
    mode:BooleanXFoldMode,subset:Option<&mut BooleanSubset4Stats>,
)->Result<(GkrProof,InputClaim,GroupedVStats,BooleanUPreweightStats),String>{
    if cache_budget_bytes!=Some(0){return Err("Boolean U test hook requires a zero cache budget".into());}
    if input_bits>24{return Err("Boolean U input dimensions exceed the supported bound".into());}
    let width=1usize.checked_shl(input_bits as u32).ok_or("Boolean U input width overflow")?;
    let checked_loads=std::cell::Cell::new(0usize);let checked_fields=std::cell::Cell::new(0usize);
    let mut checked_loader=|copy|{
        let values=load_copy(copy)?;
        if values.len()!=width||values.capacity()!=width{return Err("Boolean U input length or capacity differs from width".into());}
        if values.iter().any(|value|!value.is_zero()&&!value.is_one()){
            return Err("Boolean U input is not Boolean".into());
        }
        checked_loads.set(checked_loads.get().checked_add(1).ok_or("Boolean U load counter overflow")?);
        checked_fields.set(checked_fields.get().checked_add(values.len()).ok_or("Boolean U field counter overflow")?);
        Ok(values)
    };
    let mut group_stats=GroupedVStats::default();let mut u_stats=BooleanUPreweightStats::default();
    let (proof,claim)=prove_inner_with_fold(input_bits,copy_bits,base_row_bits,family_bits,member_row_bits,None,None,None,0,true,
        None,None,None,None,None,None,MAX_FIXED_V_COMMON_STATE_BYTES,Some(admission),Some(&mut group_stats),Some(&mut u_stats),policy,
        &mut checked_loader,transcript,bind,visit_terms,wiring,mode,subset)?;
    u_stats.boolean_checked_loads=checked_loads.get();u_stats.boolean_checked_fields=checked_fields.get();
    Ok((proof,claim,group_stats,u_stats))
}

/// Closed historical experiment. This grants no generic/native32 admission.
#[cfg(test)]
pub(crate) fn prove_historical_role1_subset4_for_test(
    headers:u64,input_bits:usize,copy_bits:usize,base_row_bits:usize,family_bits:usize,member_row_bits:&[usize],
    cache_budget_bytes:Option<usize>,admission:&GroupedVAdmission,
    load_copy:impl FnMut(usize)->Result<Vec<Fr>,String>,transcript:&mut Transcript,bind:impl FnOnce(&mut Transcript),
    visit_terms:impl FnMut(usize,&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String>,
    wiring:impl Fn(&[Fr],&[Fr],&[Fr])->Result<[Fr;4],String>,
)->Result<(GkrProof,InputClaim,GroupedVStats,BooleanUPreweightStats,BooleanSubset4Stats),String>{
    if !matches!(headers,5|8)|| (input_bits,copy_bits,base_row_bits,family_bits)!=(20,3,19,0)
        ||member_row_bits!=[19]||cache_budget_bytes!=Some(0)||admission.group_by_copy.as_ref()!=[0;8]
        ||admission.expected_terms_per_group.as_ref()!=[396561]{return Err("subset4 closed historical admission".into());}
    if transcript.challenges()!=0{return Err("subset4 transcript already challenged".into());}
    let mut table=BooleanSubset4Stats::default();
    let(p,c,g,u)=prove_boolean_u_grouped_with_fold_for_test(input_bits,copy_bits,base_row_bits,family_bits,member_row_bits,
        cache_budget_bytes,admission,GroupedDimensionPolicy::Generic24,load_copy,transcript,|t|{bind(t);Ok(())},
        visit_terms,wiring,BooleanXFoldMode::Subset4,Some(&mut table))?;
    Ok((p,c,g,u,table))
}

/// A native numeric exception cannot be requested through a generic hook.
/// All source and statement operations come from the same borrowed token.
#[cfg(test)]
pub(crate) fn prove_native_role1_boolean_grouped_for_test(
    admission:&crate::native_prefix_auth_plan::NativeRole1Admission<'_, '_>,transcript:&mut Transcript,
)->Result<(GkrProof,InputClaim,GroupedVStats,BooleanUPreweightStats),String>{
    admission.validate_for_use()?;
    if transcript.challenges()!=0{return Err("native role1 producer transcript already challenged".into());}
    let mut preflight=transcript.clone();admission.bind_statement(&mut preflight)?;
    if preflight.challenges()!=0{return Err("native role1 preflight binding sampled a challenge".into());}
    drop(preflight);
    let policy=GroupedDimensionPolicy::NativeRole1Exact{extra_capacity_bytes:admission.extra_live_capacity_bytes()?};
    policy.validate_route(20,12,19,0,&[19],0,true,false,true,Some(admission.grouped_admission()))?;
    prove_boolean_u_grouped_with_policy_for_test(20,12,19,0,&[19],Some(0),admission.grouped_admission(),policy,
        |owner|admission.load_owner(owner),transcript,|t|admission.bind_statement(t),
        |owner,sink|admission.visit_owner_terms(owner,sink),|r,u,v|admission.coefficients(r,u,v))
}

#[cfg(test)]
pub(crate) fn prove_native_role3_boolean_grouped_for_test(
    admission:&crate::native_prefix_auth_plan::NativeRole3Admission<'_, '_>,transcript:&mut Transcript,
)->Result<(GkrProof,InputClaim,GroupedVStats,BooleanUPreweightStats),String>{
    admission.validate_for_use()?;
    if transcript.challenges()!=0{return Err("native role3 producer transcript already challenged".into());}
    let policy=GroupedDimensionPolicy::NativeRole3Exact{extra_capacity_bytes:admission.extra_live_capacity_bytes()};
    policy.validate_route(13,12,14,0,&[14],0,true,false,true,Some(admission.grouped_admission()))?;
    let prebound=boolean_u_prebind_capacity_bound_with_policy(13,12,14,admission.grouped_admission(),policy)
        .ok_or("native role3 checked preflight overflow")?;
    if prebound>MAX_INCREMENTAL_CACHE_STATE_BYTES{return Err("native role3 scoped preflight exceeds512MiB".into());}
    // One fallible prepared binding, installed exactly once before output challenges.
    let prepared=admission.prepare_binding(transcript)?;
    native_role3_transaction(transcript,|working|{
        let observer=NativeRole3ObserverScope::begin(admission.started())?;
        let result=prove_boolean_u_grouped_with_policy_for_test(13,12,14,0,&[14],Some(0),admission.grouped_admission(),policy,
            |owner|admission.load_owner(owner),working,move|t|{*t=prepared;Ok(())},
            |owner,sink|admission.visit_owner_terms(owner,sink),|r,u,v|admission.coefficients(r,u,v))?;
        // Drop clears the fixed observer on error or unwind. I/O errors are
        // propagated before this transaction may commit the caller.
        let marks=observer.finish()?;admission.complete(marks,&result.2,&result.3)?;Ok(result)
    })
}

/// Historical authority is computed by the owning verifier context, never by a
/// caller-selected numeric policy or a Native diagnostic prefix.
#[cfg(test)]
pub(crate) fn prove_historical50_grouped_for_test(
    admission:&crate::historical_prefix_proof::Historical50GroupedAdmission<'_, '_>,transcript:&mut Transcript,
)->Result<(GkrProof,InputClaim,GroupedVStats,BooleanUPreweightStats),String>{
    admission.validate_for_use()?;
    if transcript.challenges()!=0||transcript.raw_queries()!=0{return Err("historical50 grouped prefix advanced".into());}
    let(role,bits,rows)=match admission.role(){3=>(3,13,14),1=>(1,20,19),_=>return Err("historical50 grouped role".into())};
    let extra_capacity_bytes=admission.extra_live_capacity_bytes();
    let policy=if role==3{GroupedDimensionPolicy::Historical50Role3{extra_capacity_bytes}}
        else{GroupedDimensionPolicy::Historical50Role1{extra_capacity_bytes}};
    policy.validate_route(bits,12,rows,0,&[rows],0,true,false,true,Some(admission.grouped_admission()))?;
    let preflight=historical50_grouped_preflight_for_test(admission)?;
    native_role3_transaction(transcript,|working|{
        let result=prove_boolean_u_grouped_with_policy_for_test(bits,12,rows,0,&[rows],Some(0),admission.grouped_admission(),policy,
            |owner|admission.load_owner(owner),working,|t|admission.bind_statement(t),
            |owner,sink|admission.visit_owner_terms(owner,sink),|r,u,v|admission.coefficients(r,u,v))?;
        admission.complete()?;
        historical50_observed_bounds([result.3.u_state_peak_capacity_bytes,result.2.grouped_state_peak_capacity_bytes],preflight)?;Ok(result)
    })
}
#[cfg(test)]
pub(crate) fn historical50_grouped_preflight_for_test(
    admission:&crate::historical_prefix_proof::Historical50GroupedAdmission<'_, '_>)->Result<[usize;2],String>{
    admission.validate_for_use()?;let(bits,rows)=match admission.role(){3=>(13,14),1=>(20,19),_=>return Err("historical50 grouped role".into())};
    let extra_capacity_bytes=admission.extra_live_capacity_bytes();
    let policy=if admission.role()==3{GroupedDimensionPolicy::Historical50Role3{extra_capacity_bytes}}
        else{GroupedDimensionPolicy::Historical50Role1{extra_capacity_bytes}};
    historical50_grouped_bounds(bits,rows,admission.grouped_admission(),policy)
}
#[cfg(test)]
fn historical50_grouped_bounds(bits:usize,rows:usize,a:&GroupedVAdmission,policy:GroupedDimensionPolicy)->Result<[usize;2],String>{
    let u=boolean_u_prebind_capacity_bound_with_policy(bits,12,rows,a,policy).ok_or("historical50 U preflight overflow")?;
    let v=grouped_v_prebind_capacity_bound_with_policy(bits,12,rows,a,policy)
        .and_then(|n|n.checked_add(boolean_u_v_reservation(1usize<<bits)?)).ok_or("historical50 V preflight overflow")?;
    if u>MAX_INCREMENTAL_CACHE_STATE_BYTES||v>MAX_INCREMENTAL_CACHE_STATE_BYTES{return Err("historical50 grouped preflight exceeds512MiB".into());}Ok([u,v])
}
#[cfg(test)]
fn historical50_observed_bounds(actual:[usize;2],bound:[usize;2])->Result<(),String>{
    if bound.iter().any(|b|*b>MAX_INCREMENTAL_CACHE_STATE_BYTES)||actual.iter().zip(bound).any(|(a,b)|*a>b){
        return Err("historical50 grouped actual exceeds preflight".into());}Ok(())
}

// Called by the single Historical50 ordinary selector. These exercise the
// actual Legacy/None guards without constructing a native witness or proof.
#[cfg(test)]
pub(crate) fn historical50_resource_controls_for_test()->Result<(),String>{
    for role in [3,1]{
        let(bits,rows,terms)=if role==3{(13,14,vec![288158])}else{(20,19,vec![396561,388369])};
        let mut map=vec![0usize;4096];if role==1{map[3072]=1;}
        let a=GroupedVAdmission::try_new(12,&map,&terms)?;
        let policy=|extra_capacity_bytes|if role==3{GroupedDimensionPolicy::Historical50Role3{extra_capacity_bytes}}
            else{GroupedDimensionPolicy::Historical50Role1{extra_capacity_bytes}};
        policy(0).validate_route(bits,12,rows,0,&[rows],0,true,false,true,Some(&a))?;
        for fault in 0..8{
            let(mut b,mut c,mut r,mut f,mut members,mut cache,mut direct,mut boolean)=(bits,12,rows,0,vec![rows],0,true,true);
            match fault{0=>b-=1,1=>c-=1,2=>r-=1,3=>f=1,4=>members[0]-=1,5=>cache=1,6=>direct=false,_=>boolean=false}
            if policy(0).validate_route(b,c,r,f,&members,cache,direct,false,boolean,Some(&a)).is_ok(){return Err("historical50 route mutant accepted".into());}
        }
        for fault in 0..3{let mut bad=a.clone();match fault{
            0=>bad.group_by_copy[3072]=if role==3{1}else{0},1=>bad.expected_terms_per_group[0]+=1,
            _=>bad.group_by_copy=vec![0;4095].into_boxed_slice()}
            if policy(0).validate_census(&bad).is_ok(){return Err("historical50 census mutant accepted".into());}}
        let u0=boolean_u_prebind_capacity_bound_with_policy(bits,12,rows,&a,policy(0)).ok_or("historical50 U preflight golden")?;
        let v0=grouped_v_prebind_capacity_bound_with_policy(bits,12,rows,&a,policy(0)).ok_or("historical50 V preflight golden")?;
        if boolean_u_prebind_capacity_bound_with_policy(bits,12,rows,&a,policy(128))!=u0.checked_add(128)
            ||grouped_v_prebind_capacity_bound_with_policy(bits,12,rows,&a,policy(128))!=v0.checked_add(128){return Err("historical50 extra charge not additive".into());}
        let bounds=historical50_grouped_bounds(bits,rows,&a,policy(128))?;historical50_observed_bounds(bounds,bounds)?;
        for side in 0..2{let mut bad=bounds;bad[side]+=1;
            if historical50_observed_bounds(bad,bounds).err().as_deref()!=Some("historical50 grouped actual exceeds preflight"){
                return Err("historical50 observed one-over attribution".into());}}
        if historical50_grouped_bounds(bits,rows,&a,policy(usize::MAX)).err().as_deref()!=Some("historical50 U preflight overflow"){
            return Err("historical50 isolated bound overflow".into());}
        let activity=std::cell::Cell::new(0usize);let mut t=Transcript::new(b"historical50-prebind-capacity-control");let before=t.clone();
        let result=prove_boolean_u_grouped_with_policy_for_test(bits,12,rows,0,&[rows],Some(0),&a,policy(MAX_INCREMENTAL_CACHE_STATE_BYTES+1),
            |_|{activity.set(activity.get()+1);Err("historical50 unexpected loader".into())},&mut t,
            |_|{activity.set(activity.get()+1);Err("historical50 unexpected binder".into())},
            |_,_|{activity.set(activity.get()+1);Err("historical50 unexpected census".into())},
            |_,_,_|{activity.set(activity.get()+1);Err("historical50 unexpected wiring".into())});
        if result.err().as_deref()!=Some("Boolean U checked capacity bound exceeds 512 MiB before binding")||activity.get()!=0
            ||t.bytes_absorbed()!=before.bytes_absorbed()||t.challenges()!=0||t.raw_queries()!=0
            ||t.clone().challenge_scalar(b"control-next")!=before.clone().challenge_scalar(b"control-next"){
            return Err("historical50 prebind guard attribution".into());}
    }
    let mut stats=BooleanUPreweightStats{u_preflight_capacity_bound_bytes:64,..Default::default()};
    stats.record_capacity(0,64)?;
    if stats.record_capacity(0,65).is_ok()||stats.record_capacity(6,0).is_ok(){return Err("historical50 actual inventory guard".into());}
    // A four-owner differential reaches the very same Legacy/None body. The
    // explicit zero occurrence tests census preservation, not only residuals.
    let templates:Vec<Vec<Term>>=(0..2).map(|g|vec![
        Term{row:0,gate:crate::gkr::Gate{left:0,right:1,c0:Fr::zero(),c1:Fr::from(g+1u64),c2:Fr::one(),c3:Fr::zero()}},
        Term{row:1,gate:crate::gkr::Gate{left:2,right:3,c0:Fr::zero(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}}]).collect();
    let map=[0usize,1,0,1];let toy=GroupedVAdmission::try_new(2,&map,&[2,2])?;let input=vec![Fr::zero();16];
    let mut global=Vec::new();for owner in 0..4{for term in &templates[map[owner]]{let mut t=term.clone();
        t.row+=owner*2;t.gate.left+=owner*4;t.gate.right+=owner*4;global.push(t);}}
    let circuit=crate::sparse::Circuit{input_len:16,row_count:8,terms:global};
    let shape=crate::sparse::validate(&circuit,0).map_err(|e|e.to_string())?;
    let bind=|t:&mut Transcript|t.append_bytes(b"historical50-small-reference",b"same-prefix");
    let start=||Transcript::new(b"historical50-small-reference");
    let mut resident=start();let(reference,reference_claim)=crate::sparse::prove_with_binding(&circuit,&input,0,&mut resident,bind).map_err(|e|e.to_string())?;
    let attempt=|fault:u8,t:&mut Transcript|native_role3_transaction(t,|working|{
        prove_boolean_u_grouped_with_policy_for_test(2,2,1,0,&[1],Some(0),&toy,GroupedDimensionPolicy::Generic24,
            |owner|{let mut values=input[owner*4..(owner+1)*4].to_vec();
                if fault==4&&owner==0{values[0]=Fr::from(2u64);}Ok(values)},working,|t|{bind(t);
                    if fault==5{Err("historical50 isolated binder failure".into())}else{Ok(())}},
            |owner,sink|{let terms=&templates[map[owner]];
                for(i,term)in terms.iter().enumerate(){if fault==1&&owner==2&&i==1{continue;}
                    let mut term=term.clone();if fault==3&&owner==2&&i==0{term.gate.c1+=Fr::one();}sink(term)?;}
                if fault==2&&owner==2{sink(terms[1].clone())?;}Ok(())},
            |r,u,v|crate::sparse::wiring(&circuit,&shape,r,u,v).map_err(|e|e.to_string()))
    });
    let mut actual=start();let(proof,claim,_,_)=attempt(0,&mut actual)?;
    if gkr::encode_proof(&proof)?!=gkr::encode_proof(&reference)?||claim!=reference_claim
        ||actual.clone().challenge_scalar(b"next")!=resident.clone().challenge_scalar(b"next"){
        return Err("historical50 small resident differential".into());}
    for(fault,error)in[(1,"grouped V owner census differs from its admitted topology"),
        (2,"grouped V owner exceeded its admitted topology count"),(3,"grouped V normalized term differs within its admitted topology"),
        (4,"Boolean U input is not Boolean"),(5,"historical50 isolated binder failure")]{let mut t=start();let before=t.clone();
        if attempt(fault,&mut t).err().as_deref()!=Some(error)||t.challenges()!=0||t.raw_queries()!=0
            ||t.bytes_absorbed()!=before.bytes_absorbed()||t.clone().challenge_scalar(b"next")!=before.clone().challenge_scalar(b"next"){
            return Err("historical50 isolated grouped fault attribution".into());}}
    Ok(())
}

#[cfg(test)]
fn native_role3_transaction<T>(t:&mut Transcript,run:impl FnOnce(&mut Transcript)->Result<T,String>)->Result<T,String>{
    let mut working=t.clone();let result=run(&mut working)?;*t=working;Ok(result)
}

#[cfg(test)]
pub(crate) fn prove_checked(
    input_bits:usize,copy_bits:usize,base_row_bits:usize,family_bits:usize,member_row_bits:&[usize],
    expected_resident_rounds:Option<&[Vec<Fr>]>,
    expected_resident_handoff:Option<(&[Fr],&[Fr],&[Fr])>,
    expected_resident_output_point:Option<&[Fr]>,
    load_copy:impl FnMut(usize)->Result<Vec<Fr>,String>,transcript:&mut Transcript,
    bind:impl FnOnce(&mut Transcript),
    visit_terms:impl FnMut(usize,&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String>,
    wiring:impl Fn(&[Fr],&[Fr],&[Fr])->Result<[Fr;4],String>,
)->Result<(GkrProof,InputClaim),String>{
    prove_inner(input_bits,copy_bits,base_row_bits,family_bits,member_row_bits,expected_resident_rounds,
        expected_resident_handoff,expected_resident_output_point,MAX_INCREMENTAL_CACHE_STATE_BYTES,false,
        None,None,None,None,None,None,MAX_FIXED_V_COMMON_STATE_BYTES,None,None,None,GroupedDimensionPolicy::Generic24,
        load_copy,transcript,|t|{bind(t);Ok(())},visit_terms,wiring)
}

fn prove_inner(
    input_bits:usize,copy_bits:usize,base_row_bits:usize,family_bits:usize,member_row_bits:&[usize],
    expected_resident_rounds:Option<&[Vec<Fr>]>,
    expected_resident_handoff:Option<(&[Fr],&[Fr],&[Fr])>,
    expected_resident_output_point:Option<&[Fr]>,cache_budget_bytes:usize,direct_u_prefix:bool,
    fixed_v:Option<&FixedCoreVTemplate<'_>>,mut fixed_workspace:Option<&mut FixedVWorkspace>,
    streamed_stats:Option<&std::cell::Cell<usize>>,template_stats:Option<&std::cell::Cell<usize>>,
    capacity_stats:Option<&std::cell::Cell<usize>>,
    u_stats:Option<&std::cell::Cell<FixedCoreUProofStats>>,
    u_capacity_budget:usize,grouped_v_admission:Option<&GroupedVAdmission>,mut grouped_v_stats:Option<&mut GroupedVStats>,
    mut boolean_u_stats:Option<&mut BooleanUPreweightStats>,
    dimension_policy:GroupedDimensionPolicy,
    mut load_copy:impl FnMut(usize)->Result<Vec<Fr>,String>,transcript:&mut Transcript,
    bind:impl FnOnce(&mut Transcript)->Result<(),String>,
    mut visit_terms:impl FnMut(usize,&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String>,
    wiring:impl Fn(&[Fr],&[Fr],&[Fr])->Result<[Fr;4],String>,
)->Result<(GkrProof,InputClaim),String>{
    prove_inner_with_fold(input_bits,copy_bits,base_row_bits,family_bits,member_row_bits,expected_resident_rounds,
        expected_resident_handoff,expected_resident_output_point,cache_budget_bytes,direct_u_prefix,fixed_v,fixed_workspace,
        streamed_stats,template_stats,capacity_stats,u_stats,u_capacity_budget,grouped_v_admission,grouped_v_stats,
        boolean_u_stats,dimension_policy,load_copy,transcript,bind,visit_terms,wiring,BooleanXFoldMode::Legacy,None)
}
fn prove_inner_with_fold(
    input_bits:usize,copy_bits:usize,base_row_bits:usize,family_bits:usize,member_row_bits:&[usize],
    expected_resident_rounds:Option<&[Vec<Fr>]>,expected_resident_handoff:Option<(&[Fr],&[Fr],&[Fr])>,
    expected_resident_output_point:Option<&[Fr]>,cache_budget_bytes:usize,direct_u_prefix:bool,
    fixed_v:Option<&FixedCoreVTemplate<'_>>,mut fixed_workspace:Option<&mut FixedVWorkspace>,
    streamed_stats:Option<&std::cell::Cell<usize>>,template_stats:Option<&std::cell::Cell<usize>>,
    capacity_stats:Option<&std::cell::Cell<usize>>,u_stats:Option<&std::cell::Cell<FixedCoreUProofStats>>,
    u_capacity_budget:usize,grouped_v_admission:Option<&GroupedVAdmission>,mut grouped_v_stats:Option<&mut GroupedVStats>,
    mut boolean_u_stats:Option<&mut BooleanUPreweightStats>,dimension_policy:GroupedDimensionPolicy,
    mut load_copy:impl FnMut(usize)->Result<Vec<Fr>,String>,transcript:&mut Transcript,
    bind:impl FnOnce(&mut Transcript)->Result<(),String>,
    mut visit_terms:impl FnMut(usize,&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String>,
    wiring:impl Fn(&[Fr],&[Fr],&[Fr])->Result<[Fr;4],String>,
    mode:BooleanXFoldMode,mut subset:Option<&mut BooleanSubset4Stats>,
)->Result<(GkrProof,InputClaim),String>{
    if (mode==BooleanXFoldMode::Subset4)!=subset.is_some(){return Err("subset4 mode/statistics mismatch".into());}
    let u_plan=if mode==BooleanXFoldMode::Subset4{
        if boolean_u_stats.is_none(){return Err("subset4 requires Boolean U".into());}
        let a=grouped_v_admission.ok_or("subset4 grouped admission missing")?;
        let p=UCapacityPlan::new(input_bits,copy_bits,base_row_bits,a,dimension_policy)?;
        let extra=subset4_extra_bound(input_bits).ok_or("subset4 preflight arithmetic")?;
        let s=subset.as_deref_mut().ok_or("subset4 statistics missing")?;
        s.extra_reserved_bytes=extra;s.preflight_bound_bytes=p.component;
        // Conservative reservation covers baseline/row/owner/V phases before
        // their allocations. The table itself exists only during local U.
        s.component_reserved_peak_bytes=p.component;
        Some(p)
    }else{None};
    phase_mark("baseline_start")?;
    dimension_policy.validate_route(input_bits,copy_bits,base_row_bits,family_bits,member_row_bits,cache_budget_bytes,
        direct_u_prefix,fixed_v.is_some(),boolean_u_stats.is_some(),grouped_v_admission)?;
    if let Some(stats)=grouped_v_stats.as_deref_mut(){stats.private_capacity_reservation_bytes=dimension_policy.extra_capacity_bytes();}
    let grouped_baseline_started=grouped_v_admission.map(|_|std::time::Instant::now());
    if grouped_v_admission.is_some()&&(family_bits!=0||input_bits>24||copy_bits>24
        ||!dimension_policy.dimensions_allowed(input_bits,copy_bits,base_row_bits)){
        return Err("grouped V dimensions exceed the supported bound before allocation".into());
    }
    let width=1usize.checked_shl(input_bits as u32).ok_or("local input width overflow")?;
    let copies=1usize.checked_shl(copy_bits as u32).ok_or("slot count overflow")?;
    let row_bits=base_row_bits.checked_add(copy_bits).and_then(|x|x.checked_add(family_bits)).ok_or("global row bits overflow")?;
    let row_count=1usize.checked_shl(row_bits as u32).ok_or("global row count overflow")?;
    let _total_input=width.checked_mul(copies).ok_or("global input width overflow")?;
    if member_row_bits.is_empty()||member_row_bits.len()>1usize<<family_bits
        ||member_row_bits.iter().any(|bits|*bits>base_row_bits){return Err(GkrError::InvalidInputWidth.to_string());}
    if direct_u_prefix&&fixed_v.is_some(){return Err("direct U prefix is restricted to the generic streamed path".into());}
    if let Some(stats)=boolean_u_stats.as_deref_mut(){
        let admission=grouped_v_admission.ok_or("Boolean U requires grouped V admission")?;
        if !direct_u_prefix||cache_budget_bytes!=0||family_bits!=0||member_row_bits!=[base_row_bits]{
            return Err("Boolean U requires direct U, zero cache and one full-width family".into());
        }
        let bound=boolean_u_prebind_capacity_bound_with_policy(input_bits,copy_bits,base_row_bits,admission,dimension_policy)
            .ok_or("Boolean U checked prebind capacity overflow or dimensions")?;
        if u_plan.is_none()&&bound>MAX_INCREMENTAL_CACHE_STATE_BYTES{return Err("Boolean U checked capacity bound exceeds 512 MiB before binding".into());}
        let v_bound=grouped_v_prebind_capacity_bound_with_policy(input_bits,copy_bits,base_row_bits,admission,dimension_policy)
            .and_then(|n|n.checked_add(boolean_u_v_reservation(width)?))
            .and_then(|n|n.checked_add(if subset.is_some(){subset4_metadata_bytes()?}else{0}))
            .ok_or("Boolean U grouped V prebind capacity overflow")?;
        if v_bound>MAX_INCREMENTAL_CACHE_STATE_BYTES{return Err("Boolean U grouped V capacity exceeds 512 MiB before binding".into());}
        if subset.as_deref().is_some_and(|s|v_bound>s.preflight_bound_bytes){return Err("subset4 V exceeds reserved component".into());}
        stats.u_preflight_capacity_bound_bytes=bound;
        if let Some(s)=subset.as_deref(){stats.u_preflight_capacity_bound_bytes=s.preflight_bound_bytes;}
        stats.preweight_entry_size_bytes=std::mem::size_of::<BooleanUPreweight>();
    }
    let mut grouped_templates=if let Some(admission)=grouped_v_admission{
        if !direct_u_prefix||fixed_v.is_some()||family_bits!=0||member_row_bits!=[base_row_bits]
            ||admission.group_by_copy.len()!=copies||!dimension_policy.dimensions_allowed(input_bits,copy_bits,base_row_bits){
            return Err("grouped V requires direct U, one family, exact admitted copies, and dimensions within 24".into());
        }
        if grouped_v_prebind_capacity_bound_with_policy(input_bits,copy_bits,base_row_bits,admission,dimension_policy)
            .is_none_or(|bytes|bytes>MAX_INCREMENTAL_CACHE_STATE_BYTES){
            return Err("grouped V checked capacity bound exceeds 512 MiB before transcript binding".into());
        }
        if grouped_v_stats.is_none(){return Err("grouped V statistics sink is missing".into());}
        if let Some(p)=&u_plan{p.before(UPhase::Baseline,0,ULive::default())?;}
        let mut templates=Vec::new();templates.try_reserve_exact(admission.expected_terms_per_group.len())
            .map_err(|_|"grouped V template table reservation failed")?;
        if u_plan.is_some()&&templates.capacity()!=admission.expected_terms_per_group.len(){return Err("capacity46 template descriptor drift".into());}
        templates.resize_with(admission.expected_terms_per_group.len(),||None);
        if let Some(stats)=grouped_v_stats.as_deref_mut(){
            stats.group_count=admission.expected_terms_per_group.len();
            stats.group_owner_counts=vec![0;stats.group_count];
            stats.group_term_counts=admission.expected_terms_per_group.to_vec();
        }
        for group in admission.group_by_copy.iter().copied(){
            let count=grouped_v_stats.as_deref_mut().ok_or("grouped V statistics sink is missing")?;
            count.group_owner_counts[group]=count.group_owner_counts[group].checked_add(1).ok_or("grouped V owner count overflow")?;
        }
        Some(templates)
    }else{
        if grouped_v_stats.is_some(){return Err("grouped V statistics were supplied without an admission".into());}
        None
    };
    if let Some(template)=fixed_v{
        if input_bits!=template.input_bits||copy_bits!=template.owner_bits||base_row_bits!=template.row_bits
            ||family_bits!=0||member_row_bits!=[template.row_bits]||width!=template.width
            ||copies!=template.owners||template.rows.checked_mul(template.owners)!=Some(row_count){
            return Err("fixed V template dimensions do not match the producer".into());
        }
        if fixed_workspace.is_none(){return Err("fixed V workspace was not reserved before producer callbacks".into());}
    }

    // The baseline pass both checks every residual and freezes each slot's
    // expected term count for all later replays.
    let mut expected_counts=Vec::with_capacity(copies);
    if let Some(p)=&u_plan{p.baseline_actual(grouped_templates.as_ref().ok_or("capacity46 templates missing")?,&expected_counts,
        grouped_v_stats.as_deref().ok_or("capacity46 statistics missing")?)?;}
    for copy in 0..copies{
        if let Some(p)=&u_plan{p.before(UPhase::Baseline,0,ULive::default())?;}
        let local_input=read_copy(&mut load_copy,copy,width)?;
        let mut previous_row=None;let mut row_residual=Fr::zero();let mut count=0usize;
        visit_terms(copy,&mut |term|{
            count=count.checked_add(1).ok_or("slot term count overflow")?;
            if let Some(counter)=streamed_stats{counter.set(counter.get().checked_add(1).ok_or("streamed term callback count overflow")?);}
            let family=term.row>>base_row_bits;let local_row=term.row&((1usize<<base_row_bits)-1);
            if let Some(admission)=grouped_v_admission{
                if term.gate.left>=width||term.gate.right>=width{return Err("grouped V rejects sentinel or out-of-range endpoints".into());}
                let group=admission.group_by_copy[copy];let expected=admission.expected_terms_per_group[group];
                if count>expected{return Err("grouped V owner exceeded its admitted topology count".into());}
                let templates=grouped_templates.as_mut().ok_or("grouped V templates are missing")?;
                if templates[group].is_none(){
                    if let Some(p)=&u_plan{p.before(UPhase::Baseline,0,ULive::default())?;}
                    let mut template=Vec::new();template.try_reserve_exact(expected)
                        .map_err(|_|"grouped V term-template reservation failed")?;
                    if u_plan.is_some()&&template.capacity()!=expected{return Err("capacity46 term template capacity drift".into());}
                    templates[group]=Some(template);
                }
                let template=templates[group].as_mut().ok_or("grouped V term template is missing")?;
                if template.len()+1==count{template.push(term.clone());}
                else if template.get(count-1)!=Some(&term){return Err("grouped V normalized term differs within its admitted topology".into());}
                if let Some(stats)=grouped_v_stats.as_deref_mut(){stats.baseline_term_callbacks=stats.baseline_term_callbacks
                    .checked_add(1).ok_or("grouped V baseline term count overflow")?;}
            }
            let left_anchor=term.gate.left==width&&term.gate.c1.is_zero()&&term.gate.c3.is_zero();
            let right_anchor=term.gate.right==width&&term.gate.c2.is_zero()&&term.gate.c3.is_zero();
            if family>=member_row_bits.len()||local_row>=1usize<<member_row_bits[family]
                ||(term.gate.left>=width&&!left_anchor)||(term.gate.right>=width&&!right_anchor){return Err(GkrError::InvalidWireIndex.to_string());}
            if let Some(previous)=previous_row{
                if term.row<previous{return Err("slot term rows are not emitted in canonical nondecreasing order".into());}
                if term.row!=previous{
                    if !row_residual.is_zero(){return Err(GkrError::NonzeroOutput.to_string());}
                    row_residual=Fr::zero();previous_row=Some(term.row);
                }
            }else{previous_row=Some(term.row);}
            let mut local_gate=term.gate.clone();if left_anchor{local_gate.left=0;}if right_anchor{local_gate.right=0;}
            row_residual+=local_gate.evaluate(&local_input);Ok(())
        })?;
        if !row_residual.is_zero(){return Err(GkrError::NonzeroOutput.to_string());}
        if let Some(admission)=grouped_v_admission{
            let group=admission.group_by_copy[copy];let expected=admission.expected_terms_per_group[group];
            if count!=expected||grouped_templates.as_ref().and_then(|templates|templates[group].as_ref())
                .is_none_or(|template|template.len()!=expected){
                return Err("grouped V owner census differs from its admitted topology".into());
            }
            let template_bytes=grouped_template_capacity_bytes(grouped_templates.as_ref().ok_or("grouped V templates are missing")?)?;
            let stats_bytes=grouped_v_stats.as_deref().map(|stats|{
                stats.group_owner_counts.capacity().checked_mul(std::mem::size_of::<usize>())?
                    .checked_add(stats.group_term_counts.capacity().checked_mul(std::mem::size_of::<usize>())?)?
                    .checked_add(stats.group_weight_sums.capacity().checked_mul(std::mem::size_of::<Fr>())?)?
                    .checked_add(stats.group_d_local_contributions.capacity().checked_mul(std::mem::size_of::<Fr>())?)
            }).flatten().ok_or("grouped V statistics capacity overflow")?;
            let admission_bytes=admission.group_by_copy.len().checked_mul(std::mem::size_of::<usize>())
                .and_then(|bytes|bytes.checked_add(admission.expected_terms_per_group.len().checked_mul(std::mem::size_of::<usize>())?))
                .ok_or("grouped V admission capacity overflow")?;
            let baseline_scratch=local_input.capacity().checked_mul(std::mem::size_of::<Fr>())
                .and_then(|bytes|bytes.checked_add(template_bytes))
                .and_then(|bytes|bytes.checked_add(expected_counts.capacity().checked_mul(std::mem::size_of::<usize>())?))
                .and_then(|bytes|bytes.checked_add(stats_bytes))
                .and_then(|bytes|bytes.checked_add(admission_bytes))
                .ok_or("grouped V baseline capacity overflow")?;
            if baseline_scratch>MAX_INCREMENTAL_CACHE_STATE_BYTES{return Err("grouped V baseline state exceeds 512 MiB".into());}
            if let Some(stats)=boolean_u_stats.as_deref_mut(){
                let live=baseline_scratch.checked_add(boolean_u_loader_scratch_bound(width)
                    .ok_or("Boolean U baseline loader capacity overflow")?)
                    .and_then(|n|n.checked_add(std::mem::size_of::<BooleanUPreweightStats>()))
                    .and_then(|n|n.checked_add(dimension_policy.extra_capacity_bytes()))
                    .ok_or("Boolean U baseline capacity overflow")?;
                let live=if let Some(p)=&u_plan{
                    p.baseline_actual(grouped_templates.as_ref().ok_or("capacity46 templates missing")?,&expected_counts,
                        grouped_v_stats.as_deref().ok_or("capacity46 statistics missing")?)?;
                    let n=u_sum(&[live,UCapacityPlan::metadata()?,subset4_metadata_bytes().ok_or("capacity46 metadata")?])?;
                    p.actual(UPhase::Baseline,0,n,dimension_policy.extra_capacity_bytes(),0,0)?;n
                }else{live};
                stats.record_capacity(0,live)?;
            }
            if let Some(stats)=grouped_v_stats.as_deref_mut(){
                stats.template_term_count=admission.expected_terms_per_group.iter().try_fold(0usize,|sum,count|sum.checked_add(*count))
                    .ok_or("grouped V template term count overflow")?;
                stats.template_capacity_bytes=template_bytes;
                stats.grouped_state_peak_capacity_bytes=stats.grouped_state_peak_capacity_bytes.max(baseline_scratch);
            }
        }
        expected_counts.push(count);
    }
    if let Some(started)=grouped_baseline_started{if let Some(stats)=grouped_v_stats.as_deref_mut(){stats.baseline_elapsed_ns=elapsed_nanos(started);}}
    phase_mark("baseline_done")?;
    let mut walk=|copy:usize,sink:&mut dyn FnMut(Term)->Result<(),String>|->Result<(),String>{
        let mut count=0usize;
        visit_terms(copy,&mut |term|{
            count=count.checked_add(1).ok_or("slot term count overflow")?;
            if let Some(counter)=streamed_stats{counter.set(counter.get().checked_add(1).ok_or("streamed term callback count overflow")?);}
            if count>expected_counts[copy]{return Err("slot term source exceeded baseline count".into());}
            let family=term.row>>base_row_bits;let local_row=term.row&((1usize<<base_row_bits)-1);
            let left_anchor=term.gate.left==width&&term.gate.c1.is_zero()&&term.gate.c3.is_zero();
            let right_anchor=term.gate.right==width&&term.gate.c2.is_zero()&&term.gate.c3.is_zero();
            if family>=member_row_bits.len()||local_row>=1usize<<member_row_bits[family]
                ||(term.gate.left>=width&&!left_anchor)||(term.gate.right>=width&&!right_anchor){return Err(GkrError::InvalidWireIndex.to_string());}
            sink(term)
        })?;
        if count!=expected_counts[copy]{return Err("slot term source count changed between passes".into());}Ok(())
    };

    if let Some(p)=&u_plan{p.before(UPhase::RowBuild,0,ULive::default())?;}
    bind(transcript)?;
    let r=gkr::output_point(row_count,transcript);
    if u_plan.as_ref().is_some_and(|_|r.capacity()>2*(base_row_bits+copy_bits+1)){
        return Err("capacity46 output point capacity drift".into());
    }
    if let Some(expected)=expected_resident_output_point{
        assert_eq!(r.as_slice(),expected,"slot tensor output point differs from resident transcript");
    }
    gkr::append_usize(transcript,b"gkr-layer-index",0);
    if let Some(stats)=boolean_u_stats.as_deref_mut(){
        let row_peak=boolean_u_row_preparation_capacity_bytes(
            grouped_templates.as_ref().ok_or("Boolean U row-preparation templates missing")?,
            grouped_v_admission.ok_or("Boolean U row-preparation admission missing")?,
            grouped_v_stats.as_deref().ok_or("Boolean U row-preparation statistics missing")?,
            expected_counts.capacity(),r.capacity(),width).ok_or("Boolean U row-preparation capacity overflow")?;
        let row_peak=if let Some(p)=&u_plan{
            let n=u_sum(&[row_peak,UCapacityPlan::metadata()?,subset4_metadata_bytes().ok_or("capacity46 metadata")?])?;
            p.actual(UPhase::RowBuild,0,n,dimension_policy.extra_capacity_bytes(),0,0)?;n
        }else{row_peak};
        stats.record_capacity(1,row_peak)?;
    }
    let row_weight_lookup=TensorRowWeightLookup::new(&r,copy_bits,base_row_bits,member_row_bits);
    if let Some(p)=&u_plan{
        p.lookup_actual(&row_weight_lookup,None)?;
    }
    let row_weight=|copy:usize,row:usize|->Fr{
        let family=row>>base_row_bits;let local=row&((1usize<<base_row_bits)-1);
        let low=member_row_bits[family];
        debug_assert_eq!(row_weight_lookup.at(copy,row),
            eq_weight_at(&r[..low],local)*eq_weight_at(&r[low..low+copy_bits],copy)
                    *r[low+copy_bits..base_row_bits+copy_bits].iter()
                    .fold(Fr::one(),|value,coordinate|value*(Fr::one()-coordinate))
                *eq_weight_at(&r[base_row_bits+copy_bits..],family),
            "family {family} slot {copy} row {local} tensor row weight");
        row_weight_lookup.at(copy,row)
    };
    // A term whose left wire is algebraically inactive still contributes its
    // c0/c2 part to the resident producer's global input index zero.  Keep
    // that anchor in slot zero rather than duplicating it at each slot's local
    // zero coordinate.
    // One local cache keeps the eight dense witness vectors, while its GKR
    // coefficient banks contain at most one entry per emitted term and bank.
    // During a fold, old and new sparse banks coexist briefly, so reserve a
    // 2x coefficient allowance without allocating dense A/B scratch arrays.
    // This limit covers retained per-slot X/coefficient cache state plus the
    // old/new sparse banks coexisting during folds. It is not a cap on the
    // process's total live memory (for example, row-weight tables are separate).
    let field_bytes=std::mem::size_of::<Fr>();let sparse_entry_bytes=std::mem::size_of::<(usize,Fr)>();
    let slot_descriptor_bytes=copies.checked_mul(std::mem::size_of::<(SparseFieldVector,SparseFieldVector,Vec<Fr>)>());
    let expected_term_total=expected_counts.iter().try_fold(0usize,|sum,count|sum.checked_add(*count));
    let retained_x_bound=copies.checked_mul(width).and_then(|fields|fields.checked_mul(field_bytes));
    let sparse_capacity_bound=expected_term_total.and_then(|terms|terms.checked_add(copies))
        .and_then(|terms|terms.checked_mul(2))
        .and_then(|entries|entries.checked_mul(sparse_entry_bytes));
    let cache_peak_bound=retained_x_bound.and_then(|x|sparse_capacity_bound.and_then(|s|s.checked_mul(2)
        .and_then(|fold_peak|x.checked_add(fold_peak))))
        .and_then(|bytes|slot_descriptor_bytes.and_then(|desc|bytes.checked_add(desc)));
    let mut retained_x_bytes=0usize;let mut retained_sparse_bytes=0usize;
    let mut incremental_slots:Option<Vec<(SparseFieldVector,SparseFieldVector,Vec<Fr>)>>=None;
    let mut can_incremental=cache_peak_bound.is_some_and(|bytes|bytes<=cache_budget_bytes);
    let mut slots=if can_incremental{Vec::with_capacity(copies)}else{Vec::new()};
    let mut global_left_b=Fr::zero();
    for copy in 0..if can_incremental{copies}else{0}{
        let local_input=read_copy(&mut load_copy,copy,width)?;
        let mut a=Vec::new();let mut b=Vec::new();
        a.try_reserve_exact(expected_counts[copy]).map_err(|_|"sparse A reservation failed")?;
        b.try_reserve_exact(expected_counts[copy].checked_add(1).ok_or("sparse B capacity overflow")?)
            .map_err(|_|"sparse B reservation failed")?;
        let new_sparse_bytes=a.capacity().checked_add(b.capacity()).and_then(|count|count.checked_mul(sparse_entry_bytes));
        let projected_live=retained_x_bytes.checked_add(local_input.capacity().checked_mul(field_bytes).unwrap_or(usize::MAX))
            .and_then(|bytes|retained_sparse_bytes.checked_add(new_sparse_bytes?).and_then(|s|s.checked_mul(2).and_then(|peak|bytes.checked_add(peak))))
            .and_then(|bytes|slot_descriptor_bytes.and_then(|desc|bytes.checked_add(desc)));
        if projected_live.is_none_or(|bytes|bytes>cache_budget_bytes){can_incremental=false;break;}
        walk(copy,&mut |term|{
            let gate=&term.gate;
            if gate.left==width{
                let right=if gate.right==width{Fr::zero()}else{local_input[gate.right]};
                global_left_b+=row_weight(copy,term.row)*(gate.c0+gate.c2*right);
            }else{
                let weight=row_weight(copy,term.row);let right=if gate.right==width{Fr::zero()}else{local_input[gate.right]};
                let av=weight*(gate.c1+gate.c3*right);let bv=weight*(gate.c0+gate.c2*right);
                if !av.is_zero(){a.push((gate.left,av));}if !bv.is_zero(){b.push((gate.left,bv));}
            }Ok(())
        })?;
        coalesce_nonzero_in_place(&mut a);coalesce_nonzero_in_place(&mut b);
        retained_x_bytes=retained_x_bytes.checked_add(local_input.capacity().checked_mul(field_bytes).ok_or("local input byte count overflow")?)
            .ok_or("retained input byte count overflow")?;
        retained_sparse_bytes=retained_sparse_bytes
            .checked_add(a.capacity().checked_add(b.capacity()).and_then(|count|count.checked_mul(sparse_entry_bytes)).ok_or("sparse coefficient byte count overflow")?)
            .ok_or("retained sparse byte count overflow")?;
        slots.push((a,b,local_input));
    }
    if let Some(p)=&u_plan{p.before(UPhase::RowBuild,0,ULive::default())?;}
    let mut u_factor=if can_incremental{None}else{
        OneFamilyRowFactor::try_new(&r,copy_bits,base_row_bits,family_bits,member_row_bits,
            row_weight_lookup.local_table(base_row_bits))
    };
    if let Some(p)=&u_plan{p.lookup_actual(&row_weight_lookup,Some(u_factor.as_ref().ok_or("capacity46 row factor missing")?))?;}
    let fixed_u=if let (Some(template),Some(stats),Some(factor),Some(workspace))=
        (fixed_v,u_stats,u_factor.as_ref(),fixed_workspace.as_ref()){
        let common_v_bytes=workspace.capacity_bytes;
        FixedCoreUWorkspace::try_new(template,factor.local_weights.as_ref(),common_v_bytes,u_capacity_budget)
            .map(|candidate|{
                let combined=common_v_bytes+candidate.capacity_bytes;
                let mut value=stats.get();
                value.descriptor_count=candidate.descriptors.len();
                value.common_u_capacity_bytes=candidate.capacity_bytes;
                stats.set(value);
                if let Some(capacity)=capacity_stats{capacity.set(capacity.get().max(combined));}
                candidate
            })
    }else{None};
    if can_incremental{
        if let Some((_,b,_))=slots.first_mut(){let value=sparse_value(b,0)+global_left_b;
            b.retain(|(wire,_)|*wire!=0);if !value.is_zero(){b.push((0,value));}coalesce_nonzero_in_place(b);}
        incremental_slots=Some(slots);
    }else{
        drop(slots);global_left_b=Fr::zero();
        if let Some(stats)=boolean_u_stats.as_deref_mut(){
            // Every captured endpoint was strictly below width at baseline.
            stats.zero_anchor_sweep_skipped=true;
        }
        for source_copy in 0..if boolean_u_stats.is_some(){0}else{copies}{
            let local_input=read_copy(&mut load_copy,source_copy,width)?;
            walk(source_copy,&mut |term|{if term.gate.left==width{
                let right=if term.gate.right==width{Fr::zero()}else{local_input[term.gate.right]};
                let weight=if let Some(factor)=&u_factor{factor.local(term.row)*factor.copy(source_copy)}
                    else{row_weight(source_copy,term.row)};
                global_left_b+=weight*(term.gate.c0+term.gate.c2*right);
            }Ok(())})?;
        }
    }
    phase_mark(if can_incremental{"u_cache_incremental"}else{"u_cache_streamed"})?;
    phase_mark("u_anchor_done")?;

    if let Some(p)=&u_plan{p.before(UPhase::Send,0,ULive::default())?;}
    let mut claim=Fr::zero();let mut rounds=Vec::new();let mut u_local=Vec::with_capacity(input_bits);
    if let Some(p)=&u_plan{
        p.before(UPhase::Send,0,ULive::default())?;
        rounds.try_reserve_exact(2*(input_bits+copy_bits)).map_err(|_|"capacity46 round reservation")?;
        p.high_actual(&rounds,&[&u_local])?;
    }
    let mut boolean_handoff=None;
    if let Some(stats)=boolean_u_stats.as_deref_mut(){
        boolean_handoff=Some(prove_boolean_u_prefixes_with_fold(width,input_bits,copies,
            grouped_templates.as_ref().ok_or("Boolean U captured templates missing")?,
            grouped_v_admission.ok_or("Boolean U admission missing")?,&row_weight_lookup,
            u_factor.as_ref().ok_or("Boolean U row factor unavailable")?,
            grouped_v_stats.as_deref().ok_or("Boolean U grouped statistics missing")?,expected_counts.capacity(),r.capacity(),
            &mut load_copy,&mut claim,&mut rounds,&mut u_local,transcript,stats,mode,subset.as_deref_mut(),u_plan.as_ref())?);
    }else if let Some(slots)=incremental_slots.as_mut(){
        for _round in 0..input_bits{
            let mut polynomial=[Fr::zero();3];
            for (a,b,x) in slots.iter(){for (sum,value) in polynomial.iter_mut().zip(sparse_quadratic_message(a,b,x)){*sum+=value;}}
            let challenge=send_round(polynomial.to_vec(),&mut claim,&mut rounds,transcript).map_err(|e|e.to_string())?;
            for (a,b,x) in slots.iter_mut(){*a=sparse_fold(a,challenge);*b=sparse_fold(b,challenge);gkr::fold(x,challenge);}
            u_local.push(challenge);
            if let Some(expected)=expected_resident_rounds{
                let round=rounds.len()-1;
                assert_eq!(rounds[round].as_slice(),expected[round].as_slice(),"slot-tensor GKR message differs at local round {round}");
            }
        }
    }else{
        for _round in 0..input_bits{
            let mut polynomial=[Fr::zero();3];
            let prefix_weights=if direct_u_prefix{Some(gkr::eq_weights(&u_local))}else{None};
            for copy in 0..copies{
                let local_input=read_copy(&mut load_copy,copy,width)?;
                let (mut a,mut b)=if direct_u_prefix{
                    direct_u_prefix_coefficients(width,&u_local,prefix_weights.as_ref().ok_or("direct U prefix weights missing")?,
                        copy,&local_input,
                        |owner,row|if let Some(factor)=&u_factor{factor.local(row)}else{row_weight(owner,row)},
                        |sink|walk(copy,sink))?
                }else{
                    let indexed=match (fixed_u.as_ref(),fixed_v,u_factor.as_ref()){
                        (Some(workspace),Some(template),Some(factor))=>workspace.build_boolean(template.terms,
                            factor.local_weights.as_ref(),&local_input),_=>None};
                    if let Some((a,b))=indexed{
                        record_fixed_u_builder(u_stats,true)?;(a,b)
                    }else{
                        record_fixed_u_builder(u_stats,false)?;
                        let mut a=vec![Fr::zero();width];let mut b=vec![Fr::zero();width];
                        walk(copy,&mut |term|{
                            let gate=&term.gate;if gate.left==width{return Ok(());}
                            let weight=if let Some(factor)=&u_factor{factor.local(term.row)}else{row_weight(copy,term.row)};
                            let right=if gate.right==width{Fr::zero()}else{local_input[gate.right]};
                            a[gate.left]+=weight*(gate.c1+gate.c3*right);
                            b[gate.left]+=weight*(gate.c0+gate.c2*right);Ok(())
                        })?;(a,b)
                    }
                };
                if u_factor.is_none()&&copy==0{
                    b[0]+=if direct_u_prefix{global_left_b*prefix_weights.as_ref().ok_or("direct U prefix weights missing")?[0]}
                        else{global_left_b};
                }
                if !direct_u_prefix{for challenge in &u_local{gkr::fold(&mut a,*challenge);gkr::fold(&mut b,*challenge);}}
                let mut x=local_input;for challenge in &u_local{gkr::fold(&mut x,*challenge);}
                if let Some(factor)=&u_factor{
                    OneFamilyRowFactor::add_scaled_message(&mut polynomial,&a,&b,&x,factor.copy(copy));
                }else{
                    for (sum,value) in polynomial.iter_mut().zip(gkr::quadratic_message(&a,&b,&x)){*sum+=value;}
                }
            }
            if let Some(factor)=&u_factor{OneFamilyRowFactor::add_anchor_message(&mut polynomial,global_left_b,&u_local);}
            u_local.push(send_round(polynomial.to_vec(),&mut claim,&mut rounds,transcript).map_err(|e|e.to_string())?);
            if let Some(expected)=expected_resident_rounds{
                let round=rounds.len()-1;
                assert_eq!(rounds[round].as_slice(),expected[round].as_slice(),"slot-tensor GKR message differs at local round {round}");
            }
        }
    }
    if boolean_handoff.is_none(){phase_mark("u_local_done")?;}

    let boolean_handled=boolean_handoff.is_some();
    let (mut high_a,mut high_b,mut high_x,direct_u_handoff_weights)=if let Some((a,b,x,weights))=boolean_handoff.take(){
        (a,b,x,Some(weights))
    }else{(Vec::with_capacity(copies),Vec::with_capacity(copies),Vec::with_capacity(copies),
        if direct_u_prefix{Some(gkr::eq_weights(&u_local))}else{None})};
    if boolean_handled{
        // The terminal bank is already scaled and all preweights were dropped.
    }else if let Some(slots)=incremental_slots{
        for (a,b,x) in slots{high_a.push(sparse_value(&a,0));high_b.push(sparse_value(&b,0));high_x.push(x[0]);}
    }else{
        for copy in 0..copies{
            let local_input=read_copy(&mut load_copy,copy,width)?;
            let (mut a,mut b)=if direct_u_prefix{
                direct_u_prefix_coefficients(width,&u_local,direct_u_handoff_weights.as_ref()
                    .ok_or("direct U handoff weights missing")?,copy,&local_input,
                    |owner,row|if let Some(factor)=&u_factor{factor.local(row)}else{row_weight(owner,row)},
                    |sink|walk(copy,sink))?
            }else{
                let indexed=match (fixed_u.as_ref(),fixed_v,u_factor.as_ref()){
                    (Some(workspace),Some(template),Some(factor))=>workspace.build_boolean(template.terms,
                        factor.local_weights.as_ref(),&local_input),_=>None};
                if let Some((a,b))=indexed{
                    record_fixed_u_builder(u_stats,true)?;(a,b)
                }else{
                    record_fixed_u_builder(u_stats,false)?;
                    let mut a=vec![Fr::zero();width];let mut b=vec![Fr::zero();width];
                    walk(copy,&mut |term|{let gate=&term.gate;if gate.left==width{return Ok(());}
                        let weight=if let Some(factor)=&u_factor{factor.local(term.row)}else{row_weight(copy,term.row)};
                        let right=if gate.right==width{Fr::zero()}else{local_input[gate.right]};
                        a[gate.left]+=weight*(gate.c1+gate.c3*right);b[gate.left]+=weight*(gate.c0+gate.c2*right);Ok(())})?;(a,b)
                }
            };
            if u_factor.is_none()&&copy==0{
                b[0]+=if direct_u_prefix{global_left_b*direct_u_handoff_weights.as_ref()
                    .ok_or("direct U handoff weights missing")?[0]}else{global_left_b};
            }
            let mut x=local_input;
            if !direct_u_prefix{for challenge in &u_local{gkr::fold(&mut a,*challenge);gkr::fold(&mut b,*challenge);}}
            for challenge in &u_local{gkr::fold(&mut x,*challenge);}
            if let Some(factor)=&u_factor{
                let anchor=if copy==0{OneFamilyRowFactor::anchor_after_prefix(global_left_b,&u_local)}else{Fr::zero()};
                high_a.push(factor.copy(copy)*a[0]);
                high_b.push(OneFamilyRowFactor::handoff(b[0],factor.copy(copy),anchor));
            }else{
                high_a.push(a[0]);high_b.push(b[0]);
            }
            high_x.push(x[0]);
        }
    }
    if let Some((expected_a,expected_b,expected_x))=expected_resident_handoff{
        assert_eq!(high_a.as_slice(),expected_a,"slot tensor A handoff differs from resident MLE");
        assert_eq!(high_b.as_slice(),expected_b,"slot tensor B handoff differs from resident MLE");
        assert_eq!(high_x.as_slice(),expected_x,"slot tensor X handoff differs from resident MLE");
    }
    drop(fixed_u);
    if let Some(p)=&u_plan{p.before(UPhase::High,input_bits,ULive::default())?;}
    let (u_high,left_value)=gkr::prove_phase(high_a,high_b,&high_x,&mut claim,&mut rounds,transcript).map_err(|e|e.to_string())?;
    drop(high_x);
    if let Some(p)=&u_plan{p.high_actual(&rounds,&[&r,&u_local,&u_high])?;p.before(UPhase::PostHigh,input_bits,ULive::default())?;}
    phase_mark("u_handoff_done")?;
    if let Some(expected)=expected_resident_rounds{
        if rounds.len()<=input_bits{return Err("resident boundary round is absent".into());}
        assert_eq!(rounds[input_bits].as_slice(),expected[input_bits].as_slice(),"slot-tensor GKR message differs at the local/slot boundary");
    }
    let mut u=u_local.clone();
    if let Some(p)=&u_plan{p.high_actual(&rounds,&[&r,&u_local,&u_high,&u])?;}
    u.extend(u_high);
    if let Some(p)=&u_plan{p.high_actual(&rounds,&[&r,&u_local,&u])?;}
    let u_local_weights=direct_u_handoff_weights.unwrap_or_else(||gkr::eq_weights(&u_local));
    let u_copy_weights=gkr::eq_weights(&u[input_bits..]);
    if let Some(p)=&u_plan{
        p.high_actual(&rounds,&[&r,&u_local,&u])?;
        p.handoff_weights_actual(&u_local_weights,&u_copy_weights)?;
        let n=boolean_u_capacity_bytes(grouped_templates.as_ref().ok_or("capacity46 templates missing")?,
            grouped_v_admission.ok_or("capacity46 admission missing")?,&row_weight_lookup,
            u_factor.as_ref().ok_or("capacity46 row factor missing")?,grouped_v_stats.as_deref().ok_or("capacity46 statistics missing")?,
            expected_counts.capacity(),&rounds,u.capacity()+u_local.capacity()+r.capacity(),u_local_weights.capacity(),0,0,0,
            u_copy_weights.capacity(),0,width).ok_or("capacity46 post-high arithmetic")?;
        let n=u_sum(&[n,UCapacityPlan::metadata()?,subset4_metadata_bytes().ok_or("capacity46 metadata")?])?;
        p.actual(UPhase::PostHigh,input_bits,n,dimension_policy.extra_capacity_bytes(),0,0)?;
        boolean_u_stats.as_deref_mut().ok_or("capacity46 statistics missing")?.record_capacity(5,n)?;
    }
    // No U plan, borrow or phase state is retained by the literal V tail.
    drop(u_plan);

    if let Some(template)=fixed_v{
        let template_term_count=expected_counts.first().copied().unwrap_or(0);
        if fixed_v_cache_bound(copies,width,template_term_count).is_none_or(|bytes|bytes>cache_budget_bytes){
            let workspace=fixed_workspace.as_deref_mut().ok_or("fixed V workspace was not reserved before transcript binding")?;
            let mut right_claim=claim;
            return prove_fixed_v_tail(template,workspace,input_bits,copy_bits,&mut load_copy,&r,&u,&row_weight_lookup,&u_local_weights,&mut right_claim,
                &mut rounds,transcript,left_value,&wiring,template_stats.ok_or("fixed V statistics sink is missing")?,
                capacity_stats.ok_or("fixed V capacity statistics sink is missing")?);
        }
    }

    if let Some(admission)=grouped_v_admission{
        let templates=grouped_templates.take().ok_or("grouped V term templates are missing")?;
        drop(u_factor);
        drop(u_local);
        let stats=grouped_v_stats.as_deref_mut().ok_or("grouped V statistics sink is missing")?;
        if boolean_u_stats.is_some(){stats.private_capacity_reservation_bytes=stats.private_capacity_reservation_bytes
            .checked_add(boolean_u_v_reservation(width).ok_or("Boolean U grouped V scratch reservation overflow")?)
            .ok_or("Boolean U grouped V total reservation overflow")?;}
        if subset.is_some(){stats.private_capacity_reservation_bytes=stats.private_capacity_reservation_bytes
            .checked_add(subset4_metadata_bytes().ok_or("subset4 V metadata arithmetic")?).ok_or("subset4 V metadata arithmetic")?;}
        return prove_grouped_v_tail(input_bits,copy_bits,base_row_bits,width,copies,admission,templates,
            &row_weight_lookup,&u_local_weights,&u_copy_weights,&r,&u,left_value,expected_counts.capacity(),
            r.capacity().checked_add(u.capacity()).ok_or("grouped V point capacity overflow")?,&mut load_copy,&mut claim,
            &mut rounds,transcript,&wiring,stats);
    }

    // Phase v uses the same bounded incremental strategy as phase u. Each
    // slot is aggregated once after u, then C/D and X are folded as each v
    // challenge arrives. Fall back to the original streamed producer when
    // retaining this local state would exceed the cap.
    let slot_descriptor_bytes=copies.checked_mul(std::mem::size_of::<(SparseFieldVector,SparseFieldVector,Vec<Fr>)>());
    let expected_term_total=expected_counts.iter().try_fold(0usize,|sum,count|sum.checked_add(*count));
    let retained_x_bound=copies.checked_mul(width).and_then(|fields|fields.checked_mul(field_bytes));
    let sparse_capacity_bound=expected_term_total.and_then(|terms|terms.checked_add(copies))
        .and_then(|terms|terms.checked_mul(2)).and_then(|entries|entries.checked_mul(sparse_entry_bytes));
    let cache_peak_bound=retained_x_bound.and_then(|x|sparse_capacity_bound.and_then(|s|s.checked_mul(2)
        .and_then(|fold_peak|x.checked_add(fold_peak))))
        .and_then(|bytes|slot_descriptor_bytes.and_then(|desc|bytes.checked_add(desc)));
    let mut retained_x_bytes=0usize;let mut retained_sparse_bytes=0usize;
    let mut incremental_v_slots:Option<Vec<(SparseFieldVector,SparseFieldVector,Vec<Fr>)>>=None;
    let mut can_incremental=cache_peak_bound.is_some_and(|bytes|bytes<=cache_budget_bytes);
    let mut slots=if can_incremental{Vec::with_capacity(copies)}else{Vec::new()};
    let mut global_right_d=Fr::zero();
    for copy in 0..if can_incremental{copies}else{0}{
        let local_input=read_copy(&mut load_copy,copy,width)?;
        let mut c=Vec::new();let mut d=Vec::new();
        c.try_reserve_exact(expected_counts[copy]).map_err(|_|"sparse C reservation failed")?;
        d.try_reserve_exact(expected_counts[copy].checked_add(1).ok_or("sparse D capacity overflow")?)
            .map_err(|_|"sparse D reservation failed")?;
        let new_sparse_bytes=c.capacity().checked_add(d.capacity()).and_then(|count|count.checked_mul(sparse_entry_bytes));
        let projected_live=retained_x_bytes.checked_add(local_input.capacity().checked_mul(field_bytes).unwrap_or(usize::MAX))
            .and_then(|bytes|retained_sparse_bytes.checked_add(new_sparse_bytes?).and_then(|s|s.checked_mul(2).and_then(|peak|bytes.checked_add(peak))))
            .and_then(|bytes|slot_descriptor_bytes.and_then(|desc|bytes.checked_add(desc)));
        if projected_live.is_none_or(|bytes|bytes>cache_budget_bytes){can_incremental=false;break;}
        walk(copy,&mut |term|{let gate=&term.gate;
            let (left_copy,left_wire)=if gate.left==width{(0,0)}else{(copy,gate.left)};
            let left_weight=u_copy_weights[left_copy]*u_local_weights[left_wire];
            let weight=row_weight(copy,term.row)*left_weight;
            if gate.right==width{
                global_right_d+=weight*(gate.c0+gate.c1*left_value);
            }else{
                let cv=weight*(gate.c2+gate.c3*left_value);let dv=weight*(gate.c0+gate.c1*left_value);
                if !cv.is_zero(){c.push((gate.right,cv));}if !dv.is_zero(){d.push((gate.right,dv));}
            }Ok(())})?;
        coalesce_nonzero_in_place(&mut c);coalesce_nonzero_in_place(&mut d);
        let x=local_input;
        retained_x_bytes=retained_x_bytes.checked_add(x.capacity().checked_mul(field_bytes).ok_or("local input byte count overflow")?)
            .ok_or("retained input byte count overflow")?;
        retained_sparse_bytes=retained_sparse_bytes
            .checked_add(c.capacity().checked_add(d.capacity()).and_then(|count|count.checked_mul(sparse_entry_bytes)).ok_or("sparse coefficient byte count overflow")?)
            .ok_or("retained sparse byte count overflow")?;
        slots.push((c,d,x));
    }
    if !can_incremental{
        if let Some(template)=fixed_v{
            drop(slots);
            let workspace=fixed_workspace.as_deref_mut().ok_or("fixed V workspace was not reserved before transcript binding")?;
            let mut right_claim=claim;
            return prove_fixed_v_tail(template,workspace,input_bits,copy_bits,&mut load_copy,&r,&u,&row_weight_lookup,
                &u_local_weights,&mut right_claim,&mut rounds,transcript,left_value,&wiring,
                template_stats.ok_or("fixed V statistics sink is missing")?,
                capacity_stats.ok_or("fixed V capacity statistics sink is missing")?);
        }
    }
    let v_factor=if can_incremental{u_factor.take();None}else{
        u_factor.take().or_else(||OneFamilyRowFactor::try_new(&r,copy_bits,base_row_bits,family_bits,member_row_bits,
            row_weight_lookup.local_table(base_row_bits)))
    };
    if can_incremental{
        if let Some((_,d,_))=slots.first_mut(){let value=sparse_value(d,0)+global_right_d;
            d.retain(|(wire,_)|*wire!=0);if !value.is_zero(){d.push((0,value));}coalesce_nonzero_in_place(d);}
        incremental_v_slots=Some(slots);
    }else{
        drop(slots);global_right_d=Fr::zero();
        for source_copy in 0..copies{walk(source_copy,&mut |term|{
            if term.gate.right==width{
                let (left_copy,left_wire)=if term.gate.left==width{(0,0)}else{(source_copy,term.gate.left)};
                let left_weight=u_copy_weights[left_copy]*u_local_weights[left_wire];
                let weight=if let Some(factor)=&v_factor{factor.local(term.row)*factor.copy(source_copy)}
                    else{row_weight(source_copy,term.row)};
                global_right_d+=weight*left_weight*(term.gate.c0+term.gate.c1*left_value);
            }Ok(())})?;}
    }
    phase_mark(if can_incremental{"v_cache_incremental"}else{"v_cache_streamed"})?;
    phase_mark("v_anchor_done")?;
    let mut v_local=Vec::with_capacity(input_bits);
    if let Some(slots)=incremental_v_slots.as_mut(){
        for _round in 0..input_bits{
            let mut polynomial=[Fr::zero();3];
            for (c,d,x) in slots.iter(){for (sum,value) in polynomial.iter_mut().zip(sparse_quadratic_message(c,d,x)){*sum+=value;}}
            let challenge=send_round(polynomial.to_vec(),&mut claim,&mut rounds,transcript).map_err(|e|e.to_string())?;
            for (c,d,x) in slots.iter_mut(){*c=sparse_fold(c,challenge);*d=sparse_fold(d,challenge);gkr::fold(x,challenge);}
            v_local.push(challenge);
            if let Some(expected)=expected_resident_rounds{
                let round=rounds.len()-1;
                assert_eq!(rounds[round].as_slice(),expected[round].as_slice(),"slot-tensor GKR message differs at local v round {round}");
            }
        }
    }else{
        for _round in 0..input_bits{
            let mut polynomial=[Fr::zero();3];
            for copy in 0..copies{
                let local_input=read_copy(&mut load_copy,copy,width)?;
                let mut c=vec![Fr::zero();width];let mut d=vec![Fr::zero();width];
                walk(copy,&mut |term|{let gate=&term.gate;
                    let (left_copy,left_wire)=if gate.left==width{(0,0)}else{(copy,gate.left)};
                    let left_weight=u_copy_weights[left_copy]*u_local_weights[left_wire];
                    let row_weight=if let Some(factor)=&v_factor{factor.local(term.row)}else{row_weight(copy,term.row)};
                    let weight=row_weight*left_weight;
                    if gate.right!=width{
                        c[gate.right]+=weight*(gate.c2+gate.c3*left_value);
                        d[gate.right]+=weight*(gate.c0+gate.c1*left_value);
                    }Ok(())})?;
                if v_factor.is_none()&&copy==0{d[0]+=global_right_d;}
                let mut x=local_input;
                for challenge in &v_local{gkr::fold(&mut c,*challenge);gkr::fold(&mut d,*challenge);gkr::fold(&mut x,*challenge);}
                if let Some(factor)=&v_factor{
                    OneFamilyRowFactor::add_scaled_message(&mut polynomial,&c,&d,&x,factor.copy(copy));
                }else{
                    for (sum,value) in polynomial.iter_mut().zip(gkr::quadratic_message(&c,&d,&x)){*sum+=value;}
                }
            }
            if v_factor.is_some(){OneFamilyRowFactor::add_anchor_message(&mut polynomial,global_right_d,&v_local);}
            v_local.push(send_round(polynomial.to_vec(),&mut claim,&mut rounds,transcript).map_err(|e|e.to_string())?);
            if let Some(expected)=expected_resident_rounds{
                let round=rounds.len()-1;
                assert_eq!(rounds[round].as_slice(),expected[round].as_slice(),"slot-tensor GKR message differs at local v round {round}");
            }
        }
    }
    phase_mark("v_local_done")?;
    let mut high_c=Vec::with_capacity(copies);let mut high_d=Vec::with_capacity(copies);let mut high_w=Vec::with_capacity(copies);
    if let Some(slots)=incremental_v_slots{
        for (c,d,x) in slots{high_c.push(sparse_value(&c,0));high_d.push(sparse_value(&d,0));high_w.push(x[0]);}
    }else{
        for copy in 0..copies{
            let local_input=read_copy(&mut load_copy,copy,width)?;
            let mut c=vec![Fr::zero();width];let mut d=vec![Fr::zero();width];
            walk(copy,&mut |term|{let gate=&term.gate;
                let (left_copy,left_wire)=if gate.left==width{(0,0)}else{(copy,gate.left)};
                let row_weight=if let Some(factor)=&v_factor{factor.local(term.row)}else{row_weight(copy,term.row)};
                let weight=row_weight*u_copy_weights[left_copy]*u_local_weights[left_wire];
                if gate.right!=width{
                    c[gate.right]+=weight*(gate.c2+gate.c3*left_value);
                    d[gate.right]+=weight*(gate.c0+gate.c1*left_value);
                }Ok(())})?;
            if v_factor.is_none()&&copy==0{d[0]+=global_right_d;}
            let mut x=local_input;
            for challenge in &v_local{gkr::fold(&mut c,*challenge);gkr::fold(&mut d,*challenge);gkr::fold(&mut x,*challenge);}
            if let Some(factor)=&v_factor{
                let anchor=if copy==0{OneFamilyRowFactor::anchor_after_prefix(global_right_d,&v_local)}else{Fr::zero()};
                high_c.push(factor.copy(copy)*c[0]);
                high_d.push(OneFamilyRowFactor::handoff(d[0],factor.copy(copy),anchor));
            }else{
                high_c.push(c[0]);high_d.push(d[0]);
            }
            high_w.push(x[0]);
        }
    }
    let v_high_start=rounds.len();
    let (v_high,right_value)=gkr::prove_phase(high_c,high_d,&high_w,&mut claim,&mut rounds,transcript).map_err(|e|e.to_string())?;
    phase_mark("v_handoff_done")?;
    if let Some(expected)=expected_resident_rounds{
        for offset in 0..v_high.len(){
            let round=v_high_start+offset;
            assert_eq!(rounds[round].as_slice(),expected[round].as_slice(),"slot-tensor GKR message differs at high v round {offset}");
        }
    }
    let mut v=v_local.clone();v.extend(v_high);
    let coefficients=wiring(&r,&u,&v)?;
    if coefficients[0]+coefficients[1]*left_value+coefficients[2]*right_value
        +coefficients[3]*left_value*right_value!=claim{
        return Err(GkrError::TerminalExpression.to_string());
    }
    phase_mark("terminal_wiring_done")?;

    phase_mark("line_start")?;
    let mut line=vec![Fr::zero();input_bits+copy_bits+1];
    for copy in 0..copies{
        let local_input=read_copy(&mut load_copy,copy,width)?;
        let local=gkr::line_polynomial(&local_input,&u_local,&v_local);
        let selector=copy_line_selector(copy,&u[input_bits..],&v[input_bits..]);
        for (sum,value) in line.iter_mut().zip(multiply(&local,&selector)){*sum+=value;}
    }
    phase_mark("line_done")?;
    if line[0]!=left_value||gkr::eval_polynomial(&line,Fr::one())!=right_value{return Err(GkrError::LineEndpoints.to_string());}
    transcript.append_scalar(b"gkr-left-value",&left_value);transcript.append_scalar(b"gkr-right-value",&right_value);
    gkr::append_polynomial(transcript,b"gkr-line-polynomial",&line);
    let challenge=transcript.challenge_scalar(b"gkr-line-challenge");
    let point=gkr::line_point(&u,&v,challenge);let value=gkr::eval_polynomial(&line,challenge);
    Ok((GkrProof{layers:vec![LayerProof{rounds,left_value,right_value,line_coefficients:line}]},InputClaim{point,value}))
}

fn prove_grouped_v_tail(
    input_bits:usize,copy_bits:usize,base_row_bits:usize,width:usize,copies:usize,
    admission:&GroupedVAdmission,templates:Vec<Option<Vec<Term>>>,row_weight_lookup:&TensorRowWeightLookup<'_>,
    u_local_weights:&Vec<Fr>,u_copy_weights:&Vec<Fr>,r:&[Fr],u:&[Fr],left_value:Fr,
    expected_counts_capacity:usize,point_capacity:usize,
    mut load_copy:impl FnMut(usize)->Result<Vec<Fr>,String>,claim:&mut Fr,rounds:&mut Vec<Vec<Fr>>,
    transcript:&mut Transcript,wiring:impl Fn(&[Fr],&[Fr],&[Fr])->Result<[Fr;4],String>,
    stats:&mut GroupedVStats,
)->Result<(GkrProof,InputClaim),String>{
    let bank_started=std::time::Instant::now();
    let local_row_weights=EqWeightLookup::new(&r[..base_row_bits]);
    let row_copy_weights=EqWeightLookup::new(&r[base_row_bits..base_row_bits+copy_bits]);
    let mut group_weight_sums=vec![Fr::zero();admission.expected_terms_per_group.len()];
    for copy in 0..copies{
        let group=admission.group_by_copy[copy];
        group_weight_sums[group]+=row_copy_weights.at(copy)*u_copy_weights[copy];
    }
    let mut banks=Vec::new();banks.try_reserve_exact(admission.expected_terms_per_group.len())
        .map_err(|_|"grouped V bank descriptor reservation failed")?;
    for _ in 0..admission.expected_terms_per_group.len(){
        let mut c=Vec::new();let mut d=Vec::new();let mut x=Vec::new();
        for vector in [&mut c,&mut d,&mut x]{
            vector.try_reserve_exact(width).map_err(|_|"grouped V dense bank reservation failed")?;
            vector.resize(width,Fr::zero());
        }
        banks.push(GroupedVBank{c,d,x});
    }
    let mut template_terms=0usize;
    for (group,template) in templates.iter().enumerate(){
        let terms=template.as_ref().ok_or("grouped V admitted group has no captured template")?;
        if terms.len()!=admission.expected_terms_per_group[group]{return Err("grouped V template count differs from its admission".into());}
        template_terms=template_terms.checked_add(terms.len()).ok_or("grouped V template count overflow")?;
        for term in terms{
            let row=term.row&((1usize<<base_row_bits)-1);let gate=&term.gate;
            let weight=local_row_weights.at(row)*u_local_weights[gate.left];
            banks[group].c[gate.right]+=weight*(gate.c2+gate.c3*left_value);
            banks[group].d[gate.right]+=weight*(gate.c0+gate.c1*left_value);
        }
    }
    stats.bank_term_callbacks=template_terms;
    let mut peak=grouped_v_total_capacity_bytes(admission,&templates,&banks,row_weight_lookup,u_local_weights,
        u_copy_weights,&group_weight_sums,&local_row_weights,&row_copy_weights,stats,expected_counts_capacity,
        rounds,0,point_capacity,0,None,None,0)?;
    if peak>MAX_INCREMENTAL_CACHE_STATE_BYTES{return Err("grouped V dense banks exceed 512 MiB before local V rounds".into());}

    for copy in 0..copies{
        let local_input=read_copy(&mut load_copy,copy,width)?;
        let group=admission.group_by_copy[copy];
        let lambda=row_copy_weights.at(copy)*u_copy_weights[copy];
        #[cfg(test)]
        let lambda=if TEST_GROUPED_V_MUTANT.with(|mode|mode.get()==2){
            row_copy_weights.at(copy^1)*u_copy_weights[copy]
        }else{lambda};
        for (sum,value) in banks[group].x.iter_mut().zip(&local_input){*sum+=lambda*value;}
        let live=grouped_v_total_capacity_bytes(admission,&templates,&banks,row_weight_lookup,u_local_weights,
            u_copy_weights,&group_weight_sums,&local_row_weights,&row_copy_weights,stats,expected_counts_capacity,
            rounds,0,point_capacity,local_input.capacity(),None,None,0)?;
        peak=peak.max(live);
        if live>MAX_INCREMENTAL_CACHE_STATE_BYTES{return Err("grouped V owner input exceeds 512 MiB state cap".into());}
    }
    stats.bank_build_elapsed_ns=elapsed_nanos(bank_started);
    stats.group_weight_sums.clear();
    stats.group_weight_sums.try_reserve_exact(group_weight_sums.len())
        .map_err(|_|"grouped V statistics reservation failed")?;
    stats.group_weight_sums.extend_from_slice(&group_weight_sums);
    stats.handoff_term_callbacks=0;
    stats.grouped_state_peak_capacity_bytes=stats.grouped_state_peak_capacity_bytes.max(peak);

    phase_mark("v_cache_grouped")?;phase_mark("v_anchor_done")?;
    let local_started=std::time::Instant::now();
    let mut v_local=Vec::with_capacity(input_bits);
    for _round in 0..input_bits{
        let mut polynomial=[Fr::zero();3];
        for (group,bank) in banks.iter().enumerate(){
            let d_scale=group_weight_sums[group];
            #[cfg(test)]
            let d_scale=if TEST_GROUPED_V_MUTANT.with(|mode|mode.get()==1){Fr::one()}else{d_scale};
            for (sum,value) in polynomial.iter_mut().zip(scaled_common_quadratic_message(
                &bank.c,&bank.d,&bank.x,d_scale)){*sum+=value;}
        }
        let challenge=send_round(polynomial.to_vec(),claim,rounds,transcript).map_err(|error|error.to_string())?;
        for bank in &mut banks{gkr::fold(&mut bank.c,challenge);gkr::fold(&mut bank.d,challenge);gkr::fold(&mut bank.x,challenge);}
        v_local.push(challenge);
        let live=grouped_v_total_capacity_bytes(admission,&templates,&banks,row_weight_lookup,u_local_weights,
            u_copy_weights,&group_weight_sums,&local_row_weights,&row_copy_weights,stats,expected_counts_capacity,
            rounds,v_local.capacity(),point_capacity,0,None,None,0)?;
        peak=peak.max(live);
        if live>MAX_INCREMENTAL_CACHE_STATE_BYTES{return Err("grouped V local rounds exceed 512 MiB state cap".into());}
    }
    stats.local_rounds=v_local.len();stats.local_v_elapsed_ns=elapsed_nanos(local_started);
    stats.group_d_local_contributions.clear();
    stats.group_d_local_contributions.try_reserve_exact(banks.len())
        .map_err(|_|"grouped V D-statistics reservation failed")?;
    for (group,bank) in banks.iter().enumerate(){
        stats.group_d_local_contributions.push(group_weight_sums[group]*bank.d[0]);
    }
    let live=grouped_v_total_capacity_bytes(admission,&templates,&banks,row_weight_lookup,u_local_weights,
        u_copy_weights,&group_weight_sums,&local_row_weights,&row_copy_weights,stats,expected_counts_capacity,
        rounds,v_local.capacity(),point_capacity,0,None,None,0)?;
    peak=peak.max(live);
    if live>MAX_INCREMENTAL_CACHE_STATE_BYTES{return Err("grouped V retained statistics exceed 512 MiB state cap".into());}
    phase_mark("v_local_done")?;

    let mut group_c0=Vec::new();let mut group_d0=Vec::new();
    for group_values in [&mut group_c0,&mut group_d0]{
        group_values.try_reserve_exact(banks.len()).map_err(|_|"grouped V group handoff reservation failed")?;
    }
    for bank in &banks{group_c0.push(bank.c[0]);group_d0.push(bank.d[0]);}
    let live=grouped_v_total_capacity_bytes(admission,&templates,&banks,row_weight_lookup,u_local_weights,
        u_copy_weights,&group_weight_sums,&local_row_weights,&row_copy_weights,stats,expected_counts_capacity,
        rounds,v_local.capacity(),point_capacity,0,Some([group_c0.capacity(),group_d0.capacity()]),None,0)?;
    peak=peak.max(live);
    if live>MAX_INCREMENTAL_CACHE_STATE_BYTES{return Err("grouped V group handoff exceeds 512 MiB state cap".into());}
    drop(banks);
    let handoff_started=std::time::Instant::now();
    let mut high_c=Vec::new();let mut high_d=Vec::new();let mut high_x=Vec::new();
    for vector in [&mut high_c,&mut high_d,&mut high_x]{
        vector.try_reserve_exact(copies).map_err(|_|"grouped V owner handoff reservation failed")?;
    }
    for copy in 0..copies{
        let group=admission.group_by_copy[copy];let lambda=row_copy_weights.at(copy)*u_copy_weights[copy];
        high_c.push(lambda*group_c0[group]);high_d.push(lambda*group_d0[group]);
        let mut local_input=read_copy(&mut load_copy,copy,width)?;
        for challenge in &v_local{gkr::fold(&mut local_input,*challenge);}
        high_x.push(local_input[0]);
        let live=grouped_v_total_capacity_bytes(admission,&templates,&Vec::new(),row_weight_lookup,u_local_weights,
            u_copy_weights,&group_weight_sums,&local_row_weights,&row_copy_weights,stats,expected_counts_capacity,
            rounds,v_local.capacity(),point_capacity,local_input.capacity(),Some([group_c0.capacity(),group_d0.capacity()]),
            Some([high_c.capacity(),high_d.capacity(),high_x.capacity()]),0)?;
        peak=peak.max(live);
        if live>MAX_INCREMENTAL_CACHE_STATE_BYTES{return Err("grouped V owner handoff exceeds 512 MiB state cap".into());}
    }
    stats.grouped_state_peak_capacity_bytes=stats.grouped_state_peak_capacity_bytes.max(peak);
    // prove_phase clones X and may grow its point and the retained round list.
    // Reserve a conservative checked allowance before those allocations occur.
    let high_scratch=copies.checked_add(2*copy_bits).and_then(|n|n.checked_add(3*copy_bits))
        .ok_or("grouped V high scratch overflow")?;
    let round_growth=rounds.capacity().checked_add(copy_bits).and_then(|n|n.checked_mul(2))
        .and_then(|n|n.checked_mul(std::mem::size_of::<Vec<Fr>>())).ok_or("grouped V high round growth overflow")?;
    let high_peak=grouped_v_total_capacity_bytes(admission,&templates,&Vec::new(),row_weight_lookup,u_local_weights,
        u_copy_weights,&group_weight_sums,&local_row_weights,&row_copy_weights,stats,expected_counts_capacity,
        rounds,v_local.capacity(),point_capacity,0,Some([group_c0.capacity(),group_d0.capacity()]),
        Some([high_c.capacity(),high_d.capacity(),high_x.capacity()]),high_scratch)?
        .checked_add(round_growth).ok_or("grouped V high allocation peak overflow")?;
    peak=peak.max(high_peak);
    if high_peak>MAX_INCREMENTAL_CACHE_STATE_BYTES{return Err("grouped V high scratch exceeds 512 MiB state cap".into());}
    let (v_high,right_value)=gkr::prove_phase(high_c,high_d,&high_x,claim,rounds,transcript).map_err(|error|error.to_string())?;
    let live=grouped_v_total_capacity_bytes(admission,&templates,&Vec::new(),row_weight_lookup,u_local_weights,
        u_copy_weights,&group_weight_sums,&local_row_weights,&row_copy_weights,stats,expected_counts_capacity,
        rounds,v_local.capacity(),point_capacity,0,Some([group_c0.capacity(),group_d0.capacity()]),
        Some([0,0,high_x.capacity()]),v_high.capacity())?;
    peak=peak.max(live);
    if live>MAX_INCREMENTAL_CACHE_STATE_BYTES{return Err("grouped V high phase exceeds 512 MiB state cap".into());}
    drop(high_x);
    stats.owner_handoff_count=copies;stats.owner_handoff_elapsed_ns=elapsed_nanos(handoff_started);
    phase_mark("v_handoff_done")?;
    let mut v=v_local.clone();v.extend(v_high);
    let terminal_scratch=v.capacity();
    let live=grouped_v_total_capacity_bytes(admission,&templates,&Vec::new(),row_weight_lookup,u_local_weights,
        u_copy_weights,&group_weight_sums,&local_row_weights,&row_copy_weights,stats,expected_counts_capacity,
        rounds,v_local.capacity(),point_capacity,0,Some([group_c0.capacity(),group_d0.capacity()]),None,terminal_scratch)?;
    peak=peak.max(live);
    if live>MAX_INCREMENTAL_CACHE_STATE_BYTES{return Err("grouped V terminal rounds exceed 512 MiB state cap".into());}
    let coefficients=wiring(r,u,&v)?;
    if coefficients[0]+coefficients[1]*left_value+coefficients[2]*right_value
        +coefficients[3]*left_value*right_value!=*claim{return Err(GkrError::TerminalExpression.to_string());}
    phase_mark("terminal_wiring_done")?;

    phase_mark("line_start")?;
    let mut line=vec![Fr::zero();input_bits+copy_bits+1];
    for copy in 0..copies{
        let local_input=read_copy(&mut load_copy,copy,width)?;
        // line_polynomial's table and next overlap. Their combined field
        // length is at most 2*width (first fold); subsequent folds shrink.
        let line_scratch=width.checked_mul(2).and_then(|n|n.checked_add(line.capacity()))
            .and_then(|n|n.checked_add(terminal_scratch)).ok_or("grouped V line preflight overflow")?;
        let line_peak=grouped_v_total_capacity_bytes(admission,&templates,&Vec::new(),row_weight_lookup,u_local_weights,
            u_copy_weights,&group_weight_sums,&local_row_weights,&row_copy_weights,stats,expected_counts_capacity,
            rounds,v_local.capacity(),point_capacity,local_input.capacity(),Some([group_c0.capacity(),group_d0.capacity()]),
            None,line_scratch)?;
        peak=peak.max(line_peak);
        if line_peak>MAX_INCREMENTAL_CACHE_STATE_BYTES{return Err("grouped V line scratch exceeds 512 MiB state cap".into());}
        let local=gkr::line_polynomial(&local_input,&u[..input_bits],&v_local);
        let selector=copy_line_selector(copy,&u[input_bits..],&v[input_bits..]);
        let products=multiply(&local,&selector);
        for (sum,value) in line.iter_mut().zip(&products){*sum+=*value;}
        let closure_scratch=local.capacity().checked_add(selector.capacity()).and_then(|n|n.checked_add(products.capacity()))
            .ok_or("grouped V terminal scratch overflow")?;
        let terminal_scratch=terminal_scratch.checked_add(closure_scratch).ok_or("grouped V terminal scratch overflow")?;
        let live=grouped_v_total_capacity_bytes(admission,&templates,&Vec::new(),row_weight_lookup,u_local_weights,
            u_copy_weights,&group_weight_sums,&local_row_weights,&row_copy_weights,stats,expected_counts_capacity,
            rounds,v_local.capacity(),point_capacity,local_input.capacity(),Some([group_c0.capacity(),group_d0.capacity()]),None,
            terminal_scratch.checked_add(line.capacity()).ok_or("grouped V line scratch overflow")?)?;
        peak=peak.max(live);
        if live>MAX_INCREMENTAL_CACHE_STATE_BYTES{return Err("grouped V terminal owner line exceeds 512 MiB state cap".into());}
    }
    stats.grouped_state_peak_capacity_bytes=stats.grouped_state_peak_capacity_bytes.max(peak);
    phase_mark("line_done")?;
    if line[0]!=left_value||gkr::eval_polynomial(&line,Fr::one())!=right_value{return Err(GkrError::LineEndpoints.to_string());}
    transcript.append_scalar(b"gkr-left-value",&left_value);transcript.append_scalar(b"gkr-right-value",&right_value);
    gkr::append_polynomial(transcript,b"gkr-line-polynomial",&line);
    let challenge=transcript.challenge_scalar(b"gkr-line-challenge");
    let point=gkr::line_point(u,&v,challenge);let value=gkr::eval_polynomial(&line,challenge);
    Ok((GkrProof{layers:vec![LayerProof{rounds:std::mem::take(rounds),left_value,right_value,line_coefficients:line}]},
        InputClaim{point,value}))
}

/// Runtime-internal cross-slot endpoint producer. Its callbacks must replay
/// the same immutable relation for the baseline, sumcheck, and terminal pass.
#[derive(Clone)]
pub(crate) struct EdgeTerm {pub(crate) source_slot:usize,pub(crate) family_row:usize,pub(crate) term:Term}

/// Occurrence identity is retained even when several demands name one X bit.
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) enum C514DemandSide { Right, LeftEven, LeftOdd }
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) struct C514Demand {
    pub(crate) term_index:usize,
    pub(crate) side:C514DemandSide,
    pub(crate) coordinate:usize,
}
#[derive(Clone,Debug,Default)]
pub(crate) struct C514Metrics {
    pub(crate) term_visits:usize,
    pub(crate) demands:usize,
    pub(crate) unique_coordinates:usize,
    pub(crate) loads:usize,
    pub(crate) duplicate_loads:usize,
    pub(crate) left_slots:usize,
    pub(crate) demand_capacity:usize,
    pub(crate) coordinate_capacity:usize,
    pub(crate) value_capacity:usize,
    pub(crate) left_slot_capacity:usize,
    pub(crate) capacity_bytes:usize,
}

/// First U-round contribution of one selected source ROW owner, not a GKR proof.
/// `qualify` must authenticate every occurrence against the caller's typed ROW
/// provenance and live physical authors. `read` must revisit those same authors.
/// No arithmetic or X reads occur until the complete demand list is qualified.
pub(crate) fn c514_selected_u0_contribution(
    terms:&[EdgeTerm],r:&[Fr],input_bits:usize,slot_bits:usize,base_row_bits:usize,
    family_bits:usize,member_row_bits:&[usize],
    mut qualify:impl FnMut(&[C514Demand])->Result<(),String>,
    mut read:impl FnMut(usize)->Result<bool,String>,
)->Result<([Fr;3],C514Metrics),String>{
    let word_bits=usize::BITS as usize;
    let input_dimension=input_bits.checked_add(slot_bits).ok_or("C514 input dimension overflow")?;
    let row_dimension=base_row_bits.checked_add(slot_bits).and_then(|n|n.checked_add(family_bits))
        .ok_or("C514 row dimension overflow")?;
    if input_bits==0 || input_dimension>=word_bits || row_dimension>=word_bits
        || r.len()!=row_dimension || member_row_bits.is_empty()
        || member_row_bits.len()>1usize<<family_bits
        || member_row_bits.iter().any(|&n|n>base_row_bits) {
        return Err("C514 geometry".into());
    }
    let selected=terms.first().ok_or("C514 selected ROW is empty")?.source_slot;
    let width=1usize<<input_bits;
    let input_len=1usize<<input_dimension;
    let max_demands=terms.len().checked_mul(3).ok_or("C514 demand count overflow")?;
    let mut demands=Vec::new();
    demands.try_reserve_exact(max_demands).map_err(|_|"C514 demand allocation")?;
    let mut left_slots=Vec::new();
    left_slots.try_reserve_exact(terms.len()).map_err(|_|"C514 slot allocation")?;
    // Compile solely from coefficients: cancellation, zero weights and authored
    // zero values cannot erase an active source or its left-pair neighbour.
    for (term_index,edge) in terms.iter().enumerate(){
        if edge.source_slot!=selected {return Err("C514 mixed source ROW owners".into());}
        let row=global_edge_row(edge.source_slot,edge.family_row,slot_bits,base_row_bits,
            family_bits,member_row_bits)?;
        if edge.term.row!=row {return Err(format!("C514 global ROW mismatch at term {term_index}"));}
        let g=&edge.term.gate;
        if g.left>=input_len || g.right>=input_len {return Err("C514 wire geometry".into());}
        left_slots.push(g.left/width);
        if !g.c2.is_zero() || !g.c3.is_zero(){
            demands.push(C514Demand{term_index,side:C514DemandSide::Right,coordinate:g.right});
        }
        if !g.c1.is_zero() || !g.c3.is_zero(){
            let even=g.left&!1;
            demands.push(C514Demand{term_index,side:C514DemandSide::LeftEven,coordinate:even});
            demands.push(C514Demand{term_index,side:C514DemandSide::LeftOdd,coordinate:even+1});
        }
    }
    qualify(&demands)?;
    left_slots.sort_unstable();left_slots.dedup();
    let mut coordinates=Vec::new();
    coordinates.try_reserve_exact(demands.len()).map_err(|_|"C514 coordinate allocation")?;
    coordinates.extend(demands.iter().map(|d|d.coordinate));
    coordinates.sort_unstable();coordinates.dedup();
    let mut values:Vec<Option<bool>>=Vec::new();
    values.try_reserve_exact(coordinates.len()).map_err(|_|"C514 value allocation")?;
    values.resize(coordinates.len(),None);
    let mut metrics=C514Metrics{
        term_visits:terms.len(),demands:demands.len(),unique_coordinates:coordinates.len(),
        left_slots:left_slots.len(),demand_capacity:demands.capacity(),
        coordinate_capacity:coordinates.capacity(),value_capacity:values.capacity(),
        left_slot_capacity:left_slots.capacity(),..Default::default()
    };
    metrics.capacity_bytes=[
        demands.capacity().checked_mul(std::mem::size_of::<C514Demand>()),
        coordinates.capacity().checked_mul(std::mem::size_of::<usize>()),
        values.capacity().checked_mul(std::mem::size_of::<Option<bool>>()),
        left_slots.capacity().checked_mul(std::mem::size_of::<usize>()),
    ].into_iter().try_fold(0usize,|sum,n|sum.checked_add(n?)).ok_or("C514 capacity overflow")?;
    for demand in &demands {
        let value=read(demand.coordinate).map_err(|reason|format!(
            "C514 read failure at term {} side {:?} coordinate {}: {reason}",
            demand.term_index,demand.side,demand.coordinate))?;
        metrics.loads+=1;
        let index=coordinates.binary_search(&demand.coordinate).map_err(|_|"C514 demand lookup")?;
        if let Some(previous)=values[index]{
            metrics.duplicate_loads+=1;
            if previous!=value {return Err(format!("C514 contradictory value at coordinate {}",demand.coordinate));}
        }else{values[index]=Some(value);}
    }
    let value=|coordinate:usize|->Result<Fr,String>{
        let index=coordinates.binary_search(&coordinate).map_err(|_|"C514 missing demanded coordinate")?;
        Ok(Fr::from(values[index].ok_or("C514 unloaded demanded coordinate")? as u64))
    };
    let mut polynomial=[Fr::zero();3];
    for edge in terms {
        let g=&edge.term.gate;
        let right=if !g.c2.is_zero() || !g.c3.is_zero(){value(g.right)?}else{Fr::zero()};
        let (x,delta)=if !g.c1.is_zero() || !g.c3.is_zero(){
            let even=g.left&!1;let x=value(even)?;(x,value(even+1)?-x)
        }else{(Fr::zero(),Fr::zero())};
        let a=g.c1+g.c3*right;
        let constant=a*x+g.c0+g.c2*right;
        let slope=a*delta;
        let weight=eq_weight_at(r,edge.term.row);
        if g.left&1==0 {
            polynomial[0]+=weight*constant;
            polynomial[1]+=weight*(slope-constant);
            polynomial[2]-=weight*slope;
        }else{
            polynomial[1]+=weight*constant;
            polynomial[2]+=weight*slope;
        }
    }
    Ok((polynomial,metrics))
}

pub(crate) fn global_edge_row(source_slot:usize,family_row:usize,slot_bits:usize,base_row_bits:usize,
    family_bits:usize,member_row_bits:&[usize])->Result<usize,String>{
    let copies=1usize.checked_shl(slot_bits as u32).ok_or("edge slots overflow")?;
    let row_mask=(1usize.checked_shl(base_row_bits as u32).ok_or("edge row width overflow")?)-1;
    let family=family_row>>base_row_bits;let local=family_row&row_mask;
    if source_slot>=copies||family>=member_row_bits.len()
        ||family>=1usize.checked_shl(family_bits as u32).ok_or("edge family width overflow")?
        ||local>=1usize.checked_shl(member_row_bits[family] as u32).ok_or("edge member width overflow")?{
        return Err("edge term row outside family/slot allocation".into());
    }
    let family_shift=base_row_bits.checked_add(slot_bits).ok_or("edge row dimension overflow")?;
    Ok((family<<family_shift)|(source_slot<<member_row_bits[family])|local)
}

fn walk_edge_endpoint<F>(
    visit:&mut F,left:bool,slot:usize,width:usize,copies:usize,base_row_bits:usize,
    member_row_bits:&[usize],expected:Option<usize>,sink:&mut dyn FnMut(EdgeTerm)->Result<(),String>,
)->Result<usize,String>
where F:FnMut(bool,usize,&mut dyn FnMut(EdgeTerm)->Result<(),String>)->Result<(),String>{
    let mut seen=0usize;
    visit(left,slot,&mut |edge|{
        seen=seen.checked_add(1).ok_or("edge endpoint term count overflow")?;
        if expected.is_some_and(|count|seen>count){return Err("edge endpoint source exceeded its baseline count".into());}
        let gate=&edge.term.gate;let endpoint=if left{gate.left}else{gate.right};
        let family=edge.family_row>>base_row_bits;let local=edge.family_row&((1usize<<base_row_bits)-1);
        if edge.source_slot>=copies||family>=member_row_bits.len()
            ||local>=1usize<<member_row_bits[family]||gate.left>=width*copies||gate.right>=width*copies
            ||endpoint/width!=slot{return Err("edge endpoint wire or row outside declared slot".into());}
        sink(edge)
    })?;
    if let Some(count)=expected{if seen!=count{return Err("edge endpoint source count changed between passes".into());}}
    Ok(seen)
}

/// Coefficients for one replayed endpoint slot. X is still a dense streamed
/// copy. Sparse storage is selected only when its checked fold peak is below
/// the two dense coefficient vectors it replaces; this introduces no new cap.
enum EdgeReplayBanks {
    Dense(Vec<Fr>,Vec<Fr>),
    Sparse(SparseFieldVector,SparseFieldVector),
}
impl EdgeReplayBanks {
    fn new(width:usize,terms:usize)->Result<Self,String>{
        let dense_bytes=width.checked_mul(2).and_then(|n|n.checked_mul(std::mem::size_of::<Fr>()));
        // Each bank has at most one entry per term. Include both old/new
        // banks and one rounding entry per bank for sparse_fold's capacity.
        let sparse_peak=terms.checked_add(1).and_then(|n|n.checked_mul(4))
            .and_then(|n|n.checked_mul(std::mem::size_of::<(usize,Fr)>()));
        if sparse_peak.zip(dense_bytes).is_some_and(|(s,d)|s<d){
            let mut a=Vec::new();let mut b=Vec::new();
            a.try_reserve_exact(terms).map_err(|_|"edge replay sparse A/C reservation failed")?;
            b.try_reserve_exact(terms).map_err(|_|"edge replay sparse B/D reservation failed")?;
            let actual_peak=a.capacity().checked_add(1)
                .and_then(|n|b.capacity().checked_add(1).and_then(|m|n.checked_add(m)))
                .and_then(|n|n.checked_mul(2))
                .and_then(|n|n.checked_mul(std::mem::size_of::<(usize,Fr)>()));
            if actual_peak.zip(dense_bytes).is_some_and(|(s,d)|s<d){return Ok(Self::Sparse(a,b));}
            // Allocator capacity must also fit before any accumulation.
            drop(a);drop(b);
        }
        Ok(Self::Dense(vec![Fr::zero();width],vec![Fr::zero();width]))
    }
    fn add(&mut self,wire:usize,a_value:Fr,b_value:Fr){
        match self{
            Self::Dense(a,b)=>{a[wire]+=a_value;b[wire]+=b_value;},
            Self::Sparse(a,b)=>{
                if !a_value.is_zero(){a.push((wire,a_value));}
                if !b_value.is_zero(){b.push((wire,b_value));}
            },
        }
    }
    fn coalesce(&mut self){if let Self::Sparse(a,b)=self{
        coalesce_nonzero_in_place(a);coalesce_nonzero_in_place(b);
    }}
    fn fold(&mut self,challenge:Fr){match self{
        Self::Dense(a,b)=>{gkr::fold(a,challenge);gkr::fold(b,challenge);},
        Self::Sparse(a,b)=>{*a=sparse_fold(a,challenge);*b=sparse_fold(b,challenge);},
    }}
    fn message(&self,x:&[Fr])->Vec<Fr>{match self{
        Self::Dense(a,b)=>gkr::quadratic_message(a,b,x),
        Self::Sparse(a,b)=>sparse_quadratic_message(a,b,x).to_vec(),
    }}
    fn terminal(&self)->(Fr,Fr){match self{
        Self::Dense(a,b)=>(a[0],b[0]),
        Self::Sparse(a,b)=>(sparse_value(a,0),sparse_value(b,0)),
    }}
}

// The same replay kernel serves local-round and terminal fallback callers.
// Incremental state and the production cache lifetime stay with their callers.
struct EdgeReplayState {
    banks:EdgeReplayBanks,x:Vec<Fr>,
    #[cfg(test)] metrics:EdgeFallbackMetrics,
}
#[cfg(test)]
#[derive(Default,Clone)]
pub(crate) struct EdgeFallbackMetrics {
    pub visits:u64,pub cache_gets:u64,pub vector_clones:u64,pub replay_folds:u64,
    pub x_fold_fields:u64,pub bank_fold_entries:u64,pub bank_capacity_peak_bytes:usize,
    pub fold_ns:u64,
    pub cache_capacity_peak_bytes:usize,pub dense:bool,
}
#[cfg(test)]
impl EdgeReplayBanks {
    fn storage_bound(&self)->usize {match self {
        Self::Dense(a,b)=>(a.capacity()+b.capacity())*std::mem::size_of::<Fr>(),
        // Includes old and newly allocated sparse fold vectors. sparse_fold's
        // output capacity is at most twice its input length plus two entries.
        Self::Sparse(a,b)=>(a.capacity()+b.capacity()+2)*3*std::mem::size_of::<(usize,Fr)>(),
    }}
    fn entries(&self)->usize {match self {Self::Dense(a,b)=>a.len()+b.len(),Self::Sparse(a,b)=>a.len()+b.len()}}
}
fn edge_replay_fold(mut banks:EdgeReplayBanks,mut x:Vec<Fr>,prefix:&[Fr],
    #[cfg(test)] mut metrics:EdgeFallbackMetrics,
)->EdgeReplayState {
    #[cfg(test)] {metrics.bank_capacity_peak_bytes=banks.storage_bound();metrics.dense=matches!(&banks,EdgeReplayBanks::Dense(..));}
    #[cfg(test)] let fold_started=std::time::Instant::now();
    for challenge in prefix {
        #[cfg(test)] {metrics.replay_folds+=1;metrics.x_fold_fields+=x.len() as u64;
            metrics.bank_fold_entries+=banks.entries() as u64;}
        banks.fold(*challenge);gkr::fold(&mut x,*challenge);
        #[cfg(test)] {metrics.bank_capacity_peak_bytes=metrics.bank_capacity_peak_bytes.max(banks.storage_bound());}
    }
    #[cfg(test)] {metrics.fold_ns=if prefix.is_empty(){0}else{u64::try_from(fold_started.elapsed().as_nanos()).unwrap_or(u64::MAX)};}
    EdgeReplayState{banks,x,#[cfg(test)] metrics}
}
#[derive(Clone,Copy)]
pub(crate) struct EdgeFullEvent{pub stage:&'static str,pub event:u8,pub round:usize,pub owners:usize,pub terms:u64}
fn full_mark(observe:&mut impl FnMut(EdgeFullEvent)->Result<(),String>,stage:&'static str,event:u8,round:usize,owners:usize,terms:u64)->Result<(),String>{
    observe(EdgeFullEvent{stage,event,round,owners,terms})
}
// Packed-only line strategy; arbitrary-field inputs keep the original branch.
#[derive(Default,Clone,Debug,PartialEq,Eq)]
pub(crate) struct PackedLineStats{
    pub builds:u64,pub owners:u64,pub coefficients:u64,pub input_expanded_fields:u64,
    pub lut_fields:usize,pub work_fields:usize,pub result_fields:usize,
    pub plan_reserved_bytes:usize,pub plan_actual_bytes:usize,pub extra_reserved_bytes:usize,pub component_bound:usize,
    pub build_ns:u64,pub apply_ns:u64,pub whole_ns:u64,
}
pub(crate) struct PackedLinePlan{
    width:usize,m:usize,u:[Fr;20],v:[Fr;20],lut:Vec<[Fr;4]>,work:Vec<Fr>,accounted:usize,
}
fn packed_line_add(a:usize,b:usize)->Result<usize,String>{a.checked_add(b).ok_or("packed line capacity arithmetic".into())}
fn packed_line_fields(n:usize)->Result<usize,String>{n.checked_mul(std::mem::size_of::<Fr>()).ok_or("packed line capacity arithmetic".into())}
fn packed_line_capacity(actual:usize,expected:usize)->Result<(),String>{
    if actual!=expected{return Err("packed line actual capacity".into());}Ok(())
}
fn packed_line_geometry(width:usize,m:usize)->Result<(),String>{
    if !(8..=1<<20).contains(&width)||!width.is_power_of_two()||m!=width.trailing_zeros()as usize{
        return Err("packed line geometry".into());}Ok(())
}
fn packed_line_plan_bound(width:usize,m:usize)->Result<usize,String>{
    packed_line_geometry(width,m)?;
    [packed_line_fields(1024)?,packed_line_fields(width/2)?,packed_line_fields(42)?,
        packed_line_fields(m+1)?,std::mem::size_of::<Vec<Fr>>(),packed_line_fields(40)?]
        .into_iter().try_fold(std::mem::size_of::<PackedLinePlan>(),packed_line_add)
}
fn packed_line_extra_charge()->Result<usize,String>{
    let option=std::mem::size_of::<Option<PackedLinePlan>>().checked_sub(std::mem::size_of::<PackedLinePlan>())
        .ok_or("packed line option capacity")?;
    let tuple=std::mem::size_of::<Result<(Vec<Fr>,u64),String>>().checked_sub(std::mem::size_of::<Vec<Fr>>())
        .ok_or("packed line tuple capacity")?;
    [std::mem::size_of::<PackedLineStats>(),std::mem::size_of::<Option<&mut PackedLineStats>>(),
        tuple,option,std::mem::size_of::<[std::time::Instant;2]>(),32768].into_iter().try_fold(0,packed_line_add)
}
fn packed_line_extra_with_limit(limit:usize)->Result<usize,String>{
    if packed_line_extra_charge()?>limit{return Err("packed line extra reservation".into());}Ok(limit)
}
fn packed_line_extra()->Result<usize,String>{packed_line_extra_with_limit(33024)}
#[cfg(test)]
pub(crate) fn packed_line52_reservation_for_test(metadata:usize)->Result<(usize,usize,usize),String>{
    let plan=packed_line_plan_bound(1<<20,20)?;let extra=packed_line_extra()?;
    let bound=[metadata,plan,extra].into_iter().try_fold(257565696usize,packed_line_add)?;
    if bound>512*1024*1024{return Err("historical52 component bound".into());}Ok((bound,plan,extra))
}
fn packed_line_preflight(input:&impl EdgeInput,width:usize,copies:usize,limit:usize)->Result<(usize,usize,usize),String>{
    if !input.supports_packed_line(){return Err("packed line unsupported input".into());}
    let m=width.trailing_zeros()as usize;packed_line_geometry(width,m)?;
    if copies==0||copies>4096||!copies.is_power_of_two(){return Err("packed line copies".into());}
    let plan=packed_line_plan_bound(width,m)?;
    let packets=(width/8).checked_mul(4).ok_or("packed line capacity arithmetic")?;
    let metadata=input.cache_budget_bytes()?.checked_sub(packets).ok_or("packed line cache metadata")?;
    let extra=packed_line_extra()?;
    let bound=[metadata,plan,extra].into_iter().try_fold(257565696usize,packed_line_add)?;
    if limit>512*1024*1024||bound>limit{return Err("packed line component bound".into());}
    Ok((bound,plan,extra))
}
impl PackedLinePlan{
    fn new(width:usize,u:&[Fr],v:&[Fr],limit:usize)->Result<Self,String>{
        let m=width.trailing_zeros()as usize;packed_line_geometry(width,m)?;
        if u.len()!=m||v.len()!=m{return Err("packed line points".into());}
        let accounted=packed_line_plan_bound(width,m)?;
        if accounted>limit{return Err("packed line plan bound".into());}
        let mut lut=Vec::<[Fr;4]>::new();lut.try_reserve_exact(256).map_err(|_|"packed line LUT allocation")?;
        packed_line_capacity(lut.capacity(),256)?;
        let mut work=Vec::new();work.try_reserve_exact(width/2).map_err(|_|"packed line work allocation")?;
        packed_line_capacity(work.capacity(),width/2)?;
        let mut basis=[[Fr::zero();4];8];
        for mask in 0..8{
            let mut p=[Fr::zero();4];p[0]=Fr::one();
            for i in 0..3{
                let(a,b)=if(mask>>i)&1==1{(u[i],v[i]-u[i])}else{(Fr::one()-u[i],u[i]-v[i])};
                let mut next=[Fr::zero();4];for d in 0..=i{next[d]+=p[d]*a;next[d+1]+=p[d]*b;}p=next;
            }basis[mask]=p;
        }
        lut.push([Fr::zero();4]);for mask in 1usize..256{
            let mut p=lut[mask&(mask-1)];let bit=mask.trailing_zeros()as usize;
            for d in 0..4{p[d]+=basis[bit][d];}lut.push(p);
        }
        let mut pu=[Fr::zero();20];let mut pv=pu;pu[..m].copy_from_slice(u);pv[..m].copy_from_slice(v);
        Ok(Self{width,m,u:pu,v:pv,lut,work,accounted})
    }
    fn apply(&mut self,packed:&[u8])->Result<Vec<Fr>,String>{
        if packed.len()!=self.width/8{return Err("packed line extent".into());}
        packed_line_capacity(self.lut.capacity(),256)?;packed_line_capacity(self.work.capacity(),self.width/2)?;
        if self.accounted!=packed_line_plan_bound(self.width,self.m)?{return Err("packed line plan bound".into());}
        self.work.resize(self.width/2,Fr::zero());
        for(j,byte)in packed.iter().enumerate(){self.work[j*4..j*4+4].copy_from_slice(&self.lut[*byte as usize]);}
        let mut entries=self.width/8;
        for i in 3..self.m{packed_line_tail(&mut self.work,entries,i,self.u[i],self.v[i]-self.u[i],false)?;entries/=2;}
        if entries!=1||self.work.len()!=self.m+1{return Err("packed line polynomial extent".into());}
        let out=self.work.to_vec();packed_line_capacity(out.capacity(),self.m+1)?;Ok(out)
    }
}
fn packed_line_tail(work:&mut Vec<Fr>,entries:usize,i:usize,u:Fr,delta:Fr,alias_fault:bool)->Result<(),String>{
    let stride=i.checked_add(1).ok_or("packed line capacity arithmetic")?;
    let next=i.checked_add(2).ok_or("packed line capacity arithmetic")?;
    if i>=20||entries<2||entries%2!=0||entries.checked_mul(stride)!=Some(work.len()){
        return Err("packed line tail geometry".into());}
    let mut left=[Fr::zero();21];let mut right=left;
    for pair in 0..entries/2{
        let lo=pair*2*stride;let hi=lo+stride;let out=pair*next;
        if !alias_fault{left[..stride].copy_from_slice(&work[lo..lo+stride]);right[..stride].copy_from_slice(&work[hi..hi+stride]);}
        work[out..out+next].fill(Fr::zero());
        for d in 0..stride{
            let(a,b)=if alias_fault{(work[lo+d],work[hi+d])}else{(left[d],right[d])};let difference=b-a;
            work[out+d]+=a+u*difference;work[out+d+1]+=delta*difference;
        }
    }work.truncate(entries/2*next);Ok(())
}

#[derive(Default)]
pub(crate) struct EdgeFullStats{
    pub term_callbacks:u64,pub owner_requests:u64,pub emitted_fields:u64,pub prefix_plans:u64,pub suffix_tables:u64,pub pattern_tables:u64,
    pub sequential_x_folds:u64,pub sequential_bank_folds:u64,pub input_vector_clones:u64,pub line_internal_clones:u64,pub line_cloned_fields:u64,
    pub prefix_full:usize,pub prefix_suffix:usize,pub prefix_patterns:usize,pub prefix_metadata:usize,pub banks:usize,pub x:usize,
    pub row_lookup:usize,pub u_weights:usize,pub owner_weights:usize,
    pub prefix_build_ns:u64,pub message_ns:u64,pub line_ns:u64,pub census_ns:[u64;2],pub high_ns:[u64;2],pub pass_ns:Vec<u64>,
    pub left_counts:Vec<usize>,pub right_counts:Vec<usize>,
}
impl EdgeFullStats{
    fn add(a:u64,b:u64)->Result<u64,String>{a.checked_add(b).ok_or("edge full counter overflow".into())}
    fn ns(start:std::time::Instant)->Result<u64,String>{u64::try_from(start.elapsed().as_nanos()).map_err(|_|"edge full clock overflow".into())}
    fn plan(&mut self,width:usize,prefix:&[Fr])->Result<EdgePrefixPlan,String>{
        let began=std::time::Instant::now();let p=EdgePrefixPlan::new(width,prefix)?;
        self.prefix_build_ns=Self::add(self.prefix_build_ns,Self::ns(began)?)?;
        self.prefix_plans=Self::add(self.prefix_plans,1)?;
        if p.k>=3{self.suffix_tables=Self::add(self.suffix_tables,1)?;}
        if p.k>0{self.pattern_tables=Self::add(self.pattern_tables,1)?;}
        self.prefix_full=self.prefix_full.max(p.weights.capacity()*std::mem::size_of::<Fr>());
        self.prefix_suffix=self.prefix_suffix.max(p.suffix.capacity()*std::mem::size_of::<Fr>());
        self.prefix_patterns=self.prefix_patterns.max(p.patterns.capacity()*std::mem::size_of::<Fr>());
        self.prefix_metadata=std::mem::size_of::<EdgePrefixPlan>();Ok(p)
    }
    fn state(&mut self,state:&EdgeReplayState,count:usize,direct:bool,k:usize,input:&impl EdgeInput)->Result<(),String>{
        self.term_callbacks=Self::add(self.term_callbacks,count as u64)?;
        self.owner_requests=Self::add(self.owner_requests,1)?;
        self.emitted_fields=Self::add(self.emitted_fields,(if direct{state.x.len()}else{input.width()})as u64)?;
        self.banks=self.banks.max(state.banks.direct_bound()?);
        self.x=self.x.max(state.x.capacity().checked_mul(std::mem::size_of::<Fr>()).ok_or("edge full X overflow")?);
        if !direct{self.sequential_x_folds=Self::add(self.sequential_x_folds,k as u64)?;
            self.sequential_bank_folds=Self::add(self.sequential_bank_folds,k as u64)?;}
        #[cfg(test)] {self.input_vector_clones=Self::add(self.input_vector_clones,input.vector_clone_increment())?;}
        Ok(())
    }
}
impl EdgeReplayBanks{
    fn direct_bound(&self)->Result<usize,String>{match self{
        Self::Dense(a,b)=>a.capacity().checked_add(b.capacity()).and_then(|n|n.checked_mul(std::mem::size_of::<Fr>())),
        Self::Sparse(a,b)=>a.capacity().checked_add(b.capacity()).and_then(|n|n.checked_add(2))
            .and_then(|n|n.checked_mul(3)).and_then(|n|n.checked_mul(std::mem::size_of::<(usize,Fr)>())),
    }.ok_or("edge full bank capacity overflow".into())}
}
fn direct_preflight(input:&impl EdgeInput,width:usize,copies:usize)->Result<(),String>{
    if width==0||!width.is_power_of_two()||width>1<<20||copies==0||copies>4096{return Err("edge direct geometry".into());}
    let bound=[36usize*1024*1024+8192+1024,input.cache_budget_bytes()?,
        width.checked_mul(32).ok_or("edge direct loader overflow")?,width.checked_mul(160).ok_or("edge direct state overflow")?,
        1024*1024,copies.checked_mul(32).ok_or("edge direct owners overflow")?,16*1024*1024]
        .into_iter().try_fold(0usize,|a,b|a.checked_add(b)).ok_or("edge direct capacity overflow")?;
    if bound>512*1024*1024{return Err("edge direct component bound".into());}Ok(())
}
fn edge_replay_direct<F,I,W>(visit:&mut F,input:&mut I,left:bool,slot:usize,width:usize,copies:usize,
    base_row_bits:usize,member_row_bits:&[usize],count:usize,row_weight:&W,
    u_slot_weights:&[Fr],u_local_weights:&[Fr],left_value:Fr,plan:&EdgePrefixPlan,
)->Result<EdgeReplayState,String>
where F:FnMut(bool,usize,&mut dyn FnMut(EdgeTerm)->Result<(),String>)->Result<(),String>,I:EdgeInput,W:Fn(&EdgeTerm)->Result<Fr,String>{
    if plan.width!=width{return Err("edge direct plan width".into());}
    if !left&&(u_slot_weights.len()!=copies||u_local_weights.len()!=width){return Err("edge direct U weight shape".into());}
    let mut banks=EdgeReplayBanks::new(plan.reduced(),count)?;
    walk_edge_endpoint(visit,left,slot,width,copies,base_row_bits,member_row_bits,Some(count),&mut |edge|{
        let g=&edge.term.gate;let row=row_weight(&edge)?;
        if left{let wire=g.left%width;let right=edge_input_value(input,g.right/width,g.right%width)?;
            let weight=row*plan.weight(wire);banks.add(wire>>plan.k,weight*(g.c1+g.c3*right),weight*(g.c0+g.c2*right));}
        else{let wire=g.right%width;let weight=row*u_slot_weights[g.left/width]*u_local_weights[g.left%width]*plan.weight(wire);
            banks.add(wire>>plan.k,weight*(g.c2+g.c3*left_value),weight*(g.c0+g.c1*left_value));}Ok(())
    })?;banks.coalesce();let x=input.projected(slot,plan)?;
    if x.len()!=plan.reduced()||x.capacity()!=plan.reduced(){return Err("edge direct projected width/capacity".into());}edge_cache_check(input)?;
    Ok(EdgeReplayState{banks,x,#[cfg(test)] metrics:EdgeFallbackMetrics{visits:count as u64,cache_gets:if left{count as u64+1}else{1},
        vector_clones:input.vector_clone_increment(),cache_capacity_peak_bytes:input.capacity_bytes().ok_or("edge direct cache overflow")?,..Default::default()}})
}

fn edge_replay_u<F,I,W>(visit:&mut F,input:&mut I,slot:usize,width:usize,
    copies:usize,base_row_bits:usize,member_row_bits:&[usize],count:usize,
    row_weight:&W,prefix:&[Fr],
)->Result<EdgeReplayState,String>
where F:FnMut(bool,usize,&mut dyn FnMut(EdgeTerm)->Result<(),String>)->Result<(),String>,
    I:EdgeInput,W:Fn(&EdgeTerm)->Result<Fr,String> {
    let mut banks=EdgeReplayBanks::new(width,count)?;
    walk_edge_endpoint(visit,true,slot,width,copies,base_row_bits,member_row_bits,Some(count),&mut |edge|{
        let gate=&edge.term.gate;let wire=gate.left%width;let weight=row_weight(&edge)?;let right=edge_input_value(input,gate.right/width,gate.right%width)?;
        banks.add(wire,weight*(gate.c1+gate.c3*right),weight*(gate.c0+gate.c2*right));Ok(())
    })?;
    banks.coalesce();
    let x=edge_input_vector(input,slot,width)?;
    Ok(edge_replay_fold(banks,x,prefix,#[cfg(test)] EdgeFallbackMetrics{
        visits:count as u64,cache_gets:count as u64+1,vector_clones:input.vector_clone_increment(),
        cache_capacity_peak_bytes:input.capacity_bytes().ok_or("edge cache byte count overflow")?,
        ..Default::default()}))
}
fn edge_replay_v<F,I,W>(visit:&mut F,input:&mut I,slot:usize,width:usize,
    copies:usize,base_row_bits:usize,member_row_bits:&[usize],count:usize,
    row_weight:&W,u_slot_weights:&[Fr],u_local_weights:&[Fr],left_value:Fr,prefix:&[Fr],
)->Result<EdgeReplayState,String>
where F:FnMut(bool,usize,&mut dyn FnMut(EdgeTerm)->Result<(),String>)->Result<(),String>,
    I:EdgeInput,W:Fn(&EdgeTerm)->Result<Fr,String> {
    let mut banks=EdgeReplayBanks::new(width,count)?;
    walk_edge_endpoint(visit,false,slot,width,copies,base_row_bits,member_row_bits,Some(count),&mut |edge|{
        let gate=&edge.term.gate;let left_slot=gate.left/width;let left_wire=gate.left%width;
        let weight=row_weight(&edge)?*u_slot_weights[left_slot]*u_local_weights[left_wire];
        let wire=gate.right%width;banks.add(wire,weight*(gate.c2+gate.c3*left_value),
            weight*(gate.c0+gate.c1*left_value));Ok(())
    })?;
    banks.coalesce();
    let x=edge_input_vector(input,slot,width)?;
    Ok(edge_replay_fold(banks,x,prefix,#[cfg(test)] EdgeFallbackMetrics{
        visits:count as u64,cache_gets:1,vector_clones:input.vector_clone_increment(),
        cache_capacity_peak_bytes:input.capacity_bytes().ok_or("edge cache byte count overflow")?,
        ..Default::default()}))
}
#[cfg(test)]
pub(crate) struct EdgeFallbackWeightsForTest {
    rows:EqWeightLookup,u_local:Vec<Fr>,u_slot:Vec<Fr>,
}
#[cfg(test)]
impl EdgeFallbackWeightsForTest {
    pub fn new(r:&[Fr],u:&[Fr],input_bits:usize)->Self {
        Self{rows:EqWeightLookup::new(r),u_local:gkr::eq_weights(&u[..input_bits]),
            u_slot:gkr::eq_weights(&u[input_bits..])}
    }
    pub fn capacity_bytes(&self)->usize {
        (self.u_local.capacity()+self.u_slot.capacity()
            +self.rows.chunks.iter().map(|(_,v)|v.capacity()).sum::<usize>())*std::mem::size_of::<Fr>()
            +self.rows.chunks.capacity()*std::mem::size_of::<(usize,Vec<Fr>)>()
    }
}
#[cfg(test)]
pub(crate) struct EdgeFallbackPrefixForTest {
    pub message:Vec<Fr>,pub terminal:(Fr,Fr),pub folded_x:Fr,pub metrics:EdgeFallbackMetrics,
    pub x_capacity_bytes:usize,
}
#[cfg(test)]
pub(crate) fn edge_fallback_prefix_for_test(
    left:bool,slot:usize,input_bits:usize,slot_bits:usize,base_row_bits:usize,family_bits:usize,
    member_row_bits:&[usize],count:usize,weights:&EdgeFallbackWeightsForTest,
    left_value:Fr,prefix:&[Fr],mut visit:impl FnMut(bool,usize,&mut dyn FnMut(EdgeTerm)->Result<(),String>)->Result<(),String>,
    load:impl FnMut(usize)->Result<Vec<Fr>,String>,decoded_x_fault:Option<usize>,
)->Result<EdgeFallbackPrefixForTest,String> {
    let width=1usize.checked_shl(input_bits as u32).ok_or("test edge width")?;
    let copies=1usize.checked_shl(slot_bits as u32).ok_or("test edge copies")?;
    if prefix.len()>input_bits || slot>=copies || member_row_bits.len()>1usize<<family_bits {
        return Err("test edge prefix geometry".into());
    }
    let row_weight=|edge:&EdgeTerm|global_edge_row(edge.source_slot,edge.family_row,slot_bits,
        base_row_bits,family_bits,member_row_bits).map(|row|weights.rows.at(row));
    // Deliberately fresh for EACH call: selected-partition simulated eviction.
    let mut input=CopyCache::new(load,width,4);
    let mut state=if left {
        edge_replay_u(&mut visit,&mut input,slot,width,copies,base_row_bits,member_row_bits,
            count,&row_weight,prefix)?
    } else {
        edge_replay_v(&mut visit,&mut input,slot,width,copies,base_row_bits,member_row_bits,
            count,&row_weight,&weights.u_slot,&weights.u_local,left_value,prefix)?
    };
    if let Some(wire)=decoded_x_fault {
        if !prefix.is_empty() || wire>=width {return Err("test decoded fault boundary".into());}
        state.x[wire]=Fr::one()-state.x[wire];
    }
    let message=if prefix.len()<input_bits {state.banks.message(&state.x)}else{Vec::new()};
    let terminal=state.banks.terminal();let folded_x=state.x[0];
    let x_capacity_bytes=state.x.capacity().checked_mul(std::mem::size_of::<Fr>()).ok_or("test edge X capacity overflow")?;
    Ok(EdgeFallbackPrefixForTest{message,terminal,folded_x,metrics:state.metrics,x_capacity_bytes})
}

/// A cold test component cache that remains alive over every RIGHT owner and
/// both V rounds. This wrapper leaves the production fallback arithmetic intact.
#[cfg(test)]
pub(crate) struct EdgeVPrefixCandidateForTest<L> {
    input:CopyCache<L>,width:usize,copies:usize,
}
#[cfg(test)]
impl<L> EdgeVPrefixCandidateForTest<L>
where L:FnMut(usize)->Result<Vec<Fr>,String> {
    pub(crate) fn new(load:L,width:usize,copies:usize)->Result<Self,String>{
        if width==0 || !width.is_power_of_two() || copies==0 || !copies.is_power_of_two(){
            return Err("V prefix candidate cache geometry".into());
        }
        Ok(Self{input:CopyCache::new(load,width,4),width,copies})
    }
    pub(crate) fn cache_capacity_bytes(&self)->Option<usize>{self.input.capacity_bytes()}
    pub(crate) fn round<F>(
        &mut self,slot_bits:usize,base_row_bits:usize,family_bits:usize,member_row_bits:&[usize],
        right_counts:&[usize],weights:&EdgeFallbackWeightsForTest,left_value:Fr,prefix:&[Fr],
        mut visit:F,mut owner_done:impl FnMut(usize,usize,[Fr;3])->Result<(),String>,
    )->Result<EdgeFallbackMetrics,String>
    where F:FnMut(bool,usize,&mut dyn FnMut(EdgeTerm)->Result<(),String>)->Result<(),String> {
        let input_bits=self.width.trailing_zeros() as usize;
        if right_counts.len()!=self.copies || prefix.len()>=input_bits
            || weights.u_local.len()!=self.width || weights.u_slot.len()!=self.copies || member_row_bits.is_empty()
            || self.input.capacity!=4
            || self.copies!=1usize.checked_shl(slot_bits as u32).ok_or("V prefix copies overflow")? {
            return Err("V prefix candidate round geometry".into());
        }
        let row_weight=|edge:&EdgeTerm|global_edge_row(edge.source_slot,edge.family_row,
            slot_bits,base_row_bits,family_bits,member_row_bits).map(|row|weights.rows.at(row));
        let mut totals=EdgeFallbackMetrics::default();
        for owner in 0..self.copies {
            let state=edge_replay_v(&mut visit,&mut self.input,owner,self.width,self.copies,
                base_row_bits,member_row_bits,right_counts[owner],&row_weight,&weights.u_slot,
                &weights.u_local,left_value,prefix)?;
            let EdgeReplayState{banks,x,metrics}=state;
            let message=banks.message(&x);
            let polynomial:[Fr;3]=message.as_slice().try_into().map_err(|_|"V prefix quadratic message extent")?;
            let expected_x_folds=prefix.iter().enumerate().try_fold(0u64,|sum,(i,_)|{
                sum.checked_add((self.width>>i) as u64).ok_or("V prefix X fold count overflow")
            })?;
            if metrics.visits!=right_counts[owner] as u64 || metrics.vector_clones!=1
                || metrics.cache_gets!=1 || metrics.replay_folds!=prefix.len() as u64
                || metrics.x_fold_fields!=expected_x_folds {
                return Err("V prefix owner metric mismatch".into());
            }
            totals.visits=totals.visits.checked_add(metrics.visits).ok_or("V prefix visits overflow")?;
            totals.cache_gets=totals.cache_gets.checked_add(metrics.cache_gets).ok_or("V prefix gets overflow")?;
            totals.vector_clones=totals.vector_clones.checked_add(metrics.vector_clones).ok_or("V prefix clones overflow")?;
            totals.replay_folds=totals.replay_folds.checked_add(metrics.replay_folds).ok_or("V prefix folds overflow")?;
            totals.x_fold_fields=totals.x_fold_fields.checked_add(metrics.x_fold_fields).ok_or("V prefix X folds overflow")?;
            totals.bank_fold_entries=totals.bank_fold_entries.checked_add(metrics.bank_fold_entries).ok_or("V prefix bank folds overflow")?;
            totals.bank_capacity_peak_bytes=totals.bank_capacity_peak_bytes.max(metrics.bank_capacity_peak_bytes);
            totals.cache_capacity_peak_bytes=totals.cache_capacity_peak_bytes.max(metrics.cache_capacity_peak_bytes);
            totals.fold_ns=totals.fold_ns.checked_add(metrics.fold_ns).ok_or("V prefix fold time overflow")?;
            totals.dense|=metrics.dense;
            owner_done(owner,right_counts[owner],polynomial)?;
        }
        Ok(totals)
    }
}

#[cfg(test)]
pub(crate) struct EdgeGroupedVContextForTest<'c,'a,'p> {
    adapter:&'c crate::native_prefix_auth_plan::Role4EndpointAdapter<'a,'p>,
    binding:crate::native_prefix_auth_plan::Role4EndpointBinding,
    inactive:crate::daa_history_roster::DaaGroupedVContextForTest<'a,'p>,
    weights:EdgeFallbackWeightsForTest,
    left_value:Fr,
}

#[cfg(test)]
impl<'c,'a,'p> EdgeGroupedVContextForTest<'c,'a,'p> {
    pub(crate) fn new(
        adapter:&'c crate::native_prefix_auth_plan::Role4EndpointAdapter<'a,'p>,
        r:&[Fr],u:&[Fr],left_value:Fr,
    )->Result<Self,String>{
        if r.len()!=32 || u.len()!=32 {
            return Err("grouped V context point dimensions".into());
        }
        let binding=adapter.binding();
        if binding.scope!=crate::native_prefix_auth_plan::Role4EndpointScope::WholeS12
            || binding.headers!=3073 || binding.slot_log!=12
            || binding.whole_alias_identities.is_none() {
            return Err("grouped V context requires the bound WholeS12 adapter".into());
        }
        let inactive=adapter.grouped_v_context_for_test(&binding,r,u,left_value)?;
        let weights=EdgeFallbackWeightsForTest::new(r,u,20);
        if weights.u_local.len()!=(1usize<<20) || weights.u_slot.len()!=4096 {
            return Err("grouped V fixed weight extents".into());
        }
        Ok(Self{adapter,binding,inactive,weights,left_value})
    }

    pub(crate) fn family_owner(&self,owner:usize)->Result<(usize,Fr),String>{
        self.adapter.grouped_v_owner_for_test(&self.binding,&self.inactive,owner)
    }

    pub(crate) fn template_visits(&self)->usize {self.inactive.template_visits()}

    pub(crate) fn weights_capacity_bytes(&self)->usize {self.weights.capacity_bytes()}

    pub(crate) fn capacity_bytes(&self)->usize {
        std::mem::size_of::<Self>().saturating_add(self.inactive.capacity_bytes()
            .saturating_sub(std::mem::size_of::<crate::daa_history_roster::DaaGroupedVContextForTest<'a,'p>>()))
            .saturating_add(self.weights.capacity_bytes())
    }
}

#[cfg(test)]
#[derive(Default,Clone)]
pub(crate) struct EdgeGroupedVMetricsForTest {
    pub(crate) fallback:EdgeFallbackMetrics,
    pub(crate) physical_visits:u64,
    pub(crate) inactive_occurrences:u64,
    pub(crate) logical_occurrences:u64,
    pub(crate) family_contributions:u64,
    pub(crate) nonzero_injections:u64,
}

#[cfg(test)]
pub(crate) struct EdgeGroupedVOwnerResultForTest {
    pub(crate) message:Vec<Fr>,
    pub(crate) terminal:(Fr,Fr),
    pub(crate) folded_x:Fr,
    pub(crate) metrics:EdgeGroupedVMetricsForTest,
}

#[cfg(test)]
fn edge_replay_v_grouped<F,L,W>(
    visit:&mut F,input:&mut CopyCache<L>,slot:usize,width:usize,copies:usize,
    base_row_bits:usize,member_row_bits:&[usize],physical_count:usize,
    logical_count:usize,inactive_count:usize,b0:Fr,row_weight:&W,
    u_slot_weights:&[Fr],u_local_weights:&[Fr],left_value:Fr,prefix:&[Fr],
)->Result<EdgeReplayState,String>
where F:FnMut(bool,usize,&mut dyn FnMut(EdgeTerm)->Result<(),String>)->Result<(),String>,
    L:FnMut(usize)->Result<Vec<Fr>,String>,W:Fn(&EdgeTerm)->Result<Fr,String> {
    if physical_count.checked_add(inactive_count)!=Some(logical_count)
        || u_slot_weights.len()!=copies || u_local_weights.len()!=width
        || prefix.len()>width.trailing_zeros() as usize {
        return Err("grouped V owner count, weights, or prefix rejected".into());
    }
    let bank_terms=physical_count.checked_add(1).ok_or("grouped V bank estimate overflow")?;
    let mut banks=EdgeReplayBanks::new(width,bank_terms)?;
    let visited=walk_edge_endpoint(visit,false,slot,width,copies,base_row_bits,member_row_bits,
        Some(physical_count),&mut |edge|{
            let gate=&edge.term.gate;let left_slot=gate.left/width;let left_wire=gate.left%width;
            let weight=row_weight(&edge)?*u_slot_weights.get(left_slot).copied()
                .ok_or("grouped V left slot weight outside bound")?*u_local_weights[left_wire];
            let wire=gate.right%width;
            banks.add(wire,weight*(gate.c2+gate.c3*left_value),
                weight*(gate.c0+gate.c1*left_value));Ok(())
        })?;
    if visited!=physical_count {
        return Err("grouped V physical endpoint count changed".into());
    }
    // Injection precedes every Boolean fold, including the terminal round.
    banks.add(0,Fr::zero(),b0);
    banks.coalesce();
    let x=input.vector(slot)?;
    Ok(edge_replay_fold(banks,x,prefix,#[cfg(test)] EdgeFallbackMetrics{
        visits:physical_count as u64,cache_gets:1,vector_clones:1,
        cache_capacity_peak_bytes:input.capacity_bytes().ok_or("grouped V cache byte count overflow")?,
        ..Default::default()}))
}

#[cfg(test)]
pub(crate) struct EdgeGroupedVCandidateForTest<L> {
    input:CopyCache<L>,width:usize,copies:usize,
}

#[cfg(test)]
impl<L> EdgeGroupedVCandidateForTest<L>
where L:FnMut(usize)->Result<Vec<Fr>,String> {
    pub(crate) fn new(load:L,width:usize,copies:usize)->Result<Self,String>{
        if width!=(1usize<<20) || copies!=4096 {
            return Err("grouped V candidate is fixed to native S12 geometry".into());
        }
        Ok(Self{input:CopyCache::new(load,width,4),width,copies})
    }

    pub(crate) fn owner(
        &mut self,context:&EdgeGroupedVContextForTest<'_,'_,'_>,owner:usize,
        canonical_count:usize,prefix:&[Fr],
    )->Result<EdgeGroupedVOwnerResultForTest,String>{
        let input_bits=self.width.trailing_zeros() as usize;
        if owner>=self.copies || prefix.len()>input_bits || self.input.capacity!=4
            || context.weights.u_local.len()!=self.width
            || context.weights.u_slot.len()!=self.copies {
            return Err("grouped V owner context or geometry rejected".into());
        }
        let (inactive_count,b0)=context.family_owner(owner)?;
        let physical_count=canonical_count.checked_sub(inactive_count)
            .ok_or("grouped V inactive occurrences exceed canonical owner count")?;
        let row_weight=|edge:&EdgeTerm|global_edge_row(edge.source_slot,edge.family_row,
            12,19,1,&[19,19]).map(|row|context.weights.rows.at(row));
        let mut visit=|left:bool,slot:usize,sink:&mut dyn FnMut(EdgeTerm)->Result<(),String>|{
            if left || slot!=owner {
                return Err("grouped V visitor requested a non-RIGHT or foreign owner".into());
            }
            context.adapter.visit_right_noninactive_for_test(&context.binding,slot,
                |edge|sink(edge)).map(|_|())
        };
        let state=edge_replay_v_grouped(&mut visit,&mut self.input,owner,self.width,self.copies,
            19,&[19,19],physical_count,canonical_count,inactive_count,b0,&row_weight,
            &context.weights.u_slot,&context.weights.u_local,context.left_value,prefix)?;
        let EdgeReplayState{banks,x,metrics:fallback}=state;
        let message=if prefix.len()<input_bits {banks.message(&x)}else{Vec::new()};
        if prefix.len()<input_bits && message.len()!=3 {
            return Err("grouped V quadratic message extent".into());
        }
        let terminal=banks.terminal();
        let folded_x=*x.first().ok_or("grouped V folded X absent")?;
        Ok(EdgeGroupedVOwnerResultForTest{message,terminal,folded_x,
            metrics:EdgeGroupedVMetricsForTest{fallback,physical_visits:physical_count as u64,
                inactive_occurrences:inactive_count as u64,logical_occurrences:canonical_count as u64,
                family_contributions:if inactive_count>0{1}else{0},
                nonzero_injections:if !b0.is_zero(){1}else{0}}})
    }

    pub(crate) fn round(
        &mut self,context:&EdgeGroupedVContextForTest<'_,'_,'_>,canonical_counts:&[usize],prefix:&[Fr],
        mut owner_done:impl FnMut(usize,usize,usize,usize,[Fr;3])->Result<(),String>,
    )->Result<EdgeGroupedVMetricsForTest,String>{
        if canonical_counts.len()!=self.copies || prefix.len()>1 {
            return Err("grouped V all-owner round count or prefix rejected".into());
        }
        let mut totals=EdgeGroupedVMetricsForTest::default();
        for (owner,&logical_count) in canonical_counts.iter().enumerate(){
            let result=self.owner(context,owner,logical_count,prefix)?;
            let m=&result.metrics;let f=&m.fallback;let t=&mut totals.fallback;
            t.visits=t.visits.checked_add(f.visits).ok_or("grouped V visit total overflow")?;
            t.cache_gets=t.cache_gets.checked_add(f.cache_gets).ok_or("grouped V cache total overflow")?;
            t.vector_clones=t.vector_clones.checked_add(f.vector_clones).ok_or("grouped V clone total overflow")?;
            t.replay_folds=t.replay_folds.checked_add(f.replay_folds).ok_or("grouped V replay fold total overflow")?;
            t.x_fold_fields=t.x_fold_fields.checked_add(f.x_fold_fields).ok_or("grouped V X fold total overflow")?;
            t.bank_fold_entries=t.bank_fold_entries.checked_add(f.bank_fold_entries).ok_or("grouped V bank fold total overflow")?;
            t.bank_capacity_peak_bytes=t.bank_capacity_peak_bytes.max(f.bank_capacity_peak_bytes);
            t.cache_capacity_peak_bytes=t.cache_capacity_peak_bytes.max(f.cache_capacity_peak_bytes);
            t.fold_ns=t.fold_ns.checked_add(f.fold_ns).ok_or("grouped V fold time total overflow")?;
            t.dense|=f.dense;
            totals.physical_visits=totals.physical_visits.checked_add(m.physical_visits)
                .ok_or("grouped V physical total overflow")?;
            totals.inactive_occurrences=totals.inactive_occurrences.checked_add(m.inactive_occurrences)
                .ok_or("grouped V inactive total overflow")?;
            totals.logical_occurrences=totals.logical_occurrences.checked_add(m.logical_occurrences)
                .ok_or("grouped V logical total overflow")?;
            totals.family_contributions=totals.family_contributions.checked_add(m.family_contributions)
                .ok_or("grouped V contribution total overflow")?;
            totals.nonzero_injections=totals.nonzero_injections.checked_add(m.nonzero_injections)
                .ok_or("grouped V injection total overflow")?;
            let polynomial:[Fr;3]=result.message.as_slice().try_into()
                .map_err(|_|"grouped V all-owner quadratic message extent")?;
            owner_done(owner,logical_count,
                usize::try_from(m.physical_visits).map_err(|_|"grouped V physical owner count extent")?,
                usize::try_from(m.inactive_occurrences).map_err(|_|"grouped V inactive owner count extent")?,
                polynomial)?;
        }
        if totals.logical_occurrences!=338580202
            || totals.inactive_occurrences!=335454208
            || totals.physical_visits!=3125994
            || totals.family_contributions!=4095
            || totals.nonzero_injections>4095
            || totals.fallback.visits!=totals.physical_visits {
            return Err("grouped V canonical, physical, and inactive census mismatch".into());
        }
        Ok(totals)
    }
}

// The actual round-major fallback. Test observations run only after a complete
// owner; they do not alter traversal, cache lifetime or polynomial arithmetic.
fn edge_replay_u_round<F,I,W>(
    visit_endpoint:&mut F,input:&mut I,width:usize,copies:usize,
    base_row_bits:usize,member_row_bits:&[usize],left_counts:&[usize],
    row_weight:&W,u_local:&[Fr],
    #[cfg(test)] observe:&mut impl FnMut(usize,&EdgeFallbackMetrics,usize,u64)->Result<(),String>,
)->Result<[Fr;3],String>
where F:FnMut(bool,usize,&mut dyn FnMut(EdgeTerm)->Result<(),String>)->Result<(),String>,
    I:EdgeInput,W:Fn(&EdgeTerm)->Result<Fr,String> {
    let mut polynomial=[Fr::zero();3];
    for slot in 0..copies{
        let state=edge_replay_u(visit_endpoint,input,slot,width,copies,
            base_row_bits,member_row_bits,left_counts[slot],row_weight,u_local)?;
        #[cfg(test)] let metrics=state.metrics.clone();
        let EdgeReplayState{banks,x,..}=state;
        #[cfg(test)] let started=std::time::Instant::now();
        for (sum,value) in polynomial.iter_mut().zip(banks.message(&x)){*sum+=value;}
        #[cfg(test)] observe(slot+1,&metrics,x.capacity()*std::mem::size_of::<Fr>(),
            u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX))?;
    }
    Ok(polynomial)
}

#[cfg(test)]
pub(crate) fn edge_u0_census_for_test(
    input_bits:usize,slot_bits:usize,base_row_bits:usize,member_row_bits:&[usize],
    mut visit:impl FnMut(bool,usize,&mut dyn FnMut(EdgeTerm)->Result<(),String>)->Result<(),String>,
    mut progress:impl FnMut(usize,u64)->Result<(),String>,
)->Result<Vec<usize>,String> {
    let width=1usize.checked_shl(input_bits as u32).ok_or("U0 width")?;
    let copies=1usize.checked_shl(slot_bits as u32).ok_or("U0 copies")?;
    let mut counts=Vec::with_capacity(copies);let mut total=0u64;
    for slot in 0..copies {
        let count=walk_edge_endpoint(&mut visit,true,slot,width,copies,base_row_bits,
            member_row_bits,None,&mut |_|Ok(()))?;
        counts.push(count);total=total.checked_add(count as u64).ok_or("U0 count overflow")?;
        progress(slot+1,total)?;
    }
    Ok(counts)
}
#[cfg(test)]
pub(crate) fn edge_v_census_for_test(
    input_bits:usize,slot_bits:usize,base_row_bits:usize,family_bits:usize,member_row_bits:&[usize],
    mut visit:impl FnMut(bool,usize,&mut dyn FnMut(EdgeTerm)->Result<(),String>)->Result<(),String>,
    mut progress:impl FnMut(usize,u64)->Result<(),String>,
)->Result<Vec<usize>,String> {
    let width=1usize.checked_shl(input_bits as u32).ok_or("V prefix width")?;
    let copies=1usize.checked_shl(slot_bits as u32).ok_or("V prefix copies")?;
    if input_bits==0 || member_row_bits.is_empty()
        || member_row_bits.len()>1usize.checked_shl(family_bits as u32).ok_or("V prefix family extent")?
        || member_row_bits.iter().any(|bits|*bits>base_row_bits) {
        return Err("V prefix census geometry".into());
    }
    let mut counts=Vec::new();counts.try_reserve_exact(copies).map_err(|_|"V prefix RIGHT census allocation")?;
    let mut total=0u64;
    for owner in 0..copies {
        // The V census is intentionally independent of the LEFT-only U helper.
        let count=walk_edge_endpoint(&mut visit,false,owner,width,copies,base_row_bits,
            member_row_bits,None,&mut |_|Ok(()))?;
        counts.push(count);total=total.checked_add(count as u64).ok_or("V prefix RIGHT count overflow")?;
        progress(owner+1,total)?;
    }
    Ok(counts)
}
#[cfg(test)]
#[derive(Default,Clone)]
pub(crate) struct EdgeU0RoundMetrics {
    pub fallback:EdgeFallbackMetrics,pub x_capacity_peak_bytes:usize,pub message_ns:u64,
    pub weights_capacity_bytes:usize,
}
#[cfg(test)]
pub(crate) fn edge_u0_round_for_test(
    input_bits:usize,slot_bits:usize,base_row_bits:usize,family_bits:usize,
    member_row_bits:&[usize],left_counts:&[usize],r:&[Fr],
    visit:impl FnMut(bool,usize,&mut dyn FnMut(EdgeTerm)->Result<(),String>)->Result<(),String>,
    load:impl FnMut(usize)->Result<Vec<Fr>,String>,
    progress:impl FnMut(usize,u64)->Result<(),String>,
)->Result<([Fr;3],EdgeU0RoundMetrics),String> {
    let width=1usize.checked_shl(input_bits as u32).ok_or("U0 width")?;
    let copies=1usize.checked_shl(slot_bits as u32).ok_or("U0 copies")?;
    let mut input=CopyCache::declared(load,width,copies);
    edge_u0_round_with_input_for_test(input_bits,slot_bits,base_row_bits,family_bits,
        member_row_bits,left_counts,r,visit,&mut input,progress)
}
#[cfg(test)]
pub(crate) fn edge_u0_round_with_input_for_test(
    input_bits:usize,slot_bits:usize,base_row_bits:usize,family_bits:usize,
    member_row_bits:&[usize],left_counts:&[usize],r:&[Fr],
    mut visit:impl FnMut(bool,usize,&mut dyn FnMut(EdgeTerm)->Result<(),String>)->Result<(),String>,
    input:&mut impl EdgeInput,
    mut progress:impl FnMut(usize,u64)->Result<(),String>,
)->Result<([Fr;3],EdgeU0RoundMetrics),String> {
    let width=1usize.checked_shl(input_bits as u32).ok_or("U0 width")?;
    let copies=1usize.checked_shl(slot_bits as u32).ok_or("U0 copies")?;
    if input_bits==0 || r.len()!=base_row_bits+slot_bits+family_bits
        || left_counts.len()!=copies || member_row_bits.is_empty()
        || member_row_bits.len()>1usize.checked_shl(family_bits as u32).ok_or("U0 families")?
        || member_row_bits.iter().any(|x|*x>base_row_bits) {return Err("U0 geometry".into());}
    edge_input_geometry(input,width,copies)?;
    let weights=EqWeightLookup::new(r);
    let row_weight=|edge:&EdgeTerm|global_edge_row(edge.source_slot,edge.family_row,
        slot_bits,base_row_bits,family_bits,member_row_bits).map(|row|weights.at(row));
    let mut out=EdgeU0RoundMetrics::default();
    out.weights_capacity_bytes=weights.chunks.capacity()*std::mem::size_of::<(usize,Vec<Fr>)>()
        +weights.chunks.iter().map(|(_,v)|v.capacity()*std::mem::size_of::<Fr>()).sum::<usize>();
    let polynomial=edge_replay_u_round(&mut visit,input,width,copies,base_row_bits,
        member_row_bits,left_counts,&row_weight,&[],&mut |completed,m,x_bytes,message_ns|{
            out.fallback.visits+=m.visits;out.fallback.cache_gets+=m.cache_gets;
            out.fallback.vector_clones+=m.vector_clones;out.fallback.replay_folds+=m.replay_folds;
            out.fallback.x_fold_fields+=m.x_fold_fields;out.fallback.bank_fold_entries+=m.bank_fold_entries;
            out.fallback.bank_capacity_peak_bytes=out.fallback.bank_capacity_peak_bytes.max(m.bank_capacity_peak_bytes);
            out.fallback.cache_capacity_peak_bytes=out.fallback.cache_capacity_peak_bytes.max(m.cache_capacity_peak_bytes);
            out.x_capacity_peak_bytes=out.x_capacity_peak_bytes.max(x_bytes);out.message_ns+=message_ns;
            progress(completed,out.fallback.visits)
        })?;
    // Banks, expanded/cloned X and row weights drop here, before the independent oracle.
    Ok((polynomial,out))
}
#[cfg(test)]
pub(crate) fn edge_u0_send_for_test(poly:[Fr;3],transcript:&mut Transcript)->Result<(Fr,Fr),String> {
    let mut claim=Fr::zero();let mut rounds=Vec::new();
    let challenge=send_round(poly.to_vec(),&mut claim,&mut rounds,transcript).map_err(|e|e.to_string())?;
    Ok((challenge,claim))
}

#[cfg(test)]
#[derive(Clone)]
pub(crate) struct EdgeUSequenceRound {
    pub round:usize,pub previous_claim:Fr,pub polynomial:[Fr;3],pub challenge:Fr,pub claim:Fr,
    pub continuation:Fr,pub counters:[u64;3],pub metrics:EdgeU0RoundMetrics,pub wall_ns:u64,
}
#[cfg(test)]
pub(crate) enum EdgeUSequenceEvent {
    Begin(usize),Progress(usize,usize,u64),
    Arithmetic(usize,Fr,[Fr;3],EdgeU0RoundMetrics,u64),Closed(EdgeUSequenceRound),
    TerminalBegin,TerminalProgress(usize),TerminalEnd(EdgeU0RoundMetrics,u64),
}
#[cfg(test)]
pub(crate) struct EdgeUSequenceResult {
    pub rounds:Vec<EdgeUSequenceRound>,pub terminals:Vec<[Fr;3]>,
}
#[cfg(test)]
fn edge_sequence_metrics(sum:&mut EdgeU0RoundMetrics,m:&EdgeFallbackMetrics,x:usize,message:u64){
    sum.fallback.visits+=m.visits;sum.fallback.cache_gets+=m.cache_gets;
    sum.fallback.vector_clones+=m.vector_clones;sum.fallback.replay_folds+=m.replay_folds;
    sum.fallback.x_fold_fields+=m.x_fold_fields;sum.fallback.bank_fold_entries+=m.bank_fold_entries;
    sum.fallback.fold_ns+=m.fold_ns;
    sum.fallback.bank_capacity_peak_bytes=sum.fallback.bank_capacity_peak_bytes.max(m.bank_capacity_peak_bytes);
    sum.fallback.cache_capacity_peak_bytes=sum.fallback.cache_capacity_peak_bytes.max(m.cache_capacity_peak_bytes);
    sum.x_capacity_peak_bytes=sum.x_capacity_peak_bytes.max(x);sum.message_ns+=message;
}
#[cfg(test)]
pub(crate) fn edge_u_sequence_for_test(
    input_bits:usize,slot_bits:usize,base_row_bits:usize,family_bits:usize,
    member_row_bits:&[usize],left_counts:&[usize],r:&[Fr],k:usize,transcript:&mut Transcript,
    mut visit:impl FnMut(bool,usize,&mut dyn FnMut(EdgeTerm)->Result<(),String>)->Result<(),String>,
    load:impl FnMut(usize)->Result<Vec<Fr>,String>,
    mut observe:impl FnMut(EdgeUSequenceEvent)->Result<(),String>,
)->Result<EdgeUSequenceResult,String>{
    let width=1usize.checked_shl(input_bits as u32).ok_or("sequence width")?;
    let copies=1usize.checked_shl(slot_bits as u32).ok_or("sequence copies")?;
    if k<2 || k>input_bits || input_bits>20 || r.len()!=base_row_bits+slot_bits+family_bits
        || left_counts.len()!=copies || member_row_bits.is_empty()
        || member_row_bits.len()>1usize.checked_shl(family_bits as u32).ok_or("sequence families")?
        || member_row_bits.iter().any(|x|*x>base_row_bits){return Err("sequence geometry".into());}
    let weights=EqWeightLookup::new(r);
    let row_weight=|edge:&EdgeTerm|global_edge_row(edge.source_slot,edge.family_row,slot_bits,
        base_row_bits,family_bits,member_row_bits).map(|row|weights.at(row));
    let weight_bytes=weights.chunks.capacity()*std::mem::size_of::<(usize,Vec<Fr>)>()
        +weights.chunks.iter().map(|(_,v)|v.capacity()*std::mem::size_of::<Fr>()).sum::<usize>();
    let mut input=CopyCache::new(load,width,4);let mut prefix=Vec::with_capacity(k);
    let mut claim=Fr::zero();let mut encoded=Vec::with_capacity(k);let mut rounds=Vec::with_capacity(k);
    for round in 0..k {
        observe(EdgeUSequenceEvent::Begin(round))?;
        let mut metrics=EdgeU0RoundMetrics::default();metrics.weights_capacity_bytes=weight_bytes;
        let started=std::time::Instant::now();
        let polynomial=edge_replay_u_round(&mut visit,&mut input,width,copies,base_row_bits,
            member_row_bits,left_counts,&row_weight,&prefix,&mut |owner,m,x,ns|{
                edge_sequence_metrics(&mut metrics,m,x,ns);
                observe(EdgeUSequenceEvent::Progress(round,owner,metrics.fallback.visits))
            })?;
        let wall_ns=u64::try_from(started.elapsed().as_nanos()).map_err(|_|"sequence wall overflow")?;
        observe(EdgeUSequenceEvent::Arithmetic(round,claim,polynomial,metrics.clone(),wall_ns))?;
        let previous_claim=claim;
        let challenge=send_round(polynomial.to_vec(),&mut claim,&mut encoded,transcript).map_err(|e|e.to_string())?;
        prefix.push(challenge);
        let round_state=EdgeUSequenceRound{round,previous_claim,polynomial,challenge,claim,
            continuation:transcript.clone().challenge_scalar(b"native-u-sequence-continuation"),
            counters:[transcript.challenges(),transcript.raw_queries(),transcript.bytes_absorbed()],metrics,wall_ns};
        observe(EdgeUSequenceEvent::Closed(round_state.clone()))?;rounds.push(round_state);
    }
    let mut terminals=Vec::new();
    if k==input_bits {
        observe(EdgeUSequenceEvent::TerminalBegin)?;
        terminals.try_reserve_exact(copies).map_err(|_|"sequence terminal allocation")?;
        let mut metrics=EdgeU0RoundMetrics::default();metrics.weights_capacity_bytes=weight_bytes;
        let started=std::time::Instant::now();
        for owner in 0..copies {
            let state=edge_replay_u(&mut visit,&mut input,owner,width,copies,base_row_bits,
                member_row_bits,left_counts[owner],&row_weight,&prefix)?;
            edge_sequence_metrics(&mut metrics,&state.metrics,state.x.capacity()*std::mem::size_of::<Fr>(),0);
            let (a,b)=state.banks.terminal();terminals.push([a,b,state.x[0]]);
            observe(EdgeUSequenceEvent::TerminalProgress(owner+1))?;
        }
        observe(EdgeUSequenceEvent::TerminalEnd(metrics,
            u64::try_from(started.elapsed().as_nanos()).map_err(|_|"terminal wall overflow")?))?;
    }
    Ok(EdgeUSequenceResult{rounds,terminals})
}

#[cfg(test)]
pub(crate) fn edge_u_sequence_send_for_test(poly:[Fr;3],previous:Fr,t:&mut Transcript)->Result<(Fr,Fr),String>{
    let mut claim=previous;let mut rounds=Vec::new();
    let q=send_round(poly.to_vec(),&mut claim,&mut rounds,t).map_err(|e|e.to_string())?;Ok((q,claim))
}

pub(crate) const MAX_EDGE_INCREMENTAL_LOCAL_BYTES:usize=1280*1024*1024;

#[derive(Default)]
struct EdgeIncrementalControl {
    #[cfg(test)] force_u_off:bool,
    #[cfg(test)] force_v_off:bool,
    #[cfg(test)] cache_limit_override:Option<usize>,
}
impl EdgeIncrementalControl {
    fn cache_limit_bytes(&self)->usize{
        #[cfg(test)] { self.cache_limit_override.unwrap_or(MAX_EDGE_INCREMENTAL_LOCAL_BYTES) }
        #[cfg(not(test))] { MAX_EDGE_INCREMENTAL_LOCAL_BYTES }
    }
    fn allow_u(&self)->bool{
        #[cfg(test)] { !self.force_u_off }
        #[cfg(not(test))] { true }
    }
    fn allow_v(&self)->bool{
        #[cfg(test)] { !self.force_v_off }
        #[cfg(not(test))] { true }
    }
}

pub(crate) fn prove_edge_terms(
    input_bits:usize,slot_bits:usize,base_row_bits:usize,family_bits:usize,
    member_row_bits:&[usize],visit_endpoint:impl FnMut(bool,usize,&mut dyn FnMut(EdgeTerm)->Result<(),String>)->Result<(),String>,
    load_copy:impl FnMut(usize)->Result<Vec<Fr>,String>,transcript:&mut Transcript,
    bind:impl FnOnce(&mut Transcript),wiring:impl Fn(&[Fr],&[Fr],&[Fr])->Result<[Fr;4],String>,
)->Result<(GkrProof,InputClaim,bool,bool),String>{
    prove_edge_terms_inner(input_bits,slot_bits,base_row_bits,family_bits,member_row_bits,
        visit_endpoint,load_copy,transcript,bind,wiring,EdgeIncrementalControl::default())
}

#[cfg(test)]
pub(crate) fn prove_edge_terms_with_cache_limit_for_test(
    input_bits:usize,slot_bits:usize,base_row_bits:usize,family_bits:usize,
    member_row_bits:&[usize],cache_limit_bytes:usize,
    visit_endpoint:impl FnMut(bool,usize,&mut dyn FnMut(EdgeTerm)->Result<(),String>)->Result<(),String>,
    load_copy:impl FnMut(usize)->Result<Vec<Fr>,String>,transcript:&mut Transcript,
    bind:impl FnOnce(&mut Transcript),wiring:impl Fn(&[Fr],&[Fr],&[Fr])->Result<[Fr;4],String>,
)->Result<(GkrProof,InputClaim,bool,bool),String>{
    prove_edge_terms_inner(input_bits,slot_bits,base_row_bits,family_bits,member_row_bits,
        visit_endpoint,load_copy,transcript,bind,wiring,EdgeIncrementalControl{
            force_u_off:false,force_v_off:false,cache_limit_override:Some(cache_limit_bytes)})
}

fn prove_edge_terms_inner(
    input_bits:usize,slot_bits:usize,base_row_bits:usize,family_bits:usize,
    member_row_bits:&[usize],visit_endpoint:impl FnMut(bool,usize,&mut dyn FnMut(EdgeTerm)->Result<(),String>)->Result<(),String>,
    load_copy:impl FnMut(usize)->Result<Vec<Fr>,String>,transcript:&mut Transcript,
    bind:impl FnOnce(&mut Transcript),wiring:impl Fn(&[Fr],&[Fr],&[Fr])->Result<[Fr;4],String>,
    control:EdgeIncrementalControl,
)->Result<(GkrProof,InputClaim,bool,bool),String>{
    let width=1usize.checked_shl(input_bits as u32).ok_or("edge width overflow")?;
    let copies=1usize.checked_shl(slot_bits as u32).ok_or("edge slots overflow")?;
    let mut input=CopyCache::declared(load_copy,width,copies);
    prove_edge_terms_with_input_inner(input_bits,slot_bits,base_row_bits,family_bits,member_row_bits,
        visit_endpoint,&mut input,transcript,bind,wiring,control)
}

#[cfg(test)]
pub(crate) fn prove_edge_terms_with_input_for_test(
    input_bits:usize,slot_bits:usize,base_row_bits:usize,family_bits:usize,member_row_bits:&[usize],
    cache_limit_bytes:usize,input:&mut impl EdgeInput,
    visit_endpoint:impl FnMut(bool,usize,&mut dyn FnMut(EdgeTerm)->Result<(),String>)->Result<(),String>,
    transcript:&mut Transcript,bind:impl FnOnce(&mut Transcript),
    wiring:impl Fn(&[Fr],&[Fr],&[Fr])->Result<[Fr;4],String>,
)->Result<(GkrProof,InputClaim,bool,bool),String>{
    prove_edge_terms_with_input_inner(input_bits,slot_bits,base_row_bits,family_bits,member_row_bits,
        visit_endpoint,input,transcript,bind,wiring,EdgeIncrementalControl{
            force_u_off:false,force_v_off:false,cache_limit_override:Some(cache_limit_bytes)})
}

fn prove_edge_terms_with_input_inner(
    input_bits:usize,slot_bits:usize,base_row_bits:usize,family_bits:usize,
    member_row_bits:&[usize],visit_endpoint:impl FnMut(bool,usize,&mut dyn FnMut(EdgeTerm)->Result<(),String>)->Result<(),String>,
    input:&mut impl EdgeInput,transcript:&mut Transcript,
    bind:impl FnOnce(&mut Transcript),wiring:impl Fn(&[Fr],&[Fr],&[Fr])->Result<[Fr;4],String>,control:EdgeIncrementalControl,
)->Result<(GkrProof,InputClaim,bool,bool),String>{
    let(proof,claim,u,v,_)=prove_edge_terms_run(input_bits,slot_bits,base_row_bits,family_bits,member_row_bits,
        visit_endpoint,input,transcript,bind,wiring,control,false,None,&mut |_|Ok(()))?;Ok((proof,claim,u,v))
}
#[cfg(test)]
pub(crate) fn prove_edge_terms_strategy_for_test(
    input_bits:usize,slot_bits:usize,base_row_bits:usize,family_bits:usize,member_row_bits:&[usize],
    direct:bool,force_u_off:bool,force_v_off:bool,cache_limit_bytes:usize,input:&mut impl EdgeInput,
    visit:impl FnMut(bool,usize,&mut dyn FnMut(EdgeTerm)->Result<(),String>)->Result<(),String>,
    transcript:&mut Transcript,bind:impl FnOnce(&mut Transcript),
    wiring:impl Fn(&[Fr],&[Fr],&[Fr])->Result<[Fr;4],String>,
    observe:&mut impl FnMut(EdgeFullEvent)->Result<(),String>,
)->Result<(GkrProof,InputClaim,bool,bool,EdgeFullStats),String>{
    prove_edge_terms_run(input_bits,slot_bits,base_row_bits,family_bits,member_row_bits,visit,input,transcript,bind,wiring,
        EdgeIncrementalControl{force_u_off,force_v_off,cache_limit_override:Some(cache_limit_bytes)},direct,None,observe)
}
#[cfg(test)]
pub(crate) fn prove_edge_terms_packed_line_for_test(
    input_bits:usize,slot_bits:usize,base_row_bits:usize,family_bits:usize,member_row_bits:&[usize],
    input:&mut PackedEdgeInput<impl FnMut(usize)->Result<Vec<u8>,String>>,
    visit:impl FnMut(bool,usize,&mut dyn FnMut(EdgeTerm)->Result<(),String>)->Result<(),String>,
    transcript:&mut Transcript,bind:impl FnOnce(&mut Transcript),
    wiring:impl Fn(&[Fr],&[Fr],&[Fr])->Result<[Fr;4],String>,
    fast:&mut PackedLineStats,observe:&mut impl FnMut(EdgeFullEvent)->Result<(),String>,
)->Result<(GkrProof,InputClaim,bool,bool,EdgeFullStats),String>{
    prove_edge_terms_run(input_bits,slot_bits,base_row_bits,family_bits,member_row_bits,visit,input,transcript,bind,wiring,
        EdgeIncrementalControl{force_u_off:true,force_v_off:true,cache_limit_override:Some(0)},true,Some(fast),observe)
}
fn prove_edge_terms_run(
    input_bits:usize,slot_bits:usize,base_row_bits:usize,family_bits:usize,
    member_row_bits:&[usize],mut visit_endpoint:impl FnMut(bool,usize,&mut dyn FnMut(EdgeTerm)->Result<(),String>)->Result<(),String>,
    input:&mut impl EdgeInput,transcript:&mut Transcript,
    bind:impl FnOnce(&mut Transcript),wiring:impl Fn(&[Fr],&[Fr],&[Fr])->Result<[Fr;4],String>,
    control:EdgeIncrementalControl,direct:bool,mut packed_line:Option<&mut PackedLineStats>,
    observe:&mut impl FnMut(EdgeFullEvent)->Result<(),String>,
)->Result<(GkrProof,InputClaim,bool,bool,EdgeFullStats),String>{
    if packed_line.is_some()&&(!(3..=20).contains(&input_bits)||slot_bits>12){
        return Err("packed line declared dimensions".into());}
    let width=1usize.checked_shl(input_bits as u32).ok_or("edge width overflow")?;
    let copies=1usize.checked_shl(slot_bits as u32).ok_or("edge slots overflow")?;
    if let Some(fast)=packed_line.as_deref_mut(){
        if *fast!=PackedLineStats::default(){return Err("packed line statistics not fresh".into());}
        if !direct{return Err("packed line requires direct strategy".into());}
        let(bound,plan,extra)=packed_line_preflight(input,width,copies,512*1024*1024)?;
        fast.component_bound=bound;fast.plan_reserved_bytes=plan;fast.extra_reserved_bytes=extra;
    }
    let row_bits=base_row_bits.checked_add(slot_bits).and_then(|x|x.checked_add(family_bits)).ok_or("edge row bits overflow")?;
    let row_count=1usize.checked_shl(row_bits as u32).ok_or("edge row count overflow")?;
    edge_input_geometry(input,width,copies)?;if direct{direct_preflight(input,width,copies)?;}
    let mut stats=EdgeFullStats::default();
    if member_row_bits.is_empty()||member_row_bits.len()>1usize<<family_bits
        ||member_row_bits.iter().any(|bits|*bits>base_row_bits){return Err(GkrError::InvalidInputWidth.to_string());}
    let mut left_counts=Vec::with_capacity(copies);let mut right_counts=Vec::with_capacity(copies);
    let mut left_total=0u64;let mut right_total=0u64;
    full_mark(observe,"census_left",b'b',0,0,0)?;full_mark(observe,"census_right",b'b',0,0,0)?;
    for slot in 0..copies{
        let began=std::time::Instant::now();
        let left=walk_edge_endpoint(&mut visit_endpoint,true,slot,width,copies,base_row_bits,member_row_bits,None,&mut |_|Ok(()))?;
        stats.census_ns[0]=EdgeFullStats::add(stats.census_ns[0],EdgeFullStats::ns(began)?)?;
        let began=std::time::Instant::now();
        let right=walk_edge_endpoint(&mut visit_endpoint,false,slot,width,copies,base_row_bits,member_row_bits,None,&mut |_|Ok(()))?;
        stats.census_ns[1]=EdgeFullStats::add(stats.census_ns[1],EdgeFullStats::ns(began)?)?;
        left_counts.push(left);right_counts.push(right);
        left_total=EdgeFullStats::add(left_total,left as u64)?;right_total=EdgeFullStats::add(right_total,right as u64)?;
        stats.term_callbacks=EdgeFullStats::add(stats.term_callbacks,EdgeFullStats::add(left as u64,right as u64)?)?;
        if (slot+1)%1024==0||slot+1==copies{
            full_mark(observe,"census_left",b'p',0,slot+1,left_total)?;
            full_mark(observe,"census_right",b'p',0,slot+1,right_total)?;
        }
    }
    if left_counts.iter().sum::<usize>()!=right_counts.iter().sum::<usize>(){
        return Err("edge left/right sources emitted different term totals".into());
    }
    bind(transcript);
    let r=gkr::output_point(row_count,transcript);
    gkr::append_usize(transcript,b"gkr-layer-index",0);
    let row_weight_lookup=EqWeightLookup::new(&r);
    stats.row_lookup=row_weight_lookup.chunks.capacity()*std::mem::size_of::<(usize,Vec<Fr>)>()
        +row_weight_lookup.chunks.iter().map(|(_,v)|v.capacity()*std::mem::size_of::<Fr>()).sum::<usize>();
    let row_weight=|edge:&EdgeTerm|->Result<Fr,String>{
        global_edge_row(edge.source_slot,edge.family_row,slot_bits,base_row_bits,family_bits,member_row_bits)
            .map(|row|row_weight_lookup.at(row))
    };
    let mut claim=Fr::zero();let mut rounds=Vec::new();let mut u_local=Vec::with_capacity(input_bits);
    let cache_limit_bytes=control.cache_limit_bytes();
    let field_bytes=std::mem::size_of::<Fr>();let sparse_entry_bytes=std::mem::size_of::<(usize,Fr)>();
    let descriptor_bytes=copies.checked_mul(std::mem::size_of::<(SparseFieldVector,SparseFieldVector,Vec<Fr>)>());
    let cache_budget_bytes=Some(input.cache_budget_bytes()?);
    let dense_scratch_bytes=width.checked_mul(field_bytes).and_then(|bytes|bytes.checked_mul(3));
    let new_sparse_worst_bytes=width.checked_mul(sparse_entry_bytes).and_then(|bytes|bytes.checked_mul(2));
    let mut retained_x_bytes=0usize;let mut retained_sparse_bytes=0usize;
    let mut incremental_u_slots:Option<Vec<(SparseFieldVector,SparseFieldVector,Vec<Fr>)>>=None;
    let mut can_incremental=control.allow_u()&&descriptor_bytes.zip(cache_budget_bytes).zip(dense_scratch_bytes).zip(new_sparse_worst_bytes)
        .is_some_and(|(((descriptors,cache),dense),sparse)|descriptors.checked_add(cache).and_then(|n|n.checked_add(dense))
            .and_then(|n|n.checked_add(sparse)).is_some_and(|total|total<=cache_limit_bytes));
    let mut slots=if can_incremental{Vec::with_capacity(copies)}else{Vec::new()};
    for slot in 0..if can_incremental{copies}else{0}{
        let projected_before_load=retained_x_bytes.checked_add(retained_sparse_bytes.checked_mul(2).unwrap_or(usize::MAX))
            .and_then(|bytes|bytes.checked_add(cache_budget_bytes?))
            .and_then(|bytes|bytes.checked_add(dense_scratch_bytes?))
            .and_then(|bytes|bytes.checked_add(new_sparse_worst_bytes?))
            .and_then(|bytes|bytes.checked_add(descriptor_bytes?));
        if projected_before_load.is_none_or(|bytes|bytes>cache_limit_bytes){can_incremental=false;break;}
        let mut a=vec![Fr::zero();width];let mut b=vec![Fr::zero();width];
        walk_edge_endpoint(&mut visit_endpoint,true,slot,width,copies,base_row_bits,member_row_bits,Some(left_counts[slot]),&mut |edge|{
            let gate=&edge.term.gate;let wire=gate.left%width;let weight=row_weight(&edge)?;let right=edge_input_value(input,gate.right/width,gate.right%width)?;
            a[wire]+=weight*(gate.c1+gate.c3*right);b[wire]+=weight*(gate.c0+gate.c2*right);Ok(())
        })?;
        let cache_bytes=input.capacity_bytes().ok_or("edge cache byte count overflow")?;
        if cache_budget_bytes.is_none_or(|budget|cache_bytes>budget){return Err("edge input live cache exceeds declared budget".into());}
        let projected_before_x=retained_x_bytes.checked_add(retained_sparse_bytes.checked_mul(2).unwrap_or(usize::MAX))
            .and_then(|bytes|bytes.checked_add(cache_budget_bytes?))
            .and_then(|bytes|bytes.checked_add(width.checked_mul(field_bytes)?))
            .and_then(|bytes|bytes.checked_add(width.checked_mul(field_bytes)?.checked_mul(2)?))
            .and_then(|bytes|bytes.checked_add(new_sparse_worst_bytes?))
            .and_then(|bytes|bytes.checked_add(descriptor_bytes?));
        if projected_before_x.is_none_or(|bytes|bytes>cache_limit_bytes){can_incremental=false;break;}
        let x=edge_input_vector(input,slot,width)?;
        let projected_live=retained_x_bytes.checked_add(retained_sparse_bytes.checked_mul(2).unwrap_or(usize::MAX))
            .and_then(|bytes|bytes.checked_add(cache_budget_bytes?))
            .and_then(|bytes|bytes.checked_add(x.capacity().checked_mul(field_bytes)?))
            .and_then(|bytes|bytes.checked_add(width.checked_mul(field_bytes)?.checked_mul(2)?))
            .and_then(|bytes|bytes.checked_add(new_sparse_worst_bytes?))
            .and_then(|bytes|bytes.checked_add(descriptor_bytes?));
        if projected_live.is_none_or(|bytes|bytes>cache_limit_bytes){can_incremental=false;break;}
        let a=compact_nonzero(a);let b=compact_nonzero(b);
        retained_x_bytes=retained_x_bytes.checked_add(x.capacity().checked_mul(field_bytes).ok_or("edge witness byte count overflow")?)
            .ok_or("edge retained witness byte count overflow")?;
        retained_sparse_bytes=retained_sparse_bytes
            .checked_add(a.capacity().checked_add(b.capacity()).and_then(|count|count.checked_mul(sparse_entry_bytes)).ok_or("edge sparse coefficient byte count overflow")?)
            .ok_or("edge retained sparse byte count overflow")?;
        slots.push((a,b,x));
    }
    if can_incremental{incremental_u_slots=Some(slots);}else{drop(slots);}
    let used_incremental_u=incremental_u_slots.is_some();
    if let Some(slots)=incremental_u_slots.as_mut(){
        for _round in 0..input_bits{
            let mut polynomial=[Fr::zero();3];
            for (a,b,x) in slots.iter(){for (sum,value) in polynomial.iter_mut().zip(sparse_quadratic_message(a,b,x)){*sum+=value;}}
            let challenge=send_round(polynomial.to_vec(),&mut claim,&mut rounds,transcript).map_err(|e|e.to_string())?;
            for (a,b,x) in slots.iter_mut(){*a=sparse_fold(a,challenge);*b=sparse_fold(b,challenge);gkr::fold(x,challenge);}
            u_local.push(challenge);
        }
    }else{
        for round in 0..input_bits{
            let began=std::time::Instant::now();full_mark(observe,"u_local",b'b',round,0,0)?;
            let plan=if direct{Some(stats.plan(width,&u_local)?)}else{None};
            let mut polynomial=[Fr::zero();3];let mut terms=0u64;
            for slot in 0..copies{
                let state=if let Some(p)=&plan{edge_replay_direct(&mut visit_endpoint,input,true,slot,width,copies,base_row_bits,
                    member_row_bits,left_counts[slot],&row_weight,&[],&[],Fr::zero(),p)?}
                else{edge_replay_u(&mut visit_endpoint,input,slot,width,copies,base_row_bits,member_row_bits,left_counts[slot],&row_weight,&u_local)?};
                stats.state(&state,left_counts[slot],direct,u_local.len(),input)?;
                let started=std::time::Instant::now();for(sum,value)in polynomial.iter_mut().zip(state.banks.message(&state.x)){*sum+=value;}
                stats.message_ns=EdgeFullStats::add(stats.message_ns,EdgeFullStats::ns(started)?)?;
                terms=EdgeFullStats::add(terms,left_counts[slot]as u64)?;
                if (slot+1)%1024==0||slot+1==copies{full_mark(observe,"u_local",b'p',round,slot+1,terms)?;}
            }
            drop(plan);stats.pass_ns.push(EdgeFullStats::ns(began)?);
            u_local.push(send_round(polynomial.to_vec(),&mut claim,&mut rounds,transcript).map_err(|e|e.to_string())?);
        }
    }
    let mut high_a=Vec::with_capacity(copies);let mut high_b=Vec::with_capacity(copies);let mut high_x=Vec::with_capacity(copies);
    if let Some(slots)=incremental_u_slots{
        for (a,b,x) in slots{high_a.push(sparse_value(&a,0));high_b.push(sparse_value(&b,0));high_x.push(x[0]);}
    }else{
        let began=std::time::Instant::now();full_mark(observe,"u_terminal",b'b',input_bits,0,0)?;
        let plan=if direct{Some(stats.plan(width,&u_local)?)}else{None};let mut terms=0u64;
        for slot in 0..copies{
            let state=if let Some(p)=&plan{edge_replay_direct(&mut visit_endpoint,input,true,slot,width,copies,base_row_bits,
                member_row_bits,left_counts[slot],&row_weight,&[],&[],Fr::zero(),p)?}
            else{edge_replay_u(&mut visit_endpoint,input,slot,width,copies,base_row_bits,member_row_bits,left_counts[slot],&row_weight,&u_local)?};
            stats.state(&state,left_counts[slot],direct,u_local.len(),input)?;
            let(a,b)=state.banks.terminal();high_a.push(a);high_b.push(b);high_x.push(state.x[0]);
            terms=EdgeFullStats::add(terms,left_counts[slot]as u64)?;
            if (slot+1)%1024==0||slot+1==copies{full_mark(observe,"u_terminal",b'p',input_bits,slot+1,terms)?;}
        }
        drop(plan);stats.pass_ns.push(EdgeFullStats::ns(began)?);
    }
    full_mark(observe,"u_high",b'b',0,0,0)?;let high_began=std::time::Instant::now();
    let (u_high,left_value)=gkr::prove_phase(high_a,high_b,&high_x,&mut claim,&mut rounds,transcript).map_err(|e|e.to_string())?;
    stats.high_ns[0]=EdgeFullStats::ns(high_began)?;
    for round in 1..=u_high.len(){full_mark(observe,"u_high",b'p',round,0,0)?;}
    drop(high_x);
    let mut u=u_local.clone();u.extend(u_high);
    let u_local_weights=gkr::eq_weights(&u_local);let u_slot_weights=gkr::eq_weights(&u[input_bits..]);
    stats.u_weights=u_local_weights.capacity()*std::mem::size_of::<Fr>();stats.owner_weights=u_slot_weights.capacity()*std::mem::size_of::<Fr>();
    let mut v_local=Vec::with_capacity(input_bits);
    retained_x_bytes=0;retained_sparse_bytes=0;
    let weight_bytes=u_local_weights.capacity().checked_add(u_slot_weights.capacity())
        .and_then(|count|count.checked_mul(field_bytes));
    let mut incremental_v_slots:Option<Vec<(SparseFieldVector,SparseFieldVector,Vec<Fr>)>>=None;
    can_incremental=control.allow_v()&&descriptor_bytes.zip(cache_budget_bytes).zip(weight_bytes).zip(dense_scratch_bytes).zip(new_sparse_worst_bytes)
        .is_some_and(|((((descriptors,cache),weights),dense),sparse)|descriptors.checked_add(cache).and_then(|n|n.checked_add(weights))
            .and_then(|n|n.checked_add(dense)).and_then(|n|n.checked_add(sparse))
            .is_some_and(|total|total<=cache_limit_bytes));
    slots=if can_incremental{Vec::with_capacity(copies)}else{Vec::new()};
    for slot in 0..if can_incremental{copies}else{0}{
        let projected_before_load=retained_x_bytes.checked_add(retained_sparse_bytes.checked_mul(2).unwrap_or(usize::MAX))
            .and_then(|bytes|bytes.checked_add(cache_budget_bytes?))
            .and_then(|bytes|bytes.checked_add(weight_bytes?))
            .and_then(|bytes|bytes.checked_add(dense_scratch_bytes?))
            .and_then(|bytes|bytes.checked_add(new_sparse_worst_bytes?))
            .and_then(|bytes|bytes.checked_add(descriptor_bytes?));
        if projected_before_load.is_none_or(|bytes|bytes>cache_limit_bytes){can_incremental=false;break;}
        let mut c=vec![Fr::zero();width];let mut d=vec![Fr::zero();width];
        walk_edge_endpoint(&mut visit_endpoint,false,slot,width,copies,base_row_bits,member_row_bits,Some(right_counts[slot]),&mut |edge|{
            let gate=&edge.term.gate;let left_slot=gate.left/width;let left_wire=gate.left%width;
            let weight=row_weight(&edge)?*u_slot_weights[left_slot]*u_local_weights[left_wire];
            let wire=gate.right%width;c[wire]+=weight*(gate.c2+gate.c3*left_value);
            d[wire]+=weight*(gate.c0+gate.c1*left_value);Ok(())
        })?;
        let cache_bytes=input.capacity_bytes().ok_or("edge cache byte count overflow")?;
        if cache_budget_bytes.is_none_or(|budget|cache_bytes>budget){return Err("edge input live cache exceeds declared budget".into());}
        let projected_before_x=retained_x_bytes.checked_add(retained_sparse_bytes.checked_mul(2).unwrap_or(usize::MAX))
            .and_then(|bytes|bytes.checked_add(cache_budget_bytes?))
            .and_then(|bytes|bytes.checked_add(weight_bytes?))
            .and_then(|bytes|bytes.checked_add(width.checked_mul(field_bytes)?))
            .and_then(|bytes|bytes.checked_add(width.checked_mul(field_bytes)?.checked_mul(2)?))
            .and_then(|bytes|bytes.checked_add(new_sparse_worst_bytes?))
            .and_then(|bytes|bytes.checked_add(descriptor_bytes?));
        if projected_before_x.is_none_or(|bytes|bytes>cache_limit_bytes){can_incremental=false;break;}
        let x=edge_input_vector(input,slot,width)?;
        let projected_live=retained_x_bytes.checked_add(retained_sparse_bytes.checked_mul(2).unwrap_or(usize::MAX))
            .and_then(|bytes|bytes.checked_add(cache_budget_bytes?))
            .and_then(|bytes|bytes.checked_add(weight_bytes?))
            .and_then(|bytes|bytes.checked_add(x.capacity().checked_mul(field_bytes)?))
            .and_then(|bytes|bytes.checked_add(width.checked_mul(field_bytes)?.checked_mul(2)?))
            .and_then(|bytes|bytes.checked_add(new_sparse_worst_bytes?))
            .and_then(|bytes|bytes.checked_add(descriptor_bytes?));
        if projected_live.is_none_or(|bytes|bytes>cache_limit_bytes){can_incremental=false;break;}
        let c=compact_nonzero(c);let d=compact_nonzero(d);
        retained_x_bytes=retained_x_bytes.checked_add(x.capacity().checked_mul(field_bytes).ok_or("edge witness byte count overflow")?)
            .ok_or("edge retained witness byte count overflow")?;
        retained_sparse_bytes=retained_sparse_bytes
            .checked_add(c.capacity().checked_add(d.capacity()).and_then(|count|count.checked_mul(sparse_entry_bytes)).ok_or("edge sparse coefficient byte count overflow")?)
            .ok_or("edge retained sparse byte count overflow")?;
        slots.push((c,d,x));
    }
    if can_incremental{incremental_v_slots=Some(slots);}else{drop(slots);}
    let used_incremental_v=incremental_v_slots.is_some();
    if let Some(slots)=incremental_v_slots.as_mut(){
        for _round in 0..input_bits{
            let mut polynomial=[Fr::zero();3];
            for (c,d,x) in slots.iter(){for (sum,value) in polynomial.iter_mut().zip(sparse_quadratic_message(c,d,x)){*sum+=value;}}
            let challenge=send_round(polynomial.to_vec(),&mut claim,&mut rounds,transcript).map_err(|e|e.to_string())?;
            for (c,d,x) in slots.iter_mut(){*c=sparse_fold(c,challenge);*d=sparse_fold(d,challenge);gkr::fold(x,challenge);}
            v_local.push(challenge);
        }
    }else{
        for round in 0..input_bits{
            let began=std::time::Instant::now();full_mark(observe,"v_local",b'b',round,0,0)?;
            let plan=if direct{Some(stats.plan(width,&v_local)?)}else{None};
            let mut polynomial=[Fr::zero();3];let mut terms=0u64;
            for slot in 0..copies{
                let state=if let Some(p)=&plan{edge_replay_direct(&mut visit_endpoint,input,false,slot,width,copies,base_row_bits,
                    member_row_bits,right_counts[slot],&row_weight,&u_slot_weights,&u_local_weights,left_value,p)?}
                else{edge_replay_v(&mut visit_endpoint,input,slot,width,copies,base_row_bits,member_row_bits,right_counts[slot],
                    &row_weight,&u_slot_weights,&u_local_weights,left_value,&v_local)?};
                stats.state(&state,right_counts[slot],direct,v_local.len(),input)?;
                let started=std::time::Instant::now();for(sum,value)in polynomial.iter_mut().zip(state.banks.message(&state.x)){*sum+=value;}
                stats.message_ns=EdgeFullStats::add(stats.message_ns,EdgeFullStats::ns(started)?)?;
                terms=EdgeFullStats::add(terms,right_counts[slot]as u64)?;
                if (slot+1)%1024==0||slot+1==copies{full_mark(observe,"v_local",b'p',round,slot+1,terms)?;}
            }
            drop(plan);stats.pass_ns.push(EdgeFullStats::ns(began)?);
            v_local.push(send_round(polynomial.to_vec(),&mut claim,&mut rounds,transcript).map_err(|e|e.to_string())?);
        }
    }
    let mut high_c=Vec::with_capacity(copies);let mut high_d=Vec::with_capacity(copies);let mut high_w=Vec::with_capacity(copies);
    if let Some(slots)=incremental_v_slots{
        for (c,d,x) in slots{high_c.push(sparse_value(&c,0));high_d.push(sparse_value(&d,0));high_w.push(x[0]);}
    }else{
        let began=std::time::Instant::now();full_mark(observe,"v_terminal",b'b',input_bits,0,0)?;
        let plan=if direct{Some(stats.plan(width,&v_local)?)}else{None};let mut terms=0u64;
        for slot in 0..copies{
            let state=if let Some(p)=&plan{edge_replay_direct(&mut visit_endpoint,input,false,slot,width,copies,base_row_bits,
                member_row_bits,right_counts[slot],&row_weight,&u_slot_weights,&u_local_weights,left_value,p)?}
            else{edge_replay_v(&mut visit_endpoint,input,slot,width,copies,base_row_bits,member_row_bits,right_counts[slot],
                &row_weight,&u_slot_weights,&u_local_weights,left_value,&v_local)?};
            stats.state(&state,right_counts[slot],direct,v_local.len(),input)?;
            let(c,d)=state.banks.terminal();high_c.push(c);high_d.push(d);high_w.push(state.x[0]);
            terms=EdgeFullStats::add(terms,right_counts[slot]as u64)?;
            if (slot+1)%1024==0||slot+1==copies{full_mark(observe,"v_terminal",b'p',input_bits,slot+1,terms)?;}
        }
        drop(plan);stats.pass_ns.push(EdgeFullStats::ns(began)?);
    }
    full_mark(observe,"v_high",b'b',0,0,0)?;let high_began=std::time::Instant::now();
    let (v_high,right_value)=gkr::prove_phase(high_c,high_d,&high_w,&mut claim,&mut rounds,transcript).map_err(|e|e.to_string())?;
    stats.high_ns[1]=EdgeFullStats::ns(high_began)?;
    for round in 1..=v_high.len(){full_mark(observe,"v_high",b'p',round,0,0)?;}
    drop(high_w);
    let mut v=v_local.clone();v.extend(v_high);
    full_mark(observe,"wiring",b'b',0,0,0)?;
    let coefficients=wiring(&r,&u,&v)?;
    full_mark(observe,"wiring",b'e',0,0,0)?;
    if coefficients[0]+coefficients[1]*left_value+coefficients[2]*right_value
        +coefficients[3]*left_value*right_value!=claim{return Err(GkrError::TerminalExpression.to_string());}
    full_mark(observe,"line",b'b',0,0,0)?;
    let whole_line=std::time::Instant::now();
    let mut packed_plan=if let Some(fast)=packed_line.as_deref_mut(){
        let began=std::time::Instant::now();let plan=PackedLinePlan::new(width,&u_local,&v_local,fast.plan_reserved_bytes)?;
        fast.build_ns=EdgeFullStats::ns(began)?;fast.builds=1;
        fast.lut_fields=plan.lut.capacity().checked_mul(4).ok_or("packed line capacity arithmetic")?;
        fast.work_fields=plan.work.capacity();fast.plan_actual_bytes=plan.accounted;
        if fast.plan_actual_bytes>fast.plan_reserved_bytes{return Err("packed line actual reservation".into());}
        Some(plan)
    }else{None};
    let mut line=vec![Fr::zero();input_bits+slot_bits+1];
    for slot in 0..copies{
        if let Some(plan)=packed_plan.as_mut(){
            let(local,apply_ns)=input.packed_line(slot,plan)?;
            let fast=packed_line.as_deref_mut().ok_or("packed line missing statistics")?;
            if local.len()!=input_bits+1{return Err("packed line local extent".into());}
            packed_line_capacity(local.capacity(),input_bits+1)?;
            fast.owners=EdgeFullStats::add(fast.owners,1)?;
            fast.coefficients=EdgeFullStats::add(fast.coefficients,local.len()as u64)?;
            fast.result_fields=fast.result_fields.max(local.capacity());
            fast.apply_ns=EdgeFullStats::add(fast.apply_ns,apply_ns)?;
            stats.owner_requests=EdgeFullStats::add(stats.owner_requests,1)?;
            let began=std::time::Instant::now();
            let selector=copy_line_selector(slot,&u[input_bits..],&v[input_bits..]);
            for(sum,value)in line.iter_mut().zip(multiply(&local,&selector)){*sum+=value;}
            stats.line_ns=EdgeFullStats::add(stats.line_ns,EdgeFullStats::add(apply_ns,EdgeFullStats::ns(began)?)?)?;
            if(slot+1)%1024==0||slot+1==copies{full_mark(observe,"line",b'p',0,slot+1,0)?;}
            continue;
        }
        let local_input=edge_input_vector(input,slot,width)?;
        stats.owner_requests=EdgeFullStats::add(stats.owner_requests,1)?;stats.emitted_fields=EdgeFullStats::add(stats.emitted_fields,local_input.len()as u64)?;
        stats.x=stats.x.max(local_input.capacity()*std::mem::size_of::<Fr>());
        #[cfg(test)] {stats.input_vector_clones=EdgeFullStats::add(stats.input_vector_clones,input.vector_clone_increment())?;}
        let began=std::time::Instant::now();
        let local=gkr::line_polynomial(&local_input,&u_local,&v_local);
        stats.line_internal_clones=EdgeFullStats::add(stats.line_internal_clones,1)?;stats.line_cloned_fields=EdgeFullStats::add(stats.line_cloned_fields,local_input.len()as u64)?;
        let selector=copy_line_selector(slot,&u[input_bits..],&v[input_bits..]);
        for (sum,value) in line.iter_mut().zip(multiply(&local,&selector)){*sum+=value;}
        stats.line_ns=EdgeFullStats::add(stats.line_ns,EdgeFullStats::ns(began)?)?;
        if (slot+1)%1024==0||slot+1==copies{full_mark(observe,"line",b'p',0,slot+1,0)?;}
    }
    drop(packed_plan);
    if let Some(fast)=packed_line.as_deref_mut(){fast.whole_ns=EdgeFullStats::ns(whole_line)?;
        if fast.build_ns.checked_add(fast.apply_ns).is_none_or(|n|n>fast.whole_ns){return Err("packed line timer nesting".into());}}
    if line[0]!=left_value||gkr::eval_polynomial(&line,Fr::one())!=right_value{return Err(GkrError::LineEndpoints.to_string());}
    transcript.append_scalar(b"gkr-left-value",&left_value);transcript.append_scalar(b"gkr-right-value",&right_value);
    gkr::append_polynomial(transcript,b"gkr-line-polynomial",&line);
    let challenge=transcript.challenge_scalar(b"gkr-line-challenge");
    let point=gkr::line_point(&u,&v,challenge);let value=gkr::eval_polynomial(&line,challenge);
    stats.left_counts=left_counts;stats.right_counts=right_counts;
    Ok((GkrProof{layers:vec![LayerProof{rounds,left_value,right_value,line_coefficients:line}]},InputClaim{point,value},used_incremental_u,used_incremental_v,stats))
}

#[cfg(test)]
pub(crate) fn packed_edge_input_boundaries_for_test(){tests::packed_input_controls();}
#[cfg(test)]
pub(crate) fn packed_line52_controls_for_test()->Result<(),String>{packed_line52_controls::run()}
#[cfg(test)]
pub(crate) fn direct_edge_boundaries_for_test(){tests::direct_prefix_controls();}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gkr::Gate;
    mod c334_all_round_mux;

    fn c514_toy_term(left:usize,right:usize,coefficients:[u64;4])->EdgeTerm{
        let [c0,c1,c2,c3]=coefficients.map(Fr::from);
        EdgeTerm{source_slot:1,family_row:2,term:Term{row:6,
            gate:Gate{left,right,c0,c1,c2,c3}}}
    }
    fn c514_toy_run(terms:&[EdgeTerm],x:&[bool;16])->([Fr;3],C514Metrics){
        c514_selected_u0_contribution(terms,&[Fr::from(3u64);4],2,2,2,0,&[2],
            |_|Ok(()),|wire|Ok(x[wire])).unwrap()
    }
    // Independent small dense relation: collect A/B banks by enumerating every
    // wire, fold A, B and X at 0/1/2, then interpolate their dot products.
    fn c514_toy_dense_oracle(terms:&[EdgeTerm],x:&[bool;16])->[Fr;3]{
        use ark_ff::Field;
        let rows=gkr::eq_weights(&[Fr::from(3u64);4]);
        let mut a=[Fr::zero();16];let mut b=[Fr::zero();16];
        for wire in 0..16 {
            for edge in terms.iter().filter(|edge|edge.term.gate.left==wire){
                let g=&edge.term.gate;let right=Fr::from(x[g.right] as u64);
                a[wire]+=rows[edge.term.row]*(g.c1+g.c3*right);
                b[wire]+=rows[edge.term.row]*(g.c0+g.c2*right);
            }
        }
        let mut evaluated=[Fr::zero();3];
        for (point,out) in evaluated.iter_mut().enumerate(){
            let t=Fr::from(point as u64);
            let mut af=a.to_vec();let mut bf=b.to_vec();
            let mut xf:Vec<Fr>=x.iter().map(|v|Fr::from(*v as u64)).collect();
            gkr::fold(&mut af,t);gkr::fold(&mut bf,t);gkr::fold(&mut xf,t);
            *out=af.iter().zip(&bf).zip(&xf).map(|((a,b),x)|*a * *x+*b).sum();
        }
        let quadratic=(evaluated[2]-Fr::from(2u64)*evaluated[1]+evaluated[0])
            *Fr::from(2u64).inverse().unwrap();
        [evaluated[0],evaluated[1]-evaluated[0]-quadratic,quadratic]
    }
    #[test]
    fn c514_selected_u0_coefficients_parity_and_foreign_left_match_dense(){
        let x=[false,true,true,false,true,false,false,true,true,false,true,true,false,true,false,false];
        let mut mixed=Vec::new();
        for coefficient in 0..4 {
            for left in [0,1,4,5,8,9] {
                let mut coefficients=[0;4];coefficients[coefficient]=7;
                let edge=c514_toy_term(left,7,coefficients);
                let (actual,m)=c514_toy_run(&[edge.clone()],&x);
                assert_eq!(actual,c514_toy_dense_oracle(&[edge.clone()],&x));
                assert_eq!(m.term_visits,1);assert_eq!(m.left_slots,1);
                let expected=[0,2,1,3][coefficient];
                assert_eq!((m.demands,m.loads,m.unique_coordinates),(expected,expected,expected));
                assert!(m.capacity_bytes>=m.demand_capacity*std::mem::size_of::<C514Demand>());
                let g=&edge.term.gate;
                let direct=eq_weight_at(&[Fr::from(3u64);4],6)*
                    (g.c0+g.c1*Fr::from(x[left] as u64)+g.c2*Fr::from(x[7] as u64)
                    +g.c3*Fr::from(x[left] as u64)*Fr::from(x[7] as u64));
                assert_eq!(actual[0]+gkr::eval_polynomial(&actual,Fr::one()),direct);
                mixed.push(edge);
            }
        }
        let (actual,m)=c514_toy_run(&mixed,&x);
        assert_eq!(actual,c514_toy_dense_oracle(&mixed,&x));assert_eq!(m.left_slots,3);
        assert_eq!(m.loads,m.demands);assert_eq!(m.duplicate_loads,m.loads-m.unique_coordinates);
    }
    #[test]
    fn c514_selected_u0_inactive_and_missing_authored_zero_are_distinct(){
        let constant=c514_toy_term(8,0,[9,0,0,0]);
        let (_,m)=c514_selected_u0_contribution(&[constant],&[Fr::from(3u64);4],2,2,2,0,&[2],
            |demands|{assert!(demands.is_empty());Ok(())},|_|panic!("constant must not read X")).unwrap();
        assert_eq!(m.loads,0);
        for coefficients in [[0,0,1,0],[0,1,0,0],[0,0,0,1]] {
            let edge=c514_toy_term(8,7,coefficients);
            let reads=std::cell::Cell::new(0);
            let rejected=c514_selected_u0_contribution(&[edge.clone()],&[Fr::from(3u64);4],2,2,2,0,&[2],
                |demands|{assert!(!demands.is_empty());Err("missing physical author".into())},
                |_|{reads.set(reads.get()+1);Ok(false)});
            assert_eq!(rejected.unwrap_err(),"missing physical author");assert_eq!(reads.get(),0);
            let (_,m)=c514_toy_run(&[edge.clone()],&[false;16]);
            assert!(m.loads>0,"active authored zero must be read");
            let missing=if coefficients[1]!=0 || coefficients[3]!=0{9}else{7};
            let rejected=c514_selected_u0_contribution(&[edge],&[Fr::from(3u64);4],2,2,2,0,&[2],
                |demands|{assert!(demands.iter().any(|d|d.coordinate==missing));Ok(())},
                |wire|if wire==missing{Err("missing active zero or pair neighbour".into())}else{Ok(false)});
            let side=if missing==9{"LeftOdd"}else{"Right"};
            assert_eq!(rejected.unwrap_err(),format!(
                "C514 read failure at term 0 side {side} coordinate {missing}: missing active zero or pair neighbour"));
        }
    }
    #[test]
    fn c514_selected_u0_reader_failure_retains_duplicate_occurrence_attribution(){
        let edge=c514_toy_term(9,7,[0,0,0,1]);
        let qualified=std::cell::Cell::new(false);
        let loads=std::cell::Cell::new(0);
        let result=c514_selected_u0_contribution(&[edge.clone(),edge],&[Fr::from(3u64);4],2,2,2,0,&[2],
            |demands|{assert_eq!(demands.len(),6);qualified.set(true);Ok(())},
            |wire|{
                assert!(qualified.get());
                let n=loads.get();loads.set(n+1);
                if n==3{assert_eq!(wire,7);Err("physical token expired".into())}else{Ok(false)}
            });
        // A later occurrence of the same coordinate must still visit its token.
        // The error returns before the arithmetic loop; no polynomial is exposed.
        assert_eq!(result.unwrap_err(),
            "C514 read failure at term 1 side Right coordinate 7: physical token expired");
        assert_eq!(loads.get(),4);
    }
    #[test]
    fn c514_selected_u0_repeated_terms_cancel_but_repeated_reads_must_agree(){
        let edge=c514_toy_term(9,7,[0,0,0,1]);
        let mut negative=edge.clone();negative.term.gate.c3=-Fr::one();
        let terms=[edge.clone(),edge,negative];
        let x=[true;16];let (actual,m)=c514_toy_run(&terms,&x);
        assert_eq!(actual,c514_toy_dense_oracle(&terms,&x));
        assert_eq!((m.term_visits,m.demands,m.loads,m.unique_coordinates,m.duplicate_loads),(3,9,9,3,6));
        let (cancelled,m)=c514_toy_run(&terms[1..],&x);
        assert_eq!(cancelled,[Fr::zero();3]);assert_eq!(m.loads,6);
        let loads=std::cell::Cell::new(0);
        let error=c514_selected_u0_contribution(&terms,&[Fr::from(3u64);4],2,2,2,0,&[2],
            |demands|{assert_eq!(demands[0],C514Demand{term_index:0,side:C514DemandSide::Right,coordinate:7});
                assert_eq!(demands[1].side,C514DemandSide::LeftEven);
                assert_eq!(demands[2].side,C514DemandSide::LeftOdd);Ok(())},
            |_|{let n=loads.get();loads.set(n+1);Ok(n!=3)}).unwrap_err();
        assert!(error.contains("contradictory value"));assert_eq!(loads.get(),4);
    }
    #[test]
    fn c514_selected_u0_geometry_and_exact_row_reject_before_qualification(){
        let edge=c514_toy_term(8,7,[0,1,0,0]);
        for fault in 0..6 {
            let mut bad=edge.clone();
            match fault {
                0=>bad.term.row-=1,1=>bad.term.row+=1,2=>bad.source_slot=4,
                3=>bad.family_row=4,4=>bad.term.gate.left=16,_=>bad.term.gate.right=16,
            }
            assert!(c514_selected_u0_contribution(&[bad],&[Fr::from(3u64);4],2,2,2,0,&[2],
                |_|panic!("bad geometry must fail before qualification"),|_|panic!("bad geometry must not read")).is_err());
        }
        let mut other=edge.clone();other.source_slot=2;other.term.row=10;
        assert!(c514_selected_u0_contribution(&[edge,other],&[Fr::from(3u64);4],2,2,2,0,&[2],
            |_|panic!("mixed ROW owners must fail before qualification"),|_|panic!("must not read")).is_err());
        assert!(c514_selected_u0_contribution(&[],&[],usize::MAX,1,2,0,&[2],
            |_|panic!("overflow must fail before qualification"),|_|panic!("must not read")).is_err());
    }

    pub(super) fn packed_line52_nonboolean_fallback(){
        edge_stream_cache_evicts_slots_and_matches_resident_proof();
        edge_sparse_replay_four_modes_match_resident_and_reject_mutants();
    }

    pub(super) fn direct_prefix_controls(){
        let width=1usize<<20;let packet:Vec<u8>=(0..width/8).map(|i|(i%256)as u8).collect();
        let boolean:Vec<Fr>=(0..width).map(|i|Fr::from(((packet[i/8]>>(i%8))&1)as u64)).collect();
        let prefix:Vec<Fr>=(0..20).map(|i|Fr::from((i*7+3)as u64)).collect();
        let mut packed=PackedEdgeInput::new(width,1,|_|Ok(packet.clone())).unwrap();
        for k in [0,1,2,3,4,7,8,9,19,20]{
            let plan=EdgePrefixPlan::new(width,&prefix[..k]).unwrap();let mut reference=boolean.clone();for q in &prefix[..k]{gkr::fold(&mut reference,*q);}
            let actual=packed.projected(0,&plan).unwrap();assert_eq!(actual,reference);assert_eq!(actual.capacity(),width>>k);
            if k==3{let small=EdgePrefixPlan::new(8,&prefix[..3]).unwrap();for byte in 0u8..=255{
                assert_eq!(small.project_bits(&[byte]).unwrap()[0],small.patterns[byte as usize]);}}
        }
        assert_eq!(packed.metrics().successful_loads,1);drop(packed);drop(boolean);
        let values:Vec<Fr>=(0..width).map(|i|Fr::from((i%29+2)as u64)).collect();
        let wires=[0,1,2,3,7,8,15,16,511,width-2,width-1];
        let edges:Vec<EdgeTerm>=wires.iter().enumerate().map(|(row,&wire)|EdgeTerm{source_slot:0,family_row:row,term:Term{row,
            gate:Gate{left:wire,right:width-1-wire,c0:Fr::from((row+1)as u64),c1:Fr::from(2u64),c2:Fr::from(3u64),c3:Fr::from(5u64)}}}).collect();
        let at=|banks:&EdgeReplayBanks,left:bool,index:usize|match banks{EdgeReplayBanks::Dense(a,b)=>if left{a[index]}else{b[index]},
            EdgeReplayBanks::Sparse(a,b)=>sparse_value(if left{a}else{b},index)};
        for k in [0,1,2,3,4,7,8,9,19,20]{
            let plan=EdgePrefixPlan::new(width,&prefix[..k]).unwrap();let mut reference=values.clone();for q in &prefix[..k]{gkr::fold(&mut reference,*q);}
            assert_eq!(plan.project_fields(&values).unwrap(),reference);
            for left in [true,false]{
                let emit=|_:bool,_:usize,sink:&mut dyn FnMut(EdgeTerm)->Result<(),String>|{for e in &edges{sink(e.clone())?;}Ok(())};
                let row=|e:&EdgeTerm|Ok(Fr::from((e.family_row+1)as u64));let ulocal=vec![Fr::from(11u64);width];let uowner=[Fr::from(13u64)];
                let mut old=CopyCache::declared(|_|Ok(values.clone()),width,1);let mut new=CopyCache::declared(|_|Ok(values.clone()),width,1);
                let legacy=if left{edge_replay_u(&mut{emit},&mut old,0,width,1,4,&[4],edges.len(),&row,&prefix[..k]).unwrap()}
                    else{edge_replay_v(&mut{emit},&mut old,0,width,1,4,&[4],edges.len(),&row,&uowner,&ulocal,Fr::from(17u64),&prefix[..k]).unwrap()};
                let direct=edge_replay_direct(&mut{emit},&mut new,left,0,width,1,4,&[4],edges.len(),&row,&uowner,&ulocal,Fr::from(17u64),&plan).unwrap();
                assert_eq!(direct.x,legacy.x);assert_eq!(direct.x.capacity(),width>>k);
                for i in 0..(width>>k){assert_eq!((at(&direct.banks,true,i),at(&direct.banks,false,i)),(at(&legacy.banks,true,i),at(&legacy.banks,false,i)));}
            }
        }
        drop(values);
        assert_eq!(EdgePrefixPlan::new(8,&prefix[..4]).err().unwrap(),"edge prefix geometry");
        assert_eq!(EdgePrefixPlan::new(0,&[]).err().unwrap(),"edge prefix geometry");
        let p=EdgePrefixPlan::new(8,&prefix[..1]).unwrap();assert_eq!(p.project_fields(&[Fr::zero();7]).unwrap_err(),"edge prefix field width");
        assert_eq!(p.project_bits(&[]).unwrap_err(),"edge prefix packet width");
        let p=EdgePrefixPlan::new(8,&prefix[..3]).unwrap();let direct=p.project_bits(&[1]).unwrap();
        assert_ne!(direct,p.project_bits(&[128]).unwrap(),"isolated LSB reversal");
        let mut bad=EdgePrefixPlan::new(8,&prefix[..3]).unwrap();bad.patterns[1]+=Fr::one();assert_ne!(direct,bad.project_bits(&[1]).unwrap());
        let fields=[Fr::from(2u64);8];let reference=p.project_fields(&fields).unwrap();bad.weights[0]+=Fr::one();assert_ne!(reference,bad.project_fields(&fields).unwrap());
        let reads=std::cell::Cell::new(0);let mut input=PackedEdgeInput::new(8,8,|owner|{reads.set(reads.get()+1);
            if owner==7{Err("direct zero-weight RIGHT read".into())}else{Ok(vec![0])}}).unwrap();
        let zero=EdgePrefixPlan::new(8,&[Fr::zero()]).unwrap();let edge=EdgeTerm{source_slot:0,family_row:0,term:Term{row:0,
            gate:Gate{left:1,right:63,c0:Fr::zero(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}}};
        let result=edge_replay_direct(&mut|_,_,sink|sink(edge.clone()),&mut input,true,0,8,8,0,&[0],1,&|_|Ok(Fr::one()),&[],&[],Fr::zero(),&zero);
        assert_eq!(result.err().unwrap(),"direct zero-weight RIGHT read");assert_eq!(reads.get(),1);
        let mut input=PackedEdgeInput::new(8,1,|_|Ok(vec![0])).unwrap();let edge=EdgeTerm{source_slot:0,family_row:0,term:Term{row:0,
            gate:Gate{left:0,right:0,c0:Fr::zero(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}}};
        assert_eq!(edge_replay_direct(&mut|_,_,sink|sink(edge.clone()),&mut input,true,0,8,1,0,&[0],2,&|_|Ok(Fr::one()),&[],&[],Fr::zero(),&zero).err().unwrap(),
            "edge endpoint source count changed between passes");
        let mut source_fault=edge.clone();source_fault.source_slot=1;
        assert_eq!(edge_replay_direct(&mut|_,_,sink|sink(source_fault.clone()),&mut input,true,0,8,1,0,&[0],1,&|_|Ok(Fr::one()),&[],&[],Fr::zero(),&zero).err().unwrap(),
            "edge endpoint wire or row outside declared slot");
        struct BadProjection{mode:u8,used:bool}
        impl EdgeInput for BadProjection{
            fn width(&self)->usize{8}fn owners(&self)->usize{1}
            fn value(&mut self,_:usize,_:usize)->Result<Fr,String>{Ok(Fr::zero())}
            fn vector(&mut self,_:usize)->Result<Vec<Fr>,String>{Ok(vec![Fr::zero();8])}
            fn projected(&mut self,_:usize,_:&EdgePrefixPlan)->Result<Vec<Fr>,String>{self.used=true;
                if self.mode==0{Ok(vec![Fr::zero();3])}else{let mut v=Vec::with_capacity(if self.mode==1{5}else{4});v.resize(4,Fr::zero());Ok(v)}}
            fn capacity_bytes(&self)->Option<usize>{Some(if self.mode==2&&self.used{2}else{0})}
            fn cache_budget_bytes(&self)->Result<usize,String>{Ok(1)}fn vector_clone_increment(&self)->u64{0}
        }
        for mode in 0..3{let mut bad=BadProjection{mode,used:false};
            let result=edge_replay_direct(&mut|_,_,sink|sink(edge.clone()),&mut bad,true,0,8,1,0,&[0],1,&|_|Ok(Fr::one()),&[],&[],Fr::zero(),&zero);
            assert_eq!(result.err().unwrap(),if mode==2{"edge input live cache exceeds declared budget"}else{"edge direct projected width/capacity"});}
        let kernel=|e:EdgeTerm,p:&EdgePrefixPlan|{let mut input=PackedEdgeInput::new(8,1,|_|Ok(vec![0])).unwrap();
            edge_replay_direct(&mut|_,_,sink|sink(e.clone()),&mut input,true,0,8,1,1,&[1],1,&|e|Ok(Fr::from((e.family_row+1)as u64)),&[],&[],Fr::zero(),p).unwrap()};
        let mut canonical=edge.clone();canonical.term.gate.c1=Fr::one();let plan=EdgePrefixPlan::new(8,&[]).unwrap();let reference=kernel(canonical.clone(),&plan);
        let mut wire=canonical.clone();wire.term.gate.left^=1;let wrong=kernel(wire,&plan);assert_ne!(at(&reference.banks,true,0),at(&wrong.banks,true,0));
        let mut row=canonical.clone();row.family_row=1;let wrong=kernel(row,&plan);assert_ne!(at(&reference.banks,true,0),at(&wrong.banks,true,0));
        let mut coefficient=canonical.clone();coefficient.term.gate.c1+=Fr::one();let wrong=kernel(coefficient,&plan);assert_ne!(at(&reference.banks,true,0),at(&wrong.banks,true,0));
        let mut weight=EdgePrefixPlan::new(8,&[]).unwrap();weight.weights[0]+=Fr::one();let wrong=kernel(canonical,&weight);
        assert_ne!(at(&reference.banks,true,0),at(&wrong.banks,true,0));
        fn execute<I:EdgeInput>(edges:&[EdgeTerm],circuit:&crate::sparse::Circuit,input:&mut I,direct:bool,off_u:bool,off_v:bool)->(GkrProof,InputClaim,Transcript,bool,bool){
            let shape=crate::sparse::validate(circuit,0).unwrap();let mut t=Transcript::new(b"direct-full-toy-v1");
            let(proof,claim,u,v,_)=prove_edge_terms_strategy_for_test(3,3,0,0,&[0],direct,off_u,off_v,MAX_EDGE_INCREMENTAL_LOCAL_BYTES,input,
                |left,owner,sink|{for e in edges{if (if left{e.term.gate.left}else{e.term.gate.right})/8==owner{sink(e.clone())?;}}Ok(())},
                &mut t,|t|t.append_bytes(b"fixture",b"direct-prefix-bilinear"),|r,u,v|crate::sparse::wiring(circuit,&shape,r,u,v).map_err(|e|e.to_string()),&mut |_|Ok(())).unwrap();
            (proof,claim,t,u,v)
        }
        for boolean in [true,false]{
            let values:Vec<Fr>=(0..64).map(|i|Fr::from(if boolean{((i*7+i/3)&1)as u64}else{(i+2)as u64})).collect();
            let mut edges=Vec::new();for source in 0..8{let left=source*8+source;let right=((source+5)%8)*8+(source+1)%8;
                let(c1,c2,c3)=(Fr::from(2u64),Fr::from(3u64),Fr::from(5u64));edges.push(EdgeTerm{source_slot:source,family_row:0,term:Term{row:source,
                    gate:Gate{left,right,c0:-(c1*values[left]+c2*values[right]+c3*values[left]*values[right]),c1,c2,c3}}});}
            for c0 in [Fr::one(),-Fr::one(),Fr::zero()]{edges.push(EdgeTerm{source_slot:7,family_row:0,term:Term{row:7,
                gate:Gate{left:0,right:0,c0,c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}}});}
            let circuit=crate::sparse::Circuit{input_len:64,row_count:8,terms:edges.iter().map(|e|e.term.clone()).collect()};let shape=crate::sparse::validate(&circuit,0).unwrap();
            let mut resident_t=Transcript::new(b"direct-full-toy-v1");let(resident,resident_claim)=crate::sparse::prove_with_binding(&circuit,&values,0,&mut resident_t,
                |t|t.append_bytes(b"fixture",b"direct-prefix-bilinear")).unwrap();let encoded=gkr::encode_proof(&resident).unwrap();
            let same=|out:(GkrProof,InputClaim,Transcript,bool,bool),off_u:bool,off_v:bool|{
                assert_eq!((out.3,out.4),(!off_u,!off_v));assert_eq!(gkr::encode_proof(&out.0).unwrap(),encoded);assert_eq!(out.1,resident_claim);
                assert_eq!(gkr::mle(&values,&out.1.point).unwrap(),out.1.value);
                assert_eq!((out.2.challenges(),out.2.raw_queries(),out.2.bytes_absorbed()),(resident_t.challenges(),resident_t.raw_queries(),resident_t.bytes_absorbed()));
                assert_eq!(out.2.clone().challenge_scalar(b"direct-toy-next"),resident_t.clone().challenge_scalar(b"direct-toy-next"));
                let mut verifier=Transcript::new(b"direct-full-toy-v1");let checked=gkr::verify_with_wiring(&[6],8,&out.0,&mut verifier,
                    |t|t.append_bytes(b"fixture",b"direct-prefix-bilinear"),|_,r,u,v|crate::sparse::wiring(&circuit,&shape,r,u,v)).unwrap();assert_eq!(checked,out.1);
                assert_eq!(verifier.clone().challenge_scalar(b"direct-toy-next"),out.2.clone().challenge_scalar(b"direct-toy-next"));
            };
            for(off_u,off_v)in [(false,false),(true,false),(false,true),(true,true)]{for direct in [false,true]{
                let mut old=CopyCache::declared(|owner|Ok(values[owner*8..(owner+1)*8].to_vec()),8,8);same(execute(&edges,&circuit,&mut old,direct,off_u,off_v),off_u,off_v);
                if boolean{let mut packed=PackedEdgeInput::new(8,8,|owner|{let mut byte=0;for i in 0..8{if values[owner*8+i].is_one(){byte|=1<<i;}}Ok(vec![byte])}).unwrap();
                    same(execute(&edges,&circuit,&mut packed,direct,off_u,off_v),off_u,off_v);}
            }}
            let mut changed=resident.clone();changed.layers[0].rounds[0][0]+=Fr::one();let mut bad_t=Transcript::new(b"direct-full-toy-v1");
            assert_eq!(gkr::verify_with_wiring(&[6],8,&changed,&mut bad_t,|t|t.append_bytes(b"fixture",b"direct-prefix-bilinear"),
                |_,r,u,v|crate::sparse::wiring(&circuit,&shape,r,u,v)).unwrap_err(),GkrError::SumcheckIdentity);
        }
    }

    pub(super) fn packed_input_controls(){
        use std::cell::{Cell,RefCell};
        for byte in 0u8..=255{
            let mut packed=PackedEdgeInput::new(8,1,|_|Ok(vec![byte])).unwrap();
            for wire in 0..8{assert_eq!(packed.value(0,wire).unwrap(),Fr::from(((byte>>wire)&1)as u64));}
            assert_eq!(packed.vector(0).unwrap(),(0..8).map(|i|Fr::from(((byte>>i)&1)as u64)).collect::<Vec<_>>());
            let m=packed.metrics();assert_eq!((m.logical_gets,m.scalar_gets,m.successful_loads,m.vector_expansions,m.expanded_fields),(9,8,1,1,8));
            assert_eq!(packed.vector_clone_increment(),0);
        }
        let packets:Vec<Vec<u8>>=(0..8).map(|owner|vec![owner as u8*29,255-owner as u8*17]).collect();
        let legacy_log=RefCell::new(Vec::new());let packed_log=RefCell::new(Vec::new());
        let mut legacy=CopyCache::declared(|owner|{legacy_log.borrow_mut().push(owner);Ok((0..16).map(|wire|
            Fr::from(((packets[owner][wire/8]>>(wire%8))&1)as u64)).collect())},16,8);
        let mut packed=PackedEdgeInput::new(16,8,|owner|{packed_log.borrow_mut().push(owner);Ok(packets[owner].clone())}).unwrap();
        let pattern=[(0,false),(1,true),(2,false),(3,true),(4,false),(0,true),(4,true),(5,false),(6,true),(7,false),(1,true)];
        for (owner,vector) in pattern{if vector{assert_eq!(legacy.vector(owner).unwrap(),packed.vector(owner).unwrap());}
            else{for wire in [0,7,8,15]{assert_eq!(legacy.value(owner,wire).unwrap(),packed.value(owner,wire).unwrap());}}}
        assert_eq!(*legacy_log.borrow(),*packed_log.borrow());assert!(packed_log.borrow().len()>4);
        assert_eq!(legacy.vector_clone_increment(),1);let m=packed.metrics();
        assert_eq!((m.logical_gets,m.scalar_gets,m.vector_expansions,m.expanded_fields),(26,20,6,96));
        assert_eq!(m.packed_bytes,m.successful_loads*2);assert!(m.cache_capacity_peak_bytes<=8+m.metadata_capacity_bytes);
        for (width,owners,error) in [(7,1,"packed edge width"),(9,1,"packed edge width"),(2097152,1,"packed edge width"),
            (8,0,"packed edge owners"),(8,4097,"packed edge owners")]{
            assert_eq!(PackedEdgeInput::new(width,owners,|_|Ok(vec![0u8])).err().unwrap(),error);
        }
        assert!(PackedEdgeInput::new(1048576,4096,|_|Ok(vec![0u8;131072])).is_ok());
        let calls=Cell::new(0);let mut domain=PackedEdgeInput::new(8,2,|_|{calls.set(calls.get()+1);Ok(vec![0])}).unwrap();
        assert_eq!(domain.value(2,0).unwrap_err(),"packed edge owner range");
        assert_eq!(domain.value(0,8).unwrap_err(),"packed edge wire range");assert_eq!(domain.vector(2).unwrap_err(),"packed edge owner range");assert_eq!(calls.get(),0);
        for (kind,error) in [(0,"packet I/O"),(1,"packed edge packet length"),(2,"packed edge packet length"),(3,"packed edge packet capacity")]{
            let mut faulty=PackedEdgeInput::new(8,1,|_|{match kind{0=>Err("packet I/O".into()),1=>Ok(Vec::new()),2=>Ok(vec![0;2]),
                _=>{let mut bytes=Vec::with_capacity(2);bytes.push(0);Ok(bytes)}}}).unwrap();
            assert_eq!(faulty.value(0,0).unwrap_err(),error);let m=faulty.metrics();
            assert_eq!((m.logical_gets,m.scalar_gets,m.successful_loads,m.vector_expansions),(0,0,0,0));assert!(faulty.entries.is_empty());
        }
        struct FaultInput{width:usize,owners:usize,mode:u8,calls:usize}
        impl EdgeInput for FaultInput{
            fn width(&self)->usize{self.width}fn owners(&self)->usize{self.owners}
            fn value(&mut self,_:usize,_:usize)->Result<Fr,String>{self.calls+=1;Ok(Fr::zero())}
            fn vector(&mut self,_:usize)->Result<Vec<Fr>,String>{self.calls+=1;match self.mode{
                4=>Ok(vec![Fr::zero();7]),5=>{let mut v=Vec::with_capacity(9);v.resize(8,Fr::zero());Ok(v)},_=>Ok(vec![Fr::zero();8])}}
            fn capacity_bytes(&self)->Option<usize>{match self.mode{2=>None,3=>Some(2),6 if self.calls>0=>Some(2),_=>Some(0)}}
            fn cache_budget_bytes(&self)->Result<usize,String>{if self.mode==1{Err("edge input cache budget overflow".into())}else{Ok(1)}}
            fn vector_clone_increment(&self)->u64{0}
        }
        for (width,owners,mode,error) in [(16,1,0,"edge input declared width mismatch"),(8,2,0,"edge input declared owners mismatch"),
            (8,1,1,"edge input cache budget overflow"),(8,1,2,"edge input cache capacity overflow"),(8,1,3,"edge input live cache exceeds declared budget")]{
            let mut bad=FaultInput{width,owners,mode,calls:0};let mut transcript=Transcript::new(b"packed-edge-admission");let before=transcript.clone();let visits=Cell::new(0);
            let result=prove_edge_terms_with_input_for_test(3,0,0,0,&[0],0,&mut bad,|_,_,_|{visits.set(visits.get()+1);Ok(())},
                &mut transcript,|_|panic!("binding reached on rejected input"),|_,_,_|panic!("wiring reached on rejected input"));
            assert_eq!(result.err().unwrap(),error);assert_eq!(bad.calls,0);assert_eq!(visits.get(),0);assert_eq!(transcript.challenges(),before.challenges());
            assert_eq!(transcript.raw_queries(),before.raw_queries());assert_eq!(transcript.bytes_absorbed(),before.bytes_absorbed());
            assert_eq!(transcript.clone().challenge_scalar(b"admission-continuation"),before.clone().challenge_scalar(b"admission-continuation"));
            let result=edge_u0_round_with_input_for_test(3,0,0,0,&[0],&[0],&[],|_,_,_|{visits.set(visits.get()+1);Ok(())},&mut bad,|_,_|Ok(()));
            assert_eq!(result.err().unwrap(),error);assert_eq!((bad.calls,visits.get()),(0,0));
        }
        for (mode,error) in [(4,"edge input vector width mismatch"),(5,"edge input vector capacity mismatch"),(6,"edge input live cache exceeds declared budget")]{
            let mut bad=FaultInput{width:8,owners:1,mode,calls:0};assert_eq!(edge_input_vector(&mut bad,0,8).unwrap_err(),error);
        }
        let mut bad=FaultInput{width:8,owners:1,mode:6,calls:0};assert_eq!(edge_input_value(&mut bad,0,0).unwrap_err(),"edge input live cache exceeds declared budget");
        let mut overflow=CopyCache::declared(|_|Ok(Vec::new()),usize::MAX,1);
        assert_eq!(edge_input_geometry(&overflow,usize::MAX,1).unwrap_err(),"edge input cache budget overflow");
        overflow.width=8;assert!(edge_input_geometry(&overflow,8,1).is_ok());
        assert_eq!(PackedEdgeInput::<fn(usize)->Result<Vec<u8>,String>>::add(u64::MAX,1).unwrap_err(),"packed edge counter overflow");
        let reads=RefCell::new(Vec::new());let mut unused=PackedEdgeInput::new(8,8,|owner|{reads.borrow_mut().push(owner);
            if owner==7{Err("unused endpoint was read".into())}else{Ok(vec![0])}}).unwrap();
        let result=edge_u0_round_with_input_for_test(3,3,0,0,&[0],&[1,0,0,0,0,0,0,0],&[Fr::from(2u64);3],
            |left,owner,sink|{assert!(left);if owner==0{sink(EdgeTerm{source_slot:0,family_row:0,term:Term{row:0,
                gate:Gate{left:0,right:63,c0:Fr::zero(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}}})?;}Ok(())},&mut unused,|_,_|Ok(()));
        assert_eq!(result.err().unwrap(),"unused endpoint was read");assert_eq!(*reads.borrow(),vec![7]);
        let input:Vec<Fr>=(0..64).map(|i|Fr::from(((i*13+i/7)&1)as u64)).collect();let members=[2usize,1];
        let mut edges=Vec::new();for owner in 0..8{let family=owner%2;let local=owner%(1<<members[family]);let left=owner*8+owner;let right=((owner+5)%8)*8+(owner+1)%8;
            let(c1,c2,c3)=(Fr::from(2u64),Fr::from(3u64),Fr::from(5u64));edges.push(EdgeTerm{source_slot:(owner+3)%8,family_row:(family<<2)|local,
                term:Term{row:local,gate:Gate{left,right,c0:-(c1*input[left]+c2*input[right]+c3*input[left]*input[right]),c1,c2,c3}}});}
        for c0 in [Fr::one(),-Fr::one(),Fr::zero()]{edges.push(EdgeTerm{source_slot:7,family_row:3,
            term:Term{row:3,gate:Gate{left:0,right:0,c0,c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}}});}
        let circuit=crate::sparse::Circuit{input_len:64,row_count:64,terms:edges.iter().map(|e|Term{
            row:((e.family_row>>2)<<5)|(e.source_slot<<members[e.family_row>>2])|(e.family_row&3),gate:e.term.gate.clone()}).collect()};
        let shape=crate::sparse::validate(&circuit,0).unwrap();let emit=|left:bool,owner:usize,sink:&mut dyn FnMut(EdgeTerm)->Result<(),String>|{
            for e in &edges{if (if left{e.term.gate.left}else{e.term.gate.right})/8==owner{sink(e.clone())?;}}Ok(())};
        let bind=|t:&mut Transcript|t.append_bytes(b"packed-edge-proof",b"boolean-cross-source-v1");let domain=b"packed-edge-full-proof";
        let same_t=|a:&Transcript,b:&Transcript|{assert_eq!((a.challenges(),a.raw_queries(),a.bytes_absorbed()),(b.challenges(),b.raw_queries(),b.bytes_absorbed()));
            assert_eq!(a.clone().challenge_scalar(b"packed-proof-continuation"),b.clone().challenge_scalar(b"packed-proof-continuation"));};
        let mut resident_t=Transcript::new(domain);let(resident,resident_claim)=crate::sparse::prove_with_binding(&circuit,&input,0,&mut resident_t,bind).unwrap();
        let resident_bytes=gkr::encode_proof(&resident).unwrap();
        for limit in [0,MAX_EDGE_INCREMENTAL_LOCAL_BYTES]{
            let mut old_t=Transcript::new(domain);let(old,old_claim,old_u,old_v)=prove_edge_terms_with_cache_limit_for_test(3,3,2,1,&members,limit,
                emit,|owner|Ok(input[owner*8..(owner+1)*8].to_vec()),&mut old_t,bind,|r,u,v|crate::sparse::wiring(&circuit,&shape,r,u,v).map_err(|e|e.to_string())).unwrap();
            let mut packed=PackedEdgeInput::new(8,8,|owner|{let mut byte=0u8;for bit in 0..8{if input[owner*8+bit].is_one(){byte|=1<<bit;}}Ok(vec![byte])}).unwrap();
            let mut new_t=Transcript::new(domain);let(new,new_claim,new_u,new_v)=prove_edge_terms_with_input_for_test(3,3,2,1,&members,limit,&mut packed,
                emit,&mut new_t,bind,|r,u,v|crate::sparse::wiring(&circuit,&shape,r,u,v).map_err(|e|e.to_string())).unwrap();
            assert_eq!((old_u,old_v),(limit!=0,limit!=0));assert_eq!((new_u,new_v),(old_u,old_v));
            assert_eq!(gkr::encode_proof(&old).unwrap(),resident_bytes);assert_eq!(gkr::encode_proof(&new).unwrap(),resident_bytes);
            assert_eq!(old_claim,resident_claim);assert_eq!(new_claim,old_claim);same_t(&new_t,&old_t);same_t(&new_t,&resident_t);
            assert_eq!(gkr::mle(&input,&new_claim.point).unwrap(),new_claim.value);
            for proof in [&old,&new]{let mut verifier=Transcript::new(domain);let claim=gkr::verify_with_wiring(&[6],64,proof,&mut verifier,bind,
                |_,r,u,v|crate::sparse::wiring(&circuit,&shape,r,u,v)).unwrap();assert_eq!(claim,new_claim);same_t(&verifier,&new_t);}
            assert_eq!(packed.vector_clone_increment(),0);assert!(packed.metrics().vector_expansions>0);
        }
        edge_sparse_replay_four_modes_match_resident_and_reject_mutants();
    }

    mod native_role1{
        use super::*;
        use ark_serialize::CanonicalSerialize;

        const COPIES:usize=4096;
        const SHORT:usize=3072;

        fn groups()->Vec<usize>{(0..COPIES).map(|owner|usize::from(owner==SHORT)).collect()}
        fn templates()->[Vec<Term>;2]{
            let equality=Term{row:0,gate:Gate{left:0,right:1,c0:Fr::zero(),c1:Fr::one(),c2:-Fr::one(),c3:Fr::zero()}};
            let boolean=Term{row:1,gate:Gate{left:0,right:0,c0:Fr::zero(),c1:-Fr::one(),c2:Fr::zero(),c3:Fr::one()}};
            [vec![equality.clone(),boolean],vec![equality]]
        }
        fn mixed_bit(owner:usize)->Fr{
            if owner==SHORT||owner==4095{return Fr::one();}
            let mut h=(owner as u32).wrapping_add(0x9E3779B9);
            h=(h^(h>>16)).wrapping_mul(0x85EBCA6B);h=(h^(h>>13)).wrapping_mul(0xC2B2AE35);
            Fr::from(((h^(h>>16))&1) as u64)
        }
        fn scalar_eq(point:&[Fr],index:usize)->Fr{
            point.iter().enumerate().fold(Fr::one(),|weight,(bit,q)|weight*if index&(1<<bit)==0{Fr::one()-q}else{*q})
        }
        fn dense_coefficients(gates:&[Gate],r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String>{
            if (r.len(),u.len(),v.len())!=(13,13,13){return Err("toy dense wiring dimensions".into());}
            let mut coefficients=[Fr::zero();4];
            for (row,gate) in gates.iter().enumerate(){
                let weight=scalar_eq(r,row)*scalar_eq(u,gate.left)*scalar_eq(v,gate.right);
                for (out,value) in coefficients.iter_mut().zip([gate.c0,gate.c1,gate.c2,gate.c3]){*out+=weight*value;}
            }
            Ok(coefficients)
        }
        fn compare_transcripts(a:&Transcript,b:&Transcript){
            assert_eq!(a.challenges(),b.challenges());assert_eq!(a.raw_queries(),b.raw_queries());assert_eq!(a.bytes_absorbed(),b.bytes_absorbed());
            assert_eq!(a.clone().challenge_scalar(b"native-role1-toy-continuation"),b.clone().challenge_scalar(b"native-role1-toy-continuation"));
        }

        #[test]
        fn native_role1_thirteen_bit_dense_differential(){
            let grouped=groups();let terms=templates();let admission=GroupedVAdmission::try_new(12,&grouped,&[2,1]).unwrap();
            let input=(0..COPIES).flat_map(|owner|[mixed_bit(owner);2]).collect::<Vec<_>>();
            let zero=Gate{left:0,right:0,c0:Fr::zero(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()};
            let mut dense=vec![zero.clone();8192];let mut terms_seen=0usize;
            for owner in 0..COPIES{for term in &terms[grouped[owner]]{
                let mut gate=term.gate.clone();gate.left+=2*owner;gate.right+=2*owner;
                dense[2*owner+term.row]=gate;terms_seen+=1;
            }}
            assert_eq!(terms_seen,8191);assert_eq!(dense[6145],zero);assert_eq!(input[2*4095],Fr::one());
            let bind=|t:&mut Transcript|t.append_bytes(b"native-role1-toy",b"local1/copy12/row1;zero-short-row");
            let layers=vec![dense.clone()];let mut resident_t=Transcript::new(b"native-role1-thirteen-bit-v1");
            let (resident,resident_claim)=gkr::prove_with_binding(&input,&layers,&mut resident_t,bind).unwrap();
            let mut streamed_t=Transcript::new(b"native-role1-thirteen-bit-v1");let visits=std::cell::Cell::new([0usize;COPIES]);
            let (streamed,streamed_claim,group_stats,stats)=prove_with_boolean_u_grouped_v_for_test(1,12,1,0,&[1],Some(0),&admission,
                |owner|Ok(input[2*owner..2*owner+2].to_vec()),&mut streamed_t,bind,|owner,sink|{
                    let mut seen=visits.get();assert_eq!(seen[owner],0,"canonical callback replay");seen[owner]+=1;visits.set(seen);
                    for term in &terms[grouped[owner]]{sink(term.clone())?;}Ok(())
                },|r,u,v|dense_coefficients(&dense,r,u,v)).unwrap();
            assert_eq!(visits.get(),[1;COPIES]);assert_eq!(streamed,resident);assert_eq!(streamed_claim,resident_claim);
            compare_transcripts(&streamed_t,&resident_t);
            assert_eq!(group_stats.baseline_term_callbacks,8191);assert_eq!(group_stats.group_owner_counts,[4095,1]);
            assert_eq!(stats.prefix_builds,2);assert_eq!(stats.shared_term_iterations,6);assert_eq!(stats.owner_term_selections,16382);
            assert_eq!(stats.boolean_checked_loads,24576);assert_eq!(stats.boolean_checked_fields,49152);
            assert_eq!(streamed.layers[0].rounds.len(),26);assert_eq!(streamed.layers[0].line_coefficients.len(),14);
            // Low local round then all twelve high rounds, in each phase.
            assert_eq!(streamed.layers[0].rounds[0],resident.layers[0].rounds[0]);
            assert_eq!(streamed.layers[0].rounds[1..13],resident.layers[0].rounds[1..13]);
            assert_eq!(streamed.layers[0].rounds[13],resident.layers[0].rounds[13]);
            assert_eq!(streamed.layers[0].rounds[14..26],resident.layers[0].rounds[14..26]);
            let encoded=gkr::encode_proof(&streamed).unwrap();let scalar_count=26*3+2+14;
            assert_eq!(scalar_count,94);assert_eq!(encoded.len(),scalar_count*Fr::zero().compressed_size());assert_eq!(encoded.len(),3008);
            assert_eq!(gkr::encode_proof(&resident).unwrap(),encoded);
            let decoded=gkr::decode_dimensions(&[13],&encoded).unwrap();assert_eq!(decoded,streamed);
            let mut verifier_t=Transcript::new(b"native-role1-thirteen-bit-v1");
            let verified=gkr::verify_with_wiring(&[13],8192,&decoded,&mut verifier_t,bind,
                |_,r,u,v|dense_coefficients(&dense,r,u,v).map_err(|_|GkrError::PointDimension)).unwrap();
            assert_eq!(verified,streamed_claim);compare_transcripts(&verifier_t,&streamed_t);
            assert_eq!(gkr::mle(&input,&verified.point).unwrap(),verified.value);
            // Isolate the absent short row with a Boolean row selector but
            // general input points. A zero residual does not hide its wiring.
            let row=(0..13).map(|bit|Fr::from(((6145usize>>bit)&1) as u64)).collect::<Vec<_>>();
            let u=(0..13).map(|bit|Fr::from((bit*2+3) as u64)).collect::<Vec<_>>();
            let v=(0..13).map(|bit|Fr::from((bit*2+31) as u64)).collect::<Vec<_>>();
            assert_eq!(dense_coefficients(&dense,&row,&u,&v).unwrap(),[Fr::zero();4]);
            let mut added=dense.clone();let mut omitted=terms[0][1].gate.clone();omitted.left+=2*SHORT;omitted.right+=2*SHORT;added[6145]=omitted;
            assert_ne!(dense_coefficients(&added,&row,&u,&v).unwrap(),[Fr::zero();4],"added absent-row Boolean term must be observable");
        }

        #[test]
        fn native_role1_owner_basis_handoff_differential(){
            let grouped=groups();let terms=templates();let captured=vec![Some(terms[0].clone()),Some(terms[1].clone())];
            let admission=GroupedVAdmission::try_new(12,&grouped,&[2,1]).unwrap();
            let r=(0..13).map(|bit|Fr::from((2*bit+29) as u64)).collect::<Vec<_>>();
            let row_lookup=TensorRowWeightLookup::new(&r,12,1,&[1]);
            let factor=OneFamilyRowFactor::try_new(&r,12,1,0,&[1],row_lookup.local_table(1)).unwrap();
            let group_stats=GroupedVStats{group_count:2,group_owner_counts:vec![4095,1],group_term_counts:vec![2,1],..Default::default()};
            let q=(0..12).map(|bit|Fr::from((2*bit+3) as u64)).collect::<Vec<_>>();
            for supported in (0..12).map(|bit|1usize<<bit).chain(std::iter::once(4095)){
                let mut stats=BooleanUPreweightStats{u_preflight_capacity_bound_bytes:boolean_u_prebind_capacity_bound(1,12,1,&admission).unwrap(),..Default::default()};
                let mut transcript=Transcript::new(b"native-role1-basis-handoff");let mut claim=Fr::zero();let mut rounds=Vec::new();let mut u_local=Vec::with_capacity(1);
                let (a,b,high_x,_weights)=prove_boolean_u_prefixes(2,1,COPIES,&captured,&admission,&row_lookup,&factor,&group_stats,COPIES,
                    r.capacity(),&mut |owner|Ok(vec![Fr::from(usize::from(owner==supported) as u64);2]),
                    &mut claim,&mut rounds,&mut u_local,&mut transcript,&mut stats).unwrap();
                assert_eq!(a.len(),COPIES);assert_eq!(b.len(),COPIES);assert_eq!(high_x.len(),COPIES);
                assert_eq!(high_x.iter().filter(|value|value.is_one()).count(),1);assert_eq!(high_x[supported],Fr::one());
                let mut actual=high_x.clone();for coordinate in &q{gkr::fold(&mut actual,*coordinate);}
                let full=(0..COPIES).flat_map(|owner|[Fr::from(usize::from(owner==supported) as u64);2]).collect::<Vec<_>>();
                let mut point=u_local.clone();point.extend_from_slice(&q);
                let source_mle=gkr::mle(&full,&point).unwrap();let expected=scalar_eq(&q,supported);
                assert_eq!(actual.as_slice(),[expected]);assert_eq!(source_mle,expected);
                if supported!=4095{
                    let j=supported.trailing_zeros() as usize;let next=(j+1)%12;
                    let mut cleared=vec![Fr::zero();COPIES];cleared[supported&!(1<<j)]=high_x[supported];
                    for coordinate in &q{gkr::fold(&mut cleared,*coordinate);}
                    let other=q.iter().enumerate().filter(|(bit,_)|*bit!=j).fold(Fr::one(),|p,(_,coordinate)|p*(Fr::one()-coordinate));
                    let delta=(Fr::from(2u64)*q[j]-Fr::one())*other;
                    assert!(!delta.is_zero());assert_eq!(actual[0]-cleared[0],delta,"clear owner bit {j}");
                    let mut swapped_q=q.clone();swapped_q.swap(j,next);let mut swapped=high_x.clone();
                    for coordinate in &swapped_q{gkr::fold(&mut swapped,*coordinate);}
                    assert_ne!(actual[0],swapped[0],"swap owner coordinates {j}/{next}");
                }
            }
        }

        fn native_census()->GroupedVAdmission{GroupedVAdmission::try_new(12,&groups(),&[396561,388369]).unwrap()}
        fn reject_before_activity(input:usize,copies:usize,rows:usize,family:usize,members:&[usize],cache:usize,
            direct:bool,fixed:Option<&FixedCoreVTemplate<'_>>,boolean:bool,admission:Option<&GroupedVAdmission>,policy:GroupedDimensionPolicy){
            let loaded=std::cell::Cell::new(false);let bound=std::cell::Cell::new(false);let visited=std::cell::Cell::new(false);
            let mut group_stats=GroupedVStats::default();let mut u_stats=BooleanUPreweightStats::default();
            let mut transcript=Transcript::new(b"native-role1-policy-negative");let before=transcript.bytes_absorbed();
            let result=prove_inner(input,copies,rows,family,members,None,None,None,cache,direct,fixed,None,None,None,None,None,
                MAX_FIXED_V_COMMON_STATE_BYTES,admission,Some(&mut group_stats),if boolean{Some(&mut u_stats)}else{None},policy,
                |_|{loaded.set(true);Err("unexpected native negative source read".into())},&mut transcript,
                |_|{bound.set(true);Ok(())},|_,_|{visited.set(true);Ok(())},|_,_,_|Ok([Fr::zero();4]));
            assert!(result.is_err());assert!(!loaded.get()&&!bound.get()&&!visited.get());
            assert_eq!(transcript.challenges(),0);assert_eq!(transcript.bytes_absorbed(),before);
        }

        #[test]
        fn native_role3_exact_policy_and_observer_are_fail_closed(){
            let census=GroupedVAdmission::try_new(12,&vec![0usize;4096],&[288158]).unwrap();
            let policy=GroupedDimensionPolicy::NativeRole3Exact{extra_capacity_bytes:0};
            assert!(policy.validate_route(13,12,14,0,&[14],0,true,false,true,Some(&census)).is_ok());
            assert_eq!(boolean_u_prebind_capacity_bound_with_policy(13,12,14,&census,policy),Some(196132592));
            for (input,copies,rows,family,members,cache,direct,boolean) in [
                (12,12,14,0,vec![14],0,true,true),(14,12,14,0,vec![14],0,true,true),(13,11,14,0,vec![14],0,true,true),
                (13,13,14,0,vec![14],0,true,true),(13,12,13,0,vec![14],0,true,true),(13,12,15,0,vec![14],0,true,true),
                (13,12,14,1,vec![14],0,true,true),(13,12,14,0,vec![13],0,true,true),(13,12,14,0,vec![14],1,true,true),
                (13,12,14,0,vec![14],0,false,true),(13,12,14,0,vec![14],0,true,false)]{
                reject_before_activity(input,copies,rows,family,&members,cache,direct,None,boolean,Some(&census),policy);
            }
            reject_before_activity(13,12,14,0,&[14],0,true,None,true,Some(&census),GroupedDimensionPolicy::Generic24);
            for fault in 0..4{let mut bad=GroupedVAdmission::try_new(12,&vec![0usize;4096],&[288158]).unwrap();
                match fault{0=>bad.group_by_copy[4095]=1,1=>bad.expected_terms_per_group[0]+=1,
                    2=>bad.group_by_copy=vec![0;4095].into_boxed_slice(),_=>bad.expected_terms_per_group=vec![288158,288158].into_boxed_slice()}
                reject_before_activity(13,12,14,0,&[14],0,true,None,true,Some(&bad),policy);
            }
            let mut t=Transcript::new(b"native-role3-observer-control");let original=t.clone();
            let error=native_role3_transaction(&mut t,|working|->Result<(),String>{
                let _scope=NativeRole3ObserverScope::begin(std::time::Instant::now())?;
                working.challenge_scalar(b"working-only");native_role3_observe("isolated-wrong-stage")
            }).unwrap_err();assert_eq!(error,"native role3 observer phase order");
            assert_eq!((t.challenges(),t.raw_queries(),t.bytes_absorbed()),(original.challenges(),original.raw_queries(),original.bytes_absorbed()));
            assert_eq!(t.clone().challenge_scalar(b"after-error"),original.clone().challenge_scalar(b"after-error"));
            assert!(NATIVE_ROLE3_OBSERVER.with(|x|x.borrow().is_none()));
            {let _scope=NativeRole3ObserverScope::begin(std::time::Instant::now()).unwrap();
                assert_eq!(NativeRole3ObserverScope::begin(std::time::Instant::now()).err().unwrap(),"native role3 observer already active");}
            assert!(NATIVE_ROLE3_OBSERVER.with(|x|x.borrow().is_none()));
            let unwind=std::panic::catch_unwind(||{let _scope=NativeRole3ObserverScope::begin(std::time::Instant::now()).unwrap();panic!("isolated observer unwind");});
            assert!(unwind.is_err());assert!(NATIVE_ROLE3_OBSERVER.with(|x|x.borrow().is_none()));
            assert!(2*std::mem::size_of::<NativeRole3Observer>()+512<1024*1024);
        }

        #[test]
        fn native_role1_exact_policy_rejects_each_geometry_field(){
            let admission=native_census();let policy=GroupedDimensionPolicy::NativeRole1Exact{extra_capacity_bytes:0};
            assert!(policy.validate_route(20,12,19,0,&[19],0,true,false,true,Some(&admission)).is_ok());
            let circuit=crate::sparse::Circuit{input_len:2,row_count:1,terms:vec![templates()[0][0].clone()]};
            let fixed=FixedCoreVTemplate::try_new(&circuit,1,0,0).unwrap();
            for fault in 0..12{
                let(mut input,mut copy,mut rows,mut family,mut members,mut cache,mut direct,mut fixed_arg,mut boolean,grouped)=
                    (20,12,19,0,vec![19],0,true,None,true,Some(&admission));
                match fault{0=>input=19,1=>input=21,2=>copy=11,3=>copy=13,4=>rows=18,5=>rows=20,
                    6=>family=1,7=>members[0]=18,8=>cache=1,9=>direct=false,10=>fixed_arg=Some(&fixed),_=>boolean=false}
                reject_before_activity(input,copy,rows,family,&members,cache,direct,fixed_arg,boolean,grouped,policy);
            }
            reject_before_activity(20,12,19,0,&[19],0,true,None,true,None,policy);
            assert!(boolean_u_prebind_capacity_bound_with_policy(20,12,19,&admission,policy).is_some());
            assert!(grouped_v_prebind_capacity_bound_with_policy(20,12,19,&admission,policy).is_some());
            assert!(boolean_u_prebind_capacity_bound_with_policy(19,12,19,&admission,policy).is_none());
            assert!(grouped_v_prebind_capacity_bound_with_policy(20,12,18,&admission,policy).is_none());
        }

        #[test]
        fn native_role1_exact_policy_rejects_each_group_census_fault(){
            let policy=GroupedDimensionPolicy::NativeRole1Exact{extra_capacity_bytes:0};
            for fault in 0..6{
                let mut admission=native_census();
                match fault{0=>admission.group_by_copy.swap(3071,3072),1=>admission.group_by_copy[4095]=1,
                    2=>admission.expected_terms_per_group[0]+=1,3=>admission.expected_terms_per_group[1]+=1,
                    4=>admission.expected_terms_per_group.swap(0,1),_=>admission.group_by_copy=vec![0;4095].into_boxed_slice()}
                reject_before_activity(20,12,19,0,&[19],0,true,None,true,Some(&admission),policy);
                assert!(boolean_u_prebind_capacity_bound_with_policy(20,12,19,&admission,policy).is_none());
                assert!(grouped_v_prebind_capacity_bound_with_policy(20,12,19,&admission,policy).is_none());
            }
            let admission=native_census();let extra=GroupedDimensionPolicy::NativeRole1Exact{extra_capacity_bytes:128};
            assert_eq!(boolean_u_prebind_capacity_bound_with_policy(20,12,19,&admission,extra).unwrap(),
                boolean_u_prebind_capacity_bound_with_policy(20,12,19,&admission,policy).unwrap()+128);
            assert_eq!(grouped_v_prebind_capacity_bound_with_policy(20,12,19,&admission,extra).unwrap(),
                grouped_v_prebind_capacity_bound_with_policy(20,12,19,&admission,policy).unwrap()+128);
            // The same additional token bytes must reach the actual row/U
            // inventories, rather than only enlarging their preflight bound.
            let terms=templates();let captured=vec![Some(terms[0].clone()),Some(terms[1].clone())];
            let toy=GroupedVAdmission::try_new(12,&groups(),&[2,1]).unwrap();
            let r=vec![Fr::from(3u64);13];let lookup=TensorRowWeightLookup::new(&r,12,1,&[1]);
            let factor=OneFamilyRowFactor::try_new(&r,12,1,0,&[1],lookup.local_table(1)).unwrap();
            let mut stats=GroupedVStats::default();let rounds=Vec::new();
            let row_before=boolean_u_row_preparation_capacity_bytes(&captured,&toy,&stats,COPIES,r.capacity(),2).unwrap();
            let u_before=boolean_u_capacity_bytes(&captured,&toy,&lookup,&factor,&stats,COPIES,&rounds,r.capacity(),0,0,0,0,0,0,2).unwrap();
            stats.private_capacity_reservation_bytes=128;
            assert_eq!(boolean_u_row_preparation_capacity_bytes(&captured,&toy,&stats,COPIES,r.capacity(),2).unwrap(),row_before+128);
            assert_eq!(boolean_u_capacity_bytes(&captured,&toy,&lookup,&factor,&stats,COPIES,&rounds,r.capacity(),0,0,0,0,0,0,2).unwrap(),u_before+128);
            let overflow=GroupedDimensionPolicy::NativeRole1Exact{extra_capacity_bytes:usize::MAX};
            assert!(boolean_u_prebind_capacity_bound_with_policy(20,12,19,&admission,overflow).is_none());
            reject_before_activity(20,12,19,0,&[19],0,true,None,true,Some(&admission),overflow);
        }

        #[test]
        fn native_role1_generic_route_rejects_native32_before_activity(){
            let admission=native_census();reject_before_activity(20,12,19,0,&[19],0,true,None,true,Some(&admission),GroupedDimensionPolicy::Generic24);
            assert!(boolean_u_prebind_capacity_bound(20,12,19,&admission).is_none());assert!(grouped_v_prebind_capacity_bound(20,12,19,&admission).is_none());
        }

        #[test]
        fn native_role1_binder_error_stops_before_output_challenge(){
            let term=templates()[0][0].clone();let admission=GroupedVAdmission::try_new(0,&[0],&[1]).unwrap();
            let bind=|t:&mut Transcript|t.append_bytes(b"legacy-unit-binder",b"unchanged bytes");
            let mut legacy_t=Transcript::new(b"native-role1-binder-inverse");
            let (legacy,legacy_claim,_,_)=prove_with_boolean_u_grouped_v_for_test(1,0,1,0,&[1],Some(0),&admission,
                |_|Ok(vec![Fr::one();2]),&mut legacy_t,bind,|_,sink|sink(term.clone()),
                |r,u,v|super::explicit_global_terms_wiring(&[term.clone()],r,u,v)).unwrap();
            let mut result_t=Transcript::new(b"native-role1-binder-inverse");
            let (result,result_claim,_,_)=prove_boolean_u_grouped_with_policy_for_test(1,0,1,0,&[1],Some(0),&admission,GroupedDimensionPolicy::Generic24,
                |_|Ok(vec![Fr::one();2]),&mut result_t,|t|{bind(t);Ok(())},|_,sink|sink(term.clone()),
                |r,u,v|super::explicit_global_terms_wiring(&[term.clone()],r,u,v)).unwrap();
            assert_eq!(legacy,result);assert_eq!(legacy_claim,result_claim);compare_transcripts(&legacy_t,&result_t);
            // Exercise the legacy checked-entry wrapper without replaying its
            // large retained-header consumer solely for this Result lift.
            let mut checked_t=Transcript::new(b"native-role1-binder-inverse");
            let (checked,checked_claim)=prove_checked(1,0,1,0,&[1],None,None,None,
                |_|Ok(vec![Fr::one();2]),&mut checked_t,bind,|_,sink|sink(term.clone()),
                |r,u,v|super::explicit_global_terms_wiring(&[term.clone()],r,u,v)).unwrap();
            assert_eq!(checked,legacy);assert_eq!(checked_claim,legacy_claim);compare_transcripts(&checked_t,&legacy_t);
            let loaded=std::cell::Cell::new(0);let mut rejected_t=Transcript::new(b"native-role1-binder-inverse");
            let before=rejected_t.bytes_absorbed();
            // Two output rows make output_point sample a challenge if the
            // binder Result is ever discarded instead of propagated.
            let rejected=prove_boolean_u_grouped_with_policy_for_test(1,0,1,0,&[1],Some(0),&admission,GroupedDimensionPolicy::Generic24,
                |_|{loaded.set(loaded.get()+1);Ok(vec![Fr::one();2])},&mut rejected_t,|_|Err("isolated binding error".into()),
                |_,sink|sink(term.clone()),|r,u,v|super::explicit_global_terms_wiring(&[term.clone()],r,u,v));
            assert_eq!(rejected.unwrap_err(),"isolated binding error");assert_eq!(loaded.get(),1);
            assert_eq!(rejected_t.challenges(),0);assert_eq!(rejected_t.bytes_absorbed(),before);
        }
    }

    fn explicit_global_terms_wiring(terms:&[Term],r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String>{
        let mut out=[Fr::zero();4];
        for term in terms{
            let gate=&term.gate;
            let weight=eq_weight_at(r,term.row)*eq_weight_at(u,gate.left)*eq_weight_at(v,gate.right);
            for (sum,coefficient) in out.iter_mut().zip([gate.c0,gate.c1,gate.c2,gate.c3]){
                *sum+=weight*coefficient;
            }
        }
        Ok(out)
    }

    fn emit_global_test_edges(edges:&[EdgeTerm],mutation:Option<(usize,usize,usize)>,left:bool,slot:usize,
        sink:&mut dyn FnMut(EdgeTerm)->Result<(),String>)->Result<(),String>{
        for (index,edge) in edges.iter().enumerate(){
            let endpoint=if left{edge.term.gate.left}else{edge.term.gate.right};
            if endpoint/4==slot{
                let mut emitted=edge.clone();
                if let Some((first,last,source_slot))=mutation{
                    if (first..last).contains(&index){emitted.source_slot=source_slot;}
                }
                sink(emitted)?;
            }
        }
        Ok(())
    }

    #[test]
    fn direct_u_prefix_coefficients_match_full_build_and_fold(){
        let width=8usize;
        let input=(0..width).map(|index|Fr::from((index as u64+3)*17)).collect::<Vec<_>>();
        let terms=vec![
            Term{row:0,gate:Gate{left:1,right:5,c0:Fr::from(7u64),c1:Fr::from(2u64),c2:Fr::from(3u64),c3:Fr::from(5u64)}},
            Term{row:1,gate:Gate{left:width,right:2,c0:Fr::from(11u64),c1:Fr::zero(),c2:Fr::from(13u64),c3:Fr::zero()}},
            Term{row:2,gate:Gate{left:4,right:width,c0:Fr::from(17u64),c1:Fr::from(19u64),c2:Fr::zero(),c3:Fr::zero()}},
            Term{row:3,gate:Gate{left:width,right:width,c0:Fr::zero(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}},
            Term{row:4,gate:Gate{left:7,right:0,c0:Fr::from(23u64),c1:Fr::from(29u64),c2:Fr::from(31u64),c3:Fr::from(37u64)}},
            Term{row:5,gate:Gate{left:1,right:6,c0:Fr::from(41u64),c1:Fr::from(43u64),c2:Fr::from(47u64),c3:Fr::from(53u64)}},
        ];
        let weight=|copy:usize,row:usize|Fr::from((copy*19+row+1) as u64);
        let mut full_a=vec![Fr::zero();width];let mut full_b=vec![Fr::zero();width];
        let mut global_left_b=Fr::zero();
        for term in &terms{
            let gate=&term.gate;let scale=weight(1,term.row);
            if gate.left==width{
                let right=if gate.right==width{Fr::zero()}else{input[gate.right]};
                global_left_b+=scale*(gate.c0+gate.c2*right);
            }else{
                let right=if gate.right==width{Fr::zero()}else{input[gate.right]};
                full_a[gate.left]+=scale*(gate.c1+gate.c3*right);
                full_b[gate.left]+=scale*(gate.c0+gate.c2*right);
            }
        }
        for prefix_len in 0..=3{
            let prefix=(0..prefix_len).map(|index|Fr::from((index as u64+2)*101)).collect::<Vec<_>>();
            let prefix_weights=gkr::eq_weights(&prefix);
            assert_eq!(prefix_weights.len(),1usize<<prefix_len);
            assert!(prefix_weights.capacity()>=prefix_weights.len()
                &&prefix_weights.capacity()<=4usize.max(prefix_weights.len()));
            let mut expected_a=full_a.clone();let mut expected_b=full_b.clone();
            for challenge in &prefix{gkr::fold(&mut expected_a,*challenge);gkr::fold(&mut expected_b,*challenge);}
            expected_b[0]+=global_left_b*prefix_weights[0];
            let (actual_a,mut actual_b)=direct_u_prefix_coefficients(width,&prefix,&prefix_weights,1,&input,
                |owner,row|weight(owner,row),|sink|{for term in &terms{sink(term.clone())?;}Ok(())}).unwrap();
            actual_b[0]+=global_left_b*prefix_weights[0];
            assert_eq!(actual_a,expected_a,"A prefix length {prefix_len}");
            assert_eq!(actual_b,expected_b,"B prefix length {prefix_len}");
            assert_eq!(actual_a.len(),width>>prefix_len);
            assert!(actual_a.capacity()>=actual_a.len()&&actual_a.capacity()<=2*actual_a.len().max(1));
            assert!(actual_b.capacity()>=actual_b.len()&&actual_b.capacity()<=2*actual_b.len().max(1));
            if prefix_len>1{
                let reversed_prefix=prefix.iter().copied().rev().collect::<Vec<_>>();
                let reversed_weights=gkr::eq_weights(&reversed_prefix);
                let (wrong_a,mut wrong_b)=direct_u_prefix_coefficients(width,&reversed_prefix,&reversed_weights,1,&input,
                    |owner,row|weight(owner,row),|sink|{for term in &terms{sink(term.clone())?;}Ok(())}).unwrap();
                wrong_b[0]+=global_left_b*reversed_weights[0];
                assert_ne!((wrong_a,wrong_b),(actual_a.clone(),actual_b.clone()),
                    "reversing challenge-coordinate order must be detected");
            }
            if prefix_len>0{
                let folded_width=width>>prefix_len;let wrong_mask=(1usize<<prefix_len)-2;
                let mut wrong_a=vec![Fr::zero();folded_width];let mut wrong_b=vec![Fr::zero();folded_width];
                for term in &terms{let gate=&term.gate;if gate.left==width{continue;}
                    let right=if gate.right==width{Fr::zero()}else{input[gate.right]};
                    let scale=prefix_weights[gate.left&wrong_mask]*weight(1,term.row);
                    let bucket=gate.left>>prefix_len;
                    wrong_a[bucket]+=scale*(gate.c1+gate.c3*right);
                    wrong_b[bucket]+=scale*(gate.c0+gate.c2*right);
                }
                wrong_b[0]+=global_left_b*prefix_weights[0];
                assert_ne!((wrong_a,wrong_b),(actual_a.clone(),actual_b.clone()),"dropping the low mask bit must be detected");
            }
            if prefix_len<3{
                let folded_width=width>>prefix_len;let mut wrong_a=vec![Fr::zero();folded_width];let mut wrong_b=vec![Fr::zero();folded_width];
                for term in &terms{let gate=&term.gate;if gate.left==width{continue;}
                    let right=if gate.right==width{Fr::zero()}else{input[gate.right]};
                    let scale=prefix_weights[gate.left&((1usize<<prefix_len)-1)]*weight(1,term.row);
                    let bucket=(gate.left>>prefix_len)^1;
                    wrong_a[bucket]+=scale*(gate.c1+gate.c3*right);
                    wrong_b[bucket]+=scale*(gate.c0+gate.c2*right);
                }
                wrong_b[0]+=global_left_b*prefix_weights[0];
                assert_ne!((wrong_a,wrong_b),(actual_a.clone(),actual_b.clone()),"shifting to the wrong bucket must be detected");
            }
        }
        assert_eq!(direct_u_prefix_coefficients(6,&[],&[Fr::one()],0,&input[..6],|_,_|Fr::one(),|_|Ok(())).unwrap_err(),
            "direct U prefix geometry is invalid");
        assert_eq!(direct_u_prefix_coefficients(width,&[],&[Fr::one()],0,&input[..width-1],|_,_|Fr::one(),|_|Ok(())).unwrap_err(),
            "direct U prefix geometry is invalid");
        assert_eq!(direct_u_prefix_coefficients(width,&[Fr::one();4],&[Fr::one();16],0,&input,|_,_|Fr::one(),|_|Ok(())).unwrap_err(),
            "direct U prefix geometry is invalid");
        assert_eq!(direct_u_prefix_coefficients(width,&[Fr::one()],&[Fr::one()],0,&input,|_,_|Fr::one(),|_|Ok(())).unwrap_err(),
            "direct U prefix geometry is invalid");
        let bad_left=Term{row:0,gate:Gate{left:width+1,right:0,c0:Fr::zero(),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()}};
        assert_eq!(direct_u_prefix_coefficients(width,&[],&[Fr::one()],0,&input,|_,_|Fr::one(),
            |sink|sink(bad_left.clone())).unwrap_err(),"direct U left wire outside width");
        let bad_right=Term{row:0,gate:Gate{left:0,right:width+1,c0:Fr::zero(),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()}};
        assert_eq!(direct_u_prefix_coefficients(width,&[],&[Fr::one()],0,&input,|_,_|Fr::one(),
            |sink|sink(bad_right.clone())).unwrap_err(),"active direct U right anchor");
        let active_double_anchor=Term{row:0,gate:Gate{left:width,right:width,c0:Fr::zero(),c1:Fr::zero(),c2:Fr::one(),c3:Fr::zero()}};
        assert_eq!(direct_u_prefix_coefficients(width,&[],&[Fr::one()],0,&input,|_,_|Fr::one(),
            |sink|sink(active_double_anchor.clone())).unwrap_err(),"active direct U right anchor");
        let active_left_anchor=Term{row:0,gate:Gate{left:width,right:2,c0:Fr::zero(),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()}};
        assert_eq!(direct_u_prefix_coefficients(width,&[],&[Fr::one()],0,&input,|_,_|Fr::one(),
            |sink|sink(active_left_anchor.clone())).unwrap_err(),"active direct U left anchor");
    }

    #[test]
    fn direct_u_prefix_proofs_match_fallback_for_small_tensors(){
        const INPUT_BITS:usize=3;const COPY_BITS:usize=1;const BASE_ROW_BITS:usize=2;const FAMILY_BITS:usize=1;
        const WIDTH:usize=1<<INPUT_BITS;const COPIES:usize=1<<COPY_BITS;const ROW_COUNT:usize=1<<(BASE_ROW_BITS+COPY_BITS+FAMILY_BITS);
        let input_one=(0..WIDTH).map(|index|Fr::from((index as u64+2)*13)).collect::<Vec<_>>();
        let gate_for=|left:usize,right:usize,c1:Fr,c2:Fr,c3:Fr,left_value:Fr,right_value:Fr|{
            let c0=-(c1*left_value+c2*right_value+c3*left_value*right_value);
            Gate{left,right,c0,c1,c2,c3}
        };
        let terms=vec![
            Term{row:0,gate:gate_for(1,5,Fr::from(2u64),Fr::from(3u64),Fr::from(5u64),input_one[1],input_one[5])},
            Term{row:1,gate:gate_for(WIDTH,2,Fr::zero(),Fr::from(7u64),Fr::zero(),Fr::zero(),input_one[2])},
            Term{row:2,gate:gate_for(4,WIDTH,Fr::from(11u64),Fr::zero(),Fr::zero(),input_one[4],Fr::zero())},
            Term{row:3,gate:Gate{left:WIDTH,right:WIDTH,c0:Fr::zero(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}},
            Term{row:4,gate:gate_for(6,7,Fr::from(13u64),Fr::from(17u64),Fr::from(19u64),input_one[6],input_one[7])},
            Term{row:5,gate:gate_for(0,3,Fr::from(23u64),Fr::from(29u64),Fr::from(31u64),input_one[0],input_one[3])},
        ];
        let input=(0..COPIES).flat_map(|_|input_one.iter().copied()).collect::<Vec<_>>();
        let bind=|transcript:&mut Transcript|transcript.append_bytes(b"direct-u-prefix-test-statement",b"small multi-copy multi-family relation");
        let load=|copy:usize|Ok(input[copy*WIDTH..(copy+1)*WIDTH].to_vec());
        let emit=|_copy:usize,sink:&mut dyn FnMut(Term)->Result<(),String>|{for term in &terms{sink(term.clone())?;}Ok(())};
        let wiring=|r:&[Fr],u:&[Fr],v:&[Fr]|->Result<[Fr;4],String>{
            if r.len()!=BASE_ROW_BITS+COPY_BITS+FAMILY_BITS||u.len()!=INPUT_BITS+COPY_BITS||v.len()!=u.len(){
                return Err("small direct-prefix wiring point dimensions differ".into());
            }
            let mut out=[Fr::zero();4];
            for copy in 0..COPIES{for term in &terms{
                let family=term.row>>BASE_ROW_BITS;let local=term.row&((1usize<<BASE_ROW_BITS)-1);
                let row_weight=eq_weight_at(&r[..BASE_ROW_BITS],local)
                    *eq_weight_at(&r[BASE_ROW_BITS..BASE_ROW_BITS+COPY_BITS],copy)
                    *eq_weight_at(&r[BASE_ROW_BITS+COPY_BITS..],family);
                let left=if term.gate.left==WIDTH{0}else{copy*WIDTH+term.gate.left};
                let right=if term.gate.right==WIDTH{0}else{copy*WIDTH+term.gate.right};
                let scale=row_weight*eq_weight_at(u,left)*eq_weight_at(v,right);
                for (sum,coefficient) in out.iter_mut().zip([term.gate.c0,term.gate.c1,term.gate.c2,term.gate.c3]){*sum+=scale*coefficient;}
            }}
            Ok(out)
        };
        let mut fallback_transcript=Transcript::new(b"direct-u-prefix-proof-differential");
        let (fallback,fallback_claim)=prove_with_cache_budget_for_test(INPUT_BITS,COPY_BITS,BASE_ROW_BITS,FAMILY_BITS,&[2,2],Some(0),
            load,&mut fallback_transcript,bind,emit,wiring).unwrap();
        let mut direct_transcript=Transcript::new(b"direct-u-prefix-proof-differential");
        let (direct,direct_claim)=prove_with_direct_u_prefix_for_test(INPUT_BITS,COPY_BITS,BASE_ROW_BITS,FAMILY_BITS,&[2,2],Some(0),
            load,&mut direct_transcript,bind,emit,wiring).unwrap();
        assert_eq!(direct,fallback);
        assert_eq!(direct_claim,fallback_claim);
        assert_eq!(gkr::encode_proof(&direct).unwrap(),gkr::encode_proof(&fallback).unwrap());
        let compare_transcript=|left:&Transcript,right:&Transcript|{
            assert_eq!(left.challenges(),right.challenges());assert_eq!(left.raw_queries(),right.raw_queries());
            assert_eq!(left.bytes_absorbed(),right.bytes_absorbed());
            let mut left_next=left.clone();let mut right_next=right.clone();
            assert_eq!(left_next.challenge_scalar(b"direct-u-prefix-continuation"),right_next.challenge_scalar(b"direct-u-prefix-continuation"));
        };
        compare_transcript(&direct_transcript,&fallback_transcript);
        let mut verifier_transcript=Transcript::new(b"direct-u-prefix-proof-differential");
        let verified=gkr::verify_with_wiring(&[INPUT_BITS+COPY_BITS],ROW_COUNT,&direct,&mut verifier_transcript,bind,
            |_,r,u,v|wiring(r,u,v).map_err(|_|GkrError::InvalidWireIndex)).unwrap();
        assert_eq!(verified,direct_claim);compare_transcript(&verifier_transcript,&direct_transcript);
        assert_eq!(input.len(),WIDTH*COPIES);
        let mut bad=terms.clone();bad[3].gate.c0=Fr::one();
        let reached=std::cell::Cell::new(false);let mut invalid_transcript=Transcript::new(b"direct-u-prefix-proof-differential");
        let rejected=prove_with_direct_u_prefix_for_test(INPUT_BITS,COPY_BITS,BASE_ROW_BITS,FAMILY_BITS,&[2,2],Some(0),
            load,&mut invalid_transcript,|_|reached.set(true),
            |_copy,sink|{for term in &bad{sink(term.clone())?;}Ok(())},wiring);
        assert_eq!(rejected.unwrap_err(),GkrError::NonzeroOutput.to_string());
        assert!(!reached.get());assert_eq!(invalid_transcript.challenges(),0);
        for budget in [None,Some(1)]{
            let hook_reached=std::cell::Cell::new(false);let mut hook_transcript=Transcript::new(b"direct-u-prefix-proof-differential");
            let hook=prove_with_direct_u_prefix_for_test(INPUT_BITS,COPY_BITS,BASE_ROW_BITS,FAMILY_BITS,&[2,2],budget,
                load,&mut hook_transcript,|_|hook_reached.set(true),emit,wiring);
            assert_eq!(hook.unwrap_err(),"direct U prefix test hook requires a zero cache budget");
            assert!(!hook_reached.get());assert_eq!(hook_transcript.challenges(),0);
        }

        let one_terms=vec![
            Term{row:0,gate:gate_for(1,5,Fr::from(2u64),Fr::from(3u64),Fr::from(5u64),input_one[1],input_one[5])},
            Term{row:1,gate:gate_for(WIDTH,2,Fr::zero(),Fr::from(7u64),Fr::zero(),Fr::zero(),input_one[2])},
            Term{row:2,gate:gate_for(4,WIDTH,Fr::from(11u64),Fr::zero(),Fr::zero(),input_one[4],Fr::zero())},
            Term{row:3,gate:Gate{left:WIDTH,right:WIDTH,c0:Fr::zero(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}},
        ];
        let one_load=|copy:usize|{let mut owner=input_one.clone();if copy==1{owner[7]+=Fr::from(101u64);}Ok(owner)};
        let one_emit=|_copy:usize,sink:&mut dyn FnMut(Term)->Result<(),String>|{for term in &one_terms{sink(term.clone())?;}Ok(())};
        let one_wiring=|r:&[Fr],u:&[Fr],v:&[Fr]|->Result<[Fr;4],String>{
            if r.len()!=BASE_ROW_BITS+COPY_BITS||u.len()!=INPUT_BITS+COPY_BITS||v.len()!=u.len(){
                return Err("one-family direct-prefix wiring point dimensions differ".into());
            }
            let mut out=[Fr::zero();4];
            for copy in 0..COPIES{for term in &one_terms{
                let row_weight=eq_weight_at(&r[..BASE_ROW_BITS],term.row)
                    *eq_weight_at(&r[BASE_ROW_BITS..],copy);
                let left=if term.gate.left==WIDTH{0}else{copy*WIDTH+term.gate.left};
                let right=if term.gate.right==WIDTH{0}else{copy*WIDTH+term.gate.right};
                let scale=row_weight*eq_weight_at(u,left)*eq_weight_at(v,right);
                for (sum,coefficient) in out.iter_mut().zip([term.gate.c0,term.gate.c1,term.gate.c2,term.gate.c3]){*sum+=scale*coefficient;}
            }}
            Ok(out)
        };
        let mut one_fallback_transcript=Transcript::new(b"direct-u-prefix-one-family");
        let (one_fallback,one_fallback_claim)=prove_with_cache_budget_for_test(INPUT_BITS,COPY_BITS,BASE_ROW_BITS,0,&[2],Some(0),
            one_load,&mut one_fallback_transcript,bind,one_emit,one_wiring).unwrap();
        let mut one_direct_transcript=Transcript::new(b"direct-u-prefix-one-family");
        let (one_direct,one_direct_claim)=prove_with_direct_u_prefix_for_test(INPUT_BITS,COPY_BITS,BASE_ROW_BITS,0,&[2],Some(0),
            one_load,&mut one_direct_transcript,bind,one_emit,one_wiring).unwrap();
        assert_eq!(gkr::encode_proof(&one_direct).unwrap(),gkr::encode_proof(&one_fallback).unwrap());
        assert_eq!(one_direct_claim,one_fallback_claim);compare_transcript(&one_direct_transcript,&one_fallback_transcript);
        let mut one_verifier_transcript=Transcript::new(b"direct-u-prefix-one-family");
        let one_verified=gkr::verify_with_wiring(&[INPUT_BITS+COPY_BITS],1<<(BASE_ROW_BITS+COPY_BITS),&one_direct,
            &mut one_verifier_transcript,bind,|_,r,u,v|one_wiring(r,u,v).map_err(|_|GkrError::InvalidWireIndex)).unwrap();
        assert_eq!(one_verified,one_direct_claim);compare_transcript(&one_verifier_transcript,&one_direct_transcript);
    }

    mod grouped_v{
        use super::*;
        use ark_ff::Field;

        const INPUT_BITS:usize=3;
        const COPY_BITS:usize=2;
        const BASE_ROW_BITS:usize=2;
        const WIDTH:usize=1<<INPUT_BITS;
        const COPIES:usize=1<<COPY_BITS;
        const ROW_COUNT:usize=1<<(BASE_ROW_BITS+COPY_BITS);
        const GROUP_BY_COPY:[usize;COPIES]=[0,0,1,0];

        fn fixture()->(Vec<Vec<Fr>>,[Vec<Term>;2]){
            let mut inputs=(0..COPIES).map(|copy|{
                (0..WIDTH).map(|wire|Fr::from((wire as u64+3)*13+copy as u64*7)).collect::<Vec<_>>()
            }).collect::<Vec<_>>();
            for owner in [0usize,1,3]{
                inputs[owner][1]=Fr::from(53u64);inputs[owner][2]=Fr::from(71u64);
                inputs[owner][5]=Fr::from(97u64);inputs[owner][6]=Fr::from(109u64);
            }
            inputs[2][3]=Fr::from(131u64);inputs[2][7]=Fr::from(149u64);
            let make_gate=|left:usize,right:usize,c1:Fr,c2:Fr,c3:Fr,input:&[Fr]|{
                let c0=-(c1*input[left]+c2*input[right]+c3*input[left]*input[right]);
                Gate{left,right,c0,c1,c2,c3}
            };
            let full=vec![
                Term{row:0,gate:make_gate(1,5,Fr::from(3u64),Fr::from(5u64),Fr::from(7u64),&inputs[0])},
                Term{row:1,gate:make_gate(2,6,Fr::from(11u64),Fr::from(13u64),Fr::from(17u64),&inputs[0])},
            ];
            let short=vec![Term{row:0,gate:make_gate(3,7,Fr::from(19u64),Fr::from(23u64),Fr::from(29u64),&inputs[2])}];
            for owner in [1usize,3] {
                for term in &full {
                    let g=&term.gate;
                    inputs[owner][g.left]+=Fr::from(owner as u64);
                    let left=inputs[owner][g.left];
                    inputs[owner][g.right]=-(g.c0+g.c1*left)*(g.c2+g.c3*left).inverse().unwrap();
                }
            }
            (inputs,[full,short])
        }

        fn emit_for<'a>(terms:&'a [Vec<Term>;2],group_by_copy:&'a [usize;COPIES],
            changed_owner:Option<usize>,inactive_sentinel:bool)->impl FnMut(usize,&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String>+'a{
            move |copy,sink|{
                for (index,original) in terms[group_by_copy[copy]].iter().enumerate(){
                    let mut term=original.clone();
                    if changed_owner==Some(copy)&&index==0{term.gate.c0+=Fr::one();}
                    if inactive_sentinel&&copy==0&&index==0{
                        term.gate.left=WIDTH;term.gate.c0=Fr::zero();term.gate.c1=Fr::zero();
                        term.gate.c2=Fr::zero();term.gate.c3=Fr::zero();
                    }
                    sink(term)?;
                }
                Ok(())
            }
        }

        fn reference_wiring(terms:&[Vec<Term>;2],group_by_copy:&[usize;COPIES],r:&[Fr],u:&[Fr],v:&[Fr])
            ->Result<[Fr;4],String>{
            if r.len()!=BASE_ROW_BITS+COPY_BITS||u.len()!=INPUT_BITS+COPY_BITS||v.len()!=u.len(){
                return Err("grouped V wiring dimensions differ".into());
            }
            let mut out=[Fr::zero();4];
            for copy in 0..COPIES{
                let row_copy=eq_weight_at(&r[BASE_ROW_BITS..],copy);
                let u_copy=eq_weight_at(&u[INPUT_BITS..],copy);
                let v_copy=eq_weight_at(&v[INPUT_BITS..],copy);
                for term in &terms[group_by_copy[copy]]{
                    let gate=&term.gate;
                    let scale=eq_weight_at(&r[..BASE_ROW_BITS],term.row)*row_copy
                        *eq_weight_at(&u[..INPUT_BITS],gate.left)*u_copy
                        *eq_weight_at(&v[..INPUT_BITS],gate.right)*v_copy;
                    for (sum,coefficient) in out.iter_mut().zip([gate.c0,gate.c1,gate.c2,gate.c3]){
                        *sum+=scale*coefficient;
                    }
                }
            }
            Ok(out)
        }

        fn compare_transcripts(left:&Transcript,right:&Transcript){
            assert_eq!(left.challenges(),right.challenges());
            assert_eq!(left.raw_queries(),right.raw_queries());
            assert_eq!(left.bytes_absorbed(),right.bytes_absorbed());
            let mut left_next=left.clone();let mut right_next=right.clone();
            assert_eq!(left_next.challenge_scalar(b"grouped-v-continuation"),
                right_next.challenge_scalar(b"grouped-v-continuation"));
        }

        #[test]
        fn grouped_v_matches_fallback_for_mixed_topologies(){
            let (inputs,terms)=fixture();
            let admission=GroupedVAdmission::try_new(COPY_BITS,&GROUP_BY_COPY,&[2,1]).unwrap();
            let load=|copy:usize|Ok(inputs[copy].clone());
            let bind=|transcript:&mut Transcript|transcript.append_bytes(b"grouped-v-test-statement",b"mixed full/short projected relation");
            let wiring=|r:&[Fr],u:&[Fr],v:&[Fr]|reference_wiring(&terms,&GROUP_BY_COPY,r,u,v);

            let mut fallback_transcript=Transcript::new(b"role1-grouped-v-differential");
            let (fallback,fallback_claim)=prove_with_cache_budget_for_test(INPUT_BITS,COPY_BITS,BASE_ROW_BITS,0,&[BASE_ROW_BITS],Some(0),
                load,&mut fallback_transcript,bind,emit_for(&terms,&GROUP_BY_COPY,None,false),wiring).unwrap();
            let mut grouped_transcript=Transcript::new(b"role1-grouped-v-differential");
            let (grouped,grouped_claim,stats)=prove_with_direct_u_grouped_v_for_test(
                INPUT_BITS,COPY_BITS,BASE_ROW_BITS,0,&[BASE_ROW_BITS],Some(0),&admission,
                load,&mut grouped_transcript,bind,emit_for(&terms,&GROUP_BY_COPY,None,false),wiring).unwrap();
            assert_eq!(grouped,fallback);
            assert_eq!(grouped_claim,fallback_claim);
            assert_eq!(gkr::encode_proof(&grouped).unwrap(),gkr::encode_proof(&fallback).unwrap());
            compare_transcripts(&grouped_transcript,&fallback_transcript);
            let mut verifier_transcript=Transcript::new(b"role1-grouped-v-differential");
            let verified=gkr::verify_with_wiring(&[INPUT_BITS+COPY_BITS],ROW_COUNT,&grouped,&mut verifier_transcript,bind,
                |_,r,u,v|wiring(r,u,v).map_err(|_|GkrError::InvalidWireIndex)).unwrap();
            assert_eq!(verified,grouped_claim);compare_transcripts(&verifier_transcript,&grouped_transcript);
            let mut invalid=grouped.clone();invalid.layers[0].rounds[0][0]+=Fr::one();
            let mut invalid_t=Transcript::new(b"role1-grouped-v-differential");
            assert!(gkr::verify_with_wiring(&[INPUT_BITS+COPY_BITS],ROW_COUNT,&invalid,&mut invalid_t,bind,
                |_,r,u,v|wiring(r,u,v).map_err(|_|GkrError::InvalidWireIndex)).is_err());
            assert_eq!(stats.group_count,2);assert_eq!(stats.group_owner_counts.as_slice(),&[3,1]);
            assert_eq!(stats.group_term_counts.as_slice(),&[2,1]);assert_eq!(stats.baseline_term_callbacks,7);
            assert_eq!(stats.template_term_count,3);assert_eq!(stats.bank_term_callbacks,3);
            assert_eq!(stats.handoff_term_callbacks,0);assert_eq!(stats.local_rounds,INPUT_BITS);
            assert_eq!(stats.owner_handoff_count,COPIES);
            assert_eq!(stats.group_weight_sums.len(),2);
            assert!(stats.group_weight_sums.iter().all(|sum|*sum!=Fr::one()),
                "mixed topology weight sums should not collapse to one");
            assert!(stats.group_d_local_contributions.iter().any(|value|!value.is_zero()),
                "the fixture must exercise a nonzero D contribution");
            struct ResetMutant;
            impl Drop for ResetMutant {fn drop(&mut self){TEST_GROUPED_V_MUTANT.with(|mode|mode.set(0));}}
            for mode in [1u8,2] {
                let _reset=ResetMutant;TEST_GROUPED_V_MUTANT.with(|current|current.set(mode));
                let reached=std::cell::Cell::new(false);let mut bad_t=Transcript::new(b"role1-grouped-v-differential");
                let bad=prove_with_direct_u_grouped_v_for_test(INPUT_BITS,COPY_BITS,BASE_ROW_BITS,0,&[BASE_ROW_BITS],
                    Some(0),&admission,load,&mut bad_t,|t|{reached.set(true);bind(t)},
                    emit_for(&terms,&GROUP_BY_COPY,None,false),wiring);
                assert!(reached.get());assert!(bad_t.challenges()>0);
                assert_eq!(bad.unwrap_err(),GkrError::SumcheckIdentity.to_string(),"post-bind arithmetic mutant {mode}");
            }
        }

        #[test]
        fn grouped_v_admission_and_arithmetic_mutants_are_isolated(){
            let (inputs,terms)=fixture();
            for invalid_map in [&[0usize,1,1,0][..],&[0usize,0,1,2][..]]{
                let result=GroupedVAdmission::try_new(COPY_BITS,invalid_map,&[2,1]);
                if invalid_map[3]==2{assert!(result.is_err());}else{assert!(result.is_ok());}
            }
            if usize::BITS>32{
                assert!(GroupedVAdmission::try_new(1usize<<32,&[0],&[1]).is_err(),
                    "copy-bit narrowing must not wrap a huge dimension to zero");
            }
            let admission=GroupedVAdmission::try_new(COPY_BITS,&GROUP_BY_COPY,&[2,1]).unwrap();
            fn assert_rejected<F>(admission:&GroupedVAdmission,inputs:&[Vec<Fr>],terms:&[Vec<Term>;2],emit:F)
            where F:FnMut(usize,&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String>{
                let group_by_copy=GROUP_BY_COPY;
                let reached=std::cell::Cell::new(false);let mut transcript=Transcript::new(b"role1-grouped-v-negative");
                let result=prove_with_direct_u_grouped_v_for_test(INPUT_BITS,COPY_BITS,BASE_ROW_BITS,0,&[BASE_ROW_BITS],Some(0),
                    admission,|copy|Ok(inputs[copy].clone()),&mut transcript,
                    |t|{reached.set(true);t.append_bytes(b"grouped-v-negative",b"statement")},emit,
                    |r,u,v|reference_wiring(terms,&group_by_copy,r,u,v));
                assert!(result.is_err());assert!(!reached.get());assert_eq!(transcript.challenges(),0);
            }
            let wrong_group=[0usize,1,1,0];
            let mut wrong_map_emit=emit_for(&terms,&wrong_group,None,false);
            assert_rejected(&admission,&inputs,&terms,move |copy,sink|wrong_map_emit(copy,sink));
            let mut changed_emit=emit_for(&terms,&GROUP_BY_COPY,Some(1),false);
            assert_rejected(&admission,&inputs,&terms,move |copy,sink|changed_emit(copy,sink));
            let mut sentinel_emit=emit_for(&terms,&GROUP_BY_COPY,None,true);
            assert_rejected(&admission,&inputs,&terms,move |copy,sink|sentinel_emit(copy,sink));
            for side in [0,1] {for inactive in [false,true] {for offset in [0usize,1] {
                assert_rejected(&admission,&inputs,&terms,|copy,sink|{
                    for original in &terms[GROUP_BY_COPY[copy]] {
                        let mut term=original.clone();
                        if copy==0 {
                            if side==0{term.gate.left=WIDTH+offset;}else{term.gate.right=WIDTH+offset;}
                            if inactive{term.gate.c0=Fr::zero();term.gate.c1=Fr::zero();term.gate.c2=Fr::zero();term.gate.c3=Fr::zero();}
                        }
                        sink(term)?;
                    }Ok(())
                });
            }}}
            for extra in [false,true] {
                assert_rejected(&admission,&inputs,&terms,|copy,sink|{
                    let owner_terms=&terms[GROUP_BY_COPY[copy]];
                    let count=if copy==1 && !extra{owner_terms.len()-1}else{owner_terms.len()};
                    for term in &owner_terms[..count]{sink(term.clone())?;}
                    if copy==1 && extra{sink(owner_terms.last().unwrap().clone())?;}Ok(())
                });
            }
            assert_rejected(&admission,&inputs,&terms,|copy,sink|{
                for original in &terms[GROUP_BY_COPY[copy]]{
                    let mut term=original.clone();if copy==0{term.row=1<<BASE_ROW_BITS;}
                    sink(term)?;
                }Ok(())
            });

            let c=[Fr::from(3u64),Fr::from(11u64),Fr::from(17u64),Fr::from(23u64)];
            let d=[Fr::from(5u64),Fr::from(7u64),Fr::from(13u64),Fr::from(19u64)];
            let x=[Fr::from(29u64),Fr::from(31u64),Fr::from(37u64),Fr::from(41u64)];
            let scale=Fr::from(43u64);
            let correct=scaled_common_quadratic_message(&c,&d,&x,scale);
            let missing_group_scale=scaled_common_quadratic_message(&c,&d,&x,Fr::one());
            assert_ne!(correct,missing_group_scale,"omitting the group D scale must be observable");
            let owner_inputs=(0..COPIES).map(|owner|{
                (0..4).map(|wire|Fr::from((owner as u64+2)*37+(wire as u64+1)*11)).collect::<Vec<_>>()
            }).collect::<Vec<_>>();
            let owner_weights=[Fr::from(2u64),Fr::from(3u64),Fr::from(5u64),Fr::from(7u64)];
            let aggregate=|weights:&[Fr;COPIES]|{
                let mut total=Fr::zero();let mut combined=vec![Fr::zero();4];
                for owner in 0..COPIES{
                    total+=weights[owner];
                    for (sum,value) in combined.iter_mut().zip(&owner_inputs[owner]){*sum+=weights[owner] * *value;}
                }
                scaled_common_quadratic_message(&c,&d,&combined,total)
            };
            let correct_owner_weights=aggregate(&owner_weights);
            let mut swapped_owner_weights=owner_weights;swapped_owner_weights.swap(0,1);
            assert_ne!(correct_owner_weights,aggregate(&swapped_owner_weights),
                "swapping two owner-coordinate weights must be observable");
            // Valid equality weights with a cancelling two-owner group.
            let row_point=[Fr::from(2u64),Fr::from(3u64)];
            let u_point=[Fr::from(3u64).inverse().unwrap(),Fr::from(5u64)];
            let lambda=[0usize,1].map(|owner|eq_weight_at(&row_point,owner)*eq_weight_at(&u_point,owner));
            assert_eq!(lambda[0]+lambda[1],Fr::zero());assert!(!lambda[0].is_zero());
            let mut cc=c.to_vec();let mut dd=d.to_vec();let mut xs=[owner_inputs[0].clone(),owner_inputs[1].clone()];
            let mut aggregate_x=(0..4).map(|i|lambda[0]*xs[0][i]+lambda[1]*xs[1][i]).collect::<Vec<_>>();
            for challenge in [Fr::from(7u64),Fr::from(11u64)] {
                let mut dense=[Fr::zero();3];
                for owner in 0..2 {for (out,value) in dense.iter_mut().zip(gkr::quadratic_message(&cc,&dd,&xs[owner])){
                    *out+=lambda[owner]*value;
                }}
                assert_eq!(scaled_common_quadratic_message(&cc,&dd,&aggregate_x,Fr::zero()),dense);
                gkr::fold(&mut cc,challenge);gkr::fold(&mut dd,challenge);gkr::fold(&mut aggregate_x,challenge);
                for x in &mut xs{gkr::fold(x,challenge);}
            }

            for budget in [None,Some(1)]{
                let reached=std::cell::Cell::new(false);let mut transcript=Transcript::new(b"role1-grouped-v-negative");
                let result=prove_with_direct_u_grouped_v_for_test(INPUT_BITS,COPY_BITS,BASE_ROW_BITS,0,&[BASE_ROW_BITS],budget,
                    &admission,|copy|Ok(inputs[copy].clone()),&mut transcript,|_|reached.set(true),
                    emit_for(&terms,&GROUP_BY_COPY,None,false),
                    |r,u,v|reference_wiring(&terms,&GROUP_BY_COPY,r,u,v));
                assert_eq!(result.unwrap_err(),"grouped V test hook requires a zero cache budget");
                assert!(!reached.get());assert_eq!(transcript.challenges(),0);
            }

            let huge=GroupedVAdmission::try_new(0,&[0usize],&[1]).unwrap();
            let reached=std::cell::Cell::new(false);let mut bad_t=Transcript::new(b"grouped-v-family-negative");
            let bad=prove_with_direct_u_grouped_v_for_test(INPUT_BITS,COPY_BITS,BASE_ROW_BITS,1,&[BASE_ROW_BITS],
                Some(0),&admission,|_|Err("family must stop before load".into()),&mut bad_t,|_|reached.set(true),
                |_,_|Ok(()),|_,_,_|Ok([Fr::zero();4]));
            assert_eq!(bad.unwrap_err(),"grouped V dimensions exceed the supported bound before allocation");
            assert!(!reached.get());assert_eq!(bad_t.challenges(),0);
            let reached=std::cell::Cell::new(false);let mut transcript=Transcript::new(b"role1-grouped-v-negative");
            let wrapped=prove_with_direct_u_grouped_v_for_test(usize::MAX,0,0,0,&[0],Some(0),&huge,
                |_|Err("invalid dimensions must stop before loading".into()),&mut transcript,
                |_|reached.set(true),|_,_|Ok(()),|_,_,_|Ok([Fr::zero();4]));
            assert_eq!(wrapped.unwrap_err(),"grouped V dimensions exceed the supported bound before allocation");
            assert!(!reached.get());assert_eq!(transcript.challenges(),0);
            let reached=std::cell::Cell::new(false);let mut transcript=Transcript::new(b"role1-grouped-v-negative");
            let over_cap=prove_with_direct_u_grouped_v_for_test(24,0,0,0,&[0],Some(0),&huge,
                |_|Err("over-cap admission must stop before reading an input".into()),&mut transcript,
                |_|reached.set(true),|_,_|Ok(()),|_,_,_|Ok([Fr::zero();4]));
            assert_eq!(over_cap.unwrap_err(),"grouped V checked capacity bound exceeds 512 MiB before transcript binding");
            assert!(!reached.get());assert_eq!(transcript.challenges(),0);
        }

        mod boolean_u_preweight{
            use super::*;

            #[test]
            fn capacity46_phase_plan_and_inventory(){
                let a=GroupedVAdmission::try_new(3,&[0;8],&[396561]).unwrap();
                let h=UCapacityPlan::new(20,3,19,&a,GroupedDimensionPolicy::Generic24).unwrap();
                let native=GroupedVAdmission::try_new(12,&(0..4096).map(|i|usize::from(i==3072)).collect::<Vec<_>>(),&[396561,388369]).unwrap();
                let n=UCapacityPlan::new(20,12,19,&native,GroupedDimensionPolicy::NativeRole1Exact{extra_capacity_bytes:72}).unwrap();
                assert_eq!(std::mem::size_of::<Term>(),152);assert_eq!(std::mem::size_of::<BooleanUPreweight>(),144);
                assert_eq!(UCapacityPlan::metadata().unwrap(),817);
                assert_eq!((h.small,h.u_max,h.v_max,h.component),(15586,337608858,330916273,337608858));
                assert_eq!(n.u_max,453168402);
                assert_eq!(n.v_max,491211105);
                assert_eq!(h.component,h.u_max.max(h.v_max));assert_eq!(n.component,n.u_max.max(n.v_max));
                assert!(n.component<=MAX_INCREMENTAL_CACHE_STATE_BYTES);
                // Pure native arithmetic only: neither constructor invokes a
                // loader, transcript, graph or executable historical hook.
                for p in [&h,&n]{for k in 0..=20{
                    assert_eq!(p.table(k).unwrap(),if k==0{0}else if k==1{128}else{128usize<<k});
                    let mut s=ULive::default();p.before(UPhase::Prefix,k,s).unwrap();
                    s.prefix=Some(k);p.before(UPhase::Bank,k,s).unwrap();s.bank=true;
                    p.before(UPhase::Table,k,s).unwrap();s.table=true;p.before(UPhase::Load,k,s).unwrap();
                    s.owner=true;p.before(UPhase::Apply,k,s).unwrap();
                    let cap=p.bound(UPhase::Apply,k).unwrap();let high=if k==20{3*p.owners}else{0};
                    p.actual(UPhase::Apply,k,cap,p.private,p.table(k).unwrap(),high).unwrap();
                    assert_eq!(p.actual(UPhase::Apply,k,cap+1,p.private,p.table(k).unwrap(),high).unwrap_err(),"capacity46 actual capacity exceeds reservation");
                    let wrong_private=if p.private==0{1}else{p.private-1};
                    assert_eq!(p.actual(UPhase::Apply,k,cap,wrong_private,p.table(k).unwrap(),high).unwrap_err(),"capacity46 private reservation drift");
                    if k!=0{assert_eq!(p.actual(UPhase::Apply,k,cap,p.private,0,high).unwrap_err(),"capacity46 table capacity drift");}
                    if k==20{assert_eq!(p.actual(UPhase::Apply,k,cap,p.private,p.table(k).unwrap(),0).unwrap_err(),"capacity46 high capacity drift");}
                    // Every state predicate is isolated from the same accepted
                    // Prefix golden; no earlier predicate can mask this field.
                    p.before(UPhase::Prefix,k,ULive::default()).unwrap();
                    for field in 0..5{let mut wrong=ULive::default();
                        match field{0=>wrong.prefix=Some(k),1=>wrong.bank=true,2=>wrong.table=true,
                            3=>wrong.owner=true,_=>wrong.coeff=true}
                        assert_eq!(p.before(UPhase::Prefix,k,wrong).unwrap_err(),"capacity46 forbidden live overlap");
                    }
                    p.before(UPhase::Apply,k,s).unwrap();let mut wrong=s;wrong.coeff=true;
                    assert_eq!(p.before(UPhase::Apply,k,wrong).unwrap_err(),"capacity46 forbidden live overlap");
                }}
                let mut exact=h.clone();exact.u_max=h.bound(UPhase::Apply,20).unwrap();exact.component=exact.u_max;
                let live=ULive{prefix:Some(20),bank:true,table:true,owner:true,coeff:false};
                exact.before(UPhase::Apply,20,live).unwrap();
                exact.component-=1;
                assert_eq!(exact.before(UPhase::Apply,20,live).unwrap_err(),"capacity46 phase exceeds reservation");
                exact.component+=2;exact.before(UPhase::Apply,20,live).unwrap();
                assert_eq!(u_mul(usize::MAX,2).unwrap_err(),"capacity46 arithmetic overflow");
                assert_eq!(u_sum(&[usize::MAX,1]).unwrap_err(),"capacity46 arithmetic overflow");
                assert_eq!(UCapacityPlan::new(usize::MAX,3,19,&a,GroupedDimensionPolicy::Generic24).err().as_deref(),Some("capacity46 dimensions"));
                let mut bad=a.clone();bad.expected_terms_per_group[0]=0;
                assert_eq!(UCapacityPlan::new(20,3,19,&bad,GroupedDimensionPolicy::Generic24).err().as_deref(),Some("capacity46 group census"));
                assert_eq!(UCapacityPlan::new(20,12,19,&native,GroupedDimensionPolicy::NativeRole1Exact{extra_capacity_bytes:usize::MAX}).err().as_deref(),Some("capacity46 arithmetic overflow"));
                let tiny=GroupedVAdmission::try_new(2,&[0,0,1,0],&[2,1]).unwrap();
                let t=UCapacityPlan::new(10,2,2,&tiny,GroupedDimensionPolicy::Generic24).unwrap();
                assert!(t.u_max<t.v_max);assert_eq!(t.component,t.v_max);
                let templates=(0..2).map(|_|None).collect::<Vec<Option<Vec<Term>>>>();
                let mut counts=Vec::with_capacity(4);
                let gs=GroupedVStats{group_owner_counts:vec![0;2],group_term_counts:vec![2,1],..Default::default()};
                t.baseline_actual(&templates,&counts,&gs).unwrap();counts.resize(4,0);counts.reserve_exact(1);
                assert_eq!(t.baseline_actual(&templates,&counts,&gs).unwrap_err(),"capacity46 baseline capacity drift");
                // Golden High/PostHigh use the actual inventory function used
                // by the producer. Change a physical Vec capacity, not the
                // global budget, to falsify each reached inventory guard.
                {
                    let (_,terms)=boolean_fixture();let a=GroupedVAdmission::try_new(COPY_BITS,&GROUP_BY_COPY,&[2,1]).unwrap();
                    let p=UCapacityPlan::new(INPUT_BITS,COPY_BITS,BASE_ROW_BITS,&a,GroupedDimensionPolicy::Generic24).unwrap();
                    let templates=vec![Some(terms[0].clone()),Some(terms[1].clone())];
                    let r=vec![Fr::from(3u64);BASE_ROW_BITS+COPY_BITS];
                    let row=TensorRowWeightLookup::new(&r,COPY_BITS,BASE_ROW_BITS,&[BASE_ROW_BITS]);
                    let factor=OneFamilyRowFactor::try_new(&r,COPY_BITS,BASE_ROW_BITS,0,&[BASE_ROW_BITS],row.local_table(BASE_ROW_BITS)).unwrap();
                    let gs=GroupedVStats{group_owner_counts:vec![3,1],group_term_counts:vec![2,1],..Default::default()};
                    let mut rounds=Vec::with_capacity(2*(INPUT_BITS+COPY_BITS));
                    for _ in 0..INPUT_BITS{rounds.push(vec![Fr::zero();3]);}
                    let u_local=vec![Fr::from(5u64);INPUT_BITS];let u_high=vec![Fr::from(7u64);COPY_BITS];
                    let mut u=u_local.clone();u.extend(u_high);
                    let local=boolean_u_eq_weights(&u_local).unwrap();let copy=gkr::eq_weights(&u[INPUT_BITS..]);
                    p.high_actual(&rounds,&[&r,&u_local,&u]).unwrap();p.handoff_weights_actual(&local,&copy).unwrap();
                    let observed=|phase:UPhase,high_cap,extra,point_cap,rounds:&Vec<Vec<Fr>>|{
                        let bytes=boolean_u_capacity_bytes(&templates,&a,&row,&factor,&gs,COPIES,rounds,
                            point_cap,local.capacity(),0,0,0,high_cap,extra,WIDTH).unwrap();
                        let bytes=u_sum(&[bytes,UCapacityPlan::metadata().unwrap(),subset4_metadata_bytes().unwrap()]).unwrap();
                        p.actual(phase,INPUT_BITS,bytes,0,0,0)
                    };
                    let high_x=vec![Fr::zero();COPIES];
                    observed(UPhase::High,3*high_x.capacity(),COPIES+5*COPY_BITS,r.capacity()+u_local.capacity(),&rounds).unwrap();
                    observed(UPhase::PostHigh,copy.capacity(),0,r.capacity()+u_local.capacity()+u.capacity(),&rounds).unwrap();
                    let over=p.bound(UPhase::High,INPUT_BITS).unwrap()/32+1;
                    let mut large_high=Vec::with_capacity(over);large_high.resize(COPIES,Fr::zero());
                    assert_eq!(observed(UPhase::High,2*COPIES+large_high.capacity(),COPIES+5*COPY_BITS,
                        r.capacity()+u_local.capacity(),&rounds).unwrap_err(),"capacity46 actual capacity exceeds reservation");
                    // Clone and extend are checked separately at their actual
                    // call boundaries; both reject the returned excess before use.
                    for extended in [false,true]{let mut changed=u_local.clone();if extended{changed.extend([Fr::one();COPY_BITS]);}
                        changed.reserve_exact(2*(p.bits+p.copies+1)+1);
                        assert_eq!(p.high_actual(&rounds,&[&r,&u_local,&changed]).unwrap_err(),"capacity46 high round or point capacity drift");}
                    let mut changed=gkr::eq_weights(&u[INPUT_BITS..]);changed.reserve_exact(COPIES+1);
                    assert_eq!(p.handoff_weights_actual(&local,&changed).unwrap_err(),"capacity46 handoff weight capacity drift");
                    let mut changed=u.clone();changed.reserve_exact(over);
                    assert_eq!(observed(UPhase::PostHigh,copy.capacity(),0,r.capacity()+u_local.capacity()+changed.capacity(),&rounds).unwrap_err(),
                        "capacity46 actual capacity exceeds reservation");
                    rounds[0].reserve_exact(1);
                    assert_eq!(p.high_actual(&rounds,&[&r,&u]).unwrap_err(),"capacity46 high round or point capacity drift");
                    let huge_message=Vec::<Fr>::with_capacity(over);
                    rounds[0]=huge_message;
                    assert_eq!(observed(UPhase::PostHigh,copy.capacity(),0,r.capacity()+u_local.capacity()+u.capacity(),&rounds).unwrap_err(),
                        "capacity46 actual capacity exceeds reservation");
                }
                let mut rounds=Vec::with_capacity(2*(h.bits+h.copies));rounds.push(vec![Fr::zero();3]);
                h.high_actual(&rounds,&[]).unwrap();rounds[0].reserve_exact(1);
                assert_eq!(h.high_actual(&rounds,&[]).unwrap_err(),"capacity46 high round or point capacity drift");
                let r=(0..22).map(|i|Fr::from((i+2) as u64)).collect::<Vec<_>>();
                let mut row=TensorRowWeightLookup::new(&r,3,19,&[19]);
                let factor=OneFamilyRowFactor::try_new(&r,3,19,0,&[19],row.local_table(19)).unwrap();
                h.lookup_actual(&row,Some(&factor)).unwrap();
                let owned=OneFamilyRowFactor::try_new(&r,3,19,0,&[19],None).unwrap();
                assert_eq!(h.lookup_actual(&row,Some(&owned)).unwrap_err(),"capacity46 row factor capacity or ownership");
                drop(owned);drop(factor);row.fallback=Some(EqWeightLookup::new(&[]));
                assert_eq!(h.lookup_actual(&row,None).unwrap_err(),"capacity46 row lookup capacity or shape");
            }

            fn boolean_fixture()->(Vec<Vec<Fr>>,[Vec<Term>;2]){
                let mut inputs=(0..COPIES).map(|copy|(0..WIDTH)
                    .map(|wire|Fr::from(((wire+copy)&1) as u64)).collect::<Vec<_>>()).collect::<Vec<_>>();
                for owner in [0usize,1,3]{
                    inputs[owner][1]=Fr::from((owner&1) as u64);inputs[owner][5]=inputs[owner][1];
                    inputs[owner][2]=Fr::from(usize::from(owner!=0) as u64);
                    inputs[owner][6]=Fr::one()-inputs[owner][2];
                }
                inputs[2][3]=Fr::one();inputs[2][7]=Fr::one();
                let full=vec![
                    Term{row:0,gate:Gate{left:1,right:5,c0:Fr::zero(),c1:Fr::from(2u64),c2:Fr::from(3u64),c3:-Fr::from(5u64)}},
                    Term{row:1,gate:Gate{left:2,right:6,c0:-Fr::from(3u64),c1:Fr::from(3u64),c2:Fr::from(3u64),c3:Fr::from(7u64)}},
                ];
                let short=vec![Term{row:0,gate:Gate{left:3,right:7,c0:Fr::zero(),c1:Fr::from(11u64),c2:Fr::from(13u64),c3:-Fr::from(24u64)}}];
                for owner in 0..COPIES{for term in [&full,&short][GROUP_BY_COPY[owner]]{assert!(term.gate.evaluate(&inputs[owner]).is_zero());}}
                (inputs,[full,short])
            }

            #[test]
            fn subset4_folds_and_proofs_match_legacy(){
                // All masks, every prefix, asymmetric inputs and challenges.
                for mask in 0usize..16{for challenges in [[Fr::from(7u64),Fr::from(11u64),Fr::from(13u64),Fr::from(17u64)],
                    [Fr::zero(),Fr::one(),Fr::from(3u64),Fr::from(5u64)]]{
                    let input=(0..16).map(|i|Fr::from(((mask>>(i%4))&1) as u64)).collect::<Vec<_>>();
                    for k in 0..=4{let mut s=BooleanSubset4Stats{extra_reserved_bytes:subset4_extra_bound(4).unwrap(),..Default::default()};
                        let weights=boolean_u_eq_weights(&challenges[..k]).unwrap();
                        let table=BooleanSubset4Table::build(&challenges[..k],&weights,16,&mut s).unwrap();
                        let mut actual=input.clone();let mut reference=input.clone();
                        table.apply(&mut actual,&mut s).unwrap();for c in &challenges[..k]{gkr::fold(&mut reference,*c);}
                        assert_eq!(actual,reference);assert_eq!(actual.capacity(),16);
                    }
                }}
                // Reached-mask private mutants: no claim of authenticated table guards.
                let prefix=[Fr::from(7u64),Fr::from(11u64)];let weights=boolean_u_eq_weights(&prefix).unwrap();
                let mut s=BooleanSubset4Stats{extra_reserved_bytes:subset4_extra_bound(2).unwrap(),..Default::default()};
                let good=BooleanSubset4Table::build(&prefix,&weights,4,&mut s).unwrap();
                let input=vec![Fr::one(),Fr::zero(),Fr::zero(),Fr::zero()];let mut reference=input.clone();
                good.apply(&mut reference,&mut s).unwrap();
                for fault in 0..3{let mut bad=BooleanSubset4Table::build(&prefix,&weights,4,&mut s).unwrap();
                    match fault{0=>bad.values.swap(1,8),1=>{let stale=boolean_u_eq_weights(&[Fr::from(3u64),Fr::from(5u64)]).unwrap();
                        bad=BooleanSubset4Table::build(&prefix,&stale,4,&mut s).unwrap();},_=>bad.values[1]+=Fr::one()}
                    let mut actual=input.clone();bad.apply(&mut actual,&mut s).unwrap();assert_ne!(actual,reference);}
                let mut bad=input.clone();bad[0]=Fr::from(2u64);
                assert_eq!(good.apply(&mut bad,&mut s).unwrap_err(),"subset4 input is not Boolean");
                let mut bad=vec![Fr::zero();3];assert_eq!(good.apply(&mut bad,&mut s).unwrap_err(),"subset4 input dimensions or capacity");
                let mut bad=Vec::with_capacity(5);bad.resize(4,Fr::zero());
                assert_eq!(good.apply(&mut bad,&mut s).unwrap_err(),"subset4 input dimensions or capacity");
                let mut zero=BooleanSubset4Stats::default();
                assert_eq!(BooleanSubset4Table::build(&prefix,&weights,4,&mut zero).err().as_deref(),Some("subset4 table exceeds reservation"));
                let exact=16*std::mem::size_of::<Fr>()+subset4_metadata_bytes().unwrap();
                let mut exact_stats=BooleanSubset4Stats{extra_reserved_bytes:exact,..Default::default()};
                assert!(BooleanSubset4Table::build(&prefix,&weights,4,&mut exact_stats).is_ok());
                let mut under=BooleanSubset4Stats{extra_reserved_bytes:exact-1,..Default::default()};
                assert_eq!(BooleanSubset4Table::build(&prefix,&weights,4,&mut under).err().as_deref(),Some("subset4 table exceeds reservation"));
                assert_eq!((under.builds,under.values_built,under.table_payload_peak_bytes),(0,0,0));
                assert_eq!(BooleanSubset4Table::build(&prefix,&weights[..3],4,&mut s).err().as_deref(),Some("subset4 prefix dimensions"));
                assert!(subset4_extra_bound(usize::BITS as usize).is_none());
                let closed=GroupedVAdmission::try_new(3,&[0;8],&[396561]).unwrap();
                let old=boolean_u_prebind_capacity_bound(20,3,19,&closed).unwrap();
                let extra=subset4_extra_bound(20).unwrap();assert_eq!(old,379535400);
                assert!(old+extra<MAX_INCREMENTAL_CACHE_STATE_BYTES);assert!(extra>134217728);
                // Actual preflight/mode guards reject before phase, loader and binder.
                for fault in 0..2{let activity=std::cell::Cell::new(false);let mut t=Transcript::new(b"subset4-cap");
                    let mut s=BooleanSubset4Stats::default();
                    let result=prove_boolean_u_grouped_with_fold_for_test(21,3,19,0,&[19],Some(0),&closed,
                        GroupedDimensionPolicy::Generic24,|_|{activity.set(true);Err("unexpected load".into())},&mut t,
                        |_|{activity.set(true);Ok(())},|_,_|Ok(()),|_,_,_|Ok([Fr::zero();4]),BooleanXFoldMode::Subset4,
                        if fault==0{Some(&mut s)}else{None});
                    assert_eq!(result.err().as_deref(),Some(if fault==0{"capacity46 component exceeds 512 MiB"}else{"subset4 mode/statistics mismatch"}));
                    assert!(!activity.get());assert_eq!(t.challenges(),0);}
                // Real terminal k20 table/capacity, no graph or retained owner history.
                {let p=(0..20).map(|i|Fr::from((i+2) as u64)).collect::<Vec<_>>();let weights=boolean_u_eq_weights(&p).unwrap();
                    let mut s=BooleanSubset4Stats{extra_reserved_bytes:extra,..Default::default()};
                    let table=BooleanSubset4Table::build(&p,&weights,1<<20,&mut s).unwrap();
                    let mut actual=(0..1usize<<20).map(|i|Fr::from(((i^(i>>3)^(i>>9))&1) as u64)).collect::<Vec<_>>();
                    let mut reference=actual.clone();table.apply(&mut actual,&mut s).unwrap();
                    for c in &p{gkr::fold(&mut reference,*c);}assert_eq!(actual,reference);assert_eq!(s.table_payload_peak_bytes,134217728);}
                let(inputs,terms)=boolean_fixture();let admission=GroupedVAdmission::try_new(COPY_BITS,&GROUP_BY_COPY,&[2,1]).unwrap();
                let bind=|t:&mut Transcript|t.append_bytes(b"subset4-statement",b"mixed owners");
                let wiring=|r:&[Fr],u:&[Fr],v:&[Fr]|reference_wiring(&terms,&GROUP_BY_COPY,r,u,v);
                let mut old_t=Transcript::new(b"subset4-proof");let(old,claim,_,_)=prove_with_boolean_u_grouped_v_for_test(
                    INPUT_BITS,COPY_BITS,BASE_ROW_BITS,0,&[BASE_ROW_BITS],Some(0),&admission,|o|Ok(inputs[o].clone()),
                    &mut old_t,bind,emit_for(&terms,&GROUP_BY_COPY,None,false),wiring).unwrap();
                let mut new_t=Transcript::new(b"subset4-proof");let mut stats=BooleanSubset4Stats::default();
                let(new,new_claim,_,_)=prove_boolean_u_grouped_with_fold_for_test(INPUT_BITS,COPY_BITS,BASE_ROW_BITS,0,&[BASE_ROW_BITS],
                    Some(0),&admission,GroupedDimensionPolicy::Generic24,|o|Ok(inputs[o].clone()),&mut new_t,
                    |t|{bind(t);Ok(())},emit_for(&terms,&GROUP_BY_COPY,None,false),wiring,BooleanXFoldMode::Subset4,Some(&mut stats)).unwrap();
                assert_eq!(gkr::encode_proof(&old).unwrap(),gkr::encode_proof(&new).unwrap());assert_eq!(claim,new_claim);
                compare_transcripts(&old_t,&new_t);assert_eq!(stats.apply_calls,(INPUT_BITS+1)*COPIES);
                let mut verify=Transcript::new(b"subset4-proof");
                let verified=gkr::verify_with_wiring(&[INPUT_BITS+COPY_BITS],ROW_COUNT,&new,&mut verify,bind,
                    |_,r,u,v|wiring(r,u,v).map_err(|_|GkrError::InvalidWireIndex)).unwrap();
                assert_eq!(verified,new_claim);compare_transcripts(&new_t,&verify);
                // The opt-in uses the actual checked loader on initial AND later loads.
                for late in [false,true]{let loads=std::cell::Cell::new(0);let bound=std::cell::Cell::new(false);
                    let mut t=Transcript::new(b"subset4-bad-load");let mut stats=BooleanSubset4Stats::default();
                    let result=prove_boolean_u_grouped_with_fold_for_test(INPUT_BITS,COPY_BITS,BASE_ROW_BITS,0,&[BASE_ROW_BITS],Some(0),
                        &admission,GroupedDimensionPolicy::Generic24,|o|{let i=loads.get();loads.set(i+1);let mut x=inputs[o].clone();
                            if i==if late{COPIES}else{0}{x[0]=Fr::from(2u64);}Ok(x)},&mut t,|_|{bound.set(true);Ok(())},
                        emit_for(&terms,&GROUP_BY_COPY,None,false),wiring,BooleanXFoldMode::Subset4,Some(&mut stats));
                    assert_eq!(result.err().as_deref(),Some("Boolean U input is not Boolean"));
                    assert_eq!(bound.get(),late);if !late{assert_eq!(t.challenges(),0);}}
            }

            #[test]
            fn boolean_u_real_producer_fused_k1_matches_dense_proof(){
                let(inputs,terms)=boolean_fixture();
                let admission=GroupedVAdmission::try_new(COPY_BITS,&GROUP_BY_COPY,&[2,1]).unwrap();
                let bind=|t:&mut Transcript|t.append_bytes(b"boolean-u-fused-k1",b"producer differential");
                let wiring=|r:&[Fr],u:&[Fr],v:&[Fr]|reference_wiring(&terms,&GROUP_BY_COPY,r,u,v);
                let mut dense_t=Transcript::new(b"boolean-u-fused-k1");
                let(dense,dense_claim,_,dense_stats)=prove_boolean_u_grouped_with_fold_for_test(
                    INPUT_BITS,COPY_BITS,BASE_ROW_BITS,0,&[BASE_ROW_BITS],Some(0),&admission,
                    GroupedDimensionPolicy::Generic24,|copy|Ok(inputs[copy].clone()),&mut dense_t,
                    |t|{bind(t);Ok(())},emit_for(&terms,&GROUP_BY_COPY,None,false),wiring,
                    BooleanXFoldMode::Legacy,None).unwrap();
                let mut fused_t=Transcript::new(b"boolean-u-fused-k1");
                let(fused,fused_claim,_,fused_stats)=prove_boolean_u_grouped_with_fold_for_test(
                    INPUT_BITS,COPY_BITS,BASE_ROW_BITS,0,&[BASE_ROW_BITS],Some(0),&admission,
                    GroupedDimensionPolicy::Generic24,|copy|Ok(inputs[copy].clone()),&mut fused_t,
                    |t|{bind(t);Ok(())},emit_for(&terms,&GROUP_BY_COPY,None,false),wiring,
                    BooleanXFoldMode::FusedPrefixK1,None).unwrap();
                assert_eq!(gkr::encode_proof(&fused).unwrap(),gkr::encode_proof(&dense).unwrap());
                assert_eq!(fused_claim,dense_claim);
                compare_transcripts(&fused_t,&dense_t);
                assert_eq!(fused_stats.owner_term_selections,dense_stats.owner_term_selections);
                let mut verifier=Transcript::new(b"boolean-u-fused-k1");
                let verified=gkr::verify_with_wiring(&[INPUT_BITS+COPY_BITS],ROW_COUNT,&fused,&mut verifier,
                    bind,|_,r,u,v|wiring(r,u,v).map_err(|_|GkrError::InvalidWireIndex)).unwrap();
                assert_eq!(verified,fused_claim);
                compare_transcripts(&verifier,&fused_t);
            }

            #[test]
            fn boolean_u_grouped_v_matches_direct_for_boolean_mixed_topologies(){
                let (inputs,terms)=boolean_fixture();
                let admission=GroupedVAdmission::try_new(COPY_BITS,&GROUP_BY_COPY,&[2,1]).unwrap();
                let bind=|t:&mut Transcript|t.append_bytes(b"boolean-u-statement",b"mixed Boolean owners");
                let wiring=|r:&[Fr],u:&[Fr],v:&[Fr]|reference_wiring(&terms,&GROUP_BY_COPY,r,u,v);
                let mut direct_t=Transcript::new(b"boolean-u-differential");
                let (direct,direct_claim,_)=prove_with_direct_u_grouped_v_for_test(INPUT_BITS,COPY_BITS,BASE_ROW_BITS,0,&[BASE_ROW_BITS],
                    Some(0),&admission,|copy|Ok(inputs[copy].clone()),&mut direct_t,bind,
                    emit_for(&terms,&GROUP_BY_COPY,None,false),wiring).unwrap();
                let mut boolean_t=Transcript::new(b"boolean-u-differential");
                let (boolean,boolean_claim,group_stats,stats)=prove_with_boolean_u_grouped_v_for_test(INPUT_BITS,COPY_BITS,BASE_ROW_BITS,0,&[BASE_ROW_BITS],
                    Some(0),&admission,|copy|Ok(inputs[copy].clone()),&mut boolean_t,bind,
                    emit_for(&terms,&GROUP_BY_COPY,None,false),wiring).unwrap();
                assert_eq!(boolean,direct);assert_eq!(boolean_claim,direct_claim);compare_transcripts(&boolean_t,&direct_t);
                assert_eq!(crate::gkr::encode_proof(&boolean).unwrap(),crate::gkr::encode_proof(&direct).unwrap());
                let mut verifier=Transcript::new(b"boolean-u-differential");
                let verified=gkr::verify_with_wiring(&[INPUT_BITS+COPY_BITS],ROW_COUNT,&boolean,&mut verifier,bind,
                    |_,r,u,v|wiring(r,u,v).map_err(|_|GkrError::InvalidWireIndex)).unwrap();
                assert_eq!(verified,boolean_claim);compare_transcripts(&verifier,&boolean_t);
                assert_eq!(group_stats.baseline_term_callbacks,7);assert_eq!(group_stats.bank_term_callbacks,3);
                assert_eq!(stats.prefix_builds,4);assert_eq!(stats.shared_term_iterations,12);assert_eq!(stats.owner_term_selections,28);
                assert_eq!(stats.boolean_checked_loads,32);assert_eq!(stats.boolean_checked_fields,32*WIDTH);
                assert!(stats.zero_anchor_sweep_skipped);assert_eq!(stats.preweight_entry_size_bytes,144);
                assert_eq!(stats.u_state_peak_capacity_bytes,*stats.u_phase_peak_capacity_bytes.iter().max().unwrap());
                assert!(stats.u_phase_peak_capacity_bytes[1]>=TensorRowWeightLookup::MAX_LOCAL_TABLE_BYTES
                    +TensorRowWeightLookup::MAX_SCALE_BYTES+64*1024,"row preparation must reserve resize overlap");
                assert!(stats.u_state_peak_capacity_bytes<=stats.u_preflight_capacity_bound_bytes);
                assert!(stats.u_preflight_capacity_bound_bytes<=MAX_INCREMENTAL_CACHE_STATE_BYTES);
                assert!(stats.u_prefix_preweight_elapsed_ns>0&&stats.u_owner_selection_elapsed_ns>0&&stats.u_x_fold_elapsed_ns>0);
            }

            #[test]
            fn boolean_u_grouped_v_rejects_nonboolean_before_bind_and_on_later_load(){
                let (inputs,terms)=boolean_fixture();let admission=GroupedVAdmission::try_new(COPY_BITS,&GROUP_BY_COPY,&[2,1]).unwrap();
                for later in [false,true]{
                    let bound=std::cell::Cell::new(false);let loads=std::cell::Cell::new(0usize);
                    let mut transcript=Transcript::new(b"boolean-u-domain-negative");
                    let result=prove_with_boolean_u_grouped_v_for_test(INPUT_BITS,COPY_BITS,BASE_ROW_BITS,0,&[BASE_ROW_BITS],Some(0),&admission,
                        |copy|{let index=loads.get();loads.set(index+1);let mut x=inputs[copy].clone();
                            if index==if later{COPIES}else{0}{x[0]=Fr::from(2u64);}Ok(x)},
                        &mut transcript,|_|bound.set(true),emit_for(&terms,&GROUP_BY_COPY,None,false),
                        |r,u,v|reference_wiring(&terms,&GROUP_BY_COPY,r,u,v));
                    assert_eq!(result.unwrap_err(),"Boolean U input is not Boolean");assert_eq!(bound.get(),later);
                    assert_eq!(transcript.challenges()>0,later);
                }
                let one=GroupedVAdmission::try_new(0,&[0],&[1]).unwrap();let bound=std::cell::Cell::new(false);
                let mut transcript=Transcript::new(b"boolean-u-zero-residual-nonboolean");
                let term=Term{row:0,gate:Gate{left:0,right:1,c0:Fr::zero(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::one()}};
                assert!(term.gate.evaluate(&[Fr::zero(),Fr::from(2u64)]).is_zero());
                let result=prove_with_boolean_u_grouped_v_for_test(1,0,0,0,&[0],Some(0),&one,
                    |_|Ok(vec![Fr::zero(),Fr::from(2u64)]),&mut transcript,|_|bound.set(true),
                    |_,sink|sink(term.clone()),|_,_,_|Ok([Fr::zero();4]));
                assert_eq!(result.unwrap_err(),"Boolean U input is not Boolean");assert!(!bound.get());assert_eq!(transcript.challenges(),0);
                // The unchanged generic fixture remains valid for its original route.
                let (arbitrary,arbitrary_terms)=super::fixture();let bound=std::cell::Cell::new(false);
                let mut transcript=Transcript::new(b"boolean-u-arbitrary-fixture-rejection");
                let result=prove_with_boolean_u_grouped_v_for_test(INPUT_BITS,COPY_BITS,BASE_ROW_BITS,0,&[BASE_ROW_BITS],Some(0),&admission,
                    |copy|Ok(arbitrary[copy].clone()),&mut transcript,|_|bound.set(true),
                    emit_for(&arbitrary_terms,&GROUP_BY_COPY,None,false),|r,u,v|reference_wiring(&arbitrary_terms,&GROUP_BY_COPY,r,u,v));
                assert_eq!(result.unwrap_err(),"Boolean U input is not Boolean");assert!(!bound.get());
            }

            #[test]
            fn boolean_u_grouped_v_does_not_replay_poisoned_canonical_callback(){
                let (inputs,terms)=boolean_fixture();let admission=GroupedVAdmission::try_new(COPY_BITS,&GROUP_BY_COPY,&[2,1]).unwrap();
                let calls=std::cell::Cell::new([0usize;COPIES]);let mut transcript=Transcript::new(b"boolean-u-frozen-relation");
                let result=prove_with_boolean_u_grouped_v_for_test(INPUT_BITS,COPY_BITS,BASE_ROW_BITS,0,&[BASE_ROW_BITS],Some(0),&admission,
                    |copy|Ok(inputs[copy].clone()),&mut transcript,|t|t.append_bytes(b"statement",b"frozen templates"),
                    |copy,sink|{let mut seen=calls.get();if seen[copy]!=0{return Err("poisoned callback replay".into());}
                        seen[copy]+=1;calls.set(seen);for term in &terms[GROUP_BY_COPY[copy]]{sink(term.clone())?;}Ok(())},
                    |r,u,v|reference_wiring(&terms,&GROUP_BY_COPY,r,u,v));
                assert!(result.is_ok());assert_eq!(calls.get(),[1;COPIES]);
            }

            #[test]
            fn boolean_u_preweighted_banks_match_direct_at_every_prefix(){
                let (inputs,terms)=boolean_fixture();let templates=vec![Some(terms[0].clone()),Some(terms[1].clone())];
                let r=[Fr::from(2u64),Fr::from(3u64),Fr::from(5u64),Fr::from(7u64)];
                let factor=OneFamilyRowFactor::try_new(&r,COPY_BITS,BASE_ROW_BITS,0,&[BASE_ROW_BITS],None).unwrap();
                let q=[Fr::from(7u64),Fr::from(11u64),Fr::from(13u64)];
                for k in 0..=INPUT_BITS{
                    let weights=boolean_u_eq_weights(&q[..k]).unwrap();
                    assert_eq!(weights,gkr::eq_weights(&q[..k]));assert_eq!(weights.capacity(),1<<k);
                    let mut stats=BooleanUPreweightStats::default();
                    let bank=BooleanUPreweightBank::build(&templates,&q[..k],&weights,&factor,WIDTH,&mut stats).unwrap();
                    for owner in 0..COPIES{
                        let actual=bank.coefficients(GROUP_BY_COPY[owner],&inputs[owner],WIDTH>>k,&mut stats).unwrap();
                        let expected=direct_u_prefix_coefficients(WIDTH,&q[..k],&weights,owner,&inputs[owner],|_,row|factor.local(row),
                            |sink|{for term in &terms[GROUP_BY_COPY[owner]]{sink(term.clone())?;}Ok(())}).unwrap();
                        assert_eq!(actual,expected,"owner {owner} prefix {k}");
                        // Independent full-width construction applies the
                        // owner row scale before any fold. This isolates each
                        // owner polynomial and handoff from aggregate cancellation.
                        let (mut reference_a,mut reference_b)=direct_u_prefix_coefficients(WIDTH,&[],&[Fr::one()],owner,
                            &inputs[owner],|copy,row|factor.local(row)*factor.copy(copy),
                            |sink|{for term in &terms[GROUP_BY_COPY[owner]]{sink(term.clone())?;}Ok(())}).unwrap();
                        let mut reference_x=inputs[owner].clone();let mut actual_x=inputs[owner].clone();
                        for challenge in &q[..k]{
                            gkr::fold(&mut reference_a,*challenge);gkr::fold(&mut reference_b,*challenge);
                            gkr::fold(&mut reference_x,*challenge);gkr::fold(&mut actual_x,*challenge);
                        }
                        if k<INPUT_BITS{
                            let mut actual_message=[Fr::zero();3];
                            OneFamilyRowFactor::add_scaled_message(&mut actual_message,&actual.0,&actual.1,&actual_x,factor.copy(owner));
                            assert_eq!(actual_message.as_slice(),gkr::quadratic_message(&reference_a,&reference_b,&reference_x).as_slice(),
                                "owner polynomial {owner} prefix {k}");
                        }else{
                            assert_eq!([factor.copy(owner)*actual.0[0],factor.copy(owner)*actual.1[0],actual_x[0]],
                                [reference_a[0],reference_b[0],reference_x[0]],"owner terminal A/B/X {owner}");
                        }
                    }
                }
            }

            #[test]
            fn boolean_u_preweight_isolated_faults(){
                let (inputs,terms)=boolean_fixture();let templates=vec![Some(terms[0].clone()),Some(terms[1].clone())];
                let r=[Fr::from(2u64),Fr::from(3u64),Fr::from(5u64),Fr::from(7u64)];
                let factor=OneFamilyRowFactor::try_new(&r,COPY_BITS,BASE_ROW_BITS,0,&[BASE_ROW_BITS],None).unwrap();
                let prefix=[Fr::from(7u64)];let weights=boolean_u_eq_weights(&prefix).unwrap();
                let mut stats=BooleanUPreweightStats::default();
                let bank=BooleanUPreweightBank::build(&templates,&prefix,&weights,&factor,WIDTH,&mut stats).unwrap();
                let expected=bank.coefficients(0,&inputs[0],WIDTH/2,&mut stats).unwrap();
                let stale_weights=boolean_u_eq_weights(&[Fr::from(11u64)]).unwrap();
                let stale=BooleanUPreweightBank::build(&templates,&prefix,&stale_weights,&factor,WIDTH,&mut stats).unwrap();
                assert_ne!(stale.coefficients(0,&inputs[0],WIDTH/2,&mut stats).unwrap(),expected,"stale prefix");
                let mut mask=bank.clone();let term=&terms[0][0];let w=weights[0]*factor.local(term.row);
                mask.entries[0].values=[w*term.gate.c1,w*(term.gate.c1+term.gate.c3),w*term.gate.c0,w*(term.gate.c0+term.gate.c2)];
                assert_ne!(mask.coefficients(0,&inputs[0],WIDTH/2,&mut stats).unwrap(),expected,"wrong low mask");
                let mut bucket=bank.clone();bucket.entries[0].bucket=1;
                assert_ne!(bucket.coefficients(0,&inputs[0],WIDTH/2,&mut stats).unwrap(),expected,"wrong bucket");
                let mut right=bank.clone();right.entries[0].right=6;
                assert_ne!(right.coefficients(0,&inputs[0],WIDTH/2,&mut stats).unwrap(),expected,"wrong right index");
                let mut folded=inputs[0].clone();gkr::fold(&mut folded,prefix[0]);folded.resize(WIDTH,Fr::zero());
                assert_ne!(bank.coefficients(0,&folded,WIDTH/2,&mut stats).unwrap(),expected,"folded X selection");
                assert_ne!(bank.coefficients(1,&inputs[0],WIDTH/2,&mut stats).unwrap(),expected,"wrong topology");
                let mut x=inputs[0].clone();gkr::fold(&mut x,prefix[0]);
                let local:[Fr;3]=gkr::quadratic_message(&expected.0,&expected.1,&x).try_into().unwrap();let scale=factor.copy(0);
                let scaled=local.map(|value|scale*value);assert_ne!(scaled,[Fr::zero();3]);
                assert_ne!(scaled,local,"omitted owner factor");assert_ne!(scaled,scaled.map(|value|scale*value),"doubled owner factor");
                let terminal=[Fr::from(7u64),Fr::from(11u64),Fr::from(13u64)];
                let terminal_bank=BooleanUPreweightBank::build(&templates,&terminal,&boolean_u_eq_weights(&terminal).unwrap(),&factor,WIDTH,&mut stats).unwrap();
                let terminal_expected=terminal_bank.coefficients(0,&inputs[0],1,&mut stats).unwrap();
                let early=BooleanUPreweightBank::build(&templates,&terminal[..2],&boolean_u_eq_weights(&terminal[..2]).unwrap(),&factor,WIDTH,&mut stats).unwrap();
                let early_value=early.coefficients(0,&inputs[0],2,&mut stats).unwrap();
                assert_ne!((terminal_expected.0[0],terminal_expected.1[0]),(early_value.0[0],early_value.1[0]),"missing terminal bank");
            }

            #[test]
            fn c324_fused_u0_width2_parity_right_and_duplicate_bucket_falsifiers(){
                let bank=BooleanUPreweightBank{
                    entries:vec![
                        BooleanUPreweight{bucket:0,right:0,values:[Fr::from(2u64),Fr::from(5u64),Fr::from(7u64),Fr::from(11u64)]},
                        BooleanUPreweight{bucket:0,right:1,values:[Fr::from(13u64),Fr::from(17u64),Fr::from(19u64),Fr::from(23u64)]},
                        BooleanUPreweight{bucket:1,right:0,values:[Fr::from(29u64),Fr::from(31u64),Fr::from(37u64),Fr::from(41u64)]},
                        BooleanUPreweight{bucket:1,right:1,values:[Fr::from(43u64),Fr::from(47u64),Fr::from(53u64),Fr::from(59u64)]},
                    ],ranges:vec![(0,4)],
                };
                let owner_factor=Fr::from(3u64);
                for mask in 0usize..4{
                    let input=[Fr::from((mask&1) as u64),Fr::from(((mask>>1)&1) as u64)];
                    let mut a=[Fr::zero();2];let mut b=[Fr::zero();2];
                    for entry in &bank.entries{
                        let selected=usize::from(input[entry.right].is_one());
                        a[entry.bucket]+=entry.values[selected];b[entry.bucket]+=entry.values[2+selected];
                    }
                    let dense:[Fr;3]=gkr::quadratic_message(&a,&b,&input).try_into().unwrap();
                    let fused=bank.fused_u0_message(0,&input).unwrap();
                    assert_eq!(fused,dense,"X mask {mask}");
                    assert_eq!(fused.map(|value|owner_factor*value),dense.map(|value|owner_factor*value),
                        "owner factor is applied after the local fused message");
                }
                // Isolate the corrected odd-p constant: B[1]=1 contributes
                // only to the linear coefficient, for every Boolean X pair.
                let odd_b_only=BooleanUPreweightBank{entries:vec![BooleanUPreweight{
                    bucket:1,right:0,values:[Fr::zero(),Fr::zero(),Fr::one(),Fr::one()],
                }],ranges:vec![(0,1)]};
                for mask in 0usize..4{
                    let input=[Fr::from((mask&1) as u64),Fr::from(((mask>>1)&1) as u64)];
                    assert_eq!(odd_b_only.fused_u0_message(0,&input).unwrap(),[Fr::zero(),Fr::one(),Fr::zero()],
                        "odd B-only constant must be zero for X mask {mask}");
                }
                assert!(bank.fused_u0_message(0,&[Fr::from(2u64),Fr::zero()]).is_err(),
                    "fused helper retains the full Boolean X check");
            }

            #[test]
            fn boolean_u_preweight_capacity_guards(){
                assert_eq!(std::mem::size_of::<Fr>(),32);assert_eq!(std::mem::size_of::<Term>(),152);
                assert_eq!(std::mem::size_of::<BooleanUPreweight>(),144);
                let native=GroupedVAdmission::try_new(2,&GROUP_BY_COPY,&[396561,388369]).unwrap();
                assert_eq!(boolean_u_prebind_capacity_bound(20,2,19,&native),Some(494492048));
                assert_eq!(boolean_u_loader_scratch_bound(1<<20),Some(2105344));
                assert!(boolean_u_prebind_capacity_bound(usize::MAX,2,19,&native).is_none());
                assert!(boolean_u_prebind_capacity_bound(20,2,22,&native).is_none());
                let huge=GroupedVAdmission::try_new(COPY_BITS,&GROUP_BY_COPY,&[1<<20,1<<20]).unwrap();
                let reached=std::cell::Cell::new(false);let mut transcript=Transcript::new(b"boolean-u-overcap");
                let result=prove_with_boolean_u_grouped_v_for_test(20,COPY_BITS,19,0,&[19],Some(0),&huge,
                    |_|Err("must not load".into()),&mut transcript,|_|reached.set(true),|_,_|Ok(()),|_,_,_|Ok([Fr::zero();4]));
                assert_eq!(result.unwrap_err(),"Boolean U checked capacity bound exceeds 512 MiB before binding");
                assert!(!reached.get());assert_eq!(transcript.challenges(),0);
                let mut stats=BooleanUPreweightStats{u_preflight_capacity_bound_bytes:MAX_INCREMENTAL_CACHE_STATE_BYTES,..Default::default()};
                assert!(stats.record_capacity(6,0).is_err());assert!(stats.record_capacity(0,MAX_INCREMENTAL_CACHE_STATE_BYTES+1).is_err());
                stats.u_preflight_capacity_bound_bytes=9;assert!(stats.record_capacity(0,10).is_err());
                let (inputs,terms)=boolean_fixture();let admission=GroupedVAdmission::try_new(COPY_BITS,&GROUP_BY_COPY,&[2,1]).unwrap();
                for side in [0,1]{for inactive in [false,true]{
                    let bound=std::cell::Cell::new(false);let mut transcript=Transcript::new(b"boolean-u-sentinel-negative");
                    let result=prove_with_boolean_u_grouped_v_for_test(INPUT_BITS,COPY_BITS,BASE_ROW_BITS,0,&[BASE_ROW_BITS],Some(0),&admission,
                        |copy|Ok(inputs[copy].clone()),&mut transcript,|_|bound.set(true),|copy,sink|{
                            for (index,original) in terms[GROUP_BY_COPY[copy]].iter().enumerate(){
                                let mut term=original.clone();if copy==0&&index==0{
                                    if side==0{term.gate.left=WIDTH;}else{term.gate.right=WIDTH;}
                                    if inactive{term.gate.c0=Fr::zero();term.gate.c1=Fr::zero();term.gate.c2=Fr::zero();term.gate.c3=Fr::zero();}
                                }sink(term)?;
                            }Ok(())},|r,u,v|reference_wiring(&terms,&GROUP_BY_COPY,r,u,v));
                    assert_eq!(result.unwrap_err(),"grouped V rejects sentinel or out-of-range endpoints");
                    assert!(!bound.get());assert_eq!(transcript.challenges(),0);
                }}
                let bound=std::cell::Cell::new(false);let mut transcript=Transcript::new(b"boolean-u-overcapacity-input");
                let result=prove_with_boolean_u_grouped_v_for_test(INPUT_BITS,COPY_BITS,BASE_ROW_BITS,0,&[BASE_ROW_BITS],Some(0),&admission,
                    |copy|{let mut x=Vec::with_capacity(2*WIDTH);x.extend_from_slice(&inputs[copy]);Ok(x)},
                    &mut transcript,|_|bound.set(true),emit_for(&terms,&GROUP_BY_COPY,None,false),
                    |r,u,v|reference_wiring(&terms,&GROUP_BY_COPY,r,u,v));
                assert_eq!(result.unwrap_err(),"Boolean U input length or capacity differs from width");assert!(!bound.get());
            }
        }
    }

    #[test]
    fn chunked_eq_weight_lookup_matches_scalar_products() {
        for bits in [0usize,1,7,8,9,16,21,41] {
            let point=(0..bits).map(|index|Fr::from((index as u64+17)*7919)).collect::<Vec<_>>();
            let lookup=EqWeightLookup::new(&point);
            let count=1usize.checked_shl(bits.min(12) as u32).unwrap();
            let mut indices=(0..count).step_by((count/37).max(1)).collect::<Vec<_>>();
            if bits>12 {indices.extend([0,(1usize<<bits)-1,1usize<<(bits-1)]);}
            for index in indices {assert_eq!(lookup.at(index),eq_weight_at(&point,index),"bits={bits} index={index}");}
        }
    }

    #[test]
    fn tensor_row_weight_tables_match_full_row_weights_and_bound_fallback() {
        let member_row_bits=[0usize,1,3,2];let base_row_bits=4;let copy_bits=2;
        let point=(0..base_row_bits+copy_bits+2)
            .map(|index|Fr::from((index as u64+29)*104729)).collect::<Vec<_>>();
        let cached=TensorRowWeightLookup::new(&point,copy_bits,base_row_bits,&member_row_bits);
        assert!(cached.fallback.is_none());
        let full=EqWeightLookup::new(&point);
        for (family,low) in member_row_bits.iter().copied().enumerate(){
            for copy in 0..1usize<<copy_bits{
                for local in 0..1usize<<low{
                    let row=(family<<base_row_bits)|local;
                    let global=(family<<(base_row_bits+copy_bits))|(copy<<low)|local;
                    assert_eq!(cached.at(copy,row),full.at(global),"family={family} copy={copy} local={local}");
                }
            }
        }

        let wide_bits=22usize;let wide_point=(0..wide_bits).map(|index|Fr::from(index as u64+3)).collect::<Vec<_>>();
        let wide_widths=[wide_bits];
        let wide=TensorRowWeightLookup::new(&wide_point,0,wide_bits,&wide_widths);
        assert!(wide.fallback.is_some(),"oversized local table should use the bounded lookup path");
        let bounded=EqWeightLookup::new(&wide_point);
        for index in [0usize,1,1usize<<(wide_bits-1),(1usize<<wide_bits)-1]{
            assert_eq!(wide.at(0,index),bounded.at(index));
        }

        // A wide family domain with only family zero present must not allocate
        // an equality table for all 2^40 family tags.
        let family_point=(0..40).map(|index|Fr::from(index as u64+11)).collect::<Vec<_>>();
        let one_family=[0usize];
        let sparse_families=TensorRowWeightLookup::new(&family_point,0,0,&one_family);
        assert!(sparse_families.fallback.is_none());
        assert_eq!(sparse_families.at(0,0),eq_weight_at(&family_point,0));

        // Exceed the family-by-copy scale budget without a large point table;
        // this must select the chunked fallback before allocating scales.
        let many_families=vec![0usize;262_145];let many_point=vec![Fr::from(7u64);21];
        let many=TensorRowWeightLookup::new(&many_point,2,0,&many_families);
        assert!(many.fallback.is_some());
        let many_full=EqWeightLookup::new(&many_point);let family=262_144;let copy=3;
        assert_eq!(many.at(copy,family),many_full.at((family<<2)|copy));
    }

    #[test]
    fn edge_stream_matches_resident_at_26_bit_three_family_layout(){
        const INPUT_BITS:usize=2;
        const SLOT_BITS:usize=4;
        const BASE_ROW_BITS:usize=20;
        const FAMILY_BITS:usize=2;
        const WIDTH:usize=1<<INPUT_BITS;
        const INPUT_WIDTH:usize=WIDTH*(1<<SLOT_BITS);
        const ROW_BITS:usize=BASE_ROW_BITS+SLOT_BITS+FAMILY_BITS;
        let member_row_bits=[17usize,19,20];
        let input=(0..INPUT_WIDTH).map(|index|Fr::from(100+index as u64)).collect::<Vec<_>>();
        let active_slots=[2usize,7,13];
        let mut edges=Vec::<EdgeTerm>::with_capacity(6);
        for (family,&source_slot) in active_slots.iter().enumerate(){
            let local_row=(1usize<<member_row_bits[family])-1;
            for term_index in 0..2{
                let left_wire=term_index;
                let right_slot=source_slot-term_index-1;
                let right_wire=3-term_index;
                let left=source_slot*WIDTH+left_wire;
                let right=right_slot*WIDTH+right_wire;
                let x=input[left];let y=input[right];
                let c1=Fr::from((3+family as u64*2+term_index as u64) as u64);
                let c2=Fr::from((7+family as u64*3+term_index as u64) as u64);
                let c3=Fr::from((11+family as u64*4+term_index as u64) as u64);
                let target=if term_index==0{Fr::one()}else{-Fr::one()};
                let c0=target-c1*x-c2*y-c3*x*y;
                assert!(!c0.is_zero()&&!c1.is_zero()&&!c2.is_zero()&&!c3.is_zero());
                let family_row=(family<<BASE_ROW_BITS)|local_row;
                let term=Term{row:local_row,gate:Gate{left,right,c0,c1,c2,c3}};
                assert_eq!(term.gate.evaluate(&input),target);
                edges.push(EdgeTerm{source_slot,family_row,term});
            }
        }

        let materialized_row=|edge:&EdgeTerm|{
            let family=edge.family_row>>BASE_ROW_BITS;
            let local=edge.family_row&((1usize<<BASE_ROW_BITS)-1);
            (family<<(BASE_ROW_BITS+SLOT_BITS))
                |(edge.source_slot<<member_row_bits[family])|local
        };
        let mut resident_terms=edges.iter().map(|edge|{
            let expected=materialized_row(edge);
            assert_eq!(global_edge_row(edge.source_slot,edge.family_row,SLOT_BITS,
                BASE_ROW_BITS,FAMILY_BITS,&member_row_bits).unwrap(),expected);
            let family=edge.family_row>>BASE_ROW_BITS;
            let uniform_slot=(family<<(BASE_ROW_BITS+SLOT_BITS))
                |(edge.source_slot<<BASE_ROW_BITS)
                |(edge.family_row&((1usize<<BASE_ROW_BITS)-1));
            if family<2{assert_ne!(expected,uniform_slot,"family {family} needs its own slot-bit offset");}
            Term{row:expected,gate:edge.term.gate.clone()}
        }).collect::<Vec<_>>();
        resident_terms.sort_by_key(|term|term.row);
        let mut row_residuals=std::collections::BTreeMap::<usize,Fr>::new();
        for term in &resident_terms{
            *row_residuals.entry(term.row).or_insert(Fr::zero())+=term.gate.evaluate(&input);
        }
        assert!(row_residuals.values().all(Zero::is_zero),"fixture must satisfy each tagged row");

        assert!(global_edge_row(0,1usize<<17,SLOT_BITS,BASE_ROW_BITS,FAMILY_BITS,&member_row_bits).is_err(),
            "DAA member row overflow must fail closed");
        assert!(global_edge_row(0,3usize<<BASE_ROW_BITS,SLOT_BITS,BASE_ROW_BITS,FAMILY_BITS,&member_row_bits).is_err(),
            "unallocated family tag must fail closed");

        let domain=b"nipopow-v2-global-edge-three-family-layout-v1";
        let bind=|transcript:&mut Transcript|{
            transcript.append_bytes(b"edge-layout-profile",b"input=2;slots=4;rows=20;families=2;members=17,19,20");
            transcript.append_bytes(b"active-source-slots",&[2,7,13]);
        };
        let mut resident_transcript=Transcript::new(domain);
        let (resident,resident_claim)=prove(6,0,ROW_BITS,0,&[ROW_BITS],|copy|{
            if copy!=0{return Err("resident fixture has exactly one flattened copy".into());}
            Ok(input.clone())
        },&mut resident_transcript,bind,|copy,sink|{
            if copy!=0{return Err("resident fixture has exactly one term stream".into());}
            for term in &resident_terms{sink(term.clone())?;}
            Ok(())
        },|r,u,v|explicit_global_terms_wiring(&resident_terms,r,u,v)).unwrap();

        let mut streamed_transcript=Transcript::new(domain);
        let (streamed,streamed_claim,_,_)=prove_edge_terms(INPUT_BITS,SLOT_BITS,BASE_ROW_BITS,
            FAMILY_BITS,&member_row_bits,|left,slot,sink|{
                emit_global_test_edges(&edges,None,left,slot,sink)
            },|slot|Ok(input[slot*WIDTH..(slot+1)*WIDTH].to_vec()),&mut streamed_transcript,
            bind,|r,u,v|explicit_global_terms_wiring(&resident_terms,r,u,v)).unwrap();

        assert_eq!(gkr::encode_proof(&streamed).unwrap(),gkr::encode_proof(&resident).unwrap(),
            "streamed family/slot packing must match a resident 2^26-row relation");
        assert_eq!(streamed_claim,resident_claim);
        assert_eq!(streamed_transcript.challenges(),resident_transcript.challenges());
        assert_eq!(streamed_transcript.raw_queries(),resident_transcript.raw_queries());
        assert_eq!(streamed_transcript.bytes_absorbed(),resident_transcript.bytes_absorbed());

        let mut mutant_transcript=Transcript::new(domain);
        let mutant=prove_edge_terms(INPUT_BITS,SLOT_BITS,BASE_ROW_BITS,FAMILY_BITS,&member_row_bits,
            |left,slot,sink|emit_global_test_edges(&edges,Some((0,2,active_slots[0]+1)),left,slot,sink),
            |slot|Ok(input[slot*WIDTH..(slot+1)*WIDTH].to_vec()),&mut mutant_transcript,
            bind,|r,u,v|explicit_global_terms_wiring(&resident_terms,r,u,v));
        assert_eq!(mutant.unwrap_err(),GkrError::TerminalExpression.to_string(),
            "moving one complete zero-residual family row must fail canonical terminal wiring");
    }

    #[test]
    #[ignore = "bounded H5 replay-count diagnostic; expands eight 2^20-field slots"]
    fn diagnostic_h5_local_roster_copy_replays() {
        let copies=8usize;let width=1usize<<20;
        let mut reads=vec![0usize;copies];let mut visits=vec![0usize;copies];
        let started=std::time::Instant::now();
        let mut transcript=Transcript::new(b"nipopow-v2-h5-local-replay-diagnostic-v1");
        let (proof,claim)=prove(20,3,0,0,&[0],|copy|{
            reads[copy]+=1;Ok(vec![Fr::zero();width])
        },&mut transcript,|_|{},|copy,sink|{
            visits[copy]+=1;sink(Term{row:0,gate:Gate{left:0,right:0,
                c0:Fr::zero(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}})
        },|_,_,_|Ok([Fr::zero();4])).unwrap();
        assert_eq!(proof.layers[0].rounds.len(),46);
        assert_eq!(claim.point.len(),23);
        assert_eq!(reads,&[4;8],"bounded sparse coefficient cache should use baseline, U, V, and final-line reads only");
        assert_eq!(visits,&[3;8],"each slot's terms should be visited in baseline, U, and V only");
        println!("h5_local_replay_diagnostic copies={copies} width={width} reads_per_copy={} term_visits_per_copy={} total_reads={} elapsed_ms={}",
            reads[0],visits[0],reads.iter().sum::<usize>(),started.elapsed().as_millis());
    }

    #[test]
    #[ignore = "bounded H5 resident/streaming differential; retains a 256 MiB witness"]
    fn diagnostic_h5_sparse_cache_matches_resident_nontrivial_proof() {
        let copies=8usize;let width=1usize<<20;let input_len=copies*width;
        let input=(0..copies).flat_map(|copy|{
            let mut local=vec![Fr::zero();width];local[0]=Fr::from((copy&1) as u64);local
        }).collect::<Vec<_>>();
        let mut terms=Vec::with_capacity(copies*3);
        for copy in 0..copies{
            // The first term is constant in the streamed relation and thus
            // exercises both global-index-zero anchor paths; the second
            // cancels it at this row. The final nonlinear term constrains the
            // nonzero witness values to bits.
            terms.push(Term{row:copy,gate:Gate{left:0,right:0,c0:Fr::one(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}});
            terms.push(Term{row:copy,gate:Gate{left:copy*width,right:copy*width,c0:-Fr::one(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}});
            terms.push(Term{row:copy,gate:Gate{left:copy*width,right:copy*width,c0:Fr::zero(),c1:-Fr::one(),c2:Fr::zero(),c3:Fr::one()}});
        }
        let circuit=crate::sparse::Circuit{input_len,row_count:copies,terms};
        let shape=crate::sparse::validate(&circuit,0).unwrap();
        let bind=|transcript:&mut Transcript|transcript.append_bytes(b"toy-statement",b"h5-sparse-cache-nonlinear-anchors-v1");

        let started=std::time::Instant::now();
        let mut resident_transcript=Transcript::new(b"h5-sparse-cache-parity");
        let (resident,resident_claim)=crate::sparse::prove_with_binding(&circuit,&input,0,&mut resident_transcript,bind).unwrap();
        let mut reads=vec![0usize;copies];let mut visits=vec![0usize;copies];
        let mut streamed_transcript=Transcript::new(b"h5-sparse-cache-parity");
        let (streamed,streamed_claim)=prove(20,3,0,0,&[0],|copy|{
            reads[copy]+=1;Ok(input[copy*width..(copy+1)*width].to_vec())
        },&mut streamed_transcript,bind,|copy,sink|{
            visits[copy]+=1;
            sink(Term{row:0,gate:Gate{left:width,right:width,c0:Fr::one(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}})?;
            sink(Term{row:0,gate:Gate{left:0,right:0,c0:-Fr::one(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}})?;
            sink(Term{row:0,gate:Gate{left:0,right:0,c0:Fr::zero(),c1:-Fr::one(),c2:Fr::zero(),c3:Fr::one()}})
        },|r,u,v|crate::sparse::wiring(&circuit,&shape,r,u,v).map_err(|error|error.to_string())).unwrap();
        assert_eq!(streamed,resident,"sparse-cache GKR proof differs from resident proof");
        assert_eq!(streamed_claim,resident_claim);
        assert_eq!(streamed_transcript.challenges(),resident_transcript.challenges());
        assert_eq!(streamed_transcript.raw_queries(),resident_transcript.raw_queries());
        assert_eq!(streamed_transcript.bytes_absorbed(),resident_transcript.bytes_absorbed());
        assert_eq!(reads,vec![4;copies]);assert_eq!(visits,vec![3;copies]);

        let mut verifier_transcript=Transcript::new(b"h5-sparse-cache-parity");
        let checked=crate::gkr::verify_with_wiring(&[23],copies,&streamed,&mut verifier_transcript,bind,
            |_,r,u,v|crate::sparse::wiring(&circuit,&shape,r,u,v)).unwrap();
        assert_eq!(checked,streamed_claim);
        assert_eq!(verifier_transcript.challenges(),streamed_transcript.challenges());
        assert_eq!(verifier_transcript.raw_queries(),streamed_transcript.raw_queries());

        let mut mutant=circuit.clone();mutant.terms[2].gate.c1+=Fr::one();
        let mutant_shape=crate::sparse::validate(&mutant,0).unwrap();
        let mut mutant_transcript=Transcript::new(b"h5-sparse-cache-parity");
        assert!(crate::gkr::verify_with_wiring(&[23],copies,&streamed,&mut mutant_transcript,bind,
            |_,r,u,v|crate::sparse::wiring(&mutant,&mutant_shape,r,u,v)).is_err(),
            "single-term coefficient mutant must not verify");
        println!("h5_sparse_cache_parity copies={copies} width={width} total_reads={} term_visits={} proof_bytes={} elapsed_ms={}",
            reads.iter().sum::<usize>(),visits.iter().sum::<usize>(),crate::gkr::encode_proof(&streamed).unwrap().len(),started.elapsed().as_millis());
    }

    #[test]
    fn sparse_gkr_messages_and_incremental_folds_match_dense_vectors() {
        for width in [2usize,4,16,64]{
            let mut a=(0..width).map(|index|if index%5==0{Fr::zero()}else{Fr::from((index*17+3) as u64)}).collect::<Vec<_>>();
            let mut b=(0..width).map(|index|if index%7==0{Fr::zero()}else{Fr::from((index*13+9) as u64)}).collect::<Vec<_>>();
            let mut x=(0..width).map(|index|Fr::from((index*19+5) as u64)).collect::<Vec<_>>();
            let mut sparse_a=compact_nonzero(a.clone());let mut sparse_b=compact_nonzero(b.clone());
            for challenge in [Fr::from(23u64),Fr::from(31u64),Fr::from(47u64)].into_iter().take(width.trailing_zeros() as usize){
                let dense_message=gkr::quadratic_message(&a,&b,&x);
                assert_eq!(sparse_quadratic_message(&sparse_a,&sparse_b,&x).as_slice(),dense_message.as_slice());
                gkr::fold(&mut a,challenge);gkr::fold(&mut b,challenge);gkr::fold(&mut x,challenge);
                sparse_a=sparse_fold(&sparse_a,challenge);sparse_b=sparse_fold(&sparse_b,challenge);
                assert_eq!(sparse_a,compact_nonzero(a.clone()));assert_eq!(sparse_b,compact_nonzero(b.clone()));
            }
        }
    }

    #[test]
    fn edge_endpoint_walk_rejects_count_drift_and_endpoint_slot_drift() {
        let edge = || EdgeTerm {
            source_slot: 0,
            family_row: 0,
            term: Term { row: 0, gate: Gate { left: 0, right: 0, c0: Fr::zero(), c1: Fr::one(), c2: Fr::zero(), c3: Fr::zero() } },
        };
        let mut stable = |_left: bool, _slot: usize, sink: &mut dyn FnMut(EdgeTerm)->Result<(),String>| sink(edge());
        assert_eq!(walk_edge_endpoint(&mut stable,true,0,2,2,0,&[0],Some(1),&mut |_|Ok(())).unwrap(),1);

        let mut drifted = |_left: bool, _slot: usize, sink: &mut dyn FnMut(EdgeTerm)->Result<(),String>| {
            sink(edge())?;sink(edge())
        };
        assert!(walk_edge_endpoint(&mut drifted,true,0,2,2,0,&[0],Some(1),&mut |_|Ok(()) )
            .unwrap_err().contains("exceeded its baseline count"));

        let mut wrong_endpoint = |_left: bool, _slot: usize, sink: &mut dyn FnMut(EdgeTerm)->Result<(),String>| {
            let mut term=edge();term.term.gate.left=2;sink(term)
        };
        assert!(walk_edge_endpoint(&mut wrong_endpoint,true,0,2,2,0,&[0],Some(1),&mut |_|Ok(()))
            .unwrap_err().contains("outside declared slot"));
    }

    #[test]
    fn edge_stream_cache_evicts_slots_and_matches_resident_proof() {
        let copies=8usize;
        // Edge s compares left[s] == right[s-1]. Both endpoint values vary
        // across slots, so reloading the wrong cache entry cannot pass by
        // relying on the all-ones wire used in the earlier fixture.
        let input=(0..copies).flat_map(|slot|[Fr::from(slot as u64+1),Fr::from(slot as u64+2)]).collect::<Vec<_>>();
        let mut terms=Vec::new();
        for source_slot in 1..copies{
            terms.push(Term{row:source_slot,gate:Gate{left:source_slot*2,right:(source_slot-1)*2+1,
                c0:Fr::zero(),c1:Fr::one(),c2:-Fr::one(),c3:Fr::zero()}});
        }
        let circuit=crate::sparse::Circuit{input_len:input.len(),row_count:64,terms};
        let shape=crate::sparse::validate(&circuit,0).unwrap();
        let bind=|t:&mut Transcript|t.append_bytes(b"toy-streamed-edges",b"eight-slot-chain-v1");
        let mut resident_t=Transcript::new(b"copy-cache-eviction-parity");
        let (resident,resident_claim)=crate::sparse::prove_with_binding(&circuit,&input,0,&mut resident_t,bind).unwrap();
        let mut reads=0usize;let mut streamed_t=Transcript::new(b"copy-cache-eviction-parity");
        let (streamed,streamed_claim,used_u,used_v)=prove_edge_terms_with_cache_limit_for_test(1,3,3,0,&[0],0,|left,slot,sink|{
            let source_slot=if left{slot}else{slot+1};
            if source_slot==0||source_slot>=copies{return Ok(());}
            sink(EdgeTerm{source_slot,family_row:0,term:Term{row:source_slot,gate:Gate{
                left:source_slot*2,right:(source_slot-1)*2+1,c0:Fr::zero(),c1:Fr::one(),c2:-Fr::one(),c3:Fr::zero()}}})
        },|copy|{reads+=1;Ok(input[copy*2..(copy+1)*2].to_vec())},&mut streamed_t,bind,
            |r,u,v|crate::sparse::wiring(&circuit,&shape,r,u,v).map_err(|error|error.to_string())).unwrap();
        assert_eq!(crate::gkr::encode_proof(&streamed).unwrap(),crate::gkr::encode_proof(&resident).unwrap());
        assert_eq!(streamed_claim,resident_claim);
        assert!(!used_u && !used_v,"both local phases must exercise fallback");
        assert_eq!(streamed_t.challenges(),resident_t.challenges());
        assert_eq!(streamed_t.raw_queries(),resident_t.raw_queries());
        assert_eq!(streamed_t.bytes_absorbed(),resident_t.bytes_absorbed());
        assert_eq!(streamed_t.clone().challenge_scalar(b"cache-eviction-continuation"),
            resident_t.clone().challenge_scalar(b"cache-eviction-continuation"));
        assert!(reads>copies,"eight slots must evict and reread entries through the fixed four-slot cache");
    }

    #[test]
    fn edge_sparse_replay_four_modes_match_resident_and_reject_mutants() {
        const WIDTH:usize=64;const COPIES:usize=8;const ROWS:usize=64;
        let input=(1..=WIDTH*COPIES).map(|i|Fr::from(i as u64)).collect::<Vec<_>>();
        let members=[2usize,1];
        let satisfied=|left:usize,right:usize,c1:Fr,c2:Fr,c3:Fr|Gate{left,right,
            c0:-(c1*input[left]+c2*input[right]+c3*input[left]*input[right]),c1,c2,c3};
        let edge=|source_slot:usize,family:usize,local:usize,gate:Gate|EdgeTerm{
            source_slot,family_row:(family<<2)|local,term:Term{row:local,gate}};
        let mut edges=vec![
            edge(0,0,0,satisfied(0,WIDTH*COPIES-1,Fr::from(2u64),Fr::from(3u64),Fr::from(5u64))),
            edge(1,0,1,Gate{left:WIDTH+5,right:4*WIDTH+9,c0:Fr::zero(),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()}),
            edge(1,0,1,Gate{left:WIDTH+5,right:4*WIDTH+9,c0:-input[WIDTH+5],c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}),
            edge(3,1,0,satisfied(2*WIDTH+3,5*WIDTH+7,-Fr::from(3u64),Fr::from(2u64),Fr::one())),
            edge(7,1,1,satisfied(WIDTH*COPIES-1,0,Fr::one(),-Fr::from(4u64),Fr::from(2u64))),
            // The right-slot-2 C bank is completely absent, but D is not.
            edge(2,0,3,satisfied(3*WIDTH+9,2*WIDTH+11,Fr::one(),Fr::zero(),Fr::zero())),
        ];
        // Repeated support and exact cancellation exercise coalescing. The
        // crowded slot also keeps the old dense fallback cheaper than sparse.
        for pair in 0..14{
            let (source_slot,local,left,right)=if pair==0{(1,1,WIDTH+5,4*WIDTH+9)}else{(4,2,4*WIDTH+9,5*WIDTH+7)};
            for sign in [Fr::one(),-Fr::one()]{edges.push(edge(source_slot,0,local,Gate{left,right,
                c0:sign*Fr::from(13u64),c1:sign*Fr::from(7u64),c2:sign*Fr::from(11u64),c3:sign*Fr::from(17u64)}));}
        }
        let circuit_for=|source:&[EdgeTerm]|crate::sparse::Circuit{input_len:input.len(),row_count:ROWS,
            terms:source.iter().map(|edge|Term{
                // Independent explicit row packing for the resident verifier.
                row:((edge.family_row>>2)<<5)|(edge.source_slot<<members[edge.family_row>>2])|(edge.family_row&3),
                gate:edge.term.gate.clone(),
            }).collect()};
        let circuit=circuit_for(&edges);let shape=crate::sparse::validate(&circuit,0).unwrap();
        let counts=|left:bool,slot:usize|edges.iter().filter(|e|{
            (if left{e.term.gate.left}else{e.term.gate.right})/WIDTH==slot
        }).count();
        for left in [true,false]{
            assert!(matches!(EdgeReplayBanks::new(WIDTH,counts(left,0)).unwrap(),EdgeReplayBanks::Sparse(..)));
            assert_eq!(counts(left,6),0);
            assert!(matches!(EdgeReplayBanks::new(WIDTH,counts(left,6)).unwrap(),EdgeReplayBanks::Sparse(..)));
        }
        assert!(matches!(EdgeReplayBanks::new(WIDTH,counts(true,4)).unwrap(),EdgeReplayBanks::Dense(..)));
        assert!(matches!(EdgeReplayBanks::new(WIDTH,counts(false,5)).unwrap(),EdgeReplayBanks::Dense(..)));
        assert!(matches!(EdgeReplayBanks::new(WIDTH,usize::MAX).unwrap(),EdgeReplayBanks::Dense(..)));
        let emit=|source:&[EdgeTerm],left:bool,slot:usize,sink:&mut dyn FnMut(EdgeTerm)->Result<(),String>|{
            for edge in source{if (if left{edge.term.gate.left}else{edge.term.gate.right})/WIDTH==slot{sink(edge.clone())?;}}
            Ok(())
        };
        let bind=|t:&mut Transcript|t.append_bytes(b"edge-replay-fixture",b"eight-distinct-slots-four-modes-v1");
        let domain=b"edge-sparse-replay-resident-parity";
        let mut resident_t=Transcript::new(domain);
        let (resident,resident_claim)=crate::sparse::prove_with_binding(&circuit,&input,0,&mut resident_t,bind).unwrap();
        let resident_bytes=gkr::encode_proof(&resident).unwrap();
        let same_transcript=|a:&Transcript,b:&Transcript|{
            assert_eq!(a.challenges(),b.challenges());assert_eq!(a.raw_queries(),b.raw_queries());
            assert_eq!(a.bytes_absorbed(),b.bytes_absorbed());
            assert_eq!(a.clone().challenge_scalar(b"next-after-edge-proof"),b.clone().challenge_scalar(b"next-after-edge-proof"));
        };
        for (force_u_off,force_v_off) in [(false,false),(true,false),(false,true),(true,true)]{
            let mut streamed_t=Transcript::new(domain);let mut reads=0usize;
            let (proof,claim,used_u,used_v)=prove_edge_terms_inner(6,3,2,1,&members,
                |left,slot,sink|emit(&edges,left,slot,sink),
                |slot|{reads+=1;Ok(input[slot*WIDTH..(slot+1)*WIDTH].to_vec())},&mut streamed_t,bind,
                |r,u,v|crate::sparse::wiring(&circuit,&shape,r,u,v).map_err(|e|e.to_string()),
                EdgeIncrementalControl{force_u_off,force_v_off,..EdgeIncrementalControl::default()}).unwrap();
            assert_eq!((used_u,used_v),(!force_u_off,!force_v_off));
            assert_eq!(gkr::encode_proof(&proof).unwrap(),resident_bytes);assert_eq!(claim,resident_claim);
            assert_eq!(gkr::mle(&input,&claim.point).unwrap(),claim.value);
            same_transcript(&streamed_t,&resident_t);assert!(reads>COPIES);
            let mut verifier_t=Transcript::new(domain);
            let checked=gkr::verify_with_wiring(&[9],ROWS,&proof,&mut verifier_t,bind,
                |_,r,u,v|crate::sparse::wiring(&circuit,&shape,r,u,v)).unwrap();
            assert_eq!(checked,claim);same_transcript(&verifier_t,&streamed_t);
        }
        // Change one endpoint only; coefficients, row and transcript binding
        // remain fixed. Both the residual and canonical proof must reject it.
        let mut endpoint_edges=edges.clone();endpoint_edges[0].term.gate.left=1;
        let endpoint_circuit=circuit_for(&endpoint_edges);
        assert!(!endpoint_circuit.terms[0].gate.evaluate(&input).is_zero());
        let endpoint_shape=crate::sparse::validate(&endpoint_circuit,0).unwrap();
        let mut endpoint_t=Transcript::new(domain);
        assert!(gkr::verify_with_wiring(&[9],ROWS,&resident,&mut endpoint_t,bind,
            |_,r,u,v|crate::sparse::wiring(&endpoint_circuit,&endpoint_shape,r,u,v)).is_err());
        // Move every term of a satisfied, non-identically-zero row. Term
        // counts, endpoints and coefficients are identical: only its source
        // slot changes. Its own proof succeeds, but the canonical row rejects.
        let mut relocated=edges.clone();let mut moved=0;
        for edge in &mut relocated{if edge.source_slot==1&&edge.family_row==1{edge.source_slot=5;moved+=1;}}
        assert_eq!(moved,4);
        let relocated_circuit=circuit_for(&relocated);
        let mut rows=vec![Fr::zero();ROWS];
        for term in &relocated_circuit.terms{rows[term.row]+=term.gate.evaluate(&input);}
        assert!(rows.iter().all(Zero::is_zero));
        let relocated_shape=crate::sparse::validate(&relocated_circuit,0).unwrap();
        let mut relocated_t=Transcript::new(domain);
        let (relocated_proof,_,used_u,used_v)=prove_edge_terms_inner(6,3,2,1,&members,
            |left,slot,sink|emit(&relocated,left,slot,sink),
            |slot|Ok(input[slot*WIDTH..(slot+1)*WIDTH].to_vec()),&mut relocated_t,bind,
            |r,u,v|crate::sparse::wiring(&relocated_circuit,&relocated_shape,r,u,v).map_err(|e|e.to_string()),
                EdgeIncrementalControl{force_u_off:true,force_v_off:true,..EdgeIncrementalControl::default()}).unwrap();
        assert_eq!((used_u,used_v),(false,false));
        assert_ne!(gkr::encode_proof(&relocated_proof).unwrap(),resident_bytes);
        let mut wrong_row_t=Transcript::new(domain);
        assert!(gkr::verify_with_wiring(&[9],ROWS,&relocated_proof,&mut wrong_row_t,bind,
            |_,r,u,v|crate::sparse::wiring(&circuit,&shape,r,u,v)).is_err());
        // This is an algebraic fallback differential, not a historical cost
        // estimate. X and the copy cache remain streamed/dense.
    }

    #[test]
    fn tensor_residual_rejects_nonmonotone_rows() {
        let mut transcript=Transcript::new(b"nonmonotone-residual-order");
        let error=prove(0,0,1,0,&[1],|_|Ok(vec![Fr::zero()]),&mut transcript,|_|{},|_,sink|{
            sink(Term{row:0,gate:Gate{left:0,right:0,c0:Fr::one(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}})?;
            sink(Term{row:0,gate:Gate{left:0,right:0,c0:-Fr::one(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}})?;
            sink(Term{row:1,gate:Gate{left:0,right:0,c0:Fr::zero(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}})?;
            sink(Term{row:0,gate:Gate{left:0,right:0,c0:Fr::zero(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}})
        },|_,_,_|Err("wiring must not be reached".into())).unwrap_err();
        assert!(error.contains("canonical nondecreasing order"),"unexpected error: {error}");
    }

    #[test]
    fn tensor_stream_aggregates_4_8_16_copies_into_one_resident_equivalent_proof() {
        use std::cell::Cell;

        for copy_bits in [2usize,3,4] {
            let copies=1usize<<copy_bits;
            let input=(0..copies).flat_map(|copy|[
                Fr::from((copy&1) as u64),Fr::from(((copy>>1)&1) as u64),
            ]).collect::<Vec<_>>();
            let local_gate=|wire|Gate{left:wire,right:wire,c0:Fr::zero(),c1:-Fr::one(),c2:Fr::zero(),c3:Fr::one()};
            let terms=(0..copies).map(|copy|Term{row:copy,gate:local_gate(copy*2)}).collect::<Vec<_>>();
            let circuit=crate::sparse::Circuit{input_len:input.len(),row_count:copies,terms};
            let shape=crate::sparse::validate(&circuit,0).unwrap();
            let bind=|transcript:&mut Transcript|transcript.append_bytes(b"toy-statement",b"single-global-copy-roster-v1");

            let mut resident_transcript=Transcript::new(b"copy-scale-single-proof");
            let (resident,claim)=crate::sparse::prove_with_binding(&circuit,&input,0,&mut resident_transcript,bind).unwrap();
            let reads=Cell::new(0usize);
            let mut streamed_transcript=Transcript::new(b"copy-scale-single-proof");
            let (streamed,streamed_claim)=prove(1,copy_bits,0,0,&[0],|copy|{
                reads.set(reads.get()+1);
                Ok(input[copy*2..copy*2+2].to_vec())
            },&mut streamed_transcript,bind,|_copy,sink|{
                sink(Term{row:0,gate:local_gate(0)})
            },|r,u,v|crate::sparse::wiring(&circuit,&shape,r,u,v).map_err(|error|error.to_string())).unwrap();

            let proof_bytes=crate::gkr::encode_proof(&streamed).unwrap().len();
            assert_eq!(streamed.layers.len(),1,"all copies must produce one GKR layer/proof");
            assert_eq!(streamed.layers[0].rounds.len(),2*(1+copy_bits),"one proof must cover the combined input/slot domain");
            assert_eq!(streamed, resident,"streamed aggregate must equal the resident proof");
            assert_eq!(streamed_claim,claim);
            assert_eq!(streamed_transcript.challenges(),resident_transcript.challenges());
            assert_eq!(streamed_transcript.raw_queries(),resident_transcript.raw_queries());
            assert_eq!(streamed_transcript.bytes_absorbed(),resident_transcript.bytes_absorbed());
            eprintln!("copy-scale copies={copies} load_copy_calls={} proof_bytes={proof_bytes} gkr_rounds={}",reads.get(),streamed.layers[0].rounds.len());
        }
    }

    #[test]
    #[ignore = "manual stress at the approximate Mainnet header count"]
    fn tensor_stream_aggregates_mainnet_scale_copy_count_into_one_resident_equivalent_proof() {
        use std::cell::Cell;

        let copy_bits=21usize;
        let copies=1usize<<copy_bits;
        let input=vec![Fr::zero();copies];
        let local_gate=Gate{left:0,right:0,c0:Fr::zero(),c1:-Fr::one(),c2:Fr::zero(),c3:Fr::one()};
        let resident_layer=(0..copies).map(|copy|Gate{left:copy,right:copy,..local_gate.clone()}).collect::<Vec<_>>();
        let resident_layers=vec![resident_layer];
        let bind=|transcript:&mut Transcript|transcript.append_bytes(b"toy-statement",b"mainnet-copy-count-single-roster-v1");

        let mut resident_transcript=Transcript::new(b"copy-scale-mainnet-count");
        let (resident,claim)=crate::gkr::prove_with_binding(&input,&resident_layers,&mut resident_transcript,bind).unwrap();
        let reads=Cell::new(0usize);
        let mut streamed_transcript=Transcript::new(b"copy-scale-mainnet-count");
        let (streamed,streamed_claim)=prove(0,copy_bits,0,0,&[0],|_|{
            reads.set(reads.get()+1);
            Ok(vec![Fr::zero()])
        },&mut streamed_transcript,bind,|_copy,sink|{
            sink(Term{row:0,gate:local_gate.clone()})
        },|r,u,v|{
            let mut coefficients=[Fr::zero();4];
            for row in 0..copies{
                let weight=eq_weight_at(r,row)*eq_weight_at(u,row)*eq_weight_at(v,row);
                coefficients[1]-=weight;coefficients[3]+=weight;
            }
            Ok(coefficients)
        }).unwrap();

        let proof_bytes=crate::gkr::encode_proof(&streamed).unwrap().len();
        assert_eq!(streamed.layers.len(),1,"all history copies must produce one GKR layer/proof");
        assert_eq!(streamed.layers[0].rounds.len(),2*copy_bits,"the proof must cover all high copy bits");
        assert_eq!(streamed,resident,"streamed aggregate must equal the resident proof");
        assert_eq!(streamed_claim,claim);
        assert_eq!(streamed_transcript.challenges(),resident_transcript.challenges());
        assert_eq!(streamed_transcript.raw_queries(),resident_transcript.raw_queries());
        assert_eq!(streamed_transcript.bytes_absorbed(),resident_transcript.bytes_absorbed());
        eprintln!("copy-scale copies={copies} load_copy_calls={} proof_bytes={proof_bytes} gkr_rounds={}",reads.get(),streamed.layers[0].rounds.len());
    }

    #[test]
    #[ignore = "manual cross-slot stress for the streamed adjacency relation"]
    fn edge_stream_aggregates_mainnet_scale_adjacent_copies_into_one_gkr_dory_proof() {
        use std::cell::Cell;
        use std::{fs::OpenOptions,io::Write,sync::atomic::{AtomicU64,Ordering}};
        static NEXT:AtomicU64=AtomicU64::new(0);

        let slot_bits=21usize;
        let copies=1usize<<slot_bits;
        let input=(0..copies).flat_map(|slot|[
            Fr::from((slot.wrapping_sub(1)&1) as u64),Fr::from((slot&1) as u64),
        ]).collect::<Vec<_>>();
        let zero=Gate{left:0,right:0,c0:Fr::zero(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()};
        let mut resident_layer=Vec::with_capacity(copies);
        resident_layer.push(zero.clone());
        for source_slot in 1..copies{
            resident_layer.push(Gate{left:source_slot*2,right:(source_slot-1)*2+1,c0:Fr::zero(),
                c1:Fr::one(),c2:-Fr::one(),c3:Fr::zero()});
        }
        let resident_layers=vec![resident_layer];
        let bind=|transcript:&mut Transcript|transcript.append_bytes(b"toy-statement",b"long-cross-slot-adjacency-v1");
        let mut resident_transcript=Transcript::new(b"edge-scale-single-proof");
        let (resident,claim)=crate::gkr::prove_with_binding(&input,&resident_layers,&mut resident_transcript,bind).unwrap();

        let reads=Cell::new(0usize);
        let mut streamed_transcript=Transcript::new(b"edge-scale-single-proof");
        let (streamed,streamed_claim,used_incremental_u,used_incremental_v)=prove_edge_terms(
            1,slot_bits,0,0,&[0],|left,slot,sink|{
                let source_slot=if left{slot}else{slot+1};
                if source_slot==0||source_slot>=copies{return Ok(());}
                sink(EdgeTerm{source_slot,family_row:0,term:Term{row:source_slot,gate:Gate{
                    left:source_slot*2,right:(source_slot-1)*2+1,c0:Fr::zero(),c1:Fr::one(),
                    c2:-Fr::one(),c3:Fr::zero(),
                }}})
            },|slot|{
                reads.set(reads.get()+1);
                Ok(vec![Fr::from((slot.wrapping_sub(1)&1) as u64),Fr::from((slot&1) as u64)])
            },&mut streamed_transcript,bind,|r,u,v|{
                let mut coefficients=[Fr::zero();4];
                for source_slot in 1..copies{
                    let weight=eq_weight_at(r,source_slot)*eq_weight_at(u,source_slot*2)
                        *eq_weight_at(v,(source_slot-1)*2+1);
                    coefficients[1]+=weight;coefficients[2]-=weight;
                }
                Ok(coefficients)
            }).unwrap();

        let proof_bytes=crate::gkr::encode_proof(&streamed).unwrap().len();
        assert_eq!(streamed.layers.len(),1,"all adjacency edges must form one GKR layer/proof");
        assert_eq!(streamed.layers[0].rounds.len(),2*(1+slot_bits));
        assert_eq!(streamed,resident,"streamed edge aggregate must equal the resident adjacency proof");
        assert_eq!(streamed_claim,claim);
        assert_eq!(streamed_transcript.challenges(),resident_transcript.challenges());
        assert_eq!(streamed_transcript.raw_queries(),resident_transcript.raw_queries());
        assert_eq!(streamed_transcript.bytes_absorbed(),resident_transcript.bytes_absorbed());

        let mut verifier_transcript=Transcript::new(b"edge-scale-single-proof");
        let verified_claim=crate::gkr::verify_with_wiring(&[1+slot_bits],copies,&streamed,&mut verifier_transcript,
            |transcript|transcript.append_bytes(b"toy-statement",b"long-cross-slot-adjacency-v1"),|_,r,u,v|{
                let mut coefficients=[Fr::zero();4];
                let row_weights=gkr::eq_weights(r);
                let left_weights=gkr::eq_weights(u);
                let right_weights=gkr::eq_weights(v);
                for source_slot in 1..copies{
                    let weight=row_weights[source_slot]*left_weights[source_slot*2]
                        *right_weights[(source_slot-1)*2+1];
                    coefficients[1]+=weight;coefficients[2]-=weight;
                }
                Ok(coefficients)
            }).unwrap();
        assert_eq!(verified_claim,streamed_claim);
        assert_eq!(verifier_transcript.challenges(),streamed_transcript.challenges());
        assert_eq!(verifier_transcript.raw_queries(),streamed_transcript.raw_queries());
        assert_eq!(verifier_transcript.bytes_absorbed(),streamed_transcript.bytes_absorbed());

        let packed_bits=input.len();
        let mut packed_bytes=vec![0u8;packed_bits.div_ceil(8)];
        for (index,value) in input.iter().enumerate(){if *value==Fr::one(){packed_bytes[index/8]|=1<<(index%8);}}
        let path=std::env::temp_dir().join(format!("nipopow-edge-scale-{}-{}.bin",std::process::id(),NEXT.fetch_add(1,Ordering::Relaxed)));
        let mut file=OpenOptions::new().write(true).create_new(true).open(&path).unwrap();
        file.write_all(&packed_bytes).unwrap();drop(file);
        let setup=crate::pcs::generate_setup(1+slot_bits).unwrap();
        let source=crate::packed::PackedFile::open(&path,1+slot_bits).unwrap();
        let committed=crate::packed::commit(&source,&setup).unwrap();
        let mut opening_transcript=streamed_transcript.clone();
        let opening=crate::packed::open(&committed,&source,&streamed_claim.point,&setup,&mut opening_transcript).unwrap();
        let pcs_proof_bytes=crate::pcs::encode_proof(&opening).unwrap().len();
        let mut pcs_verifier_transcript=verifier_transcript.clone();
        crate::pcs::verify(committed.commitment.clone(),streamed_claim.value,&streamed_claim.point,
            &opening,&setup,&mut pcs_verifier_transcript).unwrap();
        assert_eq!(pcs_verifier_transcript.challenges(),opening_transcript.challenges());
        assert_eq!(pcs_verifier_transcript.raw_queries(),opening_transcript.raw_queries());
        assert_eq!(pcs_verifier_transcript.bytes_absorbed(),opening_transcript.bytes_absorbed());
        drop(source);std::fs::remove_file(&path).unwrap();
        eprintln!("edge-scale copies={copies} load_copy_calls={} gkr_proof_bytes={proof_bytes} dory_proof_bytes={pcs_proof_bytes} gkr_rounds={} incremental_u={used_incremental_u} incremental_v={used_incremental_v}",reads.get(),streamed.layers[0].rounds.len());
    }

    #[test]
    fn tensor_slot_handoff_matches_resident_for_uneven_family_rows() {
        let mut input=Vec::new();
        for value in [7u64,11,13,17]{input.extend([Fr::from(value),Fr::from(value),Fr::from(value+20),Fr::from(value+20)]);}
        let gate=|left,right|Gate{left,right,c0:Fr::zero(),c1:Fr::one(),c2:-Fr::one(),c3:Fr::zero()};
        let mut terms=Vec::new();
        for slot in 0..4{let wire=slot*4;terms.push(Term{row:slot*2,gate:gate(wire,wire+1)});
            terms.push(Term{row:16+slot*4+1,gate:gate(wire+2,wire+3)});}
        let circuit=crate::sparse::Circuit{input_len:16,row_count:32,terms};
        let shape=crate::sparse::validate(&circuit,0).unwrap();
        let mut resident_transcript=Transcript::new(b"tensor-toy-parity");
        let (resident,claim)=crate::sparse::prove_with_binding(&circuit,&input,0,&mut resident_transcript,|t|{
            t.append_bytes(b"toy-statement",b"same");
        }).unwrap();
        let mut tensor_transcript=Transcript::new(b"tensor-toy-parity");
        let (tensor,tensor_claim)=prove(2,2,2,1,&[1,2],|copy|Ok(input[copy*4..(copy+1)*4].to_vec()),&mut tensor_transcript,|t|{
            t.append_bytes(b"toy-statement",b"same");
        },|slot,sink|{
            let wire=0;
            sink(Term{row:0,gate:gate(wire,wire+1)})?;
            sink(Term{row:5,gate:gate(wire+2,wire+3)})
        },|r,u,v|crate::sparse::wiring(&circuit,&shape,r,u,v).map_err(|e|e.to_string())).unwrap();
        assert_eq!(tensor,resident);
        assert_eq!(tensor_claim,claim);
        assert_eq!(tensor_transcript.challenges(),resident_transcript.challenges());
    }

    #[test]
    fn tensor_slot_handoff_preserves_global_left_anchor() {
        let input=vec![Fr::from(2u64),Fr::from(9u64),Fr::from(1u64),Fr::from(5u64)];
        let linear=Gate{left:2,right:0,c0:Fr::zero(),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()};
        let constant=Gate{left:0,right:0,c0:-Fr::one(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()};
        let circuit=crate::sparse::Circuit{input_len:4,row_count:2,terms:vec![
            Term{row:1,gate:linear.clone()},Term{row:1,gate:constant.clone()},
        ]};
        let shape=crate::sparse::validate(&circuit,0).unwrap();
        let mut resident_transcript=Transcript::new(b"tensor-global-anchor");
        let (resident,claim)=crate::sparse::prove_with_binding(&circuit,&input,0,&mut resident_transcript,|t|{
            t.append_bytes(b"toy-statement",b"global-left-zero");
        }).unwrap();
        let mut tensor_transcript=Transcript::new(b"tensor-global-anchor");
        let (tensor,tensor_claim)=prove(1,1,0,0,&[0],|copy|Ok(input[copy*2..(copy+1)*2].to_vec()),&mut tensor_transcript,|t|{
            t.append_bytes(b"toy-statement",b"global-left-zero");
        },|slot,sink|{
            if slot==1{
                sink(Term{row:0,gate:Gate{left:0,right:2,..linear.clone()}})?;
                sink(Term{row:0,gate:Gate{left:2,right:2,..constant.clone()}})?;
            }
            Ok(())
        },|r,u,v|crate::sparse::wiring(&circuit,&shape,r,u,v).map_err(|e|e.to_string())).unwrap();
        assert_eq!(tensor,resident,"global-left anchor must preserve every resident sumcheck message");
        assert_eq!(tensor_claim,claim);
        assert_eq!(tensor_transcript.challenges(),resident_transcript.challenges());
    }

    #[test]
    fn tensor_slot_handoff_preserves_mixed_global_and_slot_local_anchors() {
        let input=vec![Fr::zero(),Fr::zero(),Fr::one(),Fr::one()];
        let circuit=crate::sparse::Circuit{input_len:4,row_count:4,terms:vec![
            Term{row:2,gate:Gate{left:2,right:0,c0:Fr::zero(),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()}},
            Term{row:2,gate:Gate{left:0,right:0,c0:-Fr::one(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}},
            Term{row:3,gate:Gate{left:3,right:2,c0:Fr::zero(),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()}},
            Term{row:3,gate:Gate{left:2,right:2,c0:-Fr::one(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}},
        ]};
        let shape=crate::sparse::validate(&circuit,0).unwrap();
        let bind=|t:&mut Transcript|t.append_bytes(b"toy-statement",b"mixed-anchor-v1");
        let emit=|mark_left:bool,mark_right:bool,slot:usize,sink:&mut dyn FnMut(Term)->Result<(),String>|->Result<(),String>{
            if slot!=1{return Ok(());}
            let width=2;
            let mut global_constant=Gate{left:0,right:0,c0:-Fr::one(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()};
            if !mark_left{global_constant.left=0;}else{global_constant.left=width;}
            if !mark_right{global_constant.right=0;}else{global_constant.right=width;}
            let mut global_right=Gate{left:0,right:0,c0:Fr::zero(),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()};
            global_right.left=0;
            global_right.right=if mark_right{width}else{0};
            sink(Term{row:0,gate:global_right})?;
            sink(Term{row:0,gate:global_constant})?;
            sink(Term{row:1,gate:Gate{left:1,right:0,c0:Fr::zero(),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()}})?;
            sink(Term{row:1,gate:Gate{left:0,right:0,c0:-Fr::one(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}})?;
            Ok(())
        };
        let mut resident_transcript=Transcript::new(b"tensor-mixed-anchors");
        let (resident,claim)=crate::sparse::prove_with_binding(&circuit,&input,0,&mut resident_transcript,bind).unwrap();
        let mut tensor_transcript=Transcript::new(b"tensor-mixed-anchors");
        let load=|copy|Ok(input[copy*2..(copy+1)*2].to_vec());
        let (tensor,tensor_claim)=prove(1,1,1,0,&[1],load,&mut tensor_transcript,|t|{
            t.append_bytes(b"toy-statement",b"mixed-anchor-v1");
        },|slot,sink|emit(true,true,slot,sink),|r,u,v|{
            crate::sparse::wiring(&circuit,&shape,r,u,v).map_err(|e|e.to_string())
        }).unwrap();
        assert_eq!(tensor,resident,"mixed global/slot-local anchor rounds must match resident");
        assert_eq!(tensor_claim,claim);
        assert_eq!(tensor_transcript.challenges(),resident_transcript.challenges());

        for (mark_left,mark_right,label) in [(false,true,"left"),(true,false,"right")] {
            let mut mutant_transcript=Transcript::new(b"tensor-mixed-anchors");
            let mutant=prove(1,1,1,0,&[1],|copy|Ok(input[copy*2..(copy+1)*2].to_vec()),&mut mutant_transcript,|t|{
                t.append_bytes(b"toy-statement",b"mixed-anchor-v1");
            },|slot,sink|emit(mark_left,mark_right,slot,sink),|r,u,v|{
                crate::sparse::wiring(&circuit,&shape,r,u,v).map_err(|e|e.to_string())
            });
            assert!(mutant.is_err(),"moving the {label} global anchor into slot-local zero must fail terminal verification");
        }
    }

    #[test]
    fn edge_tensor_matches_h3_successor_child_and_fixed_fan_in_under_one_dory_commitment() {
        use crate::work_tree_wiring::{Descriptor,Family,Mapping};
        use std::{fs::OpenOptions,io::Write};
        let descriptor=Descriptor::new(3,[0x42;32]).unwrap();
        assert_eq!(descriptor.slots,4);
        let families=vec![
            Family{name:"successor".into(),mapping:Mapping::HeaderSuccessor{lo:1,hi:3},left_wires:vec![0],right_wires:vec![1],constants:None},
            Family{name:"right-child".into(),mapping:Mapping::Child{level:1,branch:1},left_wires:vec![2],right_wires:vec![3],constants:None},
            Family{name:"profile-fan-in".into(),mapping:Mapping::FixedRight{lo:0,hi:2,target:descriptor.profile_node_slot},left_wires:vec![4],right_wires:vec![5],constants:None},
        ];
        let member_row_bits=vec![0usize;families.len()];let mut edge_terms=Vec::new();let mut resident_terms=Vec::new();
        for (family_index,family) in families.iter().enumerate(){
            let stride=family.left_wires.len().next_power_of_two();
            family.emit_terms(&descriptor,|mut term|{
                let source_slot=term.row/stride;let local_row=term.row%stride;
                let full_width=crate::work_tree_layout::WIDTH;
                let left_slot=term.gate.left/full_width;
                let right_slot=term.gate.right/full_width;
                term.gate.left=left_slot*16+term.gate.left%full_width;
                term.gate.right=right_slot*16+term.gate.right%full_width;
                let family_row=(family_index<<0)|local_row;
                term.row=(family_index<<2)|source_slot;
                resident_terms.push(term.clone());edge_terms.push(EdgeTerm{source_slot,family_row,term});Ok(())
            }).unwrap();
        }
        let mut input=(0..64).map(|index|Fr::from(((index/16+index%16)&1) as u64)).collect::<Vec<_>>();
        input[16]=Fr::one();input[1]=Fr::one();   // successor: row 1 -> row 0
        input[32]=Fr::zero();input[17]=Fr::zero(); // successor: row 2 -> row 1
        input[2]=Fr::one();input[16+3]=Fr::one(); // level-1 right child
        input[4]=Fr::zero();input[16+4]=Fr::zero();input[16+5]=Fr::zero(); // fixed-target fan-in
        assert!(input.iter().all(|value|*value==Fr::zero()||*value==Fr::one()));
        let circuit=crate::sparse::Circuit{input_len:64,row_count:16,terms:resident_terms};
        let shape=crate::sparse::validate(&circuit,0).unwrap();
        let domain=b"nipopow-v2-h3-edge-tensor-test-v1";
        let bind=|t:&mut Transcript|t.append_bytes(b"toy-edge-mappings",b"successor-child-fixed");
        let mut resident_transcript=Transcript::new(domain);
        let (resident,resident_claim)=crate::sparse::prove_with_binding(&circuit,&input,0,&mut resident_transcript,bind).unwrap();
        let mut emit_endpoints=|mutate_source_slot:bool,left:bool,slot:usize,sink:&mut dyn FnMut(EdgeTerm)->Result<(),String>|->Result<(),String>{
            for (family_index,family) in families.iter().enumerate(){
                family.emit_endpoint_terms(&descriptor,left,slot,|source_slot,local_row,mut term|{
                    let full_width=crate::work_tree_layout::WIDTH;
                    let left_slot=term.gate.left/full_width;let right_slot=term.gate.right/full_width;
                    term.gate.left=left_slot*16+term.gate.left%full_width;
                    term.gate.right=right_slot*16+term.gate.right%full_width;
                    let source_slot=if mutate_source_slot{(source_slot+1)%descriptor.slots}else{source_slot};
                    sink(EdgeTerm{source_slot,family_row:family_index+local_row,term})
                })?;
            }
            Ok(())
        };
        let mut tensor_transcript=Transcript::new(domain);
        let (tensor,tensor_claim,_,_)=prove_edge_terms(4,2,0,2,&member_row_bits,|left,slot,sink|emit_endpoints(false,left,slot,sink),|copy|Ok(input[copy*16..(copy+1)*16].to_vec()),&mut tensor_transcript,|t|{
            t.append_bytes(b"toy-edge-mappings",b"successor-child-fixed");
        },|r,u,v|crate::sparse::wiring(&circuit,&shape,r,u,v).map_err(|e|e.to_string())).unwrap();
        assert_eq!(crate::gkr::encode_proof(&tensor).unwrap(),crate::gkr::encode_proof(&resident).unwrap());
        assert_eq!(tensor_claim,resident_claim);
        assert_eq!(tensor_transcript.challenges(),resident_transcript.challenges());
        assert_eq!(tensor_transcript.raw_queries(),resident_transcript.raw_queries());
        assert_eq!(tensor_transcript.bytes_absorbed(),resident_transcript.bytes_absorbed());

        let mut mutant_transcript=Transcript::new(domain);
        let mutant=prove_edge_terms(4,2,0,2,&member_row_bits,|left,slot,sink|emit_endpoints(true,left,slot,sink),|copy|Ok(input[copy*16..(copy+1)*16].to_vec()),&mut mutant_transcript,|t|{
            t.append_bytes(b"toy-edge-mappings",b"successor-child-fixed");
        },|r,u,v|crate::sparse::wiring(&circuit,&shape,r,u,v).map_err(|e|e.to_string()));
        assert!(mutant.is_err(),"a consistent wrong-but-in-range source_slot on both endpoint walks must fail the canonical wiring check");

        let bytes=input.chunks(8).map(|chunk|chunk.iter().enumerate().fold(0u8,|acc,(bit,value)|
            acc|((value==&Fr::one()) as u8)<<bit)).collect::<Vec<_>>();
        let stamp=std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
        let path=std::env::temp_dir().join(format!("nipopow-edge-tensor-{}-{stamp}.bin",std::process::id()));
        let mut file=OpenOptions::new().write(true).create_new(true).open(&path).unwrap();file.write_all(&bytes).unwrap();drop(file);
        let source=crate::packed::PackedFile::open(&path,6).unwrap();let setup=crate::pcs::generate_setup(6).unwrap();
        let committed=crate::packed::commit(&source,&setup).unwrap();
        let mut resident_open_transcript=resident_transcript.clone();
        let mut tensor_open_transcript=tensor_transcript.clone();
        let resident_opening=crate::packed::open(&committed,&source,&resident_claim.point,&setup,&mut resident_open_transcript).unwrap();
        let tensor_opening=crate::packed::open(&committed,&source,&tensor_claim.point,&setup,&mut tensor_open_transcript).unwrap();
        let resident_opening_bytes=crate::pcs::encode_proof(&resident_opening).unwrap();
        assert_eq!(crate::pcs::encode_proof(&tensor_opening).unwrap(),resident_opening_bytes);
        assert_eq!(resident_open_transcript.challenges(),tensor_open_transcript.challenges());
        assert_eq!(resident_open_transcript.raw_queries(),tensor_open_transcript.raw_queries());
        assert_eq!(resident_open_transcript.bytes_absorbed(),tensor_open_transcript.bytes_absorbed());
        let decoded=crate::pcs::decode_proof(&resident_opening_bytes,6).unwrap();
        let mut verifier=Transcript::new(domain);
        let verified=crate::gkr::verify_with_wiring(&[6],circuit.row_count,&tensor,&mut verifier,|t|{
            t.append_bytes(b"toy-edge-mappings",b"successor-child-fixed");
        },|_,r,u,v|crate::sparse::wiring(&circuit,&shape,r,u,v).map_err(|e|{
            eprintln!("edge toy verifier wiring r={} u={} v={}: {e}",r.len(),u.len(),v.len());crate::gkr::GkrError::PointDimension
        })).unwrap();
        assert_eq!(verified,tensor_claim);
        crate::pcs::verify(committed.commitment,verified.value,&verified.point,&decoded,&setup,&mut verifier).unwrap();
        drop(source);std::fs::remove_file(path).unwrap();
    }

    #[test]
    fn row_weight_factorization_matches_dense_reference_and_respects_bounds(){
        let copy_bits=21usize;let base_row_bits=2usize;
        let mut point=(0..base_row_bits+copy_bits).map(|i|Fr::from((i as u64+19)*13)).collect::<Vec<_>>();
        point[base_row_bits]=Fr::one();
        for coordinate in &mut point[base_row_bits+1..]{*coordinate=Fr::zero();}
        let members=[base_row_bits];
        let old=TensorRowWeightLookup::new(&point,copy_bits,base_row_bits,&members);
        assert!(old.fallback.is_some(),"21 slot bits must exceed the old 32 MiB owner scale table bound");
        let factor=OneFamilyRowFactor::try_new(&point,copy_bits,base_row_bits,0,&members,old.local_table(base_row_bits))
            .expect("small local table should factor when the owner scale table is too large");
        assert!(matches!(&factor.local_weights,std::borrow::Cow::Owned(_)));
        let full=EqWeightLookup::new(&point);
        let copies=1usize<<copy_bits;
        for copy in [0usize,1,2,3,1usize<<20,copies-1]{
            for row in 0..1usize<<base_row_bits{
                let global=(copy<<base_row_bits)|row;
                let actual=factor.local(row)*factor.copy(copy);
                assert_eq!(actual,full.at(global),"slot={copy} row={row}");
                assert_eq!(actual,old.at(copy,row),"old fallback slot={copy} row={row}");
            }
        }
        assert!(factor.copy(0).is_zero(),"the zero slot scale must stay zero");
        assert_eq!(factor.copy(1),Fr::one(),"the selected slot scale must stay one");

        let cached_point=[Fr::from(3u64),Fr::from(7u64),Fr::from(2u64)];
        let cached=TensorRowWeightLookup::new(&cached_point,1,2,&[2]);
        let cached_factor=OneFamilyRowFactor::try_new(&cached_point,1,2,0,&[2],cached.local_table(2)).unwrap();
        assert!(matches!(&cached_factor.local_weights,std::borrow::Cow::Borrowed(_)),
            "reuse the existing bounded local equality table when the cached lookup has one");
        for copy in 0..2{for row in 0..4{
            assert_eq!(cached_factor.local(row)*cached_factor.copy(copy),cached.at(copy,row));
        }}

        let mixed_point=vec![Fr::from(2u64),Fr::from(5u64),Fr::from(7u64),Fr::from(11u64)];
        let mixed=OneFamilyRowFactor::try_new(&mixed_point,1,2,1,&[2],None);
        assert!(mixed.is_none(),"a family dimension must remain on the reviewed generic path");
        let unequal=OneFamilyRowFactor::try_new(&mixed_point,1,2,0,&[1],None);
        assert!(unequal.is_none(),"unequal member row widths must remain on the reviewed generic path");
        let oversized_point=vec![Fr::zero();22];
        let oversized=OneFamilyRowFactor::try_new(&oversized_point,0,22,0,&[22],None);
        assert!(oversized.is_none(),"checked local-table payload above 64 MiB must be rejected before allocation");
        let overflow_bits=usize::BITS as usize;
        let overflow_point=vec![Fr::zero();overflow_bits];
        let overflow=OneFamilyRowFactor::try_new(&overflow_point,0,overflow_bits,0,&[overflow_bits],None);
        assert!(overflow.is_none(),"local equality length overflow must be rejected before allocation");
        let malformed_local=vec![Fr::zero();3];
        let malformed=OneFamilyRowFactor::try_new(&cached_point,1,2,0,&[2],Some(&malformed_local));
        assert!(malformed.is_none(),"cached local table with the wrong length must be rejected");
    }

    #[test]
    fn factored_message_handoff_matches_dense_global_anchor_reference(){
        let prefixes=[
            vec![],
            vec![Fr::zero(),Fr::one()],
            vec![Fr::one(),Fr::zero(),Fr::one()],
            vec![Fr::from(2u64),Fr::from(5u64),Fr::from(11u64)],
        ];
        let scales=[Fr::zero(),Fr::one(),Fr::from(3u64),Fr::from(9u64)];
        let anchor=Fr::from(37u64);
        for prefix in prefixes{
            let initial_width=1usize<<(prefix.len()+1);
            let handoff_width=1usize<<prefix.len();
            let mut actual_message=[Fr::zero();3];let mut dense_message=[Fr::zero();3];
            let mut actual_handoff_a=Vec::new();let mut dense_handoff_a=Vec::new();
            let mut actual_handoff_b=Vec::new();let mut dense_handoff_b=Vec::new();
            for copy in 0..scales.len(){
                let scale=scales[copy];
                let mut a=(0..initial_width).map(|i|if i%5==0{Fr::zero()}else{Fr::from((i*7+copy+3) as u64)}).collect::<Vec<_>>();
                let mut b=(0..initial_width).map(|i|Fr::from((i*11+copy*3+5) as u64)).collect::<Vec<_>>();
                let mut x=(0..initial_width).map(|i|Fr::from((i*13+copy*5+7) as u64)).collect::<Vec<_>>();
                let mut dense_a=a.iter().map(|value|scale * *value).collect::<Vec<_>>();
                let mut dense_b=b.iter().map(|value|scale * *value).collect::<Vec<_>>();
                for coordinate in &prefix{
                    gkr::fold(&mut a,*coordinate);gkr::fold(&mut b,*coordinate);gkr::fold(&mut x,*coordinate);
                    gkr::fold(&mut dense_a,*coordinate);gkr::fold(&mut dense_b,*coordinate);
                }
                OneFamilyRowFactor::add_scaled_message(&mut actual_message,&a,&b,&x,scale);
                for (sum,value) in dense_message.iter_mut().zip(gkr::quadratic_message(&dense_a,&dense_b,&x)){*sum+=value;}

                let mut handoff_a=(0..handoff_width).map(|i|Fr::from((i*17+copy+1) as u64)).collect::<Vec<_>>();
                let mut handoff_b=(0..handoff_width).map(|i|Fr::from((i*19+copy*2+3) as u64)).collect::<Vec<_>>();
                let mut full_a=handoff_a.iter().map(|value|scale * *value).collect::<Vec<_>>();
                let mut full_b=handoff_b.iter().map(|value|scale * *value).collect::<Vec<_>>();
                let global=if copy==0{anchor}else{Fr::zero()};
                full_b[0]+=global;
                for coordinate in &prefix{
                    gkr::fold(&mut handoff_a,*coordinate);gkr::fold(&mut handoff_b,*coordinate);
                    gkr::fold(&mut full_a,*coordinate);gkr::fold(&mut full_b,*coordinate);
                }
                actual_handoff_a.push(OneFamilyRowFactor::handoff(handoff_a[0],scale,Fr::zero()));
                actual_handoff_b.push(OneFamilyRowFactor::handoff(handoff_b[0],scale,
                    OneFamilyRowFactor::anchor_after_prefix(global,&prefix)));
                dense_handoff_a.push(full_a[0]);dense_handoff_b.push(full_b[0]);
            }
            assert_eq!(actual_message,dense_message,"factored owner scalar must match dense scaled A/B messages");
            assert_eq!(actual_handoff_a,dense_handoff_a,"A handoff must scale local rows by owner");
            assert_eq!(actual_handoff_b,dense_handoff_b,"the global anchor must be injected once after local folding");

            let width=1usize<<(prefix.len()+1);
            let mut anchor_a=vec![Fr::zero();width];let mut anchor_b=vec![Fr::zero();width];
            let mut anchor_x=(0..width).map(|i|Fr::from((i*23+1) as u64)).collect::<Vec<_>>();
            anchor_b[0]=anchor;
            for coordinate in &prefix{
                gkr::fold(&mut anchor_a,*coordinate);gkr::fold(&mut anchor_b,*coordinate);gkr::fold(&mut anchor_x,*coordinate);
            }
            let mut actual_anchor=[Fr::zero();3];
            OneFamilyRowFactor::add_anchor_message(&mut actual_anchor,anchor,&prefix);
            assert_eq!(actual_anchor.as_slice(),gkr::quadratic_message(&anchor_a,&anchor_b,&anchor_x).as_slice(),
                "global-left/global-right anchor polynomial after prefix {prefix:?}");
        }
    }

    #[test]
    fn cache_zero_factored_proof_matches_resident_expansion_and_rejects_bad_residual(){
        use std::cell::Cell;
        const INPUT_BITS:usize=3;const COPY_BITS:usize=2;const BASE_ROW_BITS:usize=2;
        const WIDTH:usize=1<<INPUT_BITS;const COPIES:usize=1<<COPY_BITS;const ROWS:usize=1<<(BASE_ROW_BITS+COPY_BITS);
        let input=(0..WIDTH*COPIES).map(|index|Fr::from((index*29+17) as u64)).collect::<Vec<_>>();
        let mut per_copy=vec![Vec::<Term>::new();COPIES];
        for copy in 0..COPIES{for row in 0..1usize<<BASE_ROW_BITS{
            let left=(copy*3+row)%WIDTH;let right=(copy*5+row*2+1)%WIDTH;
            let c1=Fr::from((copy+2) as u64);let c2=Fr::from((row+3) as u64);let c3=Fr::from((copy+row+5) as u64);
            let target=Fr::from((copy*7+row+13) as u64);
            let value=c1*input[copy*WIDTH+left]+c2*input[copy*WIDTH+right]
                +c3*input[copy*WIDTH+left]*input[copy*WIDTH+right];
            per_copy[copy].push(Term{row,gate:Gate{left,right,c0:target-value,c1,c2,c3}});
            per_copy[copy].push(Term{row,gate:Gate{left:0,right:0,c0:-target,c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}});
            if copy%2==1&&row==2{
                let extra_left=(left+2)%WIDTH;let extra_right=(right+3)%WIDTH;
                let e1=Fr::from((copy+11) as u64);let e2=Fr::from((row+7) as u64);let e3=Fr::from(19u64);
                let extra_target=Fr::from((copy+row+31) as u64);
                let extra_value=e1*input[copy*WIDTH+extra_left]+e2*input[copy*WIDTH+extra_right]
                    +e3*input[copy*WIDTH+extra_left]*input[copy*WIDTH+extra_right];
                per_copy[copy].push(Term{row,gate:Gate{left:extra_left,right:extra_right,c0:extra_target-extra_value,c1:e1,c2:e2,c3:e3}});
                per_copy[copy].push(Term{row,gate:Gate{left:0,right:0,c0:-extra_target,c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}});
            }
            if row==0{
                let anchor_right=(copy+1)%WIDTH;let anchor_c0=Fr::from((copy+2) as u64);let anchor_c2=Fr::from(7u64);
                let left_anchor_value=anchor_c0+anchor_c2*input[copy*WIDTH+anchor_right];
                per_copy[copy].push(Term{row,gate:Gate{left:WIDTH,right:anchor_right,c0:anchor_c0,c1:Fr::zero(),c2:anchor_c2,c3:Fr::zero()}});
                per_copy[copy].push(Term{row,gate:Gate{left:0,right:0,c0:-left_anchor_value,c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}});

                let anchor_left=(copy+3)%WIDTH;let right_anchor_c0=Fr::from((copy+5) as u64);let right_anchor_c1=Fr::from(11u64);
                let right_anchor_value=right_anchor_c0+right_anchor_c1*input[copy*WIDTH+anchor_left];
                per_copy[copy].push(Term{row,gate:Gate{left:anchor_left,right:WIDTH,c0:right_anchor_c0,c1:right_anchor_c1,c2:Fr::zero(),c3:Fr::zero()}});
                per_copy[copy].push(Term{row,gate:Gate{left:0,right:0,c0:-right_anchor_value,c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}});
            }
        }}
        let mut expanded=Vec::new();
        for copy in 0..COPIES{for term in &per_copy[copy]{
            let mut gate=term.gate.clone();
            gate.left=if gate.left==WIDTH{0}else{copy*WIDTH+gate.left};
            gate.right=if gate.right==WIDTH{0}else{copy*WIDTH+gate.right};
            expanded.push(Term{row:(copy<<BASE_ROW_BITS)|term.row,gate});
        }}
        let circuit=crate::sparse::Circuit{input_len:input.len(),row_count:ROWS,terms:expanded};
        let shape=crate::sparse::validate(&circuit,0).unwrap();
        let bind=|transcript:&mut Transcript|transcript.append_bytes(b"toy-statement",b"one-family-row-factor-v1");
        let domain=b"one-family-row-factor-proof-v1";
        let mut resident_transcript=Transcript::new(domain);
        let (resident,resident_claim)=crate::sparse::prove_with_binding(&circuit,&input,0,&mut resident_transcript,bind).unwrap();
        let compare_transcripts=|left:&Transcript,right:&Transcript|{
            assert_eq!(left.challenges(),right.challenges());assert_eq!(left.raw_queries(),right.raw_queries());
            assert_eq!(left.bytes_absorbed(),right.bytes_absorbed());
            let mut left_next=left.clone();let mut right_next=right.clone();
            assert_eq!(left_next.challenge_scalar(b"after-row-factor"),right_next.challenge_scalar(b"after-row-factor"));
        };
        let emit=|copy:usize,sink:&mut dyn FnMut(Term)->Result<(),String>|{
            for term in &per_copy[copy]{sink(term.clone())?;}Ok(())
        };
        let load=|copy:usize|Ok(input[copy*WIDTH..(copy+1)*WIDTH].to_vec());
        let mut cached_transcript=Transcript::new(domain);
        let (cached,cached_claim)=prove(INPUT_BITS,COPY_BITS,BASE_ROW_BITS,0,&[BASE_ROW_BITS],load,&mut cached_transcript,bind,
            emit,|r,u,v|crate::sparse::wiring(&circuit,&shape,r,u,v).map_err(|error|error.to_string())).unwrap();
        let mut factor_transcript=Transcript::new(domain);
        let (factored,factored_claim)=prove_with_cache_budget_for_test(INPUT_BITS,COPY_BITS,BASE_ROW_BITS,0,&[BASE_ROW_BITS],Some(0),
            load,&mut factor_transcript,bind,emit,
            |r,u,v|crate::sparse::wiring(&circuit,&shape,r,u,v).map_err(|error|error.to_string())).unwrap();
        let resident_bytes=crate::gkr::encode_proof(&resident).unwrap();
        assert_eq!(crate::gkr::encode_proof(&cached).unwrap(),resident_bytes,"default cached branch must preserve proof bytes");
        assert_eq!(crate::gkr::encode_proof(&factored).unwrap(),resident_bytes,"factored fallback must preserve proof bytes");
        assert_eq!(cached_claim,resident_claim);assert_eq!(factored_claim,resident_claim);
        compare_transcripts(&cached_transcript,&resident_transcript);compare_transcripts(&factor_transcript,&resident_transcript);
        assert_eq!(crate::gkr::mle(&input,&factored_claim.point).unwrap(),factored_claim.value);
        let mut verifier_transcript=Transcript::new(domain);
        let verified=crate::gkr::verify_with_wiring(&[INPUT_BITS+COPY_BITS],ROWS,&factored,&mut verifier_transcript,bind,
            |_,r,u,v|crate::sparse::wiring(&circuit,&shape,r,u,v)).unwrap();
        assert_eq!(verified,factored_claim);compare_transcripts(&verifier_transcript,&factor_transcript);

        let mut bad_terms=per_copy.clone();bad_terms[1][0].gate.c0+=Fr::one();
        let bind_reached=Cell::new(false);let mut bad_transcript=Transcript::new(domain);
        let bad=prove_with_cache_budget_for_test(INPUT_BITS,COPY_BITS,BASE_ROW_BITS,0,&[BASE_ROW_BITS],Some(0),
            |copy|Ok(input[copy*WIDTH..(copy+1)*WIDTH].to_vec()),&mut bad_transcript,|_|bind_reached.set(true),
            |copy,sink|{for term in &bad_terms[copy]{sink(term.clone())?;}Ok(())},
            |_,_,_|Err("wiring must not be reached before residual validation".into()));
        assert_eq!(bad.unwrap_err(),GkrError::NonzeroOutput.to_string());
        assert!(!bind_reached.get(),"invalid row residual must reject before transcript challenges and factor construction");
        assert_eq!(bad_transcript.challenges(),0);assert_eq!(bad_transcript.raw_queries(),0);
    }
}

#[cfg(test)]
mod fixed_v_aggregation_tests{
    use super::*;
    use crate::gkr::Gate;
    use std::cell::Cell;

    fn sample_circuit()->crate::sparse::Circuit{
        // Genuine constraints: x[1]^2=4 and x[3]=x[5]. No cancelling terms.
        crate::sparse::Circuit{input_len:8,row_count:4,terms:vec![
            Term{row:0,gate:gkr::Gate{left:1,right:1,c0:-Fr::from(4u64),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::one()}},
            Term{row:2,gate:gkr::Gate{left:3,right:5,c0:Fr::zero(),c1:Fr::one(),c2:-Fr::one(),c3:Fr::zero()}},
        ]}
    }

    fn compare_transcripts(left:&Transcript,right:&Transcript){
        assert_eq!(left.challenges(),right.challenges());assert_eq!(left.raw_queries(),right.raw_queries());
        assert_eq!(left.bytes_absorbed(),right.bytes_absorbed());
        let mut left=left.clone();let mut right=right.clone();
        assert_eq!(left.challenge_scalar(b"fixed-v-continuation"),right.challenge_scalar(b"fixed-v-continuation"));
    }

    #[test]
    fn fixed_core_template_matches_generic_proofs_and_fails_closed(){
        let circuit=sample_circuit();let template=FixedCoreVTemplate::try_new(&circuit,3,2,2).unwrap();
        let shape=crate::sparse::validate(&circuit,2).unwrap();
        let input=(0..4u64).flat_map(|owner|[
            Fr::from(owner+11),if owner%2==0{Fr::from(2u64)}else{-Fr::from(2u64)},
            Fr::from(17*owner+7),Fr::from(3*owner+1),Fr::from(19*owner+5),
            Fr::from(3*owner+1),Fr::from(23*owner+2),Fr::from(31*owner+4),
        ]).collect::<Vec<_>>();
        let mut expanded_terms=Vec::new();
        for owner in 0..4{for term in &circuit.terms{
            let mut gate=term.gate.clone();gate.left+=owner*8;gate.right+=owner*8;
            expanded_terms.push(Term{row:(owner<<2)|term.row,gate});
        }}
        let expanded=crate::sparse::Circuit{input_len:32,row_count:16,terms:expanded_terms};
        let bind=|transcript:&mut Transcript|transcript.append_bytes(b"fixed-core-v-statement",b"single immutable core across owners");
        let wiring=|r:&[Fr],u:&[Fr],v:&[Fr]|crate::sparse::wiring(&circuit,&shape,r,u,v).map_err(|error|error.to_string());
        let load=|owner:usize|Ok(input[owner*8..(owner+1)*8].to_vec());
        let emit=|_owner:usize,sink:&mut dyn FnMut(Term)->Result<(),String>|{for term in &circuit.terms{sink(term.clone())?;}Ok(())};
        let mut resident_transcript=Transcript::new(b"fixed-core-v-differential");
        let (resident,resident_claim)=crate::sparse::prove_with_binding(&expanded,&input,0,&mut resident_transcript,bind).unwrap();
        let mut cached_transcript=Transcript::new(b"fixed-core-v-differential");
        let (cached,cached_claim)=prove_with_cache_budget_for_test(3,2,2,0,&[2],None,load,
            &mut cached_transcript,bind,emit,wiring).unwrap();
        let mut fallback_transcript=Transcript::new(b"fixed-core-v-differential");
        let (fallback,fallback_claim)=prove_with_cache_budget_for_test(3,2,2,0,&[2],Some(0),load,
            &mut fallback_transcript,bind,emit,wiring).unwrap();
        let mut fixed_transcript=Transcript::new(b"fixed-core-v-differential");
        let fixed_loads=Cell::new(0usize);
        let (fixed,fixed_claim,stats)=prove_fixed_core_v_with_cache_budget_for_test(&template,Some(0),
            |owner|{fixed_loads.set(fixed_loads.get()+1);load(owner)},
            &mut fixed_transcript,bind,wiring).unwrap();
        let mut default_transcript=Transcript::new(b"fixed-core-v-differential");
        let (default,default_claim,default_stats)=prove_fixed_core_v(&template,load,&mut default_transcript,bind,wiring).unwrap();
        let resident_bytes=crate::gkr::encode_proof(&resident).unwrap();
        assert_eq!(crate::gkr::encode_proof(&cached).unwrap(),resident_bytes);
        assert_eq!(crate::gkr::encode_proof(&fallback).unwrap(),resident_bytes);
        assert_eq!(crate::gkr::encode_proof(&fixed).unwrap(),resident_bytes);
        assert_eq!(crate::gkr::encode_proof(&default).unwrap(),resident_bytes);
        assert_eq!(cached_claim,resident_claim);assert_eq!(fallback_claim,resident_claim);assert_eq!(fixed_claim,resident_claim);
        assert_eq!(default_claim,resident_claim);
        compare_transcripts(&cached_transcript,&resident_transcript);compare_transcripts(&fallback_transcript,&resident_transcript);
        compare_transcripts(&fixed_transcript,&resident_transcript);
        compare_transcripts(&default_transcript,&resident_transcript);
        assert_eq!(stats.common_v_template_callbacks,circuit.terms.len());
        assert_eq!(stats.streamed_term_callbacks,(3+3)*4*circuit.terms.len());
        assert_eq!(fixed_loads.get(),(3+6)*4);
        assert_eq!(default_stats.common_v_template_callbacks,0,"default cached V route must stay unchanged");
        let workspace=template.reserve_workspace().unwrap();
        assert_eq!(stats.common_state_peak_capacity_bytes,workspace.capacity_bytes);
        assert_eq!(default_stats.common_state_peak_capacity_bytes,workspace.capacity_bytes,"report reserved capacity even when the old cache is selected");
        assert!(stats.common_state_peak_capacity_bytes>0&&stats.common_state_peak_capacity_bytes<=MAX_FIXED_V_COMMON_STATE_BYTES);
        assert_eq!(gkr::mle(&input,&fixed_claim.point).unwrap(),fixed_claim.value);
        for (candidate,claim,producer) in [(&fixed,&fixed_claim,&fixed_transcript),(&default,&default_claim,&default_transcript)]{
            let bytes=gkr::encode_proof(candidate).unwrap();let decoded=gkr::decode_dimensions(&[5],&bytes).unwrap();
            assert_eq!(&decoded,candidate);
            let mut verifier=Transcript::new(b"fixed-core-v-differential");
            let verified=gkr::verify_with_wiring(&[5],16,&decoded,&mut verifier,bind,
                |_,r,u,v|crate::sparse::wiring(&circuit,&shape,r,u,v)).unwrap();
            assert_eq!(&verified,claim);compare_transcripts(&verifier,producer);
        }

        check_arbitrary_field_rounds_and_handoff();

        let invalid_wire=GkrError::InvalidWireIndex.to_string();
        let mut unsorted=circuit.clone();unsorted.terms.swap(0,1);
        reject_before_callbacks(&unsorted,3,2,2,"fixed V rows are not in canonical nondecreasing order");
        for (left,value) in [(true,8usize),(false,8),(true,9),(false,9)]{
            let mut bad=circuit.clone();
            if left{bad.terms[0].gate.left=value}else{bad.terms[0].gate.right=value}
            reject_before_callbacks(&bad,3,2,2,&invalid_wire);
        }
        // Reject even anchors whose corresponding coefficients are inactive.
        for left in [true,false]{let mut bad=circuit.clone();
            if left{bad.terms[0].gate.left=8;bad.terms[0].gate.c1=Fr::zero();bad.terms[0].gate.c3=Fr::zero();}
            else{bad.terms[0].gate.right=8;bad.terms[0].gate.c2=Fr::zero();bad.terms[0].gate.c3=Fr::zero();}
            reject_before_callbacks(&bad,3,2,2,&invalid_wire);
        }
        let mut bad_row=circuit.clone();bad_row.terms[0].row=4;
        reject_before_callbacks(&bad_row,3,2,2,&invalid_wire);
        let mut bad_width=circuit.clone();bad_width.input_len=7;
        reject_before_callbacks(&bad_width,3,2,2,&GkrError::InvalidInputWidth.to_string());
        let mut bad_rows=circuit.clone();bad_rows.row_count=3;
        reject_before_callbacks(&bad_rows,3,2,2,&GkrError::InvalidLayerWidth.to_string());
        reject_before_callbacks(&circuit,2,2,2,&GkrError::InvalidInputWidth.to_string());
        reject_before_callbacks(&circuit,3,2,1,&GkrError::InvalidInputWidth.to_string());
        reject_before_callbacks(&circuit,3,usize::MAX,2,"fixed V owner count overflow");
        reject_before_callbacks(&circuit,usize::MAX,2,2,"fixed V input width overflow");
        reject_before_callbacks(&circuit,3,2,usize::MAX,"fixed V row count overflow");
        reject_before_callbacks(&circuit,3,22,2,"fixed V input dimensions exceed sparse verifier bound");
        let row_dimensions=crate::sparse::Circuit{input_len:2,row_count:4,terms:Vec::new()};
        reject_before_callbacks(&row_dimensions,1,23,2,"fixed V row dimensions exceed sparse verifier bound");
        let oversized=crate::sparse::Circuit{input_len:1<<19,row_count:2,terms:Vec::new()};
        reject_before_callbacks(&oversized,19,0,1,"fixed V common-state cap exceeded");
        let too_many=crate::sparse::Circuit{input_len:8,row_count:4,terms:vec![circuit.terms[0].clone();(1<<20)+1]};
        reject_before_callbacks(&too_many,3,2,2,&GkrError::RepeatedSizeLimit.to_string());drop(too_many);

        let mut residual=circuit.clone();residual.terms[0].gate.c0+=Fr::one();
        let residual_template=FixedCoreVTemplate::try_new(&residual,3,2,2).unwrap();
        let bind_reached=Cell::new(false);let mut bad_transcript=Transcript::new(b"fixed-core-v-differential");
        let load_calls=Cell::new(0usize);
        let rejected=prove_fixed_core_v_with_cache_budget_for_test(&residual_template,Some(0),
            |owner|{load_calls.set(load_calls.get()+1);Ok(input[owner*8..(owner+1)*8].to_vec())},
            &mut bad_transcript,|_|bind_reached.set(true),wiring);
        assert_eq!(rejected.err().unwrap(),GkrError::NonzeroOutput.to_string());
        assert!(load_calls.get()>0);assert!(!bind_reached.get());
        assert_eq!(bad_transcript.challenges(),0);assert_eq!(bad_transcript.raw_queries(),0);
        let mut wrong_width=Transcript::new(b"fixed-core-v-differential");let binds=Cell::new(0usize);
        let rejected=prove_fixed_core_v_with_cache_budget_for_test(&template,Some(0),|_|Ok(vec![Fr::zero();7]),
            &mut wrong_width,|_|binds.set(binds.get()+1),wiring);
        assert_eq!(rejected.err().unwrap(),GkrError::InvalidInputWidth.to_string());
        assert_eq!(binds.get(),0);assert_eq!(wrong_width.challenges(),0);assert_eq!(wrong_width.raw_queries(),0);
    }

    fn reject_before_callbacks(circuit:&crate::sparse::Circuit,input_bits:usize,owner_bits:usize,row_bits:usize,expected:&str){
        let loads=Cell::new(0usize);let binds=Cell::new(0usize);let wiring=Cell::new(0usize);
        let mut transcript=Transcript::new(b"fixed-v-malformed-constructor");
        let result=FixedCoreVTemplate::try_new(circuit,input_bits,owner_bits,row_bits).and_then(|template|
            prove_fixed_core_v_with_cache_budget_for_test(&template,Some(0),
                |_|{loads.set(loads.get()+1);Err("loader must not run".into())},&mut transcript,
                |_|binds.set(binds.get()+1),|_,_,_|{wiring.set(wiring.get()+1);Err("wiring must not run".into())}));
        assert_eq!(result.err().unwrap(),expected);
        assert_eq!((loads.get(),binds.get(),wiring.get(),transcript.challenges(),transcript.raw_queries()),(0,0,0,0,0));
    }

    fn check_arbitrary_field_rounds_and_handoff(){
        use ark_ff::Field;
        let third=Fr::from(3u64).inverse().unwrap();
        let points=[
            (vec![Fr::from(2u64),Fr::from(5u64)],vec![Fr::from(7u64),Fr::from(11u64)]),
            (vec![-Fr::one()],vec![Fr::from(2u64)*third]), // k=[2/3,-2/3], sum(k)=0
            (vec![Fr::zero()],vec![Fr::one()]), // every k is zero
            (vec![Fr::one(),Fr::zero()],vec![Fr::one(),Fr::zero()]),
        ];
        let mut missing_u_detected=0usize;let mut bad_d_detected=0usize;let mut collapsed_x_detected=0usize;
        let mut individual_x_detected=[false;4];
        for (case,(r_owner,u_owner)) in points.iter().enumerate(){for bits in [2usize,3]{
            let owners=1usize<<r_owner.len();let width=1usize<<bits;
            let r_weights=gkr::eq_weights(r_owner);let u_weights=gkr::eq_weights(u_owner);
            let scales=(0..owners).map(|owner|r_weights[owner]*u_weights[owner]).collect::<Vec<_>>();
            let sum_scale=scales.iter().copied().fold(Fr::zero(),|a,b|a+b);
            if case==1{assert!(sum_scale.is_zero());assert!(scales.iter().any(|s|!s.is_zero()));}
            if case==2{assert!(scales.iter().all(|s|s.is_zero()));}
            let mut c=(0..width).map(|i|Fr::from((i*i*7+i*3+2) as u64)).collect::<Vec<_>>();
            let mut d=(0..width).map(|i|Fr::from((i*i*i*11+i*5+3) as u64)).collect::<Vec<_>>();
            let mut owner_x=(0..owners).map(|owner|(0..width)
                .map(|i|Fr::from((owner*owner*13+i*i*(owner+2)*17+i*3+9) as u64)).collect::<Vec<_>>()).collect::<Vec<_>>();
            let mut aggregate_x=vec![Fr::zero();width];
            for owner in 0..owners{for i in 0..width{aggregate_x[i]+=scales[owner]*owner_x[owner][i];}}
            for round in 0..bits{
                let mut dense=[Fr::zero();3];
                for owner in 0..owners{
                    let ca=c.iter().map(|value|scales[owner]*value).collect::<Vec<_>>();
                    let da=d.iter().map(|value|scales[owner]*value).collect::<Vec<_>>();
                    for (sum,value) in dense.iter_mut().zip(gkr::quadratic_message(&ca,&da,&owner_x[owner])){*sum+=value;}
                }
                assert_eq!(scaled_common_quadratic_message(&c,&d,&aggregate_x,sum_scale),dense,"case {case}, local round {round}");
                let mut wrong_x=vec![Fr::zero();c.len()];
                for owner in 0..owners{for i in 0..c.len(){wrong_x[i]+=r_weights[owner]*owner_x[owner][i];}}
                let wrong_sum=r_weights.iter().copied().fold(Fr::zero(),|a,b|a+b);
                missing_u_detected+=usize::from(scaled_common_quadratic_message(&c,&d,&wrong_x,wrong_sum)!=dense);
                bad_d_detected+=usize::from(scaled_common_quadratic_message(&c,&d,&aggregate_x,sum_scale+Fr::one())!=dense);
                let coordinate=if round==0{Fr::from(5u64)}else{Fr::from(7u64)};
                gkr::fold(&mut c,coordinate);gkr::fold(&mut d,coordinate);gkr::fold(&mut aggregate_x,coordinate);
                for values in &mut owner_x{gkr::fold(values,coordinate);}
                let expected_x=(0..owners).fold(Fr::zero(),|sum,owner|sum+scales[owner]*owner_x[owner][0]);
                assert_eq!(aggregate_x[0],expected_x,"aggregate commutes with every local fold");
            }
            let high_c=scales.iter().map(|scale|*scale*c[0]).collect::<Vec<_>>();
            let high_d=scales.iter().map(|scale|*scale*d[0]).collect::<Vec<_>>();
            let high_x=owner_x.iter().map(|values|values[0]).collect::<Vec<_>>();
            for owner in 0..owners{
                assert_eq!(high_c[owner],scales[owner]*c[0]);assert_eq!(high_d[owner],scales[owner]*d[0]);
                assert_eq!(high_x[owner],owner_x[owner][0]);
                let mut mutant=high_x.clone();mutant[owner]+=Fr::one();
                let expected=gkr::quadratic_message(&high_c,&high_d,&high_x);
                let mutated=gkr::quadratic_message(&high_c,&high_d,&mutant);
                let low=owner&!1usize;
                if !high_c[low].is_zero()||!high_c[low+1].is_zero(){
                    assert_ne!(mutated,expected,"owner {owner}'s isolated high-X change must alter the actual high-round message");
                    individual_x_detected[owner]=true;
                }else{
                    assert_eq!(mutated,expected,"a pair with both A coefficients zero is algebraically inactive");
                }
            }
            let collapsed=vec![aggregate_x[0];owners];
            collapsed_x_detected+=usize::from(gkr::quadratic_message(&high_c,&high_d,&collapsed)
                !=gkr::quadratic_message(&high_c,&high_d,&high_x));
        }}
        assert!(missing_u_detected>0&&bad_d_detected>0&&collapsed_x_detected>0,"all isolated algebra mutants must be falsified");
        assert!(individual_x_detected.iter().all(|seen|*seen),"every individual owner's high-X mutant must be detected with nonzero weights");
    }

    fn boolean_fixed_core()->crate::sparse::Circuit{
        crate::sparse::Circuit{input_len:8,row_count:4,terms:vec![
            Term{row:0,gate:Gate{left:1,right:1,c0:Fr::zero(),c1:-Fr::from(3u64),c2:Fr::zero(),c3:Fr::from(3u64)}},
            Term{row:2,gate:Gate{left:3,right:5,c0:Fr::zero(),c1:Fr::from(3u64),c2:-Fr::from(3u64),c3:Fr::zero()}},
        ]}
    }

    fn boolean_owner_inputs(non_boolean_owner:Option<usize>)->Vec<Vec<Fr>>{
        (0..4).map(|owner|{
            let bit=Fr::from((owner&1) as u64);let mut input=vec![Fr::zero();8];
            input[1]=bit;input[3]=bit;input[5]=bit;
            if non_boolean_owner==Some(owner){input[7]=Fr::from(2u64);}else{input[7]=Fr::from(((owner>>1)&1) as u64);}
            input
        }).collect()
    }

    #[test]
    fn fixed_u_tables_match_every_generic_term_with_general_coefficients(){
        let circuit=crate::sparse::Circuit{input_len:8,row_count:4,terms:vec![
            Term{row:0,gate:Gate{left:1,right:6,c0:Fr::from(7u64),c1:-Fr::from(3u64),c2:Fr::from(5u64),c3:Fr::from(3u64)}},
            Term{row:2,gate:Gate{left:5,right:7,c0:-Fr::from(11u64),c1:Fr::from(13u64),c2:-Fr::from(4u64),c3:Fr::from(2u64)}},
            Term{row:3,gate:Gate{left:2,right:4,c0:Fr::from(17u64),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}},
        ]};
        let template=FixedCoreVTemplate::try_new(&circuit,3,1,2).unwrap();
        let row_weights=(0..4).map(|row|Fr::from((row*19+7) as u64)).collect::<Vec<_>>();
        let workspace=FixedCoreUWorkspace::try_new(&template,&row_weights,0,MAX_FIXED_V_COMMON_STATE_BYTES).unwrap();
        assert_eq!(workspace.descriptors.len(),2);
        let input=[Fr::zero(),Fr::one(),Fr::zero(),Fr::one(),Fr::zero(),Fr::zero(),Fr::one(),Fr::one()];
        let (actual_a,actual_b)=workspace.build_boolean(&circuit.terms,&row_weights,&input).unwrap();
        let mut expected_a=vec![Fr::zero();8];let mut expected_b=vec![Fr::zero();8];
        for term in &circuit.terms{
            let gate=&term.gate;let weight=row_weights[term.row];let right=input[gate.right];
            expected_a[gate.left]+=weight*(gate.c1+gate.c3*right);
            expected_b[gate.left]+=weight*(gate.c0+gate.c2*right);
        }
        assert_eq!(actual_a,expected_a);assert_eq!(actual_b,expected_b);
        let mut non_boolean=input;non_boolean[0]=Fr::from(2u64);
        assert!(workspace.build_boolean(&circuit.terms,&row_weights,&non_boolean).is_none(),
            "the dispatch guard covers coordinates unused by every descriptor");
    }

    #[test]
    fn fixed_u_descriptor_bounds_and_combined_capacity_fail_closed(){
        let mut term=Term{row:0,gate:Gate{left:0,right:1,c0:Fr::zero(),c1:Fr::zero(),c2:Fr::one(),c3:Fr::zero()}};
        assert!(FixedUDescriptor::try_new(u32::MAX as usize+1,&term,8,4).is_none());
        term.row=u32::MAX as usize+1;assert!(FixedUDescriptor::try_new(0,&term,8,term.row+1).is_none());
        term.row=0;term.gate.left=u16::MAX as usize+1;
        assert!(FixedUDescriptor::try_new(0,&term,u16::MAX as usize+2,4).is_none());
        term.gate.left=0;term.gate.right=u16::MAX as usize+1;
        assert!(FixedUDescriptor::try_new(0,&term,u16::MAX as usize+2,4).is_none());

        let circuit=boolean_fixed_core();let template=FixedCoreVTemplate::try_new(&circuit,3,2,2).unwrap();
        let row_weights=(0..4).map(|row|Fr::from((row+2) as u64)).collect::<Vec<_>>();
        let admitted=FixedCoreUWorkspace::try_new(&template,&row_weights,0,MAX_FIXED_V_COMMON_STATE_BYTES).unwrap();
        let actual_u_bytes=(admitted.a0.capacity()+admitted.b0.capacity())*std::mem::size_of::<Fr>()
            +admitted.descriptors.capacity()*std::mem::size_of::<FixedUDescriptor>()
            +std::mem::size_of::<FixedCoreUWorkspace>();
        assert_eq!(admitted.capacity_bytes,actual_u_bytes,"count the entire struct, including scalar metadata");
        let actual_v_bytes=template.reserve_workspace().unwrap().capacity_bytes;
        let exact_budget=actual_u_bytes+actual_v_bytes;
        assert!(FixedCoreUWorkspace::try_new(&template,&row_weights,actual_v_bytes,exact_budget).is_some());
        assert!(FixedCoreUWorkspace::try_new(&template,&row_weights,actual_v_bytes,exact_budget-1).is_none(),
            "independently computed actual U+V capacity must reject a budget one byte below admission");
        assert!(FixedCoreUWorkspace::try_new(&template,&row_weights,
            MAX_FIXED_V_COMMON_STATE_BYTES-actual_u_bytes+1,MAX_FIXED_V_COMMON_STATE_BYTES).is_none(),
            "combined fixed-V and reusable-U state cannot exceed the shared ceiling");
        assert!(FixedCoreUWorkspace::try_new(&template,&row_weights,
            MAX_FIXED_V_COMMON_STATE_BYTES-actual_u_bytes+1,usize::MAX).is_none(),
            "a test override cannot raise the production common-state ceiling");
        assert!(FixedCoreUWorkspace::try_new(&template,&row_weights,usize::MAX,usize::MAX).is_none(),
            "combined byte arithmetic must reject overflow");
        assert_eq!(std::mem::size_of::<FixedUDescriptor>(),FIXED_U_DESCRIPTOR_BYTES);
    }

    #[test]
    fn fixed_uv_proof_matches_generic_and_dispatches_mixed_owner_fallback(){
        let circuit=boolean_fixed_core();let template=FixedCoreVTemplate::try_new(&circuit,3,2,2).unwrap();
        let shape=crate::sparse::validate(&circuit,2).unwrap();let owners=boolean_owner_inputs(None);
        let expanded_terms=(0..4).flat_map(|owner|circuit.terms.iter().map(move |term|{
            let mut gate=term.gate.clone();gate.left+=owner*8;gate.right+=owner*8;
            Term{row:(owner<<2)|term.row,gate}
        })).collect::<Vec<_>>();
        let expanded=crate::sparse::Circuit{input_len:32,row_count:16,terms:expanded_terms};
        let bind=|transcript:&mut Transcript|transcript.append_bytes(b"fixed-core-uv-statement",b"same immutable relation");
        let wiring=|r:&[Fr],u:&[Fr],v:&[Fr]|crate::sparse::wiring(&circuit,&shape,r,u,v).map_err(|error|error.to_string());
        let load=|owner:usize|Ok(owners[owner].clone());

        let mut resident_t=Transcript::new(b"fixed-core-uv-differential");
        let (resident,resident_claim)=crate::sparse::prove_with_binding(&expanded,&owners.concat(),0,&mut resident_t,bind).unwrap();
        let mut generic_t=Transcript::new(b"fixed-core-uv-differential");
        let (generic,generic_claim,_)=prove_fixed_core_v_with_cache_budget_for_test(&template,Some(0),load,
            &mut generic_t,bind,wiring).unwrap();
        let mut candidate_t=Transcript::new(b"fixed-core-uv-differential");
        let (candidate,candidate_claim,stats)=prove_fixed_core_uv_with_cache_budget_for_test(&template,Some(0),load,
            &mut candidate_t,bind,wiring).unwrap();
        let proof_bytes=crate::gkr::encode_proof(&resident).unwrap();
        assert_eq!(crate::gkr::encode_proof(&generic).unwrap(),proof_bytes);
        assert_eq!(crate::gkr::encode_proof(&candidate).unwrap(),proof_bytes);
        assert_eq!(generic_claim,resident_claim);assert_eq!(candidate_claim,resident_claim);
        compare_transcripts(&generic_t,&resident_t);compare_transcripts(&candidate_t,&resident_t);
        assert_eq!(stats.u.specialized_builders,16);assert_eq!(stats.u.generic_builders,0);
        assert_eq!(stats.u.descriptor_count,2);assert!(stats.u.common_u_capacity_bytes>0);
        assert!(stats.common_state_peak_capacity_bytes<=MAX_FIXED_V_COMMON_STATE_BYTES);

        let mixed=boolean_owner_inputs(Some(2));let mixed_load=|owner:usize|Ok(mixed[owner].clone());
        let mut mixed_resident_t=Transcript::new(b"fixed-core-uv-differential");
        let (mixed_resident,mixed_resident_claim)=crate::sparse::prove_with_binding(&expanded,&mixed.concat(),0,
            &mut mixed_resident_t,bind).unwrap();
        let mut mixed_generic_t=Transcript::new(b"fixed-core-uv-differential");
        let (mixed_generic,mixed_generic_claim,_)=prove_fixed_core_v_with_cache_budget_for_test(&template,Some(0),mixed_load,
            &mut mixed_generic_t,bind,wiring).unwrap();
        let mixed_proof_bytes=crate::gkr::encode_proof(&mixed_resident).unwrap();
        assert_eq!(crate::gkr::encode_proof(&mixed_generic).unwrap(),mixed_proof_bytes);
        assert_eq!(mixed_generic_claim,mixed_resident_claim);compare_transcripts(&mixed_generic_t,&mixed_resident_t);
        let mut fallback_t=Transcript::new(b"fixed-core-uv-differential");
        let (fallback,fallback_claim,fallback_stats)=prove_fixed_core_uv_with_cache_budget_for_test(&template,Some(0),mixed_load,
            &mut fallback_t,bind,wiring).unwrap();
        assert_eq!(crate::gkr::encode_proof(&fallback).unwrap(),mixed_proof_bytes);
        assert_eq!(fallback_claim,mixed_resident_claim);compare_transcripts(&fallback_t,&mixed_resident_t);
        assert_eq!(fallback_stats.u.specialized_builders,12);
        assert_eq!(fallback_stats.u.generic_builders,4,
            "the unused non-Boolean coordinate sends every builder for that owner through the generic route");
        assert_eq!(fallback_stats.u.descriptor_count,2);
    }

    #[test]
    fn fixed_uv_keeps_cached_route_and_old_stats_unmodified(){
        let circuit=boolean_fixed_core();let template=FixedCoreVTemplate::try_new(&circuit,3,2,2).unwrap();
        let shape=crate::sparse::validate(&circuit,2).unwrap();let owners=boolean_owner_inputs(None);
        let bind=|transcript:&mut Transcript|transcript.append_bytes(b"fixed-core-uv-cached",b"same");
        let wiring=|r:&[Fr],u:&[Fr],v:&[Fr]|crate::sparse::wiring(&circuit,&shape,r,u,v).map_err(|error|error.to_string());
        let load=|owner:usize|Ok(owners[owner].clone());
        let mut old_t=Transcript::new(b"fixed-core-uv-cached");
        let (old,old_claim,old_stats)=prove_fixed_core_v(&template,load,&mut old_t,bind,wiring).unwrap();
        let mut uv_t=Transcript::new(b"fixed-core-uv-cached");
        let (uv,uv_claim,uv_stats)=prove_fixed_core_uv(&template,load,&mut uv_t,bind,wiring).unwrap();
        assert_eq!(crate::gkr::encode_proof(&uv).unwrap(),crate::gkr::encode_proof(&old).unwrap());
        assert_eq!(uv_claim,old_claim);compare_transcripts(&uv_t,&old_t);
        assert_eq!(uv_stats.u,FixedCoreUProofStats::default());
        assert_eq!(old_stats.u,FixedCoreUProofStats::default());

        let mut zero_u_t=Transcript::new(b"fixed-core-uv-cached");
        let (zero_u,zero_u_claim,zero_u_stats)=prove_fixed_core_uv_with_u_budget_for_test(&template,Some(0),0,
            load,&mut zero_u_t,bind,wiring).unwrap();
        assert_eq!(crate::gkr::encode_proof(&zero_u).unwrap(),crate::gkr::encode_proof(&old).unwrap());
        assert_eq!(zero_u_claim,old_claim);compare_transcripts(&zero_u_t,&old_t);
        assert_eq!(zero_u_stats.u.specialized_builders,0);
        assert_eq!(zero_u_stats.u.generic_builders,16);
        assert_eq!(zero_u_stats.u.descriptor_count,0);
        assert_eq!(zero_u_stats.u.common_u_capacity_bytes,0);
    }
}

// Fixture-only deferred-X continuation. The existing grouped replay is
// intentionally retained byte-for-byte for the accepted V0/V1 reference.
#[cfg(test)]
impl EdgeReplayBanks {
    fn a_is_exact_zero(&self) -> bool {
        match self {
            Self::Dense(a, _) => a.iter().all(Zero::is_zero),
            Self::Sparse(a, _) => a.is_empty(),
        }
    }

    fn zero_a_message(&self) -> Result<[Fr; 3], String> {
        if !self.a_is_exact_zero() {
            return Err("deferred V message requires exact zero A bank".into());
        }
        let mut message = [Fr::zero(); 3];
        match self {
            Self::Dense(_, b) => {
                if b.len() % 2 != 0 {
                    return Err("deferred V dense B bank has odd extent".into());
                }
                for pair in (0..b.len()).step_by(2) {
                    message[0] += b[pair];
                    message[1] += b[pair + 1] - b[pair];
                }
            }
            Self::Sparse(_, b) => {
                let mut previous = None;
                for &(wire, value) in b {
                    if previous.is_some_and(|prior| wire <= prior) {
                        return Err("deferred V sparse B bank is not canonical".into());
                    }
                    previous = Some(wire);
                    if wire & 1 == 0 {
                        message[0] += value;
                        message[1] -= value;
                    } else {
                        message[1] += value;
                    }
                }
            }
        }
        Ok(message)
    }
}

#[cfg(test)]
pub(crate) struct EdgeGroupedVDeferredOwnerResultForTest {
    pub(crate) message: [Fr; 3],
    /// None means the exact-zero A branch did not observe X. Some is only the
    /// locally folded observation and is never a terminal claim.
    pub(crate) x_observation: Option<Fr>,
    pub(crate) metrics: EdgeGroupedVMetricsForTest,
}

/// Duplicate the reviewed grouped pre-X construction. Keep the accepted
/// edge_replay_v_grouped body above literal; this helper is the only entry to
/// the deferred test path.
#[cfg(test)]
fn edge_replay_v_grouped_banks_deferred_for_test<F, W>(
    visit: &mut F,
    slot: usize,
    width: usize,
    copies: usize,
    base_row_bits: usize,
    member_row_bits: &[usize],
    physical_count: usize,
    logical_count: usize,
    inactive_count: usize,
    b0: Fr,
    row_weight: &W,
    u_slot_weights: &[Fr],
    u_local_weights: &[Fr],
    left_value: Fr,
) -> Result<(EdgeReplayBanks, EdgeFallbackMetrics), String>
where
    F: FnMut(bool, usize, &mut dyn FnMut(EdgeTerm) -> Result<(), String>) -> Result<(), String>,
    W: Fn(&EdgeTerm) -> Result<Fr, String>,
{
    if width == 0
        || !width.is_power_of_two()
        || slot >= copies
        || physical_count.checked_add(inactive_count) != Some(logical_count)
        || u_slot_weights.len() != copies
        || u_local_weights.len() != width
    {
        return Err("deferred grouped V bank geometry or count rejected".into());
    }
    let bank_terms = physical_count
        .checked_add(1)
        .ok_or("deferred grouped V bank estimate overflow")?;
    let mut banks = EdgeReplayBanks::new(width, bank_terms)?;
    let visited = walk_edge_endpoint(
        visit,
        false,
        slot,
        width,
        copies,
        base_row_bits,
        member_row_bits,
        Some(physical_count),
        &mut |edge| {
            let gate = &edge.term.gate;
            let left_slot = gate.left / width;
            let left_wire = gate.left % width;
            let weight = row_weight(&edge)?
                * u_slot_weights
                    .get(left_slot)
                    .copied()
                    .ok_or("deferred grouped V left slot weight outside bound")?
                * u_local_weights[left_wire];
            let wire = gate.right % width;
            banks.add(
                wire,
                weight * (gate.c2 + gate.c3 * left_value),
                weight * (gate.c0 + gate.c1 * left_value),
            );
            Ok(())
        },
    )?;
    if visited != physical_count {
        return Err("deferred grouped V physical endpoint count changed".into());
    }
    // Injection precedes every Boolean fold, including the terminal round.
    banks.add(0, Fr::zero(), b0);
    banks.coalesce();
    let metrics = EdgeFallbackMetrics {
        visits: physical_count as u64,
        bank_capacity_peak_bytes: banks.storage_bound(),
        dense: matches!(&banks, EdgeReplayBanks::Dense(..)),
        ..Default::default()
    };
    Ok((banks, metrics))
}

#[cfg(test)]
fn edge_finish_v_deferred_local_for_test<L>(
    mut banks: EdgeReplayBanks,
    input: &mut CopyCache<L>,
    slot: usize,
    prefix: &[Fr],
    mut metrics: EdgeFallbackMetrics,
) -> Result<([Fr; 3], Option<Fr>, EdgeFallbackMetrics), String>
where
    L: FnMut(usize) -> Result<Vec<Fr>, String>,
{
    let input_bits = input.width.trailing_zeros() as usize;
    if input.width == 0
        || !input.width.is_power_of_two()
        || prefix.len() >= input_bits
    {
        return Err("deferred local V prefix or geometry rejected".into());
    }
    if banks.a_is_exact_zero() {
        let started = std::time::Instant::now();
        for challenge in prefix {
            metrics.replay_folds = metrics
                .replay_folds
                .checked_add(1)
                .ok_or("deferred local V fold count overflow")?;
            metrics.bank_fold_entries = metrics
                .bank_fold_entries
                .checked_add(banks.entries() as u64)
                .ok_or("deferred local V bank fold count overflow")?;
            banks.fold(*challenge);
            metrics.bank_capacity_peak_bytes =
                metrics.bank_capacity_peak_bytes.max(banks.storage_bound());
        }
        metrics.fold_ns = if prefix.is_empty() {
            0
        } else {
            u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX)
        };
        metrics.cache_capacity_peak_bytes = input
            .capacity_bytes()
            .ok_or("deferred local V cache byte count overflow")?;
        return Ok((banks.zero_a_message()?, None, metrics));
    }

    let x = input.vector(slot)?;
    metrics.cache_gets = 1;
    metrics.vector_clones = 1;
    metrics.cache_capacity_peak_bytes = input
        .capacity_bytes()
        .ok_or("deferred local V cache byte count overflow")?;
    let state = edge_replay_fold(banks, x, prefix, metrics);
    let polynomial: [Fr; 3] = state
        .banks
        .message(&state.x)
        .as_slice()
        .try_into()
        .map_err(|_| "deferred local V quadratic message extent")?;
    let observed = *state
        .x
        .first()
        .ok_or("deferred local V folded X absent")?;
    Ok((polynomial, Some(observed), state.metrics))
}

#[cfg(test)]
impl<L> EdgeGroupedVCandidateForTest<L>
where
    L: FnMut(usize) -> Result<Vec<Fr>, String>,
{
    pub(crate) fn local_owner_deferred(
        &mut self,
        context: &EdgeGroupedVContextForTest<'_, '_, '_>,
        owner: usize,
        canonical_count: usize,
        prefix: &[Fr],
    ) -> Result<EdgeGroupedVDeferredOwnerResultForTest, String> {
        let input_bits = self.width.trailing_zeros() as usize;
        if owner >= self.copies
            || prefix.len() >= input_bits
            || self.input.capacity != 4
            || context.weights.u_local.len() != self.width
            || context.weights.u_slot.len() != self.copies
        {
            return Err("deferred grouped V owner context or geometry rejected".into());
        }
        let (inactive_count, b0) = context.family_owner(owner)?;
        let physical_count = canonical_count
            .checked_sub(inactive_count)
            .ok_or("deferred grouped V inactive occurrences exceed canonical owner count")?;
        let row_weight = |edge: &EdgeTerm| {
            global_edge_row(edge.source_slot, edge.family_row, 12, 19, 1, &[19, 19])
                .map(|row| context.weights.rows.at(row))
        };
        let mut visit = |left: bool,
                         slot: usize,
                         sink: &mut dyn FnMut(EdgeTerm) -> Result<(), String>| {
            if left || slot != owner {
                return Err("deferred grouped V visitor requested non-RIGHT or foreign owner".into());
            }
            context
                .adapter
                .visit_right_noninactive_for_test(&context.binding, slot, |edge| sink(edge))
                .map(|_| ())
        };
        let (banks, metrics) = edge_replay_v_grouped_banks_deferred_for_test(
            &mut visit,
            owner,
            self.width,
            self.copies,
            19,
            &[19, 19],
            physical_count,
            canonical_count,
            inactive_count,
            b0,
            &row_weight,
            &context.weights.u_slot,
            &context.weights.u_local,
            context.left_value,
        )?;
        let (message, x_observation, fallback) = edge_finish_v_deferred_local_for_test(
            banks,
            &mut self.input,
            owner,
            prefix,
            metrics,
        )?;
        Ok(EdgeGroupedVDeferredOwnerResultForTest {
            message,
            x_observation,
            metrics: EdgeGroupedVMetricsForTest {
                fallback,
                physical_visits: physical_count as u64,
                inactive_occurrences: inactive_count as u64,
                logical_occurrences: canonical_count as u64,
                family_contributions: u64::from(inactive_count > 0),
                nonzero_injections: u64::from(!b0.is_zero()),
            },
        })
    }

    pub(crate) fn terminal_owner(
        &mut self,
        context: &EdgeGroupedVContextForTest<'_, '_, '_>,
        owner: usize,
        canonical_count: usize,
        prefix: &[Fr],
    ) -> Result<EdgeGroupedVOwnerResultForTest, String> {
        if prefix.len() != 20 {
            return Err("deferred grouped V terminal requires exactly20 challenges".into());
        }
        // Reuse the accepted path, which loads and folds real X for every owner.
        self.owner(context, owner, canonical_count, prefix)
    }
}

#[cfg(test)]
pub(crate) fn edge_line_owner_contribution_for_test(
    owner: usize,
    local_line: &[Fr],
    u_high: &[Fr],
    v_high: &[Fr],
) -> Result<Vec<Fr>, String> {
    if owner >= 4096 || local_line.len() != 21 || u_high.len() != 12 || v_high.len() != 12 {
        return Err("complete V line owner or polynomial geometry rejected".into());
    }
    let selector = copy_line_selector(owner, u_high, v_high);
    let contribution = multiply(local_line, &selector);
    if selector.len() != 13 || contribution.len() != 33 {
        return Err("complete V line selector or contribution extent changed".into());
    }
    Ok(contribution)
}

#[cfg(test)]
fn edge_deferred_control_term(
    right: usize,
    c0: Fr,
    c1: Fr,
    c2: Fr,
    c3: Fr,
) -> EdgeTerm {
    EdgeTerm {
        source_slot: 0,
        family_row: 0,
        term: Term {
            row: 0,
            gate: gkr::Gate {
                left: 0,
                right,
                c0,
                c1,
                c2,
                c3,
            },
        },
    }
}

#[cfg(test)]
fn edge_deferred_control_banks(
    width: usize,
    left_value: Fr,
    terms: &[EdgeTerm],
    b0: Fr,
) -> Result<(EdgeReplayBanks, EdgeFallbackMetrics), String> {
    let mut visit = |left: bool,
                     slot: usize,
                     sink: &mut dyn FnMut(EdgeTerm) -> Result<(), String>| {
        if left || slot != 0 {
            return Err("deferred V control visitor scope".into());
        }
        for term in terms {
            sink(term.clone())?;
        }
        Ok(())
    };
    let row_weight = |_edge: &EdgeTerm| Ok(Fr::one());
    edge_replay_v_grouped_banks_deferred_for_test(
        &mut visit,
        0,
        width,
        2,
        1,
        &[1],
        terms.len(),
        terms.len(),
        0,
        b0,
        &row_weight,
        &[Fr::one(); 2],
        &vec![Fr::one(); width],
        left_value,
    )
}

#[cfg(test)]
fn edge_deferred_control_linear_message(values: &[Fr]) -> Result<[Fr; 3], String> {
    if values.is_empty() || values.len() % 2 != 0 {
        return Err("deferred V reference B extent".into());
    }
    let mut message = [Fr::zero(); 3];
    for pair in (0..values.len()).step_by(2) {
        message[0] += values[pair];
        message[1] += values[pair + 1] - values[pair];
    }
    Ok(message)
}

#[cfg(test)]
fn edge_deferred_control_zero_case(
    width: usize,
    left_value: Fr,
    terms: &[EdgeTerm],
    b0: Fr,
    prefix: &[Fr],
    expect_dense: bool,
) -> Result<(), String> {
    let (banks, metrics) = edge_deferred_control_banks(width, left_value, terms, b0)?;
    if !banks.a_is_exact_zero() || metrics.dense != expect_dense {
        return Err("deferred V zero-A bank representation or equality mismatch".into());
    }
    let mut reference_b = vec![Fr::zero(); width];
    for edge in terms {
        reference_b[edge.term.gate.right % width] +=
            edge.term.gate.c0 + edge.term.gate.c1 * left_value;
    }
    reference_b[0] += b0;
    for challenge in prefix {
        gkr::fold(&mut reference_b, *challenge);
    }
    let expected = edge_deferred_control_linear_message(&reference_b)?;
    let loads = std::cell::Cell::new(0usize);
    let mut input = CopyCache::new(
        |_owner| {
            loads.set(loads.get() + 1);
            Err("zero-A control must not load X".into())
        },
        width,
        4,
    );
    let (message, observed, actual_metrics) = edge_finish_v_deferred_local_for_test(
        banks,
        &mut input,
        0,
        prefix,
        metrics,
    )?;
    if message != expected
        || observed.is_some()
        || loads.get() != 0
        || actual_metrics.cache_gets != 0
        || actual_metrics.vector_clones != 0
        || actual_metrics.x_fold_fields != 0
        || actual_metrics.replay_folds != prefix.len() as u64
    {
        return Err("deferred V exact-zero path observed or folded X".into());
    }
    Ok(())
}

#[cfg(test)]
fn edge_deferred_control_reference_multiply(a: &[Fr], b: &[Fr]) -> Vec<Fr> {
    let mut out = vec![Fr::zero(); a.len() + b.len() - 1];
    for (i, left) in a.iter().enumerate() {
        for (j, right) in b.iter().enumerate() {
            out[i + j] += *left * *right;
        }
    }
    out
}

/// Called by the ordinary complete-V control selector so these controls do
/// not require an additional compile/run phase.
#[cfg(test)]
pub(crate) fn edge_grouped_v_deferred_controls_for_test() -> Result<(), String> {
    let same_wire = [
        edge_deferred_control_term(0, Fr::from(2u64), Fr::one(), Fr::one(), Fr::zero()),
        edge_deferred_control_term(0, -Fr::one(), Fr::from(2u64), -Fr::one(), Fr::one()),
    ];
    edge_deferred_control_zero_case(8, Fr::zero(), &same_wire, Fr::from(3u64), &[], true)?;
    edge_deferred_control_zero_case(
        64,
        Fr::zero(),
        &same_wire,
        Fr::from(3u64),
        &[Fr::from(7u64)],
        false,
    )?;
    let long_prefix = (0..19)
        .map(|index| Fr::from((index as u64 + 3) * 11))
        .collect::<Vec<_>>();
    edge_deferred_control_zero_case(
        1usize << 20,
        Fr::zero(),
        &same_wire,
        Fr::from(3u64),
        &long_prefix,
        false,
    )?;

    // Cancellation is pointwise by wire: [a,-a] on distinct wires is not zero.
    let cross_wire = [
        edge_deferred_control_term(0, Fr::zero(), Fr::zero(), Fr::one(), Fr::zero()),
        edge_deferred_control_term(1, Fr::zero(), Fr::zero(), -Fr::one(), Fr::zero()),
    ];
    let (banks, metrics) = edge_deferred_control_banks(8, Fr::zero(), &cross_wire, Fr::zero())?;
    if banks.a_is_exact_zero() || banks.zero_a_message().is_ok() {
        return Err("deferred V cross-wire cancellation was incorrectly eligible".into());
    }
    let actual_x = (0..8).map(|i| Fr::from((i + 2) as u64)).collect::<Vec<_>>();
    let mut changed_x = actual_x.clone();
    changed_x[0] += Fr::one();
    let actual = banks.message(&actual_x);
    if actual == banks.message(&changed_x) || actual == [Fr::zero(); 3] {
        return Err("deferred V nonzero-A X sensitivity was vacuous".into());
    }
    let loads = std::cell::Cell::new(0usize);
    let mut input = CopyCache::new(
        |_owner| {
            loads.set(loads.get() + 1);
            Ok(actual_x.clone())
        },
        8,
        4,
    );
    let (candidate_message, observed, nonzero_metrics) = edge_finish_v_deferred_local_for_test(
        banks,
        &mut input,
        0,
        &[],
        metrics,
    )?;
    if candidate_message.as_slice() != actual.as_slice()
        || observed != Some(actual_x[0])
        || loads.get() != 1
        || nonzero_metrics.cache_gets != 1
        || nonzero_metrics.vector_clones != 1
        || nonzero_metrics.x_fold_fields != 0
    {
        return Err("deferred V nonzero-A path did not retain real X".into());
    }

    // The exact decision depends on the bound left value, not only c2.
    let left_sensitive = [
        edge_deferred_control_term(0, Fr::zero(), Fr::zero(), Fr::one(), Fr::zero()),
        edge_deferred_control_term(0, Fr::zero(), Fr::zero(), -Fr::one(), Fr::one()),
    ];
    let (at_zero, _) = edge_deferred_control_banks(8, Fr::zero(), &left_sensitive, Fr::zero())?;
    let (at_three, _) = edge_deferred_control_banks(8, Fr::from(3u64), &left_sensitive, Fr::zero())?;
    if !at_zero.a_is_exact_zero() || at_three.a_is_exact_zero() {
        return Err("deferred V left-value binding sensitivity failed".into());
    }

    // The existing full-X kernel remains mandatory for a zero-A terminal.
    let terminal_loads = std::cell::Cell::new(0usize);
    let mut terminal_cache = CopyCache::new(
        |_owner| {
            terminal_loads.set(terminal_loads.get() + 1);
            Ok(actual_x.clone())
        },
        8,
        4,
    );
    let mut visit = |left: bool,
                     slot: usize,
                     sink: &mut dyn FnMut(EdgeTerm) -> Result<(), String>| {
        if left || slot != 0 {
            return Err("deferred V terminal control visitor scope".into());
        }
        for term in &same_wire {
            sink(term.clone())?;
        }
        Ok(())
    };
    let row_weight = |_edge: &EdgeTerm| Ok(Fr::one());
    let terminal_prefix = [Fr::from(3u64), Fr::from(5u64), Fr::from(7u64)];
    let terminal_state = edge_replay_v_grouped(
        &mut visit,
        &mut terminal_cache,
        0,
        8,
        2,
        1,
        &[1],
        same_wire.len(),
        same_wire.len(),
        0,
        Fr::from(3u64),
        &row_weight,
        &[Fr::one(); 2],
        &[Fr::one(); 8],
        Fr::zero(),
        &terminal_prefix,
    )?;
    if terminal_loads.get() != 1
        || terminal_state.x.len() != 1
        || terminal_state.x[0] != Fr::from(43u64)
        || terminal_state.metrics.x_fold_fields != 14
        || terminal_state.metrics.cache_gets != 1
        || terminal_state.metrics.vector_clones != 1
    {
        return Err("deferred V terminal did not load and fold real X".into());
    }
    let mut no_terminal_prefix = CopyCache::new(
        |_owner| Err("terminal must use true X".into()),
        8,
        4,
    );
    if edge_finish_v_deferred_local_for_test(
        edge_deferred_control_banks(8, Fr::zero(), &same_wire, Fr::zero())?.0,
        &mut no_terminal_prefix,
        0,
        &terminal_prefix,
        EdgeFallbackMetrics::default(),
    )
    .is_ok()
    {
        return Err("deferred local API accepted a terminal prefix".into());
    }

    // Exercise the existing selector/multiply through a strict owner wrapper.
    let local_line = (0..21)
        .map(|index| Fr::from(index as u64 + 1))
        .collect::<Vec<_>>();
    let u_high = (0..12)
        .map(|index| Fr::from(index as u64 + 2))
        .collect::<Vec<_>>();
    let v_high = (0..12)
        .map(|index| Fr::from(index as u64 * 3 + 17))
        .collect::<Vec<_>>();
    let contribution = edge_line_owner_contribution_for_test(5, &local_line, &u_high, &v_high)?;
    let mut selector = vec![Fr::one()];
    for (bit, (u, v)) in u_high.iter().zip(&v_high).enumerate() {
        let factor = if (5usize >> bit) & 1 == 1 {
            [*u, *v - *u]
        } else {
            [Fr::one() - *u, *u - *v]
        };
        selector = edge_deferred_control_reference_multiply(&selector, &factor);
    }
    let expected = edge_deferred_control_reference_multiply(&local_line, &selector);
    if contribution != expected || contribution.len() != 33 {
        return Err("deferred V line owner contribution mismatch".into());
    }
    if edge_line_owner_contribution_for_test(4096, &local_line, &u_high, &v_high).is_ok()
        || edge_line_owner_contribution_for_test(5, &local_line[..20], &u_high, &v_high).is_ok()
        || edge_line_owner_contribution_for_test(5, &local_line, &u_high[..11], &v_high).is_ok()
    {
        return Err("deferred V line owner wrapper accepted invalid geometry".into());
    }
    Ok(())
}

#[cfg(test)]
mod packed_line52_controls{
use super::*;
type R<T>=Result<T,String>;
type Plan=PackedLinePlan;
const MAX_WIDTH:usize=1<<20;
const PLAN_LIMIT:usize=512*1024*1024;
fn need(ok:bool,message:&str)->R<()>{if ok{Ok(())}else{Err(message.into())}}
fn reference_line(packed:&[u8],u:&[Fr],v:&[Fr])->Vec<Fr>{
    let fields=expand(packed);
    gkr::line_polynomial(&fields,u,v)
}
fn expand(packed:&[u8])->Vec<Fr>{
    packed.iter().flat_map(|byte|(0..8).map(move|bit|Fr::from(((byte>>bit)&1)as u64))).collect()
}
fn pre_fs<I:EdgeInput>(input:&mut I,bits:usize,slots:usize,expected:&str,loads:&std::cell::Cell<usize>)->R<()>{
    let activity=std::cell::Cell::new([0usize;4]);
    let bump=|i:usize|{let mut a=activity.get();a[i]+=1;activity.set(a);};
    let mut t=Transcript::new(b"packed-line52-preflight-v1");
    let before=[t.challenges(),t.raw_queries(),t.bytes_absorbed()];
    let next=t.clone().try_challenge_scalar(b"packed-line52-preflight-next")?;
    let mut fast=PackedLineStats::default();
    let result=prove_edge_terms_run(bits,slots,2,0,&[2],|_,_,_|{bump(0);Ok(())},input,&mut t,
        |_|bump(1),|_,_,_|{bump(2);Ok([Fr::zero();4])},
        EdgeIncrementalControl{force_u_off:true,force_v_off:true,cache_limit_override:Some(0)},true,Some(&mut fast),
        &mut|_|{bump(3);Ok(())});
    need(result.err().as_deref()==Some(expected),"packed line actual run rejection")?;
    need(activity.get()==[0;4]&&loads.get()==0&&[t.challenges(),t.raw_queries(),t.bytes_absorbed()]==before
        &&t.clone().try_challenge_scalar(b"packed-line52-preflight-next")?==next,"packed line pre-FS no activity")
}
fn whole_proofs()->R<()>{
    for width in [8usize,16]{for copies in [2usize,4]{
        let packets:Vec<_>=(0..copies).map(|owner|packet(width,5,owner)).collect();
        let fields:Vec<_>=packets.iter().flat_map(|p|expand(p)).collect();
        let edges:Vec<_>=(0..copies).map(|owner|{
            let left=owner*width;let right=((owner+1)%copies)*width+1;
            let(c1,c2,c3)=(Fr::from(2u64),Fr::from(3u64),Fr::from(5u64));
            EdgeTerm{source_slot:owner,family_row:0,term:Term{row:0,gate:gkr::Gate{left,right,
                c0:-(c1*fields[left]+c2*fields[right]+c3*fields[left]*fields[right]),c1,c2,c3}}}
        }).collect();
        let circuit=crate::sparse::Circuit{input_len:fields.len(),row_count:4*copies,
            terms:edges.iter().map(|e|Term{row:e.source_slot*4,gate:e.term.gate.clone()}).collect()};
        let shape=crate::sparse::validate(&circuit,0).map_err(|e|e.to_string())?;
        let visit=|left:bool,owner:usize,sink:&mut dyn FnMut(EdgeTerm)->R<()>|->R<()>{
            for e in &edges{if(if left{e.term.gate.left}else{e.term.gate.right})/width==owner{sink(e.clone())?;}}Ok(())};
        let bind=|t:&mut Transcript|t.append_bytes(b"packed-line52-fixture",b"same-relation-v1");
        let wiring=|r:&[Fr],u:&[Fr],v:&[Fr]|crate::sparse::wiring(&circuit,&shape,r,u,v).map_err(|e|e.to_string());
        let mut normal_t=Transcript::new(b"packed-line52-whole-proof");let mut fast_t=normal_t.clone();
        let mut normal=PackedEdgeInput::new(width,copies,|owner|Ok(packets[owner].clone()))?;
        let mut packed=PackedEdgeInput::new(width,copies,|owner|Ok(packets[owner].clone()))?;
        let bits=width.trailing_zeros()as usize;let slots=copies.trailing_zeros()as usize;
        let(a,ca,_,_,old)=prove_edge_terms_strategy_for_test(bits,slots,2,0,&[2],true,true,true,0,&mut normal,
            visit,&mut normal_t,bind,wiring,&mut|_|Ok(()))?;
        let mut stats=PackedLineStats::default();
        let(b,cb,_,_,new)=prove_edge_terms_packed_line_for_test(bits,slots,2,0,&[2],&mut packed,
            visit,&mut fast_t,bind,wiring,&mut stats,&mut|_|Ok(()))?;
        need(gkr::encode_proof(&a)?==gkr::encode_proof(&b)?&&ca==cb,"packed line whole proof bytes/claim")?;
        need([normal_t.challenges(),normal_t.raw_queries(),normal_t.bytes_absorbed()]
            ==[fast_t.challenges(),fast_t.raw_queries(),fast_t.bytes_absorbed()]
            &&normal_t.clone().try_challenge_scalar(b"packed-line52-next")?==fast_t.clone().try_challenge_scalar(b"packed-line52-next")?,
            "packed line whole proof transcript")?;
        let mut verifier=Transcript::new(b"packed-line52-whole-proof");
        let checked=gkr::verify_with_wiring(&[bits+slots],4*copies,&b,&mut verifier,bind,
            |_,r,u,v|crate::sparse::wiring(&circuit,&shape,r,u,v)).map_err(|e|e.to_string())?;
        need(checked==cb&&gkr::mle(&fields,&cb.point).map_err(|e|e.to_string())?==cb.value,"packed line normal verifier/MLE")?;
        need([verifier.challenges(),verifier.raw_queries(),verifier.bytes_absorbed()]
            ==[fast_t.challenges(),fast_t.raw_queries(),fast_t.bytes_absorbed()]
            &&verifier.clone().try_challenge_scalar(b"packed-line52-next")?==fast_t.clone().try_challenge_scalar(b"packed-line52-next")?,
            "packed line normal verifier transcript")?;
        need(stats.builds==1&&stats.owners==copies as u64&&stats.coefficients==(copies*(bits+1))as u64
            &&new.line_internal_clones==0&&old.line_internal_clones==copies as u64,"packed line actual whole proof telemetry")?;
    }}Ok(())
}
pub(super) fn run()->R<()>{
    need(std::mem::size_of::<Fr>()==32&&std::mem::size_of::<usize>()==8,"packed line ABI")?;
    need(correctness()?==(840,12,1),"packed line fixture census")?;guards()?;faults()?;
    let loads=std::cell::Cell::new(0usize);
    let mut generic=CopyCache::declared(|_|{loads.set(loads.get()+1);Ok(vec![Fr::from(2u64);8])},8,2);
    pre_fs(&mut generic,3,1,"packed line unsupported input",&loads)?;
    let mut packed=PackedEdgeInput::new(8,2,|_|{loads.set(loads.get()+1);Ok(vec![0u8;1])})?;
    pre_fs(&mut packed,2,1,"packed line declared dimensions",&loads)?;
    pre_fs(&mut packed,(1usize<<32)+3,1,"packed line declared dimensions",&loads)?;
    let mut wide=PackedEdgeInput::new(1<<20,2,|_|{loads.set(loads.get()+1);Ok(vec![0u8;1<<17])})?;
    pre_fs(&mut wide,21,1,"packed line declared dimensions",&loads)?;
    let mut slots=PackedEdgeInput::new(8,4096,|_|{loads.set(loads.get()+1);Ok(vec![0u8;1])})?;
    pre_fs(&mut slots,3,13,"packed line declared dimensions",&loads)?;
    let mut two=PackedEdgeInput::new(8,2,|_|{loads.set(loads.get()+1);Ok(vec![0u8;1])})?;
    pre_fs(&mut two,3,(1usize<<32)+1,"packed line declared dimensions",&loads)?;
    let(bound,_,_)=packed_line_preflight(&packed,8,2,512*1024*1024)?;
    need(packed_line_preflight(&packed,8,2,bound)?.0==bound,"packed line exact component limit")?;
    rejected(packed_line_preflight(&packed,8,2,bound-1),"packed line component bound")?;
    let actual=packed_line_extra_charge()?;
    need(packed_line_extra_with_limit(actual)?==actual,"packed line exact extra reservation")?;
    rejected(packed_line_extra_with_limit(actual-1),"packed line extra reservation")?;
    tests::packed_line52_nonboolean_fallback();whole_proofs()
}
fn points(m: usize, kind: usize) -> (Vec<Fr>, Vec<Fr>) {
    let u: Vec<_> = (0..m).map(|i| if kind == 2 { Fr::from((i % 2) as u64) }
        else { Fr::from((2 + 3 * i) as u64) }).collect();
    let v = (0..m).map(|i| if kind == 1 { u[i] } else if kind == 2 { Fr::one() - u[i] }
        else { Fr::from((17 + 5 * i) as u64) }).collect();
    (u, v)
}
fn packet(width: usize, kind: usize, owner: usize) -> Vec<u8> {
    let mut p = vec![0u8; width / 8];
    match kind {
        0 => (), 1 => p.fill(255), 2 => p[0] = 1,
        3 => { let last = p.len() - 1; p[last] = 128; },
        4 => p.fill(0x55),
        _ => for (i, byte) in p.iter_mut().enumerate() {
            let x = (i as u64).wrapping_mul(0x9e3779b97f4a7c15).wrapping_add(0xd1b54a32d192ed03 ^ owner as u64);
            *byte = (x ^ (x >> 17) ^ (x >> 43)) as u8;
        },
    }
    p
}
fn equal(a: &[Fr], b: &[Fr]) -> R<()> { need(a == b, "coefficient differential") }
fn different(a: &[Fr], b: &[Fr]) -> R<()> { need(a != b, "private fault not detected") }
fn rejected<T>(r:R<T>,reason:&'static str)->R<()>{
    match r{Err(e)if e==reason=>Ok(()),_=>Err("packed line guard attribution".into())}
}
fn poly_mul(a: &[Fr], b: &[Fr]) -> Vec<Fr> {
    let mut out = vec![Fr::zero(); a.len() + b.len() - 1];
    for (i, x) in a.iter().enumerate() { for (j, y) in b.iter().enumerate() { out[i + j] += *x * *y; } }
    out
}
fn owner_selector(owner: usize, u: &[Fr], v: &[Fr]) -> Vec<Fr> {
    let mut p = vec![Fr::one()];
    for (i, (a, b)) in u.iter().zip(v).enumerate() {
        let factor = if (owner >> i) & 1 == 1 { [*a, *b - a] } else { [Fr::one() - a, *a - b] };
        p = poly_mul(&p, &factor);
    }
    p
}
fn assembled(packets: &[Vec<u8>], width: usize, u: &[Fr], v: &[Fr], wrong_owner: bool) -> R<Vec<Fr>> {
    let m = width.trailing_zeros() as usize;
    let mut plan = Plan::new(width, &u[..m], &v[..m], PLAN_LIMIT)?;
    let mut sum = vec![Fr::zero(); u.len() + 1];
    for (owner, packed) in packets.iter().enumerate() {
        let local = plan.apply(packed)?;
        let tag = if wrong_owner { owner ^ 1 } else { owner };
        let product = poly_mul(&local, &owner_selector(tag, &u[m..], &v[m..]));
        need(product.len() == sum.len(), "owner polynomial extent")?;
        for (s, x) in sum.iter_mut().zip(product) { *s += x; }
    }
    Ok(sum)
}
fn global_reference(packets: &[Vec<u8>], u: &[Fr], v: &[Fr]) -> Vec<Fr> {
    let mut fields = Vec::new();
    for p in packets { fields.extend(expand(p)); }
    gkr::line_polynomial(&fields, u, v)
}
fn correctness() -> R<(usize, usize, usize)> {
    let mut cases = 0;
    for byte in 0..256 {
        for kind in 0..3 {
            let (u, v) = points(3, kind); let packed = [byte as u8];
            let expected = reference_line(&packed, &u, &v);
            let mut plan = Plan::new(8, &u, &v, PLAN_LIMIT)?;
            equal(&plan.apply(&packed)?, &expected)?; cases += 1;
        }
    }
    for width in [16usize, 256, 65536, MAX_WIDTH] {
        let m = width.trailing_zeros() as usize;
        for pattern in 0..6 { for kind in 0..3 {
            let packed = packet(width, pattern, 0); let (u, v) = points(m, kind);
            let expected = reference_line(&packed, &u, &v);
            let mut plan = Plan::new(width, &u, &v, PLAN_LIMIT)?;
            equal(&plan.apply(&packed)?, &expected)?; cases += 1;
        } }
    }
    need(cases == 840, "correctness case census")?;
    let mut globals = 0;
    for width in [8usize, 16] { for owners in [2usize, 4] { for kind in 0..3 {
        let bits = width.trailing_zeros() as usize + owners.trailing_zeros() as usize;
        let (u, v) = points(bits, kind);
        let packets: Vec<_> = (0..owners).map(|s| packet(width, 5, s)).collect();
        equal(&assembled(&packets, width, &u, &v, false)?, &global_reference(&packets, &u, &v))?;
        globals += 1;
    } } }
    need(globals == 12, "global case census")?;
    // This reference case is genuinely non-Boolean. It is not an assertion
    // that the packed helper accepts Fr input or that a crate fallback ran.
    let fields: Vec<_> = (0..8).map(|i| Fr::from((i + 2) as u64)).collect();
    let (u, v) = points(3, 0); let p = gkr::line_polynomial(&fields, &u, &v);
    let z = Fr::from(7u64); let at: Vec<_> = u.iter().zip(&v).map(|(a, b)| *a + z * (*b - a)).collect();
    let mut folded = fields;
    for c in at { let n = folded.len() / 2; for i in 0..n {
        folded[i] = folded[2 * i] + c * (folded[2 * i + 1] - folded[2 * i]);
    } folded.truncate(n); }
    let value = p.iter().rev().fold(Fr::zero(), |acc, c| acc * z + c);
    need(value == folded[0] && p.len() == 4, "field reference differential")?;
    Ok((cases, globals, 1))
}
fn guards() -> R<()> {
    let (u, v) = points(3, 0);
    for w in [0, 12, MAX_WIDTH * 2] { rejected(Plan::new(w, &u, &v, PLAN_LIMIT), "packed line geometry")?; }
    let mut plan = Plan::new(8, &u, &v, PLAN_LIMIT)?;
    rejected(plan.apply(&[]), "packed line extent")?;
    rejected(plan.apply(&[0, 0]), "packed line extent")?;
    rejected(Plan::new(8, &u[..2], &v, PLAN_LIMIT), "packed line points")?;
    let mut long = v.clone(); long.push(Fr::zero());
    rejected(Plan::new(8, &u, &long, PLAN_LIMIT), "packed line points")?;
    let exact = packed_line_plan_bound(8, 3)?;
    let mut golden = Plan::new(8, &u, &v, exact)?;
    equal(&golden.apply(&[0x19])?, &reference_line(&[0x19], &u, &v))?;
    rejected(Plan::new(8, &u, &v, exact - 1), "packed line plan bound")?;
    rejected(packed_line_capacity(5, 4), "packed line actual capacity")?;
    // Real shared arithmetic helper, using an actually overflowing input.
    // The outer W<=2^20 admission cannot itself reach this overflow.
    rejected(packed_line_fields(usize::MAX), "packed line capacity arithmetic")?;
    Ok(())
}
fn faults() -> R<()> {
    let (u, v) = points(3, 0); let packed = [0x19u8]; let expected = reference_line(&packed, &u, &v);
    {
        let mut p = Plan::new(8, &u, &v, PLAN_LIMIT)?;
        for a in 0usize..256 { let b = (a as u8).reverse_bits() as usize; if a < b { p.lut.swap(a, b); } }
        different(&p.apply(&packed)?, &expected)?;
    }
    {
        let mut ru = u.clone(); let mut rv = v.clone(); ru.reverse(); rv.reverse();
        let mut p = Plan::new(8, &ru, &rv, PLAN_LIMIT)?;
        different(&p.apply(&packed)?, &expected)?;
    }
    {
        let mut stale = u.clone(); stale[0] += Fr::one();
        let stale_plan = Plan::new(8, &stale, &v, PLAN_LIMIT)?;
        let mut p = Plan::new(8, &u, &v, PLAN_LIMIT)?;
        p.lut = stale_plan.lut;
        different(&p.apply(&packed)?, &expected)?;
    }
    {
        let mut p = Plan::new(8, &u, &v, PLAN_LIMIT)?;
        p.lut[packed[0] as usize][2] += Fr::one();
        different(&p.apply(&packed)?, &expected)?;
    }
    {
        let wrong: Vec<_> = u.iter().zip(&v).map(|(a, b)| *a + *a - b).collect();
        let mut p = Plan::new(8, &u, &wrong, PLAN_LIMIT)?;
        different(&p.apply(&packed)?, &expected)?;
    }
    {
        let mut actual: Vec<_> = (1u64..=8).map(Fr::from).collect(); let mut bad = actual.clone();
        packed_line_tail(&mut actual, 2, 3, Fr::from(2u64), Fr::from(3u64), false)?;
        packed_line_tail(&mut bad, 2, 3, Fr::from(2u64), Fr::from(3u64), true)?;
        different(&bad, &actual)?;
    }
    {
        let (a, b) = points(3, 1); let mut p = Plan::new(8, &a, &b, PLAN_LIMIT)?;
        let actual = p.apply(&packed)?; let mut bad = actual.clone();
        while bad.last().is_some_and(|x| x.is_zero()) { bad.pop(); }
        different(&bad, &actual)?;
    }
    {
        let (a, b) = points(4, 0); let packets = vec![vec![0u8], vec![255u8]];
        let expected = global_reference(&packets, &a, &b);
        different(&assembled(&packets, 8, &a, &b, true)?, &expected)?;
    }
    {
        let (a, b) = points(4, 0); let packets = vec![vec![0u8], vec![255u8]];
        let expected = global_reference(&packets, &a, &b);
        let reversed = vec![packets[1].clone(), packets[0].clone()];
        different(&assembled(&reversed, 8, &a, &b, false)?, &expected)?;
    }
    Ok(())
}

}

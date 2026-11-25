//! Native N3/N4 adjacency over the existing cross-slot replay kernel.
//! TEST-only module: one producer join, without a new proof or PCS construction.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use std::cell::{Cell, RefCell};

use crate::{
    gkr::{GkrProof, InputClaim},
    header_adjacency_layout::HeaderAdjacencyLayout,
    sparse::Term,
    sparse_stream_roster::{self, EdgeTerm},
    transcript::Transcript,
};

const LOCAL_INPUT_BITS: usize = 20;
const SLOT_BITS: usize = 2;
const LOCAL_ROW_BITS: usize = 9;
const WIDTH: usize = 1 << LOCAL_INPUT_BITS;
const COPIES: usize = 1 << SLOT_BITS;
const INPUT_LEN: usize = WIDTH * COPIES;
const ROW_COUNT: usize = 1 << (LOCAL_ROW_BITS + SLOT_BITS);
const MAX_DIMENSION: usize = 24;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ChallengeTrace {
    pub(crate) r: Vec<Fr>,
    pub(crate) u: Vec<Fr>,
    pub(crate) v: Vec<Fr>,
    pub(crate) continuation: Fr,
}

#[derive(Debug)]
pub(crate) struct Diagnostics {
    pub(crate) terms: usize,
    pub(crate) term_capacity: usize,
    pub(crate) left_index_capacity: usize,
    pub(crate) right_index_capacity: usize,
    pub(crate) tuple_blake2b256: String,
    pub(crate) loader_per_slot: [usize; COPIES],
    pub(crate) max_slot_capacity: usize,
    pub(crate) endpoint_calls: [[usize; COPIES]; 2],
    pub(crate) endpoint_terms: [[usize; COPIES]; 2],
    pub(crate) used_incremental_u: bool,
    pub(crate) used_incremental_v: bool,
    pub(crate) trace: ChallengeTrace,
}

pub(crate) struct Produced {
    pub(crate) proof: GkrProof,
    pub(crate) claim: InputClaim,
    pub(crate) diagnostics: Diagnostics,
}

// No public mutation or caller-selected term callback enters this snapshot.
#[derive(Clone)]
struct FrozenAdjacency {
    terms: Vec<Term>,
    left: [Vec<usize>; COPIES],
    right: [Vec<usize>; COPIES],
}

fn admit_dimensions(
    n: u64,
    slot_bits: usize,
    input_bits: usize,
    row_bits: usize,
    input_len: usize,
    row_count: usize,
    term_count: usize,
    source_len: usize,
) -> Result<usize, String> {
    if usize::BITS < 64 {
        return Err("native adjacency requires 64-bit indices".into());
    }
    if input_bits > MAX_DIMENSION || row_bits > MAX_DIMENSION {
        return Err("native adjacency exceeds dimension24".into());
    }
    let expected_input_bits = LOCAL_INPUT_BITS.checked_add(slot_bits)
        .ok_or("native adjacency input dimension overflow")?;
    let expected_row_bits = LOCAL_ROW_BITS.checked_add(slot_bits)
        .ok_or("native adjacency row dimension overflow")?;
    let expected_terms = usize::try_from(n).ok()
        .and_then(|count| count.checked_add(1))
        .and_then(|count| count.checked_mul(256))
        .ok_or("native adjacency term count overflow")?;
    if !matches!(n, 3 | 4)
        || slot_bits != SLOT_BITS
        || input_bits != expected_input_bits
        || row_bits != expected_row_bits
        || input_len != INPUT_LEN
        || source_len != INPUT_LEN
        || row_count != ROW_COUNT
        || term_count != expected_terms
    {
        return Err("native adjacency fixed N3/N4 dimensions rejected".into());
    }
    Ok(expected_terms)
}

fn admit(layout: &HeaderAdjacencyLayout, source_len: usize) -> Result<usize, String> {
    admit_dimensions(
        layout.n(), layout.slot_log(), layout.input_log(), layout.row_log(),
        layout.input_len(), layout.row_count(), layout.term_count(), source_len,
    )
}

fn check_edge_identity(term: &Term, source_slot: usize, family_row: usize) -> Result<(), String> {
    if term.row >= ROW_COUNT || term.gate.left >= INPUT_LEN || term.gate.right >= INPUT_LEN {
        return Err("native adjacency tuple outside fixed domains".into());
    }
    let reconstructed = sparse_stream_roster::global_edge_row(
        source_slot, family_row, SLOT_BITS, LOCAL_ROW_BITS, 0, &[LOCAL_ROW_BITS],
    )?;
    if term.row != reconstructed {
        return Err("native adjacency global row identity mismatch".into());
    }
    Ok(())
}

fn reserve_exact<T>(count: usize) -> Result<Vec<T>, String> {
    let mut values = Vec::new();
    values.try_reserve_exact(count).map_err(|_| "native adjacency reservation failed")?;
    if values.capacity() > count {
        return Err("native adjacency reservation capacity exceeds declared count".into());
    }
    Ok(values)
}

fn partition(terms: &[Term]) -> Result<([Vec<usize>; COPIES], [Vec<usize>; COPIES]), String> {
    let mut left_counts = [0usize; COPIES];
    let mut right_counts = [0usize; COPIES];
    for term in terms {
        check_edge_identity(term, term.row >> LOCAL_ROW_BITS, term.row & 511)?;
        left_counts[term.gate.left / WIDTH] += 1;
        right_counts[term.gate.right / WIDTH] += 1;
    }
    let mut left: [Vec<usize>; COPIES] = std::array::from_fn(|_| Vec::new());
    let mut right: [Vec<usize>; COPIES] = std::array::from_fn(|_| Vec::new());
    for slot in 0..COPIES {
        left[slot] = reserve_exact(left_counts[slot])?;
        right[slot] = reserve_exact(right_counts[slot])?;
    }
    for (index, term) in terms.iter().enumerate() {
        left[term.gate.left / WIDTH].push(index);
        right[term.gate.right / WIDTH].push(index);
    }
    Ok((left, right))
}

impl FrozenAdjacency {
    fn freeze(layout: &HeaderAdjacencyLayout, source_len: usize) -> Result<Self, String> {
        // Fail before snapshot allocation, native emission, loading or transcript binding.
        let count = admit(layout, source_len)?;
        let mut terms: Vec<Term> = reserve_exact(count)?;
        for owner in 0..layout.n() {
            layout.visit_slot_terms(owner, |row, gate| {
                if terms.len() == count || row >> LOCAL_ROW_BITS != owner as usize {
                    return Err("native adjacency native emission owner/count drift".into());
                }
                let term = Term { row, gate };
                check_edge_identity(&term, row >> LOCAL_ROW_BITS, row & 511)?;
                terms.push(term);
                Ok(())
            })?;
        }
        if terms.len() != count {
            return Err("native adjacency native term count drift".into());
        }
        let (left, right) = partition(&terms)?;
        let frozen = Self { terms, left, right };
        frozen.validate(layout, source_len)?;
        Ok(frozen)
    }

    fn validate(&self, layout: &HeaderAdjacencyLayout, source_len: usize) -> Result<(), String> {
        let count = admit(layout, source_len)?;
        if self.terms.len() != count || self.terms.capacity() > count {
            return Err("native adjacency immutable snapshot size drift".into());
        }
        let mut seen = 0usize;
        for owner in 0..layout.n() {
            let emitted = layout.visit_slot_terms(owner, |row, gate| {
                let term = self.terms.get(seen).ok_or("native adjacency immutable tuple missing")?;
                if term.row != row || term.gate != gate || row >> LOCAL_ROW_BITS != owner as usize {
                    return Err("native adjacency immutable tuple/order drift".into());
                }
                check_edge_identity(term, row >> LOCAL_ROW_BITS, row & 511)?;
                seen += 1;
                Ok(())
            })?;
            let expected: usize = 256 + if owner + 1 == layout.n() { 256 } else { 0 };
            if emitted != expected {
                return Err("native adjacency native owner term count drift".into());
            }
        }
        if seen != count {
            return Err("native adjacency immutable tuple count drift".into());
        }
        for (left, lists) in [(true, &self.left), (false, &self.right)] {
            let mut positions = [0usize; COPIES];
            for (index, term) in self.terms.iter().enumerate() {
                let endpoint = if left { term.gate.left } else { term.gate.right };
                let slot = endpoint / WIDTH;
                if lists[slot].get(positions[slot]) != Some(&index) {
                    return Err("native adjacency endpoint index/order drift".into());
                }
                positions[slot] += 1;
            }
            for slot in 0..COPIES {
                if lists[slot].len() != positions[slot] || lists[slot].capacity() > positions[slot] {
                    return Err("native adjacency endpoint capacity/count drift".into());
                }
            }
        }
        Ok(())
    }

    fn visit_endpoint(
        &self, left: bool, slot: usize,
        sink: &mut dyn FnMut(EdgeTerm) -> Result<(), String>,
    ) -> Result<(), String> {
        if slot >= COPIES {
            return Err("native adjacency endpoint slot rejected".into());
        }
        let lists = if left { &self.left } else { &self.right };
        for &index in &lists[slot] {
            let term = self.terms.get(index).ok_or("native adjacency endpoint index rejected")?;
            // Term.row is global. The generic edge kernel does not inspect it.
            let source_slot = term.row >> LOCAL_ROW_BITS;
            let family_row = term.row & 511;
            check_edge_identity(term, source_slot, family_row)?;
            let endpoint = if left { term.gate.left } else { term.gate.right };
            if endpoint / WIDTH != slot {
                return Err("native adjacency endpoint partition rejected".into());
            }
            sink(EdgeTerm { source_slot, family_row, term: term.clone() })?;
        }
        Ok(())
    }
}

// Both the actual MAX dispatch and its differential use this producer.
pub(crate) fn prove(
    layout: &HeaderAdjacencyLayout,
    source_len: usize,
    mut load_slot: impl FnMut(usize) -> Result<Vec<Fr>, String>,
    transcript: &mut Transcript,
) -> Result<Produced, String> {
    let frozen = FrozenAdjacency::freeze(layout, source_len)?;
    let loader_per_slot = RefCell::new([0usize; COPIES]);
    let max_slot_capacity = Cell::new(0usize);
    let endpoint_calls = RefCell::new([[0usize; COPIES]; 2]);
    let endpoint_terms = RefCell::new([[0usize; COPIES]; 2]);
    let wiring_trace = RefCell::new(None::<(Vec<Fr>, Vec<Fr>, Vec<Fr>)>);
    let (proof, claim, used_incremental_u, used_incremental_v) =
        sparse_stream_roster::prove_edge_terms_with_cache_limit_for_test(
            LOCAL_INPUT_BITS, SLOT_BITS, LOCAL_ROW_BITS, 0, &[LOCAL_ROW_BITS], 0,
            |left, slot, sink| {
                if slot >= COPIES {
                    return Err("native adjacency endpoint slot rejected".into());
                }
                let side = usize::from(!left);
                endpoint_calls.borrow_mut()[side][slot] += 1;
                frozen.visit_endpoint(left, slot, &mut |edge| {
                    sink(edge)?;
                    endpoint_terms.borrow_mut()[side][slot] += 1;
                    Ok(())
                })
            },
            |slot| {
                if slot >= COPIES {
                    return Err("native adjacency loader slot rejected".into());
                }
                let values = load_slot(slot)?;
                if values.len() != WIDTH || values.capacity() > WIDTH {
                    return Err("native adjacency loaded slot width/capacity rejected".into());
                }
                loader_per_slot.borrow_mut()[slot] += 1;
                max_slot_capacity.set(max_slot_capacity.get().max(values.capacity()));
                Ok(values)
            },
            transcript,
            |t| layout.bind(t),
            |r, u, v| {
                let coefficients = layout.coefficients(r, u, v)?;
                if wiring_trace.borrow().is_some() {
                    return Err("native adjacency analytic wiring called more than once".into());
                }
                *wiring_trace.borrow_mut() = Some((r.to_vec(), u.to_vec(), v.to_vec()));
                Ok(coefficients)
            },
        )?;
    if used_incremental_u || used_incremental_v {
        return Err("native adjacency replay unexpectedly retained incremental banks".into());
    }
    let (r, u, v) = wiring_trace.into_inner().ok_or("native adjacency analytic trace missing")?;
    let continuation = transcript.clone().challenge_scalar(b"native-adjacency-trace-continuation");
    let diagnostics = Diagnostics {
        terms: frozen.terms.len(),
        term_capacity: frozen.terms.capacity(),
        left_index_capacity: frozen.left.iter().map(Vec::capacity).sum(),
        right_index_capacity: frozen.right.iter().map(Vec::capacity).sum(),
        tuple_blake2b256: crate::work_tree_layout::hash_terms(&frozen.terms),
        loader_per_slot: loader_per_slot.into_inner(),
        max_slot_capacity: max_slot_capacity.get(),
        endpoint_calls: endpoint_calls.into_inner(),
        endpoint_terms: endpoint_terms.into_inner(),
        used_incremental_u,
        used_incremental_v,
        trace: ChallengeTrace { r, u, v, continuation },
    };
    Ok(Produced { proof, claim, diagnostics })
}

#[cfg(test)]
pub(crate) fn prove_linear_for_test(layout:&HeaderAdjacencyLayout,source:&crate::packed::PackedFile,
    retained_external_bytes:usize,transcript:&mut Transcript)
    ->Result<(GkrProof,InputClaim,crate::segment_adjacency::linear_for_test::Stats),String>{
    let descriptor=layout.linear_descriptor_for_test()?;
    descriptor.validate(source.input_len(),16)?;
    let retained=retained_external_bytes.checked_add(std::mem::size_of::<crate::packed::PackedFile>())
        .and_then(|n|n.checked_add(std::mem::size_of::<HeaderAdjacencyLayout>()))
        .and_then(|n|n.checked_add(std::mem::size_of::<std::sync::Mutex<crate::packed::PackedIoSnapshot>>()+2*std::mem::size_of::<usize>()))
        .ok_or("linear adapter retained inventory overflow")?;
    crate::segment_adjacency::linear_for_test::prove(&descriptor,source.input_len(),retained,
        |chunk|source.read_copy(1<<16,chunk),transcript)
}

// Closed cache-eviction diagnostic. Native geometry below is arithmetic only;
// neither a source capability nor a native producer dispatcher is constructed.
#[cfg(test)]
mod cache_eviction_for_test {
    use super::*;
    const LIMIT:usize=512*1024*1024;
    const CATEGORY:usize=4*1024*1024;
    fn add(a:usize,b:usize)->Result<usize,String>{a.checked_add(b).ok_or("cache ledger sum overflow".into())}
    fn mul(a:usize,b:usize)->Result<usize,String>{a.checked_mul(b).ok_or("cache ledger product overflow".into())}
    fn bytes<T>(v:&Vec<T>)->Result<usize,String>{mul(v.capacity(),std::mem::size_of::<T>())}
    #[derive(Clone,Copy)]
    pub(super) enum ModelGeometry {Cache8,Native32Projection}
    #[derive(Clone,Debug,serde::Serialize)]
    pub(super) struct ModelInputs {
        active_owners:usize,padded_owners:usize,owner_width_fields:usize,term_count:usize,
        field_bytes:usize,term_bytes:usize,usize_bytes:usize,vec_header_bytes:usize,
    }
    #[derive(Clone,Debug,Default,serde::Serialize)]
    pub(super) struct SnapshotCapacities {
        terms:usize,left_indices:usize,right_indices:usize,left_outer:usize,right_outer:usize,
    }
    #[derive(Clone,Debug,serde::Serialize)]
    pub(super) struct Memory {
        model_inputs:ModelInputs,
        snapshot_bound_bytes:usize,snapshot_actual_bytes:usize,snapshot_capacities:SnapshotCapacities,
        endpoint_max_terms:[usize;2],loader_extra_bound_bytes:usize,opaque_bank_bound_bytes:usize,
        auxiliary_bound_bytes:usize,auxiliary_category_bound_bytes:[usize;4],
        adapter_owned_capacity_bytes:usize,phase_bound_bytes:[usize;4],preflight_bound_bytes:usize,
        scoped_limit_bytes:usize,helper_bounds_measured:bool,external_native_plan_included:bool,
    }
    impl Memory {
        pub(super) fn model(geometry:ModelGeometry,limit:usize)->Result<Self,String>{
            if usize::BITS!=64 || std::mem::size_of::<Fr>()!=32 || std::mem::size_of::<Term>()!=152
                ||std::mem::size_of::<Vec<usize>>()!=24{return Err("cache ledger requires frozen x64 layout".into());}
            let (active,padded)=match geometry{ModelGeometry::Cache8=>(7usize,8usize),
                ModelGeometry::Native32Projection=>(3073,4096)};
            let term_count=mul(add(active,1)?,256)?;
            let input=ModelInputs{active_owners:active,padded_owners:padded,owner_width_fields:WIDTH,term_count,
                field_bytes:32,term_bytes:152,usize_bytes:8,vec_header_bytes:24};
            let snapshot=add(add(mul(term_count,152+2*8)?,mul(2*padded,24)?)?,mul(2*padded,8)?)?;
            // Frozen CopyCache evicts before replacement:4W cache plus returned
            // X separately. EdgeReplayBanks' checked sparse admission and each
            // <=512-term endpoint bound its bank old/new overlap by3WF; dense
            // banks fit2WF. U uses8WF, V9WF+PFr, line8WF+PFr including persistent
            // u_local_weights and the unchanged line helper's old/new tables.
            // Loader destination is already in the cache component; only its
            // 65536Fr chunk and8192 packed bytes are additional here.
            let wf=mul(WIDTH,32)?;let loader=add(mul(65536,32)?,8192)?;let aux=mul(CATEGORY,4)?;
            // Four modeled4MiB categories: direct adapter metadata; high
            // handoffs/proof/point/selector scratch;8-bit equality/Transcript/
            // hashing/wiring scratch; partition-validation and bounded capture
            // metadata/error/serialization overlap. These are bounds, not RSS
            // or observations of opaque helper allocations/native parent heaps.
            let base=add(snapshot,aux)?;
            let phase_bound_bytes=[base,add(add(base,mul(8,wf)?)?,loader)?,
                add(add(add(base,mul(9,wf)?)?,mul(padded,32)?)?,loader)?,
                add(add(add(base,mul(8,wf)?)?,mul(padded,32)?)?,loader)?];
            let peak=*phase_bound_bytes.iter().max().ok_or("cache ledger empty phases")?;
            if limit!=LIMIT || peak>limit{return Err("cache producer preflight exceeds fixed512MiB or changed limit".into());}
            Ok(Self{model_inputs:input,snapshot_bound_bytes:snapshot,snapshot_actual_bytes:0,
                snapshot_capacities:SnapshotCapacities::default(),endpoint_max_terms:[0;2],
                loader_extra_bound_bytes:loader,opaque_bank_bound_bytes:mul(3,wf)?,auxiliary_bound_bytes:aux,
                auxiliary_category_bound_bytes:[CATEGORY;4],adapter_owned_capacity_bytes:0,
                phase_bound_bytes,preflight_bound_bytes:peak,scoped_limit_bytes:LIMIT,
                helper_bounds_measured:false,external_native_plan_included:false})
        }
    }

    struct Snapshot {terms:Vec<Term>,left:Vec<Vec<usize>>,right:Vec<Vec<usize>>}
    impl Snapshot {
        fn admit(layout:&HeaderAdjacencyLayout,source_len:usize)->Result<(),String>{
            let d=layout.cache_eviction_descriptor_for_test()?;d.validate(source_len,16)
        }
        fn check(term:&Term)->Result<(),String>{
            if term.row>=1<<12||term.gate.left>=1<<23||term.gate.right>=1<<23
                ||term.row>>9>=7{return Err("cache tuple outside active/source domain".into());}
            let row=sparse_stream_roster::global_edge_row(term.row>>9,term.row&511,3,9,0,&[9])?;
            if row!=term.row{return Err("cache source row reconstruction".into());}Ok(())
        }
        fn freeze(layout:&HeaderAdjacencyLayout,source_len:usize,memory:&mut Memory)->Result<Self,String>{
            Self::admit(layout,source_len)?;
            let mut terms=reserve_exact(2048)?;
            for owner in 0..7 {layout.visit_slot_terms(owner,|row,gate|{
                if terms.len()>=2048||row>>9!=owner as usize{return Err("cache canonical owner/census".into());}
                let term=Term{row,gate};Self::check(&term)?;terms.push(term);Ok(())
            })?;}
            if terms.len()!=2048{return Err("cache canonical total".into());}
            let mut counts=[vec![0usize;8],vec![0usize;8]];
            for term in &terms{counts[0][term.gate.left/WIDTH]+=1;counts[1][term.gate.right/WIDTH]+=1;}
            if counts.iter().flatten().any(|n|*n>512){return Err("cache endpoint exceeds sparse-bank model".into());}
            let mut left=reserve_exact(8)?;let mut right=reserve_exact(8)?;
            for owner in 0..8{left.push(reserve_exact(counts[0][owner])?);right.push(reserve_exact(counts[1][owner])?);}
            for (index,term) in terms.iter().enumerate(){left[term.gate.left/WIDTH].push(index);right[term.gate.right/WIDTH].push(index);}
            drop(counts);
            let snapshot=Self{terms,left,right};snapshot.validate(layout,source_len)?;
            let sum=|lists:&Vec<Vec<usize>>|lists.iter().try_fold(0usize,|n,v|add(n,v.capacity()));
            memory.snapshot_capacities=SnapshotCapacities{terms:snapshot.terms.capacity(),
                left_indices:sum(&snapshot.left)?,right_indices:sum(&snapshot.right)?,
                left_outer:snapshot.left.capacity(),right_outer:snapshot.right.capacity()};
            let cap=&memory.snapshot_capacities;
            memory.snapshot_actual_bytes=add(add(mul(cap.terms,152)?,mul(add(cap.left_indices,cap.right_indices)?,8)?)?,
                mul(add(cap.left_outer,cap.right_outer)?,24)?)?;
            // Only Frozen vector capacities above are observed. The extra2P
            // kernel count entries in R are a source-derived reservation.
            if memory.snapshot_actual_bytes!=344448||memory.snapshot_actual_bytes>memory.snapshot_bound_bytes{
                return Err("cache actual snapshot inventory".into());}
            memory.endpoint_max_terms=[snapshot.left.iter().map(Vec::len).max().unwrap_or(0),
                snapshot.right.iter().map(Vec::len).max().unwrap_or(0)];
            Ok(snapshot)
        }
        fn validate(&self,layout:&HeaderAdjacencyLayout,source_len:usize)->Result<(),String>{
            Self::admit(layout,source_len)?;
            if self.terms.len()!=2048||self.terms.capacity()!=2048||self.left.len()!=8||self.right.len()!=8
                ||self.left.capacity()>8||self.right.capacity()>8{return Err("cache snapshot shape/capacity".into());}
            let mut at=0usize;
            for owner in 0..7 {let emitted=layout.visit_slot_terms(owner,|row,gate|{
                let term=self.terms.get(at).ok_or("cache missing canonical term")?;
                if term.row!=row||term.gate!=gate||row>>9!=owner as usize{return Err("cache canonical term/order drift".into());}
                Self::check(term)?;at+=1;Ok(())
            })?;if emitted!=if owner==6{512}else{256}{return Err("cache owner count drift".into());}}
            if at!=2048{return Err("cache canonical census drift".into());}
            for (left,lists) in [(true,&self.left),(false,&self.right)]{
                let mut positions=[0usize;8];
                for (index,term) in self.terms.iter().enumerate(){let endpoint=if left{term.gate.left}else{term.gate.right};
                    let owner=endpoint/WIDTH;if lists[owner].get(positions[owner])!=Some(&index){return Err("cache endpoint/order drift".into());}
                    positions[owner]+=1;}
                for owner in 0..8{if lists[owner].len()!=positions[owner]||lists[owner].capacity()!=positions[owner]
                    ||positions[owner]>512{return Err("cache endpoint census/capacity".into());}}
            }Ok(())
        }
        fn visit(&self,left:bool,owner:usize,sink:&mut dyn FnMut(EdgeTerm)->Result<(),String>)->Result<(),String>{
            if owner>=8{return Err("cache endpoint owner outside domain".into());}
            let lists=if left{&self.left}else{&self.right};
            for &index in &lists[owner]{let term=self.terms.get(index).ok_or("cache endpoint index")?;
                Self::check(term)?;let endpoint=if left{term.gate.left}else{term.gate.right};
                if endpoint/WIDTH!=owner{return Err("cache endpoint owner mismatch".into());}
                sink(EdgeTerm{source_slot:term.row>>9,family_row:term.row&511,term:term.clone()})?;
            }Ok(())
        }
    }
    pub(super) struct Produced {
        pub(super) proof:GkrProof,pub(super) claim:InputClaim,pub(super) trace:ChallengeTrace,
        pub(super) memory:Memory,
    }
    pub(super) fn prove(layout:&HeaderAdjacencyLayout,source_len:usize,
        load:impl FnMut(usize)->Result<Vec<Fr>,String>,t:&mut Transcript)->Result<Produced,String>{
        prove_with_budget(layout,source_len,load,t,CATEGORY,0)
    }
    // Private controls may lower this category or add a conservative charge;
    // they cannot increase the admitted model or enable another geometry.
    fn prove_with_budget(layout:&HeaderAdjacencyLayout,source_len:usize,
        mut load:impl FnMut(usize)->Result<Vec<Fr>,String>,t:&mut Transcript,
        category_limit:usize,extra_inline:usize)->Result<Produced,String>{
        Snapshot::admit(layout,source_len)?;
        let mut memory=Memory::model(ModelGeometry::Cache8,LIMIT)?;
        let inline=add(add(add(add(std::mem::size_of::<Snapshot>(),std::mem::size_of::<Memory>())?,
            std::mem::size_of_val(&load))?,std::mem::size_of::<Transcript>())?,
            add(std::mem::size_of::<RefCell<Option<(Vec<Fr>,Vec<Fr>,Vec<Fr>)>>>(),extra_inline)?)?;
        let trace_bound=mul(12+23+23,std::mem::size_of::<Fr>())?;
        if category_limit>CATEGORY||add(inline,trace_bound)?>category_limit{
            return Err("cache adapter metadata preflight exceeds model category".into());
        }
        let snapshot=Snapshot::freeze(layout,source_len,&mut memory)?;
        let trace=RefCell::new(None::<(Vec<Fr>,Vec<Fr>,Vec<Fr>)>);
        // The generic kernel binds and samples before its first load. Work on a
        // clone so every fallible adapter/kernel path leaves the caller intact.
        let mut working=t.clone();
        let (proof,claim,iu,iv)=sparse_stream_roster::prove_edge_terms_with_cache_limit_for_test(20,3,9,0,&[9],0,
            |left,owner,sink|snapshot.visit(left,owner,sink),
            |owner|{if owner>=8{return Err("cache loader owner".into());}let x=load(owner)?;
                if x.len()!=WIDTH||x.capacity()>WIDTH{return Err("cache loader width/capacity".into());}
                if x.iter().any(|v|!v.is_zero()&&!v.is_one()){return Err("cache non-Boolean owner".into());}Ok(x)},
            &mut working,|t|layout.bind(t),|r,u,v|{
                if trace.borrow().is_some(){return Err("cache coefficient replay".into());}
                if (r.len(),u.len(),v.len())!=(12,23,23){return Err("cache coefficient trace shape".into());}
                let owned=(r.to_vec(),u.to_vec(),v.to_vec());
                let actual=add(add(bytes(&owned.0)?,bytes(&owned.1)?)?,bytes(&owned.2)?)?;
                if actual>trace_bound||add(inline,actual)?>category_limit{
                    return Err("cache coefficient trace exceeds preflight".into());
                }
                *trace.borrow_mut()=Some(owned);layout.coefficients(r,u,v)
            })?;
        if iu||iv{return Err("cache diagnostic incremental cache must remain disabled".into());}
        let (r,u,v)=trace.into_inner().ok_or("cache coefficient trace absent")?;
        memory.adapter_owned_capacity_bytes=add(inline,add(add(bytes(&r)?,bytes(&u)?)?,bytes(&v)?)?)?;
        if memory.adapter_owned_capacity_bytes>category_limit{return Err("cache adapter metadata exceeds model category".into());}
        let continuation=working.clone().try_challenge_scalar(b"native-adjacency-trace-continuation")?;
        let result=Produced{proof,claim,trace:ChallengeTrace{r,u,v,continuation},memory};
        *t=working;
        Ok(result)
    }
    pub(super) fn linear(layout:&HeaderAdjacencyLayout,source:&crate::packed::PackedFile,
        retained:usize,t:&mut Transcript)->Result<(GkrProof,InputClaim,crate::segment_adjacency::linear_for_test::Stats),String>{
        let d=layout.cache_eviction_descriptor_for_test()?;d.validate(source.input_len(),16)?;
        let retained=add(add(add(retained,std::mem::size_of::<crate::packed::PackedFile>())?,
            std::mem::size_of::<HeaderAdjacencyLayout>())?,
            std::mem::size_of::<std::sync::Mutex<crate::packed::PackedIoSnapshot>>()+2*std::mem::size_of::<usize>())?;
        crate::segment_adjacency::linear_for_test::preflight_for_test(&d,retained)?;
        crate::segment_adjacency::linear_for_test::prove(&d,source.input_len(),retained,
            |chunk|source.read_copy(1<<16,chunk),t)
    }

    pub(super) fn controls(literal:impl Fn(&[Term],&[Fr],&[Fr],&[Fr])->[Fr;4]){
        let model=Memory::model(ModelGeometry::Cache8,LIMIT).unwrap();
        assert_eq!(model.snapshot_bound_bytes,344576);assert_eq!(model.phase_bound_bytes,[17121792,287662592,321217280,287662848]);
        let native=Memory::model(ModelGeometry::Native32Projection,LIMIT).unwrap();
        assert_eq!(native.snapshot_bound_bytes,132468736);assert_eq!(native.preflight_bound_bytes,453472256);
        assert_eq!(native.opaque_bank_bound_bytes,96*1024*1024);
        assert!(Memory::model(ModelGeometry::Cache8,LIMIT-1).is_err());
        assert!(add(usize::MAX,1).is_err());assert!(mul(usize::MAX,2).is_err());
        for (n,h) in [(3,2),(4,2),(6,3),(8,3),(3073,12)]{
            let layout=HeaderAdjacencyLayout::compile(n,h,[0;32],[0;32]).unwrap();
            let called=Cell::new(0);let mut t=Transcript::new(b"cache-admission-control");let before=t.clone().challenge_scalar(b"unchanged");
            assert!(prove(&layout,layout.input_len(),|_|{called.set(called.get()+1);Err("should not load".into())},&mut t).is_err());
            assert_eq!(called.get(),0);assert_eq!(t.challenges(),0);assert_eq!(t.clone().challenge_scalar(b"unchanged"),before);
        }
        let layout=HeaderAdjacencyLayout::compile(7,3,[0;32],[0;32]).unwrap();
        let d=layout.cache_eviction_descriptor_for_test().unwrap();d.validate(1<<23,16).unwrap();
        assert!(layout.linear_descriptor_for_test().is_err());assert!(d.validate(1<<22,16).is_err());
        assert!(d.validate(1<<23,15).is_err());
        let metadata=HeaderAdjacencyLayout::compile_metadata(7,3,0).unwrap();assert!(metadata.cache_eviction_descriptor_for_test().is_err());
        let mut memory=Memory::model(ModelGeometry::Cache8,LIMIT).unwrap();
        let snapshot=Snapshot::freeze(&layout,1<<23,&mut memory).unwrap();assert_eq!(memory.snapshot_actual_bytes,344448);
        assert_eq!(memory.endpoint_max_terms,[512,512]);
        let r=(0..12).map(|i|Fr::from((i+2) as u64)).collect::<Vec<_>>();
        let u=(0..23).map(|i|Fr::from((i+17) as u64)).collect::<Vec<_>>();
        let v=(0..23).map(|i|Fr::from((i+43) as u64)).collect::<Vec<_>>();
        let coefficients=literal(&snapshot.terms,&r,&u,&v);
        assert_eq!(coefficients,layout.coefficients(&r,&u,&v).unwrap());
        for fault in 0..7{let mut bad=Snapshot{terms:snapshot.terms.clone(),left:snapshot.left.clone(),right:snapshot.right.clone()};
            match fault{0=>bad.terms[256].row^=512,1=>bad.terms[256].gate.left^=WIDTH,
                2=>bad.terms[256].gate.right^=WIDTH,3=>bad.left[0][0]=1,4=>bad.terms[0].gate.right=WIDTH,
                5=>bad.terms[0].row=7<<9,_=>{bad.terms.remove(256);}}
            assert!(bad.validate(&layout,1<<23).is_err());
            if fault!=3{
                // All-zero X still satisfies these relations. The independent
                // coefficient differential, rather than witness rejection,
                // establishes sensitivity to each changed ownership/endpoint.
                assert!(bad.terms.iter().all(|term|term.gate.c0.is_zero()));
                assert_ne!(literal(&bad.terms,&r,&u,&v),coefficients);
            }
        }
        for (category,extra) in [(0,0),(CATEGORY,usize::MAX)]{
            let calls=Cell::new(0);let mut t=Transcript::new(b"cache-budget-control");
            t.append_bytes(b"existing-prefix",b"retained");
            let counters=[t.challenges(),t.raw_queries(),t.bytes_absorbed()];
            let before=t.clone().challenge_scalar(b"unchanged");
            assert!(prove_with_budget(&layout,1<<23,|_|{calls.set(calls.get()+1);Err("should not load".into())},
                &mut t,category,extra).is_err());
            assert_eq!(calls.get(),0);assert_eq!([t.challenges(),t.raw_queries(),t.bytes_absorbed()],counters);
            assert_eq!(t.clone().challenge_scalar(b"unchanged"),before);
        }
        let called=Cell::new(0);let mut rejected=Transcript::new(b"cache-source-extent-control");
        let before=rejected.clone().challenge_scalar(b"unchanged");
        assert!(prove(&layout,1<<22,|_|{called.set(called.get()+1);Err("should not load".into())},&mut rejected).is_err());
        assert_eq!(called.get(),0);assert_eq!(rejected.challenges(),0);
        assert_eq!(rejected.clone().challenge_scalar(b"unchanged"),before);
        for fail_at in [1,9]{for fault in 0..4{let calls=Cell::new(0);let mut t=Transcript::new(b"cache-reader-control");
            t.append_bytes(b"existing-prefix",b"retained");
            let counters=[t.challenges(),t.raw_queries(),t.bytes_absorbed()];
            let before=t.clone().challenge_scalar(b"unchanged");
            assert!(prove(&layout,1<<23,|_|{calls.set(calls.get()+1);
                if calls.get()!=fail_at{return Ok(vec![Fr::zero();WIDTH]);}match fault{
                0=>Err("isolated read error".into()),1=>Ok(vec![Fr::zero();WIDTH-1]),
                2=>{let mut x=vec![Fr::zero();WIDTH];x[0]=Fr::from(2u64);Ok(x)},
                _=>{let mut x=Vec::with_capacity(WIDTH+1);x.resize(WIDTH,Fr::zero());Ok(x)}}},&mut t).is_err());
            assert_eq!(calls.get(),fail_at);
            assert_eq!([t.challenges(),t.raw_queries(),t.bytes_absorbed()],counters);
            assert_eq!(t.clone().challenge_scalar(b"unchanged"),before);
        }}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{gkr::Gate, header_hash, segment_relation, serializer};

    // Evaluate one index; this oracle allocates no global equality tables.
    fn seq_at(point: &[Fr], index: usize) -> Fr {
        point.iter().enumerate().fold(Fr::one(), |weight, (bit, coordinate)| {
            weight * if (index >> bit) & 1 == 1 { *coordinate } else { Fr::one() - coordinate }
        })
    }

    fn point(bits: usize, seed: u64) -> Vec<Fr> {
        (0..bits).map(|bit| Fr::from(seed + 3 + 17 * bit as u64)).collect()
    }

    fn literal(terms: &[Term], r: &[Fr], u: &[Fr], v: &[Fr]) -> [Fr; 4] {
        let mut out = [Fr::zero(); 4];
        for term in terms {
            let weight = seq_at(r, term.row) * seq_at(u, term.gate.left) * seq_at(v, term.gate.right);
            for (sum, coefficient) in out.iter_mut().zip([
                term.gate.c0, term.gate.c1, term.gate.c2, term.gate.c3,
            ]) {
                *sum += weight * coefficient;
            }
        }
        out
    }

    fn reference(n: usize, start: &[u8; 32], tip: &[u8; 32]) -> Vec<Term> {
        let compiled = serializer::build(None).unwrap();
        let parents: [usize; 256] = std::array::from_fn(|bit| {
            header_hash::SERIALIZER_OFFSET + compiled.layout.fields.parent_id[bit / 8][bit % 8]
        });
        let digests: [usize; 256] = std::array::from_fn(|bit| segment_relation::DIGEST_OFFSET + bit);
        let mut terms = Vec::with_capacity(256 * (n + 1));
        for owner in 0..n {
            for bit in 0..256 {
                terms.push(Term {
                    row: owner * 512 + bit,
                    gate: if owner == 0 {
                        Gate {
                            left: parents[bit], right: 0,
                            c0: -Fr::from(((start[bit / 8] >> (bit % 8)) & 1) as u64),
                            c1: Fr::one(), c2: Fr::zero(), c3: Fr::zero(),
                        }
                    } else {
                        Gate {
                            left: (owner - 1) * WIDTH + digests[bit],
                            right: owner * WIDTH + parents[bit],
                            c0: Fr::zero(), c1: Fr::one(), c2: -Fr::one(), c3: Fr::zero(),
                        }
                    },
                });
            }
            if owner + 1 == n {
                for bit in 0..256 {
                    terms.push(Term {
                        row: owner * 512 + 256 + bit,
                        gate: Gate {
                            left: owner * WIDTH + digests[bit], right: 0,
                            c0: -Fr::from(((tip[bit / 8] >> (bit % 8)) & 1) as u64),
                            c1: Fr::one(), c2: Fr::zero(), c3: Fr::zero(),
                        },
                    });
                }
            }
        }
        terms
    }

    fn reject_mutant(layout: &HeaderAdjacencyLayout, good: &FrozenAdjacency, mutate: impl FnOnce(&mut FrozenAdjacency)) {
        let mut mutant = good.clone();
        mutate(&mut mutant);
        assert!(mutant.validate(layout, INPUT_LEN).is_err());
    }

    fn toy_terms()->Vec<Term>{
        let mut terms=Vec::with_capacity(3074);
        for owner in 0..3073{terms.push(Term{row:2*owner,gate:if owner==0{
            Gate{left:1,right:0,c0:Fr::zero(),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()}
        }else{Gate{left:2*(owner-1),right:2*owner+1,c0:Fr::zero(),c1:Fr::one(),c2:-Fr::one(),c3:Fr::zero()}}});}
        terms.push(Term{row:6145,gate:Gate{left:6144,right:0,c0:Fr::zero(),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()}});terms
    }
    fn mixed_bit(owner:usize)->Fr{
        let mut h=(owner as u32).wrapping_add(0x9E3779B9);h=(h^(h>>16)).wrapping_mul(0x85EBCA6B);
        h=(h^(h>>13)).wrapping_mul(0xC2B2AE35);Fr::from(((h^(h>>16))&1) as u64)
    }
    fn toy_input()->Vec<Fr>{
        let digest=|owner:usize|if owner==3072{Fr::zero()}else{mixed_bit(owner)};
        (0..4096).flat_map(|owner|if owner<3073{[digest(owner),if owner==0{Fr::zero()}else{digest(owner-1)}]}
            else if owner==4095{[Fr::one(),Fr::one()]}else{[mixed_bit(owner),mixed_bit(owner^0x555)]}).collect()
    }
    fn transcript_tuple(t:&Transcript)->[u64;3]{[t.challenges(),t.raw_queries(),t.bytes_absorbed()]}
    const AB_CONTINUATION:&[u8]=b"native-adjacency-trace-continuation";
    const AB_DOMAIN:&[u8]=b"header-parent-digest-shift-one-v1";
    fn same_transcript(a:&Transcript,b:&Transcript){
        assert_eq!(transcript_tuple(a),transcript_tuple(b));
        assert_eq!(a.clone().challenge_scalar(AB_CONTINUATION),b.clone().challenge_scalar(AB_CONTINUATION));
    }
    #[test]
    fn role5_linear_thirteen_bit_owner_differential(){
        use crate::header_adjacency_layout::linear_for_test::Descriptor;
        let d=Descriptor::owner_toy();let input=toy_input();let terms=toy_terms();
        assert_eq!(terms.len(),3074);assert!(terms.iter().all(|term|term.gate.evaluate(&input).is_zero()));
        let mut left=vec![Vec::<usize>::new();4096];let mut right=left.clone();
        for (index,term) in terms.iter().enumerate(){left[term.gate.left/2].push(index);right[term.gate.right/2].push(index);}
        let empty_visits=RefCell::new([0usize;2]);let trace=RefCell::new(None);
        let mut baseline_t=Transcript::new(AB_DOMAIN);
        let (baseline,claim,used_u,used_v)=sparse_stream_roster::prove_edge_terms_with_cache_limit_for_test(1,12,1,0,&[1],0,
            |is_left,slot,sink|{
                let list=if is_left{&left[slot]}else{&right[slot]};
                if slot==4095{assert!(list.is_empty());empty_visits.borrow_mut()[usize::from(!is_left)]+=1;}
                for &index in list{let term=terms[index].clone();sink(EdgeTerm{source_slot:term.row/2,family_row:term.row%2,term})?;}Ok(())
            },|owner|Ok(input[2*owner..2*owner+2].to_vec()),&mut baseline_t,|t|d.bind(t),|r,u,v|{
                *trace.borrow_mut()=Some((r.to_vec(),u.to_vec(),v.to_vec()));Ok(literal(&terms,r,u,v))
            }).unwrap();
        assert!(!used_u&&!used_v);assert!(empty_visits.borrow().iter().all(|calls|*calls>0));
        let retained=input.capacity()*std::mem::size_of::<Fr>()+terms.capacity()*std::mem::size_of::<Term>()
            +(left.capacity()+right.capacity())*std::mem::size_of::<Vec<usize>>()
            +left.iter().chain(&right).map(|v|v.capacity()*std::mem::size_of::<usize>()).sum::<usize>();
        let mut linear_t=Transcript::new(AB_DOMAIN);
        let (linear,linear_claim,stats)=crate::segment_adjacency::linear_for_test::prove(&d,8192,retained,
            |chunk|Ok(input[2*chunk..2*chunk+2].to_vec()),&mut linear_t).unwrap();
        assert_eq!(linear,baseline);assert_eq!(linear_claim,claim);same_transcript(&linear_t,&baseline_t);
        let packet=crate::gkr::encode_proof(&linear).unwrap();assert_eq!(packet,crate::gkr::encode_proof(&baseline).unwrap());
        assert_eq!(packet.len(),3008);assert_eq!(linear.layers[0].rounds.len(),26);
        assert_eq!(linear.layers[0].rounds[1..13],baseline.layers[0].rounds[1..13]);
        assert_eq!(linear.layers[0].rounds[14..26],baseline.layers[0].rounds[14..26]);
        assert_eq!(stats.high_fold_coordinates,[12,12]);assert_eq!(stats.initial_padding_chunks,1023);
        assert_eq!(stats.read_calls,[4096,8192,8192,4096]);assert_eq!(stats.line_input_fields,8192);
        assert!(stats.combined_bound_peak_bytes.iter().all(|b|*b<=stats.preflight_bound_bytes));
        let decoded=crate::gkr::decode_dimensions(&[13],&packet).unwrap();let mut verifier_t=Transcript::new(AB_DOMAIN);
        let verified=crate::gkr::verify_with_wiring(&[13],8192,&decoded,&mut verifier_t,|t|d.bind(t),
            |_,r,u,v|Ok(literal(&terms,r,u,v))).unwrap();
        assert_eq!(verified,claim);same_transcript(&verifier_t,&baseline_t);
        assert_eq!(crate::gkr::mle(&input,&verified.point).unwrap(),verified.value);
        let (r,u,v)=trace.into_inner().unwrap();let expected=literal(&terms,&r,&u,&v);
        assert_eq!(expected,d.coefficients(&r,&u,&v).unwrap());
        for owner_coordinate in 1..13{
            let mut changed=u.clone();changed[owner_coordinate]+=Fr::one();
            assert_ne!(literal(&terms,&r,&changed,&v),expected,"owner-coordinate sensitivity");
            assert_eq!(literal(&terms,&r,&changed,&v),d.coefficients(&r,&changed,&v).unwrap());
            let mut changed=verified.point.clone();changed[owner_coordinate]+=Fr::one();
            assert_ne!(crate::gkr::mle(&input,&changed).unwrap(),verified.value,"full source fold includes owner coordinate");
        }
        for fault in 0..9{
            let mut wrong=terms.clone();
            match fault{
                0=>wrong[1].row+=2,1=>wrong[1].gate.left+=2,2=>wrong[1].gate.right+=2,
                3=>wrong[0].gate.c0+=Fr::one(),4=>wrong.last_mut().unwrap().gate.c0+=Fr::one(),
                5=>{wrong.remove(1);},6=>wrong.push(Term{row:8190,gate:Gate{left:8190,right:0,
                    c0:Fr::one(),c1:Fr::zero(),c2:Fr::zero(),c3:Fr::zero()}}),
                7=>wrong[0].gate.right=1,_=>wrong.last_mut().unwrap().gate.right=1,
            }
            assert_ne!(literal(&wrong,&r,&u,&v),expected,"isolated term/owner/dummy endpoint fault {fault}");
        }
        let mut bad=input.clone();bad[3]=Fr::one()-bad[3];assert!(!terms[1].gate.evaluate(&bad).is_zero());
        let mut omitted=terms.clone();omitted.remove(1);assert!(omitted.iter().all(|term|term.gate.evaluate(&bad).is_zero()));
        let mut untouched=Transcript::new(AB_DOMAIN);let before=transcript_tuple(&untouched);
        assert!(crate::segment_adjacency::linear_for_test::prove(&d,8192,retained,|chunk|Ok(bad[2*chunk..2*chunk+2].to_vec()),&mut untouched).is_err());
        assert_eq!(transcript_tuple(&untouched),before);
        let padding_row=(0..13).map(|bit|Fr::from(((8190usize>>bit)&1) as u64)).collect::<Vec<_>>();
        assert_eq!(literal(&terms,&padding_row,&u,&v),[Fr::zero();4]);
    }
    #[test]
    fn role5_linear_admission_and_reader_failures(){
        use crate::header_adjacency_layout::linear_for_test::Descriptor;
        let d=Descriptor::owner_toy();let input=toy_input();
        for fault in 0..6{
            let calls=Cell::new(0usize);let mut t=Transcript::new(AB_DOMAIN);let before=transcript_tuple(&t);
            let result=crate::segment_adjacency::linear_for_test::prove(&d,if fault==0{8191}else{8192},
                if fault==1{usize::MAX}else{input.capacity()*32},|chunk|{
                    let call=calls.get();calls.set(call+1);
                    if call==0{return match fault{2=>Ok(vec![Fr::zero()]),3=>Ok(vec![Fr::from(2u64);2]),
                        4=>Err("isolated chunk error".into()),5=>{let mut x=Vec::with_capacity(3);x.resize(2,Fr::zero());Ok(x)},
                        _=>Ok(input[2*chunk..2*chunk+2].to_vec())};}
                    Ok(input[2*chunk..2*chunk+2].to_vec())
                },&mut t);
            assert!(result.is_err());assert_eq!(transcript_tuple(&t),before);
            if fault<2{assert_eq!(calls.get(),0);}
        }
        for fault in 0..4{
            let calls=Cell::new(0usize);let mut t=Transcript::new(AB_DOMAIN);
            let result=crate::segment_adjacency::linear_for_test::prove(&d,8192,input.capacity()*32,|chunk|{
                let call=calls.get();calls.set(call+1);if call==8191{return match fault{
                    0=>Ok(vec![Fr::zero()]),1=>Ok(vec![Fr::from(2u64);2]),2=>Err("later isolated chunk error".into()),
                    _=>{let mut x=Vec::with_capacity(3);x.resize(2,Fr::zero());Ok(x)},
                };}Ok(input[2*chunk..2*chunk+2].to_vec())
            },&mut t);
            assert!(result.is_err());assert!(t.challenges()>0,"later padding load remains validated");
        }
        for n in [1,2,5,3073]{let layout=HeaderAdjacencyLayout::compile(n,if n==3073{12}else{3},[0;32],[0;32]).unwrap();
            assert!(layout.linear_descriptor_for_test().is_err());}
        let metadata=HeaderAdjacencyLayout::compile_metadata(3,2,0).unwrap();assert!(metadata.linear_descriptor_for_test().is_err());
        for n in [3,4]{let layout=HeaderAdjacencyLayout::compile(n,2,[0;32],[0;32]).unwrap();
            let native=layout.linear_descriptor_for_test().unwrap();assert!(native.validate(1<<22,16).is_ok());
            assert!(native.validate(1<<22,15).is_err());assert!(native.validate(1<<32,16).is_err());}
    }

    fn hex(bytes:&[u8])->String{bytes.iter().map(|b|format!("{b:02X}")).collect()}
    fn scalar_hex(value:&Fr)->String{hex(&crate::pcs::encode(value).unwrap())}
    fn io_json(io:crate::packed::PackedIoSnapshot)->serde_json::Value{
        assert_eq!((io.write_calls,io.write_bytes,io.sync_calls),(0,0,0));
        serde_json::json!({"read_calls":io.read_calls,"read_bytes":io.read_bytes,"read_ns":io.read_ns,
            "write_calls":io.write_calls,"write_bytes":io.write_bytes,"sync_calls":io.sync_calls})
    }
    fn proof_capacity(proof:&GkrProof)->usize{
        proof.layers.capacity()*std::mem::size_of::<LayerProofForCapacity>()+proof.layers.iter().map(|layer|
            layer.rounds.capacity()*std::mem::size_of::<Vec<Fr>>()
                +layer.rounds.iter().map(|r|r.capacity()*32).sum::<usize>()+layer.line_coefficients.capacity()*32).sum::<usize>()
    }
    type LayerProofForCapacity=crate::gkr::LayerProof;
    #[test]
    #[ignore="bounded N3/four-bank generic versus linear A/B; separate reviewed300s Job admission"]
    fn native_role5_linear_ab_bounded(){
        use ark_serialize::CanonicalSerialize;
        use std::{fs::OpenOptions,io::Write,time::Instant};
        let began=Instant::now();
        let out=std::path::PathBuf::from(std::env::var_os("NIPOPOW_ROLE5_LINEAR_AB_CAPTURE_DIR").expect("fresh A/B output directory"));
        assert!(out.is_absolute()&&out.to_string_lossy().len()<180&&!out.exists());std::fs::create_dir(&out).unwrap();
        let layout=HeaderAdjacencyLayout::compile(3,2,[0;32],[0;32]).unwrap();
        let descriptor=layout.linear_descriptor_for_test().unwrap();
        let mut bits=(0..524288usize).map(|i|(i.wrapping_mul(73)+(i>>3)+0x5A) as u8).collect::<Vec<_>>();
        let digest=|owner:usize,j:usize|if owner==2{Fr::zero()}else{mixed_bit(owner*256+j)};
        for owner in 0..3{for j in 0..256{for (wire,value) in [
            (descriptor.parent()[j],if owner==0{Fr::zero()}else{digest(owner-1,j)}),
            (descriptor.digest()[j],digest(owner,j))]{
            let index=owner*WIDTH+wire;let mask=1u8<<(index%8);
            if value.is_one(){bits[index/8]|=mask;}else{bits[index/8]&=!mask;}
        }}}
        assert!(bits[3*131072..].iter().any(|b|*b!=0));assert!(bits[3*131072..].iter().any(|b|*b!=255));
        let source_sha=hex(&crate::native_prefix_auth_plan::role0_sha256(&bits).unwrap());
        let source_path=out.join("source.bin");let mut f=OpenOptions::new().write(true).create_new(true).open(&source_path).unwrap();
        f.write_all(&bits).unwrap();f.sync_all().unwrap();drop(f);drop(bits);
        let before=std::fs::metadata(&source_path).unwrap();let source=crate::packed::PackedFile::open(&source_path,22).unwrap();
        let source_ns=began.elapsed().as_nanos();let mut marks=Vec::with_capacity(6);
        let mark=|name:&str,marks:&mut Vec<serde_json::Value>|{
            let item=serde_json::json!({"name":name,"elapsed_ns":began.elapsed().as_nanos()});
            if marks.is_empty(){println!();}println!("R5_LINEAR_PHASE {item}");std::io::stdout().flush().unwrap();marks.push(item);
        };
        mark("source_ready",&mut marks);
        source.reset_io_metrics();let calls=Cell::new(0u64);let fields=Cell::new(0u64);let capacity=Cell::new(0usize);
        let mut baseline_t=Transcript::new(AB_DOMAIN);let started=Instant::now();
        let baseline=prove(&layout,source.input_len(),|owner|{
            let x=crate::packed_rows::read_row(&source,WIDTH,owner)?;
            calls.set(calls.get()+1);fields.set(fields.get()+x.len() as u64);capacity.set(capacity.get().max(x.capacity()*32));Ok(x)
        },&mut baseline_t).unwrap();
        let baseline_ns=started.elapsed().as_nanos();let baseline_io=io_json(source.io_metrics_snapshot());
        assert!(!baseline.diagnostics.used_incremental_u&&!baseline.diagnostics.used_incremental_v);
        let baseline_packet=crate::gkr::encode_proof(&baseline.proof).unwrap();mark("baseline_complete",&mut marks);
        source.reset_io_metrics();let mut linear_t=Transcript::new(AB_DOMAIN);
        let retained=proof_capacity(&baseline.proof)+baseline.claim.point.capacity()*32+baseline_packet.capacity()
            +(baseline.diagnostics.trace.r.capacity()+baseline.diagnostics.trace.u.capacity()+baseline.diagnostics.trace.v.capacity())*32
            +out.capacity()*2+source_path.capacity()*2;
        let started=Instant::now();let (linear,linear_claim,stats)=prove_linear_for_test(&layout,&source,retained,&mut linear_t).unwrap();
        let linear_ns=started.elapsed().as_nanos();let linear_io=io_json(source.io_metrics_snapshot());
        assert_eq!(linear,baseline.proof);assert_eq!(linear_claim,baseline.claim);same_transcript(&baseline_t,&linear_t);
        let linear_packet=crate::gkr::encode_proof(&linear).unwrap();assert_eq!(linear_packet,baseline_packet);
        let proof_fields=44*3+2+23;assert_eq!(proof_fields,157);
        assert_eq!(baseline_packet.len(),proof_fields*Fr::zero().compressed_size());assert_eq!(baseline_packet.len(),5024);
        assert_eq!(stats.read_calls,[64,1088,1088,64]);assert_eq!(stats.high_fold_coordinates,[6,6]);
        assert_eq!(stats.initial_padding_chunks,16);assert!(!stats.helper_bounds_measured);
        assert_eq!(stats.preflight_bound_bytes,stats.retained_capacity_bytes+10597696);
        mark("linear_complete",&mut marks);
        let started=Instant::now();let mut verifier_counters=None;
        for packet in [&baseline_packet,&linear_packet]{
            let decoded=crate::gkr::decode_dimensions(&[22],packet).unwrap();assert_eq!(crate::gkr::encode_proof(&decoded).unwrap(),*packet);
            let mut verifier=Transcript::new(AB_DOMAIN);
            let claim=crate::gkr::verify_with_wiring(&[22],ROW_COUNT,&decoded,&mut verifier,|t|layout.bind(t),
                |_,r,u,v|layout.coefficients(r,u,v).map_err(|_|crate::gkr::GkrError::PointDimension)).unwrap();
            assert_eq!(claim,baseline.claim);same_transcript(&baseline_t,&verifier);verifier_counters=Some(transcript_tuple(&verifier));
        }
        let verify_ns=started.elapsed().as_nanos();mark("verify_complete",&mut marks);
        let started=Instant::now();
        assert_eq!(source.evaluate(&baseline.claim.point).unwrap(),baseline.claim.value);
        assert_eq!(source.evaluate(&linear_claim.point).unwrap(),linear_claim.value);
        let mle_ns=started.elapsed().as_nanos();mark("mle_complete",&mut marks);
        let after=std::fs::metadata(&source_path).unwrap();assert_eq!(before.len(),after.len());assert_eq!(before.modified().unwrap(),after.modified().unwrap());
        drop(source);let saved=std::fs::read(&source_path).unwrap();assert_eq!(saved.len(),524288);
        assert_eq!(hex(&crate::native_prefix_auth_plan::role0_sha256(&saved).unwrap()),source_sha);drop(saved);
        let baseline_sha=hex(&crate::native_prefix_auth_plan::role0_sha256(&baseline_packet).unwrap());
        let linear_sha=hex(&crate::native_prefix_auth_plan::role0_sha256(&linear_packet).unwrap());
        let total=began.elapsed().as_nanos();mark("export_ready",&mut marks);
        let report=serde_json::json!({"schema":"role5-linear-ab-diagnostic-v1","state":"AB_COMPLETE",
            "scope":{"active_owners":3,"padded_owners":4,"local_input_bits":20,"local_row_bits":9,"id_bits":256,
                "input_log":22,"row_log":11,"synthetic_boolean":true,"native32":false,"pcs_invoked":false,"full_history":false,"production":false},
            "source":{"bytes":524288,"sha256":source_sha,"padding_bank_nonzero":true,"identity_stable":true},
            "baseline":{"elapsed_ns":baseline_ns,"loader_calls":calls.get(),"reconstructed_fields":fields.get(),
                "loader_peak_capacity_bytes":capacity.get(),"modeled_scratch_clone_fields":43usize*4*WIDTH,
                "used_incremental_u":false,"used_incremental_v":false,"io":baseline_io},
            "linear":{"elapsed_ns":linear_ns,"stats":stats,"io":linear_io},
            "proof":{"bytes":5024,"baseline_sha256":baseline_sha,"linear_sha256":linear_sha,"equal":true,
                "point_hex":linear_claim.point.iter().map(scalar_hex).collect::<Vec<_>>(),"value_hex":scalar_hex(&linear_claim.value),
                "producer_counters":transcript_tuple(&linear_t),"verifier_counters":verifier_counters.unwrap(),
                "continuation_hex":scalar_hex(&linear_t.clone().challenge_scalar(AB_CONTINUATION)),
                "gkr_verifications":2,"source_mle_checks":2,"independent_verify":true,"source_mle_equal":true},
            "phase_marks":marks,"timing_ns":{"source":source_ns,"baseline":baseline_ns,"linear":linear_ns,
                "verify_pair":verify_ns,"mle_pair":mle_ns,"total_before_export":total}});
        let bytes=serde_json::to_vec(&report).unwrap();assert!(bytes.len()<=32768);
        for (name,data) in [("baseline.gkr",baseline_packet.as_slice()),("linear.gkr",linear_packet.as_slice()),("result.json",bytes.as_slice())]{
            let mut f=OpenOptions::new().write(true).create_new(true).open(out.join(name)).unwrap();f.write_all(data).unwrap();f.sync_all().unwrap();
        }
    }

    #[test]
    fn role5_cache_eviction_admission_and_faults(){
        super::cache_eviction_for_test::controls(literal);
    }

    #[test]
    #[ignore="closed eight-owner cache-eviction A/B; separately reviewed300s Job admission"]
    fn native_role5_cache_eviction_ab_bounded(){
        use super::cache_eviction_for_test as cache;
        use ark_serialize::CanonicalSerialize;
        use std::{fs::OpenOptions,io::Write,time::Instant};
        let began=Instant::now();
        let out=std::path::PathBuf::from(std::env::var_os("NIPOPOW_ROLE5_CACHE_AB_CAPTURE_DIR").expect("fresh cache A/B output directory"));
        assert!(out.is_absolute()&&out.to_string_lossy().len()<180&&!out.exists());
        // Pure producer preflight precedes source allocation and either producer.
        let _preflight=cache::Memory::model(cache::ModelGeometry::Cache8,512*1024*1024).unwrap();
        std::fs::create_dir(&out).unwrap();
        let layout=HeaderAdjacencyLayout::compile(7,3,[0;32],[0;32]).unwrap();
        let descriptor=layout.cache_eviction_descriptor_for_test().unwrap();
        let mut bits=(0..1048576usize).map(|i|(i.wrapping_mul(73)+(i>>3)+0x5A) as u8).collect::<Vec<_>>();
        let digest=|owner:usize,j:usize|if owner==6{Fr::zero()}else{mixed_bit(owner*256+j)};
        for owner in 0..7{for j in 0..256{for (wire,value) in [
            (descriptor.parent()[j],if owner==0{Fr::zero()}else{digest(owner-1,j)}),
            (descriptor.digest()[j],digest(owner,j))]{
            let index=owner*WIDTH+wire;let mask=1u8<<(index%8);
            if value.is_one(){bits[index/8]|=mask;}else{bits[index/8]&=!mask;}
        }}}
        assert!(bits[7*131072..].iter().any(|b|*b!=0));assert!(bits[7*131072..].iter().any(|b|*b!=255));
        let source_sha=hex(&crate::native_prefix_auth_plan::role0_sha256(&bits).unwrap());
        let source_path=out.join("source.bin");let mut f=OpenOptions::new().write(true).create_new(true).open(&source_path).unwrap();
        f.write_all(&bits).unwrap();f.sync_all().unwrap();drop(f);drop(bits);
        let before=std::fs::metadata(&source_path).unwrap();let source=crate::packed::PackedFile::open(&source_path,23).unwrap();
        let source_ns=began.elapsed().as_nanos();let mut marks=Vec::with_capacity(6);
        let mark=|name:&str,marks:&mut Vec<serde_json::Value>|{
            let item=serde_json::json!({"name":name,"elapsed_ns":began.elapsed().as_nanos()});
            if marks.is_empty(){println!();}println!("R5_CACHE_PHASE {item}");std::io::stdout().flush().unwrap();marks.push(item);
        };
        mark("source_ready",&mut marks);
        source.reset_io_metrics();let calls=Cell::new(0u64);let fields=Cell::new(0u64);let capacity=Cell::new(0usize);
        let mut baseline_t=Transcript::new(AB_DOMAIN);let started=Instant::now();
        let baseline=cache::prove(&layout,source.input_len(),|owner|{
            let x=crate::packed_rows::read_row(&source,WIDTH,owner)?;
            calls.set(calls.get()+1);fields.set(fields.get()+x.len() as u64);capacity.set(capacity.get().max(x.capacity()*32));Ok(x)
        },&mut baseline_t).unwrap();
        assert!(calls.get()>8,"cache-eviction fixture must reload beyond its eight owners");
        let baseline_ns=started.elapsed().as_nanos();let baseline_io=io_json(source.io_metrics_snapshot());
        let baseline_packet=crate::gkr::encode_proof(&baseline.proof).unwrap();mark("baseline_complete",&mut marks);
        source.reset_io_metrics();let mut linear_t=Transcript::new(AB_DOMAIN);
        let retained=proof_capacity(&baseline.proof)+baseline.claim.point.capacity()*32+baseline_packet.capacity()
            +(baseline.trace.r.capacity()+baseline.trace.u.capacity()+baseline.trace.v.capacity())*32
            +std::mem::size_of_val(&baseline.memory)+out.capacity()*2+source_path.capacity()*2;
        let started=Instant::now();let (linear,linear_claim,stats)=cache::linear(&layout,&source,retained,&mut linear_t).unwrap();
        let linear_ns=started.elapsed().as_nanos();let linear_io=io_json(source.io_metrics_snapshot());
        assert_eq!(linear,baseline.proof);assert_eq!(linear_claim,baseline.claim);same_transcript(&baseline_t,&linear_t);
        let linear_packet=crate::gkr::encode_proof(&linear).unwrap();assert_eq!(linear_packet,baseline_packet);
        let proof_fields=46*3+2+24;assert_eq!(proof_fields,164);
        assert_eq!(baseline_packet.len(),proof_fields*Fr::zero().compressed_size());assert_eq!(baseline_packet.len(),5248);
        assert_eq!(stats.read_calls,[128,2176,2176,128]);assert_eq!(stats.high_fold_coordinates,[7,7]);
        assert_eq!(stats.initial_padding_chunks,16);assert_eq!(stats.line_input_fields,1<<23);assert!(!stats.helper_bounds_measured);
        assert_eq!(stats.preflight_bound_bytes,stats.retained_capacity_bytes+10605248);
        mark("linear_complete",&mut marks);
        let started=Instant::now();let mut verifier_counters=None;
        for packet in [&baseline_packet,&linear_packet]{
            let decoded=crate::gkr::decode_dimensions(&[23],packet).unwrap();assert_eq!(crate::gkr::encode_proof(&decoded).unwrap(),*packet);
            let mut verifier=Transcript::new(AB_DOMAIN);
            let claim=crate::gkr::verify_with_wiring(&[23],1<<12,&decoded,&mut verifier,|t|layout.bind(t),
                |_,r,u,v|layout.coefficients(r,u,v).map_err(|_|crate::gkr::GkrError::PointDimension)).unwrap();
            assert_eq!(claim,baseline.claim);same_transcript(&baseline_t,&verifier);verifier_counters=Some(transcript_tuple(&verifier));
        }
        let verify_ns=started.elapsed().as_nanos();mark("verify_complete",&mut marks);
        let started=Instant::now();
        assert_eq!(source.evaluate(&baseline.claim.point).unwrap(),baseline.claim.value);
        assert_eq!(source.evaluate(&linear_claim.point).unwrap(),linear_claim.value);
        let mle_ns=started.elapsed().as_nanos();mark("mle_complete",&mut marks);
        let after=std::fs::metadata(&source_path).unwrap();assert_eq!(before.len(),after.len());assert_eq!(before.modified().unwrap(),after.modified().unwrap());
        drop(source);let saved=std::fs::read(&source_path).unwrap();assert_eq!(saved.len(),1048576);
        assert_eq!(hex(&crate::native_prefix_auth_plan::role0_sha256(&saved).unwrap()),source_sha);drop(saved);
        let baseline_sha=hex(&crate::native_prefix_auth_plan::role0_sha256(&baseline_packet).unwrap());
        let linear_sha=hex(&crate::native_prefix_auth_plan::role0_sha256(&linear_packet).unwrap());
        let total=began.elapsed().as_nanos();mark("export_ready",&mut marks);
        let report=serde_json::json!({"schema":"role5-cache-eviction-ab-diagnostic-v1","state":"AB_COMPLETE",
            "scope":{"active_owners":7,"padded_owners":8,"local_input_bits":20,"local_row_bits":9,"id_bits":256,
                "input_log":23,"row_log":12,"synthetic_boolean":true,"native32":false,"pcs_invoked":false,"full_history":false,"production":false},
            "source":{"bytes":1048576,"sha256":source_sha,"padding_bank_nonzero":true,"identity_stable":true},
            "baseline":{"elapsed_ns":baseline_ns,"loader_calls":calls.get(),"reconstructed_fields":fields.get(),
                "loader_peak_capacity_bytes":capacity.get(),"modeled_scratch_clone_fields":43usize*8*WIDTH,
                "used_incremental_u":false,"used_incremental_v":false,"io":baseline_io,"memory":baseline.memory},
            "linear":{"elapsed_ns":linear_ns,"stats":stats,"io":linear_io},
            "proof":{"bytes":5248,"baseline_sha256":baseline_sha,"linear_sha256":linear_sha,"equal":true,
                "point_hex":linear_claim.point.iter().map(scalar_hex).collect::<Vec<_>>(),"value_hex":scalar_hex(&linear_claim.value),
                "producer_counters":transcript_tuple(&linear_t),"verifier_counters":verifier_counters.unwrap(),
                "continuation_hex":scalar_hex(&linear_t.clone().challenge_scalar(AB_CONTINUATION)),
                "gkr_verifications":2,"source_mle_checks":2,"independent_verify":true,"source_mle_equal":true},
            "phase_marks":marks,"timing_ns":{"source":source_ns,"baseline":baseline_ns,"linear":linear_ns,
                "verify_pair":verify_ns,"mle_pair":mle_ns,"total_before_export":total}});
        let bytes=serde_json::to_vec(&report).unwrap();assert!(bytes.len()<=32768);
        for (name,data) in [("baseline.gkr",baseline_packet.as_slice()),("linear.gkr",linear_packet.as_slice()),("result.json",bytes.as_slice())]{
            let mut f=OpenOptions::new().write(true).create_new(true).open(out.join(name)).unwrap();f.write_all(data).unwrap();f.sync_all().unwrap();
        }
    }

    #[test]
    fn native_adjacency_endpoint_partition() {
        // A reduced static fixture isolates source-row owner versus endpoint owner.
        let small = vec![
            Term { row: 512 + 3, gate: Gate {
                left: 7, right: WIDTH + 9, c0: Fr::from(2u64),
                c1: Fr::from(3u64), c2: Fr::from(5u64), c3: Fr::from(7u64),
            }},
            Term { row: 2 * 512 + 259, gate: Gate {
                left: 2 * WIDTH + 11, right: 0, c0: -Fr::one(),
                c1: Fr::one(), c2: Fr::zero(), c3: Fr::zero(),
            }},
        ];
        let (left, right) = partition(&small).unwrap();
        assert_eq!(left[0], vec![0]);
        assert_eq!(left[2], vec![1]);
        assert_eq!(right[0], vec![1]);
        assert_eq!(right[1], vec![0]);
        assert_eq!(sparse_stream_roster::global_edge_row(1, 3, 2, 9, 0, &[9]).unwrap(), small[0].row);
        assert!(check_edge_identity(&small[0], 0, 3).is_err());
        assert!(check_edge_identity(&small[0], 1, 4).is_err());
        for coordinate in 0..3 {
            let mut mutant = small.clone();
            match coordinate {
                0 => mutant[0].row = ROW_COUNT,
                1 => mutant[0].gate.left = INPUT_LEN,
                _ => mutant[0].gate.right = INPUT_LEN,
            }
            assert!(partition(&mutant).is_err());
        }

        for n in [3usize, 4] {
            let start = [0xA5u8; 32];
            let tip = [0x5Au8; 32];
            let layout = HeaderAdjacencyLayout::compile(n as u64, 2, start, tip).unwrap();
            let frozen = FrozenAdjacency::freeze(&layout, INPUT_LEN).unwrap();
            let expected = reference(n, &start, &tip);
            assert_eq!(frozen.terms, expected);
            assert_eq!(frozen.terms.len(), 256 * (n + 1));
            assert_eq!(frozen.terms.capacity(), 256 * (n + 1));
            assert_eq!(frozen.left.iter().map(Vec::capacity).sum::<usize>(), expected.len());
            assert_eq!(frozen.right.iter().map(Vec::capacity).sum::<usize>(), expected.len());
            for is_left in [true, false] {
                let mut covered = vec![0usize; expected.len()];
                for slot in 0..COPIES {
                    let mut ordered: Vec<Term> = Vec::new();
                    frozen.visit_endpoint(is_left, slot, &mut |edge| {
                        assert_eq!(edge.term.row, sparse_stream_roster::global_edge_row(
                            edge.source_slot, edge.family_row, 2, 9, 0, &[9],
                        ).unwrap());
                        assert_eq!(edge.source_slot, edge.term.row >> 9);
                        let endpoint = if is_left { edge.term.gate.left } else { edge.term.gate.right };
                        assert_eq!(endpoint / WIDTH, slot);
                        ordered.push(edge.term);
                        Ok(())
                    }).unwrap();
                    let indices = if is_left { &frozen.left[slot] } else { &frozen.right[slot] };
                    assert_eq!(ordered, indices.iter().map(|&i| expected[i].clone()).collect::<Vec<_>>());
                    for &index in indices { covered[index] += 1; }
                }
                assert!(covered.iter().all(|&count| count == 1));
            }

            let r = point(11, 2);
            let u = point(22, 5);
            let v = point(22, 9);
            let analytical = layout.coefficients(&r, &u, &v).unwrap();
            assert_eq!(literal(&expected, &r, &u, &v), analytical);
            for channel in 0..4 {
                let mut mutant = frozen.clone();
                match channel {
                    0 => mutant.terms[0].gate.c0 += Fr::one(),
                    1 => mutant.terms[0].gate.c1 += Fr::one(),
                    2 => mutant.terms[0].gate.c2 += Fr::one(),
                    _ => mutant.terms[0].gate.c3 += Fr::one(),
                }
                assert!(mutant.validate(&layout, INPUT_LEN).is_err());
                assert_ne!(literal(&mutant.terms, &r, &u, &v), analytical);
            }
            reject_mutant(&layout, &frozen, |m| m.terms[0].row += 1);
            reject_mutant(&layout, &frozen, |m| m.terms[256].row -= 512);
            reject_mutant(&layout, &frozen, |m| m.terms[0].gate.left += 1);
            reject_mutant(&layout, &frozen, |m| m.terms[256].gate.right -= WIDTH);
            reject_mutant(&layout, &frozen, |m| m.terms[0].gate.right = 1);
            reject_mutant(&layout, &frozen, |m| m.terms[0].gate.c0 += Fr::one());
            let last = frozen.terms.len() - 1;
            reject_mutant(&layout, &frozen, |m| m.terms[last].gate.c0 += Fr::one());
            reject_mutant(&layout, &frozen, |m| { m.terms.remove(0); });
            reject_mutant(&layout, &frozen, |m| m.terms[1] = m.terms[0].clone());
            reject_mutant(&layout, &frozen, |m| m.terms.swap(0, 1));
            reject_mutant(&layout, &frozen, |m| m.left[0][0] = m.left[0][1]);
            reject_mutant(&layout, &frozen, |m| m.right[0].swap(0, 1));
            reject_mutant(&layout, &frozen, |m| m.left.swap(0, 1));
            reject_mutant(&layout, &frozen, |m| m.right.swap(0, 1));
            if n == 3 {
                // These are inactive rows and an inactive owner, not endpoint advice.
                assert!(frozen.terms.iter().all(|t| t.row < 1536));
                reject_mutant(&layout, &frozen, |m| m.terms[0].row = 1536);
                reject_mutant(&layout, &frozen, |m| m.terms[0].row = 256);
            }
            let mut sink_calls = 0usize;
            assert!(frozen.visit_endpoint(true, COPIES, &mut |_| {
                sink_calls += 1; Ok(())
            }).is_err());
            assert_eq!(sink_calls, 0);

            let bad = [
                (0, 2, 22, 11, INPUT_LEN, ROW_COUNT, expected.len(), INPUT_LEN),
                (1, 2, 22, 11, INPUT_LEN, ROW_COUNT, expected.len(), INPUT_LEN),
                (2, 2, 22, 11, INPUT_LEN, ROW_COUNT, expected.len(), INPUT_LEN),
                (5, 2, 22, 11, INPUT_LEN, ROW_COUNT, expected.len(), INPUT_LEN),
                (u64::MAX, 2, 22, 11, INPUT_LEN, ROW_COUNT, expected.len(), INPUT_LEN),
                (n as u64, 21, 41, 30, INPUT_LEN, ROW_COUNT, expected.len(), INPUT_LEN),
                (n as u64, usize::MAX, 22, 11, INPUT_LEN, ROW_COUNT, expected.len(), INPUT_LEN),
                (n as u64, 2, 25, 11, INPUT_LEN, ROW_COUNT, expected.len(), INPUT_LEN),
                (n as u64, 2, 22, 25, INPUT_LEN, ROW_COUNT, expected.len(), INPUT_LEN),
                (n as u64, 2, 22, 11, INPUT_LEN - 1, ROW_COUNT, expected.len(), INPUT_LEN),
                (n as u64, 2, 22, 11, INPUT_LEN, ROW_COUNT - 1, expected.len(), INPUT_LEN),
                (n as u64, 2, 22, 11, INPUT_LEN, ROW_COUNT, expected.len() - 1, INPUT_LEN),
            ];
            for args in bad {
                assert!(admit_dimensions(args.0, args.1, args.2, args.3, args.4, args.5, args.6, args.7).is_err());
            }
            let loads = Cell::new(0usize);
            let mut t = Transcript::new(b"native-adjacency-invalid-admission");
            let before = t.clone().challenge_scalar(b"unchanged");
            assert!(prove(&layout, INPUT_LEN - 1, |_| {
                loads.set(loads.get() + 1); Err("loader must not run".into())
            }, &mut t).is_err());
            assert_eq!(loads.get(), 0);
            assert_eq!(t.challenges(), 0);
            assert_eq!(before, t.clone().challenge_scalar(b"unchanged"));
        }
    }
}

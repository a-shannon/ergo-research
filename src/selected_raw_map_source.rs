//! Test-only q9 RAW-to-Map staging. Scattered checked bytes do not authenticate
//! a native parent, a global U certificate, or a full H21 proof.
use ark_bn254::Fr;
use ark_ff::{One,Zero};
use num_bigint::{BigInt,BigUint};
use std::collections::{BTreeMap,BTreeSet};
use crate::{bank53_map,h21_row_support::{relocate,Family},
    legacy_envelope_map::{Map,Binding,Import,Inputs,Kind,D_LOCAL,T_LOCAL},
    native_owner_exports::NativeExports,packed_owner_assembly::{NativePrefix,validate_native_plan_input},
    work_tree_history_plan::WorkTreeHistoryPlan,
    q9_selected_raw_fixture::{CheckedQ9RawFixture,Q9RawIdentity},sparse::Term};

const OWNER:usize=10175;
const WIDTH:usize=1<<20;
const HELPERS:usize=5757;
const HELPER_BASE:usize=671744;
const READ_BITS:usize=2592;
const TERM_COUNT:usize=68233;
const POLICY:&str="selected-raw-q9-upper-only-e55-c0-v1";
const Q9_HEIGHTS:[usize;10]=[2048,3072,4096,5120,6144,7168,8192,9216,10176,10177];

#[derive(Clone,Debug,PartialEq,Eq)]
struct SourceBinding {policy:&'static str,authority:Q9RawIdentity,map:Binding,owner:usize,context:usize}

// Native authority is separate from the unchanged upper-only Map binding.
// Comparing this metadata alone can never construct a NativeQ9Binding.
#[derive(Clone,Debug,PartialEq,Eq)]
struct NativeParentIdentity {
    headers:u64,slot_log:usize,slots:usize,genuine:usize,leaves:usize,
    root:[u8;32],total:[u8;28],profile:[u8;32],profiles:Vec<u8>,source:SourceBinding,
}
impl NativeParentIdentity {
    fn from_objects(parent:&WorkTreeHistoryPlan,native:&NativePrefix,source:SourceBinding)->Result<Self,String> {
        if parent.headers()!=1_827_840||parent.slot_log()!=21||parent.slots()!=1<<21
            ||parent.descriptor().genuine!=1_827_839||parent.descriptor().leaves!=1<<21 {
            return Err("native q9 requires full H21 parent".into());
        }
        validate_native_plan_input(parent,native)?;
        let profiles=serde_json::to_vec(&(parent.fixed_profile(),parent.leaf_profile(),parent.work_profile()))
            .map_err(|e|format!("native parent profiles: {e}"))?;
        Ok(Self{headers:parent.headers(),slot_log:parent.slot_log(),slots:parent.slots(),
            genuine:parent.descriptor().genuine,leaves:parent.descriptor().leaves,
            root:native.root(),total:native.total_be28(),profile:native.profile(),profiles,source})
    }
}
fn compare_native_identity(actual:&NativeParentIdentity,expected:&NativeParentIdentity)->Result<(),String> {
    if (actual.headers,actual.slot_log,actual.slots,actual.genuine,actual.leaves)
        !=(expected.headers,expected.slot_log,expected.slots,expected.genuine,expected.leaves) {
        return Err("native parent geometry binding".into());
    }
    if actual.root!=expected.root{return Err("native parent root binding".into());}
    if actual.total!=expected.total{return Err("native parent total binding".into());}
    if actual.profile!=expected.profile||actual.profiles!=expected.profiles{return Err("native parent profile binding".into());}
    if actual.source!=expected.source{return Err("native Map/source dispatch binding".into());}
    Ok(())
}
fn compare_raw(height:usize,selected:&[u8],native:&[u8])->Result<(),String> {
    if selected!=native{return Err(format!("native q9 RAW identity at height {height}"));}Ok(())
}
fn compare_native_reads(actual:&BTreeMap<usize,Fr>,expected:&BTreeMap<usize,Fr>)->Result<(),String> {
    if expected.len()!=READ_BITS||actual!=expected{return Err("native physical READ address/value binding".into());}Ok(())
}

/// Code-owned native seal. Retained immutable references prevent a caller from
/// substituting a new parent or source after construction. There is no loader
/// or constructor from a root, receipt, serialized metadata, or READ map.
pub(crate) struct NativeQ9Binding<'a> {
    parent:&'a WorkTreeHistoryPlan,native:&'a NativePrefix,fixture:&'a CheckedQ9RawFixture,
    identity:NativeParentIdentity,reads:BTreeMap<usize,Fr>,
}
impl<'a> NativeQ9Binding<'a> {
    pub(crate) fn from_native(parent:&'a WorkTreeHistoryPlan,native:&'a NativePrefix,
        fixture:&'a CheckedQ9RawFixture)->Result<Self,String> {
        let source=SelectedRawMapSource::new(fixture)?;
        let identity=NativeParentIdentity::from_objects(parent,native,source.binding.clone())?;
        for height in Q9_HEIGHTS {compare_raw(height,fixture.checked_raw(height as u32)?,native.raw(height)?)?;}
        let reads=source.imports(&source.map.imports(OWNER as u64)?)?.1;
        let exports=NativeExports::new_for_history(parent,native)?;
        let expected=reads.keys().map(|q|exports.bit(*q).map(|bit|(*q,Fr::from(u64::from(bit)))))
            .collect::<Result<BTreeMap<_,_>,_>>()?;
        compare_native_reads(&reads,&expected)?;
        Ok(Self{parent,native,fixture,identity,reads})
    }
    fn check_source(&self,source:&SelectedRawMapSource<'_>)->Result<(),String> {
        source.check_binding()?;
        let current=NativeParentIdentity::from_objects(self.parent,self.native,source.binding.clone())?;
        compare_native_identity(&self.identity,&current)?;
        for height in Q9_HEIGHTS {
            let raw=self.native.raw(height)?;
            compare_raw(height,self.fixture.checked_raw(height as u32)?,raw)?;
            compare_raw(height,source.fixture.checked_raw(height as u32)?,raw)?;
        }Ok(())
    }
    fn check_reads(&self,reads:&BTreeMap<usize,Fr>)->Result<(),String> {
        let exports=NativeExports::new_for_history(self.parent,self.native)?;
        let fresh=self.reads.keys().map(|q|exports.bit(*q).map(|bit|(*q,Fr::from(u64::from(bit)))))
            .collect::<Result<BTreeMap<_,_>,_>>()?;
        compare_native_reads(&self.reads,&fresh)?;
        compare_native_reads(reads,&fresh)
    }
    pub(crate) fn headers(&self)->u64{self.identity.headers}
    pub(crate) fn slot_log(&self)->usize{self.identity.slot_log}
    pub(crate) fn root(&self)->[u8;32]{self.identity.root}
    pub(crate) fn total_be28(&self)->[u8;28]{self.identity.total}
    pub(crate) fn profile(&self)->[u8;32]{self.identity.profile}
    pub(crate) fn selected_read_count(&self)->usize{self.reads.len()}
    pub(crate) fn selected_raw_hashes(&self)->Result<Vec<(usize,[u8;32])>,String> {
        Q9_HEIGHTS.into_iter().map(|height|crate::native_prefix_auth_plan::role0_sha256(
            self.fixture.checked_raw(height as u32)?).map(|digest|(height,digest))).collect()
    }
    pub(crate) fn selected_read_digest(&self)->Result<[u8;32],String> {
        let mut bytes=Vec::with_capacity(READ_BITS*9);
        for (address,value) in &self.reads {
            bytes.extend_from_slice(&u64::try_from(*address).map_err(|_|"native READ digest address range")?.to_le_bytes());
            bytes.push(if value.is_zero(){0}else if value.is_one(){1}else{return Err("native READ digest nonbit".into());});
        }
        crate::native_prefix_auth_plan::role0_sha256(&bytes)
    }
}

#[derive(Clone,Debug,PartialEq,Eq)]
enum PublicationAuthority {SelectedRawFixture,NativeParent(NativeParentIdentity)}

/// A native batch cannot be constructed from an ordinary selected batch by a
/// caller. Every validation/publication still requires the live native seal.
#[derive(Clone,Debug,PartialEq,Eq)]
pub(crate) struct NativeQ9MapBatch {selected:SelectedRawMapBatch,identity:NativeParentIdentity}
impl NativeQ9MapBatch {
    pub(crate) fn counts(&self)->(usize,usize,usize){
        (self.selected.reads.len(),self.selected.helpers.len(),self.selected.terms.len())
    }
    pub(crate) fn read_cells(&self)->impl Iterator<Item=(usize,Fr)>+'_ {
        self.selected.reads.iter().map(|(&address,&value)|(address,value))
    }
    pub(crate) fn helper_cells(&self)->impl Iterator<Item=(usize,Fr)>+'_ {
        self.selected.helpers.iter().map(|(&address,&value)|(address,value))
    }
    pub(crate) fn terms(&self)->&[Term]{&self.selected.terms}
}

/// The sole constructor takes checked immutable RAW custody, never caller
/// imports, witness values, terms, or claimed native root/total metadata.
pub(crate) struct SelectedRawMapSource<'a> {fixture:&'a CheckedQ9RawFixture,map:Map,binding:SourceBinding}
impl<'a> SelectedRawMapSource<'a> {
    pub(crate) fn new(fixture:&'a CheckedQ9RawFixture)->Result<Self,String> {
        if fixture.identity()!=Q9RawIdentity::SelectedRawFixture {return Err("selected RAW authority".into());}
        let map=Map::new_modern_global_u(1_827_840,21,55)?;
        let binding=SourceBinding {policy:POLICY,authority:fixture.identity(),map:map.binding(),owner:OWNER,context:0};
        Ok(Self{fixture,map,binding})
    }
    fn check_binding(&self)->Result<(),String> {
        let expected=Map::new_modern_global_u(1_827_840,21,55)?.binding();
        if self.fixture.identity()!=Q9RawIdentity::SelectedRawFixture || self.binding.authority!=self.fixture.identity()
            ||self.binding.policy!=POLICY||self.binding.owner!=OWNER||self.binding.context!=0
            ||self.binding.map!=expected||self.map.binding()!=expected {
            return Err("selected RAW Map binding".into());
        }Ok(())
    }
    // Re-decode immutable canonical RAW bytes on every call. In particular,
    // validation must not trust values or merely READ keys carried by a batch.
    fn imports(&self,requested:&[Import])->Result<(Inputs,BTreeMap<usize,Fr>),String> {
        self.check_binding()?;
        let canonical=self.map.imports(OWNER as u64)?;
        if canonical.len()!=18||canonical!=requested
            ||requested.iter().copied().collect::<BTreeSet<_>>().len()!=18 {
            return Err("exact import census".into());
        }
        let mut inputs=Inputs::default();let mut reads=BTreeMap::new();
        for imp in requested {
            let offset=match (imp.kind,imp.local,imp.width) {
                (Kind::Difficulty,D_LOCAL,224)=>2,
                (Kind::Timestamp,T_LOCAL,64)=>1,
                _=>return Err("typed RAW import".into()),
            };
            let height=u32::try_from(imp.owner.checked_add(offset).ok_or("RAW height overflow")?)
                .map_err(|_|"RAW height range")?;
            let raw=self.fixture.checked_raw(height)?;
            let header=ergo_header_core::Header::decode(raw,None).map_err(|e|format!("RAW import decode: {e:?}"))?;
            if header.height!=height||header.encode().map_err(|e|format!("RAW import encode: {e:?}"))?!=raw {
                return Err("RAW import canonical height".into());
            }
            let word=match imp.kind {
                Kind::Difficulty=>{
                    let d=crate::work_tree_work::native_decode(header.n_bits)?;
                    if d.bits()>224||d==num_bigint::BigUint::from(0u8){return Err("RAW D224 range".into());}
                    BigInt::from(d)
                },
                Kind::Timestamp=>BigInt::from(header.timestamp),
            };
            inputs.put(&self.map,*imp,&word)?;
            for bit in 0..imp.width {
                let address=self.map.input_index(*imp,bit)?;
                let value=Fr::from(u64::from(inputs.bit(imp.owner,imp.local+bit)?));
                if reads.insert(address,value).is_some(){return Err("duplicate READ address".into());}
            }
        }
        if reads.len()!=READ_BITS{return Err("RAW READ bit census".into());}
        Ok((inputs,reads))
    }
    fn terms(&self)->Result<Vec<Term>,String> {
        let terms=bank53_map::map_owner_terms(&self.map,OWNER as u64,0)?.iter()
            .map(|t|relocate(Family::Map(0),OWNER,t)).collect::<Result<Vec<_>,_>>()?;
        if terms.len()!=TERM_COUNT{return Err("source term census".into());}Ok(terms)
    }
    fn stage_requested(&self,requested:&[Import])->Result<SelectedRawMapBatch,String> {
        let (inputs,reads)=self.imports(requested)?;
        let generated=self.map.generate(OWNER as u64,&inputs)?;self.map.check_row(&generated)?;
        let mut helpers=BTreeMap::new();
        for bit in 0..HELPERS {
            if helpers.insert(OWNER*WIDTH+HELPER_BASE+bit,Fr::from(u64::from(generated.bit(crate::legacy_envelope_map::BASE+bit)?))).is_some(){
                return Err("duplicate helper writer".into());
            }
        }
        Ok(SelectedRawMapBatch{binding:self.binding.clone(),imports:requested.to_vec(),reads,helpers,terms:self.terms()?})
    }
    pub(crate) fn stage(&self)->Result<SelectedRawMapBatch,String> {
        self.stage_requested(&self.map.imports(OWNER as u64)?)
    }
    pub(crate) fn validate(&self,b:&SelectedRawMapBatch)->Result<(),String> {
        self.check_binding()?;
        if b.binding!=self.binding{return Err("batch binding".into());}
        if b.imports!=self.map.imports(OWNER as u64)?{return Err("exact import census".into());}
        let expected_helpers=(0..HELPERS).map(|k|OWNER*WIDTH+HELPER_BASE+k).collect::<BTreeSet<_>>();
        if b.helpers.keys().copied().collect::<BTreeSet<_>>()!=expected_helpers{return Err("helper writer census".into());}
        if b.terms!=self.terms()?{return Err("ordered term census".into());}
        let fresh_reads=self.imports(&b.imports)?.1;
        if b.reads!=fresh_reads{return Err("RAW READ address/value binding".into());}
        if b.helpers.values().chain(b.reads.values()).any(|v|!v.is_zero()&&!v.is_one()){
            return Err("helper/READ bitness".into());
        }
        if let Some((row,_))=residuals(b)?.into_iter().find(|(_,z)|!z.is_zero()){
            return Err(format!("Map residual ROW {row}"));
        }Ok(())
    }
    pub(crate) fn publish(&self,d:&mut Destination,b:SelectedRawMapBatch)->Result<(),String> {
        self.validate(&b)?;
        self.publish_validated(d,b,PublicationAuthority::SelectedRawFixture)
    }
    pub(crate) fn stage_native(&self,seal:&NativeQ9Binding<'_>)->Result<NativeQ9MapBatch,String> {
        seal.check_source(self)?;
        let selected=self.stage()?;self.validate(&selected)?;seal.check_reads(&selected.reads)?;
        Ok(NativeQ9MapBatch{selected,identity:seal.identity.clone()})
    }
    pub(crate) fn validate_native(&self,b:&NativeQ9MapBatch,seal:&NativeQ9Binding<'_>)->Result<(),String> {
        seal.check_source(self)?;compare_native_identity(&b.identity,&seal.identity)?;
        self.validate(&b.selected)?;seal.check_reads(&b.selected.reads)
    }
    pub(crate) fn publish_native(&self,d:&mut Destination,b:NativeQ9MapBatch,seal:&NativeQ9Binding<'_>)->Result<(),String> {
        self.validate_native(&b,seal)?;
        self.publish_validated(d,b.selected,PublicationAuthority::NativeParent(b.identity))
    }
    fn publish_validated(&self,d:&mut Destination,b:SelectedRawMapBatch,authority:PublicationAuthority)->Result<(),String> {
        let rows=destination_preflight(d,&b.helpers,&b.terms)?;
        // All checks precede this point. Multiple monomials of this relation at
        // one ROW share its writer. Native-source READS are never X writes.
        d.published=true;
        d.authority=Some(authority);
        d.cells.extend(b.helpers);
        for row in rows {d.rows.insert(row,POLICY);}
        Ok(())
    }
}
#[derive(Clone,Debug,PartialEq,Eq)]
pub(crate) struct SelectedRawMapBatch {
    binding:SourceBinding,imports:Vec<Import>,reads:BTreeMap<usize,Fr>,helpers:BTreeMap<usize,Fr>,terms:Vec<Term>,
}
#[derive(Clone,Debug,Default,PartialEq,Eq)]
pub(crate) struct Destination {
    published:bool,authority:Option<PublicationAuthority>,cells:BTreeMap<usize,Fr>,rows:BTreeMap<usize,&'static str>,
}
impl Destination {
    pub(crate) fn is_native_parent_bound(&self)->bool {
        self.published&&matches!(&self.authority,Some(PublicationAuthority::NativeParent(_)))
    }
}
fn destination_preflight(d:&Destination,helpers:&BTreeMap<usize,Fr>,terms:&[Term])->Result<BTreeSet<usize>,String> {
    if d.published{return Err("duplicate owner batch".into());}
    if helpers.keys().any(|q|d.cells.contains_key(q)){return Err("destination X collision".into());}
    let rows=terms.iter().map(|t|t.row).collect::<BTreeSet<_>>();
    if rows.iter().any(|q|d.rows.contains_key(q)){return Err("destination ROW collision".into());}Ok(rows)
}
fn residuals(b:&SelectedRawMapBatch)->Result<BTreeMap<usize,Fr>,String> {
    let read=|q|b.helpers.get(&q).or_else(||b.reads.get(&q)).copied().ok_or_else(||format!("missing active X {q}"));
    let mut sums=BTreeMap::new();
    for t in &b.terms {
        let g=&t.gate;let mut z=g.c0;
        if !g.c1.is_zero(){z+=g.c1*read(g.left)?;}
        if !g.c2.is_zero(){z+=g.c2*read(g.right)?;}
        if !g.c3.is_zero(){z+=g.c3*read(g.left)?*read(g.right)?;}
        *sums.entry(t.row).or_insert(Fr::zero())+=z;
    }Ok(sums)
}

/// A source-derived, deliberately unsealed counterexample for the scoped
/// Work/Map/HEADER evaluator. Never admitted by validate_native or published.
#[cfg(test)]
pub(crate) struct CoherentAlternate {
    pub(crate) nbits:u32,
    pub(crate) difficulty:BigUint,
    pub(crate) batch:NativeQ9MapBatch,
}
#[cfg(test)]
pub(crate) fn coherent_nbits_alternate_for_test(source:&SelectedRawMapSource<'_>,
    seal:&NativeQ9Binding<'_>)->Result<CoherentAlternate,String> {
    let honest=source.stage_native(seal)?;
    let d=*honest.selected.imports.iter().find(|i|i.owner==OWNER as u64&&i.kind==Kind::Difficulty)
        .ok_or("coherent alternate D import missing")?;
    if (d.local,d.width)!=(D_LOCAL,224){return Err("coherent alternate D port changed".into());}
    let original_nbits=seal.native.compact_n_bits(OWNER+2)?;
    let original_d=crate::work_tree_work::native_decode(original_nbits)?;
    let (lower_be,_)=seal.native.interval(OWNER+2)?;
    let lower=BigUint::from_bytes_be(&lower_be);
    for mantissa_bit in 0..23 {
        let nbits=original_nbits^(1u32<<mantissa_bit);
        let Ok(difficulty)=crate::work_tree_work::native_decode(nbits) else {continue};
        if difficulty==original_d || (&lower+&difficulty).bits()>224 {continue;}
        let (mut inputs,_)=source.imports(&honest.selected.imports)?;
        inputs.put(&source.map,d,&BigInt::from(difficulty.clone()))?;
        let Ok(generated)=source.map.generate(OWNER as u64,&inputs) else {continue};
        if source.map.check_row(&generated).is_err(){continue;}
        let mut batch=honest.clone();
        for bit in 0..224 {
            let address=source.map.input_index(d,bit)?;
            *batch.selected.reads.get_mut(&address).ok_or("coherent alternate D READ missing")?=
                Fr::from(u64::from(difficulty.bit(bit as u64)));
        }
        for bit in 0..HELPERS {
            *batch.selected.helpers.get_mut(&(OWNER*WIDTH+HELPER_BASE+bit))
                .ok_or("coherent alternate Map helper missing")?=
                Fr::from(u64::from(generated.bit(crate::legacy_envelope_map::BASE+bit)?));
        }
        if !residuals(&batch.selected)?.values().all(|z|z.is_zero()) {
            return Err("coherent alternate Map residual".into());
        }
        match seal.check_reads(&batch.selected.reads) {
            Err(error) if error=="native physical READ address/value binding"=>{},
            Err(error)=>return Err(format!("coherent alternate wrong seal rejection: {error}")),
            Ok(())=>return Err("coherent alternate unexpectedly resealed".into()),
        }
        return Ok(CoherentAlternate {nbits,difficulty,batch});
    }
    Err("no valid coherent nBits/D alternate for selected RAW".into())
}

/// Full-fixture negatives for the H21 hook. Requires the existing live source
/// and native seal; never constructs a NativePrefix, parent plan or new seal.
/// All mutated data and the nonempty publication destination remain local.
#[cfg(test)]
pub(crate) fn assert_native_q9_faults_for_test(source:&SelectedRawMapSource<'_>,
    seal:&NativeQ9Binding<'_>)->Result<(usize,usize,usize,usize),String> {
    fn need(ok:bool,message:&str)->Result<(),String>{if ok{Ok(())}else{Err(message.into())}}
    fn rejected(result:Result<(),String>,expected:&str)->Result<(),String>{
        match result {
            Err(error) if error==expected=>Ok(()),
            Err(error)=>Err(format!("native live fault phase: expected {expected}, got {error}")),
            Ok(())=>Err(format!("native live fault accepted: {expected}")),
        }
    }
    let honest=source.stage_native(seal)?;
    source.validate_native(&honest,seal)?;
    for fault in 0..4 {
        let mut bad=seal.identity.clone();let expected=match fault {
            0=>{bad.root[0]^=1;"native parent root binding"},
            1=>{bad.total[0]^=1;"native parent total binding"},
            2=>{bad.profile[0]^=1;"native parent profile binding"},
            _=>{bad.headers-=1;"native parent geometry binding"},
        };
        rejected(compare_native_identity(&bad,&seal.identity),expected)?;
    }

    let raw=seal.fixture.checked_raw(2048)?;
    let mut header=ergo_header_core::Header::decode(raw,None)
        .map_err(|e|format!("native live RAW decode: {e:?}"))?;
    let original_parent=header.parent_id;let original_nbits=header.n_bits;
    let original_timestamp=header.timestamp;let original_height=header.height;
    let original_d=crate::work_tree_work::native_decode(header.n_bits)?;
    header.parent_id[0]^=1;
    let changed=header.encode().map_err(|e|format!("native live RAW encode: {e:?}"))?;
    let roundtrip=ergo_header_core::Header::decode(&changed,None)
        .map_err(|e|format!("native live RAW roundtrip decode: {e:?}"))?;
    need(roundtrip.encode().map_err(|e|format!("native live RAW roundtrip encode: {e:?}"))?==changed,
        "native live RAW failed canonical roundtrip")?;
    need(changed!=raw&&roundtrip.parent_id!=original_parent,"native live RAW mutation did not change identity")?;
    need(original_height==2048&&roundtrip.height==original_height&&roundtrip.n_bits==original_nbits
        &&roundtrip.timestamp==original_timestamp&&crate::work_tree_work::native_decode(roundtrip.n_bits)?==original_d,
        "native live RAW mutation changed D/T/height")?;
    rejected(compare_raw(2048,&changed,seal.native.raw(2048)?),"native q9 RAW identity at height 2048")?;

    let mut forged=honest.clone();
    let d=*honest.selected.imports.iter().find(|i|i.owner==OWNER as u64&&i.kind==Kind::Difficulty)
        .ok_or("native live destination D import missing")?;
    need((d.local,d.width)==(987674,224),"native live destination D port")?;
    let (mut inputs,_)=source.imports(&honest.selected.imports)?;
    need(inputs.get(d)?>BigInt::from(1u8),"native live D bit0 mutation would be zero")?;
    let address=source.map.input_index(d,0)?;
    let original=*forged.selected.reads.get(&address).ok_or("native live D READ missing")?;
    *forged.selected.reads.get_mut(&address).ok_or("native live D READ missing")?=Fr::one()-original;
    inputs.flip(d,0)?;
    let replacement=source.map.generate(OWNER as u64,&inputs)?;source.map.check_row(&replacement)?;
    for bit in 0..HELPERS {
        *forged.selected.helpers.get_mut(&(OWNER*WIDTH+HELPER_BASE+bit)).ok_or("native live helper missing")?=
            Fr::from(u64::from(replacement.bit(crate::legacy_envelope_map::BASE+bit)?));
    }
    need(forged.identity==honest.identity&&forged.selected.binding==honest.selected.binding
        &&forged.selected.imports==honest.selected.imports&&forged.selected.terms==honest.selected.terms
        &&forged.selected.reads!=honest.selected.reads,"native live coherent mutant changed census/identity")?;
    need(residuals(&forged.selected)?.values().all(|z|z.is_zero()),"native live coherent mutant has nonzero residuals")?;
    // Exercise the native comparison directly. validate_native intentionally
    // checks selected RAW custody first, which would otherwise mask this gate.
    rejected(seal.check_reads(&forged.selected.reads),"native physical READ address/value binding")?;

    let mut destination=Destination::default();destination.cells.insert(1,Fr::one());
    let frozen=destination.clone();
    // Keep the honest READs/helpers/terms, changing only native authority.
    let mut bad=honest.clone();bad.identity.root[0]^=1;
    rejected(source.publish_native(&mut destination,bad,seal),"native parent root binding")?;
    need(destination==frozen,"native live failed publication mutated destination")?;
    println!("C131_NATIVE_Q9_LIVE_FAULTS_PASS identity=4 raw=1 native_read=1 atomic=1");
    Ok((4,1,1,1))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    #[ignore="bounded c131 no-frame comparison/dispatch test; does not construct an H21 seal"]
    fn native_binding_comparison_faults() {
        // Synthetic comparator inputs are deliberately not NativeQ9Binding.
        // No NativePrefix, WorkTreeHistoryPlan, RAW fixture, or frame is loaded.
        let map=Map::new_modern_global_u(1_827_840,21,55).unwrap();
        assert_eq!(map.binding().parent_root,None);
        let source=SourceBinding{policy:POLICY,authority:Q9RawIdentity::SelectedRawFixture,
            map:map.binding(),owner:OWNER,context:0};
        let expected=NativeParentIdentity{headers:1_827_840,slot_log:21,slots:1<<21,
            genuine:1_827_839,leaves:1<<21,root:[7;32],total:[8;28],profile:[9;32],profiles:vec![10,11],source};
        compare_native_identity(&expected,&expected).unwrap();
        for fault in 0..18 {
            let mut bad=expected.clone();let error=match fault {
                0=>{bad.headers-=1;"native parent geometry binding"},
                1=>{bad.slot_log-=1;"native parent geometry binding"},
                2=>{bad.slots/=2;"native parent geometry binding"},
                3=>{bad.genuine-=1;"native parent geometry binding"},
                4=>{bad.leaves/=2;"native parent geometry binding"},
                5=>{bad.root[0]^=1;"native parent root binding"},
                6=>{bad.total[0]^=1;"native parent total binding"},
                7=>{bad.profile[0]^=1;"native parent profile binding"},
                8=>{bad.profiles[0]^=1;"native parent profile binding"},
                9=>{bad.source.owner+=1;"native Map/source dispatch binding"},
                10=>{bad.source.context=1;"native Map/source dispatch binding"},
                11=>{bad.source.policy="other policy";"native Map/source dispatch binding"},
                12=>{bad.source.map.e=54;"native Map/source dispatch binding"},
                13=>{bad.source.map.parent_root=Some(expected.root);"native Map/source dispatch binding"},
                14=>{bad.source.map=Map::new(1_827_840,21,55).unwrap().binding();"native Map/source dispatch binding"},
                15=>{bad.source.map.n-=1;"native Map/source dispatch binding"},
                16=>{bad.source.map.h=20;"native Map/source dispatch binding"},
                _=>{bad.source.map=Map::new_modern_global_u_selected_lower(1_827_840,21,55,
                    crate::legacy_envelope_map::LowerSelector {
                        source:crate::legacy_envelope_map::LowerSource::HeaderDifficulty{height:841729},
                        branch:crate::legacy_envelope_map::LowerBranch::Pivot(54),
                    }).unwrap().binding();"native Map/source dispatch binding"},
            };
            assert_eq!(compare_native_identity(&bad,&expected).unwrap_err(),error,"identity fault {fault}");
        }
        // Exact RAW identity rejects a substitution even if a caller says its
        // separately held D/T values agree. This helper makes no decode claim.
        compare_raw(2048,b"same canonical bytes",b"same canonical bytes").unwrap();
        assert_eq!(compare_raw(2048,b"different bytes",b"same canonical bytes").unwrap_err(),
            "native q9 RAW identity at height 2048");
        let mut canonical=BTreeMap::new();
        for imp in map.imports(OWNER as u64).unwrap() {for bit in 0..imp.width {
            assert!(canonical.insert(map.input_index(imp,bit).unwrap(),Fr::one()).is_none());
        }}
        assert_eq!(canonical.len(),READ_BITS);compare_native_reads(&canonical,&canonical).unwrap();
        let empty=BTreeMap::new();
        assert_eq!(compare_native_reads(&empty,&empty).unwrap_err(),"native physical READ address/value binding");
        for fault in 0..5 {
            let mut bad=canonical.clone();let first=*bad.first_key_value().unwrap().0;
            match fault {
                0=>{bad.remove(&first);},
                1=>{assert!(bad.insert(0,Fr::one()).is_none());},
                2=>{*bad.get_mut(&first).unwrap()=Fr::zero();},
                3=>{let same=bad.remove(&first).unwrap();assert!(bad.insert(first+WIDTH,same).is_none());},
                _=>{let same=bad.remove(&first).unwrap();assert!(bad.insert(first-1,same).is_none());},
            }
            assert_eq!(compare_native_reads(&bad,&canonical).unwrap_err(),"native physical READ address/value binding",
                "READ fault {fault}");
        }
        // Exercise the actual shared preflight without constructing a source,
        // batch or native seal. Comparator inputs have no witness authority.
        let q=OWNER*WIDTH+HELPER_BASE;let helpers=BTreeMap::from([(q,Fr::one())]);
        let row=OWNER*(1<<19)+477074;
        let terms=vec![Term{row,gate:crate::gkr::Gate{left:q,right:q,c0:Fr::zero(),
            c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()}}];
        for fault in 0..3 {
            let mut destination=Destination::default();let error=match fault {
                0=>{destination.published=true;"duplicate owner batch"},
                1=>{destination.cells.insert(q,Fr::one());"destination X collision"},
                _=>{destination.rows.insert(row,"other semantic writer");"destination ROW collision"},
            };
            let frozen=destination.clone();
            assert_eq!(destination_preflight(&destination,&helpers,&terms).unwrap_err(),error);
            assert_eq!(destination,frozen);
        }
        assert!(!Destination::default().is_native_parent_bound());
        println!("C131_NATIVE_Q9_COMPARISON_FAULTS_PASS identity_faults=18 read_faults=6 raw_faults=1 collision_faults=3 native_seal=false");
    }
    fn fixture()->CheckedQ9RawFixture {
        let dir=std::env::var_os("NIPOPOW_H21_Q9_HEADERS_DIR").expect("pinned q9 directory env");
        CheckedQ9RawFixture::load(std::path::Path::new(&dir)).unwrap()
    }
    #[test]
    #[ignore="requires pinned q9 RAW bundle"]
    fn checked_raw_q9_stage_validate_publish_once() {
        let fixture=fixture();let source=SelectedRawMapSource::new(&fixture).unwrap();
        let batch=source.stage().unwrap();
        assert_eq!(batch.imports.len(),18);assert_eq!(batch.reads.len(),READ_BITS);
        assert_eq!(batch.helpers.len(),HELPERS);assert_eq!(batch.terms.len(),TERM_COUNT);
        assert_eq!(batch.imports.iter().filter(|i|i.kind==Kind::Difficulty).map(|i|i.owner).collect::<Vec<_>>(),
            vec![3070,4094,5118,6142,7166,8190,9214,10174,10175]);
        assert_eq!(batch.imports.iter().filter(|i|i.kind==Kind::Timestamp).map(|i|i.owner).collect::<Vec<_>>(),
            vec![2047,3071,4095,5119,6143,7167,8191,9215,10175]);
        for imp in &batch.imports {
            let (height,local,width)=match imp.kind {
                Kind::Difficulty=>(imp.owner+2,987674,224),
                Kind::Timestamp=>(imp.owner+1,525330,64),
            };
            assert_eq!((imp.local,imp.width),(local,width));
            let header=ergo_header_core::Header::decode(fixture.checked_raw(height as u32).unwrap(),None).unwrap();
            let value=match imp.kind {
                Kind::Difficulty=>BigInt::from(crate::work_tree_work::native_decode(header.n_bits).unwrap()),
                Kind::Timestamp=>BigInt::from(header.timestamp),
            };
            for k in 0..width {
                let expected=if ((&value>>k)&BigInt::from(1u8))==BigInt::from(1u8){Fr::one()}else{Fr::zero()};
                assert_eq!(batch.reads[&(imp.owner as usize*1048576+local+k)],expected);
            }
        }
        assert_eq!(batch.binding.authority,Q9RawIdentity::SelectedRawFixture);
        assert_eq!(batch.binding.map.parent_root,None);
        source.validate(&batch).unwrap();
        assert!(residuals(&batch).unwrap().values().all(|z|z.is_zero()));
        let mut destination=Destination::default();source.publish(&mut destination,batch.clone()).unwrap();
        assert!(destination.published);assert_eq!(destination.cells.len(),HELPERS);
        assert!(batch.reads.keys().all(|q|!destination.cells.contains_key(q)));
        let frozen=destination.clone();
        assert_eq!(source.publish(&mut destination,batch).unwrap_err(),"duplicate owner batch");
        assert_eq!(destination,frozen);
        println!("C130C_Q9_PUBLISH_PASS reads=2592 helpers=5757 terms=68233");
    }
    #[test]
    #[ignore="requires pinned q9 RAW bundle"]
    fn coherent_destination_d_helpers_cannot_forge_raw_reads() {
        let fixture=fixture();let source=SelectedRawMapSource::new(&fixture).unwrap();
        let honest=source.stage().unwrap();source.validate(&honest).unwrap();
        let d=*honest.imports.iter().find(|i|i.owner==OWNER as u64&&i.kind==Kind::Difficulty).unwrap();
        assert_eq!((d.local,d.width),(987674,224));
        let (mut inputs,_)=source.imports(&honest.imports).unwrap();
        assert!(inputs.get(d).unwrap()>BigInt::from(1u8));
        let mut forged=honest.clone();let address=source.map.input_index(d,0).unwrap();
        *forged.reads.get_mut(&address).unwrap()=Fr::one()-honest.reads[&address];
        inputs.flip(d,0).unwrap();
        let replacement=source.map.generate(OWNER as u64,&inputs).unwrap();
        for k in 0..HELPERS {
            *forged.helpers.get_mut(&(OWNER*WIDTH+HELPER_BASE+k)).unwrap()=
                Fr::from(u64::from(replacement.bit(crate::legacy_envelope_map::BASE+k).unwrap()));
        }
        assert_eq!(forged.binding,honest.binding);assert_eq!(forged.imports,honest.imports);
        assert_eq!(forged.terms,honest.terms);assert_ne!(forged.reads,honest.reads);
        assert!(residuals(&forged).unwrap().values().all(|z|z.is_zero()),"coherent actual Map regeneration");
        assert_eq!(source.validate(&forged).unwrap_err(),"RAW READ address/value binding");
        let mut destination=Destination::default();destination.cells.insert(1,Fr::one());
        let frozen=destination.clone();
        assert_eq!(source.publish(&mut destination,forged).unwrap_err(),"RAW READ address/value binding");
        assert_eq!(destination,frozen);
        println!("C130C_COHERENT_FORGERY_REJECT_PASS residuals=zero raw_binding=rejected");
    }
    #[test]
    #[ignore="requires pinned q9 RAW bundle"]
    fn import_and_writer_census_fail_before_residuals() {
        let fixture=fixture();let source=SelectedRawMapSource::new(&fixture).unwrap();
        let honest=source.stage().unwrap();
        for fault in 0..7 {
            let mut bad=honest.clone();
            match fault {
                0=>{bad.imports.pop();},
                1=>bad.imports.insert(0,bad.imports[0]),
                2=>bad.imports[0].local+=1,
                3=>bad.imports[0].width-=1,
                4=>bad.imports[0].kind=if bad.imports[0].kind==Kind::Difficulty{Kind::Timestamp}else{Kind::Difficulty},
                5=>bad.imports[0].owner+=1,
                _=>bad.imports.swap(0,1),
            }
            assert_eq!(source.stage_requested(&bad.imports).unwrap_err(),"exact import census");
            let mut destination=Destination::default();let frozen=destination.clone();
            assert_eq!(source.publish(&mut destination,bad).unwrap_err(),"exact import census","fault {fault}");
            assert_eq!(destination,frozen);
        }
        for fault in 0..3 {
            let mut bad=honest.clone();let expected=match fault {
                0=>{bad.helpers.pop_first();"helper writer census"},
                1=>{bad.terms.pop();"ordered term census"},
                _=>{bad.reads.pop_first();"RAW READ address/value binding"},
            };
            let mut destination=Destination::default();let frozen=destination.clone();
            assert_eq!(source.publish(&mut destination,bad).unwrap_err(),expected);
            assert_eq!(destination,frozen);
        }
        for fault in 0..5 {
            let mut bad=honest.clone();match fault {
                0=>bad.binding.owner+=1,
                1=>bad.binding.context=1,
                2=>bad.binding.policy="other policy",
                3=>bad.binding.map.e+=1,
                _=>bad.binding.map.parent_root=Some([1u8;32]),
            }
            let mut destination=Destination::default();let frozen=destination.clone();
            assert_eq!(source.publish(&mut destination,bad).unwrap_err(),"batch binding");
            assert_eq!(destination,frozen);
        }
        println!("C130C_CENSUS_REJECT_PASS faults=15");
    }
    #[test]
    #[ignore="requires pinned q9 RAW bundle"]
    fn equal_x_and_cross_writer_row_collisions_are_atomic() {
        let fixture=fixture();let source=SelectedRawMapSource::new(&fixture).unwrap();
        let honest=source.stage().unwrap();
        for fault in 0..2 {
            let mut destination=Destination::default();
            let expected=if fault==0 {
                let (q,value)=honest.helpers.first_key_value().unwrap();destination.cells.insert(*q,*value);
                "destination X collision"
            } else {
                destination.rows.insert(honest.terms[0].row,"other semantic relation");"destination ROW collision"
            };
            let frozen=destination.clone();
            assert_eq!(source.publish(&mut destination,honest.clone()).unwrap_err(),expected);
            assert_eq!(destination,frozen);
        }
        println!("C130C_COLLISION_REJECT_PASS faults=2");
    }

    #[test]
    #[ignore="requires pinned q9 RAW bundle"]
    fn q9_upper_only_map_is_not_selected_lower_compatible() {
        use crate::legacy_envelope_map::{LowerBranch,LowerSelector,LowerSource};

        let fixture=fixture();
        let upper=SelectedRawMapSource::new(&fixture).unwrap();
        let selected=Map::new_modern_global_u_selected_lower(1_827_840,21,55,LowerSelector {
            source:LowerSource::HeaderDifficulty {height:841729},
            branch:LowerBranch::Pivot(54),
        }).unwrap();

        assert_ne!(upper.map.binding(),selected.binding(),"full Map binding includes lower-selector mode");
        let upper_imports=upper.map.imports(OWNER as u64).unwrap();
        let selected_imports=selected.imports(OWNER as u64).unwrap();
        assert_eq!(upper_imports,selected_imports,"q9 exact typed import census");
        assert!(upper_imports.iter().any(|i|i.kind==Kind::Difficulty&&i.owner==3070),
            "foreign D owner 3070 must remain in the q9 imports");
        assert_eq!(upper.map.active_intervals(OWNER as u64).unwrap(),
            selected.active_intervals(OWNER as u64).unwrap(),"q9 active interval census");

        // Reuse only values decoded from the checked ten-header fixture.
        let (inputs,reads)=upper.imports(&upper_imports).unwrap();
        assert_eq!(reads.len(),READ_BITS);
        let mut selected_reads=BTreeMap::new();
        let mut selected_foreign_d_reads=BTreeMap::new();
        let mut upper_foreign_d_reads=BTreeMap::new();
        for imp in &selected_imports {
            for bit in 0..imp.width {
                let selected_address=selected.input_index(*imp,bit).unwrap();
                let value=Fr::from(u64::from(inputs.bit(imp.owner,imp.local+bit).unwrap()));
                assert!(selected_reads.insert(selected_address,value).is_none(),
                    "selected-lower import address collision: {imp:?} bit {bit}");
                if imp.kind==Kind::Difficulty&&imp.owner==3070 {
                    let upper_address=upper.map.input_index(*imp,bit).unwrap();
                    assert_eq!(selected_address,upper_address,"foreign D owner 3070 address bit {bit}");
                    assert_eq!(value,reads[&upper_address],"foreign D owner 3070 value bit {bit}");
                    selected_foreign_d_reads.insert(selected_address,value);
                    upper_foreign_d_reads.insert(upper_address,reads[&upper_address]);
                }
            }
        }
        assert_eq!(selected_reads.len(),READ_BITS,"selected-lower exact READ census");
        assert_eq!(selected_reads,reads,"selected-lower (address,value) READ map from checked inputs");
        assert_eq!(selected_foreign_d_reads.len(),224,"foreign D owner 3070 bit-address census");
        assert_eq!(selected_foreign_d_reads,upper_foreign_d_reads,
            "foreign D owner 3070 selected-lower READ addresses and values");
        let upper_row=upper.map.generate(OWNER as u64,&inputs).unwrap();
        let selected_row=selected.generate(OWNER as u64,&inputs).unwrap();
        upper.map.check_row(&upper_row).unwrap();
        selected.check_row(&selected_row).unwrap();
        assert_eq!(upper_row.bits,selected_row.bits,"q9 generated owner bit values from identical checked inputs");

        let upper_terms=bank53_map::map_owner_terms(&upper.map,OWNER as u64,0).unwrap().iter()
            .map(|t|relocate(Family::Map(0),OWNER,t)).collect::<Result<Vec<_>,_>>().unwrap();
        let selected_terms=bank53_map::map_owner_terms(&selected,OWNER as u64,0).unwrap().iter()
            .map(|t|relocate(Family::Map(0),OWNER,t)).collect::<Result<Vec<_>,_>>().unwrap();
        assert_eq!(upper_terms,selected_terms,"q9 ordered relocated terms");
        assert_eq!(upper_terms,upper.terms().unwrap(),"existing q9 source term path");

        let selected_owner=841727usize;
        let upper_selected_terms=bank53_map::map_owner_terms(&upper.map,selected_owner as u64,0).unwrap().iter()
            .map(|t|relocate(Family::Map(0),selected_owner,t)).collect::<Result<Vec<_>,_>>().unwrap();
        let lower_selected_terms=bank53_map::map_owner_terms(&selected,selected_owner as u64,0).unwrap().iter()
            .map(|t|relocate(Family::Map(0),selected_owner,t)).collect::<Result<Vec<_>,_>>().unwrap();
        assert_ne!(upper_selected_terms,lower_selected_terms,
            "selected lower D owner 841727 changes ordered relocated terms");
    }
}

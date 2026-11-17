//! Test-only native Map source/cut join. No global-U or HEADER admission.
use ark_bn254::Fr;
use ark_ff::{One,Zero};
use blake2::{Blake2b,Digest,digest::consts::U32};
use num_bigint::BigInt;
use std::collections::{BTreeMap,BTreeSet};
use crate::{bank53_map,legacy_envelope_map::{Map,Binding,Import,Inputs,Kind,LowerSelector,LowerSource,LowerBranch},
    native_owner_exports::NativeExports,native_prefix_auth_plan::role0_sha256,
    packed_owner_assembly::{NativePrefix,validate_native_plan_input},
    work_tree_history_plan::WorkTreeHistoryPlan,h21_row_support::{relocate,Family},sparse::Term};

const FRAME:&str="A68D86562A56C5B71CF2180E4762BF8775B1061B6953BFF7281EC50B7EE52C5E";
const BUNDLE_SHA:&str="ABB3D74AE75256CED63110B72C2E0D5EBA1B90B09889E45EA327BDA1C9A640D2";
const BUNDLE_BLAKE:&str="8CDB90DA475E646280113D97C9469BE7EB86A1D04F20404C64239187284FC009";
const MANIFEST_SHA:&str="9EC19F37B4523ABDDA12FA312CA30AAC41FAE99E054ECE5EC601B18CC9DE700E";
const POLICY:&str="native-parent-exact-map-cut-v1";
const WIDTH:usize=1<<20;
fn hex(bytes:&[u8])->String{bytes.iter().map(|b|format!("{b:02X}")).collect()}
fn profile_bytes(p:&WorkTreeHistoryPlan)->Result<Vec<u8>,String>{
    serde_json::to_vec(&(p.fixed_profile(),p.leaf_profile(),p.work_profile())).map_err(|e|e.to_string())
}

/// Private fields; only verified bytes and an exact native pair create this.
#[derive(Clone,Debug,PartialEq,Eq)]
pub(super) struct VerifiedBundleIdentity {
    frame:&'static str,bundle:[u8;32],manifest:[u8;32],headers:u64,slot_log:usize,
    root:[u8;32],total:[u8;28],native_profile:[u8;32],profiles:Vec<u8>,
}
impl VerifiedBundleIdentity {
    pub(super) fn from_bundle(parent:&WorkTreeHistoryPlan,native:&NativePrefix,bundle:&[u8],manifest:&[u8])->Result<Self,String>{
        if bundle.len()!=869449||manifest.len()!=896||hex(&role0_sha256(bundle)?)!=BUNDLE_SHA
            ||hex(&Blake2b::<U32>::digest(bundle))!=BUNDLE_BLAKE||hex(&role0_sha256(manifest)?)!=MANIFEST_SHA {
            return Err("pinned bundle/manifest bytes".into());
        }
        let m:serde_json::Value=serde_json::from_slice(manifest).map_err(|e|e.to_string())?;
        if m["sourceFrameSha256"].as_str()!=Some(FRAME)||m["extractedRecords"].as_u64()!=Some(3073)
            ||m["bundleSha256"].as_str()!=Some(BUNDLE_SHA){return Err("bundle manifest identity".into());}
        validate_native_plan_input(parent,native)?;
        if parent.headers()!=3073||parent.slot_log()!=12{return Err("bundle native geometry".into());}
        let mut pos=0usize;
        for height in 1..=3073 {
            let prefix=bundle.get(pos..pos+4).ok_or("bundle length prefix")?;
            let n=u32::from_le_bytes(prefix.try_into().map_err(|_|"bundle u32")?) as usize;pos+=4;
            let raw=bundle.get(pos..pos+n).ok_or("bundle RAW extent")?;pos+=n;
            if raw!=native.raw(height)?{return Err("bundle RAW/native identity".into());}
        }
        if pos!=bundle.len(){return Err("bundle surplus".into());}
        Ok(Self{frame:FRAME,bundle:role0_sha256(bundle)?,manifest:role0_sha256(manifest)?,
            headers:parent.headers(),slot_log:parent.slot_log(),root:native.root(),total:native.total_be28(),
            native_profile:native.profile(),profiles:profile_bytes(parent)?})
    }
    fn check(&self,parent:&WorkTreeHistoryPlan,native:&NativePrefix)->Result<(),String>{
        validate_native_plan_input(parent,native)?;
        if self.frame!=FRAME||hex(&self.bundle)!=BUNDLE_SHA||hex(&self.manifest)!=MANIFEST_SHA
            ||self.headers!=parent.headers()||self.slot_log!=parent.slot_log()
            ||self.root!=native.root()||self.total!=native.total_be28()
            ||self.native_profile!=native.profile()||self.profiles!=profile_bytes(parent)? {
            return Err("sealed source root/total/count/profile".into());
        }Ok(())
    }
}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(super) enum SealedCutProfile {Bounded,H21Metadata}
#[derive(Clone,Debug,PartialEq,Eq)]
struct Parameters {source_n:u64,h:usize,cut:u64,e:usize,lower:LowerSelector}
impl SealedCutProfile {
    fn parameters(self,c:usize)->Result<Parameters,String>{
        if c>=2{return Err("cut context".into());}
        Ok(match self {
            Self::Bounded=>Parameters{source_n:3073,h:12,cut:[3073,3072][c],e:48,
                lower:LowerSelector{source:LowerSource::LegacyBound{q:2},branch:LowerBranch::Pivot(45)}},
            Self::H21Metadata=>Parameters{source_n:1827840,h:21,cut:[1827840,1827775][c],e:55,
                lower:LowerSelector{source:LowerSource::HeaderDifficulty{height:841729},branch:LowerBranch::Pivot(54)}},
        })
    }
}
#[derive(Clone,Debug,PartialEq,Eq)]
pub(super) struct CutBinding {policy:&'static str,source:VerifiedBundleIdentity,context:usize,cut:u64,map:Binding}
impl CutBinding {
    // Read-only metadata, without inventing a transcript encoding in this lot.
    pub(super) fn source_headers(&self)->u64{self.source.headers}
    pub(super) fn source_slot_log(&self)->usize{self.source.slot_log}
    pub(super) fn source_root(&self)->[u8;32]{self.source.root}
    pub(super) fn source_total(&self)->[u8;28]{self.source.total}
    pub(super) fn source_frame(&self)->&'static str{self.source.frame}
    pub(super) fn bundle_sha(&self)->[u8;32]{self.source.bundle}
    pub(super) fn manifest_sha(&self)->[u8;32]{self.source.manifest}
    pub(super) fn native_profile(&self)->[u8;32]{self.source.native_profile}
    pub(super) fn native_profiles(&self)->&[u8]{&self.source.profiles}
    pub(super) fn map_binding(&self)->&Binding{&self.map}
    pub(super) fn context(&self)->usize{self.context}
    pub(super) fn cut(&self)->u64{self.cut}
    pub(super) fn policy(&self)->&'static str{self.policy}
}
pub(super) struct CutMapSource<'a> {
    parent:&'a WorkTreeHistoryPlan,native:&'a NativePrefix,exports:NativeExports<'a>,
    profile:SealedCutProfile,map:Map,binding:CutBinding,
}
fn geometry(source_n:u64,h:usize,cut:u64)->Result<(),String>{
    if cut<3||cut>source_n||(64-(cut-1).leading_zeros()) as usize!=h{return Err("source/cut extent or slot log".into());}Ok(())
}
impl<'a> CutMapSource<'a> {
    pub(super) fn new(parent:&'a WorkTreeHistoryPlan,native:&'a NativePrefix,source:VerifiedBundleIdentity,
        profile:SealedCutProfile,context:usize)->Result<Self,String>{
        let cut=profile.parameters(context)?.cut;
        Self::new_checked(parent,native,source,profile,context,cut)
    }
    fn new_checked(parent:&'a WorkTreeHistoryPlan,native:&'a NativePrefix,source:VerifiedBundleIdentity,
        profile:SealedCutProfile,context:usize,cut:u64)->Result<Self,String>{
        let p=profile.parameters(context)?;geometry(parent.headers(),parent.slot_log(),cut)?;
        if cut!=p.cut||parent.headers()!=p.source_n||parent.slot_log()!=p.h{return Err("unsealed parent/cut profile".into());}
        if profile==SealedCutProfile::H21Metadata{return Err("H21 native construction deferred".into());}
        source.check(parent,native)?;
        let map=Map::new_modern_global_u_selected_lower(cut,p.h,p.e,p.lower)?;
        let binding=CutBinding{policy:POLICY,source,context,cut,map:map.binding()};
        Ok(Self{parent,native,exports:NativeExports::new_for_history(parent,native)?,profile,map,binding})
    }
    pub(super) fn binding(&self)->&CutBinding{&self.binding}
    fn check_binding(&self)->Result<(),String>{
        self.binding.source.check(self.parent,self.native)?;
        let p=self.profile.parameters(self.binding.context)?;
        let expected=Map::new_modern_global_u_selected_lower(p.cut,p.h,p.e,p.lower)?.binding();
        if self.binding.policy!=POLICY||self.binding.cut!=p.cut||self.binding.map!=expected||self.map.binding()!=expected{
            return Err("complete Map mode/selector/cut binding".into());}Ok(())
    }
    fn imports(&self,owner:usize,requested:&[Import])->Result<(Inputs,BTreeMap<usize,Fr>),String>{
        self.check_binding()?;
        let canonical=self.map.imports(owner as u64)?;
        if canonical!=requested||requested.iter().copied().collect::<BTreeSet<_>>().len()!=requested.len(){
            return Err("exact destination import census".into());}
        let mut inputs=Inputs::default();let mut bits=BTreeMap::new();
        for imp in requested {
            let height=imp.owner+if imp.kind==Kind::Difficulty{2}else{1};
            if height>self.parent.headers(){return Err("import outside source parent".into());}
            let mut n=BigInt::from(0u8);
            for k in 0..imp.width {
                let address=self.map.input_index(*imp,k)?;let bit=self.exports.bit(address)?;
                if bit{n+=BigInt::from(1u8)<<k;}
                if bits.insert(address,Fr::from(u64::from(bit))).is_some(){return Err("duplicate native import address".into());}
            }inputs.put(&self.map,*imp,&n)?;
        }Ok((inputs,bits))
    }
    fn terms(&self,owner:usize)->Result<Vec<Term>,String>{
        self.check_binding()?;
        bank53_map::map_owner_terms(&self.map,owner as u64,self.binding.context)?.iter()
            .map(|t|relocate(Family::Map(self.binding.context),owner,t)).collect()
    }
    pub(super) fn stage_owner(&self,owner:usize)->Result<OwnerMapBatch,String>{
        self.check_binding()?;let imports=self.map.imports(owner as u64)?;
        let (inputs,reads)=self.imports(owner,&imports)?;
        let source=self.map.generate(owner as u64,&inputs)?;self.map.check_row(&source)?;
        let mut helpers=BTreeMap::new();
        for k in 0..bank53_map::MAP_LIVE {
            let q=owner*WIDTH+671744+self.binding.context*8192+k;
            if helpers.insert(q,Fr::from(u64::from(source.bits[k]))).is_some(){return Err("duplicate helper write".into());}
        }
        Ok(OwnerMapBatch{binding:self.binding.clone(),owner,imports,helpers,reads,terms:self.terms(owner)?})
    }
    fn validate(&self,b:&OwnerMapBatch)->Result<(),String>{
        self.check_binding()?;
        if b.binding!=self.binding||b.imports!=self.map.imports(b.owner as u64)?||b.terms!=self.terms(b.owner)?{
            return Err("binding/import/ordered term census".into());}
        let expected=(0..bank53_map::MAP_LIVE).map(|k|b.owner*WIDTH+671744+self.binding.context*8192+k).collect::<BTreeSet<_>>();
        if b.helpers.keys().copied().collect::<BTreeSet<_>>()!=expected{return Err("helper writer census".into());}
        let expected=self.imports(b.owner,&b.imports)?.1;
        if b.reads.keys().copied().collect::<BTreeSet<_>>()!=expected.keys().copied().collect::<BTreeSet<_>>(){return Err("native read census".into());}
        // Shape and root metadata alone do not bind a coherently regenerated
        // Map witness to the immutable native values. Compare every read bit.
        if b.reads!=expected{return Err("native READ values/source binding".into());}
        if b.helpers.values().chain(b.reads.values()).any(|v|!v.is_zero()&&!v.is_one()){return Err("native/helper bitness".into());}
        if let Some((q,_))=residuals(b)?.into_iter().find(|(_,v)|!v.is_zero()){return Err(format!("Map residual ROW {q}"));}Ok(())
    }
    fn publish(&self,d:&mut Destination,b:OwnerMapBatch)->Result<(),String>{
        self.validate(&b)?;let writer=(self.binding.context,b.owner);
        let rows=b.terms.iter().map(|t|t.row).collect::<BTreeSet<_>>();
        if d.owners.contains_key(&writer)||b.helpers.keys().any(|q|d.cells.contains_key(q))
            ||rows.iter().any(|q|d.rows.get(q).is_some_and(|old|*old!=writer)){
            return Err("duplicate batch/X or cross-writer ROW".into());}
        // No fallible work after this point. Imported native cells stay READS.
        d.owners.insert(writer,b.binding);
        for (q,value) in b.helpers{d.cells.insert(q,(writer,value));}
        for q in rows{d.rows.insert(q,writer);}Ok(())
    }
    pub(super) fn publish_owner(&self,d:&mut Destination,owner:usize)->Result<(),String>{self.publish(d,self.stage_owner(owner)?)}
}
#[derive(Clone,Debug,PartialEq,Eq)]
pub(super) struct OwnerMapBatch {
    binding:CutBinding,owner:usize,imports:Vec<Import>,helpers:BTreeMap<usize,Fr>,
    reads:BTreeMap<usize,Fr>,terms:Vec<Term>,
}
#[derive(Clone,Debug,Default,PartialEq,Eq)]
pub(super) struct Destination {
    owners:BTreeMap<(usize,usize),CutBinding>,cells:BTreeMap<usize,((usize,usize),Fr)>,rows:BTreeMap<usize,(usize,usize)>,
}
fn residuals(b:&OwnerMapBatch)->Result<BTreeMap<usize,Fr>,String>{
    let read=|q:usize|b.helpers.get(&q).or_else(||b.reads.get(&q)).copied().ok_or_else(||format!("missing active X {q}"));
    let mut out=BTreeMap::new();
    for t in &b.terms {let g=&t.gate;let mut z=g.c0;
        // Unused operands remain in the tuple census, but aren't X reads.
        if !g.c1.is_zero(){z+=g.c1*read(g.left)?;}
        if !g.c2.is_zero(){z+=g.c2*read(g.right)?;}
        if !g.c3.is_zero(){z+=g.c3*read(g.left)?*read(g.right)?;}
        *out.entry(t.row).or_insert(Fr::zero())+=z;
    }Ok(out)
}
#[cfg(test)]
#[path="native_map_cut_source_tests.rs"]
mod tests;

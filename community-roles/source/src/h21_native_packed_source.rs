//! Ordered storage of source-owned H21 values. A bounded fragment is never a
//! complete polynomial or proof admission. No PCS key/setup is selected here.
use super::*;
use crate::packed::{H21PackedFragment,H21PackedWriter,PackedFile};
use std::path::Path;

#[derive(Clone,PartialEq,Eq)]
struct SourceIdentity {
    parent:HeaderSourceBinding,
    maps:[crate::legacy_envelope_map::Binding;2],
}

/// No PackedFile, Polynomial, complete-source constructor or conversion is
/// exposed by this type. Its held reader covers only the requested prefix.
pub(crate) struct NativeH21PackedFragment {identity:SourceIdentity,fragment:H21PackedFragment}
impl NativeH21PackedFragment {
    pub(crate) fn owners(&self)->usize {self.fragment.owners()}
    pub(crate) fn bytes(&self)->u64 {self.fragment.bytes()}
    pub(crate) fn digest(&self)->[u8;64] {self.fragment.digest()}
    pub(crate) fn parent_binding(&self)->&HeaderSourceBinding {&self.identity.parent}
}

/// Issued only by write_h21_all after the complete native stream, immutable
/// readback digest and EOF have passed. This remains a witness candidate;
/// no structural proof, PCS verification or production qualification follows.
pub(crate) struct NativeH21PackedSource {
    identity:SourceIdentity,source:PackedFile,digest:[u8;64],
}
impl NativeH21PackedSource {
    pub(crate) fn packed(&self)->&PackedFile {&self.source}
    pub(crate) fn digest(&self)->[u8;64] {self.digest}
    pub(crate) fn parent_binding(&self)->&HeaderSourceBinding {&self.identity.parent}
    pub(crate) fn map_bindings(&self)->&[crate::legacy_envelope_map::Binding;2] {&self.identity.maps}
}

impl<'ctx,'src,'max,'snapshot> H21ScoreEndpointStream<'ctx,'src,'max,'snapshot> {
    fn packed_source_identity(&self)->Result<SourceIdentity,String> {
        self.terminal_r()?;
        let context=self.context;let producer=&context.producer;
        validate_native_plan_input(producer.plan,producer.input)?;
        if producer.plan.headers()!=N as u64 || producer.plan.slot_log()!=21
            || producer.plan.slots()!=SLOTS || context.descriptor!=crate::bank53_map::CutDescriptor::eligible08() {
            return Err("H21 packed native geometry/cut".into());
        }
        self.closed_max.closed_native_snapshot(producer.plan,producer.input)?;
        let maps=std::array::from_fn(|c|context.maps[c].binding());
        for (c,binding) in maps.iter().enumerate() {
            if binding.n!=context.descriptor.terminals()[c]as u64 || binding.h!=21 {
                return Err("H21 packed two Map contexts".into());
            }
        }
        Ok(SourceIdentity {parent:HeaderSourceBinding::for_plan(producer.plan,0)?,maps})
    }
    fn write_native_owner(&self,identity:&SourceIdentity,writer:&mut H21PackedWriter,owner:usize)
        ->Result<(),String> {
        // Exactly one generated row per owner. No read failure or absent
        // source is replaced by zero bytes or by a row from another context.
        let row=self.native_owner_values(owner)?;
        row.require_context(self.context)?;
        let expected=HeaderSourceBinding::for_plan(self.context.producer.plan,owner)?;
        if row.owner()!=owner || row.binding()!=&expected
            || !row.binding().matches_sink(identity.parent.root,identity.parent.total,
                identity.parent.profile,&identity.parent.cut,owner) {
            return Err("H21 packed row differs from native parent/context".into());
        }
        writer.write_owner(owner,row.packed_bytes())
    }
    pub(crate) fn write_h21_prefix(&self,path:&Path,owners_log:usize)->Result<NativeH21PackedFragment,String> {
        if owners_log>4 {return Err("H21 fragment owner log must be 0..4".into());}
        let identity=self.packed_source_identity()?;
        let mut writer=H21PackedWriter::prefix(path,owners_log)?;
        for owner in 0..1usize<<owners_log {self.write_native_owner(&identity,&mut writer,owner)?;}
        if self.packed_source_identity()?!=identity {return Err("H21 fragment source identity changed".into());}
        let fragment=writer.finish_fragment()?;
        if fragment.owners()!=1usize<<owners_log || fragment.bytes()!=(fragment.owners()*BYTES)as u64 {
            return Err("H21 fragment final census".into());
        }
        Ok(NativeH21PackedFragment {identity,fragment})
    }
    pub(crate) fn write_h21_all(&self,path:&Path)->Result<NativeH21PackedSource,String> {
        let identity=self.packed_source_identity()?;
        let mut writer=H21PackedWriter::all(path)?;
        for owner in 0..SLOTS {self.write_native_owner(&identity,&mut writer,owner)?;}
        if self.packed_source_identity()?!=identity {return Err("H21 complete source identity changed".into());}
        let(source,digest)=writer.finish_all()?;
        if source.input_len()!=1usize<<41 {return Err("H21 complete polynomial extent".into());}
        // Contiguous owner rows give PCS row j = owner 2j || owner 2j+1.
        let complete=NativeH21PackedSource {identity,source,digest};
        let digest=complete.digest().iter().map(|b|format!("{b:02X}")).collect::<String>();
        println!("C588_NATIVE_PACKED_SOURCE_COMPLETE owners=2097152 bytes=274877906944 log_n=41 contexts=2 digest={digest} readback=true eof=true pcs=false proof=false source_qualified=false");
        Ok(complete)
    }
}

#[path="h21_native_packed_source_tests.rs"]
mod tests;

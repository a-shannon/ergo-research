//! TEST-only direct sum over the existing native input addresses. No PCS role.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use ark_serialize::CanonicalSerialize;
use crate::{legacy_envelope_map::Map, legacy_native_adapter::LegacyNativeAdapter,
    sparse::Term, transcript::Transcript};

pub(crate) const INPUT_LOG: usize = 32;
pub(crate) const PAYLOAD_LOG: usize = 31;
pub(crate) const MAP_LOG: usize = 26;
pub(crate) const ROW_LOG: usize = 33;
pub(crate) const PAYLOAD: usize = 1usize << PAYLOAD_LOG;
const DOMAIN: &[u8] = b"legacy-native-tagged-composition-v1";
const MAP_CONTRACT: &[u8] = b"1AC18112EC82D0E770D6501EACA59A15194EAA1BE756CADBC8F9312E8EE9EDE6";
const PRECODE: &[u8] = b"51BF5D005E5F0BF2A632FB82BDCB6C8882BCB1E5F2B79AD0C50C385641B20441";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Component { Header, LegacyMap, Daa }
impl Component {
    pub(crate) fn tag(self) -> usize {
        match self {Self::Header=>0, Self::LegacyMap=>1, Self::Daa=>2}
    }
    pub(crate) fn source_log(self) -> usize {
        match self {Self::LegacyMap=>MAP_LOG, _=>PAYLOAD_LOG}
    }
    fn owner_log(self) -> usize {
        match self {Self::LegacyMap=>14, _=>19}
    }
}
impl TryFrom<usize> for Component {
    type Error = String;
    fn try_from(tag: usize) -> Result<Self,String> {
        match tag {0=>Ok(Self::Header),1=>Ok(Self::LegacyMap),2=>Ok(Self::Daa),
            _=>Err("composition component tag rejected".into())}
    }
}

// The arrays are immutable, code-owned descriptor fields. The test mutation
// helper below hashes a separate descriptor; compile never accepts one.
pub(crate) const NUMBERS: &[(&[u8],u64)] = &[
    (b"version",1),(b"header-tag",0),(b"map-tag",1),(b"daa-tag",2),(b"zero-tag",3),
    (b"input-log",32),(b"payload-log",31),(b"outer-tag-log",2),(b"row-log",33),
    (b"header-source-log",31),(b"daa-source-log",31),(b"map-source-log",26),
    (b"map-padding",5),(b"map-e",64),(b"parent-n",3073),(b"parent-h",12),
    (b"parent-slots",4096),(b"input-owner-stride",1<<20),
    (b"header-owner-stride",1<<19),(b"daa-owner-stride",1<<19),(b"map-owner-stride",1<<14),
    (b"gate-channels",4),(b"map-bank-base",655654),(b"map-bank-length",7898),
];
pub(crate) const BYTES: &[(&[u8],&[u8])] = &[
    (b"component-order",b"H/M/D"),(b"coordinate-order",b"little-endian"),
    (b"map-padding-convention",b"five-high-zero-coordinates-after-global-owner"),
    (b"gate-convention",b"preserve-c0/c1/c2/c3-and-both-endpoints"),
    (b"native-adapter-domain",b"legacy-native-local-adapter-binding"),
    (b"map-contract",MAP_CONTRACT),(b"composition-contract",PRECODE),
    (b"cap-convention",b"diagnostic-integer-2^64;not-protocol-U"),
];

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct Counts { pub(crate) header: usize, pub(crate) map: usize, pub(crate) daa: usize }

pub(crate) struct LegacyComposition<'a,'p> {
    adapter: &'a LegacyNativeAdapter<'p>,
    map: Map,
    binding: [u8;32],
}

pub(crate) fn embed(component: Component, mut term: Term) -> Result<Term,String> {
    if term.row >= 1usize<<component.source_log()
        || term.gate.left >= 1usize<<INPUT_LOG || term.gate.right >= 1usize<<INPUT_LOG {
        return Err("composition source coordinate rejected".into());
    }
    term.row = component.tag().checked_mul(PAYLOAD).and_then(|base|base.checked_add(term.row))
        .filter(|row|*row < 1usize<<ROW_LOG).ok_or("composition row embedding overflow")?;
    Ok(term)
}

fn append_descriptor(t: &mut Transcript, numeric: Option<usize>, bytes: Option<usize>) {
    for (index,&(label,value)) in NUMBERS.iter().enumerate() {
        t.append_u64(label,if numeric==Some(index) {value^1}else{value});
    }
    for (index,&(label,value)) in BYTES.iter().enumerate() {
        if bytes==Some(index) {
            let mut changed=value.to_vec(); changed[0]^=1; t.append_bytes(label,&changed);
        } else {t.append_bytes(label,value);}
    }
}
fn derive_binding(adapter:&LegacyNativeAdapter<'_>,map:&Map,domain:&[u8],
    numeric:Option<usize>,bytes:Option<usize>) -> Result<[u8;32],String> {
    let mut t=Transcript::new(domain);
    t.append_bytes(b"native-adapter-binding",&adapter.binding());
    adapter.roster().bind(&mut t);
    let b=map.binding();
    t.append_u64(b"map-binding-n",b.n);t.append_u64(b"map-binding-h",b.h as u64);
    t.append_u64(b"map-binding-e",b.e as u64);
    t.append_bytes(b"map-parent-root",&b.parent_root.ok_or("composition map parent root absent")?);
    t.append_bytes(b"map-fixed-contract",MAP_CONTRACT);
    append_descriptor(&mut t,numeric,bytes);
    let mut encoded=Vec::new();
    t.challenge_scalar(b"binding").serialize_compressed(&mut encoded)
        .map_err(|e|format!("composition binding serialization: {e}"))?;
    encoded.try_into().map_err(|_|"composition binding width".into())
}

impl<'a,'p> LegacyComposition<'a,'p> {
    pub(crate) fn compile(adapter:&'a LegacyNativeAdapter<'p>) -> Result<Self,String> {
        adapter.check(adapter.parent(),adapter.input())?;
        let parent=adapter.parent();
        if usize::BITS!=64 || parent.headers()!=3073 || parent.slot_log()!=12 || parent.slots()!=4096
            || adapter.roster().input_log()!=INPUT_LOG || adapter.roster().row_log()!=PAYLOAD_LOG {
            return Err("composition native geometry rejected".into());
        }
        let map=Map::from_parent(parent,64)?;
        let b=map.binding();
        if b.n!=3073 || b.h!=12 || b.e!=64 || b.parent_root!=Some(parent.descriptor().root)
            || 14+b.h!=MAP_LOG || 20+b.h!=INPUT_LOG {
            return Err("composition map binding rejected".into());
        }
        let binding=derive_binding(adapter,&map,DOMAIN,None,None)?;
        Ok(Self{adapter,map,binding})
    }
    pub(crate) fn check(&self,adapter:&LegacyNativeAdapter<'_>) -> Result<(),String> {
        if !std::ptr::eq(self.adapter as *const _,adapter as *const _) {
            return Err("composition adapter identity mismatch".into());
        }
        self.adapter.check(self.adapter.parent(),self.adapter.input())
    }
    pub(crate) fn input_log(&self)->usize {INPUT_LOG}
    pub(crate) fn row_log(&self)->usize {ROW_LOG}
    pub(crate) fn binding(&self)->[u8;32] {self.binding}
    pub(crate) fn bind(&self,t:&mut Transcript) {
        t.append_bytes(b"legacy-composition-domain",DOMAIN);
        t.append_bytes(b"legacy-composition-binding",&self.binding);
        append_descriptor(t,None,None);
    }
    pub(crate) fn visit_owner_terms(&self,owner:usize,
        mut sink:impl FnMut(Term)->Result<(),String>) -> Result<Counts,String> {
        self.check(self.adapter)?;
        if owner>=4096 {return Err("composition owner outside domain".into());}
        let mut counts=Counts::default();
        let mut emit=|component:Component,term:Term| -> Result<(),String> {
            if term.row>>component.owner_log()!=owner {
                return Err("composition source owner mismatch".into());
            }
            let mapped=embed(component,term)?;
            sink(mapped)?;
            match component {Component::Header=>counts.header+=1,
                Component::LegacyMap=>counts.map+=1,Component::Daa=>counts.daa+=1}
            Ok(())
        };
        let h=self.adapter.roster().visit_header_terms(owner as u64,|term|emit(Component::Header,term))?;
        for term in self.adapter.terms(owner)? {emit(Component::LegacyMap,term)?;}
        let d=self.adapter.roster().visit_owner_terms(owner as u64,|term|emit(Component::Daa,term))?;
        if counts.header!=h.emitted || counts.daa!=d.lanes.iter().sum::<usize>() {
            return Err("composition emission count mismatch".into());
        }
        Ok(counts)
    }
    pub(crate) fn coefficients(&self,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String> {
        if (r.len(),u.len(),v.len())!=(ROW_LOG,INPUT_LOG,INPUT_LOG) {
            return Err("composition point dimensions rejected".into());
        }
        self.check(self.adapter)?;
        let h=self.adapter.roster().header_coefficients(&r[..PAYLOAD_LOG],u,v)?;
        let m=self.map.coefficients(&r[..MAP_LOG],u,v)?;
        let d=self.adapter.roster().coefficients(&r[..PAYLOAD_LOG],u,v)?;
        let z0=r[31];let z1=r[32];
        let weights=[(Fr::one()-z0)*(Fr::one()-z1),z0*(Fr::one()-z1),
            (Fr::one()-z0)*z1];
        let padding=r[MAP_LOG..PAYLOAD_LOG].iter().fold(Fr::one(),|a,x|a*(Fr::one()-x));
        Ok(std::array::from_fn(|k|weights[0]*h[k]+weights[1]*padding*m[k]+weights[2]*d[k]))
    }
    // Isolated binding hashes only; these never construct or alter a consumer.
    pub(crate) fn descriptor_mutant_for_test(&self,numeric:Option<usize>,bytes:Option<usize>,
        wrong_domain:bool)->Result<[u8;32],String> {
        if numeric.is_some_and(|i|i>=NUMBERS.len()) || bytes.is_some_and(|i|i>=BYTES.len()) {
            return Err("composition descriptor mutation index".into());
        }
        derive_binding(self.adapter,&self.map,if wrong_domain {b"wrong-composition-domain"}else{DOMAIN},numeric,bytes)
    }
}

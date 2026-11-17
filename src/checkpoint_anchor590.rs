//! Diagnostic checkpoint extraction under one verified Historical51 tree.
//! No FullS, work-maturity, audit readiness or production-security result.
use super::*;
use crate::native_work_opening::MAX_OPENING_BYTES;

const MAGIC:&[u8;8]=b"NCK59001";
pub(crate) const MAX_PACKET_BYTES:usize=192*1024;
const K0:u64=64;

/// Diagnostic launch contract only. The pure packet verifier below never
/// inspects environment variables. Requiring the path value is separate.
pub(crate) fn validate_cold_environment_names(
    names:impl IntoIterator<Item=std::ffi::OsString>)->Result<(),String> {
    for name in names {
        let text=name.to_string_lossy();
        // Windows treats environment names case-insensitively.
        if text.as_bytes().get(..8).is_some_and(|prefix|prefix.eq_ignore_ascii_case(b"NIPOPOW_"))
            &&!text.eq_ignore_ascii_case("NIPOPOW_C590_PACKET_PATH") {
            return Err("C590 cold receiver permits only NIPOPOW_C590_PACKET_PATH".into());
        }
    }
    Ok(())
}

pub(crate) fn diagnostic_profile()->Vec<u8> {
    let mut out=b"nipopow-checkpoint-anchor-diagnostic-v1;network=ergo-mainnet;raw=canonical-header-v1;opening=NIPOWP01;key=fixed32-testonly;native=8995ff243b140e7fe716bd3204423dd35690c2e4;".to_vec();
    out.extend(crate::header_order::MAINNET_GENESIS);
    out.extend(crate::work_tree_fixed_hash::PROFILE_PREFIX);
    for n in [K0,95,514,32] {out.extend(n.to_le_bytes());}out
}

/// The exact immutable proof buffers and key material that actually passed
/// verification. There is no constructor from a seal, digest or caller claim.
pub(crate) struct VerifiedBase<'packet> {
    bytes:Historical51PublicBytes<'packet>,key:&'packet[u8],metadata:&'packet[u8],
    history:VerifiedHistorical51Prefix,
}
impl<'packet> VerifiedBase<'packet> {
    pub(crate) fn verify(bytes:Historical51PublicBytes<'packet>,key:&'packet[u8],metadata:&'packet[u8])
        ->Result<Self,String> {
        let mut diagnostic=Historical51Diagnostics::default();
        let history=verify_and_seal_historical_h12_prefix51(&bytes,key,metadata,
            &Historical51TrustedKeyPolicy::fixed32_testonly(),&mut diagnostic)?;
        if diagnostic.role_completions!=[1;7] || diagnostic.pcs_completions!=1 || diagnostic.successes!=1 {
            return Err("checkpoint base atomic completion".into());
        }
        Ok(Self {bytes,key,metadata,history})
    }
    pub(crate) fn history(&self)->&VerifiedHistorical51Prefix {&self.history}
    pub(crate) fn checkpoint(self,profile:&[u8],h:u64,raw_claim:&[u8],audit_claim:[u8;28],
        anchor_h:&[u8],anchor_f:&[u8])->Result<VerifiedCheckpoint<'packet>,String> {
        let data=derive(&self,profile,h,raw_claim,audit_claim,anchor_h,anchor_f)?;
        Ok(VerifiedCheckpoint {base:self,data,anchor_h:anchor_h.to_vec(),anchor_f:anchor_f.to_vec()})
    }
}

struct Derived {h:u64,f:u64,raw:Vec<u8>,floor:[u8;28],audit:[u8;28]}
/// Only the verified base consumed by checkpoint() is retained. encode() has
/// no separate base/proof/digest argument and includes both structural anchors.
pub(crate) struct VerifiedCheckpoint<'packet> {
    base:VerifiedBase<'packet>,data:Derived,anchor_h:Vec<u8>,anchor_f:Vec<u8>,
}
impl VerifiedCheckpoint<'_> {
    pub(crate) fn h(&self)->u64 {self.data.h}
    pub(crate) fn f(&self)->u64 {self.data.f}
    pub(crate) fn header_raw(&self)->&[u8] {&self.data.raw}
    pub(crate) fn floor_work(&self)->[u8;28] {self.data.floor}
    pub(crate) fn audit_work(&self)->[u8;28] {self.data.audit}
    pub(crate) fn history(&self)->&VerifiedHistorical51Prefix {&self.base.history}
    /// Literal structural-certificate encoding for a future audit. This method
    /// neither queries H_A nor certifies the missing FullS/maturity conditions.
    pub(crate) fn encode(&self)->Result<Vec<u8>,String> {
        encode_parts(&self.base.bytes,self.base.key,self.base.metadata,&diagnostic_profile(),
            self.data.h,&self.data.raw,self.data.audit,&self.anchor_h,&self.anchor_f)
    }
}

fn work95(value:[u8;28])->bool {value[..16].iter().all(|b|*b==0)&&value[16]&0x80==0}
fn difference(total:[u8;28],floor:[u8;28])->Result<[u8;28],String> {
    if !work95(total)||!work95(floor)||floor>=total {return Err("checkpoint positive 95-bit work domain".into());}
    let mut out=[0u8;28];let mut borrow=0i16;
    for i in (0..28).rev() {
        let n=i16::from(total[i])-i16::from(floor[i])-borrow;
        if n<0 {out[i]=(n+256)as u8;borrow=1;}else{out[i]=n as u8;borrow=0;}
    }
    if borrow!=0||!work95(out)||out==[0;28] {return Err("checkpoint work subtraction".into());}Ok(out)
}
fn floor_height(h:u64,n:u64)->Result<u64,String> {
    if h<2 {return Err("checkpoint query below height2".into());}
    let mature=h.checked_add(K0).ok_or("checkpoint height overflow")?;
    let f=mature.checked_sub(1).ok_or("checkpoint floor overflow")?;
    if n<mature {return Err("checkpoint requires n >= h+64".into());}Ok(f)
}
fn lower(encoded:&[u8])->Result<[u8;28],String> {
    if !(70..=MAX_OPENING_BYTES).contains(&encoded.len()) {return Err("checkpoint opening extent".into());}
    encoded[12..40].try_into().map_err(|_|"checkpoint opening lower".into())
}
fn derive(base:&VerifiedBase<'_>,profile:&[u8],h:u64,raw_claim:&[u8],audit_claim:[u8;28],
    anchor_h:&[u8],anchor_f:&[u8])->Result<Derived,String> {
    if profile!=diagnostic_profile() {return Err("checkpoint unsupported diagnostic profile".into());}
    if raw_claim.is_empty()||raw_claim.len()>514||!work95(audit_claim) {return Err("checkpoint claim extent/95-bit bound".into());}
    let f=floor_height(h,base.history.headers()as u64)?;
    let first=base.history.verify_work_opening(lower(anchor_h)?,anchor_h).map_err(|e|e.to_string())?;
    let floor=base.history.verify_work_opening(lower(anchor_f)?,anchor_f).map_err(|e|e.to_string())?;
    if !std::ptr::eq(first.history(),&base.history)||!std::ptr::eq(floor.history(),&base.history)
        ||u64::from(first.member().height())!=h||u64::from(floor.member().height())!=f
        ||u64::from(first.member().position())+2!=h||u64::from(floor.member().position())+2!=f {
        return Err("checkpoint exact h/f and sealed-history identity".into());
    }
    if first.member().raw()!=raw_claim {return Err("checkpoint public RAW differs from authenticated header".into());}
    let floor_work=floor.member().interval_be28().1;
    let audit=difference(base.history.total_be28(),floor_work)?;
    if audit_claim!=audit {return Err("checkpoint public F differs from exact total-floor".into());}
    Ok(Derived {h,f,raw:first.member().raw().to_vec(),floor:floor_work,audit})
}

fn put(out:&mut Vec<u8>,bytes:&[u8],cap:usize)->Result<(),String> {
    if bytes.len()>cap {return Err("checkpoint component extent".into());}
    out.extend(u32::try_from(bytes.len()).map_err(|_|"checkpoint component width")?.to_le_bytes());
    out.extend(bytes);
    if out.len()>MAX_PACKET_BYTES {return Err("checkpoint packet extent".into());}Ok(())
}
fn encode_parts(base:&Historical51PublicBytes<'_>,key:&[u8],metadata:&[u8],profile:&[u8],h:u64,
    raw:&[u8],audit:[u8;28],anchor_h:&[u8],anchor_f:&[u8])->Result<Vec<u8>,String> {
    let mut out=MAGIC.to_vec();put(&mut out,profile,512)?;out.extend(h.to_le_bytes());
    put(&mut out,raw,514)?;out.extend(audit);
    put(&mut out,base.frame,571)?;put(&mut out,key,33264)?;put(&mut out,metadata,40)?;
    put(&mut out,base.commitment,384)?;
    for (role,bytes)in base.roles.iter().enumerate() {put(&mut out,bytes,if role==3{5696}else{7264})?;}
    put(&mut out,base.common,HISTORICAL51_COMMON_BOUND)?;
    put(&mut out,anchor_h,MAX_OPENING_BYTES)?;put(&mut out,anchor_f,MAX_OPENING_BYTES)?;Ok(out)
}
struct Parsed<'packet> {
    base:Historical51PublicBytes<'packet>,key:&'packet[u8],metadata:&'packet[u8],
    profile:&'packet[u8],h:u64,raw:&'packet[u8],audit:[u8;28],anchor_h:&'packet[u8],anchor_f:&'packet[u8],
}
fn parse(packet:&[u8])->Result<Parsed<'_>,String> {
    if packet.len()>MAX_PACKET_BYTES||packet.get(..8)!=Some(MAGIC) {return Err("checkpoint packet magic/extent".into());}
    struct Cursor<'a>{bytes:&'a[u8],at:usize}
    impl<'a> Cursor<'a> {
        fn take(&mut self,n:usize)->Result<&'a[u8],String> {
            let end=self.at.checked_add(n).ok_or("checkpoint offset overflow")?;
            let value=self.bytes.get(self.at..end).ok_or("checkpoint truncated component")?;self.at=end;Ok(value)
        }
        fn blob(&mut self,min:usize,max:usize)->Result<&'a[u8],String> {
            let n=u32::from_le_bytes(self.take(4)?.try_into().map_err(|_|"checkpoint length width")?)as usize;
            if !(min..=max).contains(&n) {return Err("checkpoint declared component extent".into());}self.take(n)
        }
    }
    let mut c=Cursor {bytes:packet,at:8};let profile=c.blob(1,512)?;
    let h=u64::from_le_bytes(c.take(8)?.try_into().map_err(|_|"checkpoint height width")?);
    let raw=c.blob(1,514)?;let audit=c.take(28)?.try_into().map_err(|_|"checkpoint F width")?;
    let frame=c.blob(571,571)?;let key=c.blob(33264,33264)?;let metadata=c.blob(40,40)?;
    let commitment=c.blob(384,384)?;let mut roles:[&[u8];7]=[&[];7];
    for(role,bytes)in roles.iter_mut().enumerate() {*bytes=c.blob(if role==3{5696}else{7264},if role==3{5696}else{7264})?;}
    let common=c.blob(1,HISTORICAL51_COMMON_BOUND)?;
    let anchor_h=c.blob(70,MAX_OPENING_BYTES)?;let anchor_f=c.blob(70,MAX_OPENING_BYTES)?;
    if c.at!=packet.len() {return Err("checkpoint packet trailing bytes".into());}
    Ok(Parsed {base:Historical51PublicBytes {frame,commitment,roles,common},key,metadata,profile,h,raw,audit,anchor_h,anchor_f})
}
pub(crate) fn verify_packet(packet:&[u8])->Result<VerifiedCheckpoint<'_>,String> {
    let p=parse(packet)?;
    // Cheap profile/height bounds precede the expensive base verification.
    if p.profile!=diagnostic_profile() {return Err("checkpoint unsupported diagnostic profile".into());}
    floor_height(p.h,3073)?;
    let base=VerifiedBase::verify(p.base,p.key,p.metadata)?;
    let result=base.checkpoint(p.profile,p.h,p.raw,p.audit,p.anchor_h,p.anchor_f)?;
    if result.encode()?.as_slice()!=packet {return Err("checkpoint noncanonical packet".into());}Ok(result)
}

#[path="checkpoint_anchor590_tests.rs"]
mod tests;

pub(crate) fn native_negative_controls(result:&VerifiedCheckpoint<'_>)->Result<usize,String> {
    tests::native_negatives(result)
}

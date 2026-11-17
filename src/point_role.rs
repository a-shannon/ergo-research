//! Canonical all-physical-owner POINT role under one expected original-X C.
//! Role verification is not a complete history or native-source certificate.
use ark_bn254::Fr;
use ark_ff::One;
use blake2::{digest::consts::U32, Blake2b, Digest};
use dory_pcs::backends::arkworks::{ArkDoryProof, ArkGT, ArkworksVerifierSetup};
use std::{path::Path, sync::{Arc,OnceLock}};
use crate::{gkr::{self, GkrError, GkrProof, InputClaim}, packed::{self, PackedCommitted, PackedFile},
    pcs, point_membership::{self, Compiled}, sparse::{self, Circuit}, transcript::Transcript,
    verifier_key::{self, AdmittedVerifierKey}, work_tree_history_plan::WorkTreeHistoryPlan,
    work_tree_layout as layout};

const VERSION: &[u8] = b"point-same-x-v1";
const POLICY: &[u8] = b"all-physical-owners-canonical-membership-v1";
const CODEC: &[u8] = b"ergo-header-core-canonical-v1-v2-max514";
const BANK: usize = crate::segment_points::POINT_OFFSET;

/// Shared algebra only. Legacy verification retains exactly sparse::bind;
/// ordinary public verification adds its expected statement BEFORE this call.
pub(crate) struct PointMath<'a> {
    pub(crate) base: &'a Circuit,
    shape: sparse::Shape,
    copies_log: usize,
    input_log: usize,
    row_log: usize,
    common_log: usize,
}
impl<'a> PointMath<'a> {
    pub(crate) fn dimensions(base: &'a Circuit, h: usize, input: usize, row: usize, common: usize)
        -> Result<Self, String> {
        if h > 21 { return Err("point adapter copy dimension".into()); }
        let shape = sparse::validate(base, 0).map_err(|e| e.to_string())?;
        if shape.input_bits != 13 || shape.row_bits != 14 || base.terms.len() != 288158 {
            return Err("point adapter canonical base geometry".into());
        }
        let plus = |n: usize| n.checked_add(h).ok_or("point adapter dimension overflow");
        if input != plus(13)? || row != plus(14)? || common != plus(20)? {
            return Err("point adapter joined geometry".into());
        }
        for dimension in [input, row, common] {
            1usize.checked_shl(dimension as u32).ok_or("point adapter domain overflow")?;
        }
        input.checked_mul(7).and_then(|n| n.checked_add(3)).and_then(|n| n.checked_mul(32))
            .ok_or("point adapter proof extent overflow")?;
        Ok(Self { base, shape, copies_log: h, input_log: input, row_log: row, common_log: common })
    }
    /// Bounded legacy algebra fixture only. It cannot construct an ordinary
    /// POINT statement or bypass the canonical dimensions constructor.
    #[cfg(test)]
    pub(crate) fn legacy_toy_coefficients_fixture(base: &'a Circuit, h: usize) -> Result<Self,String> {
        if base.input_len != 4 || base.row_count != 2 || h > 3 {
            return Err("point legacy toy fixture geometry".into());
        }
        sparse::validate(base,h).map_err(|e|e.to_string())?;
        let shape=sparse::validate(base,0).map_err(|e|e.to_string())?;
        Ok(Self { base,shape,copies_log:h,input_log:2+h,row_log:1+h,common_log:9+h })
    }
    pub(crate) fn coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], GkrError> {
        if r.len() != self.row_log || u.len() != self.input_log || v.len() != self.input_log {
            return Err(GkrError::PointDimension);
        }
        let (rb, ib) = (self.shape.row_bits, self.shape.input_bits);
        let mut out = sparse::wiring(self.base, &self.shape, &r[..rb], &u[..ib], &v[..ib])?;
        let high = r[rb..].iter().zip(&u[ib..]).zip(&v[ib..]).fold(Fr::one(), |a, ((r,u),v)|
            a * ((Fr::one()-r)*(Fr::one()-u)*(Fr::one()-v) + *r**u**v));
        for c in &mut out { *c *= high; }
        Ok(out)
    }
    fn verify(&self, proof: &GkrProof, transcript: &mut Transcript) -> Result<InputClaim, GkrError> {
        gkr::verify_with_wiring(&[self.input_log], 1usize << self.row_log, proof, transcript,
            |t| sparse::bind(self.base, self.copies_log, t),
            |layer,r,u,v| if layer == 0 { self.coefficients(r,u,v) } else { Err(GkrError::PointDimension) })
    }
    #[cfg(test)]
    pub(crate) fn verify_legacy(&self, proof: &GkrProof, transcript: &mut Transcript) -> Result<InputClaim,GkrError> {
        self.verify(proof,transcript)
    }
    pub(crate) fn project(&self, point: &[Fr]) -> Result<Vec<Fr>, String> {
        if point.len() != self.input_log { return Err("point adapter projection dimension".into()); }
        let out = layout::embed_bank(BANK, point_membership::POINT_WIDTH, self.copies_log, point)?;
        if out.len() != self.common_log { return Err("point adapter projected geometry".into()); }
        Ok(out)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Error { Statement(String), Producer(String), GkrEncoding(String), PcsEncoding(String), Gkr(GkrError), Pcs(String) }

#[derive(Clone, Debug, PartialEq, Eq)]
struct Context {
    // N,g,L,role input,role rows,common X,bank offset,bank width.
    numbers: [u64; 8],
    native_profile: [u8; 32],
    codec: Vec<u8>,
    template: String,
    aliases: String,
    policy: Vec<u8>,
}
impl Context {
    fn expected(parent: &WorkTreeHistoryPlan, canonical: &Compiled) -> Result<Self, String> {
        let n = parent.headers(); let g = parent.slot_log(); let slots = parent.slots();
        if n < 3 || g > 21 || slots != 1usize << g || n.next_power_of_two() != slots as u64
            || BANK != 96 * 8192 || canonical.circuit.input_len != 8192
            || canonical.circuit.row_count != 16384 || canonical.circuit.terms.len() != 288158
            || ergo_header_core::MAX_HEADER_BYTES != 514 {
            return Err("POINT expected parent/template/codec geometry".into());
        }
        let mut profile = crate::work_tree_fixed_hash::PROFILE_PREFIX.to_vec();
        profile.extend_from_slice(&crate::header_order::MAINNET_GENESIS);
        let aliases: Vec<_> = parent.header_boundary().canonical_circuit().terms.iter()
            .filter(|term| (405784..405850).contains(&term.row)).cloned().collect();
        if aliases.len() != 66 * 8 { return Err("POINT expected HEADER alias census".into()); }
        Ok(Self { numbers: [n,g as u64,slots as u64,(13+g) as u64,(14+g) as u64,
            (20+g) as u64,BANK as u64,8192], native_profile: Blake2b::<U32>::digest(profile).into(),
            codec: CODEC.to_vec(), template: layout::hash_terms(&canonical.circuit.terms),
            aliases: layout::hash_terms(&aliases), policy: POLICY.to_vec() })
    }
    fn require(&self, expected: &Self) -> Result<(), String> {
        for i in 0..8 { if self.numbers[i] != expected.numbers[i] { return Err(format!("POINT context number {i}")); } }
        for (name, same) in [("native profile",self.native_profile==expected.native_profile),
            ("codec",self.codec==expected.codec),("template",self.template==expected.template),
            ("aliases",self.aliases==expected.aliases),("policy",self.policy==expected.policy)] {
            if !same { return Err(format!("POINT context {name}")); }
        }
        Ok(())
    }
}

fn pinned_bytes(log: usize) -> Result<&'static [u8], String> {
    match log {
        22 => Ok(include_bytes!("../fixtures/verifier-keys-v1/log22.vk")),
        41 => Ok(include_bytes!("../fixtures/verifier-keys-v1/log41.vk")),
        _ => Err("POINT requires an existing compatible key22 or key41".into()),
    }
}
fn pinned_expected_id(log:usize)->Result<[u8;32],String> {
    static KEY22:OnceLock<Result<[u8;32],String>>=OnceLock::new();
    static KEY41:OnceLock<Result<[u8;32],String>>=OnceLock::new();
    let expected=match log {
        22=>KEY22.get_or_init(||verifier_key::admit(22,
            include_bytes!("../fixtures/verifier-keys-v1/log22.vk")).map(|key|*key.id())),
        41=>KEY41.get_or_init(||verifier_key::admit(41,
            include_bytes!("../fixtures/verifier-keys-v1/log41.vk")).map(|key|*key.id())),
        _=>return Err("POINT requires an existing compatible key22 or key41".into()),
    };
    expected.as_ref().map(|id|*id).map_err(Clone::clone)
}
fn require_key(key: &AdmittedVerifierKey, log: usize) -> Result<(), String> {
    let bytes = pinned_bytes(log)?; let expected = pinned_expected_id(log)?;
    if key.log_n() != log || key.id() != &expected
        || pcs::encode(&ArkworksVerifierSetup(key.verifier().clone()))?.as_slice() != bytes {
        return Err("POINT expected admitted key identity".into());
    }
    Ok(())
}

/// Immutable expected-input material, created only by the statement constructor.
/// Parent and graph identity prevent a cache from being transplanted by geometry.
struct ExpectedContextSeal<'p> {
    parent:&'p WorkTreeHistoryPlan,
    canonical:Arc<Compiled>,
    context:Context,
}

/// Expected public fields; no witness, producer or source handle is retained.
#[derive(Clone)]
pub(crate) struct PointPublicStatement<'p> {
    parent: &'p WorkTreeHistoryPlan,
    canonical: Arc<Compiled>,
    expected:Arc<ExpectedContextSeal<'p>>,
    context: Context,
    key_id: [u8; 32],
    commitment_bytes: Vec<u8>,
}
impl<'p> PointPublicStatement<'p> {
    pub(crate) fn new(parent: &'p WorkTreeHistoryPlan, key: &AdmittedVerifierKey, commitment_bytes: &[u8])
        -> Result<Self, Error> {
        let canonical = Arc::new(point_membership::build().map_err(Error::Statement)?);
        Self::from_canonical(parent,canonical,key,commitment_bytes)
    }
    fn from_canonical(parent: &'p WorkTreeHistoryPlan, canonical: Arc<Compiled>, key: &AdmittedVerifierKey,
        commitment_bytes: &[u8]) -> Result<Self, Error> {
        let context = Context::expected(parent,&canonical).map_err(Error::Statement)?;
        require_key(key,context.numbers[5] as usize).map_err(Error::Statement)?;
        pcs::decode_commitment(commitment_bytes).map_err(Error::Statement)?;
        let expected=Arc::new(ExpectedContextSeal {parent,canonical:Arc::clone(&canonical),context:context.clone()});
        Ok(Self { parent,canonical,expected,context,key_id:*key.id(),commitment_bytes:commitment_bytes.to_vec() })
    }
    fn require(&self, key: &AdmittedVerifierKey) -> Result<(), Error> {
        if !std::ptr::eq(self.parent,self.expected.parent) {
            return Err(Error::Statement("POINT expected parent identity".into()));
        }
        if !Arc::ptr_eq(&self.canonical,&self.expected.canonical) {
            return Err(Error::Statement("POINT expected canonical identity".into()));
        }
        let g=self.parent.slot_log();
        if g>21 || self.parent.headers()!=self.expected.context.numbers[0]
            || g as u64!=self.expected.context.numbers[1]
            || self.parent.slots()as u64!=self.expected.context.numbers[2]
            || self.canonical.circuit.input_len!=8192 || self.canonical.circuit.row_count!=16384
            || self.canonical.circuit.terms.len()!=288158 || BANK!=786432
            || point_membership::POINT_WIDTH!=8192 || ergo_header_core::MAX_HEADER_BYTES!=514 {
            return Err(Error::Statement("POINT expected live geometry".into()));
        }
        self.context.require(&self.expected.context).map_err(Error::Statement)?;
        require_key(key,self.context.numbers[5] as usize).map_err(Error::Statement)?;
        if self.key_id != *key.id() { return Err(Error::Statement("POINT statement key ID".into())); }
        pcs::decode_commitment(&self.commitment_bytes).map_err(Error::Statement)?;
        Ok(())
    }
    fn math(&self) -> Result<PointMath<'_>, Error> {
        let g = self.context.numbers[1] as usize;
        PointMath::dimensions(&self.canonical.circuit,g,13+g,14+g,20+g).map_err(Error::Statement)
    }
    pub(crate) fn bind(&self, key: &AdmittedVerifierKey, transcript: &mut Transcript) -> Result<(), Error> {
        self.require(key)?;
        if transcript.challenges() != 0 { return Err(Error::Statement("POINT prefix already challenged".into())); }
        // Exact order is part of point-same-x-v1. sparse::bind follows this
        // public frame in both ordinary proof construction and verification.
        transcript.append_bytes(b"point-role",VERSION);
        self.parent.bind(transcript);
        for number in self.context.numbers { transcript.append_u64(b"point-shape",number); }
        transcript.append_bytes(b"point-native-profile",&self.context.native_profile);
        transcript.append_bytes(b"point-codec",&self.context.codec);
        transcript.append_bytes(b"point-template",self.context.template.as_bytes());
        transcript.append_bytes(b"point-header-aliases",self.context.aliases.as_bytes());
        transcript.append_bytes(b"point-owner-policy",&self.context.policy);
        transcript.append_bytes(b"point-key",&self.key_id);
        transcript.append_bytes(b"point-C",&self.commitment_bytes);
        Ok(())
    }
}

pub(crate) struct PointPublicVerifier<'p,'k> { statement: PointPublicStatement<'p>, key: &'k AdmittedVerifierKey, commitment: ArkGT }
impl<'p,'k> PointPublicVerifier<'p,'k> {
    pub(crate) fn new(statement: PointPublicStatement<'p>, key: &'k AdmittedVerifierKey) -> Result<Self, Error> {
        statement.require(key)?;
        let commitment = pcs::decode_commitment(&statement.commitment_bytes).map_err(Error::Statement)?;
        Ok(Self { statement,key,commitment })
    }
    /// A POINT proof and mapped PCS opening are both mandatory. Only their
    /// successful joined result publishes a role-scoped claim/continuation.
    pub(crate) fn verify_on(&self, proof: &GkrProof, opening: &ArkDoryProof, transcript: &mut Transcript)
        -> Result<InputClaim, Error> {
        let mut next = transcript.clone(); self.statement.bind(self.key,&mut next)?;
        let math = self.statement.math()?;
        let local = math.verify(proof,&mut next).map_err(Error::Gkr)?;
        let point = math.project(&local.point).map_err(Error::Statement)?;
        pcs::verify_admitted(self.commitment,local.value,&point,opening,self.key,&mut next).map_err(Error::Pcs)?;
        *transcript = next;
        Ok(InputClaim { point,value:local.value })
    }
    pub(crate) fn verify_encoded_on(&self, proof: &[u8], opening: &[u8], transcript: &mut Transcript)
        -> Result<InputClaim, Error> {
        self.statement.require(self.key)?;
        if transcript.challenges() != 0 { return Err(Error::Statement("POINT prefix already challenged".into())); }
        let proof = gkr::decode_dimensions(&[self.statement.context.numbers[3] as usize],proof).map_err(Error::GkrEncoding)?;
        let opening = pcs::decode_proof(opening,self.statement.context.numbers[5] as usize).map_err(Error::PcsEncoding)?;
        self.verify_on(&proof,&opening,transcript)
    }
}

fn producer_admission(canonical: &Compiled, g: usize) -> Result<(), Error> {
    sparse::validate(&canonical.circuit,g).map_err(|e| Error::Producer(e.to_string()))?;
    if 20+g > pcs::MAX_LOG_N { return Err(Error::Producer("POINT packed producer dimension".into())); }
    pinned_bytes(20+g).map_err(Error::Producer)?;
    Ok(())
}

pub(crate) struct PointProof { pub(crate) gkr: GkrProof, pub(crate) opening: ArkDoryProof }

/// Sealed ownership: no borrowed commit state, circuit or alternative reader.
pub(crate) struct PointProducer<'p> {
    parent: &'p WorkTreeHistoryPlan,
    source: PackedFile,
    setup: pcs::Setup,
    committed: PackedCommitted,
    key: AdmittedVerifierKey,
    statement: PointPublicStatement<'p>,
}
#[cfg(test)]
#[derive(Default,Debug,PartialEq,Eq)]
struct PreparationAudit { opens:usize, setups:usize, commits:usize }

impl<'p> PointProducer<'p> {
    pub(crate) fn new(parent: &'p WorkTreeHistoryPlan, path: impl AsRef<Path>) -> Result<Self, Error> {
        Self::create(parent,path.as_ref(),#[cfg(test)] None)
    }
    fn create(parent: &'p WorkTreeHistoryPlan, path: &Path,
        #[cfg(test)] mut audit: Option<&mut PreparationAudit>) -> Result<Self, Error> {
        let canonical = Arc::new(point_membership::build().map_err(Error::Producer)?);
        // This is intentionally BEFORE open, setup, commit, any source read
        // or transcript construction. H21 fails here with RepetitionLimit.
        producer_admission(&canonical,parent.slot_log())?;
        let context = Context::expected(parent,&canonical).map_err(Error::Producer)?;
        let log = context.numbers[5] as usize;
        #[cfg(test)] if let Some(a) = audit.as_deref_mut() { a.opens += 1; }
        let source = PackedFile::open(path,log).map_err(Error::Producer)?;
        if source.input_len() != 1usize << log { return Err(Error::Producer("POINT original-X source length".into())); }
        #[cfg(test)] if let Some(a) = audit.as_deref_mut() { a.setups += 1; }
        let setup = pcs::generate_setup(log).map_err(Error::Producer)?;
        let key = verifier_key::admit(log,pinned_bytes(log).map_err(Error::Producer)?).map_err(Error::Producer)?;
        require_key(&key,log).map_err(Error::Producer)?;
        if setup.id != *key.id() || pcs::encode(&ArkworksVerifierSetup(setup.verifier.clone())).map_err(Error::Producer)?.as_slice()
            != pinned_bytes(log).map_err(Error::Producer)? { return Err(Error::Producer("POINT generated setup identity".into())); }
        #[cfg(test)] if let Some(a) = audit.as_deref_mut() { a.commits += 1; }
        let committed = packed::commit(&source,&setup).map_err(Error::Producer)?;
        let bytes = pcs::encode_commitment(&committed.commitment).map_err(Error::Producer)?;
        let statement = PointPublicStatement::from_canonical(parent,canonical,&key,&bytes)?;
        Ok(Self { parent,source,setup,committed,key,statement })
    }
    pub(crate) fn statement(&self) -> PointPublicStatement<'p> { self.statement.clone() }
    pub(crate) fn prove_on(&self, transcript: &mut Transcript) -> Result<PointProof, Error> {
        producer_admission(&self.statement.canonical,self.parent.slot_log())?;
        if self.source.input_len() != 1usize << (20+self.parent.slot_log()) {
            return Err(Error::Producer("POINT original-X source length".into()));
        }
        let mut next = transcript.clone(); self.statement.bind(&self.key,&mut next)?;
        let (proof,local) = crate::sparse_stream_boolean::prove(&self.statement.canonical.circuit,
            self.parent.slot_log(),|owner| self.source.read_copy(8192,owner*128+96)
                .map_err(|_| GkrError::InvalidInputWidth),&mut next)
            .map_err(|e| Error::Producer(e.to_string()))?;
        let point = self.statement.math()?.project(&local.point).map_err(Error::Producer)?;
        if self.source.evaluate(&point).map_err(Error::Producer)? != local.value {
            return Err(Error::Producer("POINT mapped claim differs from held original X".into()));
        }
        let opening = packed::open(&self.committed,&self.source,&point,&self.setup,&mut next).map_err(Error::Producer)?;
        *transcript = next;
        Ok(PointProof { gkr:proof,opening })
    }
}

#[cfg(test)]
#[path="point_role_tests.rs"]
mod tests;

/// Test-only borrowed path; binders/math and original-X projection stay shared.
#[cfg(test)]
pub(crate) fn c573_prove_owned_on(lease:&crate::numeric_daa_authenticated::C573PcsLease<'_,'_>,
    transcript:&mut Transcript)->Result<(Vec<u8>,Vec<u8>),Error>
{
    lease.check().map_err(Error::Producer)?;let parent=lease.parent();
    let canonical=Arc::new(point_membership::build().map_err(Error::Producer)?);
    producer_admission(&canonical,parent.slot_log())?;
    let statement=PointPublicStatement::from_canonical(parent,canonical,lease.key(),lease.commitment_bytes())?;
    let mut next=transcript.clone();statement.bind(lease.key(),&mut next)?;
    let(proof,local)=crate::sparse_stream_boolean::prove(&statement.canonical.circuit,parent.slot_log(),
        |owner|lease.source().read_copy(8192,owner*128+96).map_err(|_|GkrError::InvalidInputWidth),&mut next)
        .map_err(|e|Error::Producer(e.to_string()))?;
    let point=statement.math()?.project(&local.point).map_err(Error::Producer)?;
    if point.len()!=22||lease.source().evaluate(&point).map_err(Error::Producer)?!=local.value{
        return Err(Error::Producer("C573 POINT mapped original-X claim".into()));
    }
    let opening=packed::open(lease.committed(),lease.source(),&point,lease.setup(),&mut next).map_err(Error::Producer)?;
    let g=gkr::encode_proof(&proof).map_err(Error::GkrEncoding)?;
    let p=pcs::encode_proof(&opening).map_err(Error::PcsEncoding)?;
    if g.len()!=3456||p.len()!=29421{return Err(Error::Producer("C573 POINT encoded extent".into()));}
    gkr::decode_dimensions(&[15],&g).map_err(Error::GkrEncoding)?;pcs::decode_proof(&p,22).map_err(Error::PcsEncoding)?;
    *transcript=next;Ok((g,p))
}

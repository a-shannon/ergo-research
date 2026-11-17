//! Bounded N3/N4 common-commitment experiment; not a production packet or admission path.
use crate::{
    core_pool_boolean,
    daa_history_roster::{DaaHistoryRoster, HeaderCounts, OwnerClass},
    gkr::{self, GkrError, GkrProof, InputClaim},
    header_adjacency_layout::HeaderAdjacencyLayout,
    header_metadata_order_layout::HeaderMetadataOrderLayout,
    historical_prefix_height_work::HeightWork,
    historical_prefix_witness as witness,
    opening_batch::{self, Claim},
    packed::{self, PackedFile, PackedFileWriter},
    pcs, point_membership, segment_points,
    sparse::{self, Circuit, Term},
    sparse_stream_boolean, sparse_stream_roster,
    transcript::Transcript,
    verifier_key, work_tree_fixed_hash as fixed,
    work_tree_history_plan::WorkTreeHistoryPlan,
    work_tree_layout as layout, work_tree_wiring,
};
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use blake2::{digest::consts::U32, Blake2b, Digest};
use std::{fs::OpenOptions, io::Write, path::Path, time::Instant};

use crate::historical_prefix_public::{PROFILE, PROFILE_N4, ROLES};

#[derive(Clone)]
struct Public {
    headers: u64,
    root: [u8; 32],
    total: [u8; 28],
    tip: [u8; 32],
    tip_time: i64,
}
impl Public {
    fn native(headers: u64) -> Result<Self, String> {
        let expected = crate::historical_prefix_public::expected(headers)?;
        Ok(Self {
            headers: expected.headers,
            root: expected.root,
            total: expected.total,
            tip: expected.tip,
            tip_time: expected.tip_time,
        })
    }
    fn profile(&self) -> Result<&'static [u8], String> {
        match self.headers {
            3 => Ok(PROFILE),
            4 => Ok(PROFILE_N4),
            _ => Err("common prefix requires N3 or N4".into()),
        }
    }

    fn bytes_with_geometry(&self, geometry: &Geometry) -> Result<Vec<u8>, String> {
        geometry.check_public(self)?;
        let mut bytes = self.profile()?.to_vec();
        bytes.extend(crate::header_order::MAINNET_GENESIS);
        bytes.extend([0u8; 32]); // Parent anchor of the fixed genesis.
        for n in [self.headers, geometry.slots as u64, geometry.slot_log as u64, geometry.common_input as u64] {
            bytes.extend(n.to_le_bytes());
        }
        bytes.extend(self.root);
        bytes.extend(self.total);
        bytes.extend(self.tip);
        bytes.extend(self.tip_time.to_le_bytes());
        for i in 0..7 {
            bytes.extend((i as u64).to_le_bytes());
            bytes.extend((ROLES[i].len() as u64).to_le_bytes());
            bytes.extend(ROLES[i]);
            bytes.extend((geometry.input_bits[i] as u64).to_le_bytes());
            bytes.extend((geometry.row_bits[i] as u64).to_le_bytes());
        }
        Ok(bytes)
    }

}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Geometry {
    headers: u64,
    slot_log: usize,
    slots: usize,
    common_input: usize,
    bank_bits: usize,
    input_bits: [usize; 7],
    row_bits: [usize; 7],
    height_row: usize,
    daa_row: usize,
    daa_row_base: usize,
    point_local_input: usize,
    point_local_row: usize,
}

impl Geometry {
    fn domain(bits: usize) -> Result<usize, String> {
        1usize.checked_shl(u32::try_from(bits).map_err(|_| "geometry shift overflow")?)
            .ok_or_else(|| "geometry shift overflow".into())
    }
    fn log(size: usize) -> Result<usize, String> {
        if !size.is_power_of_two() { return Err("geometry non-power-of-two domain".into()); }
        Ok(size.trailing_zeros() as usize)
    }
    fn core_bank_bits() -> Result<usize, String> {
        if layout::CORE == 0 || layout::WIDTH % layout::CORE != 0 {
            return Err("geometry core bank divisibility".into());
        }
        Self::log(layout::WIDTH / layout::CORE)
    }
    fn profile_terms(headers: u64) -> Result<usize, String> {
        match headers { 3 => Ok(329122), 4 => Ok(330050), _ => Err("geometry unsupported profile terms".into()) }
    }
    // This reads the same objects borrowed by the context; it never visits owners.
    fn read(consumer: &Consumer, height: &HeightWork<'_>, daa: &DaaHistoryRoster<'_>) -> Result<Self, String> {
        Self::read_layouts(consumer.layout_refs(), height, daa)
    }
    fn read_layouts(layouts: LayoutRefs<'_>, height: &HeightWork<'_>, daa: &DaaHistoryRoster<'_>) -> Result<Self, String> {
        let parent = layouts.parent;
        let h = parent.slot_log();
        let add = |n: usize| n.checked_add(h).ok_or("geometry width overflow");
        let header = parent.header_boundary().canonical_circuit();
        let (_, _, roster_row, roster_input) = work_tree_wiring::full_roster_shape(parent.topology())?;
        let point_local_input = Self::log(layouts.points.circuit.input_len)?;
        let point_local_row = Self::log(layouts.points.circuit.row_count)?;
        let daa_row = daa.row_log();
        Ok(Self {
            headers: parent.headers(), slot_log: h, slots: parent.slots(),
            common_input: parent.core_pool().input_log(),
            bank_bits: Self::core_bank_bits()?,
            input_bits: [parent.core_pool().input_log(), add(Self::log(header.input_len)?)?,
                roster_input, add(point_local_input)?, height.input_log(),
                layouts.adjacency.input_log(), layouts.metadata.input_log()],
            row_bits: [parent.core_pool().row_log(), add(Self::log(header.row_count)?)?,
                roster_row, add(point_local_row)?, daa_row.checked_add(1).ok_or("geometry width overflow")?,
                layouts.adjacency.row_log(), layouts.metadata.row_log()],
            height_row: height.row_log(), daa_row, daa_row_base: Self::domain(daa_row)?,
            point_local_input, point_local_row,
        })
    }
    fn derive(consumer: &Consumer, height: &HeightWork<'_>, daa: &DaaHistoryRoster<'_>) -> Result<Self, String> {
        let geometry = Self::read(consumer, height, daa)?;
        geometry.validate_layouts(consumer, height, daa)?;
        Ok(geometry)
    }
    fn check_public(&self, public: &Public) -> Result<(), String> {
        if public.headers != self.headers { return Err("geometry public headers mismatch".into()); }
        if self.slots != Self::domain(self.slot_log)? || self.headers < 3 || self.headers > self.slots as u64 {
            return Err("geometry public H/slots mismatch".into());
        }
        Ok(())
    }
    fn validate_layouts(&self, consumer: &Consumer, height: &HeightWork<'_>, daa: &DaaHistoryRoster<'_>) -> Result<(), String> {
        self.validate_refs(consumer.layout_refs(), height, daa)?;
        if consumer.public.headers != self.headers { return Err("geometry layout history mismatch".into()); }
        self.check_public(&consumer.public)
    }
    fn validate_refs(&self, layouts: LayoutRefs<'_>, height: &HeightWork<'_>, daa: &DaaHistoryRoster<'_>) -> Result<(), String> {
        let expected = Self::read_layouts(layouts, height, daa)?;
        if self.headers != expected.headers { return Err("geometry layout headers mismatch".into()); }
        if self.slot_log != expected.slot_log { return Err("geometry layout H mismatch".into()); }
        if self.slots != expected.slots || self.slots != Self::domain(self.slot_log)? {
            return Err("geometry layout slots mismatch".into());
        }
        if layouts.adjacency.n() != self.headers || layouts.metadata.n() != self.headers
            || daa.headers() != self.headers
            || layouts.parent.header_boundary().history_slots() != self.headers {
            return Err("geometry layout history mismatch".into());
        }
        if layouts.adjacency.slot_log() != self.slot_log || layouts.metadata.slot_log() != self.slot_log
            || daa.slot_log() != self.slot_log || height.slots() != self.slots
            || layouts.parent.header_boundary().slot_log() != self.slot_log {
            return Err("geometry layout owner mismatch".into());
        }
        if self.common_input != expected.common_input || daa.input_log() != self.common_input
            || height.input_log() != self.common_input || layouts.adjacency.input_log() != self.common_input
            || layouts.metadata.input_log() != self.common_input {
            return Err("geometry common input mismatch".into());
        }
        if self.bank_bits != expected.bank_bits { return Err("geometry core bank bits mismatch".into()); }
        if layouts.parent.core_pool().input_len() != Self::domain(self.common_input)?
            || layouts.parent.core_pool().row_count() != Self::domain(expected.row_bits[0])?
            || layouts.adjacency.input_len() != Self::domain(self.common_input)?
            || layouts.adjacency.row_count() != Self::domain(expected.row_bits[5])?
            || layouts.metadata.input_len() != Self::domain(self.common_input)?
            || layouts.metadata.row_count() != Self::domain(expected.row_bits[6])? {
            return Err("geometry concrete layout domain mismatch".into());
        }
        for role in 0..7 {
            if self.input_bits[role] != expected.input_bits[role] {
                return Err(format!("geometry role {role} input mismatch"));
            }
            if self.row_bits[role] != expected.row_bits[role] {
                return Err(format!("geometry role {role} row mismatch"));
            }
            Self::domain(self.input_bits[role])?; Self::domain(self.row_bits[role])?;
        }
        if self.height_row != expected.height_row { return Err("geometry height split mismatch".into()); }
        if self.daa_row != expected.daa_row { return Err("geometry DAA split mismatch".into()); }
        if self.height_row >= self.daa_row || self.row_bits[4] != self.daa_row.checked_add(1).ok_or("geometry width overflow")? {
            return Err("geometry composite split mismatch".into());
        }
        if self.daa_row_base != Self::domain(self.daa_row)? { return Err("geometry DAA base mismatch".into()); }
        if self.point_local_input != expected.point_local_input || self.point_local_row != expected.point_local_row {
            return Err("geometry point local mismatch".into());
        }
        Ok(())
    }
    fn proof_bytes(&self, role: usize) -> Result<usize, String> {
        self.input_bits.get(role).ok_or("geometry role index")?.checked_mul(7)
            .and_then(|n| n.checked_add(3)).and_then(|n| n.checked_mul(32))
            .ok_or_else(|| "geometry proof extent overflow".into())
    }
}

#[derive(Default)]
struct PreparationObservation { transcript_created: bool, challenges: u64, queries: u64 }

/// Borrowed canonical template; only the high-copy equality is analytic.
/// This does not admit a public history or weaken sparse's small-profile caps.
struct PointRole<'a> {
    base: &'a Circuit,
    math: crate::point_role::PointMath<'a>,
}
impl<'a> PointRole<'a> {
    fn dimensions(base: &'a Circuit, h: usize, input: usize, row: usize, common: usize)
        -> Result<Self, String> {
        let math = crate::point_role::PointMath::dimensions(base,h,input,row,common)?;
        Geometry::domain(input)?; Geometry::domain(row)?; Geometry::domain(common)?;
        Ok(Self { base, math })
    }
    fn new(consumer: &'a Consumer, geometry: &Geometry) -> Result<Self, String> {
        if geometry.point_local_input != 13 || geometry.point_local_row != 14 {
            return Err("point adapter local geometry".into());
        }
        Self::dimensions(&consumer.points.circuit, geometry.slot_log, geometry.input_bits[3],
            geometry.row_bits[3], geometry.common_input)
    }
    #[cfg(test)]
    fn toy_coefficients_for_test(base: &'a Circuit,h:usize)->Result<Self,String> {
        let math=crate::point_role::PointMath::legacy_toy_coefficients_fixture(base,h)?;
        Ok(Self {base,math})
    }
    fn coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], GkrError> {
        self.math.coefficients(r,u,v)
    }
    fn verify(&self, proof: &GkrProof, transcript: &mut Transcript) -> Result<InputClaim, GkrError> {
        self.math.verify_legacy(proof,transcript)
    }
    fn project(&self, point: &[Fr]) -> Result<Vec<Fr>, String> {
        self.math.project(point)
    }
}

#[path="point_role_legacy_tests.rs"]
mod point_role_legacy_tests;

#[derive(Clone)]
struct RoleProof {
    role: usize,
    bytes: Vec<u8>,
}
#[derive(Clone)]
struct Artifact {
    commitment: Vec<u8>,
    roles: Vec<RoleProof>,
    batch: Vec<u8>,
}

#[derive(Debug, PartialEq, Eq)]
enum Reject {
    Shape,
    Commitment,
    Role(usize),
    Linkage,
}

#[derive(Clone, Copy, Debug, Default)]
struct RoleObservation {
    canonical_decode: bool,
    prefix_challenges: u64,
    prefix_raw_queries: u64,
    prefix_bytes: u64,
    verifier_entered: bool,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RoleStage { Shape, Commitment, Decode, Prefix, Gkr, Projection }
#[derive(Debug)]
struct RoleFailure {
    role: usize,
    stage: RoleStage,
    observation: RoleObservation,
    message: String,
}
struct VerifiedRole {
    role: usize,
    claim: Claim,
    observation: RoleObservation,
    counters: [u64; 3],
    continuation: Fr,
}
// Closed test-only alternatives; normal verification still selects None.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Historical48PrefixFault { NoFault, ExtraRole0Binder }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Historical49PrefixFault { NoFault, ExtraRoleBinder }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Historical50PrefixFault { NoFault, ExtraRoleBinder }
enum RolePrefixControl<'a> {
    LegacyH2(&'a Public, common_tests::PrefixFault),
    Historical48(Historical48PrefixFault),
    Historical49(Historical49PrefixFault),
    Historical50(Historical50PrefixFault),
}
#[derive(Clone)]
struct VerifiedClaims { claims: [Claim; 7] }
#[derive(Debug)]
enum CommonFailure { Statement(Reject), Codec(String), Verification(String) }

// Internal reachability diagnostics are never an acceptance token. Only the
// atomic success result below contains verified observations.
#[derive(Default)]
pub(crate) struct Historical51Diagnostics{
    pub(crate) role_entries:[u8;7],pub(crate) role_completions:[u8;7],
    pub(crate) role_completion_order:[u8;7],pub(crate) roles_completed:u8,
    pub(crate) common_entries:u8,pub(crate) frontend_entries:u8,pub(crate) frontend_completions:u8,
    pub(crate) pcs_entries:u8,pub(crate) pcs_completions:u8,pub(crate) successes:u8,
}
impl Historical51Diagnostics{
    fn pristine(&self)->bool{self.role_entries==[0;7]&&self.role_completions==[0;7]&&self.common_entries==0
        &&self.role_completion_order==[0;7]&&self.roles_completed==0&&self.frontend_entries==0&&self.frontend_completions==0
        &&self.pcs_entries==0&&self.pcs_completions==0&&self.successes==0}
}
struct Historical51RoleObservations{counters:[[u64;3];7],continuations:[Fr;7],elapsed_ns:[u128;7]}
impl Default for Historical51RoleObservations{
    fn default()->Self{Self{counters:[[0;3];7],continuations:[Fr::zero();7],elapsed_ns:[0;7]}}
}
struct Historical51AtomicSuccess{
    claims:[Claim;7],roles:Option<Historical51RoleObservations>,common:Option<opening_batch::Common51Success>,
    roles_ns:u128,common_ns:u128,
}

// Private construction requests are not authenticated Public statements.
struct LayoutRequest {
    headers: u64, slot_log: usize, root: [u8; 32], total: [u8; 28],
    tip: [u8; 32], tip_time: i64,
}
impl LayoutRequest {
    fn preflight(&self) -> Result<(), String> { self.preflight_abi(usize::BITS as usize) }
    fn preflight_abi(&self, bits: usize) -> Result<(), String> {
        if bits != 64 { return Err("next36 requires 64-bit ABI".into()); }
        if self.headers < 3 { return Err("next36 header extent".into()); }
        let slots = self.headers.checked_next_power_of_two().ok_or("next36 header padding overflow")?;
        if self.headers > 1u64 << 21 { return Err("next36 header extent".into()); }
        let h = slots.trailing_zeros() as usize;
        if self.slot_log != h { return Err("next36 canonical owner dimension".into()); }
        for width in [20usize.checked_add(h), 14usize.checked_add(h), 21usize.checked_add(h)] {
            Geometry::domain(width.ok_or("next36 domain width overflow")?)?;
        }
        Ok(())
    }
}

std::thread_local! {
    // Direct observations of actual factory/census entry, isolated per test thread.
    static NEXT36_CONSTRUCTIONS: std::cell::Cell<[u64; 2]> = const { std::cell::Cell::new([0; 2]) };
    static NEXT36_CALLBACKS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}
fn next36_construction_event(index: usize) -> Result<(), String> {
    NEXT36_CONSTRUCTIONS.with(|counter| {
        let mut counts = counter.get();
        counts[index] = counts[index].checked_add(1).ok_or("next36 construction counter overflow")?;
        counter.set(counts); Ok(())
    })
}
fn next36_constructions() -> [u64; 2] { NEXT36_CONSTRUCTIONS.with(|counter| counter.get()) }
fn next36_callback_calls() -> u64 { NEXT36_CALLBACKS.with(|counter| counter.get()) }

struct OwnedLayouts {
    parent: WorkTreeHistoryPlan, adjacency: HeaderAdjacencyLayout,
    metadata: HeaderMetadataOrderLayout, points: point_membership::Compiled, point_template: String,
}
#[derive(Clone, Copy)]
struct LayoutRefs<'p> {
    parent: &'p WorkTreeHistoryPlan, adjacency: &'p HeaderAdjacencyLayout,
    metadata: &'p HeaderMetadataOrderLayout, points: &'p point_membership::Compiled, point_template: &'p String,
}
impl OwnedLayouts {
    fn layout_refs(&self) -> LayoutRefs<'_> {
        LayoutRefs { parent: &self.parent, adjacency: &self.adjacency, metadata: &self.metadata,
            points: &self.points, point_template: &self.point_template }
    }
}
fn compile_layouts(request: &LayoutRequest) -> Result<OwnedLayouts, String> {
    request.preflight()?;
    next36_construction_event(0)?;
    let parent = WorkTreeHistoryPlan::compile(request.headers, request.slot_log, request.root, request.total)?;
    let adjacency = HeaderAdjacencyLayout::compile(request.headers, request.slot_log, [0; 32], request.tip)?;
    let metadata = HeaderMetadataOrderLayout::compile(request.headers, request.slot_log, request.tip_time)?;
    let points = point_membership::build()?;
    if points.circuit.input_len != 8192 || points.circuit.row_count != 16384 || points.circuit.terms.len() != 288158 {
        return Err("point role geometry drift".into());
    }
    let point_template = layout::hash_terms(&points.circuit.terms);
    Ok(OwnedLayouts { parent, adjacency, metadata, points, point_template })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum HeightBinding { LegacyN3N4, HistoricalDiagnostic }
struct RelationParts<'p> {
    layouts: LayoutRefs<'p>, mode: HeightBinding, height: HeightWork<'p>, daa: DaaHistoryRoster<'p>,
    geometry: Geometry, point_role: PointRole<'p>, composite_terms: usize,
}
#[derive(Clone, Copy)]
struct RelationRefs<'r, 'p> {
    layouts: LayoutRefs<'p>, mode: HeightBinding, height: &'r HeightWork<'p>, daa: &'r DaaHistoryRoster<'p>,
    geometry: &'r Geometry, point_role: &'r PointRole<'p>, composite_terms: usize,
}
impl<'p> RelationParts<'p> {
    fn compile(layouts: LayoutRefs<'p>, mode: HeightBinding) -> Result<Self, String> {
        let height = match mode {
            HeightBinding::LegacyN3N4 => HeightWork::new(layouts.parent)?,
            HeightBinding::HistoricalDiagnostic => HeightWork::compile_history(layouts.parent)?,
        };
        let daa = DaaHistoryRoster::compile(layouts.parent)?;
        let geometry = Geometry::read_layouts(layouts, &height, &daa)?;
        geometry.validate_refs(layouts, &height, &daa)?;
        let point_role = PointRole::dimensions(&layouts.points.circuit, geometry.slot_log,
            geometry.input_bits[3], geometry.row_bits[3], geometry.common_input)?;
        let composite_terms = ProofContext::composite_census(layouts.parent, &height, &daa)?;
        Ok(Self { layouts, mode, height, daa, geometry, point_role, composite_terms })
    }
    fn refs(&self) -> RelationRefs<'_, 'p> {
        RelationRefs { layouts: self.layouts, mode: self.mode, height: &self.height, daa: &self.daa,
            geometry: &self.geometry, point_role: &self.point_role, composite_terms: self.composite_terms }
    }
}
fn role_coefficients(rel: RelationRefs<'_, '_>, role: usize, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
    if role >= 7 { return Err("next36 coefficient role".into()); }
    if r.len() != rel.geometry.row_bits[role] || u.len() != rel.geometry.input_bits[role]
        || v.len() != rel.geometry.input_bits[role] { return Err("next36 coefficient point dimensions".into()); }
    NEXT36_CALLBACKS.with(|counter| {
        counter.set(counter.get().checked_add(1).ok_or("next36 callback counter overflow")?);
        Ok::<(), String>(())
    })?;
    match role {
        0 => rel.layouts.parent.core_pool().coefficients(r, u, v).map_err(|e| e.to_string()),
        1 => rel.daa.header_coefficients(r, u, v),
        2 => work_tree_wiring::full_roster_coefficients(rel.layouts.parent.topology(), fixed::engine()?,
            rel.layouts.parent.fixed_profile(), rel.layouts.parent.leaf_boundary(), rel.layouts.parent.work_boundary(), r, u, v),
        3 => rel.point_role.coefficients(r, u, v).map_err(|e| e.to_string()),
        4 => crate::native_prefix_auth_plan::composite_coefficients(rel.height, rel.daa, r, u, v),
        5 => rel.layouts.adjacency.coefficients(r, u, v),
        6 => rel.layouts.metadata.coefficients(r, u, v),
        _ => unreachable!("checked role"),
    }
}

// Separate public-input-only H21 callback entry. This is not an admission of
// Historical51 packets, a producer, or the complete public S certificate.
use crate::packed_owner_assembly::h21_structural_roster::{H21StructuralRoster, PublicMapParameters};
pub(crate) struct H21StructuralDiagnostic {
    layouts: OwnedLayouts,
    parameters: [PublicMapParameters; 2],
    public_bytes: Vec<u8>,
}
pub(crate) struct H21StructuralDiagnosticContext<'a> {
    layouts: LayoutRefs<'a>,
    height: HeightWork<'a>,
    geometry: Geometry,
    point_role: PointRole<'a>,
    composite_terms: usize,
    roster: H21StructuralRoster<'a>,
    public_bytes: &'a [u8],
}
impl H21StructuralDiagnostic {
    pub(crate) fn compile(root: [u8;32], total: [u8;28], tip: [u8;32], tip_time: i64,
        parameters: [PublicMapParameters;2]) -> Result<Self,String> {
        let layouts = compile_layouts(&LayoutRequest { headers:1_827_840,slot_log:21,
            root,total,tip,tip_time })?;
        let descriptor = H21StructuralRoster::public_descriptor(&layouts.parent,parameters)?;
        let mut public_bytes = b"historical-prefix-h21-eligible08-structural-diagnostic-v1".to_vec();
        public_bytes.extend(crate::header_order::MAINNET_GENESIS);
        public_bytes.extend(root); public_bytes.extend(total); public_bytes.extend(tip);
        public_bytes.extend(tip_time.to_be_bytes());
        public_bytes.extend(descriptor);
        for (input,row) in [41usize,41,41,34,41,41,41].into_iter()
            .zip([42usize,40,41,35,41,30,33]) {
            public_bytes.extend((input as u64).to_be_bytes());
            public_bytes.extend((row as u64).to_be_bytes());
        }
        Ok(Self {layouts,parameters,public_bytes})
    }
    pub(crate) fn context(&self) -> Result<H21StructuralDiagnosticContext<'_>,String> {
        let layouts = self.layouts.layout_refs();
        let roster = H21StructuralRoster::from_public(layouts.parent,self.parameters)?;
        let height = HeightWork::compile_history(layouts.parent)?;
        let geometry = Geometry::read_layouts(layouts, &height, roster.daa())?;
        geometry.validate_refs(layouts, &height, roster.daa())?;
        if geometry.input_bits != [41,41,41,34,41,41,41]
            || geometry.row_bits != [42,40,41,35,41,30,33]
            || geometry.common_input != 41 {
            return Err("H21 structural seven-role geometry".into());
        }
        let point_role = PointRole::dimensions(&layouts.points.circuit, geometry.slot_log,
            geometry.input_bits[3], geometry.row_bits[3], geometry.common_input)?;
        let composite_terms = ProofContext::composite_census(layouts.parent, &height, roster.daa())?;
        Ok(H21StructuralDiagnosticContext {layouts,height,geometry,point_role,composite_terms,
            roster,public_bytes:&self.public_bytes})
    }
}
impl<'a> H21StructuralDiagnosticContext<'a> {
    fn refs(&self) -> RelationRefs<'_, 'a> {
        RelationRefs { layouts:self.layouts, mode:HeightBinding::HistoricalDiagnostic,
            height:&self.height, daa:self.roster.daa(), geometry:&self.geometry,
            point_role:&self.point_role, composite_terms:self.composite_terms }
    }
    pub(crate) fn coefficients(&self,role:usize,r:&[Fr],u:&[Fr],v:&[Fr]) -> Result<[Fr;4],String> {
        if role==1 { self.roster.coefficients(r,u,v) }
        else { role_coefficients(self.refs(),role,r,u,v) }
    }
    pub(crate) fn bind_role(&self,role:usize,t:&mut Transcript) -> Result<(),String> {
        if role>=7 || t.challenges()!=0 || t.raw_queries()!=0 {
            return Err("H21 structural role/binder freshness".into());
        }
        t.append_bytes(b"H21-structural-public-statement",self.public_bytes);
        t.append_u64(b"H21-structural-role",role as u64);
        self.roster.bind(t);
        Ok(())
    }
    pub(crate) fn visit_role1_owner(&self,owner:usize,
        mut sink:impl FnMut(Term)->Result<(),String>) -> Result<(),String> {
        self.roster.visit_owner_terms(owner,|_,term|sink(term))?; Ok(())
    }
}

#[test]
fn c586_h21_distinct_callback_closes_upper_alias_missing_from_old_role1() {
    use crate::legacy_envelope_map::{LowerSelector,LowerSource,LowerBranch};
    let parameters=crate::bank53_map::CutDescriptor::eligible08().terminals()
        .map(|terminal|PublicMapParameters {terminal,exponent:55,
            lower:LowerSelector {source:LowerSource::HeaderDifficulty {height:841_729},
                branch:LowerBranch::Pivot(54)}});
    let owned=H21StructuralDiagnostic::compile([0x31;32],[0x42;28],[0x52;32],1,parameters).unwrap();
    let context=owned.context().unwrap();
    let bits=|value:usize,n| (0..n).map(|bit|Fr::from(((value>>bit)&1)as u64)).collect::<Vec<_>>();
    let r=bits(1_810_841*(1<<19)+506_925+17,40);
    let u=bits(1_810_840*(1<<20)+987_450+17,41);let v=bits(0,41);
    assert_eq!(role_coefficients(context.refs(),1,&r,&u,&v).unwrap(),[Fr::zero();4]);
    assert_eq!(context.coefficients(1,&r,&u,&v).unwrap(),
        [Fr::zero(),-Fr::one(),Fr::zero(),Fr::zero()]);
    let mut transcript=Transcript::new(b"c586-H21-callback");
    context.bind_role(1,&mut transcript).unwrap();
    assert_eq!((transcript.challenges(),transcript.raw_queries()),(0,0));
    assert!(context.bind_role(7,&mut transcript).is_err());
    assert!(context.coefficients(1,&r[..39],&u,&v).is_err());
}

/// Constructed from bounded candidate fields and code-owned layouts.
/// No private witness or producer-supplied claims enter the consumer.
struct Consumer {
    public: Public,
    parent: WorkTreeHistoryPlan,
    adjacency: HeaderAdjacencyLayout,
    metadata: HeaderMetadataOrderLayout,
    points: point_membership::Compiled,
    point_template: String,
}
impl Consumer {
    fn new(public: &Public) -> Result<Self, String> {
        public.profile()?;
        let OwnedLayouts { parent, adjacency, metadata, points, point_template } = compile_layouts(&LayoutRequest {
            headers: public.headers, slot_log: 2, root: public.root, total: public.total, tip: public.tip, tip_time: public.tip_time,
        })?;
        Ok(Self {
            public: public.clone(),
            parent,
            adjacency,
            metadata,
            points,
            point_template,
        })
    }
    fn layout_refs(&self) -> LayoutRefs<'_> {
        LayoutRefs { parent: &self.parent, adjacency: &self.adjacency, metadata: &self.metadata,
            points: &self.points, point_template: &self.point_template }
    }
}

/// Both relations borrow the same consumer-owned history. Their construction
/// and binding precede challenges and occur once per top-level operation.
struct ProofContext<'a> {
    consumer: &'a Consumer,
    height: HeightWork<'a>,
    daa: DaaHistoryRoster<'a>,
    geometry: Geometry,
    point_role: PointRole<'a>,
    height_binding: HeightBinding,
    composite_terms: usize,
    public_bytes: Vec<u8>,
    corpus_id: [u8; 32],
    base: Transcript,
}
impl<'a> ProofContext<'a> {
    fn new(consumer: &'a Consumer) -> Result<Self, String> {
        let parts = RelationParts::compile(consumer.layout_refs(), HeightBinding::LegacyN3N4)?;
        let (mut base, public_bytes, corpus_id, composite_terms) = Self::prepare_prefix(
            consumer, parts.refs(), &mut PreparationObservation::default())?;
        Self::bind_composite_parts(&parts.geometry, composite_terms, &parts.height, &parts.daa, &mut base);
        let RelationParts { height, daa, geometry, point_role, mode: height_binding, .. } = parts;
        Ok(Self {
            consumer,
            height,
            daa,
            geometry, point_role, height_binding, composite_terms, public_bytes, corpus_id, base,
        })
    }
    fn relation_refs(&self) -> RelationRefs<'_, 'a> {
        RelationRefs { layouts: self.consumer.layout_refs(), mode: self.height_binding,
            height: &self.height, daa: &self.daa, geometry: &self.geometry,
            point_role: &self.point_role, composite_terms: self.composite_terms }
    }

    // Verifier-owned, sealed TESTONLY entry; never inferred from received mode bits.
    fn historical_tiny(consumer: &'a Consumer, serialized: &[u8]) -> Result<Self, String> {
        let decoded = crate::historical_prefix_public::decode_tiny_candidate(serialized)?;
        if decoded.headers != consumer.public.headers || decoded.root != consumer.public.root
            || decoded.total != consumer.public.total || decoded.tip != consumer.public.tip
            || decoded.tip_time != consumer.public.tip_time { return Err("generic37 candidate identity".into()); }
        let parts = RelationParts::compile(consumer.layout_refs(), HeightBinding::HistoricalDiagnostic)?;
        if consumer.public.bytes_with_geometry(&parts.geometry)? != serialized {
            return Err("generic37 canonical public frame".into());
        }
        let (mut base, public_bytes, corpus_id, composite_terms) = Self::prepare_prefix_mode(
            consumer, parts.refs(), HeightBinding::HistoricalDiagnostic, &mut PreparationObservation::default())?;
        Self::bind_composite_parts(&parts.geometry, composite_terms, &parts.height, &parts.daa, &mut base);
        let RelationParts { height, daa, geometry, point_role, mode: height_binding, .. } = parts;
        Ok(Self { consumer, height, daa, geometry, point_role, height_binding, composite_terms,
            public_bytes, corpus_id, base })
    }

    fn prepare_prefix(consumer: &Consumer, parts: RelationRefs<'_, '_>, observation: &mut PreparationObservation)
        -> Result<(Transcript, Vec<u8>, [u8; 32], usize), String> {
        Self::prepare_prefix_mode(consumer, parts, HeightBinding::LegacyN3N4, observation)
    }

    fn prepare_prefix_mode(consumer: &Consumer, parts: RelationRefs<'_, '_>, required: HeightBinding,
        observation: &mut PreparationObservation) -> Result<(Transcript, Vec<u8>, [u8; 32], usize), String> {
        let original = consumer.layout_refs();
        if !std::ptr::eq(parts.layouts.parent, original.parent) { return Err("next36 parent layout identity".into()); }
        if !std::ptr::eq(parts.layouts.adjacency, original.adjacency) { return Err("next36 adjacency layout identity".into()); }
        if !std::ptr::eq(parts.layouts.metadata, original.metadata) { return Err("next36 metadata layout identity".into()); }
        if !std::ptr::eq(parts.layouts.points, original.points) { return Err("next36 points layout identity".into()); }
        if !std::ptr::eq(parts.layouts.point_template, original.point_template) { return Err("next36 fingerprint owner identity".into()); }
        let (height, daa, geometry) = (parts.height, parts.daa, parts.geometry);
        if !std::ptr::eq(height.endpoint_parent(), original.parent) { return Err("composite height parent identity".into()); }
        if !std::ptr::eq(daa.endpoint_parent(), original.parent) { return Err("composite DAA parent identity".into()); }
        if !std::ptr::eq(parts.point_role.base, &original.points.circuit) { return Err("next36 point base identity".into()); }
        geometry.validate_layouts(consumer, height, daa)?;
        let golden = Geometry::profile_terms(geometry.headers)?;
        consumer.public.profile()?;
        if parts.mode != required { return Err("next36 legacy binding mode".into()); }
        let composite_terms = Self::admit_census(golden, parts.composite_terms)?;
        let public_bytes = consumer.public.bytes_with_geometry(geometry)?;
        let corpus_id = Blake2b::<U32>::digest(&public_bytes).into();
        let mut base = Transcript::new(consumer.public.profile()?);
        observation.transcript_created = true;
        base.append_bytes(b"public-statement-and-roster", &public_bytes);
        consumer.parent.bind(&mut base);
        consumer.adjacency.bind(&mut base);
        consumer.metadata.bind(&mut base);
        base.append_bytes(b"point-template", consumer.point_template.as_bytes());
        observation.challenges = base.challenges(); observation.queries = base.raw_queries();
        Ok((base, public_bytes, corpus_id, composite_terms))
    }

    fn composite_census(parent: &WorkTreeHistoryPlan, height: &HeightWork<'_>, daa: &DaaHistoryRoster<'_>)
        -> Result<usize, String> {
        if !std::ptr::eq(height.endpoint_parent(), parent) { return Err("composite height parent identity".into()); }
        if !std::ptr::eq(daa.endpoint_parent(), parent) { return Err("composite DAA parent identity".into()); }
        if daa.headers() != parent.headers() || daa.slot_log() != parent.slot_log()
            || height.slots() != parent.slots() || height.input_log() != daa.input_log()
            || height.input_log() != parent.core_pool().input_log() {
            return Err("composite census layout geometry".into());
        }
        next36_construction_event(1)?;
        let mut unit = 0usize;
        let genesis = height.visit_owner_terms(0, |_| {
            unit = unit.checked_add(1).ok_or("composite height unit overflow")?; Ok(())
        })?;
        if genesis.height != unit || genesis.numeric != 0 { return Err("composite height genesis unit".into()); }
        let lanes = daa.term_census()?.lanes;
        Self::census_total(parent.headers(), unit, lanes)
    }
    fn census_total(headers: u64, unit: usize, lanes: [usize; 4]) -> Result<usize, String> {
        let n = usize::try_from(headers).map_err(|_| "composite census header width")?;
        let height = unit.checked_mul(n).and_then(|n| n.checked_add(lanes[2]))
            .ok_or("composite census height overflow")?;
        let total = lanes.into_iter().try_fold(height, |a, n| a.checked_add(n).ok_or("composite census total overflow"))?;
        u64::try_from(total).map_err(|_| "composite census transcript width")?;
        Ok(total)
    }
    fn admit_census(golden: usize, observed: usize) -> Result<usize, String> {
        if observed != golden { return Err("composite census differs from admitted profile".into()); }
        Ok(observed)
    }

    fn bind_composite(&self, t: &mut Transcript) {
        Self::bind_composite_parts(&self.geometry, self.composite_terms, &self.height, &self.daa, t);
    }
    fn bind_composite_parts(g: &Geometry, terms: usize, height: &HeightWork<'_>, daa: &DaaHistoryRoster<'_>, t: &mut Transcript) {
        t.append_bytes(
            b"height-daa-composition",
            b"complete-height-and-four-daa-lanes-v2",
        );
        for dimension in [
            g.slot_log as u64,
            g.headers,
            height.input_log() as u64,
            daa.input_log() as u64,
            g.height_row as u64,
            g.daa_row as u64,
            0,
            1,
            (g.daa_row - g.height_row) as u64,
        ] {
            t.append_u64(b"height-daa-fixed-dimension", dimension);
        }
        t.append_u64(b"height-daa-row-base", g.daa_row_base as u64);
        t.append_u64(b"height-daa-total-terms", terms as u64);
        height.bind(t);
        daa.bind(t);
    }

    fn term_count(&self) -> usize {
        self.composite_terms
    }

    fn composite_coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
        crate::native_prefix_auth_plan::composite_coefficients(&self.height, &self.daa, r, u, v)
    }

    fn composite_circuit(&self) -> Result<Circuit, String> {
        let height = self.height.circuit()?;
        if height.input_len != Geometry::domain(self.geometry.common_input)?
            || height.row_count != Geometry::domain(self.geometry.height_row)? {
            return Err("common height geometry drift".into());
        }
        let mut terms = Vec::with_capacity(self.term_count());
        terms.extend(height.terms);
        let numeric = if self.consumer.parent.headers() == 3 {
            [0usize, 225, 448, 0]
        } else {
            [0usize, 225, 448, 448]
        };
        for (owner, expected_numeric) in numeric.into_iter().enumerate() {
            let counts = self.daa.visit_owner_terms(owner as u64, |mut term| {
                term.row = term
                    .row
                    .checked_add(self.geometry.daa_row_base)
                    .ok_or("common DAA row overflow")?;
                if term.row >= Geometry::domain(self.geometry.row_bits[4])?
                    || term.gate.left >= Geometry::domain(self.geometry.common_input)?
                    || term.gate.right >= Geometry::domain(self.geometry.common_input)? {
                    return Err("common DAA term escapes fixed domain".into());
                }
                terms.push(term);
                Ok(())
            })?;
            if counts.lanes != [0, 0, expected_numeric, 81920] {
                return Err("common DAA fixed owner census drift".into());
            }
        }
        if terms.len() != self.term_count() {
            return Err("common height/DAA complete term count drift".into());
        }
        Ok(Circuit {
            input_len: Geometry::domain(self.geometry.common_input)?,
            row_count: Geometry::domain(self.geometry.row_bits[4])?,
            terms,
        })
    }

    fn tiny_historical_composite(&self) -> Result<Circuit, String> {
        let g = &self.geometry;
        if self.height_binding != HeightBinding::HistoricalDiagnostic || !matches!(g.headers, 3 | 4)
            || (g.slot_log, g.slots, g.common_input, g.height_row, g.daa_row, g.row_bits[4]) != (2,4,22,8,21,22)
            || self.term_count() >= 1 << 20 { return Err("generic37 collector admission".into()); }
        let mut height = Vec::with_capacity(128);
        let mut numeric = Vec::with_capacity(1344);
        for owner in 0..g.slots {
            self.height.visit_owner_terms(owner as u64, |term| {
                let target = if term.row < 32 * g.slots { &mut height } else { &mut numeric };
                let limit = if term.row < 32 * g.slots { 128 } else { 1344 };
                if target.len() >= limit || term.row >= 1 << g.height_row
                    || term.gate.left >= 1 << g.common_input || term.gate.right >= 1 << g.common_input {
                    return Err("generic37 height collector bound".into());
                }
                target.push(term); Ok(())
            })?;
        }
        let mut terms = Vec::with_capacity(self.term_count());
        terms.extend(height); terms.extend(numeric);
        for owner in 0..g.slots {
            self.daa.visit_owner_terms(owner as u64, |mut term| {
                term.row = term.row.checked_add(g.daa_row_base).ok_or("generic37 collector row overflow")?;
                if terms.len() >= self.term_count() || term.row >= 1 << g.row_bits[4]
                    || term.gate.left >= 1 << g.common_input || term.gate.right >= 1 << g.common_input {
                    return Err("generic37 DAA collector bound".into());
                }
                terms.push(term); Ok(())
            })?;
        }
        if terms.len() != self.term_count() { return Err("generic37 collector census".into()); }
        let circuit = Circuit { input_len: 1 << g.common_input, row_count: 1 << g.row_bits[4], terms };
        sparse::validate(&circuit, 0).map_err(|e| e.to_string())?;
        Ok(circuit)
    }

    fn transcript(
        &self,
        role: usize,
        key: &verifier_key::AdmittedVerifierKey,
        commitment: &[u8],
    ) -> Transcript {
        let mut t = self.base.clone();
        t.append_bytes(b"setup-id", key.id());
        t.append_bytes(b"commitment", commitment);
        t.append_u64(b"role-index", role as u64);
        t.append_bytes(b"role-domain", ROLES[role]);
        t
    }

    fn bind_role(&self, role: usize, t: &mut Transcript) {
        match role {
            0 => self.consumer.parent.core_pool().bind(t),
            1 => self.daa.bind(t),
            2 => work_tree_wiring::bind_full_roster(
                self.consumer.parent.topology(),
                self.consumer.parent.fixed_profile(),
                self.consumer.parent.leaf_profile(),
                self.consumer.parent.work_profile(),
                t,
            ),
            // The point prover/verifier add sparse::bind themselves.
            3 => unreachable!("point binding is owned by sparse"),
            4 => self.bind_composite(t),
            5 => self.consumer.adjacency.bind(t),
            6 => self.consumer.metadata.bind(t),
            _ => unreachable!("fixed roster"),
        }
    }

    fn coefficients(&self, role: usize, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
        role_coefficients(self.relation_refs(), role, r, u, v)
    }

    fn small_circuit(&self, role: usize) -> Result<Circuit, String> {
        if role == 2 {
            return work_tree_wiring::full_roster_circuit(
                self.consumer.parent.topology(),
                fixed::engine()?,
                self.consumer.parent.fixed_profile(),
                self.consumer.parent.leaf_boundary(),
                self.consumer.parent.work_boundary(),
            );
        }
        if role == 4 {
            return self.composite_circuit();
        }
        if role != 5 && role != 6 {
            return Err("not a materialized role".into());
        }
        let mut terms = Vec::new();
        for owner in 0..self.consumer.parent.headers() {
            let mut sink = |row, gate| {
                terms.push(Term { row, gate });
                Ok(())
            };
            if role == 5 {
                self.consumer.adjacency.visit_slot_terms(owner, &mut sink)?;
            } else {
                self.consumer.metadata.visit_slot_terms(owner, &mut sink)?;
            }
        }
        let n = self.consumer.parent.headers() as usize;
        let expected = if role == 5 {
            (n + 1) * 256
        } else {
            n * 2337 + 256
        };
        if terms.len() != expected {
            return Err("small role term count drift".into());
        }
        Ok(Circuit {
            input_len: Geometry::domain(self.geometry.input_bits[role])?,
            row_count: Geometry::domain(self.geometry.row_bits[role])?,
            terms,
        })
    }

    fn verify_role4(
        &self,
        proof: &GkrProof,
        transcript: &mut Transcript,
    ) -> Result<InputClaim, GkrError> {
        gkr::verify_with_wiring(
            &[self.geometry.input_bits[4]],
            1 << self.geometry.row_bits[4],
            proof,
            transcript,
            |t| self.bind_role(4, t),
            |_, r, u, v| {
                self.coefficients(4, r, u, v)
                    .map_err(|_| GkrError::InvalidWireIndex)
            },
        )
    }

    fn verify_role(
        &self, packet: &RoleProof, key: &verifier_key::AdmittedVerifierKey, commitment: &[u8],
    ) -> Result<VerifiedRole, RoleFailure> {
        self.verify_role_inner(packet, key, commitment, None)
    }

    // Only the closed child-test enum can select a different fresh prefix.
    // No caller-supplied or advanced Transcript is accepted by this seam.
    fn verify_role_control(
        &self, packet: &RoleProof, key: &verifier_key::AdmittedVerifierKey, commitment: &[u8],
        public: &Public, fault: common_tests::PrefixFault,
    ) -> Result<VerifiedRole, RoleFailure> {
        self.verify_role_inner(packet, key, commitment, Some(RolePrefixControl::LegacyH2(public, fault)))
    }

    fn historical48_control_prefix(
        &self, role: usize, key: &verifier_key::AdmittedVerifierKey, commitment: &[u8],
        fault: Historical48PrefixFault,
    ) -> Result<Transcript, String> {
        historical47_geometry(&self.geometry)?;
        if role != 0 || key.log_n() != 32 || self.height_binding != HeightBinding::HistoricalDiagnostic
            || self.public_bytes != historical47_frame(&self.consumer.public)? {
            return Err("historical48 closed prefix control".into());
        }
        // NoFault is the exact normal prefix, not a second H12 serializer.
        let mut t = self.transcript(role, key, commitment);
        if fault == Historical48PrefixFault::ExtraRole0Binder { self.bind_role(0, &mut t); }
        if t.challenges() != 0 || t.raw_queries() != 0 {
            return Err("historical48 prefix control advanced".into());
        }
        Ok(t)
    }

    fn verify_role_historical48_control(
        &self, packet: &RoleProof, key: &verifier_key::AdmittedVerifierKey, commitment: &[u8],
        fault: Historical48PrefixFault,
    ) -> Result<VerifiedRole, RoleFailure> {
        self.verify_role_inner(packet, key, commitment, Some(RolePrefixControl::Historical48(fault)))
    }

    fn verify_role_inner(
        &self, packet: &RoleProof, key: &verifier_key::AdmittedVerifierKey, commitment: &[u8],
        control: Option<RolePrefixControl<'_>>,
    ) -> Result<VerifiedRole, RoleFailure> {
        let role = packet.role;
        let mut observation = RoleObservation::default();
        let failure = |stage, message: String, observation| RoleFailure { role, stage, observation, message };
        if role >= 7 || key.log_n() != self.geometry.common_input
            || self.geometry.proof_bytes(role).map_or(true, |n| packet.bytes.len() != n) {
            return Err(failure(RoleStage::Shape, "role/key/packet geometry".into(), observation));
        }
        let decoded_c = pcs::decode_commitment(commitment)
            .map_err(|e| failure(RoleStage::Commitment, e, observation))?;
        if pcs::encode_commitment(&decoded_c)
            .map_err(|e| failure(RoleStage::Commitment, e, observation))? != commitment {
            return Err(failure(RoleStage::Commitment, "noncanonical commitment".into(), observation));
        }
        let proof = gkr::decode_dimensions(&[self.geometry.input_bits[role]], &packet.bytes)
            .map_err(|e| failure(RoleStage::Decode, e, observation))?;
        if gkr::encode_proof(&proof).map_err(|e| failure(RoleStage::Decode, e, observation))? != packet.bytes {
            return Err(failure(RoleStage::Decode, "noncanonical GKR".into(), observation));
        }
        observation.canonical_decode = true;
        let mut t = match control {
            None => self.transcript(role, key, commitment),
            Some(RolePrefixControl::LegacyH2(public, fault)) => common_tests::fresh_prefix(self, public, role, key, commitment, fault)
                .map_err(|e| failure(RoleStage::Prefix, e, observation))?,
            Some(RolePrefixControl::Historical48(fault)) => self.historical48_control_prefix(role, key, commitment, fault)
                .map_err(|e| failure(RoleStage::Prefix, e, observation))?,
            Some(RolePrefixControl::Historical49(fault)) => self.historical49_control_prefix(role, key, commitment, fault)
                .map_err(|e| failure(RoleStage::Prefix, e, observation))?,
            Some(RolePrefixControl::Historical50(fault)) => self.historical50_control_prefix(role, key, commitment, fault)
                .map_err(|e| failure(RoleStage::Prefix, e, observation))?,
        };
        observation.prefix_challenges = t.challenges();
        observation.prefix_raw_queries = t.raw_queries();
        observation.prefix_bytes = t.bytes_absorbed();
        if observation.prefix_challenges != 0 || observation.prefix_raw_queries != 0 {
            return Err(failure(RoleStage::Prefix, "prefix is not fresh".into(), observation));
        }
        observation.verifier_entered = true;
        let terminal = if role == 3 {
            self.point_role.verify(&proof, &mut t)
        } else if role == 4 {
            self.verify_role4(&proof, &mut t)
        } else {
            gkr::verify_with_wiring(&[self.geometry.input_bits[role]], 1 << self.geometry.row_bits[role], &proof, &mut t,
                |t| self.bind_role(role, t),
                |_, r, u, v| self.coefficients(role, r, u, v).map_err(|_| GkrError::InvalidWireIndex))
        }.map_err(|e| failure(RoleStage::Gkr, e.to_string(), observation))?;
        let point = if role == 3 {
            self.point_role.project(&terminal.point)
                .map_err(|e| failure(RoleStage::Projection, e, observation))?
        } else { terminal.point };
        if point.len() != self.geometry.common_input {
            return Err(failure(RoleStage::Projection, "projected point dimension".into(), observation));
        }
        let counters = [t.challenges(), t.raw_queries(), t.bytes_absorbed()];
        let continuation = t.clone().try_challenge_scalar(b"candidate-binding-role-continuation-v1")
            .map_err(|e| failure(RoleStage::Projection, e, observation))?;
        Ok(VerifiedRole { role, claim: Claim { point, value: terminal.value }, observation, counters, continuation })
    }

    fn verified_roles(
        &self,
        artifact: &Artifact,
        key: &verifier_key::AdmittedVerifierKey,
    ) -> Result<VerifiedClaims, Reject> {
        self.verified_roles_core51(artifact,key,None,None)
    }

    fn verified_roles_core51(&self,artifact:&Artifact,key:&verifier_key::AdmittedVerifierKey,
        mut diagnostic:Option<&mut Historical51Diagnostics>,mut observations:Option<&mut Historical51RoleObservations>)
        ->Result<VerifiedClaims,Reject>{
        if key.log_n() != self.geometry.common_input
            || artifact.roles.len() != 7
            || artifact
                .roles
                .iter()
                .enumerate()
                .any(|(i, p)| p.role != i || self.geometry.proof_bytes(i).map_or(true, |n| p.bytes.len() != n))
        {
            return Err(Reject::Shape);
        }
        pcs::decode_commitment(&artifact.commitment).map_err(|_| Reject::Commitment)?;
        let mut claims = Vec::with_capacity(7);
        for (role, packet) in artifact.roles.iter().enumerate() {
            if let Some(d)=diagnostic.as_deref_mut(){d.role_entries[role]+=1;}
            let started=observations.as_ref().map(|_|Instant::now());
            let verified = self.verify_role(packet, key, &artifact.commitment).map_err(|_| Reject::Role(role))?;
            if verified.role != role { return Err(Reject::Shape); }
            if let Some(o)=observations.as_deref_mut(){o.counters[role]=verified.counters;o.continuations[role]=verified.continuation;
                o.elapsed_ns[role]=started.ok_or(Reject::Shape)?.elapsed().as_nanos();}
            if let Some(d)=diagnostic.as_deref_mut(){d.role_completions[role]+=1;
                d.role_completion_order[d.roles_completed as usize]=role as u8;d.roles_completed+=1;}
            claims.push(verified.claim);
        }
        Ok(VerifiedClaims { claims: claims.try_into().map_err(|_| Reject::Shape)? })
    }

    fn verify_roles(&self, artifact: &Artifact, key: &verifier_key::AdmittedVerifierKey)
        -> Result<[Claim; 7], Reject> {
        Ok(self.verified_roles(artifact, key)?.claims)
    }

    fn verify_common(&self, artifact: &Artifact, key: &verifier_key::AdmittedVerifierKey,
        verified: &VerifiedClaims) -> Result<(), CommonFailure> {
        self.verify_common_core51(artifact,key,verified,None,false).map(|_|())
    }

    fn verify_common_core51(&self,artifact:&Artifact,key:&verifier_key::AdmittedVerifierKey,verified:&VerifiedClaims,
        mut diagnostic:Option<&mut Historical51Diagnostics>,observed:bool)->Result<Option<opening_batch::Common51Success>,CommonFailure>{
        if let Some(d)=diagnostic.as_deref_mut(){d.common_entries+=1;}
        let statement = self.statement(artifact, key, verified.claims.clone())
            .map_err(CommonFailure::Statement)?;
        let proof = opening_batch::decode_proof(&artifact.batch, self.geometry.common_input).map_err(CommonFailure::Codec)?;
        if opening_batch::encode_proof(&proof, self.geometry.common_input).map_err(CommonFailure::Codec)? != artifact.batch {
            return Err(CommonFailure::Codec("noncanonical common proof".into()));
        }
        if observed{
            let mut reached=|event|{if let Some(d)=diagnostic.as_deref_mut(){match event{
                opening_batch::Common51Event::FrontendEntered=>d.frontend_entries+=1,
                opening_batch::Common51Event::FrontendComplete=>d.frontend_completions+=1,
                opening_batch::Common51Event::PcsEntered=>d.pcs_entries+=1,
                opening_batch::Common51Event::PcsComplete=>d.pcs_completions+=1,
            }}};
            let success=opening_batch::verify_admitted_observed51(&statement,key,&proof,&mut reached)
                .map_err(CommonFailure::Verification)?;
            Ok(Some(success))
        }else{
            opening_batch::verify_admitted(&statement,key,&proof).map_err(CommonFailure::Verification)?;
            Ok(None)
        }
    }

    fn verify(
        &self,
        artifact: &Artifact,
        key: &verifier_key::AdmittedVerifierKey,
    ) -> Result<[Claim; 7], Reject> {
        Ok(self.verify_atomic_core51(artifact,key,None,false)?.claims)
    }

    fn verify_atomic_core51(&self,artifact:&Artifact,key:&verifier_key::AdmittedVerifierKey,
        mut diagnostic:Option<&mut Historical51Diagnostics>,observed:bool)->Result<Historical51AtomicSuccess,Reject>{
        if diagnostic.as_ref().map_or(false,|d|!d.pristine()){return Err(Reject::Shape);}
        let mut roles=if observed{Some(Historical51RoleObservations::default())}else{None};
        let started=observed.then(Instant::now);
        let verified=self.verified_roles_core51(artifact,key,diagnostic.as_deref_mut(),roles.as_mut())?;
        let roles_ns=started.map_or(0,|t|t.elapsed().as_nanos());let started=observed.then(Instant::now);
        let common=self.verify_common_core51(artifact,key,&verified,diagnostic.as_deref_mut(),observed)
            .map_err(|_|Reject::Linkage)?;
        let common_ns=started.map_or(0,|t|t.elapsed().as_nanos());
        if let Some(d)=diagnostic.as_deref_mut(){d.successes+=1;}
        Ok(Historical51AtomicSuccess{claims:verified.claims,roles,common,roles_ns,common_ns})
    }
}

impl ProofContext<'_> {
    fn statement(
        &self,
        artifact: &Artifact,
        key: &verifier_key::AdmittedVerifierKey,
        claims: [Claim; 7],
    ) -> Result<opening_batch::Statement, Reject> {
        Ok(opening_batch::Statement {
            log_n: self.geometry.common_input,
            setup_id: *key.id(),
            commitment: pcs::decode_commitment(&artifact.commitment)
                .map_err(|_| Reject::Commitment)?,
            corpus_id: Some(self.corpus_id),
            claims,
        })
    }

}

impl Consumer {
    fn verify(
        &self,
        artifact: &Artifact,
        key: &verifier_key::AdmittedVerifierKey,
    ) -> Result<[Claim; 7], Reject> {
        ProofContext::new(self)
            .map_err(|_| Reject::Shape)?
            .verify(artifact, key)
    }
}

fn read_slot(source: &PackedFile, owner: usize, geometry: &Geometry) -> Result<Vec<Fr>, String> {
    if owner >= geometry.slots || source.input_len() != Geometry::domain(geometry.common_input)? {
        return Err("prefix packed dimensions".into());
    }
    let mut values = Vec::with_capacity(layout::WIDTH);
    let banks = Geometry::domain(geometry.bank_bits)?;
    for bank in 0..banks {
        values.extend(source.read_copy(layout::CORE, owner * banks + bank)?);
    }
    Ok(values)
}
fn read_all(source: &PackedFile, geometry: &Geometry) -> Result<Vec<Fr>, String> {
    let mut values = Vec::with_capacity(Geometry::domain(geometry.common_input)?);
    for owner in 0..geometry.slots {
        values.extend(read_slot(source, owner, geometry)?);
    }
    Ok(values)
}
fn write_new(path: &Path, bytes: &[u8]) -> Result<(), String> {
    OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .and_then(|mut f| {
            f.write_all(bytes)?;
            f.sync_all()
        })
        .map_err(|e| e.to_string())
}

fn historical_role1_header_census(
    class: OwnerClass,
    counts: HeaderCounts,
    observed: usize,
) -> Result<(), String> {
    let (emitted, omitted_mature_a4, omitted_short_a4) = match class {
        OwnerClass::Short(_) => (388_369, 0, 8_192),
        OwnerClass::Mature(_) => (388_369, 8_192, 0),
        _ => (396_561, 0, 0),
    };
    let total = counts
        .emitted
        .checked_add(counts.omitted_mature_a4)
        .and_then(|total| total.checked_add(counts.omitted_short_a4))
        .and_then(|total| total.checked_add(counts.omitted_worktree))
        .ok_or("retained header total overflow")?;
    if counts.emitted != emitted
        || observed != emitted
        || counts.omitted_mature_a4 != omitted_mature_a4
        || counts.omitted_short_a4 != omitted_short_a4
        || counts.omitted_worktree != 78_194
        || total != 474_755
    {
        return Err("retained header count drift".into());
    }
    Ok(())
}

#[cfg(test)]
mod role1_census_tests {
    use super::*;

    fn counts(emitted: usize, omitted_mature_a4: usize, omitted_short_a4: usize) -> HeaderCounts {
        HeaderCounts {
            emitted,
            omitted_worktree: 78_194,
            omitted_mature_a4,
            omitted_short_a4,
        }
    }

    #[test]
    fn admits_short_and_mature_a4_omissions() {
        for class in [
            OwnerClass::Genesis,
            OwnerClass::Initial,
            OwnerClass::Carry,
            OwnerClass::FixedV2,
            OwnerClass::Singleton,
            OwnerClass::M1,
            OwnerClass::Padding,
        ] {
            assert!(
                historical_role1_header_census(class, counts(396_561, 0, 0), 396_561).is_ok(),
                "full-count owner class {class:?}"
            );
        }
        assert!(historical_role1_header_census(
            OwnerClass::Short(crate::short_daa_layout::Profile::M2),
            counts(388_369, 0, 8_192),
            388_369,
        )
        .is_ok());
        assert!(historical_role1_header_census(
            OwnerClass::Mature(crate::daa_integer::Epoch::Eip),
            counts(388_369, 8_192, 0),
            388_369,
        )
        .is_ok());
    }

    #[test]
    fn rejects_class_mismatch_and_both_a4_omissions() {
        assert!(historical_role1_header_census(
            OwnerClass::Mature(crate::daa_integer::Epoch::Eip),
            counts(388_369, 0, 8_192),
            388_369,
        )
        .is_err());
        assert!(historical_role1_header_census(
            OwnerClass::Short(crate::short_daa_layout::Profile::M2),
            counts(388_369, 8_192, 8_192),
            388_369,
        )
        .is_err());
    }

    #[test]
    fn rejects_emitted_observed_and_total_drift() {
        let full = OwnerClass::Carry;
        assert!(historical_role1_header_census(full, counts(396_560, 0, 0), 396_560).is_err());
        assert!(historical_role1_header_census(full, counts(396_561, 0, 0), 396_560).is_err());
        let mut wrong_total = counts(396_561, 0, 0);
        wrong_total.omitted_worktree -= 1;
        assert!(historical_role1_header_census(full, wrong_total, 396_561).is_err());
    }
}

// Atomic TESTONLY consumer: no witness, setup object, expected public/C or naked claims.
fn verify_historical_tiny_bytes(statement: &[u8], artifact: &Artifact) -> Result<[Claim; 7], String> {
    let decoded = crate::historical_prefix_public::decode_tiny_candidate(statement)?;
    if artifact.commitment.len() != 384 || artifact.roles.len() != 7 || artifact.batch.len() != 31581 {
        return Err("generic37 package extent".into());
    }
    for (role, packet) in artifact.roles.iter().enumerate() {
        if packet.role != role || packet.bytes.len() != if role == 3 {3456} else {5024} {
            return Err("generic37 package role extent".into());
        }
    }
    let key = verifier_key::admit(22, include_bytes!("../fixtures/verifier-keys-v1/log22.vk"))?;
    let c = pcs::decode_commitment(&artifact.commitment)?;
    if pcs::encode_commitment(&c)? != artifact.commitment { return Err("generic37 noncanonical C".into()); }
    let public = Public { headers: decoded.headers, root: decoded.root, total: decoded.total,
        tip: decoded.tip, tip_time: decoded.tip_time };
    let consumer = Consumer::new(&public)?;
    let context = ProofContext::historical_tiny(&consumer, statement)?;
    context.verify(artifact, &key).map_err(|e| format!("generic37 atomic verification: {e:?}"))
}
fn packed_source(path: &Path, bytes: &[u8]) -> Result<PackedFile, String> {
    // This legacy fixture is deliberately limited to log22; contexts validate it.
    let mut writer = PackedFileWriter::create_new(path, 22)?;
    writer.write_bytes(bytes)?;
    writer.finish()
}
fn phase(name: &str, start: Instant) {
    println!(
        "{}",
        serde_json::json!({"phase":name,"seconds":start.elapsed().as_secs_f64()})
    );
    std::io::stdout().flush().unwrap();
}

fn prove_role(
    context: &ProofContext<'_>,
    source: &PackedFile,
    key: &verifier_key::AdmittedVerifierKey,
    commitment: &[u8],
    role: usize,
) -> Result<(GkrProof, InputClaim), String> {
    let geometry = &context.geometry;
    if source.input_len() != Geometry::domain(geometry.common_input)? || key.log_n() != geometry.common_input {
        return Err("producer/context geometry mismatch".into());
    }
    let mut t = context.transcript(role, key, commitment);
    match role {
        0 => core_pool_boolean::prove_with_copy_bits_for_test(
            &fixed::engine()?.core,
            geometry.bank_bits,
            &layout::CORE_OFFSETS
                .iter()
                .map(|offset| offset / layout::CORE)
                .collect::<Vec<_>>(),
            geometry.slot_log,
            |owner| read_slot(source, owner, geometry),
            &mut t,
            |t| context.bind_role(0, t),
            |r, u, v| context.coefficients(0, r, u, v),
        ),
        1 => sparse_stream_roster::prove(
            geometry.common_input - geometry.slot_log,
            geometry.slot_log,
            geometry.row_bits[1] - geometry.slot_log,
            0,
            &[geometry.row_bits[1] - geometry.slot_log],
            |owner| read_slot(source, owner, geometry),
            &mut t,
            |t| context.bind_role(1, t),
            |owner, sink| {
                let class = context.daa.owner_class(owner as u64)?;
                let mut observed = 0usize;
                let counts = context.daa.visit_header_terms(owner as u64, |mut term| {
                    let ib = owner * layout::WIDTH;
                    let local_rows = Geometry::domain(geometry.row_bits[1] - geometry.slot_log)?;
                    let rb = owner * local_rows;
                    if !(ib..ib + layout::WIDTH).contains(&term.gate.left)
                        || !(ib..ib + layout::WIDTH).contains(&term.gate.right)
                        || !(rb..rb + local_rows).contains(&term.row)
                    {
                        return Err("retained header escapes owner".into());
                    }
                    term.row -= rb;
                    term.gate.left -= ib;
                    term.gate.right -= ib;
                    sink(term)?;
                    observed = observed.checked_add(1).ok_or("retained header observed count overflow")?;
                    Ok(())
                })?;
                historical_role1_header_census(class, counts, observed)?;
                Ok(())
            },
            |r, u, v| context.coefficients(1, r, u, v),
        ),
        3 => sparse_stream_boolean::prove(
            &context.consumer.points.circuit,
            geometry.slot_log,
            |owner| {
                segment_points::load_copy(source, 3, geometry.slots, owner)
                    .map_err(|_| GkrError::InvalidInputWidth)
            },
            &mut t,
        )
        .map_err(|e| format!("{e:?}")),
        2 | 4 | 5 | 6 => {
            let circuit = context.small_circuit(role)?;
            let input = read_all(source, geometry)?;
            sparse::prove_with_binding(&circuit, &input, 0, &mut t, |t| context.bind_role(role, t))
                .map_err(|e| e.to_string())
        }
        _ => Err("unknown fixed role".into()),
    }
}

// Endpoint emission needs the generic visitor, while the existing role keeps
// its legacy transcript binding through context.height.
fn role4_complete_s2_endpoint_height<'a>(
    context: &ProofContext<'a>,
) -> Result<HeightWork<'a>, String> {
    HeightWork::compile_history(&context.consumer.parent)
}

fn prove_role4_complete_s2_streaming(
    context: &ProofContext<'_>,
    source: &PackedFile,
    cache_limit_bytes: usize,
    transcript: &mut Transcript,
) -> Result<(GkrProof, InputClaim, bool, bool), String> {
    use crate::native_prefix_auth_plan::{Role4EndpointAdapter, Role4EndpointScope};
    if context.consumer.parent.headers() != 3
        || context.consumer.parent.slot_log() != 2
        || context.height.slots() != 4
        || context.height.input_log() != 22
        || context.daa.slot_log() != 2
        || context.daa.input_log() != 22
        || context.daa.row_log() != 21
        || source.input_len() != 1 << 22
    {
        return Err("role4 streaming requires native N3 CompleteS2 geometry".into());
    }
    let endpoint_height = role4_complete_s2_endpoint_height(context)?;
    let adapter = Role4EndpointAdapter::new(
        &endpoint_height,
        &context.daa,
        Role4EndpointScope::CompleteS2,
    )?;
    let binding = adapter.binding();
    sparse_stream_roster::prove_edge_terms_with_cache_limit_for_test(
        20,
        2,
        19,
        1,
        &[19, 19],
        cache_limit_bytes,
        |left, owner, sink| {
            adapter.visit_endpoint(&binding, left, owner, sink)?;
            Ok(())
        },
        |owner| read_slot(source, owner, &context.geometry),
        transcript,
        |t| context.bind_role(4, t),
        |r, u, v| adapter.coefficients(r, u, v),
    )
}

#[derive(Default)]
struct HistoryStreamMetrics {
    endpoint_calls: u64, callbacks: u64, left_terms: u64, right_terms: u64,
    load_calls: u64, loaded_fields: u64, load_decode_ns: u64, loader_capacity_peak: usize,
    io: packed::PackedIoSnapshot,
}

fn prove_role4_historical_streaming(
    context: &ProofContext<'_>, source: &PackedFile, transcript: &mut Transcript,
) -> Result<(GkrProof, InputClaim, bool, bool, HistoryStreamMetrics), String> {
    let g = &context.geometry;
    if context.height_binding != HeightBinding::HistoricalDiagnostic || !matches!(g.headers, 3 | 4)
        || (g.slot_log, g.slots, g.common_input, g.height_row, g.daa_row, g.row_bits[4]) != (2,4,22,8,21,22)
        || source.input_len() != 1usize << 22 {
        return Err("history streaming tiny admission".into());
    }
    let adapter = crate::native_prefix_auth_plan::HistoricalRole4Endpoints::new(&context.height, &context.daa)?;
    use std::cell::Cell;
    let calls = Cell::new(0u64); let callbacks = Cell::new(0u64);
    let sides = [Cell::new(0u64), Cell::new(0u64)];
    let loads = Cell::new(0u64); let fields = Cell::new(0u64);
    let load_ns = Cell::new(0u64); let capacity = Cell::new(0usize);
    let add = |cell: &Cell<u64>, value: u64| -> Result<(), String> {
        cell.set(cell.get().checked_add(value).ok_or("history streaming counter overflow")?); Ok(())
    };
    source.reset_io_metrics();
    let (proof, claim, u, v) = sparse_stream_roster::prove_edge_terms_with_cache_limit_for_test(
        20, g.slot_log, 19, 1, &[19,19], 0,
        |left, owner, sink| {
            add(&calls, 1)?; let before = callbacks.get();
            let counts = adapter.visit(left, owner, |edge| {
                sink(edge)?; add(&callbacks, 1)?; add(&sides[usize::from(!left)], 1)
            })?;
            if counts.total()? as u64 != callbacks.get() - before { return Err("history endpoint reported count".into()); }
            Ok(())
        },
        |owner| {
            let began = Instant::now(); let values = read_slot(source, owner, g)?;
            if values.len() != layout::WIDTH || values.capacity() != layout::WIDTH {
                return Err("history streaming loader width or capacity".into());
            }
            add(&loads, 1)?; add(&fields, values.len() as u64)?;
            add(&load_ns, u64::try_from(began.elapsed().as_nanos()).map_err(|_| "history loader clock")?)?;
            capacity.set(capacity.get().max(values.capacity() * std::mem::size_of::<Fr>()));
            Ok(values)
        }, transcript,
        |t| context.bind_role(4, t), |r,u,v| adapter.coefficients(r,u,v),
    )?;
    Ok((proof, claim, u, v, HistoryStreamMetrics {
        endpoint_calls: calls.get(), callbacks: callbacks.get(), left_terms: sides[0].get(), right_terms: sides[1].get(),
        load_calls: loads.get(), loaded_fields: fields.get(), load_decode_ns: load_ns.get(),
        loader_capacity_peak: capacity.get(), io: source.io_metrics_snapshot(),
    }))
}

// Private historical-only producer seam. Legacy dispatch and its materialized
// reference stay unchanged; no packet can select this path or its geometry.
struct History39Shape { family_bits: usize, strides: Vec<usize>, terms: u64 }

fn history39_admit(context: &ProofContext<'_>, role: usize, source_len: usize,
    chunk_bits: usize, retained: usize) -> Result<History39Shape, String> {
    if role >= 7 { return Err("stream39 role".into()); }
    if context.height_binding != HeightBinding::HistoricalDiagnostic { return Err("stream39 historical mode".into()); }
    let g = &context.geometry;
    if !matches!(g.headers, 3 | 4) || (g.slot_log,g.slots,g.common_input) != (2,4,22)
        || g.input_bits != [22,22,22,15,22,22,22] || g.row_bits != [23,21,21,16,22,11,14] {
        return Err("stream39 tiny geometry".into());
    }
    if source_len != 1usize << 22 { return Err("stream39 source extent".into()); }
    if chunk_bits != 16 { return Err("stream39 chunk width".into()); }
    if retained > crate::segment_adjacency::linear_for_test::LIMIT { return Err("stream39 retained extent".into()); }
    g.validate_layouts(context.consumer, &context.height, &context.daa)?;
    if !std::ptr::eq(context.height.endpoint_parent(), &context.consumer.parent)
        || !std::ptr::eq(context.daa.endpoint_parent(), &context.consumer.parent) {
        return Err("stream39 parent identity".into());
    }
    let parent = &context.consumer.parent;
    let mut shape = History39Shape { family_bits: 0, strides: Vec::new(), terms: 0 };
    match role {
        2 => {
            let topology = parent.topology();
            let (local,bits,rows,input) = work_tree_wiring::full_roster_shape(topology)?;
            if (local,rows,input) != (14+g.slot_log,g.row_bits[2],g.input_bits[2]) {
                return Err("stream39 role2 geometry".into());
            }
            shape.family_bits=bits;
            shape.strides=Vec::with_capacity(topology.families.len()+6);
            let mut add=|terms:u64|->Result<(),String>{
                shape.terms=shape.terms.checked_add(terms).ok_or("stream39 term overflow")?;Ok(())
            };
            for family in &topology.families {
                let count=family.count(&topology.descriptor)?;
                shape.strides.push(count.row_log.checked_sub(g.slot_log).ok_or("stream39 member stride")?);add(count.terms)?;
            }
            shape.strides.extend([11,14,11]);
            add(crate::work_tree_fixed_hash::count(fixed::engine()?,parent.fixed_profile())?.total_boundary_terms)?;
            add(crate::work_tree_leaf_hash::count(fixed::engine()?,parent.leaf_boundary())?["new_boundary_terms"]
                .as_u64().ok_or("stream39 leaf count")?)?;
            add(crate::work_tree_work::count(parent.work_boundary())?["new_local_terms"]
                .as_u64().ok_or("stream39 work count")?)?;
            for family in parent.work_boundary().links() {
                let count=family.count(&topology.descriptor)?;
                shape.strides.push(count.row_log.checked_sub(g.slot_log).ok_or("stream39 link stride")?);add(count.terms)?;
            }
            if shape.strides.len()!=topology.families.len()+6 || shape.strides.len()>64
                || shape.strides.iter().any(|stride|*stride>14) { return Err("stream39 role2 strides".into()); }
        }
        5 => {
            let descriptor=context.consumer.adjacency.linear_descriptor_for_test()?;
            descriptor.validate(source_len,chunk_bits)?;
            crate::segment_adjacency::linear_for_test::preflight_for_test(&descriptor,retained)?;
            shape.terms=(g.headers+1)*256;
        }
        6 => { context.consumer.metadata.role6_endpoint_shape_for_test()?;
            shape.strides.push(12);shape.terms=2337*g.headers+256; }
        4 => { shape.strides.extend([19,19]);shape.family_bits=1;shape.terms=context.term_count() as u64; }
        _ => (),
    }
    Ok(shape)
}

fn history39_vector(values: Vec<Fr>, width: usize) -> Result<Vec<Fr>, String> {
    if values.len()!=width { return Err("stream39 loader length".into()); }
    if values.capacity()>width { return Err("stream39 loader capacity".into()); }
    Ok(values)
}

fn history39_visit(context: &ProofContext<'_>, role: usize, shape: &History39Shape,
    left: bool, owner: usize, sink: &mut dyn FnMut(sparse_stream_roster::EdgeTerm)->Result<(),String>) -> Result<(),String> {
    let g=&context.geometry;
    if owner>=g.slots { return Err("stream39 endpoint owner".into()); }
    match role {
        2 => { let p=&context.consumer.parent;
            work_tree_wiring::visit_full_roster_endpoint(p.topology(),fixed::engine()?,p.fixed_profile(),
                p.leaf_boundary(),p.work_boundary(),left,owner,&mut |edge| {
                    work_tree_wiring::check_role2_endpoint_edge(&edge,left,owner,g.slot_log,&shape.strides)?;
                    sink(edge)
                })
        }
        6 => context.consumer.metadata.visit_endpoint_for_test(left,owner,
            &mut crate::header_metadata_order_layout::Role6EndpointStats::default(), &mut |edge| {
                if sparse_stream_roster::global_edge_row(edge.source_slot,edge.family_row,g.slot_log,12,0,&[12])?!=edge.term.row
                    || (if left {edge.term.gate.left} else {edge.term.gate.right})/layout::WIDTH!=owner {
                    return Err("stream39 role6 exact endpoint".into());
                }
                sink(edge)
            }),
        _ => Err("stream39 endpoint role".into()),
    }
}

struct History39Produced {
    proof: GkrProof, claim: InputClaim, sender: Option<([u64;3],Fr)>,
    edge: Option<HistoryStreamMetrics>, linear: Option<crate::segment_adjacency::linear_for_test::Stats>,
    io: packed::PackedIoSnapshot, elapsed_ns: u64,
    load_calls: u64, loaded_fields: u64, load_decode_ns: u64, loader_capacity_peak: usize, terms: u64,
}

fn history39_transaction<T>(transcript: &mut Transcript,
    operation: impl FnOnce(&mut Transcript)->Result<T,String>) -> Result<T,String> {
    let mut working=transcript.clone();let value=operation(&mut working)?;*transcript=working;Ok(value)
}

fn prove_historical_stream39(context: &ProofContext<'_>, source: &PackedFile,
    key: &verifier_key::AdmittedVerifierKey, commitment: &[u8], role: usize, retained: usize) -> Result<History39Produced,String> {
    let shape=history39_admit(context,role,source.input_len(),16,retained)?;
    if key.log_n()!=22 || pcs::encode_commitment(&pcs::decode_commitment(commitment)?)?!=commitment {
        return Err("stream39 key or commitment".into());
    }
    use std::cell::Cell;
    let calls=Cell::new(0u64);let callbacks=Cell::new(0u64);
    let sides=[Cell::new(0u64),Cell::new(0u64)];
    let loads=Cell::new(0u64);let fields=Cell::new(0u64);let load_ns=Cell::new(0u64);let capacity=Cell::new(0usize);
    let add=|cell:&Cell<u64>,n:u64|->Result<(),String>{cell.set(cell.get().checked_add(n).ok_or("stream39 counter overflow")?);Ok(())};
    let mut t=context.transcript(role,key,commitment);
    let mut edge=None;let mut linear=None;
    source.reset_io_metrics();let started=Instant::now();
    let (proof,claim,sender)=match role {
        0 | 1 | 3 => { let (proof,claim)=prove_role(context,source,key,commitment,role)?;(proof,claim,None) }
        4 => {
            let (proof,claim,u,v,metrics)=prove_role4_historical_streaming(context,source,&mut t)?;
            if u||v {return Err("stream39 role4 replay branch".into());}edge=Some(metrics);
            let counters=[t.challenges(),t.raw_queries(),t.bytes_absorbed()];
            let continuation=t.clone().try_challenge_scalar(b"candidate-binding-role-continuation-v1")?;
            (proof,claim,Some((counters,continuation)))
        }
        5 => {
            let descriptor=context.consumer.adjacency.linear_descriptor_for_test()?;
            // The raw complete-scan entry mutates its transcript. Keep its
            // working copy private until its own closure returns successfully.
            let (proof,claim,stats)=history39_transaction(&mut t,|working|
                crate::segment_adjacency::linear_for_test::prove(&descriptor,source.input_len(),retained,|chunk| {
                    let began=Instant::now();let values=history39_vector(source.read_copy(65536,chunk)?,65536)?;
                    add(&loads,1)?;add(&fields,values.len() as u64)?;
                    add(&load_ns,u64::try_from(began.elapsed().as_nanos()).map_err(|_|"stream39 loader clock")?)?;
                    capacity.set(capacity.get().max(values.capacity()*32));Ok(values)
                },working).and_then(|(proof,claim,stats)| {
                    if stats.read_calls!=[64,1088,1088,64] || loads.get()!=2304 || fields.get()!=150994944 {
                        return Err("stream39 linear census".into());
                    }
                    if claim.point.len()!=22 || gkr::encode_proof(&proof)?.len()!=5024 {
                        return Err("stream39 linear result shape".into());
                    }
                    Ok((proof,claim,stats))
                }))?;
            linear=Some(stats);let counters=[t.challenges(),t.raw_queries(),t.bytes_absorbed()];
            let continuation=t.clone().try_challenge_scalar(b"candidate-binding-role-continuation-v1")?;
            (proof,claim,Some((counters,continuation)))
        }
        2 | 6 => {
            let base=if role==2 {14}else{12};
            let (proof,claim,u,v)=sparse_stream_roster::prove_edge_terms_with_cache_limit_for_test(
                20,context.geometry.slot_log,base,shape.family_bits,&shape.strides,0,
                |left,owner,sink| {add(&calls,1)?;history39_visit(context,role,&shape,left,owner,&mut |term| {
                    sink(term)?;add(&callbacks,1)?;add(&sides[usize::from(!left)],1)
                })},
                |owner| {let began=Instant::now();let values=history39_vector(read_slot(source,owner,&context.geometry)?,layout::WIDTH)?;
                    add(&loads,1)?;add(&fields,values.len() as u64)?;
                    add(&load_ns,u64::try_from(began.elapsed().as_nanos()).map_err(|_|"stream39 loader clock")?)?;
                    capacity.set(capacity.get().max(values.capacity()*32));Ok(values)},
                &mut t,|t|context.bind_role(role,t),|r,u,v|context.coefficients(role,r,u,v))?;
            if u||v {return Err("stream39 replay branch".into());}
            if callbacks.get()!=44*shape.terms || sides[0].get()!=22*shape.terms || sides[1].get()!=22*shape.terms
                || calls.get()!=176 || loads.get()!=4 || fields.get()!=4194304 {return Err("stream39 edge census".into());}
            edge=Some(HistoryStreamMetrics {endpoint_calls:calls.get(),callbacks:callbacks.get(),left_terms:sides[0].get(),
                right_terms:sides[1].get(),load_calls:loads.get(),loaded_fields:fields.get(),load_decode_ns:load_ns.get(),
                loader_capacity_peak:capacity.get(),io:source.io_metrics_snapshot()});
            let counters=[t.challenges(),t.raw_queries(),t.bytes_absorbed()];
            let continuation=t.clone().try_challenge_scalar(b"candidate-binding-role-continuation-v1")?;
            (proof,claim,Some((counters,continuation)))
        }
        _ => return Err("stream39 role".into()),
    };
    let elapsed_ns=u64::try_from(started.elapsed().as_nanos()).map_err(|_|"stream39 producer clock")?;
    Ok(History39Produced {proof,claim,sender,edge,linear,io:source.io_metrics_snapshot(),elapsed_ns,
        load_calls:loads.get(),loaded_fields:fields.get(),load_decode_ns:load_ns.get(),loader_capacity_peak:capacity.get(),terms:shape.terms})
}

fn run_common(headers: u64) -> Result<(), String> {
    let dir =
        std::env::var_os("NIPOPOW_COMMON_PREFIX_DIR").ok_or("missing fresh artifact directory")?;
    let dir = Path::new(&dir);
    let started = Instant::now();
    let public = Public::native(headers)?;
    let w = witness::build(&witness::retained_headers_n(headers as usize)?)?;
    if w.root != public.root
        || w.total != public.total
        || w.tip != public.tip
        || w.tip_time != public.tip_time
    {
        return Err("native expected public differs from field-witness producer".into());
    }
    let mut bits = vec![0u8; (1 << 22) / 8];
    for (i, value) in w.values.iter().enumerate() {
        if value.is_one() {
            bits[i / 8] |= 1 << (i % 8);
        } else if !value.is_zero() {
            return Err("non-Boolean prefix witness".into());
        }
    }
    drop(w);
    let source = packed_source(&dir.join("witness.bits"), &bits)?;
    phase("witness", started);
    let started = Instant::now();
    let consumer = Consumer::new(&public)?;
    let context = ProofContext::new(&consumer)?;
    write_new(&dir.join("statement.bin"), &context.public_bytes)?;
    phase("layouts", started);
    let started = Instant::now();
    let setup = pcs::generate_setup(context.geometry.common_input)?;
    let key = verifier_key::admit(context.geometry.common_input, include_bytes!("../fixtures/verifier-keys-v1/log22.vk"))?;
    if setup.id != *key.id() {
        return Err("setup differs from admitted key".into());
    }
    phase("setup", started);
    let started = Instant::now();
    let committed = packed::commit(&source, &setup)?;
    let commitment = pcs::encode_commitment(&committed.commitment)?;
    write_new(&dir.join("commitment.bin"), &commitment)?;
    phase("commitment", started);
    let mut artifact = Artifact {
        commitment,
        roles: Vec::new(),
        batch: Vec::new(),
    };
    let mut producer_claims = Vec::new();
    for role in 0..7 {
        let started = Instant::now();
        let (proof, terminal) = prove_role(&context, &source, &key, &artifact.commitment, role)?;
        phase(&format!("gkr-{role}"), started);
        let started = Instant::now();
        let bytes = gkr::encode_proof(&proof)?;
        if bytes.len() != context.geometry.proof_bytes(role)? {
            return Err("GKR codec length drift".into());
        }
        write_new(&dir.join(format!("role-{role}.gkr")), &bytes)?;
        phase(&format!("encode-{role}"), started);
        let point = if role == 3 {
            let embedded = segment_points::embed(3, context.geometry.slot_log, &terminal.point)?;
            let mut local = Vec::with_capacity(Geometry::domain(context.geometry.input_bits[3])?);
            for owner in 0..context.geometry.slots {
                local.extend(segment_points::load_copy(&source, 3, context.geometry.slots, owner)?);
            }
            if gkr::mle(&local, &terminal.point).map_err(|e| e.to_string())? != terminal.value
                || source.evaluate(&embedded)? != terminal.value
            {
                return Err("point claim embedding differs from source".into());
            }
            let mut wrong = embedded.clone();
            wrong[18] = Fr::zero(); // bank 96 -> bank 64.
            if source.evaluate(&wrong)? == terminal.value {
                return Err("wrong bank mutant not isolated".into());
            }
            embedded
        } else {
            terminal.point
        };
        producer_claims.push(Claim {
            point,
            value: terminal.value,
        });
        artifact.roles.push(RoleProof { role, bytes });
    }
    if artifact.roles.iter().map(|p| p.bytes.len()).sum::<usize>() != 33600 {
        return Err("fixed total GKR bytes drift".into());
    }
    let started = Instant::now();
    let derived = context
        .verify_roles(&artifact, &key)
        .map_err(|e| format!("role verify {e:?}"))?;
    let producer_claims: [Claim; 7] = producer_claims.try_into().map_err(|_| "producer roster")?;
    if derived != producer_claims {
        return Err("producer/consumer claims differ".into());
    }
    phase("verify-roles", started);
    let statement = context
        .statement(&artifact, &key, derived.clone())
        .map_err(|e| format!("{e:?}"))?;
    let started = Instant::now();
    let (batch, _, _) = opening_batch::prove(&source, &committed, &setup, &statement)?;
    phase("batch-prove", started);
    let started = Instant::now();
    artifact.batch = opening_batch::encode_proof(&batch, context.geometry.common_input)?;
    write_new(&dir.join("openings.bin"), &artifact.batch)?;
    phase("batch-encode", started);
    let started = Instant::now();
    let accepted = context
        .verify(&artifact, &key)
        .map_err(|e| format!("common verify {e:?}"))?;
    if accepted != derived {
        return Err("common consumer changed claims".into());
    }
    phase("common-verify", started);

    let started = Instant::now();
    let mut mutant = artifact.clone();
    mutant.roles.remove(6);
    assert_eq!(context.verify(&mutant, &key), Err(Reject::Shape));
    let mut mutant = artifact.clone();
    mutant.roles[1] = mutant.roles[0].clone();
    assert_eq!(context.verify(&mutant, &key), Err(Reject::Shape));
    let mut mutant = artifact.clone();
    mutant.roles.swap(0, 1);
    assert_eq!(context.verify(&mutant, &key), Err(Reject::Shape));
    let mut mutant = artifact.clone();
    mutant.roles.push(artifact.roles[4].clone());
    assert_eq!(context.verify(&mutant, &key), Err(Reject::Shape));
    let mut mutant = artifact.clone();
    mutant.roles[4].bytes = artifact.roles[1].bytes.clone();
    assert_eq!(context.verify(&mutant, &key), Err(Reject::Role(4)));
    let mut mutant = artifact.clone();
    mutant.roles[1].bytes = artifact.roles[4].bytes.clone();
    mutant.roles[4].bytes = artifact.roles[1].bytes.clone();
    assert_eq!(context.verify(&mutant, &key), Err(Reject::Role(1)));
    let mut mutant = artifact.clone();
    mutant.roles[3].bytes.push(0);
    assert_eq!(context.verify(&mutant, &key), Err(Reject::Shape));
    for invalid in [2, 5] {
        let mut altered = public.clone();
        altered.headers = invalid;
        assert!(altered.bytes_with_geometry(&context.geometry).is_err());
        assert!(Consumer::new(&altered).is_err());
    }
    phase("roster-and-statement-negatives", started);

    let started = Instant::now();
    bits[0] ^= 1;
    let foreign_source = packed_source(&dir.join("foreign-witness.bits"), &bits)?;
    let foreign = packed::commit(&foreign_source, &setup)?;
    let mut mutant = artifact.clone();
    mutant.commitment = pcs::encode_commitment(&foreign.commitment)?;
    assert_ne!(mutant.commitment, artifact.commitment);
    pcs::decode_commitment(&mutant.commitment)?;
    assert_eq!(context.verify(&mutant, &key), Err(Reject::Role(0)));
    phase("foreign-valid-commitment-negative", started);

    let started = Instant::now();
    let mut reordered = statement.clone();
    reordered.claims.swap(0, 1);
    assert_ne!(reordered.claims, statement.claims);
    let (wrong_batch, _, _) = opening_batch::prove(&source, &committed, &setup, &reordered)?;
    opening_batch::verify_admitted(&reordered, &key, &wrong_batch)?;
    let mut mutant = artifact.clone();
    mutant.batch = opening_batch::encode_proof(&wrong_batch, context.geometry.common_input)?;
    write_new(&dir.join("reordered-valid-openings.bin"), &mutant.batch)?;
    assert_eq!(context.verify(&mutant, &key), Err(Reject::Linkage));
    phase("genuine-reordered-batch-negative", started);
    drop(context); drop(consumer);
    // Altered-public layout construction never overlaps the original context.
    let mut altered = public.clone();
    altered.tip_time ^= 1;
    { let changed = Consumer::new(&altered)?;
      assert_eq!(changed.verify(&artifact, &key), Err(Reject::Role(0))); }
    if headers == 4 {
        let mut altered = public.clone(); altered.headers = 3;
        let changed = Consumer::new(&altered)?;
        assert_eq!(changed.verify(&artifact, &key), Err(Reject::Role(0)));
    }
    println!(
        "{}",
        serde_json::json!({"result":"PASS","headers":headers,"owners":4,"roles":7,
        "gkr_bytes":33600,"opening_bytes":artifact.batch.len(),"commitment_bytes":artifact.commitment.len(),
        "raw_hidden":false,"full_history":false,"production":false})
    );
    Ok(())
}

#[test]
#[ignore = "requires a fresh artifact directory and bounded proof runner"]
fn n3_all_roles_share_one_admitted_commitment_and_reject_substitution() {
    std::thread::Builder::new()
        .name("historical-prefix-common".into())
        .stack_size(32 * 1024 * 1024)
        .spawn(|| run_common(3).unwrap())
        .unwrap()
        .join()
        .unwrap();
}

#[test]
#[ignore = "requires a fresh artifact directory and bounded proof runner"]
fn n4_all_roles_share_one_admitted_commitment_and_reject_substitution() {
    std::thread::Builder::new()
        .name("historical-prefix-common-n4".into())
        .stack_size(32 * 1024 * 1024)
        .spawn(|| run_common(4).unwrap())
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn point_claim_embedding_uses_bank96_and_both_owner_coordinates() {
    // Independent Boolean index oracle, including owner3 and wrong-bank/owner mutations.
    for owner in 0..4 {
        for wire in [0usize, 1, 8061, 8191] {
            let local: Vec<Fr> = (0..13)
                .map(|i| Fr::from(((wire >> i) & 1) as u64))
                .chain((0..2).map(|i| Fr::from(((owner >> i) & 1) as u64)))
                .collect();
            let embedded = segment_points::embed(3, 2, &local).unwrap();
            let expected = owner * layout::WIDTH + 786432 + wire;
            let actual = embedded.iter().enumerate().fold(0usize, |n, (i, x)| {
                assert!(x.is_zero() || x.is_one());
                n | ((x.is_one() as usize) << i)
            });
            assert_eq!(actual, expected);
            let mut wrong_bank = embedded.clone();
            wrong_bank[18] = Fr::zero();
            assert_ne!(wrong_bank, embedded);
            let mut wrong_owner = embedded.clone();
            wrong_owner[20] = Fr::one() - wrong_owner[20];
            assert_ne!(wrong_owner, embedded);
        }
    }
    assert!(segment_points::embed(3, 2, &vec![Fr::zero(); 14]).is_err());
}

#[path = "historical_prefix_common_tests.rs"]
mod common_tests;

// Private H3 policy. Neither the legacy Public/profile admission nor its codec
// accepts this policy; callers cannot replace a layout or supply a transcript.
#[derive(Clone,Copy,Debug)]
struct Historical41Policy { headers:u64 }
impl Historical41Policy {
    fn new(headers:u64)->Result<Self,String>{
        if !matches!(headers,5|8){return Err("scaling41 headers".into());}Ok(Self{headers})
    }
    fn profile(self)->&'static [u8]{if self.headers==5 {b"historical-prefix-n5-common-seven-daa-v2"}else{b"historical-prefix-n8-common-seven-daa-v2"}}
    fn geometry(self,g:&Geometry)->Result<(),String>{
        if g.headers!=self.headers || (g.slot_log,g.slots,g.common_input,g.bank_bits)!=(3,8,23,4)
            || g.input_bits!=[23,23,23,16,23,23,23] || g.row_bits!=[24,22,22,17,23,12,15]
            || (g.height_row,g.daa_row,g.daa_row_base)!=(9,22,1<<22){return Err("scaling41 geometry".into());}Ok(())
    }
}
fn historical41_frame(public:&Public)->Result<Vec<u8>,String>{
    let policy=Historical41Policy::new(public.headers)?;let mut out=policy.profile().to_vec();
    out.extend(crate::header_order::MAINNET_GENESIS);out.extend([0u8;32]);
    for n in [public.headers,8,3,23]{out.extend(n.to_le_bytes());}
    out.extend(public.root);out.extend(public.total);out.extend(public.tip);out.extend(public.tip_time.to_le_bytes());
    for role in 0..7{out.extend((role as u64).to_le_bytes());out.extend((ROLES[role].len() as u64).to_le_bytes());
        out.extend(ROLES[role]);out.extend(([23u64,23,23,16,23,23,23][role]).to_le_bytes());
        out.extend(([24u64,22,22,17,23,12,15][role]).to_le_bytes());}
    if out.len()!=568{return Err("scaling41 frame serializer".into());}Ok(out)
}
fn historical41_take<const N:usize>(bytes:&[u8],at:&mut usize)->Result<[u8;N],String>{
    let end=at.checked_add(N).ok_or("scaling41 frame overflow")?;
    let value=bytes.get(*at..end).ok_or("scaling41 frame truncated")?.try_into().map_err(|_|"scaling41 frame width")?;
    *at=end;Ok(value)
}
fn historical41_decode(bytes:&[u8])->Result<Public,String>{
    if bytes.len()!=568{return Err("scaling41 frame extent".into());}
    let n=u64::from_le_bytes(bytes[104..112].try_into().map_err(|_|"scaling41 header field")?);
    let policy=Historical41Policy::new(n)?;
    if &bytes[..40]!=policy.profile(){return Err("scaling41 frame profile".into());}
    let mut at=40;
    if historical41_take::<32>(bytes,&mut at)?!=crate::header_order::MAINNET_GENESIS
        || historical41_take::<32>(bytes,&mut at)?!=[0;32]{return Err("scaling41 genesis anchor".into());}
    for expected in [n,8,3,23]{if u64::from_le_bytes(historical41_take(bytes,&mut at)?)!=expected{
        return Err("scaling41 frame geometry".into());}}
    let public=Public{headers:n,root:historical41_take(bytes,&mut at)?,total:historical41_take(bytes,&mut at)?,
        tip:historical41_take(bytes,&mut at)?,tip_time:i64::from_le_bytes(historical41_take(bytes,&mut at)?)};
    for role in 0..7{
        if u64::from_le_bytes(historical41_take(bytes,&mut at)?)!=role as u64
            || u64::from_le_bytes(historical41_take(bytes,&mut at)?)!=ROLES[role].len() as u64{
            return Err("scaling41 role roster".into());}
        let end=at.checked_add(ROLES[role].len()).ok_or("scaling41 role overflow")?;
        if bytes.get(at..end)!=Some(ROLES[role]){return Err("scaling41 role domain".into());}at=end;
        if u64::from_le_bytes(historical41_take(bytes,&mut at)?)!=[23,23,23,16,23,23,23][role]
            || u64::from_le_bytes(historical41_take(bytes,&mut at)?)!=[24,22,22,17,23,12,15][role]{
            return Err("scaling41 role geometry".into());}
    }
    if at!=bytes.len() || historical41_frame(&public)?!=bytes{return Err("scaling41 frame canonical".into());}Ok(public)
}

// This policy is trusted ONLY inside the independently admitted diagnostic
// parent invocation. Syntactic transport checks do not authenticate a caller.
#[derive(Clone)]
struct Historical41KeyPolicy { bytes:usize,sha:[u8;32],id:[u8;32],log_n:usize,review:[u8;32] }
impl Historical41KeyPolicy {
    fn transport(bytes:usize,sha:[u8;32],id:[u8;32],log_n:usize,review:[u8;32])->Result<Self,String>{
        if bytes!=25584 || log_n!=23{return Err("scaling41 key policy shape".into());}
        Ok(Self{bytes,sha,id,log_n,review})
    }
    fn admit(&self,bytes:&[u8],metadata:&[u8])->Result<verifier_key::AdmittedVerifierKey,String>{
        if self.bytes!=25584 || self.log_n!=23{return Err("scaling41 key policy shape".into());}
        if metadata.len()!=40{return Err("scaling41 key metadata extent".into());}
        if u64::from_le_bytes(metadata[..8].try_into().map_err(|_|"scaling41 key dimension width")?)!=self.log_n as u64{
            return Err("scaling41 key dimension".into());}
        if metadata[8..]!=self.id {return Err("scaling41 key id".into());}
        if bytes.len()!=self.bytes{return Err("scaling41 key extent".into());}
        if crate::native_prefix_auth_plan::role0_sha256(bytes)?!=self.sha{return Err("scaling41 key bytes".into());}
        verifier_key::admit_generated_test_key(23,bytes,self.id)
    }
}
fn historical41_consumer(public:&Public)->Result<Consumer,String>{
    Historical41Policy::new(public.headers)?;
    let OwnedLayouts{parent,adjacency,metadata,points,point_template}=compile_layouts(&LayoutRequest{
        headers:public.headers,slot_log:3,root:public.root,total:public.total,tip:public.tip,tip_time:public.tip_time})?;
    Ok(Consumer{public:public.clone(),parent,adjacency,metadata,points,point_template})
}
fn historical41_visit(parts:RelationRefs<'_, '_>,mut sink:impl FnMut(Term)->Result<(),String>)->Result<usize,String>{
    Historical41Policy::new(parts.geometry.headers)?.geometry(parts.geometry)?;
    // This enumeration is deliberately restricted to eight private TESTONLY
    // owners. It is not used by any generic/H21/default verifier path.
    let mut count=0usize;let mut emit=|term:Term|->Result<(),String>{
        if count>=1<<20 || term.row>=1<<parts.geometry.row_bits[4]
            || term.gate.left>=1<<23 || term.gate.right>=1<<23{return Err("scaling41 counted term domain".into());}
        count+=1;sink(term)
    };
    for owner in 0..8{parts.height.visit_owner_terms(owner,|term|emit(term))?;}
    for owner in 0..8{parts.daa.visit_owner_terms(owner,|mut term|{
        term.row=term.row.checked_add(parts.geometry.daa_row_base).ok_or("scaling41 row overflow")?;emit(term)})?;}
    Ok(count)
}
fn historical41_prefix(consumer:&Consumer,parts:RelationRefs<'_, '_>,serialized:&[u8],observation:&mut PreparationObservation)
    ->Result<(Transcript,Vec<u8>,[u8;32],usize),String>{
    let original=consumer.layout_refs();
    if !std::ptr::eq(parts.layouts.parent,original.parent){return Err("next36 parent layout identity".into());}
    if !std::ptr::eq(parts.layouts.adjacency,original.adjacency){return Err("next36 adjacency layout identity".into());}
    if !std::ptr::eq(parts.layouts.metadata,original.metadata){return Err("next36 metadata layout identity".into());}
    if !std::ptr::eq(parts.layouts.points,original.points){return Err("next36 points layout identity".into());}
    if !std::ptr::eq(parts.layouts.point_template,original.point_template){return Err("next36 fingerprint owner identity".into());}
    if !std::ptr::eq(parts.height.endpoint_parent(),original.parent){return Err("composite height parent identity".into());}
    if !std::ptr::eq(parts.daa.endpoint_parent(),original.parent){return Err("composite DAA parent identity".into());}
    if !std::ptr::eq(parts.point_role.base,&original.points.circuit){return Err("next36 point base identity".into());}
    parts.geometry.validate_layouts(consumer,parts.height,parts.daa)?;
    let policy=Historical41Policy::new(consumer.public.headers)?;policy.geometry(parts.geometry)?;
    if parts.mode!=HeightBinding::HistoricalDiagnostic{return Err("scaling41 historical mode".into());}
    let independent=historical41_visit(parts,|_|Ok(()))?;
    let terms=ProofContext::admit_census(independent,parts.composite_terms)?;
    let public_bytes=historical41_frame(&consumer.public)?;
    if public_bytes!=serialized{return Err("scaling41 candidate identity".into());}
    let corpus=Blake2b::<U32>::digest(&public_bytes).into();let mut base=Transcript::new(policy.profile());
    observation.transcript_created=true;base.append_bytes(b"public-statement-and-roster",&public_bytes);
    consumer.parent.bind(&mut base);consumer.adjacency.bind(&mut base);consumer.metadata.bind(&mut base);
    base.append_bytes(b"point-template",consumer.point_template.as_bytes());
    observation.challenges=base.challenges();observation.queries=base.raw_queries();
    Ok((base,public_bytes,corpus,terms))
}
impl<'a> ProofContext<'a>{
    fn historical_h3(consumer:&'a Consumer,serialized:&[u8])->Result<Self,String>{
        let decoded=historical41_decode(serialized)?;
        if historical41_frame(&decoded)?!=historical41_frame(&consumer.public)?{return Err("scaling41 candidate identity".into());}
        let parts=RelationParts::compile(consumer.layout_refs(),HeightBinding::HistoricalDiagnostic)?;
        let (mut base,public_bytes,corpus_id,composite_terms)=historical41_prefix(consumer,parts.refs(),serialized,&mut PreparationObservation::default())?;
        Self::bind_composite_parts(&parts.geometry,composite_terms,&parts.height,&parts.daa,&mut base);
        let RelationParts{height,daa,geometry,point_role,mode:height_binding,..}=parts;
        Ok(Self{consumer,height,daa,geometry,point_role,height_binding,composite_terms,public_bytes,corpus_id,base})
    }
}

struct Historical48Produced {
    proof: GkrProof,
    claim: InputClaim,
    counters: [u64;3],
    continuation: Fr,
    io: packed::PackedIoSnapshot,
}

#[path="historical_prefix_role0_candidate589_tests.rs"]
mod historical_prefix_role0_candidate589_tests;

fn prove_role0_historical48(
    context: &ProofContext<'_>, source: &PackedFile, admitted: &Historical47Admission,
) -> Result<Historical48Produced, String> {
    historical47_geometry(&context.geometry)?;
    historical47_refs(context.consumer, context.relation_refs())?;
    historical47_commitment(&admitted.commitment)?;
    if context.height_binding != HeightBinding::HistoricalDiagnostic || admitted.key.log_n() != 32
        || source.input_len() != 1usize << 32 || context.public_bytes != admitted.frame
        || historical47_frame(&context.consumer.public)? != admitted.frame {
        return Err("historical48 producer borrowed admission".into());
    }
    let mut transcript = context.transcript(0, &admitted.key, &admitted.commitment);
    if transcript.challenges() != 0 || transcript.raw_queries() != 0 {
        return Err("historical48 producer prefix advanced".into());
    }
    // The plan, binder and coefficients borrow the same owning Consumer.
    // The tensor engine calls bind once, after its actual residual validation.
    source.reset_io_metrics();
    let (proof, claim) = context.consumer.parent.core_pool().prove_packed_native_role0_for_test(
        source, &mut transcript,
        |t| { context.bind_role(0, t); Ok(()) },
        |r,u,v| context.coefficients(0,r,u,v),
    )?;
    if claim.point.len() != 32 || gkr::encode_proof(&proof)?.len() != 7264 {
        return Err("historical48 producer result shape".into());
    }
    let counters = [transcript.challenges(), transcript.raw_queries(), transcript.bytes_absorbed()];
    let continuation = transcript.clone().try_challenge_scalar(b"candidate-binding-role-continuation-v1")?;
    Ok(Historical48Produced { proof, claim, counters, continuation, io: source.io_metrics_snapshot() })
}
// Private Historical49 bridge. Native prepared prefixes and caller transcripts
// are deliberately absent; endpoint geometry is derived from these borrows.
#[derive(Clone,Debug,PartialEq,Eq)]
struct Historical49Shape{role:usize,base:usize,family:usize,strides:Vec<usize>,terms:u64,challenges:u64}
fn historical49_role(role:usize)->Result<(usize,usize,usize,u64,u64),String>{
    match role{6=>Ok((12,0,1,7181857,89)),2=>Ok((14,6,40,129277400,97)),
        4=>Ok((19,1,2,338580202,97)),_=>Err("historical49 closed role".into())}
}
fn historical49_policy(role:usize,mode:HeightBinding,g:&Geometry,source_len:usize,key_log:usize,
    same_frame:bool)->Result<(),String>{
    historical49_role(role)?;
    if mode!=HeightBinding::HistoricalDiagnostic{return Err("historical49 historical mode".into());}
    historical47_geometry(g)?;
    if source_len!=1usize<<32{return Err("historical49 source extent".into());}
    if key_log!=32{return Err("historical49 key dimension".into());}
    if !same_frame{return Err("historical49 candidate frame".into());}Ok(())
}
fn historical49_shape_policy(s:&Historical49Shape)->Result<(),String>{
    let(base,family,members,terms,challenges)=historical49_role(s.role)?;
    if (s.base,s.family,s.strides.len(),s.terms,s.challenges)!=(base,family,members,terms,challenges){
        return Err("historical49 endpoint shape/census".into());}
    if s.strides.iter().any(|v|*v>base)||s.strides.is_empty()
        ||(s.role==6&&s.strides!=[12])||(s.role==4&&s.strides!=[19,19]){
        return Err("historical49 endpoint strides".into());}Ok(())
}
fn historical49_admit(consumer:&Consumer,parts:RelationRefs<'_, '_>,role:usize,source_len:usize,key_log:usize,
    frame:&[u8])->Result<Historical49Shape,String>{
    historical49_policy(role,parts.mode,parts.geometry,source_len,key_log,
        historical47_frame(&consumer.public)?==frame)?;
    historical47_refs(consumer,parts)?;
    let(base,family,_,_,challenges)=historical49_role(role)?;
    let p=&consumer.parent;let mut shape=Historical49Shape{role,base,family,strides:Vec::new(),terms:0,challenges};
    let add=|sum:&mut u64,n:u64|->Result<(),String>{*sum=sum.checked_add(n).ok_or("historical49 census overflow")?;Ok(())};
    match role{
        6=>{consumer.metadata.role6_endpoint_shape_for_test()?;shape.strides.push(12);
            shape.terms=2337u64.checked_mul(parts.geometry.headers).and_then(|n|n.checked_add(256)).ok_or("historical49 census overflow")?;},
        2=>{let topo=p.topology();if work_tree_wiring::full_roster_shape(topo)?!=(26,6,32,32){return Err("historical49 role2 geometry".into());}
            for f in &topo.families{let c=f.count(&topo.descriptor)?;
                shape.strides.push(c.row_log.checked_sub(12).ok_or("historical49 source stride")?);add(&mut shape.terms,c.terms)?;}
            shape.strides.extend([11,14,11]);
            for n in [fixed::count(fixed::engine()?,p.fixed_profile())?.total_boundary_terms,
                crate::work_tree_leaf_hash::count(fixed::engine()?,p.leaf_boundary())?["new_boundary_terms"].as_u64().ok_or("historical49 leaf census")?,
                crate::work_tree_work::count(p.work_boundary())?["new_local_terms"].as_u64().ok_or("historical49 work census")?]{add(&mut shape.terms,n)?;}
            for f in p.work_boundary().links(){let c=f.count(&topo.descriptor)?;
                shape.strides.push(c.row_log.checked_sub(12).ok_or("historical49 source stride")?);add(&mut shape.terms,c.terms)?;}},
        4=>{crate::native_prefix_auth_plan::HistoricalRole4Endpoints::new(parts.height,parts.daa)?;
            let units=historical47_units(parts)?;let total=units.total()?;
            historical47_check_count(total,parts.composite_terms)?;
            shape.strides.extend([19,19]);shape.terms=u64::try_from(total).map_err(|_|"historical49 census width")?;},
        _=>return Err("historical49 closed role".into()),
    }
    historical49_shape_policy(&shape)?;Ok(shape)
}
fn historical49_visit(context:&ProofContext<'_>,shape:&Historical49Shape,left:bool,owner:usize,
    sink:&mut dyn FnMut(sparse_stream_roster::EdgeTerm)->Result<(),String>)->Result<(),String>{
    let p=&context.consumer.parent;
    match shape.role{
        6=>context.consumer.metadata.visit_endpoint_for_test(left,owner,
            &mut crate::header_metadata_order_layout::Role6EndpointStats::default(),sink),
        2=>work_tree_wiring::visit_full_roster_endpoint(p.topology(),fixed::engine()?,p.fixed_profile(),p.leaf_boundary(),
            p.work_boundary(),left,owner,&mut|edge|{work_tree_wiring::check_role2_endpoint_edge(&edge,left,owner,12,&shape.strides)?;sink(edge)}),
        4=>{crate::native_prefix_auth_plan::HistoricalRole4Endpoints::new(&context.height,&context.daa)?.visit(left,owner,sink)?;Ok(())},
        _=>Err("historical49 closed role".into()),
    }
}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
struct Historical49Census{expected:u64,left:Option<u64>,right:Option<u64>,events:u64,failed:bool}
impl Historical49Census{
    fn new(expected:u64)->Result<Self,String>{if expected==0{return Err("historical49 census expectation".into());}
        Ok(Self{expected,left:None,right:None,events:0,failed:false})}
    fn observe(&mut self,e:sparse_stream_roster::EdgeFullEvent)->Result<(),String>{
        if self.failed{return Err("historical49 poisoned census".into());}
        let result=self.observe_inner(e);if result.is_err(){self.failed=true;}result
    }
    fn observe_inner(&mut self,e:sparse_stream_roster::EdgeFullEvent)->Result<(),String>{
        self.events=self.events.checked_add(1).ok_or("historical49 observer count")?;
        if self.events>1024{return Err("historical49 bounded observer".into());}
        if e.stage!="census_left"&&e.stage!="census_right"{return Ok(());}
        if e.event!=b'p'{return Ok(());}
        if e.round!=0||e.owners==0||e.owners>4096||e.owners%1024!=0{return Err("historical49 census marker".into());}
        if e.owners!=4096{return Ok(());}
        if e.stage=="census_left"{
            if self.left.is_some()||self.right.is_some(){return Err("historical49 census completion order".into());}
            if e.terms!=self.expected{return Err("historical49 left census".into());}self.left=Some(e.terms);
        }else{
            if self.left!=Some(self.expected)||self.right.is_some(){return Err("historical49 census completion order".into());}
            if e.terms!=self.expected{return Err("historical49 right census".into());}self.right=Some(e.terms);
        }Ok(())
    }
    fn complete(&self)->Result<(),String>{if self.failed||self.left!=Some(self.expected)||self.right!=Some(self.expected){
        return Err("historical49 incomplete census".into());}Ok(())}
    fn try_bind(&self,t:&mut Transcript,bind:impl FnOnce(&mut Transcript))->Result<(),String>{
        self.complete()?;bind(t);Ok(())
    }
    fn bind(&self,t:&mut Transcript,bind:impl FnOnce(&mut Transcript)){
        // Returning without bind would still let the kernel consume challenges.
        // Abort the impossible incomplete callback path before any FS activity.
        self.try_bind(t,bind).expect("historical49 incomplete census before binder")
    }
}
struct Historical49Produced{
    proof:GkrProof,claim:InputClaim,counters:[u64;3],continuation:Fr,io:packed::PackedIoSnapshot,
    shape:Historical49Shape,edge:sparse_stream_roster::EdgeFullStats,
    packed:sparse_stream_roster::PackedEdgeMetrics,component_bound:usize,census:Historical49Census,
}
fn historical49_stats(s:&Historical49Shape,e:&sparse_stream_roster::EdgeFullStats,
    p:&sparse_stream_roster::PackedEdgeMetrics,io:&packed::PackedIoSnapshot)->Result<usize,String>{
    let t=s.terms;let mul=|a:u64,b:u64|a.checked_mul(b).ok_or("historical49 statistics overflow");
    let logical=mul(21,t)?.checked_add(176128).ok_or("historical49 statistics overflow")?;
    if e.left_counts.len()!=4096||e.right_counts.len()!=4096
        ||e.left_counts.iter().try_fold(0u64,|a,v|a.checked_add(*v as u64))!=Some(t)
        ||e.right_counts.iter().try_fold(0u64,|a,v|a.checked_add(*v as u64))!=Some(t)
        ||(e.term_callbacks,e.owner_requests,e.emitted_fields)!=(mul(44,t)?,176128,21474828288)
        ||(e.prefix_plans,e.suffix_tables,e.pattern_tables)!=(42,36,40)
        ||(e.sequential_x_folds,e.sequential_bank_folds,e.input_vector_clones)!=(0,0,0)
        ||(e.line_internal_clones,e.line_cloned_fields)!=(4096,4294967296)
        ||e.pass_ns.len()!=42{return Err("historical49 direct census statistics".into());}
    if (p.scalar_gets,p.logical_gets)!=(mul(21,t)?,logical)
        ||(p.vector_expansions,p.expanded_fields)!=(12288,12884901888)
        ||(p.projection_calls,p.projection_fields)!=(163840,8589926400)
        ||p.successful_loads==0||p.packed_bytes!=mul(p.successful_loads,131072)?
        ||io.read_calls!=p.successful_loads||io.read_bytes!=p.packed_bytes
        ||(io.write_calls,io.write_bytes,io.write_ns,io.sync_calls,io.sync_ns)!=(0,0,0,0,0){return Err("historical49 packed census statistics".into());}
    let bound=257565696usize.checked_add(p.metadata_capacity_bytes).ok_or("historical49 capacity overflow")?;
    if bound>512*1024*1024||p.packet_capacity_peak_bytes>131072
        ||p.cache_capacity_peak_bytes>524288usize.checked_add(p.metadata_capacity_bytes).ok_or("historical49 capacity overflow")?
        ||e.prefix_full>33554432||e.prefix_suffix>4194304||e.prefix_patterns>8192||e.prefix_metadata>1024
        ||e.banks>100663296||e.x>33554432||e.row_lookup>65536||e.u_weights>33554432||e.owner_weights>131072{
        return Err("historical49 direct component capacity".into());}Ok(bound)
}
fn prove_roles_historical49(context:&ProofContext<'_>,source:&PackedFile,admitted:&Historical47Admission,role:usize)
    ->Result<Historical49Produced,String>{
    historical47_commitment(&admitted.commitment)?;
    let shape=historical49_admit(context.consumer,context.relation_refs(),role,source.input_len(),admitted.key.log_n(),&admitted.frame)?;
    if context.public_bytes!=admitted.frame{return Err("historical49 context frame".into());}
    let mut t=context.transcript(role,&admitted.key,&admitted.commitment);
    if t.challenges()!=0||t.raw_queries()!=0{return Err("historical49 prefix advanced".into());}
    let view=source.native_role0_view()?;view.require_same_source(source)?;
    let mut input=sparse_stream_roster::PackedEdgeInput::new(1<<20,4096,|owner|Ok(view.read_copy(owner)?.into_bytes()))?;
    let census=std::cell::RefCell::new(Historical49Census::new(shape.terms)?);
    source.reset_io_metrics();
    let(proof,claim,used_u,used_v,edge)=sparse_stream_roster::prove_edge_terms_strategy_for_test(
        20,12,shape.base,shape.family,&shape.strides,true,true,true,0,&mut input,
        |left,owner,sink|historical49_visit(context,&shape,left,owner,sink),&mut t,
        |t|census.borrow().bind(t,|t|context.bind_role(role,t)),|r,u,v|context.coefficients(role,r,u,v),
        &mut|event|census.borrow_mut().observe(event))?;
    let census=census.into_inner();census.complete()?;
    if used_u||used_v||claim.point.len()!=32||gkr::encode_proof(&proof)?.len()!=7264{
        return Err("historical49 direct result shape".into());}
    let packed=input.metrics();drop(input);let io=source.io_metrics_snapshot();
    let component_bound=historical49_stats(&shape,&edge,&packed,&io)?;
    let counters=[t.challenges(),t.raw_queries(),t.bytes_absorbed()];
    if counters[0]!=shape.challenges{return Err("historical49 challenge census".into());}
    let continuation=t.clone().try_challenge_scalar(b"candidate-binding-role-continuation-v1")?;
    Ok(Historical49Produced{proof,claim,counters,continuation,io,shape,edge,packed,component_bound,census})
}
impl ProofContext<'_>{
    fn historical49_control_prefix(&self,role:usize,key:&verifier_key::AdmittedVerifierKey,commitment:&[u8],
        fault:Historical49PrefixFault)->Result<Transcript,String>{
        historical47_commitment(commitment)?;
        historical49_admit(self.consumer,self.relation_refs(),role,1usize<<32,key.log_n(),&self.public_bytes)?;
        let mut t=self.transcript(role,key,commitment);
        if fault==Historical49PrefixFault::ExtraRoleBinder{self.bind_role(role,&mut t);}
        if t.challenges()!=0||t.raw_queries()!=0{return Err("historical49 control prefix advanced".into());}Ok(t)
    }
    fn verify_role_historical49_control(&self,packet:&RoleProof,key:&verifier_key::AdmittedVerifierKey,commitment:&[u8],
        fault:Historical49PrefixFault)->Result<VerifiedRole,RoleFailure>{
        self.verify_role_inner(packet,key,commitment,Some(RolePrefixControl::Historical49(fault)))
    }
}

// Closed Historical50 capabilities. The lower producers never receive an
// arbitrary transcript prefix, loader or numeric permission from a caller.
const H50_COMPONENT_LIMIT:usize=512*1024*1024;
const H50_ROLE1_NUMERIC_BINDING_SERIALIZED_MAX:usize=6372;
const H50_ROLE1_NUMERIC_BINDING_HELPER_BOUND:usize=19116;
fn h50_add(a:usize,b:usize)->Result<usize,String>{a.checked_add(b).ok_or_else(||"historical50 capacity overflow".into())}
fn h50_mul(a:usize,b:usize)->Result<usize,String>{a.checked_mul(b).ok_or_else(||"historical50 capacity overflow".into())}
fn h50_sum(values:&[usize])->Result<usize,String>{values.iter().try_fold(0usize,|a,b|h50_add(a,*b))}
fn historical50_constructor_bound(role:usize,retained:usize)->Result<usize,String>{
    let bound=match role{5=>retained,3|1=>h50_sum(&[retained,h50_mul(3*4096+6,std::mem::size_of::<usize>())?,1024])?,
        _=>return Err("historical50 memory role/ABI".into())};
    if bound>H50_COMPONENT_LIMIT{return Err("historical50 constructor capacity".into());}Ok(bound)
}
#[derive(Clone,Copy,Debug,Default)]
struct Historical50Buffers{caller_inline:usize,caller_heap:usize,observer_inline:usize,export_retained:usize}
#[derive(Clone,Copy,Debug,Default,serde::Serialize)]
struct Historical50Memory{
    token_inline:usize,context_inline:usize,admission_inline:usize,descriptor_inline:usize,public_capacity:usize,frame_capacity:usize,
    commitment_capacity:usize,fingerprint_capacity:usize,transcript_clones:usize,binding_helper_bound:usize,
    caller_inline:usize,caller_heap:usize,observer_inline:usize,export_retained:usize,
    original_point_inline:usize,original_point_terms:usize,point_box_bytes:usize,
    retained_bytes:usize,constructor_bound:usize,component_limit:usize,opaque_graph_and_vendor_excluded:bool,
}
fn historical50_memory(context:&ProofContext<'_>,a:&Historical47Admission,role:usize,
    token_inline:usize,b:Historical50Buffers)->Result<Historical50Memory,String>{
    if !matches!(role,1|3|5)||std::mem::size_of::<usize>()!=8{return Err("historical50 memory role/ABI".into());}
    let mut m=Historical50Memory{token_inline,context_inline:std::mem::size_of_val(context),
        admission_inline:std::mem::size_of_val(a),public_capacity:context.public_bytes.capacity(),frame_capacity:a.frame.capacity(),
        descriptor_inline:if role==5{std::mem::size_of::<crate::header_adjacency_layout::linear_for_test::Descriptor<'static>>()}else{0},
        commitment_capacity:a.commitment.capacity(),fingerprint_capacity:context.consumer.point_template.capacity(),
        transcript_clones:h50_mul(3,std::mem::size_of::<Transcript>())?,
        binding_helper_bound:if role==1{H50_ROLE1_NUMERIC_BINDING_HELPER_BOUND}else if role==3{32}else{0},
        caller_inline:b.caller_inline,caller_heap:b.caller_heap,observer_inline:b.observer_inline,export_retained:b.export_retained,
        component_limit:H50_COMPONENT_LIMIT,opaque_graph_and_vendor_excluded:true,..Default::default()};
    if role==3{
        m.original_point_inline=std::mem::size_of_val(&context.consumer.points);
        m.original_point_terms=h50_mul(context.consumer.points.circuit.terms.capacity(),std::mem::size_of::<Term>())?;
        // The boxes are distinct original allocations, not the normalized
        // captured template already counted by the grouped kernel.
        for p in &context.consumer.points.layout.points{
            for x in [&p.x,&p.y,&p.u,&p.v].into_iter().chain(p.quotients.iter()).chain(p.comparisons.iter()){
                m.point_box_bytes=h50_add(m.point_box_bytes,h50_mul(x.len(),std::mem::size_of::<usize>())?)?;
            }
            for row in &p.carries{for x in row{m.point_box_bytes=h50_add(m.point_box_bytes,h50_mul(x.len(),std::mem::size_of::<usize>())?)?;}}
        }
        if m.point_box_bytes!=64352{return Err("historical50 point box ABI".into());}
    }
    m.retained_bytes=h50_sum(&[m.token_inline,m.context_inline,m.admission_inline,m.descriptor_inline,m.public_capacity,m.frame_capacity,
        m.commitment_capacity,m.fingerprint_capacity,m.transcript_clones,m.binding_helper_bound,m.caller_inline,m.caller_heap,
        m.observer_inline,m.export_retained,m.original_point_inline,m.original_point_terms,m.point_box_bytes])?;
    m.constructor_bound=historical50_constructor_bound(role,m.retained_bytes)?;Ok(m)
}
fn historical50_policy(role:usize,mode:HeightBinding,g:&Geometry,source_len:usize,key_log:usize,
    frame:&[u8],expected:&[u8])->Result<(),String>{
    historical47_policy(g.headers,g.slot_log,g.slots,key_log)?;
    if !matches!(role,1|3|5)||mode!=HeightBinding::HistoricalDiagnostic||source_len!=1usize<<32
        ||g.common_input!=32||g.input_bits!=[32,32,32,25,32,32,32]||g.row_bits!=[33,31,32,26,32,21,24]
        ||frame!=expected||frame.len()!=571{return Err("historical50 closed admission".into());}Ok(())
}
fn historical50_admit(consumer:&Consumer,parts:RelationRefs<'_, '_>,role:usize,source_len:usize,key_log:usize,
    frame:&[u8])->Result<(),String>{
    historical47_refs(consumer,parts)?;
    historical50_policy(role,parts.mode,parts.geometry,source_len,key_log,frame,&historical47_frame(&consumer.public)?)?;
    consumer.parent.work_profile().validate()?;
    if role==3&&(consumer.points.circuit.input_len!=8192||consumer.points.circuit.row_count!=16384
        ||consumer.points.circuit.terms.len()!=288158){return Err("historical50 point geometry".into());}Ok(())
}
fn historical50_hash_windows(count:usize,width:usize,expected:[u8;32],
    mut read:impl FnMut(usize)->Result<Vec<u8>,String>)->Result<[u8;32],String>{
    if count==0||count>4096||width==0||width>131072||h50_mul(count,width)?>536870912{
        return Err("historical50 reader binding bounds".into());}
    let mut state=Blake2b::<U32>::new();
    for owner in 0..count{let bytes=read(owner)?;
        if bytes.len()!=width||bytes.capacity()!=width{return Err("historical50 reader window".into());}state.update(&bytes);}
    let actual:[u8;32]=state.finalize().into();
    if actual!=expected{return Err("historical50 actual reader digest".into());}Ok(actual)
}
fn historical50_baseline_complete(role:usize,next:usize,terms:u64)->Result<(),String>{
    let expected=match role{3=>1180295168,1=>1624305664,_=>return Err("historical50 grouped role".into())};
    if next!=4096||terms!=expected{return Err("historical50 incomplete baseline".into());}Ok(())
}
struct Historical50BoundSource<'s>{source:&'s PackedFile,digest:[u8;32],io:packed::PackedIoSnapshot}
impl<'s> Historical50BoundSource<'s>{
    fn new(source:&'s PackedFile)->Result<Self,String>{
        let view=source.native_role0_view()?;view.require_same_source(source)?;source.reset_io_metrics();
        let expected=historical47_hex::<32>("725D7B1215E1185C52C1012D9294260612653ACAD53A02429B8EAAFD0F0770C8")?;
        let digest=historical50_hash_windows(4096,131072,expected,|owner|Ok(view.read_copy(owner)?.into_bytes()))?;
        let io=source.io_metrics_snapshot();
        if io.read_calls!=4096||io.read_bytes!=536870912{return Err("historical50 reader scan census".into());}
        Ok(Self{source,digest,io})
    }
    fn validate(&self)->Result<(),String>{
        if self.source.input_len()!=1usize<<32||self.digest!=historical47_hex::<32>(
            "725D7B1215E1185C52C1012D9294260612653ACAD53A02429B8EAAFD0F0770C8")?{
            return Err("historical50 bound source identity".into());}
        self.source.native_role0_view()?.require_same_source(self.source)
    }
}
pub(crate) struct Historical50GroupedAdmission<'c,'p>{
    context:&'c ProofContext<'p>,bound:&'c Historical50BoundSource<'c>,a:&'c Historical47Admission,role:usize,
    grouped:sparse_stream_roster::GroupedVAdmission,next:std::cell::Cell<usize>,terms:std::cell::Cell<u64>,
    bound_once:std::cell::Cell<bool>,memory:Historical50Memory,
}
impl<'c,'p> Historical50GroupedAdmission<'c,'p>{
    fn new(context:&'c ProofContext<'p>,bound:&'c Historical50BoundSource<'c>,a:&'c Historical47Admission,
        role:usize,buffers:Historical50Buffers)->Result<Self,String>{
        if !matches!(role,1|3){return Err("historical50 grouped role".into());}bound.validate()?;
        historical50_admit(context.consumer,context.relation_refs(),role,bound.source.input_len(),a.key.log_n(),&a.frame)?;
        let memory=historical50_memory(context,a,role,std::mem::size_of::<Self>(),buffers)?;
        // Charge map construction before any allocation; the sparse kernel
        // subsequently accounts the boxed map/counts and normalized templates.
        let mut map=vec![0usize;4096];if role==1{map[3072]=1;}
        if map.capacity()!=4096{return Err("historical50 grouped map capacity".into());}
        let grouped=sparse_stream_roster::GroupedVAdmission::try_new(12,&map,
            if role==3{&[288158]}else{&[396561,388369]})?;
        Ok(Self{context,bound,a,role,grouped,next:std::cell::Cell::new(0),terms:std::cell::Cell::new(0),
            bound_once:std::cell::Cell::new(false),memory})
    }
    pub(crate) fn role(&self)->usize{self.role}
    pub(crate) fn validate_for_use(&self)->Result<(),String>{
        self.bound.validate()?;historical50_admit(self.context.consumer,self.context.relation_refs(),self.role,
            self.bound.source.input_len(),self.a.key.log_n(),&self.a.frame)
    }
    pub(crate) fn grouped_admission(&self)->&sparse_stream_roster::GroupedVAdmission{&self.grouped}
    pub(crate) fn extra_live_capacity_bytes(&self)->usize{self.memory.retained_bytes}
    pub(crate) fn load_owner(&self,owner:usize)->Result<Vec<Fr>,String>{
        if owner>=4096{return Err("historical50 owner bound".into());}
        match self.role{3=>self.bound.source.read_copy(8192,owner.checked_mul(128).and_then(|x|x.checked_add(96))
            .ok_or("historical50 point owner overflow")?),
            1=>crate::packed_rows::read_row(self.bound.source,1usize<<20,owner),_=>Err("historical50 grouped role".into())}
    }
    pub(crate) fn visit_owner_terms(&self,owner:usize,sink:&mut dyn FnMut(Term)->Result<(),String>)->Result<(),String>{
        if owner>=4096||owner!=self.next.get(){return Err("historical50 baseline owner order".into());}
        let mut count=0u64;
        if self.role==3{
            for term in &self.context.consumer.points.circuit.terms{sink(term.clone())?;count=count.checked_add(1).ok_or("historical50 term overflow")?;}
            if count!=288158{return Err("historical50 point owner census".into());}
        }else if self.role==1{
            let rb=owner.checked_mul(1usize<<19).ok_or("historical50 row overflow")?;
            let ib=owner.checked_mul(1usize<<20).ok_or("historical50 input overflow")?;
            let counts=self.context.daa.visit_header_terms(owner as u64,|mut term|{
                if !(rb..rb+(1usize<<19)).contains(&term.row)||!(ib..ib+(1usize<<20)).contains(&term.gate.left)
                    ||!(ib..ib+(1usize<<20)).contains(&term.gate.right){return Err("historical50 header term window".into());}
                term.row-=rb;term.gate.left-=ib;term.gate.right-=ib;sink(term)?;
                count=count.checked_add(1).ok_or("historical50 term overflow")?;Ok(())})?;
            let short=owner==3072;
            if counts.emitted!=if short{388369}else{396561}||count!=counts.emitted as u64||counts.omitted_worktree!=78194
                ||counts.omitted_mature_a4!=0||counts.omitted_short_a4!=if short{8192}else{0}{
                return Err("historical50 header owner census".into());}
        }else{return Err("historical50 grouped role".into());}
        self.terms.set(self.terms.get().checked_add(count).ok_or("historical50 baseline overflow")?);
        self.next.set(owner+1);Ok(())
    }
    fn baseline_complete(&self)->Result<(),String>{
        historical50_baseline_complete(self.role,self.next.get(),self.terms.get())
    }
    pub(crate) fn bind_statement(&self,t:&mut Transcript)->Result<(),String>{
        self.validate_for_use()?;self.baseline_complete()?;
        if self.bound_once.get()||t.challenges()!=0||t.raw_queries()!=0{return Err("historical50 binder freshness/once".into());}
        let mut prepared=t.clone();
        if self.role==3{sparse::bind(&self.context.consumer.points.circuit,12,&mut prepared);}else{self.context.bind_role(1,&mut prepared);}
        if prepared.challenges()!=0||prepared.raw_queries()!=0{return Err("historical50 binder sampled challenge".into());}
        *t=prepared;self.bound_once.set(true);Ok(())
    }
    pub(crate) fn coefficients(&self,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String>{self.context.coefficients(self.role,r,u,v)}
    pub(crate) fn complete(&self)->Result<(),String>{self.baseline_complete()?;
        if !self.bound_once.get(){return Err("historical50 binder missing".into());}Ok(())}
}
pub(crate) struct Historical50Role5Admission<'c,'p>{
    context:&'c ProofContext<'p>,bound:&'c Historical50BoundSource<'c>,a:&'c Historical47Admission,
    memory:Historical50Memory,progress_count:std::cell::Cell<usize>,prepared:std::cell::Cell<bool>,
}
impl<'c,'p> Historical50Role5Admission<'c,'p>{
    fn new(context:&'c ProofContext<'p>,bound:&'c Historical50BoundSource<'c>,a:&'c Historical47Admission,
        buffers:Historical50Buffers)->Result<Self,String>{
        bound.validate()?;historical50_admit(context.consumer,context.relation_refs(),5,bound.source.input_len(),a.key.log_n(),&a.frame)?;
        let memory=historical50_memory(context,a,5,std::mem::size_of::<Self>(),buffers)?;
        Ok(Self{context,bound,a,memory,progress_count:std::cell::Cell::new(0),prepared:std::cell::Cell::new(false)})
    }
    pub(crate) fn require_layout(&self,layout:&HeaderAdjacencyLayout)->Result<(),String>{
        if !std::ptr::eq(layout,&self.context.consumer.adjacency){return Err("historical50 foreign adjacency capability".into());}
        self.bound.validate()?;historical50_admit(self.context.consumer,self.context.relation_refs(),5,
            self.bound.source.input_len(),self.a.key.log_n(),&self.a.frame)
    }
    pub(crate) fn descriptor(&self)->Result<crate::header_adjacency_layout::linear_for_test::Descriptor<'_>,String>{
        self.context.consumer.adjacency.historical50_role5_descriptor_for_test(self)
    }
    pub(crate) fn extra_live_capacity_bytes(&self)->usize{self.memory.retained_bytes}
    pub(crate) fn load_chunk(&self,chunk:usize)->Result<Vec<Fr>,String>{
        if chunk>=65536{return Err("historical50 role5 chunk bound".into());}self.bound.source.read_copy(65536,chunk)
    }
    pub(crate) fn prepare_binding(&self,t:&Transcript)->Result<Transcript,String>{
        self.require_layout(&self.context.consumer.adjacency)?;
        if self.prepared.get()||t.challenges()!=0||t.raw_queries()!=0{return Err("historical50 role5 binder freshness/once".into());}
        let mut prepared=t.clone();self.context.bind_role(5,&mut prepared);
        if prepared.challenges()!=0||prepared.raw_queries()!=0{return Err("historical50 binder sampled challenge".into());}
        self.prepared.set(true);Ok(prepared)
    }
    pub(crate) fn progress(&self,event:crate::segment_adjacency::linear_for_test::Native5Progress)->Result<(),String>{
        use crate::segment_adjacency::linear_for_test::{Native5Progress as E,Native5Side as S};
        let index=self.progress_count.get();let expected=match index{
            0=>E::ValidationComplete,1..=32=>E::Round{side:S::U,completed:index},
            33..=64=>E::Round{side:S::V,completed:index-32},65=>E::LineComplete,66=>E::ProducerComplete,
            _=>return Err("historical50 role5 progress extent".into())};
        if event!=expected{return Err("historical50 role5 progress order".into());}self.progress_count.set(index+1);Ok(())
    }
    pub(crate) fn complete(&self)->Result<(),String>{
        if !self.prepared.get()||self.progress_count.get()!=67{return Err("historical50 role5 incomplete producer".into());}Ok(())
    }
}
struct Historical50Produced{
    role:usize,proof:GkrProof,raw_claim:InputClaim,common_claim:Claim,counters:[u64;3],continuation:Fr,
    io:packed::PackedIoSnapshot,memory:Historical50Memory,
    grouped:Option<(sparse_stream_roster::GroupedVStats,sparse_stream_roster::BooleanUPreweightStats)>,
    linear:Option<(crate::segment_adjacency::linear_for_test::Stats,crate::segment_adjacency::linear_for_test::SupportStats)>,
    grouped_preflight:[usize;2],baseline_owners:u64,baseline_terms:u64,progress_events:u64,
}
fn prove_role_historical50(context:&ProofContext<'_>,bound:&Historical50BoundSource<'_>,a:&Historical47Admission,
    role:usize,buffers:Historical50Buffers)->Result<Historical50Produced,String>{
    historical47_commitment(&a.commitment)?;
    if context.public_bytes!=a.frame{return Err("historical50 context frame".into());}
    bound.validate()?;historical50_admit(context.consumer,context.relation_refs(),role,bound.source.input_len(),a.key.log_n(),&a.frame)?;
    let mut t=context.transcript(role,&a.key,&a.commitment);
    if t.challenges()!=0||t.raw_queries()!=0{return Err("historical50 producer prefix advanced".into());}
    bound.source.reset_io_metrics();
    let(proof,raw_claim,memory,grouped,linear,grouped_preflight,baseline_owners,baseline_terms,progress_events)=match role{
        3|1=>{let token=Historical50GroupedAdmission::new(context,bound,a,role,buffers)?;
            let preflight=sparse_stream_roster::historical50_grouped_preflight_for_test(&token)?;
            let(p,c,g,u)=sparse_stream_roster::prove_historical50_grouped_for_test(&token,&mut t)?;
            if u.u_state_peak_capacity_bytes>u.u_preflight_capacity_bound_bytes||u.u_preflight_capacity_bound_bytes>H50_COMPONENT_LIMIT
                ||g.grouped_state_peak_capacity_bytes>H50_COMPONENT_LIMIT{return Err("historical50 grouped component capacity".into());}
            (p,c,token.memory,Some((g,u)),None,preflight,token.next.get() as u64,token.terms.get(),0)},
        5=>{let token=Historical50Role5Admission::new(context,bound,a,buffers)?;
            let(p,c,s,support)=crate::segment_adjacency::linear_for_test::prove_historical50_role5_for_test(&token,&mut t)?;
            let owners=s.read_calls[0]/16;let terms=context.consumer.adjacency.term_count() as u64;
            (p,c,token.memory,None,Some((s,support)),[0;2],owners,terms,token.progress_count.get() as u64)},
        _=>return Err("historical50 producer role".into()),
    };
    let common_point=if role==3{context.point_role.project(&raw_claim.point)?}else{raw_claim.point.clone()};
    if common_point.len()!=32{return Err("historical50 common claim width".into());}
    let common_claim=Claim{point:common_point,value:raw_claim.value};let counters=[t.challenges(),t.raw_queries(),t.bytes_absorbed()];
    let expected=match role{3=>77,5=>86,1=>96,_=>unreachable!()};
    if counters[0]!=expected{return Err("historical50 producer challenge census".into());}
    let mut continuation=t.clone();let continuation=continuation.challenge_scalar(b"candidate-binding-role-continuation-v1");
    Ok(Historical50Produced{role,proof,raw_claim,common_claim,counters,continuation,io:bound.source.io_metrics_snapshot(),
        memory,grouped,linear,grouped_preflight,baseline_owners,baseline_terms,progress_events})
}
impl ProofContext<'_>{
    fn historical50_control_prefix(&self,role:usize,key:&verifier_key::AdmittedVerifierKey,commitment:&[u8],
        fault:Historical50PrefixFault)->Result<Transcript,String>{
        historical47_commitment(commitment)?;historical50_admit(self.consumer,self.relation_refs(),role,1usize<<32,key.log_n(),&self.public_bytes)?;
        let mut t=self.transcript(role,key,commitment);
        if fault==Historical50PrefixFault::ExtraRoleBinder{
            if role==3{sparse::bind(&self.consumer.points.circuit,12,&mut t);}else{self.bind_role(role,&mut t);}}
        if t.challenges()!=0||t.raw_queries()!=0{return Err("historical50 control prefix advanced".into());}Ok(t)
    }
    fn verify_role_historical50_control(&self,packet:&RoleProof,key:&verifier_key::AdmittedVerifierKey,commitment:&[u8],
        fault:Historical50PrefixFault)->Result<VerifiedRole,RoleFailure>{
        self.verify_role_inner(packet,key,commitment,Some(RolePrefixControl::Historical50(fault)))
    }
}

fn historical41_package(artifact:&Artifact)->Result<(),String>{
    if artifact.commitment.len()!=384 || artifact.roles.len()!=7 || artifact.batch.len()!=34269{
        return Err("scaling41 package extent".into());}
    for (role,packet) in artifact.roles.iter().enumerate(){
        if packet.role!=role || packet.bytes.len()!=if role==3{3680}else{5248}{return Err("scaling41 package role".into());}
    }
    if pcs::encode_commitment(&pcs::decode_commitment(&artifact.commitment).map_err(|_|"scaling41 canonical C")?)?!=artifact.commitment{
        return Err("scaling41 canonical C".into());}Ok(())
}
// Atomic fresh-byte entry: key material/policy are independently admitted by
// the diagnostic parent; none belongs to the candidate ten-file package.
fn verify_historical_h3_bytes(statement:&[u8],artifact:&Artifact,key_bytes:&[u8],id_bytes:&[u8],policy:&Historical41KeyPolicy)
    ->Result<[Claim;7],String>{
    let public=historical41_decode(statement)?;let key=policy.admit(key_bytes,id_bytes)?;
    historical41_package(artifact)?;let consumer=historical41_consumer(&public)?;
    let context=ProofContext::historical_h3(&consumer,statement)?;
    context.verify(artifact,&key).map_err(|e|format!("scaling41 atomic verification: {e:?}"))
}

fn historical41_admit(context:&ProofContext<'_>,source_len:usize,role:usize)->Result<History39Shape,String>{
    if role>=7{return Err("scaling41 role".into());}
    Historical41Policy::new(context.geometry.headers)?.geometry(&context.geometry)?;
    if context.height_binding!=HeightBinding::HistoricalDiagnostic{return Err("scaling41 historical mode".into());}
    if source_len!=1<<23{return Err("scaling41 source extent".into());}
    context.geometry.validate_layouts(context.consumer,&context.height,&context.daa)?;
    if !std::ptr::eq(context.height.endpoint_parent(),&context.consumer.parent)
        || !std::ptr::eq(context.daa.endpoint_parent(),&context.consumer.parent){return Err("stream39 parent identity".into());}
    let mut out=History39Shape{family_bits:0,strides:Vec::new(),terms:0};
    match role{
        2=>{let p=&context.consumer.parent;let topo=p.topology();let(local,family,row,input)=work_tree_wiring::full_roster_shape(topo)?;
            if (local,row,input)!=(17,22,23){return Err("scaling41 role2 geometry".into());}out.family_bits=family;
            for f in &topo.families{let c=f.count(&topo.descriptor)?;out.strides.push(c.row_log.checked_sub(3).ok_or("scaling41 stride")?);
                out.terms=out.terms.checked_add(c.terms).ok_or("scaling41 census overflow")?;}
            out.strides.extend([11,14,11]);
            for value in [crate::work_tree_fixed_hash::count(fixed::engine()?,p.fixed_profile())?.total_boundary_terms,
                crate::work_tree_leaf_hash::count(fixed::engine()?,p.leaf_boundary())?["new_boundary_terms"].as_u64().ok_or("scaling41 leaf count")?,
                crate::work_tree_work::count(p.work_boundary())?["new_local_terms"].as_u64().ok_or("scaling41 work count")?]{
                out.terms=out.terms.checked_add(value).ok_or("scaling41 census overflow")?;}
            for f in p.work_boundary().links(){let c=f.count(&topo.descriptor)?;out.strides.push(c.row_log.checked_sub(3).ok_or("scaling41 stride")?);
                out.terms=out.terms.checked_add(c.terms).ok_or("scaling41 census overflow")?;}
            if out.strides.len()!=topo.families.len()+6 || out.strides.len()>64 || out.strides.iter().any(|s|*s>14){return Err("scaling41 role2 strides".into());}
        },
        4=>{out.family_bits=1;out.strides.extend([19,19]);out.terms=context.term_count() as u64;},
        5=>{let d=context.consumer.adjacency.historical_h3_descriptor_for_test()?;d.validate(source_len,16)?;
            crate::segment_adjacency::linear_for_test::preflight_for_test(&d,0)?;out.terms=(context.geometry.headers+1)*256;},
        6=>{context.consumer.metadata.role6_endpoint_shape_for_test()?;out.strides.push(12);out.terms=2337*context.geometry.headers+256;},
        _=>(),
    }Ok(out)
}

fn historical41_point_shape(stage:usize,slots:usize,source_len:usize,owner:usize)->Result<(),GkrError>{
    if stage!=3||slots!=8||owner>=slots||source_len!=slots*crate::segment_relation::HEADER_WIDTH
        ||segment_points::POINT_WIDTH!=8192{return Err(GkrError::InvalidInputWidth);}Ok(())
}
fn historical41_point_load(source:&PackedFile,stage:usize,slots:usize,owner:usize)->Result<Vec<Fr>,GkrError>{
    historical41_point_shape(stage,slots,source.input_len(),owner)?;
    let bank=segment_points::POINT_OFFSET/segment_points::POINT_WIDTH;
    let per_owner=crate::segment_relation::HEADER_WIDTH/segment_points::POINT_WIDTH;
    source.read_copy(segment_points::POINT_WIDTH,owner*per_owner+bank).map_err(|_|GkrError::InvalidInputWidth)
}
fn historical41_edge_census(terms:u64,counts:[u64;4],loads:u64,fields:u64,io:&packed::PackedIoSnapshot)->Result<(),String>{
    let times=|n:u64,k:u64|n.checked_mul(k).ok_or("scaling41 census overflow");
    if terms==0||terms>1<<20{return Err("scaling41 edge term extent".into());}
    if counts!=[352,times(terms,44)?,times(terms,22)?,times(terms,22)?]{return Err("scaling41 edge census".into());}
    let upper=times(terms,21)?.checked_add(344).ok_or("scaling41 census overflow")?;
    if !(8..=upper).contains(&loads)||fields!=times(loads,layout::WIDTH as u64)?
        ||io.read_calls!=times(loads,16)?||io.read_bytes!=times(loads,131072)?{
        return Err("scaling41 edge load census".into());}Ok(())
}
fn prove_historical_h3(context:&ProofContext<'_>,source:&PackedFile,key:&verifier_key::AdmittedVerifierKey,commitment:&[u8],role:usize)
    ->Result<History39Produced,String>{
    let shape=historical41_admit(context,source.input_len(),role)?;
    if key.log_n()!=23 || pcs::encode_commitment(&pcs::decode_commitment(commitment)?)?!=commitment{return Err("scaling41 key or C".into());}
    let mut t=context.transcript(role,key,commitment);source.reset_io_metrics();let started=Instant::now();
    use std::cell::Cell;
    let calls=Cell::new(0u64);let callbacks=Cell::new(0u64);let sides=[Cell::new(0u64),Cell::new(0u64)];
    let loads=Cell::new(0u64);let fields=Cell::new(0u64);let load_ns=Cell::new(0u64);let capacity=Cell::new(0usize);
    let add=|c:&Cell<u64>,v:u64|->Result<(),String>{c.set(c.get().checked_add(v).ok_or("scaling41 counter overflow")?);Ok(())};
    let mut edge=None;let mut linear=None;
    let (proof,claim)=match role{
        0=>core_pool_boolean::prove_h3_for_test(&fixed::engine()?.core,4,
            &layout::CORE_OFFSETS.iter().map(|n|n/layout::CORE).collect::<Vec<_>>(),3,
            |owner|read_slot(source,owner,&context.geometry),&mut t,|t|context.bind_role(0,t),|r,u,v|context.coefficients(0,r,u,v))?,
        1=>prove_role(context,source,key,commitment,role)?,
        3=>sparse_stream_boolean::prove(&context.consumer.points.circuit,3,
            |owner|historical41_point_load(source,3,context.geometry.slots,owner),&mut t)
            .map_err(|e|format!("{e:?}"))?,
        5=>{let d=context.consumer.adjacency.historical_h3_descriptor_for_test()?;
            let(p,c,s)=crate::segment_adjacency::linear_for_test::prove(&d,source.input_len(),0,|chunk|{
                let begin=Instant::now();let x=history39_vector(source.read_copy(65536,chunk)?,65536)?;
                add(&loads,1)?;add(&fields,x.len() as u64)?;add(&load_ns,u64::try_from(begin.elapsed().as_nanos()).map_err(|_|"scaling41 clock")?)?;
                capacity.set(capacity.get().max(x.capacity()*32));Ok(x)},&mut t)?;
            if s.read_calls!=[128,2176,2176,128] || loads.get()!=4608 || fields.get()!=301989888{return Err("scaling41 linear census".into());}
            linear=Some(s);(p,c)
        },
        2|4|6=>{let role4=if role==4{Some(crate::native_prefix_auth_plan::HistoricalRole4Endpoints::new(&context.height,&context.daa)?)}else{None};
            let base=if role==2{14}else if role==4{19}else{12};
            let(p,c,u,v)=sparse_stream_roster::prove_edge_terms_with_cache_limit_for_test(20,3,base,shape.family_bits,&shape.strides,0,
                |left,owner,sink|{add(&calls,1)?;
                    let mut emit=|term|{sink(term)?;add(&callbacks,1)?;add(&sides[usize::from(!left)],1)};
                    if let Some(adapter)=&role4{adapter.visit(left,owner,|term|emit(term))?;}
                    else{history39_visit(context,role,&shape,left,owner,&mut emit)?;}Ok(())},
                |owner|{let begin=Instant::now();let x=history39_vector(read_slot(source,owner,&context.geometry)?,layout::WIDTH)?;
                    add(&loads,1)?;add(&fields,x.len() as u64)?;add(&load_ns,u64::try_from(begin.elapsed().as_nanos()).map_err(|_|"scaling41 clock")?)?;
                    capacity.set(capacity.get().max(x.capacity()*32));Ok(x)},&mut t,|t|context.bind_role(role,t),|r,u,v|context.coefficients(role,r,u,v))?;
            if u||v{return Err("scaling41 edge strategy".into());}
            historical41_edge_census(shape.terms,[calls.get(),callbacks.get(),sides[0].get(),sides[1].get()],
                loads.get(),fields.get(),&source.io_metrics_snapshot())?;
            edge=Some(HistoryStreamMetrics{endpoint_calls:calls.get(),callbacks:callbacks.get(),left_terms:sides[0].get(),right_terms:sides[1].get(),
                load_calls:loads.get(),loaded_fields:fields.get(),load_decode_ns:load_ns.get(),loader_capacity_peak:capacity.get(),io:source.io_metrics_snapshot()});(p,c)
        },
        _=>return Err("scaling41 role".into()),
    };
    if claim.point.len()!=context.geometry.input_bits[role] || gkr::encode_proof(&proof)?.len()!=if role==3{3680}else{5248}{
        return Err("scaling41 producer result shape".into());}
    let sender=if matches!(role,2|4|5|6){Some(([t.challenges(),t.raw_queries(),t.bytes_absorbed()],
        t.clone().try_challenge_scalar(b"candidate-binding-role-continuation-v1")?))}else{None};
    Ok(History39Produced{proof,claim,sender,edge,linear,io:source.io_metrics_snapshot(),
        elapsed_ns:u64::try_from(started.elapsed().as_nanos()).map_err(|_|"scaling41 clock")?,load_calls:loads.get(),
        loaded_fields:fields.get(),load_decode_ns:load_ns.get(),loader_capacity_peak:capacity.get(),terms:shape.terms})
}

// Private admission-only Historical32 diagnostic. No public profile is widened.
const H47_PROFILE: &[u8] = b"historical-prefix-n3073-common-seven-daa-v2";
const H47_INPUTS: [usize; 7] = [32,32,32,25,32,32,32];
const H47_ROWS: [usize; 7] = [33,31,32,26,32,21,24];
std::thread_local!{static H47_ACTIVITY:std::cell::Cell<[u64;2]>=const{std::cell::Cell::new([0;2])};}
fn historical47_activity()->[u64;2]{H47_ACTIVITY.with(|v|v.get())}
fn historical47_event(i:usize)->Result<(),String>{H47_ACTIVITY.with(|v|{let mut a=v.get();
    a[i]=a[i].checked_add(1).ok_or("admission47 activity overflow")?;v.set(a);Ok(())})}
fn historical47_policy(n:u64,h:usize,s:usize,log:usize)->Result<(),String>{
    if (n,h,s,log)!=(3073,12,4096,32){return Err("admission47 closed policy".into());}Ok(())
}
fn historical47_geometry(g:&Geometry)->Result<(),String>{
    historical47_policy(g.headers,g.slot_log,g.slots,g.common_input)?;
    if g.input_bits!=H47_INPUTS || g.row_bits!=H47_ROWS || g.bank_bits!=4
        || (g.height_row,g.daa_row,g.daa_row_base)!=(18,31,1usize<<31)
        || (g.point_local_input,g.point_local_row)!=(13,14){return Err("admission47 geometry".into());}Ok(())
}
fn historical47_frame(p:&Public)->Result<Vec<u8>,String>{
    historical47_policy(p.headers,12,4096,32)?;
    let mut out=H47_PROFILE.to_vec();out.extend(crate::header_order::MAINNET_GENESIS);out.extend([0;32]);
    for v in [p.headers,4096,12,32]{out.extend(v.to_le_bytes());}
    out.extend(p.root);out.extend(p.total);out.extend(p.tip);out.extend(p.tip_time.to_le_bytes());
    for i in 0..7{out.extend((i as u64).to_le_bytes());out.extend((ROLES[i].len() as u64).to_le_bytes());
        out.extend(ROLES[i]);out.extend((H47_INPUTS[i] as u64).to_le_bytes());out.extend((H47_ROWS[i] as u64).to_le_bytes());}
    if out.len()!=571{return Err("admission47 frame serializer".into());}Ok(out)
}
fn historical47_take<const N:usize>(b:&[u8],at:&mut usize)->Result<[u8;N],String>{
    let end=at.checked_add(N).ok_or("admission47 frame overflow")?;
    let v=b.get(*at..end).ok_or("admission47 frame truncated")?.try_into().map_err(|_|"admission47 frame width")?;
    *at=end;Ok(v)
}
fn historical47_decode(b:&[u8])->Result<Public,String>{
    if b.len()!=571{return Err("admission47 frame extent".into());}
    if b.get(..43)!=Some(H47_PROFILE){return Err("admission47 frame profile".into());}
    let mut at=43;
    if historical47_take::<32>(b,&mut at)?!=crate::header_order::MAINNET_GENESIS
        || historical47_take::<32>(b,&mut at)?!=[0;32]{return Err("admission47 genesis anchor".into());}
    for v in [3073u64,4096,12,32]{if u64::from_le_bytes(historical47_take(b,&mut at)?)!=v{
        return Err("admission47 frame geometry".into());}}
    let p=Public{headers:3073,root:historical47_take(b,&mut at)?,total:historical47_take(b,&mut at)?,
        tip:historical47_take(b,&mut at)?,tip_time:i64::from_le_bytes(historical47_take(b,&mut at)?)};
    for i in 0..7{
        if u64::from_le_bytes(historical47_take(b,&mut at)?)!=i as u64
            || u64::from_le_bytes(historical47_take(b,&mut at)?)!=ROLES[i].len() as u64{
            return Err("admission47 role roster".into());}
        let end=at.checked_add(ROLES[i].len()).ok_or("admission47 frame overflow")?;
        if b.get(at..end)!=Some(ROLES[i]){return Err("admission47 role domain".into());}at=end;
        if u64::from_le_bytes(historical47_take(b,&mut at)?)!=H47_INPUTS[i] as u64
            || u64::from_le_bytes(historical47_take(b,&mut at)?)!=H47_ROWS[i] as u64{
            return Err("admission47 role geometry".into());}
    }
    if at!=b.len() || historical47_frame(&p)?!=b{return Err("admission47 frame canonical".into());}Ok(p)
}
fn historical47_commitment(bytes:&[u8])->Result<(),String>{
    if bytes.len()!=384{return Err("admission47 commitment extent".into());}
    let c=pcs::decode_commitment(bytes).map_err(|_|"admission47 commitment decode")?;
    if pcs::encode_commitment(&c).map_err(|_|"admission47 commitment encode")?!=bytes{
        return Err("admission47 commitment canonical".into());}Ok(())
}
struct Historical47Admission{public:Public,frame:Vec<u8>,commitment:Vec<u8>,key:verifier_key::AdmittedVerifierKey}

// Provisional51 byte-only seam. The parent must separately adopt import
// custody, resource/interface bounds and actual50 results before any execution.
// This bound is a local allocation ceiling, not a production wire policy or
// an assertion of the future opening's measured size.
const HISTORICAL51_COMMON_BOUND:usize=65536;
const HISTORICAL51_CONTINUATION:&[u8]=b"native-seven-distinct-join-continuation-v1";
pub(crate) struct Historical51PublicBytes<'a>{
    pub(crate) frame:&'a[u8],pub(crate) commitment:&'a[u8],pub(crate) roles:[&'a[u8];7],pub(crate) common:&'a[u8],
}
// Closed fixed32 policy: this object cannot carry a transport-selected id,
// log dimension, key digest or profile. Historical47Admission checks the
// actual key/envelope against its existing fixed public TESTONLY authority.
pub(crate) struct Historical51TrustedKeyPolicy{_private:()}
impl Historical51TrustedKeyPolicy{
    pub(crate) fn fixed32_testonly()->Self{Self{_private:()}}
    fn admit(&self,bytes:&Historical51PublicBytes<'_>,key:&[u8],metadata:&[u8])->Result<Historical47Admission,String>{
        Historical47Admission::new(bytes.frame,key,metadata,bytes.commitment)
    }
    pub(crate) fn admit_key(&self,bytes:&Historical51PublicBytes<'_>,key:&[u8],metadata:&[u8])
        ->Result<verifier_key::AdmittedVerifierKey,String>{Ok(self.admit(bytes,key,metadata)?.key)}
}
pub(crate) struct Historical51Observations{
    pub(crate) role_counters:[[u64;3];7],pub(crate) role_continuations:[Fr;7],pub(crate) role_ns:[u128;7],
    pub(crate) common_counters:[u64;3],pub(crate) common_continuation:Fr,
    pub(crate) admission_ns:u128,pub(crate) context_ns:u128,pub(crate) roles_ns:u128,
    pub(crate) common_ns:u128,pub(crate) frontend_ns:u128,pub(crate) pcs_ns:u128,pub(crate) total_ns:u128,
    pub(crate) capacity:Historical51Capacity,
}
pub(crate) struct Historical51ByteSuccess{
    pub(crate) claims:[Claim;7],pub(crate) observations:Historical51Observations,
}
/// A verifier-created N3073/log32 prefix identity under the fixed TESTONLY key
/// policy. This retains Historical51's diagnostic scope. Fields are private:
/// diagnostic success record above, transported claims, and caller-root work
/// contexts cannot construct or deserialize this authority.
pub(crate) struct VerifiedHistorical51Prefix {
    headers: usize,
    root: [u8; 32],
    total: [u8; 28],
    tip: [u8; 32],
    tip_time: i64,
    genesis: [u8; 32],
    profile: &'static [u8],
    work_profile: [u8; 32],
    commitment: [u8; 384],
    key_id: [u8; 32],
    key_fingerprint: [u8; 32],
    binding_id: [u8; 32],
}

/// Membership under a successfully verified seven-role/common-PCS prefix.
/// It borrows that exact prefix handle and owns the checked RAW member. It is
/// not a native PoW result or a freshness/chain-comparison decision.
pub(crate) struct HistoryBoundWorkMember<'history> {
    history: &'history VerifiedHistorical51Prefix,
    member: crate::native_work_opening::NativeWorkMembership,
}

/// A history-bound opened member whose own authenticated header passed the
/// native Autolykos predicate. This preserves the fixed Historical51 TESTONLY
/// prefix scope; it does not establish sampling, chain selection or freshness.
pub(crate) struct HistoryBoundPowMember<'history> {
    history: &'history VerifiedHistorical51Prefix,
    pow: crate::native_autolykos_pow::NativePowMembership,
}

impl VerifiedHistorical51Prefix {
    pub(crate) fn headers(&self)->usize { self.headers }
    pub(crate) fn root(&self)->[u8;32] { self.root }
    pub(crate) fn total_be28(&self)->[u8;28] { self.total }
    pub(crate) fn tip(&self)->[u8;32] { self.tip }
    pub(crate) fn tip_time(&self)->i64 { self.tip_time }
    pub(crate) fn genesis(&self)->[u8;32] { self.genesis }
    pub(crate) fn profile(&self)->&'static [u8] { self.profile }
    pub(crate) fn work_profile(&self)->[u8;32] { self.work_profile }
    pub(crate) fn commitment(&self)->&[u8;384] { &self.commitment }
    pub(crate) fn key_id(&self)->[u8;32] { self.key_id }
    pub(crate) fn key_fingerprint(&self)->[u8;32] { self.key_fingerprint }
    pub(crate) fn binding_id(&self)->[u8;32] { self.binding_id }

    pub(crate) fn verify_work_opening(&self, coordinate:[u8;28], encoded:&[u8])
        ->Result<HistoryBoundWorkMember<'_>,crate::native_work_opening::NativeWorkOpeningError> {
        // There is deliberately no caller-selected n/root/total/context here.
        let context=crate::native_work_opening::NativeWorkMembershipContext::new(
            self.headers,self.root,self.total)?;
        let member=context.verify_encoded(coordinate,encoded)?;
        Ok(HistoryBoundWorkMember{history:self,member})
    }
}
impl<'history> HistoryBoundWorkMember<'history> {
    pub(crate) fn history(&self)->&VerifiedHistorical51Prefix { self.history }
    pub(crate) fn member(&self)->&crate::native_work_opening::NativeWorkMembership { &self.member }
    pub(crate) fn verify_native_pow(self)
        ->Result<HistoryBoundPowMember<'history>,crate::native_autolykos_pow::NativePowError> {
        let pow=crate::native_autolykos_pow::verify_membership(self.member)?;
        Ok(HistoryBoundPowMember{history:self.history,pow})
    }
}
impl HistoryBoundPowMember<'_> {
    pub(crate) fn history(&self)->&VerifiedHistorical51Prefix { self.history }
    pub(crate) fn member(&self)->&crate::native_work_opening::NativeWorkMembership { self.pow.membership() }
}

struct Historical51ByteResult{claims:[Claim;7],observations:Option<Historical51Observations>,verified:VerifiedHistorical51Prefix}

// Match the private child's <=4MiB actual caller metadata plus the inherited
// Native32 4MiB bounded codec/claim/serializer workspace reservation. These
// are reservations, not claimed actual heap measurements. Opaque graph/vendor
// internals remain separately limited by the enclosing2GiB Job.
#[derive(Clone,Copy,serde::Serialize)]
pub(crate) struct Historical51Capacity{
    known_owned_bytes:usize,caller_reservation:usize,auxiliary_reservation:usize,
    original_point_terms:usize,point_boxes:usize,component_bound:usize,
}
pub(crate) fn historical51_component_guard(known:usize,caller:usize,auxiliary:usize)->Result<usize,String>{
    let total=h50_sum(&[known,caller,auxiliary])?;
    if total>H50_COMPONENT_LIMIT{return Err("common51 known component capacity".into());}Ok(total)
}
fn historical51_capacity(context:&ProofContext<'_>,a:&Historical47Admission,artifact:&Artifact)->Result<Historical51Capacity,String>{
    if std::mem::size_of::<usize>()!=8{return Err("common51 capacity ABI".into());}
    let vector=|v:&Vec<u8>|v.capacity();
    let original_point_terms=h50_mul(context.consumer.points.circuit.terms.capacity(),std::mem::size_of::<Term>())?;
    let mut point_boxes=0;
    for p in &context.consumer.points.layout.points{
        for x in [&p.x,&p.y,&p.u,&p.v].into_iter().chain(p.quotients.iter()).chain(p.comparisons.iter()){
            point_boxes=h50_add(point_boxes,h50_mul(x.len(),std::mem::size_of::<usize>())?)?;}
        for row in &p.carries{for x in row{point_boxes=h50_add(point_boxes,h50_mul(x.len(),std::mem::size_of::<usize>())?)?;}}
    }
    if point_boxes!=64352{return Err("common51 point box ABI".into());}
    let mut known=h50_sum(&[std::mem::size_of_val(context.consumer),std::mem::size_of_val(context),std::mem::size_of_val(a),
        std::mem::size_of_val(artifact),vector(&context.public_bytes),vector(&a.frame),vector(&a.commitment),
        context.consumer.point_template.capacity(),original_point_terms,point_boxes,vector(&artifact.commitment),vector(&artifact.batch),
        h50_mul(artifact.roles.capacity(),std::mem::size_of::<RoleProof>())?])?;
    for p in &artifact.roles{known=h50_add(known,p.bytes.capacity())?;}
    let key=a.key.verifier();for v in [&key.delta_1l,&key.delta_1r,&key.delta_2l,&key.delta_2r,&key.chi]{
        known=h50_add(known,h50_mul(v.capacity(),std::mem::size_of::<dory_pcs::backends::arkworks::ArkGT>())?)?;}
    let caller_reservation=4*1024*1024;let auxiliary_reservation=4*1024*1024;
    let component_bound=historical51_component_guard(known,caller_reservation,auxiliary_reservation)?;
    Ok(Historical51Capacity{known_owned_bytes:known,caller_reservation,auxiliary_reservation,original_point_terms,point_boxes,component_bound})
}

fn historical51_public_shape(bytes:&Historical51PublicBytes<'_>)->Result<(),String>{
    if bytes.frame.len()!=571||bytes.commitment.len()!=384||bytes.common.is_empty()
        ||bytes.common.len()>HISTORICAL51_COMMON_BOUND{return Err("common51 public envelope extent".into());}
    for (role,packet) in bytes.roles.iter().enumerate(){
        if packet.len()!=if role==3{5696}else{7264}{return Err(format!("common51 role{role} packet extent"));}
    }
    Ok(())
}

// The candidate supplies only ten public buffers, never an Artifact, context,
// claimed-value oracle or transcript. All owned copies are bounded before
// allocation; the normal/observed wrappers share this same admission/body.
fn verify_historical51_bytes_core(bytes:&Historical51PublicBytes<'_>,key:&[u8],metadata:&[u8],
    policy:&Historical51TrustedKeyPolicy,diagnostic:Option<&mut Historical51Diagnostics>,observed:bool)
    ->Result<Historical51ByteResult,String>{
    if diagnostic.as_ref().map_or(false,|d|!d.pristine()){return Err("common51 diagnostic not fresh".into());}
    historical51_public_shape(bytes)?;
    let total=observed.then(Instant::now);let started=observed.then(Instant::now);
    let admitted=policy.admit(bytes,key,metadata)?;
    let artifact=Artifact{commitment:bytes.commitment.to_vec(),roles:bytes.roles.iter().enumerate()
        .map(|(role,packet)|RoleProof{role,bytes:packet.to_vec()}).collect(),batch:bytes.common.to_vec()};
    let admission_ns=started.map_or(0,|t|t.elapsed().as_nanos());let started=observed.then(Instant::now);
    let consumer=historical47_consumer(&admitted)?;
    let(context,_units)=ProofContext::historical_h12(&consumer,&admitted)?;
    let capacity=historical51_capacity(&context,&admitted,&artifact)?;
    let context_ns=started.map_or(0,|t|t.elapsed().as_nanos());
    let success=context.verify_atomic_core51(&artifact,&admitted.key,diagnostic,observed)
        .map_err(|e|format!("common51 atomic rejection: {e:?}"))?;
    let observations=if observed{
        let roles=success.roles.ok_or("common51 role observations incomplete")?;
        let common=success.common.ok_or("common51 common observations incomplete")?;
        let common_counters=[common.transcript.challenges(),common.transcript.raw_queries(),common.transcript.bytes_absorbed()];
        let common_continuation=common.transcript.clone().try_challenge_scalar(HISTORICAL51_CONTINUATION)?;
        Some(Historical51Observations{role_counters:roles.counters,role_continuations:roles.continuations,role_ns:roles.elapsed_ns,
            common_counters,common_continuation,admission_ns,context_ns,roles_ns:success.roles_ns,common_ns:success.common_ns,
            frontend_ns:common.frontend_ns,pcs_ns:common.pcs_ns,total_ns:total.ok_or("common51 total timer missing")?.elapsed().as_nanos(),capacity})
    }else{None};
    // The sole minting site is AFTER actual seven-role derivation and common
    // PCS verification. Reuse the same admitted immutable public statement,
    // commitment and key; no unverified bytes or success summary are parsed.
    let commitment:[u8;384]=admitted.commitment.as_slice().try_into()
        .map_err(|_|"common51 verified commitment extent")?;
    let key_id=*admitted.key.id();
    let key_fingerprint:[u8;32]=Blake2b::<U32>::digest(key).into();
    let mut binding=Blake2b::<U32>::new();
    binding.update(b"nipopow-verified-historical51-prefix-v1");
    binding.update(&admitted.frame);binding.update(commitment);
    binding.update(key_id);binding.update(key_fingerprint);
    let binding_id=binding.finalize().into();
    let mut work_profile=Blake2b::<U32>::new();
    work_profile.update(crate::work_tree_fixed_hash::PROFILE_PREFIX);
    work_profile.update(crate::header_order::MAINNET_GENESIS);
    let verified=VerifiedHistorical51Prefix {
        headers:usize::try_from(admitted.public.headers).map_err(|_|"common51 verified header count")?,
        root:admitted.public.root,total:admitted.public.total,tip:admitted.public.tip,
        tip_time:admitted.public.tip_time,genesis:crate::header_order::MAINNET_GENESIS,
        profile:H47_PROFILE,work_profile:work_profile.finalize().into(),commitment,key_id,key_fingerprint,binding_id,
    };
    Ok(Historical51ByteResult{claims:success.claims,observations,verified})
}

pub(crate) fn verify_and_seal_historical_h12_prefix51(bytes:&Historical51PublicBytes<'_>,
    key:&[u8],metadata:&[u8],policy:&Historical51TrustedKeyPolicy,
    diagnostic:&mut Historical51Diagnostics)->Result<VerifiedHistorical51Prefix,String> {
    Ok(verify_historical51_bytes_core(bytes,key,metadata,policy,Some(diagnostic),true)?.verified)
}

pub(crate) fn verify_historical_h12_bytes51(bytes:&Historical51PublicBytes<'_>,key:&[u8],metadata:&[u8],
    policy:&Historical51TrustedKeyPolicy)->Result<[Claim;7],String>{
    Ok(verify_historical51_bytes_core(bytes,key,metadata,policy,None,false)?.claims)
}
pub(crate) fn verify_historical_h12_bytes_observed51(bytes:&Historical51PublicBytes<'_>,key:&[u8],metadata:&[u8],
    policy:&Historical51TrustedKeyPolicy,diagnostic:&mut Historical51Diagnostics)->Result<Historical51ByteSuccess,String>{
    let success=verify_historical51_bytes_core(bytes,key,metadata,policy,Some(diagnostic),true)?;
    Ok(Historical51ByteSuccess{claims:success.claims,
        observations:success.observations.ok_or("common51 success observations missing")?})
}

// Producer-only opening input. This is not a verification result and no byte
// consumer accepts it: Phase C always reconstructs and derives its own claims.
pub(crate) struct Historical51OpeningInput{
    pub(crate) statement:opening_batch::Statement,
    pub(crate) role_counters:[[u64;3];7],pub(crate) role_continuations:[Fr;7],pub(crate) role_ns:[u128;7],
    pub(crate) admission_ns:u128,pub(crate) context_ns:u128,pub(crate) roles_ns:u128,pub(crate) old_common_ns:u128,
    pub(crate) old_common_rejection:String,pub(crate) diagnostic:Historical51Diagnostics,
    pub(crate) capacity:Historical51Capacity,
}
pub(crate) fn prepare_historical_h12_opening51(bytes:&Historical51PublicBytes<'_>,key:&[u8],metadata:&[u8],
    policy:&Historical51TrustedKeyPolicy)->Result<Historical51OpeningInput,String>{
    historical51_public_shape(bytes)?;
    let started=Instant::now();let admitted=policy.admit(bytes,key,metadata)?;
    // Malformed/old transport is not the required domain-linkage falsifier.
    // Canonicality is established before the costly graph/role work.
    let old=opening_batch::decode_proof(bytes.common,32)?;
    if opening_batch::encode_proof(&old,32)?!=bytes.common{return Err("common51 old opening not canonical".into());}drop(old);
    let artifact=Artifact{commitment:bytes.commitment.to_vec(),roles:bytes.roles.iter().enumerate()
        .map(|(role,packet)|RoleProof{role,bytes:packet.to_vec()}).collect(),batch:bytes.common.to_vec()};
    let admission_ns=started.elapsed().as_nanos();let started=Instant::now();
    let consumer=historical47_consumer(&admitted)?;let(context,_units)=ProofContext::historical_h12(&consumer,&admitted)?;
    let capacity=historical51_capacity(&context,&admitted,&artifact)?;
    let context_ns=started.elapsed().as_nanos();let started=Instant::now();
    let mut diagnostic=Historical51Diagnostics::default();let mut roles=Historical51RoleObservations::default();
    let verified=context.verified_roles_core51(&artifact,&admitted.key,Some(&mut diagnostic),Some(&mut roles))
        .map_err(|e|format!("common51 assembly role rejection: {e:?}"))?;
    let roles_ns=started.elapsed().as_nanos();let started=Instant::now();
    let old_common_rejection=match context.verify_common_core51(&artifact,&admitted.key,&verified,Some(&mut diagnostic),true){
        Err(CommonFailure::Verification(message))=>message,
        Err(other)=>return Err(format!("common51 old opening rejected outside actual verification: {other:?}")),
        Ok(_)=>return Err("common51 old Native opening accepted".into()),
    };
    let old_common_ns=started.elapsed().as_nanos();
    if old_common_rejection.len()>512{return Err("common51 old rejection extent".into());}
    if diagnostic.role_entries!=[1;7]||diagnostic.role_completions!=[1;7]
        ||diagnostic.role_completion_order!=[0,1,2,3,4,5,6]||diagnostic.roles_completed!=7
        ||diagnostic.common_entries!=1||diagnostic.frontend_entries!=1||diagnostic.frontend_completions!=diagnostic.pcs_entries
        ||diagnostic.pcs_entries>1||diagnostic.pcs_completions!=0||diagnostic.successes!=0{
        return Err("common51 old opening rejection attribution".into());}
    let statement=context.statement(&artifact,&admitted.key,verified.claims)
        .map_err(|e|format!("common51 producer statement: {e:?}"))?;
    drop(context);drop(consumer);drop(artifact);drop(admitted);
    Ok(Historical51OpeningInput{statement,role_counters:roles.counters,role_continuations:roles.continuations,role_ns:roles.elapsed_ns,
        admission_ns,context_ns,roles_ns,old_common_ns,old_common_rejection,diagnostic,capacity})
}

// Scan the very PackedFile later used by commit/frontend/open. Its existing
// deny-write/delete handle remains alive across those operations.
pub(crate) fn bind_historical51_packed_source(source:&PackedFile)->Result<packed::PackedIoSnapshot,String>{
    let bound=Historical50BoundSource::new(source)?;bound.validate()?;Ok(bound.io)
}

#[path="historical_verified_work_tests.rs"]
mod historical_verified_work_tests;

#[path="checkpoint_anchor590.rs"]
pub(crate) mod checkpoint_anchor590;
impl Historical47Admission{
    fn new(frame:&[u8],key:&[u8],metadata:&[u8],commitment:&[u8])->Result<Self,String>{
        let public=historical47_decode(frame)?;historical47_commitment(commitment)?;
        if metadata.len()!=40{return Err("admission47 key metadata extent".into());}
        if u64::from_le_bytes(metadata[..8].try_into().map_err(|_|"admission47 key width")?)!=32{
            return Err("admission47 key dimension".into());}
        let id=historical47_hex::<32>("1AE7BADC1E529C7A5CDA709AD1B418AF6AE2EFB6B7B4D909816D091C3260A51B")?;
        if metadata[8..]!=id{return Err("admission47 key id".into());}
        if key.len()!=33264{return Err("admission47 key extent".into());}
        let sha=historical47_hex::<32>("D11220A1CBB08BE2C84F6B854EC2A932B3FCEC49C217963D079DD8053F7B31B2")?;
        if crate::native_prefix_auth_plan::role0_sha256(key)?!=sha{return Err("admission47 key hash".into());}
        let key=verifier_key::admit_generated_test_key(32,key,id)?;
        Ok(Self{public,frame:frame.to_vec(),commitment:commitment.to_vec(),key})
    }
}
fn historical47_hex<const N:usize>(s:&str)->Result<[u8;N],String>{
    if s.len()!=2*N || !s.bytes().all(|v|v.is_ascii_digit()||(b'A'..=b'F').contains(&v)){
        return Err("admission47 fixed hex".into());}
    let mut out=[0;N];for (i,v) in out.iter_mut().enumerate(){*v=u8::from_str_radix(&s[2*i..2*i+2],16)
        .map_err(|_|"admission47 fixed hex")?;}Ok(out)
}
fn historical47_refs(consumer:&Consumer,parts:RelationRefs<'_, '_>)->Result<(),String>{
    let original=consumer.layout_refs();
    if !std::ptr::eq(parts.layouts.parent,original.parent){return Err("admission47 parent identity".into());}
    if !std::ptr::eq(parts.layouts.adjacency,original.adjacency){return Err("admission47 adjacency identity".into());}
    if !std::ptr::eq(parts.layouts.metadata,original.metadata){return Err("admission47 metadata identity".into());}
    if !std::ptr::eq(parts.layouts.points,original.points){return Err("admission47 points identity".into());}
    if !std::ptr::eq(parts.layouts.point_template,original.point_template){return Err("admission47 fingerprint identity".into());}
    if !std::ptr::eq(parts.height.endpoint_parent(),original.parent){return Err("admission47 height parent identity".into());}
    if !std::ptr::eq(parts.daa.endpoint_parent(),original.parent){return Err("admission47 DAA parent identity".into());}
    if !std::ptr::eq(parts.point_role.base,&original.points.circuit){return Err("admission47 point base identity".into());}
    parts.geometry.validate_layouts(consumer,parts.height,parts.daa)?;
    if parts.mode!=HeightBinding::HistoricalDiagnostic{return Err("admission47 historical mode".into());}Ok(())
}
#[derive(Clone,Copy)]
struct Historical47Units{height:usize,initial:usize,equal:usize,a1:usize,a2:usize,alias1:usize,alias2:usize,
    full:usize,complement:usize,zero_occurrences:usize}
impl Historical47Units{
    fn total(self)->Result<usize,String>{
        if self.height!=32{return Err("admission47 height unit".into());}
        if (self.initial,self.equal)!=(225,448){return Err("admission47 numeric units".into());}
        if (self.alias1,self.alias2)!=(192,288){return Err("admission47 alias units".into());}
        if (self.full,self.complement)!=(81920,73728){return Err("admission47 inactive units".into());}
        let numeric=self.equal.checked_mul(3069).and_then(|n|n.checked_add(self.initial));
        let inactive=self.full.checked_mul(4094).and_then(|n|n.checked_add(self.complement));
        self.height.checked_mul(3073).and_then(|n|n.checked_add(numeric?))
            .and_then(|n|n.checked_add(numeric?)).and_then(|n|n.checked_add(inactive?))
            .and_then(|n|n.checked_add(self.alias1)).and_then(|n|n.checked_add(self.alias2))
            .and_then(|n|n.checked_add(self.a1)).and_then(|n|n.checked_add(self.a2))
            .ok_or_else(||"admission47 census overflow".into())
    }
}
fn historical47_units(parts:RelationRefs<'_, '_>)->Result<Historical47Units,String>{
    historical47_geometry(parts.geometry)?;
    let mut height=0usize;let h=parts.height.visit_owner_terms(0,|_|{height+=1;Ok(())})?;
    if h.height!=height || h.numeric!=0{return Err("admission47 height emission".into());}
    let mut numeric=[0usize;2];
    for (i,owner) in [1,2].into_iter().enumerate(){let mut observed=0usize;
        let got=parts.height.visit_owner_terms(owner,|_|{observed+=1;Ok(())})?;
        if got.height!=32 || observed!=got.height+got.numeric{return Err("admission47 numeric emission".into());}numeric[i]=got.numeric;}
    let mut lane=[[0usize;4];2];let mut zero_occurrences=0;
    for (i,owner) in [2048usize,3072].into_iter().enumerate(){
        let got=parts.daa.visit_owner_terms(owner as u64,|term|{
            if term.row>>crate::daa_history_roster::SLOT_ROW_LOG!=owner{return Err("admission47 representative owner".into());}
            let channel=(term.row>>crate::daa_history_roster::LOCAL_ROW_LOG)&3;
            lane[i][channel]=lane[i][channel].checked_add(1).ok_or("admission47 representative overflow")?;
            if i==0 && channel==0 && (term.gate.c0.is_zero()||term.gate.c1.is_zero()||term.gate.c2.is_zero()||term.gate.c3.is_zero()){
                zero_occurrences+=1;}Ok(())})?;
        if got.lanes!=lane[i]{return Err("admission47 representative emission".into());}
        let mut local=0;let returned=parts.daa.visit_s12_local_endpoint_terms(owner,0,|_|{local+=1;Ok(())})?;
        if local!=returned || local!=lane[i][0]{return Err("admission47 local emission".into());}
    }
    let mut full=0;let returned=parts.daa.visit_s12_local_endpoint_terms(0,3,|_|{full+=1;Ok(())})?;
    if full!=returned || lane[0][2]!=0 || lane[1][2]!=0 || lane[1][3]!=0{
        return Err("admission47 inactive emission".into());}
    let units=Historical47Units{height,initial:numeric[0],equal:numeric[1],a1:lane[0][0],a2:lane[1][0],
        alias1:lane[0][1],alias2:lane[1][1],full,complement:lane[0][3],zero_occurrences};
    units.total()?;Ok(units)
}
fn historical47_check_count(expected:usize,stored:usize)->Result<(),String>{
    if expected!=stored{return Err("admission47 composite census".into());}Ok(())
}
fn historical47_prefix(consumer:&Consumer,parts:RelationRefs<'_, '_>,frame:&[u8],commitment:&[u8],
    observation:&mut PreparationObservation)->Result<(Transcript,Vec<u8>,[u8;32],Historical47Units),String>{
    historical47_commitment(commitment)?;historical47_refs(consumer,parts)?;historical47_geometry(parts.geometry)?;
    let units=historical47_units(parts)?;historical47_check_count(units.total()?,parts.composite_terms)?;
    let public_bytes=historical47_frame(&consumer.public)?;
    if public_bytes!=frame{return Err("admission47 candidate identity".into());}
    let corpus=Blake2b::<U32>::digest(&public_bytes).into();historical47_event(0)?;let mut base=Transcript::new(H47_PROFILE);
    observation.transcript_created=true;base.append_bytes(b"public-statement-and-roster",&public_bytes);
    consumer.parent.bind(&mut base);consumer.adjacency.bind(&mut base);consumer.metadata.bind(&mut base);
    base.append_bytes(b"point-template",consumer.point_template.as_bytes());
    observation.challenges=base.challenges();observation.queries=base.raw_queries();Ok((base,public_bytes,corpus,units))
}
fn historical47_consumer(admitted:&Historical47Admission)->Result<Consumer,String>{
    // The typed admission is made before the only owning H12 graph.
    historical47_policy(admitted.public.headers,12,4096,admitted.key.log_n())?;
    let public=&admitted.public;
    let OwnedLayouts{parent,adjacency,metadata,points,point_template}=compile_layouts(&LayoutRequest{
        headers:public.headers,slot_log:12,root:public.root,total:public.total,tip:public.tip,tip_time:public.tip_time})?;
    Ok(Consumer{public:public.clone(),parent,adjacency,metadata,points,point_template})
}
impl<'a> ProofContext<'a>{
    fn historical_h12(consumer:&'a Consumer,admitted:&Historical47Admission)->Result<(Self,Historical47Units),String>{
        historical47_commitment(&admitted.commitment)?;
        if historical47_frame(&consumer.public)?!=admitted.frame{return Err("admission47 candidate identity".into());}
        let parts=RelationParts::compile(consumer.layout_refs(),HeightBinding::HistoricalDiagnostic)?;
        let (mut base,public_bytes,corpus_id,units)=historical47_prefix(consumer,parts.refs(),&admitted.frame,
            &admitted.commitment,&mut PreparationObservation::default())?;
        let composite_terms=parts.composite_terms;
        Self::bind_composite_parts(&parts.geometry,composite_terms,&parts.height,&parts.daa,&mut base);
        let RelationParts{height,daa,geometry,point_role,mode:height_binding,..}=parts;
        Ok((Self{consumer,height,daa,geometry,point_role,height_binding,composite_terms,public_bytes,corpus_id,base},units))
    }
    fn historical47_role_prefix(&self,role:usize,admitted:&Historical47Admission)->Result<Transcript,String>{
        historical47_commitment(&admitted.commitment)?;
        if role>=7 || self.public_bytes!=admitted.frame || self.geometry.common_input!=admitted.key.log_n(){
            return Err("admission47 role admission".into());}
        historical47_event(1)?;let mut t=self.transcript(role,&admitted.key,&admitted.commitment);
        if role==3{sparse::bind(&self.consumer.points.circuit,self.geometry.slot_log,&mut t);}else{self.bind_role(role,&mut t);}
        if t.challenges()!=0 || t.raw_queries()!=0{return Err("admission47 prefix advanced".into());}Ok(t)
    }
}

#[path = "historical_prefix_role4_streaming_tests.rs"]
mod role4_streaming_join_tests;

#[path = "historical_prefix_role4_stream38_tests.rs"]
mod role4_stream38_tests;

// Closed sibling: the retained49 producer/statistics and normal verifier remain unchanged.
#[cfg(test)]
fn historical52_role(role:usize)->Result<(),String>{
    if role!=6{return Err("historical52 closed role6".into());}Ok(())
}
#[cfg(test)]
fn historical52_admit(consumer:&Consumer,parts:RelationRefs<'_, '_>,role:usize,source_len:usize,key_log:usize,frame:&[u8])
    ->Result<Historical49Shape,String>{
    historical52_role(role)?;historical49_admit(consumer,parts,role,source_len,key_log,frame)
}
#[cfg(test)]
struct Historical52Produced{legacy:Historical49Produced,fast:sparse_stream_roster::PackedLineStats}
#[cfg(test)]
fn historical52_stats(s:&Historical49Shape,e:&sparse_stream_roster::EdgeFullStats,
    p:&sparse_stream_roster::PackedEdgeMetrics,fast:&sparse_stream_roster::PackedLineStats,io:&packed::PackedIoSnapshot)->Result<usize,String>{
    historical52_role(s.role)?;historical49_shape_policy(s)?;
    let t=s.terms;let mul=|a:u64,b:u64|a.checked_mul(b).ok_or("historical52 statistics overflow");
    let logical=mul(21,t)?.checked_add(176128).ok_or("historical52 statistics overflow")?;
    if e.left_counts.len()!=4096||e.right_counts.len()!=4096
        ||e.left_counts.iter().try_fold(0u64,|a,v|a.checked_add(*v as u64))!=Some(t)
        ||e.right_counts.iter().try_fold(0u64,|a,v|a.checked_add(*v as u64))!=Some(t)
        ||(e.term_callbacks,e.owner_requests,e.emitted_fields)!=(mul(44,t)?,176128,17179860992)
        ||(e.prefix_plans,e.suffix_tables,e.pattern_tables)!=(42,36,40)
        ||(e.sequential_x_folds,e.sequential_bank_folds,e.input_vector_clones)!=(0,0,0)
        ||(e.line_internal_clones,e.line_cloned_fields)!=(0,0)
        ||e.pass_ns.len()!=42{return Err("historical52 direct census statistics".into());}
    if (p.scalar_gets,p.logical_gets)!=(mul(21,t)?,logical)
        ||(p.vector_expansions,p.expanded_fields)!=(8192,8589934592)
        ||(p.projection_calls,p.projection_fields)!=(163840,8589926400)
        ||p.successful_loads==0||p.packed_bytes!=mul(p.successful_loads,131072)?
        ||io.read_calls!=p.successful_loads||io.read_bytes!=p.packed_bytes
        ||(io.write_calls,io.write_bytes,io.write_ns,io.sync_calls,io.sync_ns)!=(0,0,0,0,0){return Err("historical52 packed census statistics".into());}
    let(bound,plan,extra)=sparse_stream_roster::packed_line52_reservation_for_test(p.metadata_capacity_bytes)?;
    if fast.builds!=1||fast.owners!=4096||fast.coefficients!=86016||fast.input_expanded_fields!=0
        ||(fast.lut_fields,fast.work_fields,fast.result_fields)!=(1024,524288,21)
        ||fast.plan_reserved_bytes!=plan||fast.plan_actual_bytes!=plan||fast.extra_reserved_bytes!=extra||fast.component_bound!=bound
        ||fast.build_ns.checked_add(fast.apply_ns).is_none_or(|n|n>fast.whole_ns){
        return Err("historical52 packed line statistics".into());}
    if bound>512*1024*1024||p.packet_capacity_peak_bytes>131072
        ||p.cache_capacity_peak_bytes>524288usize.checked_add(p.metadata_capacity_bytes).ok_or("historical52 capacity overflow")?
        ||e.prefix_full>33554432||e.prefix_suffix>4194304||e.prefix_patterns>8192||e.prefix_metadata>1024
        ||e.banks>100663296||e.x>33554432||e.row_lookup>65536||e.u_weights>33554432||e.owner_weights>131072{
        return Err("historical52 direct component capacity".into());}Ok(bound)
}
#[cfg(test)]
fn prove_role_historical52(context:&ProofContext<'_>,source:&PackedFile,admitted:&Historical47Admission,role:usize)
    ->Result<Historical52Produced,String>{
    historical52_role(role)?;historical47_commitment(&admitted.commitment)?;
    let shape=historical52_admit(context.consumer,context.relation_refs(),role,source.input_len(),admitted.key.log_n(),&admitted.frame)?;
    if context.public_bytes!=admitted.frame{return Err("historical49 context frame".into());}
    let mut t=context.transcript(role,&admitted.key,&admitted.commitment);
    if t.challenges()!=0||t.raw_queries()!=0{return Err("historical49 prefix advanced".into());}
    let view=source.native_role0_view()?;view.require_same_source(source)?;
    let mut input=sparse_stream_roster::PackedEdgeInput::new(1<<20,4096,|owner|Ok(view.read_copy(owner)?.into_bytes()))?;
    let census=std::cell::RefCell::new(Historical49Census::new(shape.terms)?);
    source.reset_io_metrics();
    let mut fast=sparse_stream_roster::PackedLineStats::default();
    let(proof,claim,used_u,used_v,edge)=sparse_stream_roster::prove_edge_terms_packed_line_for_test(
        20,12,shape.base,shape.family,&shape.strides,&mut input,
        |left,owner,sink|historical49_visit(context,&shape,left,owner,sink),&mut t,
        |t|census.borrow().bind(t,|t|context.bind_role(role,t)),|r,u,v|context.coefficients(role,r,u,v),
        &mut fast,&mut|event|census.borrow_mut().observe(event))?;
    let census=census.into_inner();census.complete()?;
    if used_u||used_v||claim.point.len()!=32||gkr::encode_proof(&proof)?.len()!=7264{
        return Err("historical49 direct result shape".into());}
    let packed=input.metrics();drop(input);let io=source.io_metrics_snapshot();
    let component_bound=historical52_stats(&shape,&edge,&packed,&fast,&io)?;
    let counters=[t.challenges(),t.raw_queries(),t.bytes_absorbed()];
    if counters[0]!=shape.challenges{return Err("historical49 challenge census".into());}
    let continuation=t.clone().try_challenge_scalar(b"candidate-binding-role-continuation-v1")?;
    Ok(Historical52Produced{legacy:Historical49Produced{proof,claim,counters,continuation,io,shape,edge,packed,component_bound,census},fast})
}

//! Verifies the numeric DAA action rows against one admitted input commitment.
//! Other structural families remain the enclosing history verifier's responsibility.

use ark_bn254::Fr;
use dory_pcs::backends::arkworks::ArkGT;

use crate::{
    daa_work_actions::DaaWorkActions,
    gkr::{self, GkrError, InputClaim},
    native_work_relation::NativeWorkRelation,
    pcs,
    retained_header_pairs::{validate_history_parent, EXPECTED_RETIREMENT, OWNER_RETAINED_TERMS,
        OWNER_RETIRED_TERMS, PAIR_INPUT_LEN, PAIR_INPUT_LOG, PAIR_RETAINED_TERMS,
        PAIR_ROW_COUNT, PAIR_ROW_LOG, PAIR_STARTS, PAIR_TERM_CAP},
    transcript::Transcript,
    verifier_key::AdmittedVerifierKey,
    work_tree_history_plan::WorkTreeHistoryPlan,
    work_tree_layout,
};

const DOMAIN: &[u8] = b"nipopow-numeric-daa-authenticated-v1";
const MAX_INPUT_LOG: usize = 41;
const SCALAR_BYTES: usize = 32;

pub(crate) struct NumericDaaVerifier<'a> {
    actions: DaaWorkActions<'a>,
    key: &'a AdmittedVerifierKey,
    commitment: ArkGT,
    commitment_bytes: Vec<u8>,
    input_log: usize,
    output_width: usize,
}

impl<'a> NumericDaaVerifier<'a> {
    pub(crate) fn new(
        parent: &'a WorkTreeHistoryPlan,
        key: &'a AdmittedVerifierKey,
        commitment_bytes: &[u8],
    ) -> Result<Self, String> {
        let actions = DaaWorkActions::new(parent)?;
        let input_log = actions.input_log();
        if input_log > MAX_INPUT_LOG || key.log_n() != input_log {
            return Err("numeric DAA key/input dimensions differ".into());
        }
        let output_width = 1usize
            .checked_shl(actions.row_log() as u32)
            .ok_or("numeric DAA output width overflow")?;
        let commitment = pcs::decode_commitment(commitment_bytes)
            .map_err(|e| format!("numeric DAA commitment rejected: {e}"))?;
        Ok(Self {
            actions,
            key,
            commitment,
            commitment_bytes: commitment_bytes.to_vec(),
            input_log,
            output_width,
        })
    }

    fn bind_gkr(&self, transcript: &mut Transcript) {
        transcript.append_u64(b"numeric-daa-authentication-version", 1);
        transcript.append_bytes(b"numeric-daa-authentication-role", b"numeric-work-actions");
        self.actions.bind(transcript);
        transcript.append_u64(b"numeric-daa-authentication-input-log", self.input_log as u64);
        transcript.append_u64(b"numeric-daa-authentication-row-log", self.actions.row_log() as u64);
        transcript.append_bytes(b"numeric-daa-authentication-mode", b"Transparent-dory-v1");
        transcript.append_bytes(b"numeric-daa-authentication-vendor", pcs::VENDOR_PIN);
        transcript.append_bytes(b"numeric-daa-authentication-setup", self.key.id());
        transcript.append_bytes(b"numeric-daa-authentication-commitment", &self.commitment_bytes);
    }

    fn check_gkr_extent(&self, bytes: &[u8]) -> Result<(), String> {
        // One layer: 2k quadratic messages, two terminal values and a degree-k line.
        let expected = (7 * self.input_log + 3) * SCALAR_BYTES;
        if bytes.len() != expected {
            return Err("numeric DAA GKR extent mismatch".into());
        }
        Ok(())
    }

    // Kept private: this claim is not authenticated until the PCS check succeeds.
    fn replay_gkr(&self, bytes: &[u8]) -> Result<(InputClaim, Transcript), String> {
        self.check_gkr_extent(bytes)?;
        let proof = gkr::decode_dimensions(&[self.input_log], bytes)?;
        if gkr::encode_proof(&proof)? != bytes {
            return Err("numeric DAA GKR encoding is not canonical".into());
        }
        let mut transcript = Transcript::new(DOMAIN);
        let claim = gkr::verify_with_wiring(
            &[self.input_log],
            self.output_width,
            &proof,
            &mut transcript,
            |t| self.bind_gkr(t),
            |layer, r, u, v| {
                if layer != 0 {
                    return Err(GkrError::ProofLayerCount);
                }
                self.actions
                    .coefficients(r, u, v)
                    .map_err(|_| GkrError::PointDimension)
            },
        )
        .map_err(|e| format!("numeric DAA GKR rejected: {e:?}"))?;
        Ok((claim, transcript))
    }

    pub(crate) fn verify(&self, gkr_bytes: &[u8], pcs_bytes: &[u8]) -> Result<(), String> {
        self.check_gkr_extent(gkr_bytes)?;
        let proof = pcs::decode_proof(pcs_bytes, self.input_log)
            .map_err(|e| format!("numeric DAA PCS encoding rejected: {e}"))?;
        let (claim, mut transcript) = self.replay_gkr(gkr_bytes)?;
        pcs_separator(&mut transcript);
        pcs::verify_admitted(
            self.commitment,
            claim.value,
            &claim.point,
            &proof,
            self.key,
            &mut transcript,
        )
        .map_err(|e| format!("numeric DAA PCS rejected: {e}"))
    }
}

fn pcs_separator(transcript: &mut Transcript) {
    transcript.append_bytes(b"numeric-daa-authentication-boundary", b"gkr-to-pcs-v1");
}

const NATIVE_WORK_DOMAIN: &[u8] = b"nipopow-native-work-authenticated-v1";

/// Concrete six-family relation, authenticated at its own GKR-derived claim.
pub(crate) struct NativeWorkVerifier<'a> {
    relation: NativeWorkRelation<'a>,
    key: &'a AdmittedVerifierKey,
    commitment: ArkGT,
    commitment_bytes: Vec<u8>,
    input_log: usize,
    output_width: usize,
}

impl<'a> NativeWorkVerifier<'a> {
    pub(crate) fn new(parent: &'a WorkTreeHistoryPlan, key: &'a AdmittedVerifierKey,
        commitment_bytes: &[u8]) -> Result<Self, String>
    {
        let relation = NativeWorkRelation::new(parent)?;
        let input_log = relation.input_log();
        if input_log > MAX_INPUT_LOG || key.log_n() != input_log {
            return Err("native work key/input dimensions differ".into());
        }
        let output_width = 1usize.checked_shl(relation.row_log() as u32)
            .ok_or("native work output width overflow")?;
        let commitment = pcs::decode_commitment(commitment_bytes)
            .map_err(|e| format!("native work commitment rejected: {e}"))?;
        Ok(Self { relation, key, commitment, commitment_bytes: commitment_bytes.to_vec(),
            input_log, output_width })
    }

    fn bind_gkr(&self, transcript: &mut Transcript) -> Result<(), String> {
        if transcript.challenges() != 0 {
            return Err("native work authentication binding after challenge".into());
        }
        transcript.append_u64(b"native-work-authentication-version", 1);
        transcript.append_bytes(b"native-work-authentication-role", b"native-work-six-families");
        self.relation.bind(transcript)?;
        transcript.append_u64(b"native-work-authentication-input-log", self.input_log as u64);
        transcript.append_u64(b"native-work-authentication-row-log", self.relation.row_log() as u64);
        transcript.append_bytes(b"native-work-authentication-mode", b"Transparent-dory-v1");
        transcript.append_bytes(b"native-work-authentication-vendor", pcs::VENDOR_PIN);
        transcript.append_bytes(b"native-work-authentication-setup", self.key.id());
        transcript.append_bytes(b"native-work-authentication-commitment", &self.commitment_bytes);
        Ok(())
    }

    fn check_gkr_extent(&self, bytes: &[u8]) -> Result<(), String> {
        if bytes.len() != (7 * self.input_log + 3) * SCALAR_BYTES {
            return Err("native work GKR extent mismatch".into());
        }
        Ok(())
    }

    fn replay_gkr(&self, bytes: &[u8]) -> Result<(InputClaim, Transcript), String> {
        self.check_gkr_extent(bytes)?;
        let proof = gkr::decode_dimensions(&[self.input_log], bytes)?;
        if gkr::encode_proof(&proof)? != bytes {
            return Err("native work GKR encoding is not canonical".into());
        }
        let mut transcript = Transcript::new(NATIVE_WORK_DOMAIN);
        self.bind_gkr(&mut transcript)?;
        let claim = gkr::verify_with_wiring(&[self.input_log], self.output_width,
            &proof, &mut transcript, |_| {}, |layer, r, u, v| {
                if layer != 0 { return Err(GkrError::ProofLayerCount); }
                self.relation.coefficients(r, u, v).map_err(|_| GkrError::PointDimension)
            }).map_err(|e| format!("native work GKR rejected: {e:?}"))?;
        if claim.point.len() != self.input_log {
            return Err("native work GKR input claim dimensions differ".into());
        }
        Ok((claim, transcript))
    }

    pub(crate) fn verify(&self, gkr_bytes: &[u8], pcs_bytes: &[u8]) -> Result<(), String> {
        self.check_gkr_extent(gkr_bytes)?;
        let proof = pcs::decode_proof(pcs_bytes, self.input_log)
            .map_err(|e| format!("native work PCS encoding rejected: {e}"))?;
        let (claim, mut transcript) = self.replay_gkr(gkr_bytes)?;
        native_work_pcs_separator(&mut transcript);
        pcs::verify_admitted(self.commitment, claim.value, &claim.point, &proof, self.key,
            &mut transcript).map_err(|e| format!("native work PCS rejected: {e}"))
    }
}

fn native_work_pcs_separator(transcript: &mut Transcript) {
    transcript.append_bytes(b"native-work-authentication-boundary", b"gkr-to-pcs-v1");
}


// The bounded producer owns every object on the original-X/PCS boundary.
// Preparation is not an authenticated-history token; other structural roles
// (including B1 inactive_tree_endpoints) remain independently required.
const WORK_PRODUCER_INPUT: usize = 1 << 22;
const WORK_PRODUCER_ROWS: usize = 1 << 18;
const WORK_PRODUCER_CHUNK: usize = 1 << 16;
const WORK_PRODUCER_TERM_CAP: usize = 25_522;
const WORK_PRODUCER_COUNTS: [[usize; 6]; 2] = [
    [673, 6530, 224, 224, 224, 8372],
    [1121, 10947, 224, 448, 224, 12558],
];

#[cfg(test)]
#[derive(Default, Debug, PartialEq, Eq)]
struct WorkPreparationAudit {
    relations: usize, opens: usize, chunks: usize, residuals: usize,
    setups: usize, commits: usize,
}

fn work_geometry(parent: &WorkTreeHistoryPlan, key: &AdmittedVerifierKey)
    -> Result<[usize; 6], String>
{
    if !(parent.headers() == 3 || parent.headers() == 4)
        || parent.slot_log() != 2 || parent.slots() != 4 || key.log_n() != 22
    {
        return Err("C569 cheap geometry/key dimension".into());
    }
    Ok(WORK_PRODUCER_COUNTS[parent.headers() as usize - 3])
}

fn require_work_key22(key: &AdmittedVerifierKey) -> Result<(), String> {
    let bytes = include_bytes!("../fixtures/verifier-keys-v1/log22.vk");
    let expected = crate::verifier_key::admit(22, bytes)?;
    let encoded = pcs::encode(&dory_pcs::backends::arkworks::ArkworksVerifierSetup(
        key.verifier().clone()))?;
    if key.log_n() != 22 || key.id() != expected.id() || encoded.as_slice() != bytes {
        return Err("C569 pinned key22 identity/bytes".into());
    }
    Ok(())
}

fn push_work_term(terms: &mut Vec<crate::sparse::Term>, counts: &mut [usize; 6],
    term: crate::sparse::Term) -> Result<(), String>
{
    if terms.len() >= WORK_PRODUCER_TERM_CAP {
        return Err("C569 term cap before push".into());
    }
    let tag = term.row >> 15;
    if tag >= counts.len() || term.row >= WORK_PRODUCER_ROWS
        || term.gate.left >= WORK_PRODUCER_INPUT || term.gate.right >= WORK_PRODUCER_INPUT
    {
        return Err("C569 term domain".into());
    }
    counts[tag] = counts[tag].checked_add(1).ok_or("C569 family count overflow")?;
    terms.push(term);
    Ok(())
}

fn work_circuit(relation: &NativeWorkRelation<'_>, expected: [usize; 6])
    -> Result<crate::sparse::Circuit, String>
{
    if relation.input_log() != 22 || relation.row_log() != 18 {
        return Err("C569 relation geometry".into());
    }
    let mut terms = Vec::new();
    terms.try_reserve_exact(WORK_PRODUCER_TERM_CAP)
        .map_err(|e| format!("C569 term reservation: {e}"))?;
    let mut counts = [0usize; 6];
    let emitted = relation.visit_terms(|term| push_work_term(&mut terms, &mut counts, term))?;
    if counts != expected || emitted != terms.len() || emitted != expected.iter().sum::<usize>() {
        return Err(format!("C569 exact family census {counts:?}"));
    }
    let circuit = crate::sparse::Circuit {
        input_len: WORK_PRODUCER_INPUT, row_count: WORK_PRODUCER_ROWS, terms,
    };
    crate::sparse::validate(&circuit, 0).map_err(|e| format!("C569 sparse bounds: {e:?}"))?;
    Ok(circuit)
}

fn check_work_rows(circuit: &crate::sparse::Circuit, input: &[Fr]) -> Result<(), String> {
    if circuit.input_len != WORK_PRODUCER_INPUT || circuit.row_count != WORK_PRODUCER_ROWS
        || input.len() != WORK_PRODUCER_INPUT || circuit.terms.len() > WORK_PRODUCER_TERM_CAP
    {
        return Err("C569 residual geometry/cap".into());
    }
    crate::sparse::validate(circuit, 0).map_err(|e| format!("C569 residual domain: {e:?}"))?;
    let mut rows = Vec::new();
    rows.try_reserve_exact(WORK_PRODUCER_ROWS)
        .map_err(|e| format!("C569 residual reservation: {e}"))?;
    rows.resize(WORK_PRODUCER_ROWS, Fr::from(0u64));
    for term in &circuit.terms { rows[term.row] += term.gate.evaluate(input); }
    if let Some((row, value)) = rows.iter().enumerate().find(|(_, value)| **value != Fr::from(0u64)) {
        let term = circuit.terms.iter().find(|term| term.row == row
            && term.gate.evaluate(input) != Fr::from(0u64))
            .ok_or("C569 nonzero row lacks contributing term")?;
        return Err(format!("C569 residual family{} row{} left{} right{} value{}",
            row >> 15, row, term.gate.left, term.gate.right, value));
    }
    Ok(())
}

struct PreparedNativeWork<'p> {
    parent: &'p WorkTreeHistoryPlan,
    relation: NativeWorkRelation<'p>,
    source: crate::packed::PackedFile,
    circuit: crate::sparse::Circuit,
    input: Vec<Fr>,
    key: AdmittedVerifierKey,
}

fn prepare_work_source<'p>(parent: &'p WorkTreeHistoryPlan, path: &std::path::Path,
    key: AdmittedVerifierKey,
    #[cfg(test)] mut audit: Option<&mut WorkPreparationAudit>)
    -> Result<PreparedNativeWork<'p>, String>
{
    // These cheap getters run before relation compilation, source access,
    // large allocation, setup, commitment or transcript construction.
    let expected = work_geometry(parent, &key)?;
    require_work_key22(&key)?;
    #[cfg(test)] if let Some(a) = audit.as_deref_mut() { a.relations += 1; }
    let relation = NativeWorkRelation::new(parent)?;
    let circuit = work_circuit(&relation, expected)?;
    #[cfg(test)] if let Some(a) = audit.as_deref_mut() { a.opens += 1; }
    let source = crate::packed::PackedFile::open(path, 22)?;
    if source.input_len() != WORK_PRODUCER_INPUT {
        return Err("C569 packed source length".into());
    }
    let mut input = Vec::new();
    input.try_reserve_exact(WORK_PRODUCER_INPUT)
        .map_err(|e| format!("C569 dense reservation: {e}"))?;
    for chunk in 0..64 {
        let values = source.read_copy(WORK_PRODUCER_CHUNK, chunk)?;
        #[cfg(test)] if let Some(a) = audit.as_deref_mut() { a.chunks += 1; }
        if values.len() != WORK_PRODUCER_CHUNK
            || input.len().checked_add(values.len()).filter(|n| *n <= WORK_PRODUCER_INPUT).is_none()
        {
            return Err("C569 packed chunk length/order extent".into());
        }
        input.extend_from_slice(&values);
    }
    if input.len() != WORK_PRODUCER_INPUT { return Err("C569 complete input length".into()); }
    #[cfg(test)] if let Some(a) = audit.as_deref_mut() { a.residuals += 1; }
    // No setup/commit exists when a real source first fails this check.
    check_work_rows(&circuit, &input)?;
    Ok(PreparedNativeWork { parent, relation, source, circuit, input, key })
}

pub(crate) struct NativeWorkProof { gkr_bytes: Vec<u8>, pcs_bytes: Vec<u8> }
impl NativeWorkProof {
    pub(crate) fn gkr_bytes(&self) -> &[u8] { &self.gkr_bytes }
    pub(crate) fn pcs_bytes(&self) -> &[u8] { &self.pcs_bytes }
}

pub(crate) struct NativeWorkProducer<'p> {
    prepared: PreparedNativeWork<'p>,
    setup: pcs::Setup,
    committed: crate::packed::PackedCommitted,
    commitment_bytes: Vec<u8>,
}
impl<'p> NativeWorkProducer<'p> {
    pub(crate) fn new(parent: &'p WorkTreeHistoryPlan, path: impl AsRef<std::path::Path>,
        key: AdmittedVerifierKey) -> Result<Self, String>
    {
        Self::create(parent, path.as_ref(), key, #[cfg(test)] None)
    }
    fn create(parent: &'p WorkTreeHistoryPlan, path: &std::path::Path,
        key: AdmittedVerifierKey,
        #[cfg(test)] mut audit: Option<&mut WorkPreparationAudit>) -> Result<Self, String>
    {
        let prepared = prepare_work_source(parent, path, key,
            #[cfg(test)] audit.as_deref_mut())?;
        #[cfg(test)] if let Some(a) = audit.as_deref_mut() { a.setups += 1; }
        let setup = pcs::generate_setup(22)?;
        let encoded = pcs::encode(&dory_pcs::backends::arkworks::ArkworksVerifierSetup(
            setup.verifier.clone()))?;
        if setup.log_n != 22 || setup.id != *prepared.key.id()
            || encoded.as_slice() != include_bytes!("../fixtures/verifier-keys-v1/log22.vk")
        {
            return Err("C569 generated setup identity/bytes".into());
        }
        #[cfg(test)] if let Some(a) = audit.as_deref_mut() { a.commits += 1; }
        let committed = crate::packed::commit(&prepared.source, &setup)?;
        let commitment_bytes = pcs::encode_commitment(&committed.commitment)?;
        Ok(Self { prepared, setup, committed, commitment_bytes })
    }
    pub(crate) fn commitment_bytes(&self) -> &[u8] { &self.commitment_bytes }
    pub(crate) fn prove(&self) -> Result<NativeWorkProof, String> {
        work_geometry(self.prepared.parent, &self.prepared.key)?;
        require_work_key22(&self.prepared.key)?;
        if self.prepared.relation.input_log() != 22
            || self.prepared.relation.row_log() != 18
            || self.prepared.source.input_len() != WORK_PRODUCER_INPUT
            || pcs::encode_commitment(&self.committed.commitment)? != self.commitment_bytes
        {
            return Err("C569 owned producer identity".into());
        }
        let verifier = NativeWorkVerifier::new(self.prepared.parent,
            &self.prepared.key, &self.commitment_bytes)?;
        let mut transcript = Transcript::new(NATIVE_WORK_DOMAIN);
        verifier.bind_gkr(&mut transcript)?;
        // Preserve C554's existing frame: no additional sparse::bind.
        let (proof, claim) = crate::sparse::prove_with_binding(&self.prepared.circuit,
            &self.prepared.input, 0, &mut transcript, |_| {})
            .map_err(|e| format!("C569 GKR producer: {e:?}"))?;
        if claim.point.len() != 22
            || self.prepared.source.evaluate(&claim.point)? != claim.value
        {
            return Err("C569 held original-X claim mismatch".into());
        }
        native_work_pcs_separator(&mut transcript);
        let opening = crate::packed::open(&self.committed, &self.prepared.source,
            &claim.point, &self.setup, &mut transcript)?;
        let gkr_bytes = gkr::encode_proof(&proof)?;
        let pcs_bytes = pcs::encode_proof(&opening)?;
        // Both complete byte strings are untrusted role proof material.
        Ok(NativeWorkProof { gkr_bytes, pcs_bytes })
    }
}

#[cfg(test)]
#[path = "native_work_real_join_tests.rs"]
mod native_work_real_join_tests;


const JOINED_INPUT_LOG: usize = 22;
const JOINED_WORK_ROW_LOG: usize = 18;
const JOINED_WORK_FAMILY_TAG_SHIFT: usize = 15;
const JOINED_WORK_TERM_COUNT: usize = 25_522;
const JOINED_WORK_TERM_FAMILY_COUNTS: [u64; 6] = [1_121, 10_947, 224, 448, 224, 12_558];
const JOINED_DOMAIN_WORK: &[u8] = b"nipopow-joined-history-three-claim-work-v1";
const JOINED_DOMAIN_PAIR0: &[u8] = b"nipopow-joined-history-three-claim-pair0-v1";
const JOINED_DOMAIN_PAIR2: &[u8] = b"nipopow-joined-history-three-claim-pair2-v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum JoinedProofKind {
    Work,
    Pair0,
    Pair2,
}

impl JoinedProofKind {
    fn tag(self) -> u8 {
        match self {
            Self::Work => 0,
            Self::Pair0 => 1,
            Self::Pair2 => 2,
        }
    }

    fn from_tag(tag: u8) -> Result<Self, String> {
        match tag {
            0 => Ok(Self::Work),
            1 => Ok(Self::Pair0),
            2 => Ok(Self::Pair2),
            _ => Err("joined history proof kind is unknown".into()),
        }
    }

    fn domain(self) -> &'static [u8] {
        match self {
            Self::Work => JOINED_DOMAIN_WORK,
            Self::Pair0 => JOINED_DOMAIN_PAIR0,
            Self::Pair2 => JOINED_DOMAIN_PAIR2,
        }
    }

    fn input_log(self) -> usize {
        match self {
            Self::Work => JOINED_INPUT_LOG,
            Self::Pair0 | Self::Pair2 => PAIR_INPUT_LOG,
        }
    }

    fn row_log(self) -> usize {
        match self {
            Self::Work => JOINED_WORK_ROW_LOG,
            Self::Pair0 | Self::Pair2 => PAIR_ROW_LOG,
        }
    }

    fn output_width(self) -> usize {
        1usize << self.row_log()
    }

    fn pair_start(self) -> Option<u64> {
        match self {
            Self::Work => None,
            Self::Pair0 => Some(PAIR_STARTS[0]),
            Self::Pair2 => Some(PAIR_STARTS[1]),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct JoinedHistoryProofHeader {
    root: [u8; 32],
    total_be28: [u8; 28],
    headers: u64,
    slot_log: usize,
    pair_starts: [u64; 2],
    key_id: [u8; 32],
    canonical_commitment: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct JoinedHistoryProofEntry {
    kind_tag: u8,
    gkr_bytes: Vec<u8>,
    pcs_bytes: Vec<u8>,
}

/// A bounded in-memory diagnostic envelope; it is not a production wire codec.
#[derive(Clone, Debug, PartialEq, Eq)]
struct JoinedHistoryProofBundle {
    header: JoinedHistoryProofHeader,
    entries: Vec<JoinedHistoryProofEntry>,
}

/// Verifies exactly three claims against one plan, admitted log-22 key and C.
/// It stores no retained-pair term vectors and accepts no caller query or gate.
struct JoinedHistoryDiagnosticVerifier<'a> {
    parent: &'a WorkTreeHistoryPlan,
    work_relation: NativeWorkRelation<'a>,
    key: &'a AdmittedVerifierKey,
    commitment: ArkGT,
    commitment_bytes: Vec<u8>,
    work_term_hash: String,
    pair_source_fingerprint: String,
}

impl<'a> JoinedHistoryDiagnosticVerifier<'a> {
    fn new(
        parent: &'a WorkTreeHistoryPlan,
        key: &'a AdmittedVerifierKey,
        commitment_bytes: &[u8],
    ) -> Result<Self, String> {
        validate_history_parent(parent)?;
        if parent.retirement_counts() != EXPECTED_RETIREMENT
            || PAIR_INPUT_LEN != (1usize << PAIR_INPUT_LOG)
            || PAIR_ROW_COUNT != (1usize << PAIR_ROW_LOG)
        {
            return Err("joined history fixed pair census/dimensions differ".into());
        }
        let work_relation = NativeWorkRelation::new(parent)?;
        if work_relation.input_log() != JOINED_INPUT_LOG
            || work_relation.row_log() != JOINED_WORK_ROW_LOG
            || key.log_n() != JOINED_INPUT_LOG
        {
            return Err("joined history key/relation dimensions differ".into());
        }
        let mut work_terms = Vec::new();
        work_terms
            .try_reserve_exact(JOINED_WORK_TERM_COUNT)
            .map_err(|_| "joined history work term allocation failed")?;
        let work_term_count = work_relation.visit_terms(|term| {
            work_terms.push(term);
            Ok(())
        })?;
        let mut work_family_counts = [0u64; 6];
        for term in &work_terms {
            let tag = term.row >> JOINED_WORK_FAMILY_TAG_SHIFT;
            if tag >= work_family_counts.len() {
                return Err("joined history native-work family tag differs".into());
            }
            work_family_counts[tag] = work_family_counts[tag]
                .checked_add(1)
                .ok_or("joined history native-work family count overflow")?;
        }
        if work_term_count != JOINED_WORK_TERM_COUNT
            || work_terms.len() != JOINED_WORK_TERM_COUNT
            || work_family_counts != JOINED_WORK_TERM_FAMILY_COUNTS
        {
            return Err("joined history canonical native-work census differs".into());
        }
        let work_term_hash = work_tree_layout::hash_terms(&work_terms);
        drop(work_terms);
        let commitment = pcs::decode_commitment(commitment_bytes)
            .map_err(|e| format!("joined history commitment rejected: {e}"))?;
        let pair_source_fingerprint = work_tree_layout::hash_bytes(
            include_bytes!("retained_header_pairs.rs"),
        );
        Ok(Self {
            parent,
            work_relation,
            key,
            commitment,
            commitment_bytes: commitment_bytes.to_vec(),
            work_term_hash,
            pair_source_fingerprint,
        })
    }

    fn expected_header(&self) -> JoinedHistoryProofHeader {
        JoinedHistoryProofHeader {
            root: self.parent.descriptor().root,
            total_be28: self.parent.work_profile().total_be28,
            headers: self.parent.headers(),
            slot_log: self.parent.slot_log(),
            pair_starts: PAIR_STARTS,
            key_id: *self.key.id(),
            canonical_commitment: self.commitment_bytes.clone(),
        }
    }

    fn check_header(&self, header: &JoinedHistoryProofHeader) -> Result<(), String> {
        if header != &self.expected_header() {
            return Err("joined history bundle header differs from verifier context".into());
        }
        Ok(())
    }

    fn bind_gkr(
        &self,
        kind: JoinedProofKind,
        transcript: &mut Transcript,
    ) -> Result<(), String> {
        if transcript.challenges() != 0 {
            return Err("joined history binding after challenge".into());
        }
        self.parent.bind(transcript);
        if transcript.challenges() != 0 {
            return Err("joined history plan binding derived a challenge".into());
        }
        self.work_relation.bind(transcript)?;
        if transcript.challenges() != 0 {
            return Err("joined history work binding derived a challenge".into());
        }

        transcript.append_bytes(b"joined-history-profile", b"three-claims-one-x-n4-h2-v1");
        transcript.append_bytes(b"joined-history-pair-source", self.pair_source_fingerprint.as_bytes());
        transcript.append_bytes(b"joined-history-root", &self.parent.descriptor().root);
        transcript.append_bytes(b"joined-history-total-be28", &self.parent.work_profile().total_be28);
        transcript.append_u64(b"joined-history-headers", 4);
        transcript.append_u64(b"joined-history-slot-log", 2);
        transcript.append_bytes(b"joined-history-coverage-tags", &[0, 1, 2]);
        for start in PAIR_STARTS {
            transcript.append_u64(b"joined-history-pair-start", start);
        }
        transcript.append_u64(b"joined-history-work-term-count", JOINED_WORK_TERM_COUNT as u64);
        for count in JOINED_WORK_TERM_FAMILY_COUNTS {
            transcript.append_u64(b"joined-history-work-family-term-count", count);
        }
        transcript.append_bytes(b"joined-history-work-canonical-term-hash", self.work_term_hash.as_bytes());
        transcript.append_u64(b"joined-history-pair-retained-term-count", PAIR_RETAINED_TERMS as u64);
        transcript.append_u64(b"joined-history-pair-owner-term-count", OWNER_RETAINED_TERMS as u64);
        transcript.append_u64(b"joined-history-pair-retired-owner-term-count", OWNER_RETIRED_TERMS as u64);
        transcript.append_u64(b"joined-history-pair-a4-owner-term-count", 0);
        transcript.append_u64(b"joined-history-pair-term-cap", PAIR_TERM_CAP as u64);
        let retirement = self.parent.retirement_counts();
        for count in [
            retirement.terms,
            retirement.rows,
            retirement.dummy_terms,
            retirement.dummy_rows,
            retirement.node_terms,
            retirement.endpoint_terms,
            retirement.protected_endpoint_terms,
        ] {
            transcript.append_u64(b"joined-history-retirement-census", count as u64);
        }
        transcript.append_bytes(b"joined-history-pcs-mode", b"Transparent-dory-v1");
        transcript.append_bytes(b"joined-history-pcs-vendor", pcs::VENDOR_PIN);
        transcript.append_bytes(b"joined-history-key-setup-id", self.key.id());
        transcript.append_bytes(b"joined-history-canonical-commitment", &self.commitment_bytes);
        transcript.append_bytes(b"joined-history-proof-kind", &[kind.tag()]);
        transcript.append_u64(b"joined-history-proof-input-log", kind.input_log() as u64);
        transcript.append_u64(b"joined-history-proof-row-log", kind.row_log() as u64);
        transcript.append_u64(b"joined-history-pcs-input-log", JOINED_INPUT_LOG as u64);
        Ok(())
    }

    fn verify_bundle(&self, bundle: &JoinedHistoryProofBundle) -> Result<(), String> {
        // The complete verifier-owned header and exact ordered coverage are
        // checked before any entry body is decoded.
        self.check_header(&bundle.header)?;
        if bundle.entries.len() != 3 {
            return Err("joined history bundle must contain exactly three entries".into());
        }
        let expected = [JoinedProofKind::Work, JoinedProofKind::Pair0, JoinedProofKind::Pair2];
        for (entry, kind) in bundle.entries.iter().zip(expected) {
            if JoinedProofKind::from_tag(entry.kind_tag)? != kind {
                return Err("joined history bundle entry order/coverage differs".into());
            }
        }
        for (entry, kind) in bundle.entries.iter().zip(expected) {
            self.replay_entry(kind, &entry.gkr_bytes, &entry.pcs_bytes)?;
        }
        Ok(())
    }

    // This is the same private path used after bundle preflight. A child test
    // may call it directly to attribute the isolated pair-0 mutant to GKR.
    fn replay_entry(
        &self,
        kind: JoinedProofKind,
        gkr_bytes: &[u8],
        pcs_bytes: &[u8],
    ) -> Result<gkr::InputClaim, String> {
        let expected_gkr_bytes = (7 * kind.input_log() + 3) * SCALAR_BYTES;
        if gkr_bytes.len() != expected_gkr_bytes {
            return Err("joined history GKR extent mismatch".into());
        }
        let proof = gkr::decode_dimensions(&[kind.input_log()], gkr_bytes)?;
        if gkr::encode_proof(&proof)? != gkr_bytes {
            return Err("joined history GKR encoding is not canonical".into());
        }

        let mut transcript = Transcript::new(kind.domain());
        self.bind_gkr(kind, &mut transcript)?;
        let claim = gkr::verify_with_wiring(
            &[kind.input_log()],
            kind.output_width(),
            &proof,
            &mut transcript,
            |_| {},
            |layer, r, u, v| {
                if layer != 0 {
                    return Err(GkrError::ProofLayerCount);
                }
                let coefficients = match kind {
                    JoinedProofKind::Work => self.work_relation.coefficients(r, u, v),
                    JoinedProofKind::Pair0 | JoinedProofKind::Pair2 => {
                        let start = kind.pair_start().expect("pair proof has fixed start");
                        let bit = (start >> 1) as u8;
                        let global_r = append_pair_bit(r, bit, PAIR_ROW_LOG)
                            .map_err(|_| GkrError::PointDimension)?;
                        let global_u = append_pair_bit(u, bit, PAIR_INPUT_LOG)
                            .map_err(|_| GkrError::PointDimension)?;
                        let global_v = append_pair_bit(v, bit, PAIR_INPUT_LOG)
                            .map_err(|_| GkrError::PointDimension)?;
                        self.parent.coefficients(&global_r, &global_u, &global_v)
                    }
                };
                coefficients.map_err(|_| GkrError::PointDimension)
            },
        )
        .map_err(|e| format!("joined history GKR rejected: {e:?}"))?;
        if claim.point.len() != kind.input_log() {
            return Err("joined history GKR input claim dimensions differ".into());
        }

        let proof = pcs::decode_proof(pcs_bytes, JOINED_INPUT_LOG)
            .map_err(|e| format!("joined history PCS encoding rejected: {e}"))?;
        let full_point = match kind {
            JoinedProofKind::Work => claim.point,
            JoinedProofKind::Pair0 | JoinedProofKind::Pair2 => append_pair_bit(
                &claim.point,
                (kind.pair_start().expect("pair proof has fixed start") >> 1) as u8,
                PAIR_INPUT_LOG,
            )?,
        };
        if full_point.len() != JOINED_INPUT_LOG {
            return Err("joined history PCS point dimensions differ".into());
        }
        joined_pcs_separator(kind, &mut transcript);
        pcs::verify_admitted(
            self.commitment,
            claim.value,
            &full_point,
            &proof,
            self.key,
            &mut transcript,
        )
        .map_err(|e| format!("joined history PCS rejected: {e}"))?;
        Ok(gkr::InputClaim { point: full_point, value: claim.value })
    }
}

fn append_pair_bit(point: &[Fr], bit: u8, expected_len: usize) -> Result<Vec<Fr>, String> {
    if point.len() != expected_len || bit > 1 {
        return Err("joined history pair point embedding dimensions rejected".into());
    }
    let mut embedded = Vec::with_capacity(expected_len + 1);
    embedded.extend_from_slice(point);
    embedded.push(Fr::from(bit as u64));
    Ok(embedded)
}

fn joined_pcs_separator(kind: JoinedProofKind, transcript: &mut Transcript) {
    transcript.append_bytes(b"joined-history-authentication-boundary", b"gkr-to-pcs-v1");
    transcript.append_bytes(b"joined-history-pcs-proof-kind", &[kind.tag()]);
}

#[cfg(test)]
#[path = "numeric_daa_authenticated_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "native_work_authenticated_tests.rs"]
mod native_work_tests;

#[cfg(test)]
#[path = "joined_history_authenticated_tests.rs"]
mod joined_history_tests;

const CORE3_TREE_DOMAIN: &[u8] = b"nipopow-core3-tree-opening-n4-v1";
const CORE3_TREE_PROFILE: &[u8] = b"four-claims-one-x-n4-h2-v1";

#[derive(Clone, Debug, PartialEq, Eq)]
struct Core3TreeProofHeader {
    core3: JoinedHistoryProofHeader,
    version: u64,
    profile: Vec<u8>,
    coverage: [u8; 4],
    pcs_input_log: usize,
    tree_input_log: usize,
    tree_row_log: usize,
    tree_terms: usize,
    tree_families: usize,
    tree_source: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Core3TreeProofBundle {
    header: Core3TreeProofHeader,
    entries: Vec<JoinedHistoryProofEntry>,
}

/// Internal fixed-case prototype. The public bundle path requires all four PCS
/// openings; neither the caller nor an entry supplies its own relation/context.
struct Core3TreeDiagnosticVerifier<'a> {
    core3: JoinedHistoryDiagnosticVerifier<'a>,
    tree: crate::h4_analytic::Plan,
    tree_source: String,
}

impl<'a> Core3TreeDiagnosticVerifier<'a> {
    fn new(parent: &'a WorkTreeHistoryPlan, key: &'a AdmittedVerifierKey,
        canonical_commitment: &[u8]) -> Result<Self, String>
    {
        let core3 = JoinedHistoryDiagnosticVerifier::new(parent, key, canonical_commitment)?;
        if parent.headers() != 4 || parent.slot_log() != 2 || key.log_n() != 22 {
            return Err("core3 tree requires n4/h2/key22".into());
        }
        let tree = crate::h4_analytic::Plan::new(
            parent.descriptor().root, parent.work_profile().total_be28)?;
        Ok(Self { core3, tree,
            tree_source: work_tree_layout::hash_bytes(include_bytes!("h4_analytic.rs")) })
    }

    fn expected_header(&self) -> Core3TreeProofHeader {
        Core3TreeProofHeader {
            core3: self.core3.expected_header(), version: 1,
            profile: CORE3_TREE_PROFILE.to_vec(), coverage: [0, 1, 2, 3],
            pcs_input_log: 22, tree_input_log: 22, tree_row_log: 21,
            tree_terms: 126_573, tree_families: 23, tree_source: self.tree_source.clone(),
        }
    }

    fn bind_tree_outer(&self, transcript: &mut Transcript) -> Result<(), String> {
        if transcript.challenges() != 0 {
            return Err("core3 tree outer binding after challenge".into());
        }
        // Reuse the exact code-owned Core3 public-profile binder as an anchor.
        // This does not alter the three original proof domains or their replay.
        self.core3.bind_gkr(JoinedProofKind::Work, transcript)?;
        let header = self.expected_header();
        transcript.append_u64(b"core3-tree-version", header.version);
        transcript.append_bytes(b"core3-tree-profile", &header.profile);
        transcript.append_bytes(b"core3-tree-required-roles", &header.coverage);
        transcript.append_bytes(b"core3-tree-role", b"Tree-global-input-claim");
        transcript.append_bytes(b"core3-tree-source", header.tree_source.as_bytes());
        for (label, value) in [
            (b"core3-tree-pcs-input-log".as_slice(), header.pcs_input_log),
            (b"core3-tree-input-log".as_slice(), header.tree_input_log),
            (b"core3-tree-row-log".as_slice(), header.tree_row_log),
            (b"core3-tree-term-count".as_slice(), header.tree_terms),
            (b"core3-tree-family-count".as_slice(), header.tree_families),
        ] {
            transcript.append_u64(label, value as u64);
        }
        if transcript.challenges() != 0 {
            return Err("core3 tree context binding derived a challenge".into());
        }
        // Ordinary H4 prove_tree/verify_tree append their full roster binder next.
        Ok(())
    }

    fn verify_bundle(&self, bundle: &Core3TreeProofBundle) -> Result<(), String> {
        if bundle.header != self.expected_header() {
            return Err("core3 tree bundle header differs from verifier context".into());
        }
        if bundle.entries.len() != 4 {
            return Err("core3 tree bundle must contain exactly four entries".into());
        }
        for (entry, expected) in bundle.entries.iter().zip([0u8, 1, 2, 3]) {
            if entry.kind_tag > 3 {
                return Err("core3 tree proof kind is unknown".into());
            }
            if entry.kind_tag != expected {
                return Err("core3 tree bundle order/coverage differs".into());
            }
        }
        // Check all extents before decoding or copying any body.
        for (entry, log) in bundle.entries.iter().zip([22usize, 21, 21, 22]) {
            if entry.gkr_bytes.len() != (7 * log + 3) * SCALAR_BYTES
                || entry.pcs_bytes.len() != 29_421
            {
                return Err("core3 tree body extent mismatch".into());
            }
        }
        self.core3.verify_bundle(&JoinedHistoryProofBundle {
            header: self.core3.expected_header(), entries: bundle.entries[..3].to_vec(),
        })?;
        let tree = &bundle.entries[3];
        self.replay_tree_entry(&tree.gkr_bytes, &tree.pcs_bytes)?;
        Ok(())
    }

    // Private: this exact path is invoked by public4 and the semantic control.
    fn replay_tree_entry(&self, gkr_bytes: &[u8], pcs_bytes: &[u8])
        -> Result<InputClaim, String>
    {
        if gkr_bytes.len() != 5_024 {
            return Err("core3 tree GKR extent mismatch".into());
        }
        let proof = gkr::decode_dimensions(&[22], gkr_bytes)?;
        if gkr::encode_proof(&proof)? != gkr_bytes {
            return Err("core3 tree GKR encoding is not canonical".into());
        }
        let mut transcript = Transcript::new(CORE3_TREE_DOMAIN);
        self.bind_tree_outer(&mut transcript)?;
        let claim = self.tree.verify_tree(&proof, &mut transcript)
            .map_err(|e| format!("core3 tree GKR rejected: {e}"))?;
        if claim.point.len() != 22 {
            return Err("core3 tree global input claim dimensions differ".into());
        }
        let pcs_proof = pcs::decode_proof(pcs_bytes, 22)
            .map_err(|e| format!("core3 tree PCS encoding rejected: {e}"))?;
        core3_tree_pcs_separator(&mut transcript);
        pcs::verify_admitted(self.core3.commitment, claim.value, &claim.point,
            &pcs_proof, self.core3.key, &mut transcript)
            .map_err(|e| format!("core3 tree PCS rejected: {e}"))?;
        Ok(claim)
    }
}

fn core3_tree_pcs_separator(transcript: &mut Transcript) {
    transcript.append_bytes(b"core3-tree-authentication-boundary", b"gkr-to-pcs-v1");
    transcript.append_bytes(b"core3-tree-pcs-role", &[3]);
}

#[path = "core3_tree_case_consumer.rs"]
mod core3_tree_case_consumer;
pub use core3_tree_case_consumer::{
    verify_internal_four_claim_case, ColdCaseError, ColdCaseVerification,
};

#[cfg(test)]
#[path = "native_core_pool_real_join_tests.rs"]
mod native_core_pool_real_join_tests;

#[cfg(test)]
#[path = "native_tree_real_join_tests.rs"]
mod native_tree_real_join_tests;

// Test-only borrowing capability. No caller can assemble unrelated PCS parts.
#[cfg(test)]
pub(crate) struct C573PcsLease<'o,'p> { owner: &'o NativeWorkProducer<'p> }
#[cfg(test)]
impl<'p> NativeWorkProducer<'p> {
    fn c573_lease(&self) -> Result<C573PcsLease<'_,'p>,String> {
        let lease=C573PcsLease{owner:self};lease.check()?;Ok(lease)
    }
}
#[cfg(test)]
impl<'o,'p> C573PcsLease<'o,'p> {
    pub(crate) fn check(&self)->Result<(),String>{
        let w=self.owner;let p=w.prepared.parent;let d=p.descriptor();
        if p.headers()!=3||p.slot_log()!=2||p.slots()!=4||d.genuine!=2||d.leaves!=2||d.slots!=4
            ||&p.topology().descriptor!=d||&p.fixed_profile().tree!=d||&p.leaf_profile().tree!=d||&p.work_profile().tree!=d
            ||w.prepared.source.input_len()!=1usize<<22||w.setup.log_n!=22||w.prepared.key.log_n()!=22
        {return Err("C573 lease geometry".into());}
        require_work_key22(&w.prepared.key)?;
        if w.setup.id!=*w.prepared.key.id()
            ||pcs::encode(&dory_pcs::backends::arkworks::ArkworksVerifierSetup(w.setup.verifier.clone()))?.as_slice()!=include_bytes!("../fixtures/verifier-keys-v1/log22.vk")
            ||pcs::encode_commitment(&w.committed.commitment)?!=w.commitment_bytes
        {return Err("C573 lease owned PCS identity".into());}
        w.prepared.source.h2_boolean_view()?.require_same_source(&w.prepared.source)?;Ok(())
    }
    pub(crate) fn parent(&self)->&'p WorkTreeHistoryPlan{self.owner.prepared.parent}
    pub(crate) fn key(&self)->&AdmittedVerifierKey{&self.owner.prepared.key}
    pub(crate) fn source(&self)->&crate::packed::PackedFile{&self.owner.prepared.source}
    pub(crate) fn setup(&self)->&pcs::Setup{&self.owner.setup}
    pub(crate) fn committed(&self)->&crate::packed::PackedCommitted{&self.owner.committed}
    pub(crate) fn commitment_bytes(&self)->&[u8]{self.owner.commitment_bytes()}
}
#[cfg(test)]
#[path="native_collection_cold_tests.rs"]
mod native_collection_cold_tests;

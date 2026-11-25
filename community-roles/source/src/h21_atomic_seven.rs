//! Public-input-only atomic structural diagnostic. A successful packet does
//! not establish full S, maturity, native PoW audit, freshness or production
//! security. No source/provenance handle or transported claim is admitted.
use super::*;

#[path="h21_atomic_seven_codec.rs"]
mod codec;

#[path="h21_candidate_roles.rs"]
mod h21_candidate_roles;

#[path="h21_history_pipeline.rs"]
mod history_pipeline;

#[path="full_structural.rs"]
pub(crate) mod full_structural;

const ROLE_DOMAINS: [&[u8]; 7] = [
    H21_ROLE0_DIAGNOSTIC_DOMAIN,
    b"nipopow-h21-role1-atomic-structural-diagnostic-v1",
    b"nipopow-h21-role2-atomic-structural-diagnostic-v1",
    b"nipopow-h21-role3-atomic-structural-diagnostic-v1",
    b"nipopow-h21-role4-atomic-structural-diagnostic-v1",
    b"nipopow-h21-role5-atomic-structural-diagnostic-v1",
    b"nipopow-h21-role6-era-bound-metadata-v2",
];

/// Owned result with a single minting site after real seven-role GKR and
/// unconditional common PCS verification. It carries structural scope only.
pub(crate) struct VerifiedH21StructuralPacket {
    statement: codec::H21Statement,
    packet: Vec<u8>,
    claims: [Claim; 7],
    key_id: [u8; 32],
    corpus_id: [u8; 32],
}
impl VerifiedH21StructuralPacket {
    pub(crate) fn profile(&self) -> &'static str { "H21AtomicSevenDiagnosticV2" }
    pub(crate) fn headers(&self) -> usize { crate::h21_snapshot::N }
    pub(crate) fn slot_log(&self) -> usize { 21 }
    pub(crate) fn genesis(&self) -> [u8;32] { crate::header_order::MAINNET_GENESIS }
    pub(crate) fn root(&self) -> [u8;32] { self.statement.root }
    pub(crate) fn total_be28(&self) -> [u8;28] { self.statement.total }
    pub(crate) fn tip(&self) -> [u8;32] { self.statement.tip }
    pub(crate) fn tip_time(&self) -> i64 { self.statement.tip_time }
    pub(crate) fn parameters(&self) -> [PublicMapParameters;2] { self.statement.parameters }
    pub(crate) fn claims(&self) -> &[Claim;7] { &self.claims }
    pub(crate) fn key_id(&self) -> [u8;32] { self.key_id }
    pub(crate) fn corpus_id(&self) -> [u8;32] { self.corpus_id }
    pub(crate) fn packet_bytes(&self) -> &[u8] { &self.packet }
    /// Serialize only the canonical, fully verified bytes owned by this result.
    pub(crate) fn encode(&self) -> Vec<u8> { self.packet.clone() }
}

// All bounded byte/field/group parsers run before the large public context.
// No setup ID or imported claimed value can replace actual key admission.
fn preflight_packet(packet: &codec::DecodedH21Packet)
    -> Result<(verifier_key::AdmittedVerifierKey, Vec<GkrProof>, opening_batch::Proof), String> {
    let key = verifier_key::admit(41, &packet.key)?;
    require_h21_role0_diagnostic_key(&key)?;
    let c = pcs::decode_commitment(&packet.commitment)?;
    if pcs::encode_commitment(&c)? != packet.commitment {
        return Err("H21 atomic noncanonical commitment".into());
    }
    let mut roles = Vec::with_capacity(7);
    for role in 0..7 {
        let proof = gkr::decode_dimensions(&[codec::INPUT_BITS[role] as usize], &packet.roles[role])?;
        if gkr::encode_proof(&proof)? != packet.roles[role] {
            return Err(format!("H21 atomic noncanonical role {role}"));
        }
        roles.push(proof);
    }
    let common = opening_batch::decode_proof(&packet.common, 41)?;
    if opening_batch::encode_proof(&common, 41)? != packet.common {
        return Err("H21 atomic noncanonical common opening".into());
    }
    Ok((key, roles, common))
}

fn fresh_h21_role_prefix(public_identity: &[u8], key: &verifier_key::AdmittedVerifierKey,
    commitment: &[u8], role: usize) -> Result<Transcript, String> {
    if role >= 7 { return Err("H21 atomic role index".into()); }
    require_h21_role0_diagnostic_key(key)?;
    pcs::decode_commitment(commitment)?;
    let mut t = Transcript::new(ROLE_DOMAINS[role]);
    if role == 0 {
        // Exact C592/C593 producer prefix, including its original domain.
        bind_h21_role0_prefix(public_identity, key, commitment, 0, &mut t)?;
    } else {
        t.append_bytes(b"setup-id", key.id());
        t.append_u64(b"H21-atomic-key-log", key.log_n() as u64);
        t.append_bytes(b"commitment", commitment);
        t.append_bytes(b"H21-atomic-public-identity", public_identity);
        t.append_u64(b"role-index", role as u64);
        t.append_bytes(b"role-domain", ROLES[role]);
    }
    Ok(t)
}

fn bind_h21_role(context: &H21StructuralDiagnosticContext<'_>, role: usize,
    t: &mut Transcript) -> Result<(), String> {
    context.bind_role(role, t)?; // Full H21 statement and actual structural roster.
    match role {
        0 => context.layouts.parent.core_pool().bind(t),
        1 => {}, // context.bind_role already binds the NEW MAX/Map/Score/Slack roster.
        2 => work_tree_wiring::bind_full_roster(context.layouts.parent.topology(),
            context.layouts.parent.fixed_profile(), context.layouts.parent.leaf_profile(),
            context.layouts.parent.work_profile(), t),
        3 => {}, // PointMath owns sparse::bind for its local template and 21 copies.
        4 => ProofContext::bind_composite_parts(&context.geometry, context.composite_terms,
            &context.height, context.roster.daa(), t),
        5 => context.layouts.adjacency.bind(t),
        6 => context.layouts.metadata.bind(t),
        _ => return Err("H21 atomic binder role index".into()),
    }
    Ok(())
}

#[cfg(all(windows, feature="h21-snapshot-n0"))]
pub(super) fn frozen_role1_output_point_for_measurement(context:&H21StructuralDiagnosticContext<'_>,
    commitment:&[u8])->Result<Vec<Fr>,String>{
    Ok(frozen_role1_u0_prefix(context,commitment)?.0)
}
#[cfg(all(windows, feature="h21-snapshot-n0"))]
pub(super) fn frozen_role1_u0_prefix(context:&H21StructuralDiagnosticContext<'_>,
    commitment:&[u8])->Result<(Vec<Fr>,Transcript),String>{
    let key=verifier_key::admit(41,include_bytes!("../fixtures/verifier-keys-v1/log41.vk"))?;
    let mut t=fresh_h21_role_prefix(context.public_bytes,&key,commitment,1)?;
    bind_h21_role(context,1,&mut t)?;
    let r=gkr::output_point(1usize<<40,&mut t);
    gkr::append_usize(&mut t,b"gkr-layer-index",0);
    Ok((r,t))
}

#[cfg(all(windows,feature="h21-snapshot-n0"))]
pub(super) fn historical_edge_output_point(context:&H21StructuralDiagnosticContext<'_>,role:usize,
    commitment:&[u8])->Result<Vec<Fr>,String>{
    if !matches!(role,2|4|6){return Err("unexpected historical edge role".into());}
    let key=verifier_key::admit(41,include_bytes!("../fixtures/verifier-keys-v1/log41.vk"))?;
    let mut t=fresh_h21_role_prefix(context.public_bytes,&key,commitment,role)?;
    bind_h21_role(context,role,&mut t)?;
    let outputs=1usize.checked_shl(context.geometry.row_bits[role] as u32).ok_or("edge output dimension")?;
    Ok(gkr::output_point(outputs,&mut t))
}

fn verify_h21_role(context: &H21StructuralDiagnosticContext<'_>, key: &verifier_key::AdmittedVerifierKey,
    commitment: &[u8], role: usize, proof: &GkrProof) -> Result<Claim, String> {
    if role >= 7 { return Err("H21 atomic role index".into()); }
    let terminal = if role == 0 {
        // Reuse the real one-role consumer, not a parallel acceptance path.
        let key_bytes = pcs::encode(&dory_pcs::backends::arkworks::ArkworksVerifierSetup(key.verifier().clone()))?;
        let admission = context.admit_role0_diagnostic(&key_bytes, commitment)?;
        admission.verify(&gkr::encode_proof(proof)?)?
    } else {
        let mut t = fresh_h21_role_prefix(context.public_bytes, key, commitment, role)?;
        bind_h21_role(context, role, &mut t)?;
        if role == 3 {
            context.point_role.verify(proof, &mut t).map_err(|e| e.to_string())?
        } else {
            gkr::verify_with_wiring(&[codec::INPUT_BITS[role] as usize],
                1usize << codec::ROW_BITS[role], proof, &mut t, |_| {}, |layer,r,u,v| {
                    if layer != 0 { return Err(GkrError::ProofLayerCount); }
                    context.coefficients(role,r,u,v).map_err(|_| GkrError::InvalidWireIndex)
                }).map_err(|e| format!("H21 atomic role {role}: {e}"))?
        }
    };
    let point = if role == 3 { context.point_role.project(&terminal.point)? } else { terminal.point };
    if point.len() != 41 { return Err("H21 atomic projected claim dimension".into()); }
    Ok(Claim { point, value:terminal.value })
}

/// Decode only bounded public bytes; independently derive all seven claims,
/// then execute the actual common frontend AND admitted PCS before success.
pub(crate) fn verify_h21_packet(bytes: &[u8]) -> Result<VerifiedH21StructuralPacket, String> {
    let packet = codec::decode_packet(bytes)?;
    if codec::encode_packet(&packet)? != bytes {
        return Err("H21 atomic noncanonical packet".into());
    }
    let (key, proofs, common) = preflight_packet(&packet)?;
    let s = &packet.statement;
    let public = H21StructuralDiagnostic::compile(s.root, s.total, s.tip, s.tip_time, s.parameters)?;
    let context = public.context()?;
    let mut claims = Vec::with_capacity(7);
    for role in 0..7 {
        claims.push(verify_h21_role(&context, &key, &packet.commitment, role, &proofs[role])?);
    }
    let verified = VerifiedClaims { claims:claims.try_into().map_err(|_| "H21 atomic seven-claim count")? };
    let corpus_id: [u8;32] = Blake2b::<U32>::digest(&packet.statement_bytes).into();
    let (verified, ()) = finish_verified_seven(verified, |verified| {
        let statement = opening_batch::Statement { log_n:41, setup_id:*key.id(),
            commitment:pcs::decode_commitment(&packet.commitment)?, corpus_id:Some(corpus_id),
            claims:verified.claims.clone() };
        opening_batch::verify_admitted(&statement, &key, &common).map(|_| ())
    })?;
    // Sole H21 result construction, strictly after real common PCS success.
    Ok(VerifiedH21StructuralPacket { statement:packet.statement, packet:bytes.to_vec(),
        claims:verified.claims, key_id:*key.id(), corpus_id })
}

#[path="h21_atomic_seven_tests.rs"]
mod tests;

impl H21StructuralDiagnosticContext<'_> {
    /// Complete-role diagnostic candidate over arbitrary locked witness bytes.
    /// Neither requested identity nor this GKR output establishes PCS/history.
    pub(crate) fn prove_role1_untrusted_candidate(&self,key_bytes:&[u8],commitment:&[u8],
        candidate:&packed::UntrustedH21CandidateFile,budget:sparse_stream_roster::H21Role1Budget)
        ->Result<(Vec<u8>,InputClaim),String> {
        with_matching_h21_requested_identity(candidate.requested_logical_public_identity(),self.native_witness_identity,|| {
            let key=verifier_key::admit(41,key_bytes)?;
            require_h21_role0_diagnostic_key(&key)?;
            let c=pcs::decode_commitment(commitment)?;
            if pcs::encode_commitment(&c)?!=commitment {return Err("H21 role1 candidate noncanonical commitment".into());}
            let mut t=fresh_h21_role_prefix(self.public_bytes,&key,commitment,1)?;
            let (proof,claim,_stats)=sparse_stream_roster::prove_h21_role1_candidate(
                &self.roster,candidate,&budget,&mut t,self.public_bytes,key_bytes,commitment,|t|bind_h21_role(self,1,t),
                |r,u,v|self.coefficients(1,r,u,v))?;
            let bytes=gkr::encode_proof(&proof)?;
            if bytes.len()!=9_280 || claim.point.len()!=41 {return Err("H21 role1 candidate proof extent".into());}
            Ok((bytes,claim))
        })
    }
}

#[path="h21_role1_edge_tests.rs"]
mod role1_edge_tests;

fn admit_h21_role5_public_inputs(requested:&[u8],expected:&[u8],key_bytes:&[u8],commitment:&[u8])
    ->Result<verifier_key::AdmittedVerifierKey,String>{
    with_matching_h21_requested_identity(requested,expected,|| {
        let key=verifier_key::admit(41,key_bytes)?;
        require_h21_role0_diagnostic_key(&key)?;
        let c=pcs::decode_commitment(commitment)?;
        if pcs::encode_commitment(&c)?!=commitment{return Err("H21 role5 candidate noncanonical commitment".into());}
        Ok(key)
    })
}
impl H21StructuralDiagnosticContext<'_> {
    /// Unverified role5 GKR only, over the same held arbitrary witness. The
    /// common PCS and the other predicates remain independent obligations.
    pub(crate) fn prove_role5_untrusted_candidate(&self,key_bytes:&[u8],commitment:&[u8],
        candidate:&packed::UntrustedH21CandidateFile,budget:crate::segment_adjacency::linear_for_test::H21Role5Budget)
        ->Result<(Vec<u8>,InputClaim),String>{
        use crate::segment_adjacency::linear_for_test as linear;
        let key=admit_h21_role5_public_inputs(candidate.requested_logical_public_identity(),self.native_witness_identity,key_bytes,commitment)?;
        let d=self.layouts.adjacency.h21_role5_descriptor_for_test()?;
        d.require_h21_layout(self.layouts.adjacency)?;
        linear::h21_role5_resource_preflight(&d,candidate.untrusted_polynomial().input_len(),budget)?;
        let mut prepared=fresh_h21_role_prefix(self.public_bytes,&key,commitment,5)?;
        bind_h21_role(self,5,&mut prepared)?;
        let (proof,claim,_stats,_support)=linear::prove_h21_role5_candidate(&d,candidate,budget,&prepared)?;
        let bytes=gkr::encode_proof(&proof)?;
        if bytes.len()!=9_280||claim.point.len()!=41{return Err("H21 role5 candidate proof extent".into());}
        Ok((bytes,claim))
    }
}

#[path="h21_role5_linear_tests.rs"]
mod role5_linear_tests;

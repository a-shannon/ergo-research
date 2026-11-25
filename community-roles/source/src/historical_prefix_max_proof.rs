//! Bounded N3 MAX/common-commitment experiment; no production admission path.
use crate::{
    core_pool_boolean,
    max_header_adapter::MaxHeaderAdapter,
    packed_owner_assembly::{NativeOwnerProducer, NativePrefix, validate_native_max_row_for_history_test},
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
use std::{fs::OpenOptions, io::{Read, Write}, path::Path, time::Instant};

const PROFILE: &[u8] = b"historical-prefix-n3-common-seven-daa-max-v1";
const COMPOSITION: &[u8] = b"complete-height-four-daa-lanes-and-suffix-max-v1";
const INPUT_BITS: [usize; 7] = [22, 22, 22, 15, 22, 22, 22];
const ROW_BITS: [usize; 7] = [23, 21, 21, 16, 22, 11, 14];
const DAA_ROW_BASE: usize = 1 << 21;
const MAX_ROW_BASE: usize = 1 << 13;
const MAX_OWNER_TERMS: [usize; 4] = [2242, 2690, 1121, 673];
const OLD_COMPOSITE_TERMS: usize = 329122;
const COMPOSITE_TERMS: usize = OLD_COMPOSITE_TERMS + 6726;
const ROLES: [&[u8]; 7] = [
    b"corepool11",
    b"retained-header",
    b"worktree-roster",
    b"point-membership",
    b"height-work-daa-and-suffix-max-v1",
    b"header-id",
    b"metadata-order",
];

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
        if headers != 3 {
            return Err("MAX common prefix requires exactly N3".into());
        }
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
            _ => Err("MAX common prefix requires exactly N3".into()),
        }
    }

    fn bytes(&self) -> Result<Vec<u8>, String> {
        let mut bytes = self.profile()?.to_vec();
        bytes.extend(crate::header_order::MAINNET_GENESIS);
        bytes.extend([0u8; 32]); // Parent anchor of the fixed genesis.
        for n in [self.headers, 4, 2, 22] {
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
            bytes.extend((INPUT_BITS[i] as u64).to_le_bytes());
            bytes.extend((ROW_BITS[i] as u64).to_le_bytes());
        }
        Ok(bytes)
    }
}

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

/// Constructed solely from the expected public statement and code-owned layouts.
/// No private witness or producer-supplied claims enter the consumer.
struct Consumer {
    expected: Public,
    parent: WorkTreeHistoryPlan,
    adjacency: HeaderAdjacencyLayout,
    metadata: HeaderMetadataOrderLayout,
    points: point_membership::Compiled,
    base: Transcript,
    corpus_id: [u8; 32],
}
impl Consumer {
    fn new(public: &Public) -> Result<Self, String> {
        Self::new_with_profile_domain(public, public.profile()?)
    }

    // Private counterfactual verifier fixture; normative callers use new.
    // The canonical public bytes/corpus remain unchanged by this override.
    fn new_with_profile_domain(public: &Public, profile: &'static [u8]) -> Result<Self, String> {
        public.profile()?;
        let parent = WorkTreeHistoryPlan::compile(public.headers, 2, public.root, public.total)?;
        let adjacency = HeaderAdjacencyLayout::compile(public.headers, 2, [0; 32], public.tip)?;
        let metadata = HeaderMetadataOrderLayout::compile(public.headers, 2, public.tip_time)?;
        let points = point_membership::build()?;
        if points.circuit.input_len != 8192
            || points.circuit.row_count != 16384
            || points.circuit.terms.len() != 288158
        {
            return Err("point role geometry drift".into());
        }
        let public_bytes = public.bytes()?;
        let corpus_id = Blake2b::<U32>::digest(&public_bytes).into();
        let mut base = Transcript::new(profile);
        base.append_bytes(b"public-statement-and-roster", &public_bytes);
        parent.bind(&mut base);
        adjacency.bind(&mut base);
        metadata.bind(&mut base);
        base.append_bytes(
            b"point-template",
            layout::hash_terms(&points.circuit.terms).as_bytes(),
        );
        Ok(Self {
            expected: public.clone(),
            parent,
            adjacency,
            metadata,
            points,
            base,
            corpus_id,
        })
    }
}

/// Both relations borrow the same consumer-owned history. Their construction
/// and binding precede challenges and occur once per top-level operation.
struct ProofContext<'a> {
    consumer: &'a Consumer,
    height: HeightWork<'a>,
    adapter: MaxHeaderAdapter<'a>,
    composition: &'static [u8],
    role4_domain: &'static [u8],
    base: Transcript,
}
impl<'a> ProofContext<'a> {
    fn new(consumer: &'a Consumer) -> Result<Self, String> {
        Self::new_with_domains(consumer, COMPOSITION, ROLES[4])
    }

    // Immutable overrides are selected by tests, never by packet metadata.
    fn new_with_domains(consumer: &'a Consumer, composition: &'static [u8],
        role4_domain: &'static [u8]) -> Result<Self, String> {
        let height = HeightWork::new(&consumer.parent)?;
        let adapter = MaxHeaderAdapter::compile(&consumer.parent)?;
        if adapter.roster().input_log() != 22 || adapter.roster().row_log() != 21
            || adapter.roster().slot_log() != 2 || adapter.max().input_log() != 22
            || adapter.max().row_log() != 13 || adapter.max().row_count() != 8192
            || adapter.max().term_count() != 6726 {
            return Err("MAX common fixed dimensions rejected".into());
        }
        let mut context = Self {
            consumer,
            height,
            adapter,
            composition,
            role4_domain,
            base: consumer.base.clone(),
        };
        let mut base = consumer.base.clone();
        context.bind_composite(&mut base);
        context.base = base;
        Ok(context)
    }

    fn bind_composite(&self, t: &mut Transcript) {
        t.append_bytes(
            b"height-daa-max-composition",
            self.composition,
        );
        for dimension in [
            2u64,
            self.consumer.parent.headers(),
            22,
            22,
            8,
            21,
            0,
            1,
            13,
        ] {
            t.append_u64(b"height-daa-fixed-dimension", dimension);
        }
        t.append_u64(b"height-daa-row-base", DAA_ROW_BASE as u64);
        t.append_u64(b"height-daa-total-terms", self.term_count() as u64);
        t.append_u64(b"composition-version", 1);
        t.append_u64(b"max-row-base", MAX_ROW_BASE as u64);
        t.append_u64(b"max-row-bits", 13);
        t.append_u64(b"composite-input-bits", 22);
        t.append_u64(b"composite-row-bits", 22);
        t.append_u64(b"old-height-daa-terms", OLD_COMPOSITE_TERMS as u64);
        t.append_u64(b"height-term-count", 769);
        t.append_u64(b"active-owner-end", 2);
        t.append_u64(b"terminal-owner", 2);
        t.append_u64(b"padding-owner-start", 3);
        for (owner, count) in MAX_OWNER_TERMS.into_iter().enumerate() {
            t.append_u64(b"max-census-owner", owner as u64);
            t.append_u64(b"max-census-terms", count as u64);
        }
        self.height.bind(t);
        self.adapter.bind(t);
    }

    fn term_count(&self) -> usize {
        COMPOSITE_TERMS
    }

    fn composite_coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
        if r.len() != 22 || u.len() != 22 || v.len() != 22 {
            return Err("common height/DAA point dimensions rejected".into());
        }
        let height = self.height.coefficients(&r[..8], u, v)?;
        let daa = self.adapter.roster().coefficients(&r[..21], u, v)?;
        let max = self.adapter.max().coefficients(&r[..13], u, v)?;
        let height_mask = r[8..21]
            .iter()
            .fold(Fr::one() - r[21], |a, x| a * (Fr::one() - x));
        let max_mask = r[14..].iter().fold(r[13], |a, x| a * (Fr::one() - x));
        Ok(std::array::from_fn(|i| {
            height_mask * height[i] + r[21] * daa[i] + max_mask * max[i]
        }))
    }

    fn composite_circuit(&self) -> Result<Circuit, String> {
        let height = self.height.circuit()?;
        if height.input_len != 1 << 22 || height.row_count != 256 || height.terms.len() != 769 {
            return Err("common height geometry drift".into());
        }
        let mut terms = Vec::with_capacity(self.term_count());
        terms.extend(height.terms);
        let numeric = [0usize, 225, 448, 0];
        for (owner, expected_numeric) in numeric.into_iter().enumerate() {
            let counts = self.adapter.roster().visit_owner_terms(owner as u64, |mut term| {
                term.row = term
                    .row
                    .checked_add(DAA_ROW_BASE)
                    .ok_or("common DAA row overflow")?;
                if term.row >= 1 << 22 || term.gate.left >= 1 << 22 || term.gate.right >= 1 << 22 {
                    return Err("common DAA term escapes fixed domain".into());
                }
                terms.push(term);
                Ok(())
            })?;
            if counts.lanes != [0, 0, expected_numeric, 81920] {
                return Err("common DAA fixed owner census drift".into());
            }
        }
        if terms.len() != OLD_COMPOSITE_TERMS {
            return Err("preserved height/DAA complete term count drift".into());
        }
        for (owner, expected_count) in MAX_OWNER_TERMS.into_iter().enumerate() {
            let count = self.adapter.max().emit_owner(owner, |mut term| {
                if term.row >= 8192 {
                    return Err("MAX original row outside fixed domain".into());
                }
                term.row = term.row.checked_add(MAX_ROW_BASE).ok_or("MAX composite row overflow")?;
                if term.row >= 16384 || term.gate.left >= 1 << 22 || term.gate.right >= 1 << 22 {
                    return Err("MAX composite term escapes fixed domain".into());
                }
                terms.push(term);
                Ok(())
            })?;
            if count != expected_count {
                return Err("MAX complete owner term count drift".into());
            }
        }
        if terms.len() != COMPOSITE_TERMS {
            return Err("MAX composite complete term count drift".into());
        }
        let circuit = Circuit {
            input_len: 1 << 22,
            row_count: 1 << 22,
            terms,
        };
        sparse::validate(&circuit, 0).map_err(|e| format!("MAX composite admission: {e:?}"))?;
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
        t.append_bytes(b"role-domain", if role == 4 { self.role4_domain } else { ROLES[role] });
        t
    }

    fn bind_role(&self, role: usize, t: &mut Transcript) {
        match role {
            0 => self.consumer.parent.core_pool().bind(t),
            1 => self.adapter.bind(t),
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
        match role {
            0 => self
                .consumer
                .parent
                .core_pool()
                .coefficients(r, u, v)
                .map_err(|e| e.to_string()),
            1 => self.adapter.header_coefficients(r, u, v),
            2 => work_tree_wiring::full_roster_coefficients(
                self.consumer.parent.topology(),
                fixed::engine()?,
                self.consumer.parent.fixed_profile(),
                self.consumer.parent.leaf_boundary(),
                self.consumer.parent.work_boundary(),
                r,
                u,
                v,
            ),
            4 => self.composite_coefficients(r, u, v),
            5 => self.consumer.adjacency.coefficients(r, u, v),
            6 => self.consumer.metadata.coefficients(r, u, v),
            _ => Err("role has no analytic adapter".into()),
        }
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
            input_len: 1 << 22,
            row_count: 1 << ROW_BITS[role],
            terms,
        })
    }

    fn verify_roles(
        &self,
        artifact: &Artifact,
        key: &verifier_key::AdmittedVerifierKey,
    ) -> Result<[Claim; 7], Reject> {
        if key.log_n() != 22
            || artifact.roles.len() != 7
            || artifact
                .roles
                .iter()
                .enumerate()
                .any(|(i, p)| p.role != i || p.bytes.len() != (7 * INPUT_BITS[i] + 3) * 32)
        {
            return Err(Reject::Shape);
        }
        pcs::decode_commitment(&artifact.commitment).map_err(|_| Reject::Commitment)?;
        let mut claims = Vec::with_capacity(7);
        for (i, role) in artifact.roles.iter().enumerate() {
            let proof = gkr::decode_dimensions(&[INPUT_BITS[i]], &role.bytes)
                .map_err(|_| Reject::Role(i))?;
            let mut t = self.transcript(i, key, &artifact.commitment);
            let terminal = if i == 3 {
                sparse::verify(&self.consumer.points.circuit, 2, &proof, &mut t)
            } else {
                gkr::verify_with_wiring(
                    &[22],
                    1 << ROW_BITS[i],
                    &proof,
                    &mut t,
                    |t| self.bind_role(i, t),
                    |_, r, u, v| {
                        self.coefficients(i, r, u, v)
                            .map_err(|_| GkrError::InvalidWireIndex)
                    },
                )
            }
            .map_err(|_| Reject::Role(i))?;
            let point = if i == 3 {
                segment_points::embed(3, 2, &terminal.point).map_err(|_| Reject::Role(i))?
            } else {
                terminal.point
            };
            if point.len() != 22 {
                return Err(Reject::Role(i));
            }
            claims.push(Claim {
                point,
                value: terminal.value,
            });
        }
        claims.try_into().map_err(|_| Reject::Shape)
    }

    fn verify(
        &self,
        artifact: &Artifact,
        key: &verifier_key::AdmittedVerifierKey,
    ) -> Result<[Claim; 7], Reject> {
        let claims = self.verify_roles(artifact, key)?;
        let statement = self.consumer.statement(artifact, key, claims.clone())?;
        let proof =
            opening_batch::decode_proof(&artifact.batch, 22).map_err(|_| Reject::Linkage)?;
        opening_batch::verify_admitted(&statement, key, &proof).map_err(|_| Reject::Linkage)?;
        Ok(claims)
    }
}

impl Consumer {
    fn statement(
        &self,
        artifact: &Artifact,
        key: &verifier_key::AdmittedVerifierKey,
        claims: [Claim; 7],
    ) -> Result<opening_batch::Statement, Reject> {
        Ok(opening_batch::Statement {
            log_n: 22,
            setup_id: *key.id(),
            commitment: pcs::decode_commitment(&artifact.commitment)
                .map_err(|_| Reject::Commitment)?,
            corpus_id: Some(self.corpus_id),
            claims,
        })
    }

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

fn read_slot(source: &PackedFile, owner: usize) -> Result<Vec<Fr>, String> {
    if owner >= 4 || source.input_len() != 1 << 22 {
        return Err("prefix packed dimensions".into());
    }
    let mut values = Vec::with_capacity(layout::WIDTH);
    for bank in 0..16 {
        values.extend(source.read_copy(layout::CORE, owner * 16 + bank)?);
    }
    Ok(values)
}
fn read_all(source: &PackedFile) -> Result<Vec<Fr>, String> {
    let mut values = Vec::with_capacity(1 << 22);
    for owner in 0..4 {
        values.extend(read_slot(source, owner)?);
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
fn packed_source(path: &Path, bytes: &[u8]) -> Result<PackedFile, String> {
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


// This helper is the sole native role5 producer, shared by the dispatch and its differential.
fn prove_native_adjacency_role(
    context: &ProofContext<'_>,
    source: &PackedFile,
    transcript: &mut Transcript,
) -> Result<crate::native_adjacency_stream::Produced, String> {
    crate::native_adjacency_stream::prove(
        &context.consumer.adjacency,
        source.input_len(),
        |owner| read_slot(source, owner),
        transcript,
    )
}

fn prove_role(
    context: &ProofContext<'_>,
    source: &PackedFile,
    key: &verifier_key::AdmittedVerifierKey,
    commitment: &[u8],
    role: usize,
) -> Result<(GkrProof, InputClaim), String> {
    let mut t = context.transcript(role, key, commitment);
    match role {
        0 => core_pool_boolean::prove_with_copy_bits_for_test(
            &fixed::engine()?.core,
            4,
            &layout::CORE_OFFSETS
                .iter()
                .map(|offset| offset / layout::CORE)
                .collect::<Vec<_>>(),
            2,
            |owner| read_slot(source, owner),
            &mut t,
            |t| context.bind_role(0, t),
            |r, u, v| context.coefficients(0, r, u, v),
        ),
        1 => sparse_stream_roster::prove(
            20,
            2,
            19,
            0,
            &[19],
            |owner| read_slot(source, owner),
            &mut t,
            |t| context.bind_role(1, t),
            |owner, sink| {
                let counts = context.adapter.visit_header_terms(owner, |mut term| {
                    let ib = owner * layout::WIDTH;
                    let rb = owner * (1 << 19);
                    if !(ib..ib + layout::WIDTH).contains(&term.gate.left)
                        || !(ib..ib + layout::WIDTH).contains(&term.gate.right)
                        || !(rb..rb + (1 << 19)).contains(&term.row)
                    {
                        return Err("retained header escapes owner".into());
                    }
                    term.row -= rb;
                    term.gate.left -= ib;
                    term.gate.right -= ib;
                    sink(term)
                })?;
                let omitted_max = if owner < 2 { 673 } else { 0 };
                if counts.emitted != 396561 - omitted_max || counts.omitted_max != omitted_max
                    || counts.parent.omitted_mature_a4 != 0
                    || counts.parent.omitted_short_a4 != 0
                    || counts.parent.omitted_worktree != 78194
                {
                    return Err("retained header count drift".into());
                }
                Ok(())
            },
            |r, u, v| context.coefficients(1, r, u, v),
        ),
        3 => sparse_stream_boolean::prove(
            &context.consumer.points.circuit,
            2,
            |owner| {
                segment_points::load_copy(source, 3, 4, owner)
                    .map_err(|_| GkrError::InvalidInputWidth)
            },
            &mut t,
        )
        .map_err(|e| format!("{e:?}")),
        5 => {
            let produced = prove_native_adjacency_role(context, source, &mut t)?;
            Ok((produced.proof, produced.claim))
        }
        2 | 4 | 6 => {
            let circuit = context.small_circuit(role)?;
            let input = read_all(source)?;
            sparse::prove_with_binding(&circuit, &input, 0, &mut t, |t| context.bind_role(role, t))
                .map_err(|e| e.to_string())
        }
        _ => Err("unknown fixed role".into()),
    }
}

fn check_input_identity(public: &Public, input: &NativePrefix) -> Result<(), String> {
    if public.headers != 3 || input.header_count() != 3 {
        return Err("MAX common input requires exactly three headers".into());
    }
    if ergo_header_core::blake2b256(input.raw(1)?) != crate::header_order::MAINNET_GENESIS
        || input.header(1)?.parent_id != [0; 32]
        || input.root() != public.root || input.total_be28() != public.total
        || ergo_header_core::blake2b256(input.raw(3)?) != public.tip
        || input.timestamp(3)? != public.tip_time {
        return Err("MAX common native input differs from expected public".into());
    }
    Ok(())
}

fn native_input(public: &Public) -> Result<NativePrefix, String> {
    if public.headers != 3 {
        return Err("MAX common input requires exactly three headers".into());
    }
    let retained = witness::retained_headers_n(3)?;
    if retained.len() != 3 {
        return Err("MAX common retained RAW count".into());
    }
    let raws: Vec<Vec<u8>> = retained.iter().map(|h| h.encode()
        .map_err(|e| format!("MAX common RAW encode: {e:?}"))).collect::<Result<_, _>>()?;
    let input = NativePrefix::from_raw_iter(3, raws.into_iter().map(Ok))?;
    check_input_identity(public, &input)?;
    Ok(input)
}

fn native_packed_source(path: &Path, context: &ProofContext<'_>, input: &NativePrefix)
    -> Result<PackedFile, String> {
    // Input and adapter admission precede the first output operation.
    check_input_identity(&context.consumer.expected, input)?;
    let producer = NativeOwnerProducer::new_for_max_history(&context.consumer.parent, input, &context.adapter)?;
    let mut writer = PackedFileWriter::create_new(path, 22)?;
    for owner in 0..4 {
        let row = producer.produce(owner)?;
        validate_native_max_row_for_history_test(&context.adapter, input, &row)?;
        if row.owner() != owner || row.packed_bytes().len() != layout::WIDTH / 8 {
            return Err("MAX common native row framing".into());
        }
        writer.write_bytes(row.packed_bytes())?;
    }
    writer.finish()
}

fn check_setup_identity(id: [u8; 32], key: &verifier_key::AdmittedVerifierKey) -> Result<(), String> {
    if id != *key.id() { return Err("setup differs from admitted key".into()); }
    Ok(())
}

const LEGACY_FILES: [(&str, usize, &str); 10] = [
    ("commitment.bin",384,"548739B0A65B98114F397C995C441AE499E23FD9E51BC1724E9AB69DDB5B9D94"),
    ("openings.bin",31581,"7236C31213DBCBE8A1810A3AE58ED9A26DDEA7F2096D9D960B78384A4541B950"),
    ("role-0.gkr",5024,"0AB82346CFB4ABF97B1630BB7B2EB4B5858FCBCEFB99D69118007F6BCD381ABC"),
    ("role-1.gkr",5024,"4D3D35358994D222FB3B9DE595379BA63004D77DDE4A3965C6D51082029BED97"),
    ("role-2.gkr",5024,"00504A78B600860B54DC359DB1A461938167E994B6BA6F6707E602A8A52B5152"),
    ("role-3.gkr",3456,"53845AD2311D54577B66DE92C94A8EC22F2B1BFC0EBAA90B52E5F0D52CF8E6A6"),
    ("role-4.gkr",5024,"0F6C9280BEF8780F944510B62D5CDD1DCEED2950976B9371D9145D0EDC2746D1"),
    ("role-5.gkr",5024,"2472F8FB16E65705DDBEA2D5F0EE6520E607CD993AC26AED4BF7865695C6FC7B"),
    ("role-6.gkr",5024,"99435565C4D1F054805D9F12993BB326F9FAC61ACD5D018D8DCFDAD21CF65219"),
    ("statement.bin",552,"C6B5EE7DA04436B7A97A8A9DA145A41FB12807FB6853F46C01B75ECFDDCEAC82"),
];

fn legacy_statement(public: &Public) -> Result<Vec<u8>, String> {
    public.profile()?; // Same exact native N3 fields, separate historical profile.
    let mut bytes = b"historical-prefix-n3-common-seven-c3-v1".to_vec();
    bytes.extend(crate::header_order::MAINNET_GENESIS);
    bytes.extend([0u8;32]);
    for n in [public.headers,4,2,22] { bytes.extend(n.to_le_bytes()); }
    bytes.extend(public.root); bytes.extend(public.total); bytes.extend(public.tip);
    bytes.extend(public.tip_time.to_le_bytes());
    for i in 0..7 {
        let role = if i==4 { b"height-numeric".as_slice() } else { ROLES[i] };
        let row_bits = if i==4 { 8 } else { ROW_BITS[i] };
        bytes.extend((i as u64).to_le_bytes());
        bytes.extend((role.len() as u64).to_le_bytes()); bytes.extend(role);
        bytes.extend((INPUT_BITS[i] as u64).to_le_bytes());
        bytes.extend((row_bits as u64).to_le_bytes());
    }
    Ok(bytes)
}

fn legacy_artifact(public: &Public) -> Result<Artifact,String> {
    let dir=std::env::var_os("NIPOPOW_MAX_LEGACY_DIR").ok_or("missing exact legacy public fixture directory")?;
    let dir=Path::new(&dir);
    let mut names=std::fs::read_dir(dir).map_err(|e|e.to_string())?
        .map(|e|e.map_err(|e|e.to_string()).and_then(|e|e.file_name().into_string()
            .map_err(|_|"legacy fixture name encoding".to_string())))
        .collect::<Result<Vec<_>,_>>()?;
    names.sort_unstable();
    let mut expected:Vec<_>=LEGACY_FILES.iter().map(|(n,_,_)|n.to_string()).collect();
    expected.sort_unstable();
    if names!=expected { return Err("legacy fixture closed ten-file set".into()); }
    let mut files=std::collections::BTreeMap::new();
    for (name,length,digest) in LEGACY_FILES {
        let path=dir.join(name);
        let metadata=std::fs::symlink_metadata(&path).map_err(|e|e.to_string())?;
        if !metadata.is_file() || metadata.len()!=length as u64 {
            return Err("legacy fixture file framing".into());
        }
        let file=std::fs::File::open(&path).map_err(|e|e.to_string())?;
        let mut bytes=Vec::with_capacity(length+1);
        file.take((length+1) as u64).read_to_end(&mut bytes).map_err(|e|e.to_string())?;
        let actual=Blake2b::<U32>::digest(&bytes).iter().map(|b|format!("{b:02X}"))
            .collect::<String>();
        if bytes.len()!=length || actual!=digest {
            return Err("legacy fixture byte identity".into());
        }
        files.insert(name,bytes);
    }
    if files.remove("statement.bin").ok_or("legacy statement missing")? != legacy_statement(public)? {
        return Err("legacy statement differs from independent native N3 expectation".into());
    }
    let mut roles=Vec::new();
    for role in 0..7 {
        let name=format!("role-{role}.gkr");
        let bytes=files.remove(name.as_str()).ok_or("legacy role missing")?;
        gkr::decode_dimensions(&[INPUT_BITS[role]],&bytes)?;
        roles.push(RoleProof{role,bytes});
    }
    let commitment=files.remove("commitment.bin").ok_or("legacy commitment missing")?;
    pcs::decode_commitment(&commitment)?;
    let batch=files.remove("openings.bin").ok_or("legacy openings missing")?;
    opening_batch::decode_proof(&batch,22)?;
    if !files.is_empty() { return Err("unconsumed legacy public file".into()); }
    Ok(Artifact{commitment,roles,batch})
}

fn binding_negatives(public: &Public, consumer: &Consumer, context: &ProofContext<'_>,
    artifact: &Artifact, key: &verifier_key::AdmittedVerifierKey,
    key_bytes: &[u8], statement: &opening_batch::Statement, batch: &opening_batch::Proof)
    -> Result<(),String> {
    // Each immutable consumer variation changes one label, not the artifact.
    let profile=Consumer::new_with_profile_domain(public,b"historical-prefix-max-wrong-outer-v1")?;
    assert_eq!(profile.corpus_id,consumer.corpus_id);
    assert_eq!(profile.verify(artifact,key),Err(Reject::Role(0)));
    let composition=ProofContext::new_with_domains(consumer,
        b"complete-height-four-daa-lanes-and-suffix-max-wrong-v1",ROLES[4])?;
    assert_eq!(composition.verify(artifact,key),Err(Reject::Role(0)));
    let role=ProofContext::new_with_domains(consumer,COMPOSITION,b"height-work-daa-and-suffix-max-wrong-v1")?;
    assert_eq!(role.verify(artifact,key),Err(Reject::Role(4)));
    let smaller=verifier_key::admit(18,include_bytes!("../fixtures/verifier-keys-v1/log18.vk"))?;
    assert_eq!(context.verify(artifact,&smaller),Err(Reject::Shape));
    let mut wrong_id=*key.id(); wrong_id[0]^=1;
    let wrong_key=verifier_key::admit_generated_test_key(22,key_bytes,wrong_id)?;
    assert_eq!(wrong_key.log_n(),key.log_n());
    assert_eq!(context.verify(artifact,&wrong_key),Err(Reject::Role(0)));
    for field in 0..2 {
        let mut wrong=statement.clone();
        if field==0 {wrong.setup_id[0]^=1;} else {wrong.log_n=23;}
        assert_eq!(opening_batch::verify_admitted(&wrong,key,batch).err(),
            Some("opening-batch expected statement/verifier-key/dimension rejected".into()));
    }
    Ok(())
}

fn genuine_wiring_negatives(context: &ProofContext<'_>, source: &PackedFile,
    key: &verifier_key::AdmittedVerifierKey, artifact: &Artifact, dir: &Path) -> Result<(), String> {
    let r = composition_tests::point(22, 3);
    let u = composition_tests::point(22, 43);
    let v = composition_tests::point(22, 97);
    let mut alternate = context.composite_circuit()?;
    let zero_start = MAX_ROW_BASE + 2 * 2048;
    alternate.terms.retain(|t| !(zero_start..zero_start+673).contains(&t.row));
    if alternate.terms.len() != COMPOSITE_TERMS-673
        || composition_tests::literal(&alternate.terms, &r, &u, &v)
            == context.composite_coefficients(&r, &u, &v)? {
        return Err("isolated missing terminal MAX wiring not distinguished".into());
    }
    let shape = sparse::validate(&alternate, 0).map_err(|e| format!("{e:?}"))?;
    let input = read_all(source)?;
    let mut t = context.transcript(4, key, &artifact.commitment);
    let (proof, terminal) = sparse::prove_with_binding(&alternate, &input, 0, &mut t,
        |t| context.bind_role(4, t)).map_err(|e| e.to_string())?;
    drop(input);
    let mut t = context.transcript(4, key, &artifact.commitment);
    let accepted = gkr::verify_with_wiring(&[22], 1 << 22, &proof, &mut t,
        |t| context.bind_role(4, t), |_, r, u, v| sparse::wiring(&alternate, &shape, r, u, v))
        .map_err(|e| format!("alternate MAX positive: {e:?}"))?;
    assert_eq!(accepted, terminal);
    let mut mutant = artifact.clone();
    mutant.roles[4].bytes = gkr::encode_proof(&proof)?;
    write_new(&dir.join("genuine-omitted-terminal-max.gkr"), &mutant.roles[4].bytes)?;
    assert_eq!(context.verify(&mutant, key), Err(Reject::Role(4)));
    drop(alternate);

    // Only owner0's immediate left neighbor is additionally released.
    let neighbor = Term { row:356631, gate:crate::gkr::Gate {
        left:999423, right:0, c0:Fr::zero(), c1:Fr::one(), c2:Fr::zero(), c3:Fr::zero() } };
    let header_r = &r[..21];
    assert!(!composition_tests::literal(std::slice::from_ref(&neighbor), header_r, &u, &v)[1].is_zero());
    let mut t = context.transcript(1, key, &artifact.commitment);
    let (proof, terminal) = sparse_stream_roster::prove(20,2,19,0,&[19],
        |owner| read_slot(source, owner), &mut t, |t| context.bind_role(1,t),
        |owner,sink| {
            let ib=owner*layout::WIDTH; let rb=owner*(1 << 19); let mut omitted=0;
            let counts=context.adapter.visit_header_terms(owner,|mut term| {
                if owner==0 && term==neighbor { omitted+=1; return Ok(()); }
                if !(ib..ib+layout::WIDTH).contains(&term.gate.left)
                    || !(ib..ib+layout::WIDTH).contains(&term.gate.right)
                    || !(rb..rb+(1 << 19)).contains(&term.row) {
                    return Err("alternate header escapes owner".into());
                }
                term.row-=rb;term.gate.left-=ib;term.gate.right-=ib;sink(term)
            })?;
            if omitted!=usize::from(owner==0) || counts.emitted!=396561-if owner<2 {673}else{0} {
                return Err("alternate single neighbor release census".into());
            }
            Ok(())
        }, |r,u,v| {
            let mut out=context.coefficients(1,r,u,v)?;
            let delta=composition_tests::literal(std::slice::from_ref(&neighbor),r,u,v);
            for i in 0..4 {out[i]-=delta[i];} Ok(out)
        })?;
    let mut t = context.transcript(1,key,&artifact.commitment);
    let accepted=gkr::verify_with_wiring(&[22],1 << 21,&proof,&mut t,
        |t| context.bind_role(1,t), |_,r,u,v| {
            let mut out=context.coefficients(1,r,u,v).map_err(|_| GkrError::InvalidWireIndex)?;
            let delta=composition_tests::literal(std::slice::from_ref(&neighbor),r,u,v);
            for i in 0..4 {out[i]-=delta[i];} Ok(out)
        }).map_err(|e| format!("alternate header positive: {e:?}"))?;
    assert_eq!(accepted,terminal);
    let mut mutant=artifact.clone();mutant.roles[1].bytes=gkr::encode_proof(&proof)?;
    write_new(&dir.join("genuine-extra-neighbor-release.gkr"),&mutant.roles[1].bytes)?;
    assert_eq!(context.verify(&mutant,key),Err(Reject::Role(1)));
    Ok(())
}

fn run_common(headers: u64) -> Result<(), String> {
    let dir =
        std::env::var_os("NIPOPOW_MAX_COMMON_DIR").ok_or("missing fresh MAX common artifact directory")?;
    let dir = Path::new(&dir);
    if !dir.is_dir() {
        return Err("MAX common runner must provide fresh owned directory".into());
    }
    let started = Instant::now();
    let public = Public::native(headers)?;
    let input = native_input(&public)?;
    let consumer = Consumer::new(&public)?;
    let context = ProofContext::new(&consumer)?;
    let key_bytes=include_bytes!("../fixtures/verifier-keys-v1/log22.vk");
    let key=verifier_key::admit(22,key_bytes)?;
    // Retained genuine old packet, exact public bytes and historical positive;
    // reject it before creating a new packed witness or generating setup.
    let legacy=legacy_artifact(&public)?;
    assert_eq!(context.verify(&legacy,&key),Err(Reject::Role(0)));
    check_setup_identity(*key.id(),&key)?;
    let mut wrong_id=*key.id(); wrong_id[0]^=1;
    assert_eq!(check_setup_identity(wrong_id,&key),Err("setup differs from admitted key".into()));
    phase("legacy-and-setup-identity-guards",started);
    let started=Instant::now();
    let source = native_packed_source(&dir.join("witness.bits"), &context, &input)?;
    phase("native-packed-witness", started);
    let started = Instant::now();
    write_new(&dir.join("statement.bin"), &public.bytes()?)?;
    phase("layouts", started);
    let started = Instant::now();
    let setup = pcs::generate_setup(22)?;
    check_setup_identity(setup.id,&key)?;
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
        if bytes.len() != (7 * INPUT_BITS[role] + 3) * 32 {
            return Err("GKR codec length drift".into());
        }
        write_new(&dir.join(format!("role-{role}.gkr")), &bytes)?;
        phase(&format!("encode-{role}"), started);
        let point = if role == 3 {
            let embedded = segment_points::embed(3, 2, &terminal.point)?;
            let mut local = Vec::with_capacity(1 << 15);
            for owner in 0..4 {
                local.extend(segment_points::load_copy(&source, 3, 4, owner)?);
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
    let statement = consumer
        .statement(&artifact, &key, derived.clone())
        .map_err(|e| format!("{e:?}"))?;
    let started = Instant::now();
    let (batch, _, _) = opening_batch::prove(&source, &committed, &setup, &statement)?;
    phase("batch-prove", started);
    let started = Instant::now();
    artifact.batch = opening_batch::encode_proof(&batch, 22)?;
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

    let started=Instant::now();
    binding_negatives(&public,&consumer,&context,&artifact,&key,key_bytes,&statement,&batch)?;
    phase("binding-domain-and-key-negatives",started);

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
    for field in 0..4 {
        let mut altered = public.clone();
        match field {0=>altered.root[0]^=1,1=>altered.total[27]^=1,
            2=>altered.tip[0]^=1,_=>altered.tip_time^=1}
        let changed = Consumer::new(&altered)?;
        assert_eq!(changed.verify(&artifact, &key), Err(Reject::Role(0)));
    }
    for invalid in [2, 4, 5] {
        let mut altered = public.clone();
        altered.headers = invalid;
        assert!(altered.bytes().is_err());
        assert!(Consumer::new(&altered).is_err());
    }
    phase("roster-and-statement-negatives", started);

    let started=Instant::now();
    genuine_wiring_negatives(&context,&source,&key,&artifact,dir)?;
    phase("genuine-wrong-wiring-negatives",started);

    let started = Instant::now();
    let mut bits = std::fs::read(dir.join("witness.bits")).map_err(|e| e.to_string())?;
    if bits.len() != (1 << 22) / 8 {
        return Err("MAX common retained packed frame extent".into());
    }
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
    mutant.batch = opening_batch::encode_proof(&wrong_batch, 22)?;
    write_new(&dir.join("reordered-valid-openings.bin"), &mutant.batch)?;
    assert_eq!(context.verify(&mutant, &key), Err(Reject::Linkage));
    phase("genuine-reordered-batch-negative", started);
    let started = Instant::now();
    let mut wrong_corpus = statement.clone();
    wrong_corpus.corpus_id = Some([0x58; 32]);
    assert_ne!(wrong_corpus.corpus_id, statement.corpus_id);
    assert_eq!(wrong_corpus.claims, statement.claims);
    let (wrong_batch, _, _) = opening_batch::prove(&source, &committed, &setup, &wrong_corpus)?;
    opening_batch::verify_admitted(&wrong_corpus, &key, &wrong_batch)?;
    let mut mutant = artifact.clone();
    mutant.batch = opening_batch::encode_proof(&wrong_batch, 22)?;
    assert_eq!(mutant.roles.iter().map(|p| &p.bytes).collect::<Vec<_>>(),
        artifact.roles.iter().map(|p| &p.bytes).collect::<Vec<_>>());
    write_new(&dir.join("wrong-corpus-valid-openings.bin"), &mutant.batch)?;
    assert_eq!(context.verify(&mutant, &key), Err(Reject::Linkage));
    phase("genuine-wrong-corpus-batch-negative", started);
    println!(
        "{}",
        serde_json::json!({"result":"PASS","headers":headers,"owners":4,"roles":7,
        "gkr_bytes":33600,"opening_bytes":artifact.batch.len(),"commitment_bytes":artifact.commitment.len(),
        "max_helpers":673,"max_active_owners":2,"composite_terms":COMPOSITE_TERMS,
        "binding_negative_cases":7,"setup_identity_negative_cases":1,
        "legacy_public_files":10,"legacy_public_bytes":66117,"legacy_rejected":true,
        "raw_hidden":false,"full_history":false,"production":false})
    );
    Ok(())
}

#[test]
#[ignore = "requires a fresh artifact directory and bounded proof runner"]
fn n3_max_roles_share_one_admitted_commitment_and_reject_substitution() {
    std::thread::Builder::new()
        .name("historical-prefix-max-common".into())
        .stack_size(32 * 1024 * 1024)
        .spawn(|| run_common(3).unwrap())
        .unwrap()
        .join()
        .unwrap();
}

#[cfg(test)]
mod composition_tests {
    use super::*;

    pub(super) fn point(bits: usize, seed: u64) -> Vec<Fr> {
        (0..bits).map(|i| Fr::from(seed + 17 * (i as u64 + 1))).collect()
    }

    // Literal equality weights; no 2^22-sized tables or private field witness.
    fn eq_index(p: &[Fr], index: usize) -> Fr {
        p.iter().enumerate().fold(Fr::one(), |a, (bit, x)|
            a * if (index >> bit) & 1 == 1 { *x } else { Fr::one() - x })
    }

    struct LiteralWeights {
        chunks: Vec<Vec<Fr>>,
        bits: usize,
    }
    impl LiteralWeights {
        fn new(p: &[Fr]) -> Self {
            // Each small table is computed by the independent scalar oracle.
            // At22 bits this stores576 fields, not a full2^22 table.
            let chunks = p.chunks(8).map(|chunk|
                (0..1usize << chunk.len()).map(|i| eq_index(chunk, i)).collect()).collect();
            Self { chunks, bits:p.len() }
        }
        fn at(&self, index: usize) -> Fr {
            assert_eq!(index >> self.bits, 0);
            self.chunks.iter().enumerate().fold(Fr::one(), |a, (chunk, table)|
                a * table[(index >> (chunk*8)) & (table.len()-1)])
        }
    }

    fn add_term(out: &mut [Fr; 4], term: &Term, r: &LiteralWeights,
        u: &LiteralWeights, v: &LiteralWeights) {
        let weight = r.at(term.row) * u.at(term.gate.left) * v.at(term.gate.right);
        for (i, c) in [term.gate.c0, term.gate.c1, term.gate.c2, term.gate.c3].into_iter().enumerate() {
            out[i] += weight * c;
        }
    }

    pub(super) fn literal(terms: &[Term], r: &[Fr], u: &[Fr], v: &[Fr]) -> [Fr; 4] {
        let mut out = [Fr::zero(); 4];
        let r=LiteralWeights::new(r);let u=LiteralWeights::new(u);let v=LiteralWeights::new(v);
        for term in terms { add_term(&mut out, term, &r, &u, &v); }
        out
    }

    #[test]
    fn exact_native_input_and_new_profile_before_outputs() {
        let public = Public::native(3).unwrap();
        let input = native_input(&public).unwrap();
        assert_eq!(input.header_count(), 3);
        assert_eq!(input.genuine_count(), 2);
        check_input_identity(&public, &input).unwrap();
        assert!(public.bytes().unwrap().starts_with(PROFILE));
        assert_ne!(PROFILE, b"historical-prefix-n3-common-seven-daa-v2");
        assert_eq!(ROLES[4], b"height-work-daa-and-suffix-max-v1");
        assert_eq!(INPUT_BITS, [22, 22, 22, 15, 22, 22, 22]);
        assert_eq!(ROW_BITS, [23, 21, 21, 16, 22, 11, 14]);
        let p=point(22,7);let weights=LiteralWeights::new(&p);
        assert_eq!(weights.chunks.iter().map(Vec::len).sum::<usize>(),576);
        for index in [0,1,255,256,8191,8192,999423,999424,1000096,1 << 20,(1 << 22)-1] {
            assert_eq!(weights.at(index),eq_index(&p,index));
        }
        for field in 0..4 {
            let mut wrong = public.clone();
            match field {
                0 => wrong.root[0] ^= 1,
                1 => wrong.total[27] ^= 1,
                2 => wrong.tip[0] ^= 1,
                _ => wrong.tip_time ^= 1,
            }
            assert_eq!(check_input_identity(&wrong, &input),
                Err("MAX common native input differs from expected public".into()));
        }
        for n in [2, 4, 5] {
            assert!(Public::native(n).is_err());
            let mut wrong = public.clone(); wrong.headers = n;
            assert!(wrong.bytes().is_err());
            assert!(Consumer::new(&wrong).is_err());
            assert_eq!(native_input(&wrong).unwrap_err(),
                "MAX common input requires exactly three headers");
        }
        let raws: Vec<_> = (1..=3).map(|h| input.raw(h).unwrap().to_vec()).collect();
        assert!(NativePrefix::from_raw_iter(3, raws[..2].iter().cloned().map(Ok)).is_err());
        let mut extra = raws.clone(); extra.push(raws[2].clone());
        assert!(NativePrefix::from_raw_iter(3, extra.into_iter().map(Ok)).is_err());
        // The fixed-count convenience wrapper is intentionally inapplicable.
        assert_eq!(NativePrefix::from_raw_headers(&raws).unwrap_err(),
            "native prefix requires exactly 3073 headers");
    }

    #[test]
    fn complete_composite_literal_geometry_and_nonboolean_wiring() {
        let public = Public::native(3).unwrap();
        let consumer = Consumer::new(&public).unwrap();
        let context = ProofContext::new(&consumer).unwrap();
        let circuit = context.composite_circuit().unwrap();
        assert_eq!((circuit.input_len, circuit.row_count, circuit.terms.len()),
            (1 << 22, 1 << 22, 335848));
        let height = context.height.circuit().unwrap();
        assert_eq!(height.terms.len(), 769);
        assert_eq!(&circuit.terms[..769], height.terms.as_slice());
        let mut old = height.terms;
        for (owner, numeric) in [0, 225, 448, 0].into_iter().enumerate() {
            let counts = context.adapter.roster().visit_owner_terms(owner as u64, |mut term| {
                assert!(term.row < 1 << 21);
                term.row += 1 << 21;
                old.push(term); Ok(())
            }).unwrap();
            assert_eq!(counts.lanes, [0, 0, numeric, 81920]);
        }
        assert_eq!(old.len(), 329122);
        assert_eq!(&circuit.terms[..329122], old.as_slice());
        let mut max = Vec::new();
        for (owner, expected) in [2242, 2690, 1121, 673].into_iter().enumerate() {
            let count = context.adapter.max().emit_owner(owner, |mut term| {
                assert!(term.row < 8192);
                term.row += 8192;
                max.push(term); Ok(())
            }).unwrap();
            assert_eq!(count, expected);
        }
        assert_eq!(max.len(), 6726);
        assert_eq!(&circuit.terms[329122..], max.as_slice());
        assert!(max.iter().all(|t| (8192..16384).contains(&t.row)));
        assert!(max.iter().any(|t| t.gate.left / layout::WIDTH != t.gate.right / layout::WIDTH));
        assert!(circuit.terms.iter().all(|t| t.row < 256 || t.row >= 1 << 21
            || (8192..16384).contains(&t.row)));
        for seed in [3, 19] {
            let r = point(22, seed); let u = point(22, seed + 31); let v = point(22, seed + 79);
            let actual = literal(&circuit.terms, &r, &u, &v);
            assert_eq!(context.coefficients(4, &r, &u, &v).unwrap(), actual);
            let h = context.height.coefficients(&r[..8], &u, &v).unwrap();
            let d = context.adapter.roster().coefficients(&r[..21], &u, &v).unwrap();
            let hm = r[8..].iter().fold(Fr::one(), |a, x| a * (Fr::one() - x));
            let old_coefficients = std::array::from_fn::<_, 4, _>(|i| hm*h[i]+r[21]*d[i]);
            assert_eq!(literal(&old, &r, &u, &v), old_coefficients);
            let m = context.adapter.max().coefficients(&r[..13], &u, &v).unwrap();
            assert!(m.iter().any(|c| !c.is_zero()));
            for omitted in 14..22 {
                let bad_mask = (14..22).filter(|j| *j != omitted)
                    .fold(r[13], |a, j| a * (Fr::one() - r[j]));
                let wrong = std::array::from_fn::<_, 4, _>(|i| old_coefficients[i]+bad_mask*m[i]);
                assert_ne!(wrong, actual, "isolated missing high selector bit {omitted}");
            }
            let mut shifted = max.clone(); for t in &mut shifted { t.row += 1; }
            assert_ne!(literal(&shifted, &r, &u, &v), literal(&max, &r, &u, &v));
            let mut foreign = max.clone();
            let t = foreign.iter_mut().find(|t| t.gate.right > 0 && !t.gate.c1.is_zero()
                && t.gate.left / layout::WIDTH != t.gate.right / layout::WIDTH).unwrap();
            t.gate.right = 0;
            assert_ne!(literal(&foreign, &r, &u, &v), literal(&max, &r, &u, &v));
        }
        // Boolean row selectors independently isolate every occupied support
        // and gap. Other rows have exactly zero literal equality weight.
        let boolean = |index: usize| -> Vec<Fr> {
            assert!(index < 1 << 22);
            (0..22).map(|bit| Fr::from(((index >> bit) & 1) as u64)).collect()
        };
        let mut rows = vec![0, 255, 256, 8191, 16384, (1 << 21)-1,
            1 << 21, (1 << 22)-1];
        for owner in 0..4 {
            // Both active owners, terminal owner2 and inactive owner3 differ.
            for local in [0, 672, 673, 674, 897, 898, 1121, 1122, 2047] {
                rows.push(MAX_ROW_BASE + owner*2048 + local);
            }
            // An actual DAA relation from every owner retains its full support.
            let term = old.iter().find(|t| t.row >= DAA_ROW_BASE
                && t.gate.left / layout::WIDTH == owner).unwrap();
            rows.push(term.row);
        }
        rows.sort_unstable(); rows.dedup();
        let mut occupied = 0;
        let mut empty = 0;
        for row in rows {
            let selected: Vec<_> = circuit.terms.iter().filter(|t| t.row == row).cloned().collect();
            let r = boolean(row);
            let u = point(22, 43); let v = point(22, 97);
            assert_eq!(context.composite_coefficients(&r, &u, &v).unwrap(),
                literal(&selected, &r, &u, &v), "Boolean row {row}");
            if selected.is_empty() {
                empty += 1;
                assert_eq!(context.composite_coefficients(&r, &u, &v).unwrap(),
                    [Fr::zero(); 4], "unoccupied Boolean row {row}");
            } else {
                occupied += 1;
                // Boundary endpoints supplement the full asymmetric oracle.
                // Do not invoke the unchanged dense DAA coefficient evaluator
                // hundreds of times for one weighted arithmetic row.
                let mut pairs = vec![(selected.first().unwrap().gate.left,
                    selected.first().unwrap().gate.right),
                    (selected.last().unwrap().gate.left, selected.last().unwrap().gate.right)];
                if (MAX_ROW_BASE..MAX_ROW_BASE+4096).contains(&row)
                    && (row-MAX_ROW_BASE)%2048 == 673 {
                    let owner = (row-MAX_ROW_BASE)/2048;
                    for wire in [987674, 987897, 999648, 999871, 999872, 1000095, 1000096] {
                        pairs.push((owner*layout::WIDTH+wire, owner*layout::WIDTH));
                    }
                }
                pairs.sort_unstable(); pairs.dedup();
                for (left, right) in pairs {
                    let u = boolean(left); let v = boolean(right);
                    assert_eq!(context.composite_coefficients(&r, &u, &v).unwrap(),
                        literal(&selected, &r, &u, &v),
                        "occupied Boolean row/left/right {row}/{left}/{right}");
                }
            }
        }
        assert!(occupied > 0 && empty > 0);
        for row in [256, 8191, 16384, (1 << 21)-1] {
            assert!(!circuit.terms.iter().any(|t| t.row == row));
        }
        for owner in 0..4 {
            for tail in [1122, 2047] {
                assert!(!max.iter().any(|t| t.row == 8192 + owner*2048 + tail));
            }
        }
        let mut wrong = circuit.clone(); wrong.input_len = 1 << 21;
        assert!(sparse::validate(&wrong, 0).is_err());
        let mut wrong = circuit.clone(); wrong.row_count = 1 << 21;
        assert!(sparse::validate(&wrong, 0).is_err());
        let r = point(22, 3); let u = point(22, 7); let v = point(22, 11);
        assert!(context.composite_coefficients(&r[..21], &u, &v).is_err());
        assert!(context.composite_coefficients(&r, &u[..21], &v).is_err());
        assert!(context.composite_coefficients(&r, &u, &v[..21]).is_err());
    }

    #[test]
    fn complete_header_retirement_uses_same_consumer_adapter() {
        let public = Public::native(3).unwrap();
        let consumer = Consumer::new(&public).unwrap();
        let context = ProofContext::new(&consumer).unwrap();
        context.adapter.check_parent(&consumer.parent).unwrap();
        let r = point(21, 5); let u = point(22, 43); let v = point(22, 97);
        let rw=LiteralWeights::new(&r);let uw=LiteralWeights::new(&u);let vw=LiteralWeights::new(&v);
        let mut literal_coefficients = [Fr::zero(); 4];
        let mut total = 0;
        for owner in 0..4 {
            let ib = owner * layout::WIDTH; let rb = owner * (1 << 19);
            let mut retained = Vec::new(); let mut neighbors = [false; 2];
            let counts = context.adapter.visit_header_terms(owner, |term| {
                assert!((ib..ib+layout::WIDTH).contains(&term.gate.left));
                assert!((ib..ib+layout::WIDTH).contains(&term.gate.right));
                assert!((rb..rb+(1 << 19)).contains(&term.row));
                if (ib+999424..ib+1000097).contains(&term.gate.left) {
                    retained.push(term.clone());
                }
                for (j, wire) in [999423, 1000097].into_iter().enumerate() {
                    if term.gate.left == ib+wire && term.row == rb+wire-642792 {
                        assert_eq!(term.gate.right, ib);
                        assert_eq!([term.gate.c0,term.gate.c1,term.gate.c2,term.gate.c3],
                            [Fr::zero(),Fr::one(),Fr::zero(),Fr::zero()]);
                        assert!(!neighbors[j]); neighbors[j] = true;
                    }
                }
                add_term(&mut literal_coefficients, &term, &rw, &uw, &vw); Ok(())
            }).unwrap();
            let omitted = if owner < 2 { 673 } else { 0 };
            assert_eq!(counts.omitted_max, omitted);
            assert_eq!(counts.emitted, 396561-omitted);
            assert_eq!(neighbors, [true, true]);
            assert_eq!(retained.len(), if owner < 2 { 0 } else { 673 });
            for (j, term) in retained.iter().enumerate() {
                assert_eq!(term.row, rb+356632+j);
                assert_eq!(term.gate.left, ib+999424+j);
                assert_eq!(term.gate.right, ib);
                assert_eq!([term.gate.c0,term.gate.c1,term.gate.c2,term.gate.c3],
                    [Fr::zero(),Fr::one(),Fr::zero(),Fr::zero()]);
            }
            total += counts.emitted;
        }
        assert_eq!(total, 1584898);
        assert_eq!(context.coefficients(1, &r, &u, &v).unwrap(), literal_coefficients);
        let r4 = point(22, 5);
        assert!(context.coefficients(1, &r4, &u, &v).is_err());
    }
}


#[cfg(test)]
mod adjacency_stream_tests {
    use super::*;
    use crate::native_adjacency_stream::ChallengeTrace;
    use std::{cell::RefCell, collections::BTreeMap, path::PathBuf};

    mod packed_gkr_role1_tests { include!("packed_gkr_role1_tests.rs"); }

    include!("max_cap_projection_tests.rs");

    // These are the accepted MAX packet, not the rejected historical LEGACY_FILES.
    const PACKET_FILES: [(&str, usize, &str); 11] = [
        ("commitment.bin",384,"EF93E1157956BDCF3205EDB8C04F66994701426E0445669995EA6113D1EF2F4C"),
        ("openings.bin",31581,"47BD48C7473F92CD94DCAD101A4A78E7EDF90FFBC3D11012260C0C2DA8FED048"),
        ("role-0.gkr",5024,"7BAFA7D650020A15B43C4ABEEF0406FC22F2C9ACE5A3D018406FC3294902323E"),
        ("role-1.gkr",5024,"0EC72FF4868EF350C93183C91F4829CF79FC8CFB23401C7CCA682747148F8EF1"),
        ("role-2.gkr",5024,"0D90199215BB5F746784134D2A94132786E879CC55018642705BB3F06E645FC6"),
        ("role-3.gkr",3456,"6148438D1C6F07CD95C410A6F2952B715BC072B8C161BCC5DB5B2C450C3D2579"),
        ("role-4.gkr",5024,"FB506BCFD7C09861C541996FB380177D12913FB063671B604C5696108B908D58"),
        ("role-5.gkr",5024,"D8EACB550A25A5029E7A52DE85B939B57F58A694460E9D7F320115BE3A2720D8"),
        ("role-6.gkr",5024,"AEBBC0EE8DEADD050666E29A82E740B89794C50DCA4B0E7096A27D3169B146F4"),
        ("statement.bin",576,"2EBF0807053115FF0E8F8457EFD2FE5678E0C49A7A0EEE3EB950C3259E4556D7"),
        ("witness.bits",524288,"9D45000DD13F371AE2E740993346617B65C0C782B7867D6F6A0F7B01ADE24F30"),
    ];
    const BUNDLE_BYTES: usize = 869449;
    const BUNDLE_BLAKE2B256: &str = "8CDB90DA475E646280113D97C9469BE7EB86A1D04F20404C64239187284FC009";

    fn no_reparse_ancestors(path: &Path) -> Result<(), String> {
        if !path.is_absolute() {
            return Err("adjacency baseline path must be absolute".into());
        }
        for ancestor in path.ancestors() {
            let metadata = std::fs::symlink_metadata(ancestor).map_err(|e| e.to_string())?;
            if metadata.file_type().is_symlink() {
                return Err("adjacency baseline symlink rejected".into());
            }
            #[cfg(windows)]
            {
                use std::os::windows::fs::MetadataExt;
                if metadata.file_attributes() & 0x400 != 0 {
                    return Err("adjacency baseline reparse point rejected".into());
                }
            }
        }
        Ok(())
    }

    fn regular_file(path: &Path, length: usize) -> Result<(), String> {
        no_reparse_ancestors(path)?;
        let metadata = std::fs::symlink_metadata(path).map_err(|e| e.to_string())?;
        if !metadata.is_file() || metadata.len() != length as u64 {
            return Err("adjacency baseline file framing rejected".into());
        }
        Ok(())
    }

    fn pinned_bytes(path: &Path, length: usize, digest: &str) -> Result<Vec<u8>, String> {
        regular_file(path, length)?;
        let file = std::fs::File::open(path).map_err(|e| e.to_string())?;
        let mut bytes = Vec::with_capacity(length + 1);
        file.take((length + 1) as u64).read_to_end(&mut bytes).map_err(|e| e.to_string())?;
        let actual = Blake2b::<U32>::digest(&bytes).iter()
            .map(|byte| format!("{byte:02X}")).collect::<String>();
        if bytes.len() != length || actual != digest {
            return Err("adjacency baseline byte identity rejected".into());
        }
        Ok(bytes)
    }

    fn baseline_directory() -> Result<PathBuf, String> {
        std::env::var_os("NIPOPOW_NATIVE_ADJACENCY_BASELINE_DIR")
            .map(PathBuf::from).ok_or("missing pinned adjacency baseline directory".into())
    }

    fn check_native_bundle() -> Result<(), String> {
        let path = std::env::var_os("NIPOPOW_DAA_BUNDLE")
            .map(PathBuf::from).ok_or("missing pinned native RAW bundle")?;
        if path.file_name() != Some(std::ffi::OsStr::new("mainnet-prefix-first-3073-u32le-v1.bin")) {
            return Err("adjacency native bundle name rejected".into());
        }
        drop(pinned_bytes(&path, BUNDLE_BYTES, BUNDLE_BLAKE2B256)?);
        Ok(())
    }

    fn baseline_packet(dir: &Path, public: &Public) -> Result<Artifact, String> {
        no_reparse_ancestors(dir)?;
        let metadata = std::fs::symlink_metadata(dir).map_err(|e| e.to_string())?;
        if !metadata.is_dir() { return Err("adjacency baseline directory rejected".into()); }
        let mut names = std::fs::read_dir(dir).map_err(|e| e.to_string())?
            .map(|entry| entry.map_err(|e| e.to_string()).and_then(|entry| {
                entry.file_name().into_string().map_err(|_| "adjacency baseline name encoding".into())
            })).collect::<Result<Vec<_>, String>>()?;
        names.sort_unstable();
        let mut expected: Vec<_> = PACKET_FILES.iter().map(|(name, _, _)| name.to_string()).collect();
        expected.push("pcs-artifact-snapshot.json".into());
        expected.sort_unstable();
        if names != expected { return Err("adjacency baseline closed twelve-file set rejected".into()); }
        // Metadata only: the outer controller authenticates its SHA256. Rust never
        // parses this JSON to choose any tuple, circuit, profile or file digest.
        regular_file(&dir.join("pcs-artifact-snapshot.json"), 4480)?;
        let mut files: BTreeMap<&'static str, Vec<u8>> = BTreeMap::new();
        for (name, length, digest) in PACKET_FILES {
            files.insert(name, pinned_bytes(&dir.join(name), length, digest)?);
        }
        if files.remove("statement.bin").ok_or("adjacency baseline statement missing")? != public.bytes()? {
            return Err("adjacency baseline differs from native MAX public".into());
        }
        drop(files.remove("witness.bits").ok_or("adjacency baseline witness missing")?);
        let mut roles = Vec::with_capacity(7);
        for role in 0..7 {
            let name = format!("role-{role}.gkr");
            let bytes = files.remove(name.as_str()).ok_or("adjacency baseline role missing")?;
            gkr::decode_dimensions(&[INPUT_BITS[role]], &bytes)?;
            roles.push(RoleProof { role, bytes });
        }
        let commitment = files.remove("commitment.bin").ok_or("adjacency baseline commitment missing")?;
        pcs::decode_commitment(&commitment)?;
        let batch = files.remove("openings.bin").ok_or("adjacency baseline joint PCS missing")?;
        opening_batch::decode_proof(&batch, 22)?;
        if !files.is_empty() { return Err("adjacency baseline consumed file set drift".into()); }
        Ok(Artifact { commitment, roles, batch })
    }

    fn verify_role5_trace(
        context: &ProofContext<'_>,
        key: &verifier_key::AdmittedVerifierKey,
        commitment: &[u8],
        proof: &GkrProof,
        wrong_binder: bool,
    ) -> Result<(InputClaim, ChallengeTrace), GkrError> {
        let seen = RefCell::new(None::<(Vec<Fr>, Vec<Fr>, Vec<Fr>)>);
        let mut t = context.transcript(5, key, commitment);
        let claim = gkr::verify_with_wiring(
            &[22], 2048, proof, &mut t,
            |t| {
                context.bind_role(5, t);
                if wrong_binder { t.append_bytes(b"native-adjacency-wrong-binder", b"single-role-mutant"); }
            },
            |_, r, u, v| {
                if seen.borrow().is_some() { return Err(GkrError::InvalidWireIndex); }
                *seen.borrow_mut() = Some((r.to_vec(), u.to_vec(), v.to_vec()));
                context.coefficients(5, r, u, v).map_err(|_| GkrError::InvalidWireIndex)
            },
        )?;
        let (r, u, v) = seen.into_inner().ok_or(GkrError::InvalidWireIndex)?;
        let continuation = t.clone().challenge_scalar(b"native-adjacency-trace-continuation");
        Ok((claim, ChallengeTrace { r, u, v, continuation }))
    }

    fn run_native_adjacency_differential() -> Result<(), String> {
        // Custody is admitted before context construction or the new producer.
        check_native_bundle()?;
        let dir = baseline_directory()?;
        let public = Public::native(3)?;
        let artifact = baseline_packet(&dir, &public)?;
        let consumer = Consumer::new(&public)?;
        let context = ProofContext::new(&consumer)?;
        let key = verifier_key::admit(22, include_bytes!("../fixtures/verifier-keys-v1/log22.vk"))?;
        // Cheapest consumer falsifier first: never produce against an incompatible packet.
        let old_claims = context.verify(&artifact, &key).map_err(|e| format!("retained MAX packet: {e:?}"))?;
        let old_role5 = gkr::decode_dimensions(&[22], &artifact.roles[5].bytes)?;
        let (old_terminal, old_trace) = verify_role5_trace(
            &context, &key, &artifact.commitment, &old_role5, false,
        ).map_err(|e| e.to_string())?;
        assert_eq!(old_terminal.point, old_claims[5].point);
        assert_eq!(old_terminal.value, old_claims[5].value);

        let source = PackedFile::open(dir.join("witness.bits"), 22)?;
        source.reset_io_metrics();
        let mut producer_t = context.transcript(5, &key, &artifact.commitment);
        // Exactly the helper called by the actual MAX role5 match arm, once.
        let produced = prove_native_adjacency_role(&context, &source, &mut producer_t)?;
        let io = source.io_metrics_snapshot();
        assert_eq!(io.read_calls, 64);
        assert_eq!(io.read_bytes, 524288);
        assert_eq!(io.write_calls, 0);
        assert_eq!(io.write_bytes, 0);
        assert_eq!(io.sync_calls, 0);
        let diag = &produced.diagnostics;
        assert_eq!(diag.loader_per_slot, [1; 4]);
        assert_eq!(diag.max_slot_capacity, 1 << 20);
        assert_eq!(diag.terms, 1024);
        assert_eq!(diag.term_capacity, 1024);
        assert_eq!(diag.left_index_capacity, 1024);
        assert_eq!(diag.right_index_capacity, 1024);
        assert_eq!(diag.endpoint_calls, [[22; 4]; 2]);
        assert_eq!(diag.endpoint_calls.iter().flatten().sum::<usize>(), 176);
        assert_eq!(diag.endpoint_terms[0], [512 * 22, 256 * 22, 256 * 22, 0]);
        assert_eq!(diag.endpoint_terms[1], [512 * 22, 256 * 22, 256 * 22, 0]);
        assert!(!diag.used_incremental_u && !diag.used_incremental_v);
        assert_eq!(diag.tuple_blake2b256, layout::hash_terms(&context.small_circuit(5)?.terms));

        let encoded = gkr::encode_proof(&produced.proof)?;
        assert_eq!(encoded.len(), 5024);
        assert_eq!(encoded, artifact.roles[5].bytes);
        assert_eq!(produced.proof, old_role5);
        assert_eq!(produced.claim, old_terminal);
        assert_eq!(diag.trace, old_trace);
        let (new_terminal, new_trace) = verify_role5_trace(
            &context, &key, &artifact.commitment, &produced.proof, false,
        ).map_err(|e| e.to_string())?;
        assert_eq!(new_terminal, old_terminal);
        assert_eq!(new_trace, old_trace);
        assert_eq!(
            producer_t.clone().challenge_scalar(b"native-adjacency-trace-continuation"),
            old_trace.continuation,
        );

        let mut joined = artifact.clone();
        joined.roles[5].bytes = encoded;
        assert_eq!(context.verify(&joined, &key).map_err(|e| format!("{e:?}"))?, old_claims);

        let mut missing = joined.clone();
        missing.batch.clear();
        assert_eq!(context.verify(&missing, &key), Err(Reject::Linkage));
        let mut truncated = joined.clone();
        truncated.batch.pop();
        assert_eq!(context.verify(&truncated, &key), Err(Reject::Linkage));
        let mut changed_batch = joined.clone();
        changed_batch.batch[0] ^= 1;
        assert_eq!(context.verify(&changed_batch, &key), Err(Reject::Linkage));
        let mut missing_role = joined.clone();
        missing_role.roles.remove(5);
        assert_eq!(context.verify(&missing_role, &key), Err(Reject::Shape));
        let mut reordered = joined.clone();
        reordered.roles.swap(4, 5);
        assert_eq!(context.verify(&reordered, &key), Err(Reject::Shape));

        for field in 0..4 {
            let mut proof = produced.proof.clone();
            match field {
                0 => proof.layers[0].rounds[0][0] += Fr::one(),
                1 => proof.layers[0].line_coefficients[0] += Fr::one(),
                2 => proof.layers[0].left_value += Fr::one(),
                _ => proof.layers[0].right_value += Fr::one(),
            }
            let mut mutant = joined.clone();
            mutant.roles[5].bytes = gkr::encode_proof(&proof)?;
            assert_eq!(context.verify(&mutant, &key), Err(Reject::Role(5)));
        }
        // Only role5's manual binder is changed; a global context mutation could fail Role0.
        assert!(verify_role5_trace(
            &context, &key, &artifact.commitment, &produced.proof, true,
        ).is_err());

        // The packed source stays locked while all consumed native/packet pins are rechecked.
        let after = baseline_packet(&dir, &public)?;
        check_native_bundle()?;
        assert_eq!(after.commitment, artifact.commitment);
        assert_eq!(after.batch, artifact.batch);
        for role in 0..7 {
            assert_eq!(after.roles[role].role, artifact.roles[role].role);
            assert_eq!(after.roles[role].bytes, artifact.roles[role].bytes);
        }
        Ok(())
    }

    #[test]
    #[ignore = "requires pinned MAX packet/native bundle and bounded runner"]
    fn native_adjacency_same_proof_n3() {
        std::thread::Builder::new()
            .name("native-adjacency-same-proof".into())
            .stack_size(32 * 1024 * 1024)
            .spawn(|| run_native_adjacency_differential().unwrap())
            .unwrap().join().unwrap();
    }
}

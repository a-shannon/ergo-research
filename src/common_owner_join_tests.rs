//! One bounded common witness for two headers, mature DAA and physical imports.
//! The historical sample headers are serializer seeds, not authenticated history.
use crate::{
    daa_history_layout::DaaHistoryLayout,
    daa_integer::Epoch,
    gkr::{self, GkrProof, InputClaim},
    header_hash,
    header_history_boundary::HeaderHistoryBoundary,
    packed::{self, PackedFile, PackedFileWriter},
    pcs, serializer,
    sparse::Term,
    sparse_stream_roster::{self, EdgeTerm},
    transcript::Transcript,
    verifier_key,
};
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use dory_pcs::backends::arkworks::ArkworksVerifierSetup;
use std::{collections::HashMap, path::PathBuf, time::Instant};

const N: u64 = 844_674;
const SLOT_LOG: usize = 20;
const CHILD: u32 = 844_673;
const CHILD_SLOT: u64 = 844_672;
const LOCAL_BITS: usize = 20;
const COPY_BITS: usize = 4;
const INPUT_BITS: usize = 24;
const BASE_ROWS: usize = 19;
const MEMBER_ROWS: [usize; 2] = [19, 18];
const ROW_BITS: usize = 24;
const WIDTH: usize = 1 << LOCAL_BITS;
const CHUNK: usize = 1 << 16;
const CHUNKS: usize = 16;
const ARITH_ROW_START: usize = 1 << BASE_ROWS;
const ALIAS_ROW_START: usize = (1 << BASE_ROWS) | (1 << 17);
const TOTAL_TERMS: usize = 1_374_256;
const DOMAIN: &[u8] = b"native-common-header-daa-alias-v1";

fn boolean(index: usize, bits: usize) -> Vec<Fr> {
    (0..bits)
        .map(|bit| Fr::from(((index >> bit) & 1) as u64))
        .collect()
}
fn artifact(kind: &str, extension: &str) -> PathBuf {
    let directory = std::env::var_os("NIPOPOW_COMMON_OWNER_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    assert!(directory.is_dir());
    let stamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    directory.join(format!(
        "common-owner-{kind}-{}-{stamp}.{extension}",
        std::process::id()
    ))
}

struct Context {
    header: HeaderHistoryBoundary,
    daa: DaaHistoryLayout,
    heights: Vec<u32>,
    copies: HashMap<u64, usize>,
    arithmetic_fingerprint: String,
}
impl Context {
    fn new() -> Result<Self, String> {
        let mut heights = super::expected_heights()?;
        heights.push(CHILD.checked_add(1).ok_or("carry height overflow")?);
        if heights.len() != 11
            || heights[9] != CHILD
            || heights[10] != 844_674
            || crate::daa_header_window::for_child_height(heights[10])?.action()
                != crate::daa_header_window::Action::Carry
        {
            return Err("common native roster changed".into());
        }
        let mut copies = HashMap::new();
        for (copy, height) in heights.iter().enumerate() {
            let slot = u64::from(height.checked_sub(1).ok_or("roster zero height")?);
            if slot >= N || copies.insert(slot, copy).is_some() {
                return Err("roster exceeds N or duplicates a slot".into());
            }
        }
        let header = HeaderHistoryBoundary::compile(N, SLOT_LOG)?;
        header.validate_pair(CHILD_SLOT)?;
        let daa = DaaHistoryLayout::compile(Epoch::Eip, N, SLOT_LOG)?;
        if !header.eip_is_mature_at(CHILD_SLOT)
            || header.eip_is_mature_at(CHILD_SLOT + 1)
            || daa.mapped_relation().terms.len() != 432_042
            || daa.import_count() != 896
        {
            return Err("common code-owned mature/carry geometry changed".into());
        }
        let arithmetic_fingerprint = header.eip_arithmetic_fingerprint();
        Ok(Self {
            header,
            daa,
            heights,
            copies,
            arithmetic_fingerprint,
        })
    }
    fn bind(&self, t: &mut Transcript, setup_id: &[u8; 32], commitment: &[u8], history: u64) {
        t.append_bytes(b"profile", DOMAIN);
        for (label, value) in [
            (b"N".as_slice(), history),
            (b"logical-slot-bits", SLOT_LOG as u64),
            (b"input-bits", INPUT_BITS as u64),
            (b"row-bits", ROW_BITS as u64),
            (b"copy-bits", COPY_BITS as u64),
            (b"base-row-bits", BASE_ROWS as u64),
            (b"header-member-bits", 19),
            (b"daa-member-bits", 18),
            (b"epoch", Epoch::Eip.length()),
            (b"child-slot", CHILD_SLOT),
            (b"alias-count", 896),
            (b"term-count", TOTAL_TERMS as u64),
        ] {
            t.append_u64(label, value);
        }
        for height in &self.heights {
            t.append_u64(b"ordered-native-height", u64::from(*height));
        }
        t.append_bytes(b"header-fingerprint", self.header.fingerprint().as_bytes());
        t.append_bytes(
            b"arithmetic-fingerprint",
            self.arithmetic_fingerprint.as_bytes(),
        );
        t.append_bytes(b"setup-id", setup_id);
        t.append_bytes(b"common-commitment", commitment);
    }
    fn alias_edges(
        &self,
        mut sink: impl FnMut(EdgeTerm) -> Result<(), String>,
    ) -> Result<(), String> {
        let count = self.daa.visit_alias_terms(CHILD_SLOT, |mut term| {
            let index = term
                .row
                .checked_sub(CHILD_SLOT as usize * 1024)
                .ok_or("alias row underflow")?;
            if index >= 896 {
                return Err("alias row outside roster".into());
            }
            for endpoint in [&mut term.gate.left, &mut term.gate.right] {
                let logical = (*endpoint / WIDTH) as u64;
                let copy = *self
                    .copies
                    .get(&logical)
                    .ok_or("alias endpoint missing from common roster")?;
                *endpoint = copy
                    .checked_mul(WIDTH)
                    .and_then(|base| base.checked_add(*endpoint % WIDTH))
                    .ok_or("alias translation overflow")?;
            }
            let family_row = ALIAS_ROW_START + index;
            term.row = family_row;
            sink(EdgeTerm {
                source_slot: 9,
                family_row,
                term,
            })
        })?;
        if count != 896 {
            return Err("alias count changed".into());
        }
        Ok(())
    }
    fn visit_endpoint(
        &self,
        left: bool,
        copy: usize,
        mut sink: impl FnMut(EdgeTerm) -> Result<(), String>,
    ) -> Result<(), String> {
        if copy >= 16 {
            return Err("common endpoint copy outside domain".into());
        }
        if copy == 9 || copy == 10 {
            let logical = u64::from(self.heights[copy] - 1);
            let row_base = (logical as usize)
                .checked_mul(1 << 19)
                .ok_or("header row base overflow")?;
            let input_base = (logical as usize)
                .checked_mul(WIDTH)
                .ok_or("header input base overflow")?;
            let counts = self.header.visit_slot_terms(logical, |mut term| {
                term.row = term
                    .row
                    .checked_sub(row_base)
                    .ok_or("header local row underflow")?;
                for endpoint in [&mut term.gate.left, &mut term.gate.right] {
                    let local = endpoint
                        .checked_sub(input_base)
                        .ok_or("header local endpoint underflow")?;
                    if local >= WIDTH {
                        return Err("header endpoint escapes selected copy".into());
                    }
                    *endpoint = copy * WIDTH + local;
                }
                let family_row = term.row;
                sink(EdgeTerm {
                    source_slot: copy,
                    family_row,
                    term,
                })
            })?;
            let expected = if copy == 9 {
                (466_563, 8_192)
            } else {
                (474_755, 0)
            };
            if (counts.emitted, counts.omitted_a4) != expected {
                return Err("header release/count changed".into());
            }
            if copy == 9 {
                for source in &self.daa.mapped_relation().terms {
                    if source.row >= 1 << 17
                        || source.gate.left >= WIDTH
                        || source.gate.right >= WIDTH
                    {
                        return Err("arithmetic member escapes profile".into());
                    }
                    let mut term = source.clone();
                    let family_row = ARITH_ROW_START + source.row;
                    term.row = family_row;
                    term.gate.left += 9 * WIDTH;
                    term.gate.right += 9 * WIDTH;
                    sink(EdgeTerm {
                        source_slot: 9,
                        family_row,
                        term,
                    })?;
                }
            }
        }
        self.alias_edges(|edge| {
            let endpoint = if left {
                edge.term.gate.left
            } else {
                edge.term.gate.right
            };
            if endpoint / WIDTH == copy {
                sink(edge)?;
            }
            Ok(())
        })
    }
    // The consumer uses only code-owned analytic factories and the expected
    // schedule. It never derives its coefficients from emitted EdgeTerms.
    fn parts(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[[Fr; 4]; 3], String> {
        if r.len() != ROW_BITS || u.len() != INPUT_BITS || v.len() != INPUT_BITS {
            return Err("common coefficient dimension mismatch".into());
        }
        let mut header = [Fr::zero(); 4];
        for copy in [9, 10] {
            let fixed = boolean(self.heights[copy] as usize - 1, SLOT_LOG);
            let mut row = r[..19].to_vec();
            row.extend_from_slice(&fixed);
            let mut source = u[..20].to_vec();
            source.extend_from_slice(&fixed);
            let mut target = v[..20].to_vec();
            target.extend_from_slice(&fixed);
            let coefficients = self.header.coefficients(&row, &source, &target)?;
            let weight = (Fr::one() - r[23])
                * super::eq_at(&r[19..23], copy)
                * super::eq_at(&u[20..], copy)
                * super::eq_at(&v[20..], copy);
            for i in 0..4 {
                header[i] += weight * coefficients[i];
            }
        }
        let fixed = boolean(CHILD_SLOT as usize, SLOT_LOG);
        let mut row = r[..17].to_vec();
        row.extend_from_slice(&fixed);
        let mut source = u[..20].to_vec();
        source.extend_from_slice(&fixed);
        let mut target = v[..20].to_vec();
        target.extend_from_slice(&fixed);
        let mut arithmetic = self.daa.arithmetic_coefficients(&row, &source, &target)?;
        let arithmetic_weight = r[23]
            * (Fr::one() - r[22])
            * (Fr::one() - r[17])
            * super::eq_at(&r[18..22], 9)
            * super::eq_at(&u[20..], 9)
            * super::eq_at(&v[20..], 9);
        for c in &mut arithmetic {
            *c *= arithmetic_weight;
        }
        let mut alias_row = r[..10].to_vec();
        alias_row.extend_from_slice(&r[18..22]);
        let mut alias =
            super::wiring_restriction(&self.daa, &self.heights[..10], &alias_row, u, v)?;
        let alias_weight = r[23]
            * (Fr::one() - r[22])
            * r[17]
            * r[10..17].iter().fold(Fr::one(), |a, x| a * (Fr::one() - x));
        for c in &mut alias {
            *c *= alias_weight;
        }
        Ok([header, arithmetic, alias])
    }
    fn coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
        let parts = self.parts(r, u, v)?;
        Ok(std::array::from_fn(|i| {
            parts[0][i] + parts[1][i] + parts[2][i]
        }))
    }
    fn wrong_alias_owner(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
        let mut parts = self.parts(r, u, v)?;
        let mut row = r[..10].to_vec();
        row.extend(boolean(9, 4));
        let mut alias = super::wiring_restriction(&self.daa, &self.heights[..10], &row, u, v)?;
        let weight = r[23]
            * (Fr::one() - r[22])
            * r[17]
            * r[10..17].iter().fold(Fr::one(), |a, x| a * (Fr::one() - x))
            * super::eq_at(&r[18..22], 8);
        for c in &mut alias {
            *c *= weight;
        }
        parts[2] = alias;
        Ok(std::array::from_fn(|i| {
            parts[0][i] + parts[1][i] + parts[2][i]
        }))
    }
}

fn finite_coefficients(
    context: &Context,
    r: &[Fr],
    u: &[Fr],
    v: &[Fr],
) -> Result<([Fr; 4], usize), String> {
    let mut coefficients = [Fr::zero(); 4];
    let mut count = 0;
    for copy in 0..16 {
        context.visit_endpoint(true, copy, |edge| {
            let row = sparse_stream_roster::global_edge_row(
                edge.source_slot,
                edge.family_row,
                4,
                19,
                1,
                &MEMBER_ROWS,
            )?;
            let weight = super::eq_at(r, row)
                * super::eq_at(u, edge.term.gate.left)
                * super::eq_at(v, edge.term.gate.right);
            for (out, c) in coefficients.iter_mut().zip([
                edge.term.gate.c0,
                edge.term.gate.c1,
                edge.term.gate.c2,
                edge.term.gate.c3,
            ]) {
                if !c.is_zero() {
                    *out += weight * c;
                }
            }
            count += 1;
            Ok(())
        })?;
    }
    Ok((coefficients, count))
}

#[test]
fn common_owner_row_families_match_streamed_reference_and_isolated_mutants() {
    let context = Context::new().unwrap();
    let r = (0..24)
        .map(|i| Fr::from((7 + i * 11) as u64))
        .collect::<Vec<_>>();
    let u = (0..24)
        .map(|i| Fr::from((13 + i * 17) as u64))
        .collect::<Vec<_>>();
    let v = (0..24)
        .map(|i| Fr::from((19 + i * 23) as u64))
        .collect::<Vec<_>>();
    let (reference, count) = finite_coefficients(&context, &r, &u, &v).unwrap();
    assert_eq!(count, TOTAL_TERMS);
    assert_eq!(context.coefficients(&r, &u, &v).unwrap(), reference);
    let parts = context.parts(&r, &u, &v).unwrap();
    assert_ne!(
        std::array::from_fn::<_, 4, _>(|i| parts[0][i] + parts[1][i]),
        reference,
        "omitted alias family"
    );
    assert_ne!(
        context.wrong_alias_owner(&r, &u, &v).unwrap(),
        reference,
        "wrong physical row owner"
    );
    let copy_mask = super::eq_at(&r[18..22], 9);
    assert_ne!(
        std::array::from_fn::<_, 4, _>(|i| parts[0][i] + parts[1][i] + copy_mask * parts[2][i]),
        reference,
        "double physical copy mask"
    );
    let mut first = None;
    context
        .alias_edges(|edge| {
            if first.is_none() {
                first = Some(edge);
            }
            Ok(())
        })
        .unwrap();
    let edge = first.unwrap();
    let global =
        sparse_stream_roster::global_edge_row(9, edge.family_row, 4, 19, 1, &MEMBER_ROWS).unwrap();
    let weight = super::eq_at(&r, global)
        * super::eq_at(&u, edge.term.gate.left)
        * super::eq_at(&v, edge.term.gate.right);
    assert!(!weight.is_zero());
    let mut omitted_one = reference;
    omitted_one[1] -= weight;
    omitted_one[2] += weight;
    assert_ne!(omitted_one, reference);
    let arith_end = sparse_stream_roster::global_edge_row(
        9,
        ARITH_ROW_START + (1 << 17) - 1,
        4,
        19,
        1,
        &MEMBER_ROWS,
    )
    .unwrap();
    assert_eq!(arith_end + 1, global, "disjoint adjacent member regions");
    let wrong_copy_position = (1 << 23) | (9 << 19) | (edge.family_row & ((1 << 19) - 1));
    assert_ne!(global, wrong_copy_position);
    assert_ne!(
        super::eq_at(&r, global),
        super::eq_at(&r, wrong_copy_position)
    );
    let overlap_row =
        sparse_stream_roster::global_edge_row(9, ARITH_ROW_START, 4, 19, 1, &MEMBER_ROWS).unwrap();
    assert_ne!(global, overlap_row);
    assert_ne!(super::eq_at(&r, global), super::eq_at(&r, overlap_row));
    let row = boolean(global, 24);
    let left = boolean(edge.term.gate.left, 24);
    let right = boolean(edge.term.gate.right, 24);
    assert_eq!(
        context.coefficients(&row, &left, &right).unwrap(),
        [Fr::zero(), Fr::one(), -Fr::one(), Fr::zero()]
    );
    // Select each member with Boolean family/copy coordinates while leaving
    // its local coordinates asymmetric. The oracle reads actual emitted
    // terms, independent of the consumer's analytic decomposition.
    for (kind, owner, endpoint_copy, local_bits, expected_count) in [
        (0usize, 9usize, 9usize, 19usize, 466_563usize),
        (0, 10, 10, 19, 474_755),
        (1, 9, 9, 17, 432_042),
        (2, 9, 0, 10, 64),
    ] {
        let mut selected_row = vec![Fr::zero(); 24];
        selected_row[..local_bits].copy_from_slice(&r[..local_bits]);
        let copy_start = if kind == 0 { 19 } else { 18 };
        selected_row[copy_start..copy_start + 4].copy_from_slice(&boolean(owner, 4));
        if kind != 0 {
            selected_row[23] = Fr::one();
        }
        if kind == 2 {
            selected_row[17] = Fr::one();
        }
        let mut selected_u = u.clone();
        selected_u[20..].copy_from_slice(&boolean(endpoint_copy, 4));
        let mut selected_v = v.clone();
        selected_v[20..].copy_from_slice(&boolean(owner, 4));
        let mut expected = [Fr::zero(); 4];
        let mut selected_count = 0;
        context
            .visit_endpoint(true, endpoint_copy, |edge| {
                let selected = edge.source_slot == owner
                    && match kind {
                        0 => edge.family_row < ARITH_ROW_START,
                        1 => (ARITH_ROW_START..ALIAS_ROW_START).contains(&edge.family_row),
                        2 => edge.family_row >= ALIAS_ROW_START,
                        _ => unreachable!(),
                    };
                if selected {
                    let global = sparse_stream_roster::global_edge_row(
                        edge.source_slot,
                        edge.family_row,
                        4,
                        19,
                        1,
                        &MEMBER_ROWS,
                    )?;
                    let weight = super::eq_at(&selected_row, global)
                        * super::eq_at(&selected_u, edge.term.gate.left)
                        * super::eq_at(&selected_v, edge.term.gate.right);
                    for (out, c) in expected.iter_mut().zip([
                        edge.term.gate.c0,
                        edge.term.gate.c1,
                        edge.term.gate.c2,
                        edge.term.gate.c3,
                    ]) {
                        if !c.is_zero() {
                            *out += weight * c;
                        }
                    }
                    selected_count += 1;
                }
                Ok(())
            })
            .unwrap();
        assert_eq!(
            selected_count, expected_count,
            "selected member{kind} owner{owner}"
        );
        assert_eq!(
            context
                .coefficients(&selected_row, &selected_u, &selected_v)
                .unwrap(),
            expected,
            "selected member{kind} owner{owner}"
        );
        assert_ne!(
            expected,
            [Fr::zero(); 4],
            "nontrivial mixed reference member{kind} owner{owner}"
        );
        let mut wrong_copy = selected_row.clone();
        wrong_copy[copy_start] = Fr::one() - wrong_copy[copy_start];
        assert_eq!(
            context
                .coefficients(&wrong_copy, &selected_u, &selected_v)
                .unwrap(),
            [Fr::zero(); 4],
            "mixed copy member{kind} owner{owner}"
        );
        if kind != 0 {
            let mut wrong_padding = selected_row;
            wrong_padding[22] = Fr::one();
            assert_eq!(
                context
                    .coefficients(&wrong_padding, &selected_u, &selected_v)
                    .unwrap(),
                [Fr::zero(); 4],
                "padding bit22 member{kind}"
            );
        }
    }
    for (bad_row, bad_left, bad_right) in [
        (boolean(global ^ (1 << 22), 24), left.clone(), right.clone()),
        (
            row.clone(),
            boolean(edge.term.gate.left ^ WIDTH, 24),
            right.clone(),
        ),
        (
            row.clone(),
            left.clone(),
            boolean(edge.term.gate.right ^ WIDTH, 24),
        ),
    ] {
        assert_eq!(
            context
                .coefficients(&bad_row, &bad_left, &bad_right)
                .unwrap(),
            [Fr::zero(); 4]
        );
    }
    assert!(context.coefficients(&r[..23], &u, &v).is_err());
    println!("common row24/input24 streamed_reference_terms={count} member_rows=[19,18] all isolated coefficient gates passed");
}

fn pack_native(context: &Context) -> PackedFile {
    let (fixture, headers) = crate::header_history_boundary::tests::fixture();
    let serializer = serializer::build(None).unwrap();
    let path = artifact("packed", "bin");
    let mut writer = PackedFileWriter::create_new(&path, 24).unwrap();
    for copy in 0..16 {
        let mut input = if copy == 9 || copy == 10 {
            crate::header_history_boundary::tests::assignment_for_child(
                context.heights[copy],
                &fixture,
                &headers,
            )
        } else {
            vec![Fr::zero(); WIDTH]
        };
        if copy < 9 {
            let decoded =
                ergo_header_core::Header::decode(&headers[&context.heights[copy]], None).unwrap();
            let assignment = serializer.assign(&serializer::Fields::from_header(&decoded).unwrap());
            input
                [header_hash::SERIALIZER_OFFSET..header_hash::SERIALIZER_OFFSET + assignment.len()]
                .copy_from_slice(&assignment);
        }
        assert_eq!(input.len(), WIDTH);
        writer.write_bytes(&super::pack_bits(&input)).unwrap();
    }
    writer.finish().unwrap()
}

fn verify_common(
    proof: &GkrProof,
    setup_id: &[u8; 32],
    commitment: &[u8],
) -> Result<(InputClaim, Transcript), String> {
    let expected = Context::new()?;
    let mut t = Transcript::new(DOMAIN);
    let claim = gkr::verify_with_wiring(
        &[24],
        1 << 24,
        proof,
        &mut t,
        |t| expected.bind(t, setup_id, commitment, N),
        |_layer, r, u, v| {
            expected
                .coefficients(r, u, v)
                .map_err(|_| gkr::GkrError::PointDimension)
        },
    )
    .map_err(|e| e.to_string())?;
    Ok((claim, t))
}

#[test]
fn native_common_witness_proves_two_headers_arithmetic_aliases_and_one_pcs24() {
    let whole = Instant::now();
    let mark = Instant::now();
    let context = Context::new().unwrap();
    let context_ms = mark.elapsed().as_millis();
    let mark = Instant::now();
    let source = pack_native(&context);
    let packing_ms = mark.elapsed().as_millis();
    let mark = Instant::now();
    let setup = pcs::generate_setup(24).unwrap();
    let setup_ms = mark.elapsed().as_millis();
    let key_bytes = pcs::encode(&ArkworksVerifierSetup(setup.verifier.clone())).unwrap();
    let admitted = verifier_key::admit_generated_test_key(24, &key_bytes, setup.id).unwrap();
    let mark = Instant::now();
    let committed = packed::commit(&source, &setup).unwrap();
    let commit_ms = mark.elapsed().as_millis();
    let commitment = pcs::encode_commitment(&committed.commitment).unwrap();
    let mut t = Transcript::new(DOMAIN);
    let mut loads = 0usize;
    let mut endpoint_passes = 0usize;
    let mut term_visits = 0usize;
    source.reset_io_metrics();
    let mark = Instant::now();
    let (proof, claim, incremental_u, incremental_v) = sparse_stream_roster::prove_edge_terms(
        20,
        4,
        19,
        1,
        &MEMBER_ROWS,
        |left, copy, sink| {
            endpoint_passes += 1;
            context.visit_endpoint(left, copy, |edge| {
                term_visits += 1;
                sink(edge)
            })
        },
        |copy| {
            loads += 1;
            let mut values = Vec::with_capacity(WIDTH);
            for chunk in 0..CHUNKS {
                values.extend(source.read_copy(CHUNK, copy * CHUNKS + chunk)?);
            }
            Ok(values)
        },
        &mut t,
        |t| context.bind(t, &setup.id, &commitment, N),
        |r, u, v| context.coefficients(r, u, v),
    )
    .unwrap();
    let gkr_ms = mark.elapsed().as_millis();
    let io = source.io_metrics_snapshot();
    assert_eq!(io.read_calls, (loads * CHUNKS) as u64);
    assert_eq!(io.read_bytes, (loads * WIDTH / 8) as u64);
    let mark = Instant::now();
    let (verified, mut consumer) = verify_common(&proof, &setup.id, &commitment).unwrap();
    let full_consumer_ms = mark.elapsed().as_millis();
    assert_eq!(verified, claim);
    assert_eq!(
        t.clone().challenge_scalar(b"post-gkr"),
        consumer.clone().challenge_scalar(b"post-gkr")
    );
    let mark = Instant::now();
    let file_value = source.evaluate(&claim.point).unwrap();
    let mle_ms = mark.elapsed().as_millis();
    assert_eq!(file_value, claim.value);
    let pre_pcs = consumer.clone();
    let mut opening_t = t.clone();
    let mark = Instant::now();
    let opening = packed::open(&committed, &source, &claim.point, &setup, &mut opening_t).unwrap();
    let opening_ms = mark.elapsed().as_millis();
    let mark = Instant::now();
    pcs::verify_admitted(
        committed.commitment.clone(),
        claim.value,
        &claim.point,
        &opening,
        &admitted,
        &mut consumer,
    )
    .unwrap();
    let pcs_verify_ms = mark.elapsed().as_millis();
    assert_eq!(
        opening_t.challenge_scalar(b"post-pcs"),
        consumer.challenge_scalar(b"post-pcs")
    );
    let mut wrong_value = pre_pcs;
    assert!(pcs::verify_admitted(
        committed.commitment.clone(),
        claim.value + Fr::one(),
        &claim.point,
        &opening,
        &admitted,
        &mut wrong_value
    )
    .is_err());
    let mut wrong_context = Transcript::new(DOMAIN);
    assert_eq!(
        gkr::verify_with_wiring(
            &[24],
            1 << 24,
            &proof,
            &mut wrong_context,
            |t| context.bind(t, &setup.id, &commitment, N - 1),
            |_layer, r, u, v| context
                .coefficients(r, u, v)
                .map_err(|_| gkr::GkrError::PointDimension)
        )
        .unwrap_err(),
        gkr::GkrError::SumcheckIdentity
    );
    let mut omitted = Transcript::new(DOMAIN);
    assert_eq!(
        gkr::verify_with_wiring(
            &[24],
            1 << 24,
            &proof,
            &mut omitted,
            |t| context.bind(t, &setup.id, &commitment, N),
            |_layer, r, u, v| {
                let p = context
                    .parts(r, u, v)
                    .map_err(|_| gkr::GkrError::PointDimension)?;
                Ok(std::array::from_fn(|i| p[0][i] + p[1][i]))
            }
        )
        .unwrap_err(),
        gkr::GkrError::TerminalExpression
    );
    let mut wrong_owner = Transcript::new(DOMAIN);
    assert_eq!(
        gkr::verify_with_wiring(
            &[24],
            1 << 24,
            &proof,
            &mut wrong_owner,
            |t| context.bind(t, &setup.id, &commitment, N),
            |_layer, r, u, v| context
                .wrong_alias_owner(r, u, v)
                .map_err(|_| gkr::GkrError::PointDimension)
        )
        .unwrap_err(),
        gkr::GkrError::TerminalExpression
    );
    let mut causal = None;
    context
        .alias_edges(|edge| {
            if causal.is_none() {
                let wire = edge.term.gate.left;
                let chunk = source.read_copy(CHUNK, wire / CHUNK)?;
                if chunk[wire % CHUNK] != chunk[(wire ^ 1) % CHUNK] {
                    causal = Some(edge);
                }
            }
            Ok(())
        })
        .unwrap();
    let causal = causal.expect("one causal native alias edge");
    let mut wrong_edge_t = Transcript::new(DOMAIN);
    let false_edge = sparse_stream_roster::prove_edge_terms(
        20,
        4,
        19,
        1,
        &MEMBER_ROWS,
        |left, copy, sink| {
            // An adjacent local bit stays in the same endpoint copy, so apply
            // exactly the same single fault in both endpoint enumerations.
            context.visit_endpoint(left, copy, |mut edge| {
                if edge.family_row == causal.family_row && edge.source_slot == 9 {
                    edge.term.gate.left ^= 1;
                }
                sink(edge)
            })
        },
        |copy| {
            let mut values = Vec::with_capacity(WIDTH);
            for chunk in 0..16 {
                values.extend(source.read_copy(CHUNK, copy * 16 + chunk)?);
            }
            Ok(values)
        },
        &mut wrong_edge_t,
        |t| context.bind(t, &setup.id, &commitment, N),
        |r, u, v| context.coefficients(r, u, v),
    );
    assert_eq!(
        false_edge.unwrap_err(),
        gkr::GkrError::SumcheckIdentity.to_string()
    );
    let proof_bytes = gkr::encode_proof(&proof).unwrap();
    let pcs_bytes = pcs::encode_proof(&opening).unwrap();
    super::write_create_new(&artifact("gkr", "bin"), &proof_bytes);
    super::write_create_new(&artifact("pcs", "bin"), &pcs_bytes);
    super::write_create_new(&artifact("test-key", "bin"), &key_bytes);
    let receipt = serde_json::json!({"profile":"two native header boundaries plus mature EIP arithmetic and physical imports","N":N,"active_copies":11,"copies":16,"input_bits":24,"row_bits":24,"member_rows":MEMBER_ROWS,"terms":TOTAL_TERMS,"loader_calls":loads,"endpoint_passes":endpoint_passes,"term_visits":term_visits,"packed_reads":io.read_calls,"packed_read_bytes":io.read_bytes,"incremental_u":incremental_u,"incremental_v":incremental_v,"context_ms":context_ms,"packing_ms":packing_ms,"setup_ms":setup_ms,"commit_ms":commit_ms,"gkr_ms":gkr_ms,"full_consumer_ms":full_consumer_ms,"mle_ms":mle_ms,"opening_ms":opening_ms,"pcs_verify_ms":pcs_verify_ms,"whole_ms":whole.elapsed().as_millis(),"gkr_bytes":proof_bytes.len(),"pcs_bytes":pcs_bytes.len(),"causal_alias_local_row":causal.family_row-ALIAS_ROW_START,"setup_id":setup.id.iter().map(|b|format!("{b:02x}")).collect::<String>(),"authority_ceiling":"bounded selected common witness only; sample headers not boundary/hash proven; no carry DAA rule or authenticated historical inclusion"});
    println!("{receipt}");
    super::write_create_new(&artifact("receipt", "json"), receipt.to_string().as_bytes());
}

#[path = "height_slot_join_tests.rs"]
mod height_slot_join_tests;

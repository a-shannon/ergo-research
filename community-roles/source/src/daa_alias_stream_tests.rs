//! Bounded native physical DAA alias edge diagnostic. The fixture supplies
//! decoded header fields only; this test does not authenticate history or PoW.
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use dory_pcs::backends::arkworks::ArkworksVerifierSetup;
use std::{collections::HashMap, fs::OpenOptions, io::Write, path::PathBuf, time::Instant};

use crate::{
    daa_count, daa_finish,
    daa_header_window::{self, Action},
    daa_history_layout::DaaHistoryLayout,
    daa_integer::Epoch,
    gkr::{self, GkrProof, InputClaim},
    header_hash,
    mapped_daa_plan::MappedDaaPlan,
    packed::{self, PackedFile, PackedFileWriter},
    pcs, serializer,
    sparse::Term,
    sparse_stream_roster::{self, EdgeTerm},
    transcript::Transcript,
    verifier_key,
};

const N: u64 = 844_674;
const CHILD_HEIGHT: u32 = 844_673;
const CHILD_SLOT: u64 = 844_672;
const SLOT_LOG: usize = 20;
const LOCAL_BITS: usize = 20;
const COPY_BITS: usize = 4;
const ROW_BITS: usize = 10;
const FAMILY_BITS: usize = 0;
const INPUT_BITS: usize = LOCAL_BITS + COPY_BITS;
const COPY_LEN: usize = 1 << LOCAL_BITS;
const CHUNK: usize = 1 << 16;
const CHUNKS_PER_COPY: usize = COPY_LEN / CHUNK;
const PROFILE: &[u8] = b"native-daa-physical-alias-edge-diagnostic-v1";
const ROSTER: &[u8] = b"native-EIP-9-samples-then-child;copy-ordinals-0..9;unused-6-zero-v1";
const DOMAIN: &[u8] = b"nipopow-daa-alias-edge-v1";

fn artifact_path(kind: &str, extension: &str) -> PathBuf {
    let root = std::env::var_os("NIPOPOW_DAA_ALIAS_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    assert!(root.is_dir(), "alias artifact directory must already exist");
    let stamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    root.join(format!(
        "daa-alias-{kind}-{}-{stamp}.{extension}",
        std::process::id()
    ))
}

fn write_create_new(path: &std::path::Path, bytes: &[u8]) {
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .unwrap();
    file.write_all(bytes).unwrap();
    file.sync_all().unwrap();
}

fn eq_at(point: &[Fr], index: usize) -> Fr {
    point
        .iter()
        .enumerate()
        .fold(Fr::one(), |weight, (bit, x)| {
            weight
                * if (index >> bit) & 1 == 1 {
                    *x
                } else {
                    Fr::one() - x
                }
        })
}

fn alias_statement(transcript: &mut Transcript, setup_id: &[u8; 32], commitment: &[u8]) {
    alias_statement_with_history(transcript, setup_id, commitment, N);
}

fn alias_statement_with_history(
    transcript: &mut Transcript,
    setup_id: &[u8; 32],
    commitment: &[u8],
    history_slots: u64,
) {
    transcript.append_bytes(b"profile", PROFILE);
    transcript.append_bytes(b"family-roster", ROSTER);
    transcript.append_u64(b"input-bits", INPUT_BITS as u64);
    transcript.append_u64(b"row-bits", (ROW_BITS + COPY_BITS) as u64);
    transcript.append_u64(b"local-input-bits", LOCAL_BITS as u64);
    transcript.append_u64(b"copy-bits", COPY_BITS as u64);
    transcript.append_u64(b"history-slots", history_slots);
    transcript.append_u64(b"slot-log", SLOT_LOG as u64);
    transcript.append_u64(b"epoch", Epoch::Eip.length());
    transcript.append_u64(b"child-slot", CHILD_SLOT);
    transcript.append_bytes(b"setup-id", setup_id);
    transcript.append_bytes(b"common-commitment", commitment);
}

fn expected_heights() -> Result<Vec<u32>, String> {
    let plan = daa_header_window::for_child_height(CHILD_HEIGHT)?;
    if plan.action() != Action::Retarget(Epoch::Eip) || plan.sample_heights().len() != 9 {
        return Err("fixed native EIP roster changed".into());
    }
    Ok(plan
        .sample_heights()
        .iter()
        .copied()
        .chain(std::iter::once(CHILD_HEIGHT))
        .collect())
}

/// Consumer wiring is reconstructed from the fixed native schedule and the
/// expected code-owned layout. It never depends on the emitted producer terms.
fn wiring_restriction(
    layout: &DaaHistoryLayout,
    heights: &[u32],
    r: &[Fr],
    u: &[Fr],
    v: &[Fr],
) -> Result<[Fr; 4], String> {
    if heights.len() != 10
        || r.len() != ROW_BITS + COPY_BITS
        || u.len() != INPUT_BITS
        || v.len() != INPUT_BITS
    {
        return Err("alias restriction dimensions changed".into());
    }
    let slot_point = |slot: u64| {
        (0..SLOT_LOG)
            .map(|bit| Fr::from((slot >> bit) & 1))
            .collect::<Vec<_>>()
    };
    let mut full_r = r[..ROW_BITS].to_vec();
    full_r.extend(slot_point(CHILD_SLOT));
    let mut full_v = v[..LOCAL_BITS].to_vec();
    full_v.extend(slot_point(CHILD_SLOT));
    let owner = eq_at(&r[ROW_BITS..], 9) * eq_at(&v[LOCAL_BITS..], 9);
    let mut result = [Fr::zero(); 4];
    for (copy, height) in heights.iter().enumerate() {
        let mut full_u = u[..LOCAL_BITS].to_vec();
        full_u.extend(slot_point(u64::from(*height - 1)));
        let coefficients = layout.alias_coefficients(&full_r, &full_u, &full_v)?;
        let selector = owner * eq_at(&u[LOCAL_BITS..], copy);
        for i in 0..4 {
            result[i] += selector * coefficients[i];
        }
    }
    Ok(result)
}

fn verifier_claim(
    proof: &GkrProof,
    setup_id: &[u8; 32],
    commitment: &[u8],
    layout: &DaaHistoryLayout,
) -> Result<(InputClaim, Transcript), gkr::GkrError> {
    let heights = expected_heights().map_err(|_| gkr::GkrError::PointDimension)?;
    let mut transcript = Transcript::new(DOMAIN);
    let claim = gkr::verify_with_wiring(
        &[INPUT_BITS],
        1 << (ROW_BITS + COPY_BITS),
        proof,
        &mut transcript,
        |t| alias_statement(t, setup_id, commitment),
        |_layer, r, u, v| {
            wiring_restriction(layout, &heights, r, u, v).map_err(|_| gkr::GkrError::PointDimension)
        },
    )?;
    Ok((claim, transcript))
}

fn pack_bits(values: &[Fr]) -> Vec<u8> {
    let mut bytes = vec![0u8; values.len().div_ceil(8)];
    for (index, value) in values.iter().enumerate() {
        assert!(
            value.is_zero() || value.is_one(),
            "native witness must be Boolean"
        );
        if value.is_one() {
            bytes[index / 8] |= 1 << (index % 8);
        }
    }
    bytes
}

fn native_roster_for(
    child_height: u32,
) -> (
    Vec<u32>,
    HashMap<u64, usize>,
    HashMap<u32, Vec<u8>>,
    Vec<Fr>,
) {
    use ergo_header_core::Header;
    let (fixture, headers) = crate::header_history_boundary::tests::fixture();
    let plan = daa_header_window::for_child_height(child_height).unwrap();
    let Action::Retarget(epoch) = plan.action() else {
        panic!("native mature fixture required")
    };
    assert_eq!(plan.sample_heights().len(), 9);
    let heights = plan
        .sample_heights()
        .iter()
        .copied()
        .chain(std::iter::once(child_height))
        .collect::<Vec<_>>();
    let logical_to_copy = heights
        .iter()
        .enumerate()
        .map(|(copy, height)| (u64::from(*height - 1), copy))
        .collect();
    let samples = plan
        .sample_heights()
        .iter()
        .map(|height| headers.get(height).unwrap().as_slice())
        .collect::<Vec<_>>();
    let parent = headers.get(&(child_height - 1)).unwrap();
    let child = headers.get(&child_height).unwrap();
    let selected = daa_header_window::select_window(parent, child, &samples).unwrap();
    assert_eq!(selected.child_height(), child_height);
    let finish = daa_finish::compile_finish_with_child(
        epoch,
        &daa_count::q(),
        selected.prediction(),
        selected.child_nbits(),
        true,
    )
    .unwrap();
    let mapped = MappedDaaPlan::compile(&finish).unwrap();

    let _ = fixture;
    let serializer = serializer::build(None).unwrap();
    let mut child_daa = vec![Fr::zero(); COPY_LEN];
    for (copy, height) in heights.iter().enumerate() {
        let header = Header::decode(headers.get(height).unwrap(), None).unwrap();
        let fields = serializer::Fields::from_header(&header).unwrap();
        let assignment = serializer.assign(&fields);
        assert_eq!(assignment.len(), header_hash::SERIALIZER_WIDTH);
        let start = header_hash::SERIALIZER_OFFSET;
        if copy == 9 {
            child_daa[start..start + assignment.len()].copy_from_slice(&assignment);
            for (lo, hi) in mapped.phase_bank_ranges() {
                assert!(
                    hi <= start || lo >= start + assignment.len(),
                    "native phase bank overlaps serialized header"
                );
                child_daa[lo..hi].copy_from_slice(&mapped.witness()[lo..hi]);
            }
        }
    }
    (heights, logical_to_copy, headers, child_daa)
}

fn native_roster() -> (
    Vec<u32>,
    HashMap<u64, usize>,
    HashMap<u32, Vec<u8>>,
    Vec<Fr>,
) {
    native_roster_for(CHILD_HEIGHT)
}

fn translated_terms(terms: &[Term], roster: &HashMap<u64, usize>) -> Vec<Term> {
    terms
        .iter()
        .enumerate()
        .map(|(index, term)| {
            let mut term = term.clone();
            for endpoint in [&mut term.gate.left, &mut term.gate.right] {
                *endpoint =
                    roster[&((*endpoint >> LOCAL_BITS) as u64)] * COPY_LEN + (*endpoint % COPY_LEN);
            }
            term.row = index;
            term
        })
        .collect()
}

// Independent finite term sum, separate from the analytic consumer restriction.
fn explicit_coefficients(
    terms: &[Term],
    row_owner: usize,
    r: &[Fr],
    u: &[Fr],
    v: &[Fr],
) -> [Fr; 4] {
    let mut result = [Fr::zero(); 4];
    for term in terms {
        let weight = eq_at(&r[..ROW_BITS], term.row)
            * eq_at(&r[ROW_BITS..], row_owner)
            * eq_at(u, term.gate.left)
            * eq_at(v, term.gate.right);
        for (result, coefficient) in
            result
                .iter_mut()
                .zip([term.gate.c0, term.gate.c1, term.gate.c2, term.gate.c3])
        {
            *result += weight * coefficient;
        }
    }
    result
}

#[test]
fn physical_alias_emission_matches_all_native_fields_and_rejects_invalid_contexts() {
    use crate::daa_schedule_wiring::{DaaScheduleWiring, PortFamily};
    let wiring = DaaScheduleWiring::compile().unwrap();
    let serializer = serializer::build(None).unwrap();
    for (epoch, child) in [(Epoch::Legacy, 9_217u32), (Epoch::Eip, CHILD_HEIGHT)] {
        let (heights, roster, headers, child_input) = native_roster_for(child);
        let layout = DaaHistoryLayout::compile(epoch, N, SLOT_LOG).unwrap();
        let mut terms = Vec::new();
        assert_eq!(
            layout
                .visit_alias_terms(u64::from(child - 1), |term| {
                    terms.push(term);
                    Ok(())
                })
                .unwrap(),
            896
        );
        let decoded = heights
            .iter()
            .map(|height| ergo_header_core::Header::decode(&headers[height], None).unwrap())
            .collect::<Vec<_>>();
        let assignments = decoded
            .iter()
            .map(|header| serializer.assign(&serializer::Fields::from_header(header).unwrap()))
            .collect::<Vec<_>>();
        let mut family_counts = [0usize; 4];
        let mut mutated_classes = [false; 4];
        for (index, (term, port)) in terms.iter().zip(wiring.ports(epoch)).enumerate() {
            let (family, ordinal, bit, value, serializer_wire) = match port.family() {
                PortFamily::Timestamp => (
                    0,
                    port.field_index() / 64,
                    port.field_index() % 64,
                    decoded[port.field_index() / 64].timestamp as u64,
                    serializer.layout.fields.timestamp[port.field_index() % 64],
                ),
                PortFamily::SampleNBits => (
                    1,
                    port.field_index() / 32 + 1,
                    port.field_index() % 32,
                    u64::from(decoded[port.field_index() / 32 + 1].n_bits),
                    serializer.layout.fields.n_bits[port.field_index() % 32],
                ),
                PortFamily::X0Height => (
                    2,
                    1,
                    port.field_index(),
                    u64::from(decoded[1].height),
                    serializer.layout.fields.height[port.field_index()],
                ),
                PortFamily::ChildNBits => (
                    3,
                    9,
                    port.field_index() % 32,
                    u64::from(decoded[9].n_bits),
                    serializer.layout.fields.n_bits[port.field_index() % 32],
                ),
            };
            let expected = Fr::from((value >> bit) & 1);
            family_counts[family] += 1;
            let source_slot = u64::from(heights[ordinal] - 1);
            assert_eq!(u64::from(child - 1) - source_slot, port.offset(epoch));
            assert_eq!(term.row, (child as usize - 1) * 1024 + index);
            assert_eq!(
                term.gate.left,
                source_slot as usize * COPY_LEN + header_hash::SERIALIZER_OFFSET + serializer_wire
            );
            assert_eq!(term.gate.right / COPY_LEN, child as usize - 1);
            assert_eq!(
                [term.gate.c0, term.gate.c1, term.gate.c2, term.gate.c3],
                [Fr::zero(), Fr::one(), -Fr::one(), Fr::zero()]
            );
            assert_eq!(roster[&source_slot], ordinal);
            assert_eq!(assignments[ordinal][serializer_wire], expected);
            assert_eq!(child_input[term.gate.right % COPY_LEN], expected);
            if !mutated_classes[family] {
                let left = assignments[ordinal][serializer_wire];
                let right = child_input[term.gate.right % COPY_LEN];
                let evaluate = |left: Fr| {
                    term.gate.c0
                        + term.gate.c1 * left
                        + term.gate.c2 * right
                        + term.gate.c3 * left * right
                };
                assert!(
                    evaluate(left).is_zero(),
                    "honest emitted gate in native class {family}"
                );
                // Override only the actual emitted source bit; the right input
                // and every gate coefficient remain unchanged.
                let one_bit_fault = Fr::one() - left;
                assert!(
                    !evaluate(one_bit_fault).is_zero(),
                    "isolated native field class {family} must have nonzero residual"
                );
                mutated_classes[family] = true;
            }
        }
        assert_eq!(family_counts, [576, 256, 32, 32]);
        assert_eq!(mutated_classes, [true; 4]);
        for invalid in [
            0,
            8 * Epoch::Legacy.length(),
            417_792,
            CHILD_SLOT - 1,
            N,
            u64::MAX,
            if epoch == Epoch::Legacy {
                CHILD_SLOT
            } else {
                9_216
            },
        ] {
            let mut calls = 0;
            assert!(
                layout
                    .visit_alias_terms(invalid, |_| {
                        calls += 1;
                        Ok(())
                    })
                    .is_err(),
                "epoch {epoch:?} invalid slot {invalid}"
            );
            assert_eq!(calls, 0);
        }
        let mut calls = 0;
        assert_eq!(
            layout
                .visit_alias_terms(u64::from(child - 1), |_| {
                    calls += 1;
                    Err("sink sentinel".into())
                })
                .unwrap_err(),
            "sink sentinel"
        );
        assert_eq!(calls, 1);
    }
    assert!(DaaHistoryLayout::compile(Epoch::Eip, N, usize::MAX).is_err());
    assert!(DaaHistoryLayout::compile(Epoch::Eip, u64::MAX, SLOT_LOG).is_err());
}

#[test]
fn physical_alias_restriction_matches_asymmetric_and_boolean_points_with_isolated_mutants() {
    let heights = expected_heights().unwrap();
    let roster = heights
        .iter()
        .enumerate()
        .map(|(i, h)| (u64::from(*h - 1), i))
        .collect();
    let layout = DaaHistoryLayout::compile(Epoch::Eip, N, SLOT_LOG).unwrap();
    let mut global = Vec::new();
    layout
        .visit_alias_terms(CHILD_SLOT, |t| {
            global.push(t);
            Ok(())
        })
        .unwrap();
    let terms = translated_terms(&global, &roster);
    let r = (0..ROW_BITS + COPY_BITS)
        .map(|i| Fr::from((7 + i * 11) as u64))
        .collect::<Vec<_>>();
    let u = (0..INPUT_BITS)
        .map(|i| Fr::from((13 + i * 17) as u64))
        .collect::<Vec<_>>();
    let v = (0..INPUT_BITS)
        .map(|i| Fr::from((19 + i * 23) as u64))
        .collect::<Vec<_>>();
    let expected = wiring_restriction(&layout, &heights, &r, &u, &v).unwrap();
    assert_eq!(explicit_coefficients(&terms, 9, &r, &u, &v), expected);
    let mut omission = terms.clone();
    omission.remove(0);
    assert_ne!(explicit_coefficients(&omission, 9, &r, &u, &v), expected);
    assert_ne!(explicit_coefficients(&terms, 8, &r, &u, &v), expected);
    let mut orientation = terms.clone();
    let first = orientation[0].gate.c1;
    orientation[0].gate.c1 = orientation[0].gate.c2;
    orientation[0].gate.c2 = first;
    assert_ne!(explicit_coefficients(&orientation, 9, &r, &u, &v), expected);
    let mut wrong_roster = heights.clone();
    wrong_roster.swap(0, 1);
    assert_ne!(
        wiring_restriction(&layout, &wrong_roster, &r, &u, &v).unwrap(),
        expected
    );
    let boolean = |index: usize, width: usize| {
        (0..width)
            .map(|bit| Fr::from(((index >> bit) & 1) as u64))
            .collect::<Vec<_>>()
    };
    for index in [0, 575, 576, 831, 832, 863, 864, 895] {
        let term = &terms[index];
        let mut row = boolean(index, ROW_BITS);
        row.extend(boolean(9, COPY_BITS));
        let left = boolean(term.gate.left, INPUT_BITS);
        let right = boolean(term.gate.right, INPUT_BITS);
        assert_eq!(
            wiring_restriction(&layout, &heights, &row, &left, &right).unwrap(),
            [Fr::zero(), Fr::one(), -Fr::one(), Fr::zero()]
        );
        assert_eq!(
            explicit_coefficients(&terms, 9, &row, &left, &right),
            [Fr::zero(), Fr::one(), -Fr::one(), Fr::zero()]
        );
        for (bad_row, bad_left, bad_right) in [
            (
                boolean(index + 8 * 1024, ROW_BITS + COPY_BITS),
                left.clone(),
                right.clone(),
            ),
            (
                row.clone(),
                boolean(term.gate.left ^ COPY_LEN, INPUT_BITS),
                right.clone(),
            ),
            (
                row.clone(),
                left.clone(),
                boolean(term.gate.right ^ COPY_LEN, INPUT_BITS),
            ),
        ] {
            assert_eq!(
                wiring_restriction(&layout, &heights, &bad_row, &bad_left, &bad_right).unwrap(),
                [Fr::zero(); 4]
            );
            assert_eq!(
                explicit_coefficients(&terms, 9, &bad_row, &bad_left, &bad_right),
                [Fr::zero(); 4]
            );
        }
    }
}

#[test]
fn native_physical_alias_terms_stream_through_cross_slot_gkr_and_packed_pcs24() {
    let whole_started = Instant::now();
    let native_started = Instant::now();
    let (heights, logical_to_copy, headers, child_input) = native_roster();
    let layout = DaaHistoryLayout::compile(Epoch::Eip, N, SLOT_LOG).unwrap();
    assert_eq!(layout.import_count(), 896);
    let mut terms = Vec::with_capacity(896);
    let count = layout
        .visit_alias_terms(CHILD_SLOT, |term| {
            terms.push(term);
            Ok(())
        })
        .unwrap();
    assert_eq!(count, 896);
    assert!(terms
        .iter()
        .enumerate()
        .all(|(i, t)| t.row == CHILD_SLOT as usize * 1024 + i
            && t.gate.c0.is_zero()
            && t.gate.c1.is_one()
            && t.gate.c2 == -Fr::one()
            && t.gate.c3.is_zero()));
    let mut sink_calls = 0;
    assert!(layout
        .visit_alias_terms(CHILD_SLOT, |_| {
            sink_calls += 1;
            Err("sink stop".into())
        })
        .is_err());
    assert_eq!(sink_calls, 1);
    for invalid in [CHILD_SLOT - 1, N] {
        let mut calls = 0;
        assert!(layout
            .visit_alias_terms(invalid, |_| {
                calls += 1;
                Ok(())
            })
            .is_err());
        assert_eq!(calls, 0, "invalid context must reject before emission");
    }

    // Check the explicit coefficient sum against the independent global
    // restriction at asymmetric non-Boolean points, without equality tables.
    let r = (0..ROW_BITS + COPY_BITS)
        .map(|i| Fr::from((7 + i * 11) as u64))
        .collect::<Vec<_>>();
    let u = (0..INPUT_BITS)
        .map(|i| Fr::from((13 + i * 17) as u64))
        .collect::<Vec<_>>();
    let v = (0..INPUT_BITS)
        .map(|i| Fr::from((19 + i * 23) as u64))
        .collect::<Vec<_>>();
    let mut explicit = [Fr::zero(); 4];
    for (index, term) in terms.iter().enumerate() {
        let source_slot = (term.gate.left >> LOCAL_BITS) as u64;
        let source_copy = logical_to_copy[&source_slot];
        let w = eq_at(&r[..ROW_BITS], index)
            * eq_at(&r[ROW_BITS..], 9)
            * eq_at(&u[..LOCAL_BITS], term.gate.left & (COPY_LEN - 1))
            * eq_at(&u[LOCAL_BITS..], source_copy)
            * eq_at(&v[..LOCAL_BITS], term.gate.right & (COPY_LEN - 1))
            * eq_at(&v[LOCAL_BITS..], 9);
        explicit[1] += w;
        explicit[2] -= w;
    }
    let slot_point = |slot: u64| {
        (0..SLOT_LOG)
            .map(|bit| Fr::from((slot >> bit) & 1))
            .collect::<Vec<_>>()
    };
    let mut r_global = r[..ROW_BITS].to_vec();
    r_global.extend(slot_point(CHILD_SLOT));
    let mut v_global = v[..LOCAL_BITS].to_vec();
    v_global.extend(slot_point(CHILD_SLOT));
    let owner_mask = eq_at(&r[ROW_BITS..], 9) * eq_at(&v[LOCAL_BITS..], 9);
    let mut restricted = [Fr::zero(); 4];
    for (copy, height) in heights.iter().enumerate() {
        let mut u_global = u[..LOCAL_BITS].to_vec();
        u_global.extend(slot_point(u64::from(*height - 1)));
        let coefficients = layout
            .alias_coefficients(&r_global, &u_global, &v_global)
            .unwrap();
        let weight = owner_mask * eq_at(&u[LOCAL_BITS..], copy);
        for index in 0..4 {
            restricted[index] += weight * coefficients[index];
        }
    }
    assert_eq!(explicit, restricted);

    let native_ms = native_started.elapsed().as_millis();
    let packing_started = Instant::now();
    let packed_path = artifact_path("packed", "bin");
    let mut writer = PackedFileWriter::create_new(&packed_path, 24).unwrap();
    for copy in 0..10 {
        let mut values = vec![Fr::zero(); COPY_LEN];
        if copy == 9 {
            values.copy_from_slice(&child_input);
        } else {
            let height = heights[copy];
            let header =
                ergo_header_core::Header::decode(headers.get(&height).unwrap(), None).unwrap();
            let fields = serializer::Fields::from_header(&header).unwrap();
            let assignment = serializer::build(Some(&fields)).unwrap().input.unwrap();
            let start = header_hash::SERIALIZER_OFFSET;
            values[start..start + assignment.len()].copy_from_slice(&assignment);
        }
        writer.write_bytes(&pack_bits(&values)).unwrap();
    }
    for _ in 10..16 {
        writer.write_bytes(&vec![0u8; COPY_LEN / 8]).unwrap();
    }
    let source = writer.finish().unwrap();
    let packing_ms = packing_started.elapsed().as_millis();
    assert_eq!(source.input_len(), 1 << 24);
    let setup_started = Instant::now();
    let setup = pcs::generate_setup(24).unwrap();
    let setup_ms = setup_started.elapsed().as_millis();
    let commit_started = Instant::now();
    let committed = packed::commit(&source, &setup).unwrap();
    let commit_ms = commit_started.elapsed().as_millis();
    let commitment_bytes = pcs::encode_commitment(&committed.commitment).unwrap();
    let key_bytes = pcs::encode(&ArkworksVerifierSetup(setup.verifier.clone())).unwrap();
    let admitted = verifier_key::admit_generated_test_key(24, &key_bytes, setup.id).unwrap();

    let mut logical_terms = Vec::with_capacity(896);
    for (index, term) in terms.iter().enumerate() {
        let mut translated = term.clone();
        for endpoint in [&mut translated.gate.left, &mut translated.gate.right] {
            let logical_slot = (*endpoint >> LOCAL_BITS) as u64;
            let copy = logical_to_copy[&logical_slot];
            *endpoint = copy * COPY_LEN + (*endpoint & (COPY_LEN - 1));
        }
        translated.row = index;
        logical_terms.push(translated);
    }
    let mut io_calls = 0usize;
    let mut loader_calls = 0usize;
    source.reset_io_metrics();
    let gkr_started = Instant::now();
    let mut transcript = Transcript::new(DOMAIN);
    let (proof, claim, incremental_u, incremental_v) = sparse_stream_roster::prove_edge_terms(
        LOCAL_BITS,
        COPY_BITS,
        ROW_BITS,
        FAMILY_BITS,
        &[10],
        |left, endpoint_copy, sink| {
            for (index, term) in logical_terms.iter().enumerate() {
                let endpoint = if left {
                    term.gate.left
                } else {
                    term.gate.right
                };
                if endpoint / COPY_LEN == endpoint_copy {
                    sink(EdgeTerm {
                        source_slot: 9,
                        family_row: index,
                        term: term.clone(),
                    })?;
                }
            }
            Ok(())
        },
        |copy| {
            loader_calls += 1;
            let mut values = Vec::with_capacity(COPY_LEN);
            for chunk in 0..CHUNKS_PER_COPY {
                io_calls += 1;
                values.extend(source.read_copy(CHUNK, copy * CHUNKS_PER_COPY + chunk)?);
            }
            Ok(values)
        },
        &mut transcript,
        |t| alias_statement(t, &setup.id, &commitment_bytes),
        |r, u, v| wiring_restriction(&layout, &heights, r, u, v),
    )
    .unwrap();
    let gkr_ms = gkr_started.elapsed().as_millis();
    let gkr_io = source.io_metrics_snapshot();
    assert_eq!(logical_terms.len(), 896);
    assert!(
        io_calls >= 16,
        "packed witness was consumed in bounded chunks"
    );
    assert_eq!(io_calls, loader_calls * CHUNKS_PER_COPY);
    assert_eq!(gkr_io.read_calls, io_calls as u64);
    assert_eq!(gkr_io.read_bytes, (io_calls * CHUNK / 8) as u64);

    let verifier_started = Instant::now();
    let (verified, mut verifier_transcript) =
        verifier_claim(&proof, &setup.id, &commitment_bytes, &layout).unwrap();
    let verifier_ms = verifier_started.elapsed().as_millis();
    assert_eq!(verified, claim);
    let mut wrong_context = Transcript::new(DOMAIN);
    assert_eq!(
        gkr::verify_with_wiring(
            &[INPUT_BITS],
            1 << (ROW_BITS + COPY_BITS),
            &proof,
            &mut wrong_context,
            |t| alias_statement_with_history(t, &setup.id, &commitment_bytes, N - 1),
            |_layer, r, u, v| wiring_restriction(&layout, &heights, r, u, v)
                .map_err(|_| gkr::GkrError::PointDimension)
        )
        .unwrap_err(),
        gkr::GkrError::SumcheckIdentity
    );
    assert_eq!(
        transcript.clone().challenge_scalar(b"post-gkr-check"),
        verifier_transcript
            .clone()
            .challenge_scalar(b"post-gkr-check")
    );
    // Each consumer mutation starts at the identical pre-GKR transcript and
    // changes only its named coefficient boundary, without changing proof data.
    let mut omitted = logical_terms.clone();
    omitted.remove(0);
    let mut reversed = logical_terms.clone();
    reversed[0].gate.c1 = -Fr::one();
    reversed[0].gate.c2 = Fr::one();
    for (label, mutants, owner) in [
        ("omission", &omitted, 9),
        ("row-owner", &logical_terms, 8),
        ("orientation", &reversed, 9),
    ] {
        let mut mutant = Transcript::new(DOMAIN);
        assert_eq!(
            gkr::verify_with_wiring(
                &[INPUT_BITS],
                1 << (ROW_BITS + COPY_BITS),
                &proof,
                &mut mutant,
                |t| alias_statement(t, &setup.id, &commitment_bytes),
                |_layer, r, u, v| Ok(explicit_coefficients(mutants, owner, r, u, v))
            )
            .unwrap_err(),
            gkr::GkrError::TerminalExpression,
            "{label}"
        );
    }
    let mut changed_roster = heights.clone();
    changed_roster.swap(0, 1);
    let mut roster_transcript = Transcript::new(DOMAIN);
    assert_eq!(
        gkr::verify_with_wiring(
            &[INPUT_BITS],
            1 << (ROW_BITS + COPY_BITS),
            &proof,
            &mut roster_transcript,
            |t| alias_statement(t, &setup.id, &commitment_bytes),
            |_layer, r, u, v| wiring_restriction(&layout, &changed_roster, r, u, v)
                .map_err(|_| gkr::GkrError::PointDimension)
        )
        .unwrap_err(),
        gkr::GkrError::TerminalExpression
    );
    let mle_started = Instant::now();
    let packed_value = source.evaluate(&claim.point).unwrap();
    let mle_ms = mle_started.elapsed().as_millis();
    assert_eq!(packed_value, claim.value);
    let mut open_transcript = transcript.clone();
    let pre_pcs_transcript = verifier_transcript.clone();
    let opening_started = Instant::now();
    let opening = packed::open(
        &committed,
        &source,
        &claim.point,
        &setup,
        &mut open_transcript,
    )
    .unwrap();
    let opening_ms = opening_started.elapsed().as_millis();
    let pcs_verify_started = Instant::now();
    pcs::verify_admitted(
        committed.commitment.clone(),
        claim.value,
        &claim.point,
        &opening,
        &admitted,
        &mut verifier_transcript,
    )
    .unwrap();
    let pcs_verify_ms = pcs_verify_started.elapsed().as_millis();
    assert_eq!(
        open_transcript.challenge_scalar(b"post-pcs-check"),
        verifier_transcript.challenge_scalar(b"post-pcs-check")
    );

    let mut wrong_value_transcript = pre_pcs_transcript;
    assert!(pcs::verify_admitted(
        committed.commitment.clone(),
        claim.value + Fr::one(),
        &claim.point,
        &opening,
        &admitted,
        &mut wrong_value_transcript
    )
    .is_err());
    let mut wrong_commitment = commitment_bytes.clone();
    wrong_commitment[0] ^= 1;
    assert!(verifier_claim(&proof, &setup.id, &wrong_commitment, &layout).is_err());
    let causal_index = logical_terms
        .iter()
        .position(|term| {
            let left = term.gate.left;
            let copy = left / COPY_LEN;
            let wire = left % COPY_LEN;
            let original = source
                .read_copy(CHUNK, copy * CHUNKS_PER_COPY + wire / CHUNK)
                .unwrap()[wire % CHUNK];
            let adjacent = source
                .read_copy(CHUNK, copy * CHUNKS_PER_COPY + (wire ^ 1) / CHUNK)
                .unwrap()[(wire ^ 1) % CHUNK];
            original != adjacent
        })
        .expect("one causal native adjacent-bit edge fault");
    let mut mutant_transcript = Transcript::new(DOMAIN);
    let false_edge = sparse_stream_roster::prove_edge_terms(
        LOCAL_BITS,
        COPY_BITS,
        ROW_BITS,
        FAMILY_BITS,
        &[10],
        |left, endpoint_copy, sink| {
            for (index, term) in logical_terms.iter().enumerate() {
                let mut term = term.clone();
                if index == causal_index {
                    term.gate.left ^= 1;
                }
                let endpoint = if left {
                    term.gate.left
                } else {
                    term.gate.right
                };
                if endpoint / COPY_LEN == endpoint_copy {
                    sink(EdgeTerm {
                        source_slot: 9,
                        family_row: index,
                        term,
                    })?;
                }
            }
            Ok(())
        },
        |copy| {
            let mut values = Vec::with_capacity(COPY_LEN);
            for chunk in 0..CHUNKS_PER_COPY {
                values.extend(source.read_copy(CHUNK, copy * CHUNKS_PER_COPY + chunk)?);
            }
            Ok(values)
        },
        &mut mutant_transcript,
        |t| alias_statement(t, &setup.id, &commitment_bytes),
        |r, u, v| wiring_restriction(&layout, &heights, r, u, v),
    );
    assert_eq!(
        false_edge.unwrap_err(),
        gkr::GkrError::SumcheckIdentity.to_string(),
        "isolated false equality must fail during edge sumcheck"
    );

    let proof_path = artifact_path("gkr", "bin");
    write_create_new(&proof_path, &gkr::encode_proof(&proof).unwrap());
    let pcs_path = artifact_path("pcs", "bin");
    write_create_new(&pcs_path, &pcs::encode_proof(&opening).unwrap());
    let key_path = artifact_path("test-key", "bin");
    write_create_new(&key_path, &key_bytes);
    let receipt_path = artifact_path("receipt", "json");
    let receipt = serde_json::json!({"profile":"native EIP physical alias edge diagnostic","child":CHILD_HEIGHT,"N":N,"slot_log":SLOT_LOG,"copies":16,"active_copies":10,"terms":count,"packed_log":24,"packed_bytes":2*1024*1024,"loader_calls":loader_calls,"packed_chunk_reads":io_calls,"packed_read_bytes":gkr_io.read_bytes,"incremental_u":incremental_u,"incremental_v":incremental_v,"native_ms":native_ms,"packing_ms":packing_ms,"setup_ms":setup_ms,"commit_ms":commit_ms,"gkr_ms":gkr_ms,"verifier_ms":verifier_ms,"mle_ms":mle_ms,"opening_ms":opening_ms,"pcs_verify_ms":pcs_verify_ms,"whole_ms":whole_started.elapsed().as_millis(),"causal_fault_port":causal_index,"setup_id":setup.id.iter().map(|b|format!("{b:02x}")).collect::<String>(),"proof_bytes":gkr::encode_proof(&proof).unwrap().len(),"pcs_bytes":pcs::encode_proof(&opening).unwrap().len(),"authority_ceiling":"bounded physical import diagnostic only; no authenticated RAW history or release claim"});
    println!("{receipt}");
    write_create_new(&receipt_path, receipt.to_string().as_bytes());
    drop(source);
}

#[path = "common_owner_join_tests.rs"]
mod common_owner_join_tests;

//! Test-only N1984 Map projection into one log31 commitment.
//! The public circuit builder has no witness or frozen-bundle dependency.
use super::*;
use ark_ff::{Field, One, Zero};
use blake2::{Blake2b512, Digest};
use crate::bank53_map::map_owner_terms;
use crate::legacy_envelope_map::{LowerBranch, LowerSelector, LowerSource, Map};
use crate::packed_owner_assembly::same_x_stage1b_n1984_fixture;
use crate::work_tree_history_plan::WorkTreeHistoryPlan;
use std::collections::BTreeMap;

const N: u64 = 1984;
const SLOT_LOG: usize = 11;
const GLOBAL_LOG: usize = 31;
const WIRE_LOG: usize = 20;
const WIRE_COUNT: usize = 1 << WIRE_LOG;
const OWNER_BYTES: usize = WIRE_COUNT / 8;
const LOCAL_LOG: usize = 22;
const ROW_COUNT: usize = 1 << 19;
const MAP_OWNER: usize = 1983;
const ROW_BASE: usize = MAP_OWNER * ROW_COUNT;
const MAP_ROW_START: usize = 409_600;
const MAP_ROW_END: usize = MAP_ROW_START + crate::bank53_map::MAP_ROW_STRIDE;
const Q1: u64 = 22_538_929_735_599;
const Q1_WIRE_START: usize = 677_223;
const PROFILE_MAGIC: &[u8; 8] = b"XS1BPROF";
const PROFILE_BYTES: usize = 8 + 1 + 8 + 8 + 32 + 28 + 8;
const KEY_MAGIC: &[u8; 8] = b"XS1BKEY1";
const KEY_PIN_BYTES: usize = 8 + 8 + 64 + 32;
const PROFILE_FILE: &str = "same-x-stage1b-public-profile.bin";
const KEY_FILE: &str = "same-x-stage1b-key.pin";
const CONTROL_DIR_ENV: &str = "NIPOPOW_STAGE1B_CONTROL_DIR";
const DESCRIPTOR_TAG: &[u8] = b"nipopow-same-x-n1984-map-stage1b-descriptor-v1";
const F_DESCRIPTOR_TAG: &[u8] = b"nipopow-same-x-n1984-filtered-f-stage1b-descriptor-v1";

#[derive(Clone, Debug, PartialEq, Eq)]
struct PublicProfile {
    root: [u8; 32],
    total_be28: [u8; 28],
    q1: u64,
}

fn encode_profile(profile: &PublicProfile) -> [u8; PROFILE_BYTES] {
    let mut out = [0u8; PROFILE_BYTES];
    out[..8].copy_from_slice(PROFILE_MAGIC);
    out[8] = 1;
    out[9..17].copy_from_slice(&N.to_le_bytes());
    out[17..25].copy_from_slice(&(SLOT_LOG as u64).to_le_bytes());
    out[25..57].copy_from_slice(&profile.root);
    out[57..85].copy_from_slice(&profile.total_be28);
    out[85..93].copy_from_slice(&profile.q1.to_le_bytes());
    out
}

fn decode_profile(bytes: &[u8]) -> Result<PublicProfile, String> {
    if bytes.len() != PROFILE_BYTES || &bytes[..8] != PROFILE_MAGIC || bytes[8] != 1 {
        return Err("Stage1b profile framing rejected".into());
    }
    if u64::from_le_bytes(bytes[9..17].try_into().unwrap()) != N
        || u64::from_le_bytes(bytes[17..25].try_into().unwrap()) != SLOT_LOG as u64 {
        return Err("Stage1b profile dimension rejected".into());
    }
    let mut root = [0u8; 32];
    root.copy_from_slice(&bytes[25..57]);
    let mut total_be28 = [0u8; 28];
    total_be28.copy_from_slice(&bytes[57..85]);
    let q1 = u64::from_le_bytes(bytes[85..93].try_into().unwrap());
    if q1 != Q1 { return Err("Stage1b public q1 rejected".into()); }
    let profile = PublicProfile { root, total_be28, q1 };
    if encode_profile(&profile).as_slice() != bytes {
        return Err("Stage1b noncanonical public profile".into());
    }
    Ok(profile)
}

fn push_u64(out: &mut Vec<u8>, value: usize) {
    out.extend_from_slice(&(value as u64).to_le_bytes());
}

fn checked_rebase(original: &[sparse::Term]) -> Result<Vec<sparse::Term>, String> {
    let mut destinations = BTreeMap::<usize, usize>::new();
    let mut rebased = Vec::with_capacity(original.len());
    for term in original {
        let mut next = term.clone();
        next.row = next.row.checked_sub(ROW_BASE).ok_or("Stage1b row below owner base")?;
        if !(MAP_ROW_START..MAP_ROW_END).contains(&next.row) {
            return Err("Stage1b Map row outside context 0".into());
        }
        for wire in [&mut next.gate.left, &mut next.gate.right] {
            let source = *wire;
            let owner = source / WIRE_COUNT;
            let local = source % WIRE_COUNT;
            let slot = match owner {
                1023 => 0,
                1982 => 1,
                1983 => 2,
                _ => return Err(format!("Stage1b source owner outside census: {owner}")),
            };
            let destination = slot * WIRE_COUNT + local;
            if let Some(previous) = destinations.insert(destination, source) {
                if previous != source { return Err("Stage1b rebase collision".into()); }
            }
            *wire = destination;
        }
        rebased.push(next);
    }
    Ok(rebased)
}

fn public_circuit(profile: &PublicProfile) -> Result<(Vec<u8>, sparse::Circuit, Vec<sparse::Term>), String> {
    // No NativePrefix, source row or packed file is reachable from this builder.
    let plan = WorkTreeHistoryPlan::compile(N, SLOT_LOG, profile.root, profile.total_be28)?;
    let map = Map::from_parent_modern_global_u(
        &plan, 47,
        LowerSelector { source: LowerSource::Reset417792, branch: LowerBranch::Literal },
    )?;
    let original = map_owner_terms(&map, MAP_OWNER as u64, 0)?;
    let mut terms = checked_rebase(&original)?;
    for bit_index in 0..92 {
        let wire = 2 * WIRE_COUNT + Q1_WIRE_START + bit_index;
        let expected = (profile.q1 >> bit_index.min(63)) & 1;
        let expected = if bit_index >= 64 { 0 } else { expected };
        terms.push(sparse::Term {
            row: bit_index,
            gate: gkr::Gate {
                left: wire, right: wire,
                c0: -Fr::from(expected), c1: Fr::one(), c2: Fr::zero(), c3: Fr::zero(),
            },
        });
    }
    let circuit = sparse::Circuit { input_len: 1 << LOCAL_LOG, row_count: ROW_COUNT, terms };
    sparse::validate(&circuit, 0).map_err(|e| format!("Stage1b circuit shape: {e:?}"))?;

    // The descriptor binds the exact public context and a canonical digest
    // of every row, input wire and field coefficient. GKR additionally binds
    // the full circuit through sparse::bind before its first challenge.
    let mut descriptor = Vec::new();
    descriptor.extend_from_slice(DESCRIPTOR_TAG);
    descriptor.push(0);
    descriptor.extend_from_slice(&encode_profile(profile));
    for value in [GLOBAL_LOG, WIRE_LOG, LOCAL_LOG, ROW_COUNT, MAP_OWNER, 0, 47, 417_792,
        MAP_ROW_START, MAP_ROW_END, Q1_WIRE_START, 92] {
        push_u64(&mut descriptor, value);
    }
    descriptor.extend_from_slice(b"modern-global-u-selected-lower/literal/context0");
    for (owner, slot) in [(1023usize, 0usize), (1982, 1), (1983, 2)] {
        push_u64(&mut descriptor, owner);
        push_u64(&mut descriptor, slot);
    }
    push_u64(&mut descriptor, 3); // local slot 3 is the synthetic zero slice
    push_u64(&mut descriptor, circuit.terms.len());
    let mut canonical_terms = Vec::with_capacity(circuit.terms.len() * 152);
    for term in &circuit.terms {
        for index in [term.row, term.gate.left, term.gate.right] {
            push_u64(&mut canonical_terms, index);
        }
        for coefficient in [term.gate.c0, term.gate.c1, term.gate.c2, term.gate.c3] {
            coefficient.serialize_compressed(&mut canonical_terms)
                .map_err(|e| format!("Stage1b term coefficient codec: {e}"))?;
        }
    }
    descriptor.extend_from_slice(&Blake2b::<U32>::digest(&canonical_terms));
    Ok((descriptor, circuit, original))
}

fn canonical_term_digest(terms: &[sparse::Term]) -> Result<[u8; 32], String> {
    let mut canonical = Vec::with_capacity(terms.len().saturating_mul(152));
    for term in terms {
        for index in [term.row, term.gate.left, term.gate.right] {
            push_u64(&mut canonical, index);
        }
        for coefficient in [term.gate.c0, term.gate.c1, term.gate.c2, term.gate.c3] {
            coefficient.serialize_compressed(&mut canonical)
                .map_err(|e| format!("Stage1b term coefficient codec: {e}"))?;
        }
    }
    Ok(Blake2b::<U32>::digest(&canonical).into())
}

fn filtered_f_public_circuit(
    profile: &PublicProfile,
) -> Result<(Vec<u8>, sparse::Circuit, Vec<sparse::Term>), String> {
    let plan = WorkTreeHistoryPlan::compile(N, SLOT_LOG, profile.root, profile.total_be28)?;
    let map = Map::from_parent_modern_global_u(
        &plan, 47,
        LowerSelector { source: LowerSource::Reset417792, branch: LowerBranch::Literal },
    )?;
    let imports = map.imports(MAP_OWNER as u64)?;
    let mut filtered = map.filtered_terms(MAP_OWNER as u64)?;
    let filtered_digest = canonical_term_digest(&filtered)?;

    // Map.filtered_terms uses owner * 16384 + local. Place those rows in
    // Bank53 context 0 before checked_rebase validates the physical lane.
    let abstract_row_base = MAP_OWNER.checked_mul(1 << 14)
        .ok_or("Stage1b F abstract row base overflow")?;
    let physical_owner_base = MAP_OWNER.checked_mul(ROW_COUNT)
        .ok_or("Stage1b F physical owner base overflow")?;
    let context_row_base = 409_600usize;
    let map_row_stride = 1 << 14;
    for term in &mut filtered {
        let row_owner = term.row.checked_div(1 << 14)
            .ok_or("Stage1b F abstract row owner division")?;
        let local = term.row.checked_sub(abstract_row_base)
            .ok_or("Stage1b F row below abstract owner base")?;
        if row_owner != MAP_OWNER || local >= map_row_stride {
            return Err("Stage1b F abstract row outside owner coordinates".into());
        }
        term.row = physical_owner_base.checked_add(context_row_base)
            .and_then(|base| base.checked_add(local))
            .ok_or("Stage1b F physical context-0 row overflow")?;
    }

    let mut terms = checked_rebase(&filtered)?;
    for bit_index in 0..92 {
        let wire = 2 * WIRE_COUNT + Q1_WIRE_START + bit_index;
        let expected = if bit_index >= 64 { 0 } else { (profile.q1 >> bit_index) & 1 };
        terms.push(sparse::Term {
            row: bit_index,
            gate: gkr::Gate {
                left: wire, right: wire,
                c0: -Fr::from(expected), c1: Fr::one(), c2: Fr::zero(), c3: Fr::zero(),
            },
        });
    }
    let circuit = sparse::Circuit { input_len: 1 << LOCAL_LOG, row_count: ROW_COUNT, terms };
    sparse::validate(&circuit, 0).map_err(|e| format!("Stage1b F circuit shape: {e:?}"))?;

    let mut descriptor = Vec::new();
    descriptor.extend_from_slice(F_DESCRIPTOR_TAG);
    descriptor.push(0);
    descriptor.extend_from_slice(&encode_profile(profile));
    for value in [GLOBAL_LOG, WIRE_LOG, LOCAL_LOG, ROW_COUNT, MAP_OWNER, 0, 47, 417_792,
        MAP_ROW_START, MAP_ROW_END, 1 << 14, 524_288, 409_600, 671_744, 5_757, 8_192,
        Q1_WIRE_START, 92] {
        push_u64(&mut descriptor, value);
    }
    descriptor.extend_from_slice(b"modern-global-u-selected-lower/literal/context0/filtered-f");
    for (owner, slot) in [(1023usize, 0usize), (1982, 1), (1983, 2)] {
        push_u64(&mut descriptor, owner);
        push_u64(&mut descriptor, slot);
    }
    push_u64(&mut descriptor, 3); // local slot 3 is the synthetic zero slice
    push_u64(&mut descriptor, imports.len());
    for import in imports {
        let slot = match import.owner {
            1023 => 0,
            1982 => 1,
            1983 => 2,
            _ => return Err(format!("Stage1b F typed import owner outside slots: {}", import.owner)),
        };
        push_u64(&mut descriptor, import.owner as usize);
        push_u64(&mut descriptor, slot);
        push_u64(&mut descriptor, import.local);
        push_u64(&mut descriptor, import.width);
        push_u64(&mut descriptor, match import.kind {
            crate::legacy_envelope_map::Kind::Difficulty => 0,
            crate::legacy_envelope_map::Kind::Timestamp => 1,
        });
    }
    push_u64(&mut descriptor, filtered.len());
    descriptor.extend_from_slice(&filtered_digest);
    push_u64(&mut descriptor, circuit.terms.len());
    descriptor.extend_from_slice(&canonical_term_digest(&circuit.terms)?);
    Ok((descriptor, circuit, filtered))
}

fn packed_bit(bytes: &[u8], index: usize) -> Result<Fr, String> {
    let byte = bytes.get(index / 8).ok_or("Stage1b packed bit out of bounds")?;
    Ok(Fr::from(((byte >> (index % 8)) & 1) as u64))
}

fn residuals(terms: &[sparse::Term], mut read: impl FnMut(usize) -> Result<Fr, String>)
    -> Result<BTreeMap<usize, Fr>, String> {
    let mut sums = BTreeMap::<usize, Fr>::new();
    for term in terms {
        let gate = &term.gate;
        let left = if gate.c1.is_zero() && gate.c3.is_zero() { Fr::zero() } else { read(gate.left)? };
        let right = if gate.c2.is_zero() && gate.c3.is_zero() { Fr::zero() } else { read(gate.right)? };
        let value = gate.c0 + gate.c1 * left + gate.c2 * right + gate.c3 * left * right;
        *sums.entry(term.row).or_insert(Fr::zero()) += value;
    }
    Ok(sums)
}

fn fold_slice(bytes: &[u8], point: &[Fr]) -> Result<Fr, String> {
    if bytes.len() != OWNER_BYTES || point.len() != WIRE_LOG {
        return Err("Stage1b slice MLE shape".into());
    }
    let mut values = (0..WIRE_COUNT).map(|wire| packed_bit(bytes, wire)).collect::<Result<Vec<_>,_>>()?;
    for coordinate in point {
        let half = values.len() / 2;
        for index in 0..half {
            values[index] = values[2 * index] * (Fr::one() - coordinate)
                + values[2 * index + 1] * coordinate;
        }
        values.truncate(half);
    }
    Ok(values[0])
}

fn fold_local_y(bytes: &[u8], point: &[Fr]) -> Result<Fr, String> {
    if bytes.len() != 4 * OWNER_BYTES || point.len() != LOCAL_LOG {
        return Err("Stage1b local Y MLE shape".into());
    }
    let mut values = (0..(1 << LOCAL_LOG))
        .map(|wire| packed_bit(bytes, wire)).collect::<Result<Vec<_>,_>>()?;
    for coordinate in point {
        let half = values.len() / 2;
        for index in 0..half {
            values[index] = values[2 * index] * (Fr::one() - coordinate)
                + values[2 * index + 1] * coordinate;
        }
        values.truncate(half);
    }
    Ok(values[0])
}

fn virtual_global_x_mle(slices: &[Vec<u8>; 3], point: &[Fr]) -> Result<Fr, String> {
    if point.len() != GLOBAL_LOG { return Err("Stage1b global X MLE shape".into()); }
    let mut result = Fr::zero();
    for (slot, owner) in [1023usize, 1982, 1983].iter().enumerate() {
        let slice_value = fold_slice(&slices[slot], &point[..WIRE_LOG])?;
        let owner_weight = point[WIRE_LOG..].iter().enumerate().fold(Fr::one(), |weight,(bit,r)| {
            weight * if (owner >> bit) & 1 == 1 { *r } else { Fr::one() - r }
        });
        result += owner_weight * slice_value;
    }
    Ok(result)
}

fn global_point(wire_point: &[Fr], owner: usize) -> Vec<Fr> {
    let mut point = wire_point.to_vec();
    point.extend((0..SLOT_LOG).map(|bit| Fr::from(((owner >> bit) & 1) as u64)));
    point
}

fn control_dir() -> PathBuf {
    let dir = PathBuf::from(std::env::var_os(CONTROL_DIR_ENV).expect("Stage1b control directory env absent"));
    assert!(dir.is_absolute() && dir.is_dir(), "Stage1b control directory must preexist");
    dir
}

fn write_control_new(name: &str, bytes: &[u8]) {
    let path = control_dir().join(name);
    let mut file = OpenOptions::new().write(true).create_new(true).open(&path)
        .expect("fresh Stage1b control file");
    file.write_all(bytes).expect("complete Stage1b control file");
    file.sync_all().expect("durable Stage1b control file");
}

#[test]
fn same_x_log31_stage1b_filtered_f_phase_a() {
    let fixture = same_x_stage1b_n1984_fixture().expect("frozen N1984 owner fixture");
    let profile = PublicProfile {root: fixture.root, total_be28: fixture.total, q1: fixture.q1};
    let (map_descriptor, map_circuit, _) = public_circuit(&profile).expect("Map Stage1b circuit");
    let (f_descriptor, f_circuit, filtered) =
        filtered_f_public_circuit(&profile).expect("filtered F Stage1b circuit");
    sparse::validate(&f_circuit, 0).expect("F circuit validates");
    assert_ne!(map_descriptor, f_descriptor, "F relation descriptor must differ from Map");
    let map_id = same_x_smoke_corpus_id(&map_descriptor);
    let f_id = same_x_smoke_corpus_id(&f_descriptor);
    assert_ne!(map_id, f_id, "F relation corpus ID must differ from Map");
    let map_as_f = stage1b_admit_gkr(GLOBAL_LOG, Some(map_id), &f_descriptor,
        &f_circuit, &[0]).err().expect("Map corpus rejection");
    let f_as_map = stage1b_admit_gkr(GLOBAL_LOG, Some(f_id), &map_descriptor,
        &map_circuit, &[0]).err().expect("F corpus rejection");
    assert!(map_as_f.contains("descriptor/corpus"), "Map corpus fails F admission first");
    assert!(f_as_map.contains("descriptor/corpus"), "F corpus fails Map admission first");
    let decoder_error = stage1b_admit_gkr(GLOBAL_LOG, Some(f_id), &f_descriptor,
        &f_circuit, &[0]).err().expect("malformed GKR rejection");
    assert!(!decoder_error.contains("descriptor/corpus"),
        "with the correct F corpus, the same malformed bytes reach the GKR decoder");
    assert_ne!(map_as_f, decoder_error, "cross-corpus rejection precedes GKR decoding");

    assert!(filtered.iter().all(|term| term.row >= ROW_BASE + MAP_ROW_START
        && term.row < ROW_BASE + MAP_ROW_END), "F rows translated to Bank53 context 0");
    let own_packed_helpers = filtered.iter().flat_map(|term| [term.gate.left, term.gate.right])
        .filter_map(|index| {
            let owner = index / WIRE_COUNT;
            let local = index % WIRE_COUNT;
            (owner == MAP_OWNER && (671_744..671_744 + 8_192).contains(&local)).then_some(local)
        }).collect::<Vec<_>>();
    assert!(!own_packed_helpers.is_empty(), "F fixture must consume packed helpers");
    assert!(own_packed_helpers.iter().all(|local| (671_744..671_744 + 5_757).contains(local)),
        "F helper wires use the writer's packed 671744 lane");

    let source = residuals(&filtered, |index| {
        let owner = index / WIRE_COUNT;
        let slot = match owner {
            1023 => 0,
            1982 => 1,
            1983 => 2,
            _ => return Err("F original owner outside census".into()),
        };
        packed_bit(&fixture.owner_slices[slot], index % WIRE_COUNT)
    }).expect("F source residuals");
    let mut y = vec![0u8; 4 * OWNER_BYTES];
    for (slot, slice) in fixture.owner_slices.iter().enumerate() {
        assert_eq!(slice.len(), OWNER_BYTES);
        y[slot * OWNER_BYTES..(slot + 1) * OWNER_BYTES].copy_from_slice(slice);
    }
    assert!(y[3 * OWNER_BYTES..].iter().all(|byte| *byte == 0), "fourth input slot is synthetic zero");
    let rebased = residuals(&f_circuit.terms, |index| packed_bit(&y, index))
        .expect("F rebased residuals");
    assert!(source.values().all(|value| value.is_zero()), "fixture satisfies original F residuals");
    assert!(rebased.values().all(|value| value.is_zero()), "fixture satisfies rebased F residuals");
    assert_eq!(source.len() + 92, rebased.len(), "q1 pin rows are disjoint from F rows");
    for (row, residual) in &source {
        assert_eq!(rebased[&(row - ROW_BASE)], *residual, "F original/rebased residual parity");
    }

    let mut changed_y = y.clone();
    changed_y[(2 * WIRE_COUNT + Q1_WIRE_START) / 8] ^= 1 << (Q1_WIRE_START % 8);
    let changed = residuals(&f_circuit.terms, |index| packed_bit(&changed_y, index))
        .expect("mutated F residuals");
    assert_ne!(changed[&0], Fr::zero(), "one q1 helper bit fails its pin row");
}

#[test]
#[ignore = "N1984 host-only pre-PACK gate; frozen fixture, no setup or PCS"]
fn same_x_log31_stage1b_prepack_preflight() {
    let fixture = same_x_stage1b_n1984_fixture().expect("frozen N1984 owner fixture");
    let profile = PublicProfile {root: fixture.root, total_be28: fixture.total, q1: fixture.q1};
    let profile_bytes = encode_profile(&profile);
    assert_eq!(decode_profile(&profile_bytes).unwrap(), profile);
    assert!(decode_profile(&profile_bytes[..PROFILE_BYTES-1]).is_err());
    let mut extra = profile_bytes.to_vec(); extra.push(0);
    assert!(decode_profile(&extra).is_err());
    let mut bad_q1 = profile_bytes; bad_q1[85] ^= 1;
    assert!(decode_profile(&bad_q1).is_err(), "public q1 substitution rejected");

    let (descriptor, circuit, original) = public_circuit(&profile).expect("independent public Map circuit");
    assert_eq!(original, fixture.original_map_terms, "public Map terms differ from producer terms");
    assert!(original.iter().all(|term| term.row >= ROW_BASE + MAP_ROW_START
        && term.row < ROW_BASE + MAP_ROW_END));
    let mut reserved_row = original[0].clone();
    reserved_row.row = ROW_BASE + MAP_ROW_END;
    assert!(checked_rebase(&[reserved_row]).unwrap_err().contains("outside context 0"),
        "context-0 reserved half-lane must reject");
    assert!(circuit.terms[original.len()..].iter().enumerate().all(|(bit, term)|
        term.row == bit && term.gate.left == 2*WIRE_COUNT + Q1_WIRE_START + bit));

    let mut y = vec![0u8; 4 * OWNER_BYTES];
    for (slot, slice) in fixture.owner_slices.iter().enumerate() {
        assert_eq!(slice.len(), OWNER_BYTES);
        y[slot*OWNER_BYTES..(slot+1)*OWNER_BYTES].copy_from_slice(slice);
    }
    assert!(y[3*OWNER_BYTES..].iter().all(|byte| *byte == 0));
    let source = residuals(&original, |index| {
        let owner = index / WIRE_COUNT;
        let slot = match owner {1023=>0,1982=>1,1983=>2,_=>return Err("original owner outside census".into())};
        packed_bit(&fixture.owner_slices[slot], index % WIRE_COUNT)
    }).unwrap();
    let rebased = residuals(&circuit.terms, |index| packed_bit(&y, index)).unwrap();
    assert!(source.values().all(|value| value.is_zero()));
    assert!(rebased.values().all(|value| value.is_zero()));
    assert_eq!(source.len() + 92, rebased.len(), "q1 pin rows must be disjoint");
    for (row, residual) in &source {
        assert_eq!(rebased[&(row-ROW_BASE)], *residual, "original/rebased residual parity");
    }
    let mut changed_y = y.clone(); changed_y[(2*WIRE_COUNT+Q1_WIRE_START)/8] ^= 1 << (Q1_WIRE_START%8);
    let changed = residuals(&circuit.terms, |index| packed_bit(&changed_y,index)).unwrap();
    assert_ne!(changed[&0], Fr::zero(), "one q1 helper bit must fail its own pin row");

    let inverse_97 = Fr::from(97u64).inverse().unwrap();
    let wire_point = (0..WIRE_LOG).map(|i| Fr::from((i+2) as u64)*inverse_97).collect::<Vec<_>>();
    let t0 = Fr::from(7u64)*inverse_97;
    let t1 = Fr::from(19u64)*inverse_97;
    let mut local_point = wire_point.clone(); local_point.extend([t0,t1]);
    let local = fold_local_y(&y, &local_point).unwrap();
    let global_values = [1023usize,1982,1983].map(|owner| {
        virtual_global_x_mle(&fixture.owner_slices, &global_point(&wire_point, owner)).unwrap()
    });
    let projected = (Fr::one()-t0)*(Fr::one()-t1)*global_values[0]
        + t0*(Fr::one()-t1)*global_values[1]
        + (Fr::one()-t0)*t1*global_values[2];
    assert_eq!(local, projected, "non-Boolean local/global projection");
    assert_ne!(t0, Fr::zero()); assert_ne!(t1, Fr::one());
    let swapped = (Fr::one()-t0)*(Fr::one()-t1)*global_values[0]
        + t0*(Fr::one()-t1)*global_values[2] + (Fr::one()-t0)*t1*global_values[1];
    assert_ne!(local, swapped, "owner slot swap must change fixture projection");
    let mut reversed = (0..SLOT_LOG).map(|bit| Fr::from(((1023usize >> bit) & 1) as u64))
        .collect::<Vec<_>>();
    reversed.extend_from_slice(&wire_point);
    assert_ne!(virtual_global_x_mle(&fixture.owner_slices, &reversed).unwrap(), global_values[0],
        "[owner11,wire20] coordinate block reversal must fail");

    let profile_sha = role0_sha256(&profile_bytes).unwrap();
    if std::env::var_os(CONTROL_DIR_ENV).is_some() {
        write_control_new(PROFILE_FILE, &profile_bytes);
    }
    println!("STAGE1B_PREPACK_PASS profile_sha256={} descriptor_bytes={} terms={} q1={} root={} total={}",
        hex(&profile_sha), descriptor.len(), circuit.terms.len(), profile.q1,
        hex(&profile.root), hex(&profile.total_be28));
}

#[test]
#[ignore = "separate test-only log31 key-anchor discovery, before producer"]
fn same_x_log31_stage1b_key_discovery() {
    use dory_pcs::backends::arkworks::ArkworksVerifierSetup;
    let setup = pcs::generate_setup_for_scale_diagnostic(GLOBAL_LOG).expect("test-only log31 setup");
    let key = pcs::encode(&ArkworksVerifierSetup(setup.verifier.clone())).expect("canonical log31 verifier key");
    let digest = Blake2b512::digest(&key);
    let mut record = Vec::with_capacity(KEY_PIN_BYTES);
    record.extend_from_slice(KEY_MAGIC);
    record.extend_from_slice(&(GLOBAL_LOG as u64).to_le_bytes());
    record.extend_from_slice(&digest);
    record.extend_from_slice(&setup.id);
    assert_eq!(record.len(), KEY_PIN_BYTES);
    let record_sha = role0_sha256(&record).unwrap();
    if std::env::var_os(CONTROL_DIR_ENV).is_some() { write_control_new(KEY_FILE, &record); }
    println!("STAGE1B_KEY_PIN_PASS record_sha256={} key_blake2b512={} setup_id={} key_bytes={}",
        hex(&record_sha), hex(&digest), hex(&setup.id), key.len());
}

// These are test-only, fixed-N1984 artifacts. The two independently created
// control files are deliberately not outputs of the proof producer.
const STAGE1B_OUTPUT_ENV: &str = "NIPOPOW_STAGE1B_OUTPUT_DIR";
const STAGE1B_INPUT_ENV: &str = "NIPOPOW_STAGE1B_INPUT_DIR";
const STAGE1B_PROFILE_SHA_ENV: &str = "NIPOPOW_STAGE1B_PROFILE_SHA256";
const STAGE1B_KEY_SHA_ENV: &str = "NIPOPOW_STAGE1B_KEY_SHA256";
const STAGE1B_PROFILE_SHA: &str = "2419ECA009E25B3F47ACB7FD1BC926834821DADA4733CA1F72797760C8676892";
const STAGE1B_KEY_PIN_SHA: &str = "80558622C2936B4FE636B11DF3BD829AD070E6DA7147306CAEDD2742AB89635D";
const STAGE1B_SETUP_ID: &str = "66D65AE22F250378BC17FEB8278EDCB61FDF66961CD7BCB4AC5913BD9D02F0BD";
const STAGE1B_X_SHA: &str = "8B1BC276ACBD14D1078DF5537A4138E3BF6DB31C3D30A78DFB0D15139A480393";
const STAGE1B_F_X_INPUT_ENV: &str = "NIPOPOW_STAGE1B_F_X_INPUT_FILE";
const STAGE1B_MAP_INPUT_ENV: &str = "NIPOPOW_STAGE1B_MAP_INPUT_DIR";
const STAGE1B_X_FILE: &str = "same-x-stage1b-x.bits";
const STAGE1B_ARTIFACTS: [&str; 5] = [
    "same-x-stage1b-statement.bin",
    "same-x-stage1b-commitment.bin",
    "same-x-stage1b-verifier.key",
    "same-x-stage1b-gkr.proof",
    "same-x-stage1b-opening.proof",
];
const STAGE1B_STATEMENT_MAGIC: &[u8; 8] = b"XSSTMT01";
const STAGE1B_STATEMENT_LEN: usize = 8 + 1 + 8 + 32 + 384 + 1 + 32 + 8 + 7 * (GLOBAL_LOG + 1) * 32;
const STAGE1B_STATEMENT_CAP: usize = 8192;
const STAGE1B_GKR_CAP: usize = 1 << 16;
const STAGE1B_OPENING_CAP: usize = 1 << 20;

fn stage1b_dir(variable: &str) -> PathBuf {
    let path = PathBuf::from(std::env::var_os(variable).expect("Stage1b directory env absent"));
    assert!(crate::preview_test_paths::absolute_outside_source(&path) && path.is_dir(),
        "Stage1b artifacts must be in a prepared absolute directory outside source");
    path
}

fn stage1b_read(dir: &Path, name: &str, cap: usize) -> Result<Vec<u8>, String> {
    let path = dir.join(name);
    let meta = std::fs::symlink_metadata(&path).map_err(|e| format!("Stage1b {name} metadata: {e}"))?;
    if meta.file_type().is_symlink() || !meta.is_file() || meta.len() > cap as u64 {
        return Err(format!("Stage1b {name} regular-file/cap rejected"));
    }
    let mut bytes = Vec::with_capacity(meta.len() as usize);
    File::open(&path).map_err(|e| format!("Stage1b {name} open: {e}"))?
        .take(cap as u64 + 1).read_to_end(&mut bytes)
        .map_err(|e| format!("Stage1b {name} read: {e}"))?;
    if bytes.len() as u64 != meta.len() {
        return Err(format!("Stage1b {name} extent changed"));
    }
    Ok(bytes)
}

fn stage1b_write_new(dir: &Path, name: &str, bytes: &[u8]) -> Result<(), String> {
    let mut file = OpenOptions::new().write(true).create_new(true).open(dir.join(name))
        .map_err(|e| format!("Stage1b {name} create-new: {e}"))?;
    file.write_all(bytes).map_err(|e| format!("Stage1b {name} write: {e}"))?;
    file.sync_all().map_err(|e| format!("Stage1b {name} sync: {e}"))
}

fn stage1b_write_x(dir: &Path, slices: &[Vec<u8>; 3]) -> Result<PackedFile, String> {
    if slices.iter().any(|slice| slice.len() != OWNER_BYTES) {
        return Err("Stage1b source owner-slice extent rejected".into());
    }
    let path = dir.join(STAGE1B_X_FILE);
    let mut file = OpenOptions::new().write(true).create_new(true).open(&path)
        .map_err(|e| format!("Stage1b X create-new: {e}"))?;
    let zeros = vec![0u8; OWNER_BYTES];
    for owner in 0..(1 << SLOT_LOG) {
        let slice = match owner {
            1023 => &slices[0],
            1982 => &slices[1],
            1983 => &slices[2],
            _ => &zeros,
        };
        file.write_all(slice).map_err(|e| format!("Stage1b X owner {owner} write: {e}"))?;
    }
    file.sync_all().map_err(|e| format!("Stage1b X sync: {e}"))?;
    drop(file);
    let expected = 1u64 << (GLOBAL_LOG - 3);
    if std::fs::metadata(&path).map_err(|e| e.to_string())?.len() != expected {
        return Err("Stage1b X packed extent rejected".into());
    }
    PackedFile::open_with_limit(&path, GLOBAL_LOG, GLOBAL_LOG)
}

fn stage1b_local_y(source: &PackedFile) -> Result<Vec<Fr>, String> {
    let mut input = Vec::with_capacity(1 << LOCAL_LOG);
    for owner in [1023usize, 1982, 1983] {
        input.extend(crate::packed_rows::read_row(source, WIRE_COUNT, owner)?);
    }
    input.resize(1 << LOCAL_LOG, Fr::zero());
    if input.len() != 1 << LOCAL_LOG { return Err("Stage1b local Y extent rejected".into()); }
    Ok(input)
}

fn stage1b_bind_gkr(transcript: &mut Transcript, descriptor: &[u8], circuit: &sparse::Circuit,
    commitment: ArkGT, setup_id: [u8; 32]) {
    transcript.append_bytes(b"same-x-gkr-profile", SAME_X_SMOKE_GKR_DOMAIN);
    transcript.append_bytes(b"same-x-descriptor", descriptor);
    transcript.append_bytes(b"same-x-commitment",
        &pcs::encode_commitment(&commitment).expect("canonical Stage1b commitment"));
    transcript.append_bytes(b"same-x-setup-id", &setup_id);
    sparse::bind(circuit, 0, transcript);
}

fn stage1b_check_public_claims(statement: &Statement, claim: &InputClaim) -> Result<(), String> {
    if claim.point.len() != LOCAL_LOG || statement.claims.iter().any(|c| c.point.len() != GLOBAL_LOG) {
        return Err("Stage1b local/global claim dimension rejected".into());
    }
    for (index, owner) in [1023usize, 1982, 1983].iter().enumerate() {
        if statement.claims[index].point != global_point(&claim.point[..WIRE_LOG], *owner) {
            return Err(format!("Stage1b derived global point {index} rejected"));
        }
    }
    for (duplicate, primary) in [(3usize, 0usize), (4, 1), (5, 2), (6, 0)] {
        if statement.claims[duplicate] != statement.claims[primary] {
            return Err(format!("Stage1b duplicate claim {duplicate} rejected"));
        }
    }
    let t0 = claim.point[WIRE_LOG];
    let t1 = claim.point[WIRE_LOG + 1];
    let values = [statement.claims[0].value, statement.claims[1].value, statement.claims[2].value];
    let selected = (Fr::one()-t0)*(Fr::one()-t1)*values[0]
        + t0*(Fr::one()-t1)*values[1] + (Fr::one()-t0)*t1*values[2];
    if selected != claim.value { return Err("Stage1b selector/GKR InputClaim equality rejected".into()); }
    Ok(())
}

fn stage1b_claims_from_x(source: &PackedFile, input_claim: &InputClaim) -> Result<[Claim; 7], String> {
    if input_claim.point.len() != LOCAL_LOG { return Err("Stage1b GKR input point dimension".into()); }
    let mut primaries = Vec::with_capacity(3);
    for owner in [1023usize, 1982, 1983] {
        // A Boolean owner point reduces the global MLE exactly to this locked
        // source row. Avoid three redundant 256-MiB global source scans.
        let row = crate::packed_rows::read_row(source, WIRE_COUNT, owner)?;
        let value = gkr::mle(&row, &input_claim.point[..WIRE_LOG]).map_err(|e| e.to_string())?;
        primaries.push(Claim { point: global_point(&input_claim.point[..WIRE_LOG], owner), value });
    }
    let claims = std::array::from_fn(|index| {
        let primary = match index { 0 => 0, 1 => 1, 2 => 2, 3 => 0, 4 => 1, 5 => 2, _ => 0 };
        primaries[primary].clone()
    });
    Ok(claims)
}

fn stage1b_encode_statement(statement: &Statement) -> Result<Vec<u8>, String> {
    if statement.log_n != GLOBAL_LOG || statement.corpus_id.is_none()
        || statement.claims.iter().any(|claim| claim.point.len() != GLOBAL_LOG) {
        return Err("Stage1b statement dimension rejected".into());
    }
    let commitment = pcs::encode_commitment(&statement.commitment)?;
    if commitment.len() != 384 { return Err("Stage1b commitment extent rejected".into()); }
    let mut out = Vec::with_capacity(STAGE1B_STATEMENT_LEN);
    out.extend_from_slice(STAGE1B_STATEMENT_MAGIC);
    out.push(1);
    push_u64(&mut out, statement.log_n);
    out.extend_from_slice(&statement.setup_id);
    out.extend_from_slice(&commitment);
    out.push(1);
    out.extend_from_slice(&statement.corpus_id.expect("checked Stage1b corpus"));
    push_u64(&mut out, statement.claims.len());
    for claim in &statement.claims {
        for scalar in claim.point.iter().chain(std::iter::once(&claim.value)) {
            scalar.serialize_compressed(&mut out).map_err(|e| e.to_string())?;
        }
    }
    if out.len() != STAGE1B_STATEMENT_LEN || out.len() > STAGE1B_STATEMENT_CAP {
        return Err("Stage1b statement extent rejected".into());
    }
    Ok(out)
}

fn stage1b_decode_statement(bytes: &[u8]) -> Result<Statement, String> {
    if bytes.len() != STAGE1B_STATEMENT_LEN || bytes.len() > STAGE1B_STATEMENT_CAP {
        return Err("Stage1b statement exact extent rejected".into());
    }
    let mut cursor = 0usize;
    let mut take = |length: usize| -> Result<&[u8], String> {
        let end = cursor.checked_add(length).ok_or("Stage1b statement offset overflow")?;
        let part = bytes.get(cursor..end).ok_or("Stage1b statement truncated")?;
        cursor = end;
        Ok(part)
    };
    if take(8)? != STAGE1B_STATEMENT_MAGIC || take(1)? != [1] {
        return Err("Stage1b statement framing rejected".into());
    }
    if u64::from_le_bytes(take(8)?.try_into().unwrap()) != GLOBAL_LOG as u64 {
        return Err("Stage1b statement log31 rejected".into());
    }
    let mut setup_id = [0u8; 32]; setup_id.copy_from_slice(take(32)?);
    let commitment_bytes = take(384)?;
    let commitment = pcs::decode_commitment(commitment_bytes)?;
    if pcs::encode_commitment(&commitment)? != commitment_bytes {
        return Err("Stage1b noncanonical commitment".into());
    }
    if take(1)? != [1] { return Err("Stage1b corpus marker rejected".into()); }
    let mut corpus_id = [0u8; 32]; corpus_id.copy_from_slice(take(32)?);
    if u64::from_le_bytes(take(8)?.try_into().unwrap()) != 7 {
        return Err("Stage1b claim count rejected".into());
    }
    let mut claims = Vec::with_capacity(7);
    for _ in 0..7 {
        let mut point = Vec::with_capacity(GLOBAL_LOG);
        for _ in 0..GLOBAL_LOG {
            point.push(Fr::deserialize_compressed(take(32)?).map_err(|e| format!("Stage1b point scalar: {e}"))?);
        }
        let value = Fr::deserialize_compressed(take(32)?).map_err(|e| format!("Stage1b value scalar: {e}"))?;
        claims.push(Claim {point, value});
    }
    if cursor != bytes.len() { return Err("Stage1b statement trailing bytes".into()); }
    let claims: [Claim; 7] = claims.try_into().map_err(|_| "Stage1b claim array shape")?;
    let statement = Statement {log_n: GLOBAL_LOG, setup_id, commitment, corpus_id: Some(corpus_id), claims};
    if stage1b_encode_statement(&statement)? != bytes {
        return Err("Stage1b noncanonical statement".into());
    }
    Ok(statement)
}

fn stage1b_decode_key_pin(bytes: &[u8]) -> Result<([u8; 64], [u8; 32]), String> {
    if bytes.len() != KEY_PIN_BYTES || &bytes[..8] != KEY_MAGIC
        || u64::from_le_bytes(bytes[8..16].try_into().unwrap()) != GLOBAL_LOG as u64 {
        return Err("Stage1b key pin framing rejected".into());
    }
    let mut digest = [0u8; 64]; digest.copy_from_slice(&bytes[16..80]);
    let mut id = [0u8; 32]; id.copy_from_slice(&bytes[80..112]);
    Ok((digest, id))
}

fn stage1b_admit_key(key_bytes: &[u8], pin: ([u8; 64], [u8; 32]))
    -> Result<crate::verifier_key::AdmittedVerifierKey, String> {
    if key_bytes.len() > crate::verifier_key::MAX_PINNED_KEY_BYTES
        || Blake2b512::digest(key_bytes).as_slice() != pin.0 {
        return Err("Stage1b independently pinned verifier-key digest rejected".into());
    }
    crate::verifier_key::admit_generated_test_key(GLOBAL_LOG, key_bytes, pin.1)
}

fn stage1b_admit_corpus(log_n: usize, corpus_id: Option<[u8; 32]>, descriptor: &[u8])
    -> Result<(), String> {
    if log_n != GLOBAL_LOG || corpus_id != Some(same_x_smoke_corpus_id(descriptor)) {
        return Err("Stage1b descriptor/corpus rejected".into());
    }
    Ok(())
}

fn stage1b_admit_gkr(
    log_n: usize,
    corpus_id: Option<[u8; 32]>,
    descriptor: &[u8],
    circuit: &sparse::Circuit,
    gkr_bytes: &[u8],
) -> Result<(sparse::Shape, crate::gkr::GkrProof), String> {
    stage1b_admit_corpus(log_n, corpus_id, descriptor)?;
    let shape = sparse::validate(circuit, 0).map_err(|e| e.to_string())?;
    let gkr_proof = sparse::decode_proof(circuit, 0, gkr_bytes)?;
    if gkr::encode_proof(&gkr_proof)? != gkr_bytes {
        return Err("Stage1b GKR codec rejected".into());
    }
    Ok((shape, gkr_proof))
}

fn stage1b_verify_composed(key: &crate::verifier_key::AdmittedVerifierKey, descriptor: &[u8],
    circuit: &sparse::Circuit, statement: &Statement, opening: &Proof, gkr_bytes: &[u8],
    gkr_bound_commitment: ArkGT, gkr_bound_setup_id: [u8; 32]) -> Result<(), String> {
    let (shape, gkr_proof) = stage1b_admit_gkr(
        statement.log_n, statement.corpus_id, descriptor, circuit, gkr_bytes,
    )?;
    let mut transcript = Transcript::new(SAME_X_SMOKE_GKR_DOMAIN);
    let input_claim = gkr::verify_with_wiring(
        &[shape.input_bits], shape.row_count, &gkr_proof, &mut transcript,
        |t| stage1b_bind_gkr(t, descriptor, circuit, gkr_bound_commitment, gkr_bound_setup_id),
        |layer, r, u, v| if layer == 0 { sparse::wiring(circuit, &shape, r, u, v) }
            else { Err(gkr::GkrError::PointDimension) },
    ).map_err(|e| e.to_string())?;
    stage1b_check_public_claims(statement, &input_claim)?;
    verify_admitted(statement, key, opening).map(|_| ())
}

fn stage1b_verify_gkr_binding(descriptor: &[u8], circuit: &sparse::Circuit,
    statement: &Statement, gkr_bytes: &[u8]) -> Result<(), String> {
    // This focused transcript check intentionally skips corpus admission so a
    // relabelled, internally consistent descriptor reaches GKR verification.
    let shape = sparse::validate(circuit, 0).map_err(|e| e.to_string())?;
    let proof = sparse::decode_proof(circuit, 0, gkr_bytes)
        .map_err(|e| format!("GKR packet decode rejected: {e}"))?;
    let mut transcript = Transcript::new(SAME_X_SMOKE_GKR_DOMAIN);
    gkr::verify_with_wiring(
        &[shape.input_bits], shape.row_count, &proof, &mut transcript,
        |t| stage1b_bind_gkr(t, descriptor, circuit, statement.commitment, statement.setup_id),
        |layer, r, u, v| if layer == 0 { sparse::wiring(circuit, &shape, r, u, v) }
            else { Err(gkr::GkrError::PointDimension) },
    ).map(|_| ()).map_err(|e| format!("GKR transcript rejected: {e}"))
}

#[test]
fn same_x_log31_stage1b_packet_and_selector_pure() {
    use dory_pcs::primitives::arithmetic::Group;
    let mut local_point = (0..WIRE_LOG).map(|bit| Fr::from((bit + 5) as u64)).collect::<Vec<_>>();
    local_point.extend([Fr::from(2u64), Fr::from(3u64)]);
    let values = [Fr::from(5u64), Fr::from(7u64), Fr::from(11u64)];
    let selected = (Fr::one()-local_point[WIRE_LOG])*(Fr::one()-local_point[WIRE_LOG+1])*values[0]
        + local_point[WIRE_LOG]*(Fr::one()-local_point[WIRE_LOG+1])*values[1]
        + (Fr::one()-local_point[WIRE_LOG])*local_point[WIRE_LOG+1]*values[2];
    let claim = InputClaim {point: local_point.clone(), value: selected};
    let primary = [1023usize, 1982, 1983].map(|owner| {
        let index = match owner {1023=>0,1982=>1,_=>2};
        Claim {point: global_point(&local_point[..WIRE_LOG],owner), value: values[index]}
    });
    let claims = std::array::from_fn(|index| {
        let source = match index {0=>0,1=>1,2=>2,3=>0,4=>1,5=>2,_=>0};
        primary[source].clone()
    });
    let statement = Statement {log_n: GLOBAL_LOG, setup_id: [7u8;32],
        commitment: <ArkGT as Group>::identity(), corpus_id: Some([8u8;32]), claims};
    stage1b_check_public_claims(&statement, &claim).unwrap();
    assert_eq!(STAGE1B_STATEMENT_LEN, 7642);
    let bytes = stage1b_encode_statement(&statement).unwrap();
    let decoded = stage1b_decode_statement(&bytes).unwrap();
    assert_eq!(stage1b_encode_statement(&decoded).unwrap(), bytes);
    let mut changed = decoded.clone(); changed.claims[0].point[WIRE_LOG] += Fr::one();
    assert!(stage1b_check_public_claims(&changed,&claim).is_err());
    let mut changed = decoded.clone(); changed.claims[1].value += Fr::one();
    assert!(stage1b_check_public_claims(&changed,&claim).is_err());
    let mut changed = decoded.clone(); changed.claims[6].value += Fr::one();
    assert!(stage1b_check_public_claims(&changed,&claim).is_err());
    let mut trailing = bytes.clone(); trailing.push(0);
    assert!(stage1b_decode_statement(&trailing).is_err());
    assert!(stage1b_decode_statement(&bytes[..bytes.len()-1]).is_err());
    let mut noncanonical = bytes.clone();
    noncanonical[8+1+8+32+384+1+32+8..8+1+8+32+384+1+32+8+32].fill(0xff);
    assert!(stage1b_decode_statement(&noncanonical).is_err());
    let mut pin = Vec::with_capacity(KEY_PIN_BYTES);
    pin.extend_from_slice(KEY_MAGIC);
    pin.extend_from_slice(&(GLOBAL_LOG as u64).to_le_bytes());
    pin.extend_from_slice(&[1u8;64]);
    pin.extend_from_slice(&[2u8;32]);
    assert_eq!(stage1b_decode_key_pin(&pin).unwrap(), ([1u8;64],[2u8;32]));
    pin[8] ^= 1;
    assert!(stage1b_decode_key_pin(&pin).is_err());
}

#[test]
#[ignore = "log31 producer requires reviewed external 2-GiB Job and 600-second limit"]
fn same_x_log31_stage1b_producer() {
    use dory_pcs::backends::arkworks::ArkworksVerifierSetup;
    let started = Instant::now();
    let output = stage1b_dir(STAGE1B_OUTPUT_ENV);
    for name in STAGE1B_ARTIFACTS.into_iter().chain([STAGE1B_X_FILE]) {
        assert!(!output.join(name).exists(), "Stage1b producer output must be fresh: {name}");
    }
    let fixture = same_x_stage1b_n1984_fixture().expect("frozen N1984 Stage1b fixture");
    let profile = PublicProfile {root: fixture.root, total_be28: fixture.total, q1: fixture.q1};
    let profile_bytes = encode_profile(&profile);
    assert_eq!(role0_sha256(&profile_bytes).unwrap(), bytes32(STAGE1B_PROFILE_SHA).unwrap(),
        "producer profile must match independently discovered N1984 fixture");
    let (descriptor, circuit, original) = public_circuit(&profile).expect("public Stage1b circuit");
    assert_eq!(original, fixture.original_map_terms, "public/producer Map terms");
    drop(original);
    println!("STAGE1B_PHASE fixture elapsed_ms={} terms={} descriptor_bytes={}",
        started.elapsed().as_millis(), circuit.terms.len(), descriptor.len());

    let source = stage1b_write_x(&output, &fixture.owner_slices).expect("create, sync and lock one X");
    drop(fixture);
    println!("STAGE1B_PHASE x_locked elapsed_ms={} source_bytes={}",
        started.elapsed().as_millis(), 1usize << (GLOBAL_LOG - 3));
    let setup = pcs::generate_setup_for_scale_diagnostic(GLOBAL_LOG).expect("test-only log31 setup");
    let key_bytes = pcs::encode(&ArkworksVerifierSetup(setup.verifier.clone())).expect("canonical log31 key");
    let key_digest = Blake2b512::digest(&key_bytes);
    let mut key_record = Vec::with_capacity(KEY_PIN_BYTES);
    key_record.extend_from_slice(KEY_MAGIC);
    key_record.extend_from_slice(&(GLOBAL_LOG as u64).to_le_bytes());
    key_record.extend_from_slice(&key_digest);
    key_record.extend_from_slice(&setup.id);
    assert_eq!(key_record.len(), KEY_PIN_BYTES);
    assert_eq!(role0_sha256(&key_record).unwrap(), bytes32(STAGE1B_KEY_PIN_SHA).unwrap(),
        "generated setup/key must match independently discovered key pin before commitment");
    drop(key_record);
    println!("STAGE1B_PHASE setup elapsed_ms={} setup_id={} key_blake2b512={}",
        started.elapsed().as_millis(), hex(&setup.id), hex(&key_digest));
    let committed = packed::commit(&source, &setup).expect("one X commitment");
    println!("STAGE1B_PHASE committed elapsed_ms={}", started.elapsed().as_millis());

    let local = stage1b_local_y(&source).expect("three locked source rows and zero fourth slot");
    let mut gkr_transcript = Transcript::new(SAME_X_SMOKE_GKR_DOMAIN);
    let (gkr_proof, input_claim) = sparse::prove_with_binding(&circuit, &local, 0, &mut gkr_transcript,
        |t| stage1b_bind_gkr(t, &descriptor, &circuit, committed.commitment, setup.id))
        .expect("Stage1b descriptor-bound Map and 92 q1 rows");
    drop(local);
    let gkr_bytes = gkr::encode_proof(&gkr_proof).expect("canonical Stage1b GKR proof");
    drop(gkr_proof);
    println!("STAGE1B_PHASE gkr elapsed_ms={} gkr_bytes={}", started.elapsed().as_millis(), gkr_bytes.len());

    let statement = Statement {
        log_n: GLOBAL_LOG,
        setup_id: setup.id,
        commitment: committed.commitment,
        corpus_id: Some(same_x_smoke_corpus_id(&descriptor)),
        claims: stage1b_claims_from_x(&source, &input_claim).expect("three points of one locked X"),
    };
    stage1b_check_public_claims(&statement, &input_claim).expect("local/global selector join");
    let statement_bytes = stage1b_encode_statement(&statement).expect("canonical Stage1b statement");
    println!("STAGE1B_PHASE joined elapsed_ms={} statement_bytes={}",
        started.elapsed().as_millis(), statement_bytes.len());

    let mut opening_transcript = Transcript::new(DOMAIN);
    let frontend = prove_frontend_on_mode(&source, &statement, &mut opening_transcript,
        None, ProjectionMode::Fused, None).expect("seven-claim fused opening frontend");
    println!("STAGE1B_PHASE frontend elapsed_ms={}", started.elapsed().as_millis());
    let pcs_proof = packed::open(&committed, &source, &frontend.point, &setup, &mut opening_transcript)
        .expect("Dory opening of same locked X");
    let opening = Proof {rounds: frontend.rounds, terminal: frontend.terminal, pcs: pcs_proof};
    let opening_bytes = encode_proof(&opening, GLOBAL_LOG).expect("canonical Stage1b opening proof");
    let commitment_bytes = pcs::encode_commitment(&committed.commitment).expect("canonical commitment");
    println!("STAGE1B_PHASE pcs elapsed_ms={} opening_bytes={}",
        started.elapsed().as_millis(), opening_bytes.len());

    for (name, bytes) in STAGE1B_ARTIFACTS.into_iter().zip([
        statement_bytes.as_slice(), commitment_bytes.as_slice(), key_bytes.as_slice(),
        gkr_bytes.as_slice(), opening_bytes.as_slice(),
    ]) {
        stage1b_write_new(&output, name, bytes).expect("create-once public proof artifact");
    }
    println!("STAGE1B_PRODUCER_PASS elapsed_ms={} x_bytes={} statement_bytes={} gkr_bytes={} opening_bytes={}",
        started.elapsed().as_millis(), 1usize << (GLOBAL_LOG - 3),
        statement_bytes.len(), gkr_bytes.len(), opening_bytes.len());
}

#[test]
#[ignore = "F Stage1b producer reuses the pinned candidate69 X and requires the reviewed log31 Job"]
fn same_x_log31_stage1b_filtered_f_producer() {
    use dory_pcs::backends::arkworks::ArkworksVerifierSetup;
    let started = Instant::now();
    let output = stage1b_dir(STAGE1B_OUTPUT_ENV);
    let map_input = stage1b_dir(STAGE1B_MAP_INPUT_ENV);
    for name in STAGE1B_ARTIFACTS {
        assert!(!output.join(name).exists(), "F Stage1b output must be fresh: {name}");
    }

    let profile_bytes = stage1b_read(&map_input, PROFILE_FILE, PROFILE_BYTES)
        .expect("read candidate69 Map profile control");
    assert_eq!(role0_sha256(&profile_bytes).unwrap(), bytes32(STAGE1B_PROFILE_SHA).unwrap(),
        "F producer must use the independently pinned Map profile");
    let profile = decode_profile(&profile_bytes).expect("canonical pinned Stage1b profile");
    let (map_descriptor, map_circuit, _) = public_circuit(&profile)
        .expect("rebuild candidate69 Map verifier circuit");
    let (descriptor, circuit, _) = filtered_f_public_circuit(&profile)
        .expect("build filtered F verifier circuit");
    assert_ne!(descriptor, map_descriptor, "F descriptor is distinct from Map");
    assert_ne!(same_x_smoke_corpus_id(&descriptor), same_x_smoke_corpus_id(&map_descriptor),
        "F corpus identity is distinct from Map");
    println!("STAGE1B_F_PHASE circuits elapsed_ms={} map_terms={} f_terms={} f_descriptor_bytes={}",
        started.elapsed().as_millis(), map_circuit.terms.len(), circuit.terms.len(), descriptor.len());

    let key_pin_bytes = stage1b_read(&map_input, KEY_FILE, KEY_PIN_BYTES)
        .expect("read candidate69 independent key pin");
    assert_eq!(role0_sha256(&key_pin_bytes).unwrap(), bytes32(STAGE1B_KEY_PIN_SHA).unwrap(),
        "candidate69 independent key-pin hash");
    let key_pin = stage1b_decode_key_pin(&key_pin_bytes).expect("canonical candidate69 key pin");
    let pinned_setup = bytes32(STAGE1B_SETUP_ID).unwrap();
    assert_eq!(key_pin.1, pinned_setup, "candidate74-pinned deterministic setup ID");
    let map_key_bytes = stage1b_read(&map_input, STAGE1B_ARTIFACTS[2],
        crate::verifier_key::MAX_PINNED_KEY_BYTES).expect("read candidate69 Map verifier key");
    let map_statement_bytes = stage1b_read(&map_input, STAGE1B_ARTIFACTS[0], STAGE1B_STATEMENT_CAP)
        .expect("read candidate69 Map statement");
    let map_statement = stage1b_decode_statement(&map_statement_bytes)
        .expect("decode candidate69 Map statement");
    assert_eq!(map_statement.setup_id, pinned_setup, "candidate69 Map setup ID");
    assert_eq!(map_statement.corpus_id, Some(same_x_smoke_corpus_id(&map_descriptor)),
        "candidate69 Map descriptor identity");
    let map_commitment_bytes = stage1b_read(&map_input, STAGE1B_ARTIFACTS[1], 384)
        .expect("read candidate69 Map commitment sidecar");
    assert_eq!(pcs::encode_commitment(&map_statement.commitment).unwrap(), map_commitment_bytes,
        "candidate69 Map commitment sidecar matches statement");
    let admitted_key = stage1b_admit_key(&map_key_bytes, key_pin)
        .expect("admit candidate69 independently pinned key");
    let map_gkr_bytes = stage1b_read(&map_input, STAGE1B_ARTIFACTS[3], STAGE1B_GKR_CAP)
        .expect("read candidate69 Map GKR proof before F proving");
    let map_opening_bytes = stage1b_read(&map_input, STAGE1B_ARTIFACTS[4], STAGE1B_OPENING_CAP)
        .expect("read candidate69 Map Dory opening before F proving");
    let map_opening = decode_proof(&map_opening_bytes, GLOBAL_LOG)
        .expect("decode canonical candidate69 Map opening before F proving");
    assert_eq!(encode_proof(&map_opening, GLOBAL_LOG).unwrap(), map_opening_bytes,
        "candidate69 Map opening canonical re-encoding before F proving");
    stage1b_verify_composed(&admitted_key, &map_descriptor, &map_circuit, &map_statement,
        &map_opening, &map_gkr_bytes, map_statement.commitment, map_statement.setup_id)
        .expect("verify old Map packet under public Map verifier before F proving");

    let x_path = PathBuf::from(std::env::var_os(STAGE1B_F_X_INPUT_ENV)
        .expect("pinned candidate69 X file path env absent"));
    assert!(crate::preview_test_paths::absolute_outside_source(&x_path)
        && x_path.file_name().and_then(|name| name.to_str()) == Some(STAGE1B_X_FILE),
        "candidate69 X must be the named read-only file outside source");
    let x_meta = std::fs::symlink_metadata(&x_path).expect("candidate69 X metadata");
    assert!(!x_meta.file_type().is_symlink() && x_meta.is_file()
        && x_meta.len() == (1u64 << (GLOBAL_LOG - 3)), "candidate69 X extent/type pin");
    let x_parent = x_path.parent().expect("candidate69 X parent");
    let x_bytes = stage1b_read(x_parent, STAGE1B_X_FILE, 1usize << (GLOBAL_LOG - 3))
        .expect("read candidate69 X only to verify its independent digest");
    assert_eq!(role0_sha256(&x_bytes).unwrap(), bytes32(STAGE1B_X_SHA).unwrap(),
        "candidate69 X SHA256 pin");
    drop(x_bytes);
    let source = PackedFile::open_with_limit(&x_path, GLOBAL_LOG, GLOBAL_LOG)
        .expect("open candidate69 pinned X read-only");

    let setup = pcs::generate_setup_for_scale_diagnostic(GLOBAL_LOG)
        .expect("recreate deterministic diagnostic log31 setup");
    assert_eq!(setup.id, pinned_setup, "regenerated setup ID matches candidate69");
    let key_bytes = pcs::encode(&ArkworksVerifierSetup(setup.verifier.clone()))
        .expect("canonical regenerated verifier key");
    let key_digest = Blake2b512::digest(&key_bytes);
    assert_eq!(key_digest.as_slice(), key_pin.0, "regenerated encoded key digest matches control");
    assert_eq!(key_bytes, map_key_bytes, "regenerated encoded verifier key matches candidate69 bytes");
    let regenerated_admitted_key = stage1b_admit_key(&key_bytes, key_pin)
        .expect("regenerated key passes candidate69 independent admission");
    assert_eq!(*regenerated_admitted_key.id(), pinned_setup, "admitted deterministic setup ID");

    // The existing Map packet is the pinned C oracle. Recompute C from the
    // exact candidate69 X and stop before F proving if any setup/input differs.
    let committed = packed::commit(&source, &setup).expect("recompute C from pinned candidate69 X");
    assert_eq!(committed.commitment, map_statement.commitment,
        "recomputed X commitment must equal candidate69 Map statement");
    assert_eq!(pcs::encode_commitment(&committed.commitment).unwrap(), map_commitment_bytes,
        "recomputed X commitment must equal candidate69 Map C sidecar");
    println!("STAGE1B_F_PHASE candidate69_pins elapsed_ms={} setup_id={} x_sha256={}",
        started.elapsed().as_millis(), hex(&setup.id), STAGE1B_X_SHA);

    let local = stage1b_local_y(&source).expect("read the three candidate69 X owner rows");
    let mut gkr_transcript = Transcript::new(SAME_X_SMOKE_GKR_DOMAIN);
    let (gkr_proof, input_claim) = sparse::prove_with_binding(&circuit, &local, 0, &mut gkr_transcript,
        |t| stage1b_bind_gkr(t, &descriptor, &circuit, committed.commitment, setup.id))
        .expect("descriptor-bound filtered F GKR proof");
    drop(local);
    let gkr_bytes = gkr::encode_proof(&gkr_proof).expect("canonical F GKR proof");
    drop(gkr_proof);
    let statement = Statement {
        log_n: GLOBAL_LOG,
        setup_id: setup.id,
        commitment: committed.commitment,
        corpus_id: Some(same_x_smoke_corpus_id(&descriptor)),
        claims: stage1b_claims_from_x(&source, &input_claim).expect("seven claims from same pinned X"),
    };
    stage1b_check_public_claims(&statement, &input_claim).expect("F selector and local/global claim join");
    let statement_bytes = stage1b_encode_statement(&statement).expect("canonical F statement");
    let mut opening_transcript = Transcript::new(DOMAIN);
    let frontend = prove_frontend_on_mode(&source, &statement, &mut opening_transcript,
        None, ProjectionMode::Fused, None).expect("F seven-claim fused opening frontend");
    let pcs_proof = packed::open(&committed, &source, &frontend.point, &setup, &mut opening_transcript)
        .expect("F Dory opening of the same candidate69 X");
    let opening = Proof {rounds: frontend.rounds, terminal: frontend.terminal, pcs: pcs_proof};
    let opening_bytes = encode_proof(&opening, GLOBAL_LOG).expect("canonical F opening proof");
    let commitment_bytes = pcs::encode_commitment(&committed.commitment)
        .expect("canonical F commitment");

    for (name, bytes) in STAGE1B_ARTIFACTS.into_iter().zip([
        statement_bytes.as_slice(), commitment_bytes.as_slice(), key_bytes.as_slice(),
        gkr_bytes.as_slice(), opening_bytes.as_slice(),
    ]) {
        stage1b_write_new(&output, name, bytes).expect("create-new F public proof artifact");
    }
    println!("STAGE1B_F_PRODUCER_PASS elapsed_ms={} x_reused_read_only=true statement_bytes={} gkr_bytes={} opening_bytes={}",
        started.elapsed().as_millis(), statement_bytes.len(), gkr_bytes.len(), opening_bytes.len());
}

#[test]
#[ignore = "F Stage1b fresh proof receiver requires separate Map controls and producer artifacts"]
fn same_x_log31_stage1b_filtered_f_fresh_receiver() {
    use dory_pcs::primitives::arithmetic::Group;
    let input = stage1b_dir(STAGE1B_INPUT_ENV);
    let map_input = stage1b_dir(STAGE1B_MAP_INPUT_ENV);
    assert!(!input.join(STAGE1B_X_FILE).exists(), "F receiver directory must not contain X");

    let expected_profile = bytes32(&std::env::var(STAGE1B_PROFILE_SHA_ENV)
        .expect("independent Stage1b profile SHA256 env")).expect("canonical profile SHA256");
    let expected_key_pin = bytes32(&std::env::var(STAGE1B_KEY_SHA_ENV)
        .expect("independent Stage1b key-pin SHA256 env")).expect("canonical key-pin SHA256");
    assert_eq!(expected_key_pin, bytes32(STAGE1B_KEY_PIN_SHA).unwrap(), "frozen candidate69 key pin hash");
    let profile_bytes = stage1b_read(&map_input, PROFILE_FILE, PROFILE_BYTES)
        .expect("read independently pinned Map profile");
    assert_eq!(role0_sha256(&profile_bytes).unwrap(), expected_profile, "independent Map profile pin");
    assert_eq!(expected_profile, bytes32(STAGE1B_PROFILE_SHA).unwrap(), "frozen N1984 profile pin");
    let profile = decode_profile(&profile_bytes).expect("canonical independently pinned profile");
    let key_pin_bytes = stage1b_read(&map_input, KEY_FILE, KEY_PIN_BYTES)
        .expect("read independently pinned Map key control");
    assert_eq!(role0_sha256(&key_pin_bytes).unwrap(), expected_key_pin, "independent Map key control pin");
    let key_pin = stage1b_decode_key_pin(&key_pin_bytes).expect("canonical independent key pin");
    assert_eq!(key_pin.1, bytes32(STAGE1B_SETUP_ID).unwrap(), "pinned candidate69 setup ID");

    let (map_descriptor, map_circuit, _) = public_circuit(&profile)
        .expect("rebuild public Map verifier circuit without X");
    let (f_descriptor, f_circuit, _) = filtered_f_public_circuit(&profile)
        .expect("rebuild public filtered F verifier circuit without X");
    let map_statement_bytes = stage1b_read(&map_input, STAGE1B_ARTIFACTS[0], STAGE1B_STATEMENT_CAP)
        .expect("read candidate69 Map statement");
    let map_statement = stage1b_decode_statement(&map_statement_bytes)
        .expect("decode canonical candidate69 Map statement");
    let map_commitment_bytes = stage1b_read(&map_input, STAGE1B_ARTIFACTS[1], 384)
        .expect("read candidate69 Map C sidecar");
    assert_eq!(pcs::encode_commitment(&map_statement.commitment).unwrap(), map_commitment_bytes,
        "Map statement and C sidecar");
    let map_key_bytes = stage1b_read(&map_input, STAGE1B_ARTIFACTS[2],
        crate::verifier_key::MAX_PINNED_KEY_BYTES).expect("read candidate69 Map verifier key");
    let map_gkr_bytes = stage1b_read(&map_input, STAGE1B_ARTIFACTS[3], STAGE1B_GKR_CAP)
        .expect("read candidate69 Map GKR proof");
    let map_opening_bytes = stage1b_read(&map_input, STAGE1B_ARTIFACTS[4], STAGE1B_OPENING_CAP)
        .expect("read candidate69 Map Dory opening");
    let map_opening = decode_proof(&map_opening_bytes, GLOBAL_LOG).expect("decode Map opening");
    assert_eq!(encode_proof(&map_opening, GLOBAL_LOG).unwrap(), map_opening_bytes,
        "canonical Map opening codec");

    let f_statement_bytes = stage1b_read(&input, STAGE1B_ARTIFACTS[0], STAGE1B_STATEMENT_CAP)
        .expect("read F public statement");
    let f_statement = stage1b_decode_statement(&f_statement_bytes).expect("decode canonical F statement");
    let f_commitment_bytes = stage1b_read(&input, STAGE1B_ARTIFACTS[1], 384)
        .expect("read F C sidecar");
    assert_eq!(pcs::encode_commitment(&f_statement.commitment).unwrap(), f_commitment_bytes,
        "F statement and C sidecar");
    let f_key_bytes = stage1b_read(&input, STAGE1B_ARTIFACTS[2],
        crate::verifier_key::MAX_PINNED_KEY_BYTES).expect("read F verifier key");
    assert_eq!(f_key_bytes, map_key_bytes, "Map/F packets use the same pinned verifier-key bytes");
    let key = stage1b_admit_key(&f_key_bytes, key_pin).expect("independent profile/key admission");
    let f_gkr_bytes = stage1b_read(&input, STAGE1B_ARTIFACTS[3], STAGE1B_GKR_CAP)
        .expect("read F GKR proof");
    let f_opening_bytes = stage1b_read(&input, STAGE1B_ARTIFACTS[4], STAGE1B_OPENING_CAP)
        .expect("read F Dory opening");
    let f_opening = decode_proof(&f_opening_bytes, GLOBAL_LOG).expect("decode F opening");
    assert_eq!(encode_proof(&f_opening, GLOBAL_LOG).unwrap(), f_opening_bytes,
        "canonical F opening codec");

    let map_id = same_x_smoke_corpus_id(&map_descriptor);
    let f_id = same_x_smoke_corpus_id(&f_descriptor);
    assert_ne!(map_id, f_id, "Map/F descriptor-derived corpus IDs differ");
    let pinned_setup = bytes32(STAGE1B_SETUP_ID).unwrap();
    assert_eq!(map_statement.setup_id, pinned_setup, "candidate69 Map setup ID");
    assert_eq!(f_statement.setup_id, pinned_setup, "F setup ID matches candidate69 Map");
    assert_eq!(f_statement.commitment, map_statement.commitment, "Map/F use the same pinned X commitment");
    assert_eq!(map_statement.corpus_id, Some(map_id), "Map packet bound to public Map circuit");
    assert_eq!(f_statement.corpus_id, Some(f_id), "F packet bound to public filtered F circuit");
    stage1b_verify_composed(&key, &map_descriptor, &map_circuit, &map_statement, &map_opening,
        &map_gkr_bytes, map_statement.commitment, map_statement.setup_id)
        .expect("candidate69 Map packet verifies under current public Map verifier");
    stage1b_verify_composed(&key, &f_descriptor, &f_circuit, &f_statement, &f_opening,
        &f_gkr_bytes, f_statement.commitment, f_statement.setup_id)
        .expect("F packet verifies under freshly reconstructed public F verifier");

    assert!(stage1b_verify_composed(&key, &f_descriptor, &f_circuit, &map_statement,
        &map_opening, &map_gkr_bytes, map_statement.commitment, map_statement.setup_id).is_err(),
        "Map packet must fail under the F verifier");
    assert!(stage1b_verify_composed(&key, &map_descriptor, &map_circuit, &f_statement,
        &f_opening, &f_gkr_bytes, f_statement.commitment, f_statement.setup_id).is_err(),
        "F packet must fail under the Map verifier");
    let map_gkr_cross_error = stage1b_verify_gkr_binding(
        &f_descriptor, &f_circuit, &map_statement, &map_gkr_bytes)
        .expect_err("valid Map GKR bytes must fail under the F transcript/circuit");
    assert!(map_gkr_cross_error.starts_with("GKR transcript rejected:"),
        "Map-to-F cross substitution must reach GKR transcript: {map_gkr_cross_error}");
    let f_gkr_cross_error = stage1b_verify_gkr_binding(
        &map_descriptor, &map_circuit, &f_statement, &f_gkr_bytes)
        .expect_err("valid F GKR bytes must fail under the Map transcript/circuit");
    assert!(f_gkr_cross_error.starts_with("GKR transcript rejected:"),
        "F-to-Map cross substitution must reach GKR transcript: {f_gkr_cross_error}");

    let mut relabelled_descriptor = f_descriptor.clone();
    relabelled_descriptor[0] ^= 1;
    let relabelled_id = same_x_smoke_corpus_id(&relabelled_descriptor);
    assert_ne!(relabelled_id, f_id, "single descriptor-byte change relabels corpus ID");
    stage1b_admit_corpus(GLOBAL_LOG, Some(relabelled_id), &relabelled_descriptor)
        .expect("canonical relabelled corpus identity is internally consistent");
    assert!(stage1b_verify_gkr_binding(&relabelled_descriptor, &f_circuit, &f_statement, &f_gkr_bytes).is_err(),
        "F GKR transcript rejects a relabelled descriptor/corpus identity");
    let mut relabelled_statement = f_statement.clone();
    relabelled_statement.corpus_id = Some(map_id);
    assert!(verify_admitted(&relabelled_statement, &key, &f_opening).is_err(),
        "F opening transcript rejects a relabelled Map corpus ID independently");
    let mut relabelled_map_statement = map_statement.clone();
    relabelled_map_statement.corpus_id = Some(f_id);
    assert!(verify_admitted(&relabelled_map_statement, &key, &map_opening).is_err(),
        "Map opening transcript rejects a relabelled F corpus ID independently");

    println!("STAGE1B_F_FRESH_RECEIVER_PASS map_and_f_positive=true cross_rejections=2 gkr_cross_transcript=reject relabel_gkr=reject relabel_opening=reject x_present=false");
}

#[test]
#[ignore = "fresh-process proof-only receiver; requires separately pinned controls and five public artifacts"]
fn same_x_log31_stage1b_fresh_receiver() {
    use dory_pcs::primitives::arithmetic::Group;
    let input = stage1b_dir(STAGE1B_INPUT_ENV);
    assert!(!input.join(STAGE1B_X_FILE).exists(), "fresh receiver directory must not contain X");
    let expected_profile = bytes32(&std::env::var(STAGE1B_PROFILE_SHA_ENV)
        .expect("independent Stage1b profile SHA256 env")).expect("canonical profile SHA256");
    let expected_key = bytes32(&std::env::var(STAGE1B_KEY_SHA_ENV)
        .expect("independent Stage1b key-pin SHA256 env")).expect("canonical key-pin SHA256");
    assert_eq!(expected_key, bytes32(STAGE1B_KEY_PIN_SHA).unwrap(), "frozen key-pin SHA256");
    let profile_bytes = stage1b_read(&input, PROFILE_FILE, PROFILE_BYTES).expect("read public profile");
    assert_eq!(role0_sha256(&profile_bytes).unwrap(), expected_profile, "independent profile SHA256");
    assert_eq!(expected_profile, bytes32(STAGE1B_PROFILE_SHA).unwrap(), "frozen N1984 profile SHA256");
    let profile = decode_profile(&profile_bytes).expect("canonical independent public profile");
    let key_pin_bytes = stage1b_read(&input, KEY_FILE, KEY_PIN_BYTES).expect("read independent key pin");
    assert_eq!(role0_sha256(&key_pin_bytes).unwrap(), expected_key, "independent key pin SHA256");
    let key_pin = stage1b_decode_key_pin(&key_pin_bytes).expect("canonical independent key pin");
    let (descriptor, circuit, original) = public_circuit(&profile).expect("rebuild verifier Map without X");
    drop(original);

    let statement_bytes = stage1b_read(&input, STAGE1B_ARTIFACTS[0], STAGE1B_STATEMENT_CAP)
        .expect("read canonical public statement");
    let statement = stage1b_decode_statement(&statement_bytes).expect("decode canonical public statement");
    assert_eq!(statement.setup_id, key_pin.1, "packet setup ID must match independent key pin");
    assert_eq!(statement.corpus_id, Some(same_x_smoke_corpus_id(&descriptor)), "public circuit descriptor bound");
    let commitment_bytes = stage1b_read(&input, STAGE1B_ARTIFACTS[1], 384).expect("read C sidecar");
    assert_eq!(pcs::encode_commitment(&statement.commitment).unwrap(), commitment_bytes,
        "C sidecar must match public statement");
    let key_bytes = stage1b_read(&input, STAGE1B_ARTIFACTS[2], crate::verifier_key::MAX_PINNED_KEY_BYTES)
        .expect("read verifier key artifact");
    let key = stage1b_admit_key(&key_bytes, key_pin).expect("independent log31 verifier-key admission");
    assert_eq!(*key.id(), key_pin.1, "admitted key setup ID");
    let gkr_bytes = stage1b_read(&input, STAGE1B_ARTIFACTS[3], STAGE1B_GKR_CAP).expect("read GKR proof");
    let opening_bytes = stage1b_read(&input, STAGE1B_ARTIFACTS[4], STAGE1B_OPENING_CAP)
        .expect("read Dory opening proof");
    let opening = decode_proof(&opening_bytes, GLOBAL_LOG).expect("decode canonical opening proof");
    assert_eq!(encode_proof(&opening, GLOBAL_LOG).unwrap(), opening_bytes, "canonical opening re-encoding");
    stage1b_verify_composed(&key, &descriptor, &circuit, &statement, &opening, &gkr_bytes,
        statement.commitment, statement.setup_id).expect("fresh same-X joined proof verification");

    let mut truncated = statement_bytes.clone(); truncated.pop();
    assert!(stage1b_decode_statement(&truncated).is_err(), "truncated statement rejected");
    let mut trailing = statement_bytes.clone(); trailing.push(0);
    assert!(stage1b_decode_statement(&trailing).is_err(), "extra statement byte rejected");
    let mut noncanonical = statement_bytes.clone();
    let first_scalar = 8+1+8+32+384+1+32+8;
    noncanonical[first_scalar..first_scalar+32].fill(0xff);
    assert!(stage1b_decode_statement(&noncanonical).is_err(), "noncanonical scalar rejected");
    let mut bad_profile = profile_bytes.clone(); bad_profile[25] ^= 1;
    assert_ne!(role0_sha256(&bad_profile).unwrap(), expected_profile, "changed public profile pin rejected");
    let mut bad_pin = key_pin_bytes.clone(); bad_pin[16] ^= 1;
    assert_ne!(role0_sha256(&bad_pin).unwrap(), expected_key, "changed key record pin rejected");
    let mut bad_key = key_bytes.clone(); bad_key[0] ^= 1;
    assert!(stage1b_admit_key(&bad_key, key_pin).is_err(), "one key byte rejected by independent pin");
    let alternate_commitment = <ArkGT as Group>::identity();
    assert_ne!(alternate_commitment, statement.commitment);
    assert!(stage1b_verify_composed(&key, &descriptor, &circuit, &statement, &opening, &gkr_bytes,
        alternate_commitment, statement.setup_id).is_err(), "GKR-only C mutation rejected");
    let mut alternate_setup = statement.setup_id; alternate_setup[0] ^= 1;
    assert!(stage1b_verify_composed(&key, &descriptor, &circuit, &statement, &opening, &gkr_bytes,
        statement.commitment, alternate_setup).is_err(), "GKR-only setup mutation rejected");
    let mut changed = statement.clone(); changed.commitment = alternate_commitment;
    assert!(stage1b_verify_composed(&key, &descriptor, &circuit, &changed, &opening, &gkr_bytes,
        statement.commitment, statement.setup_id).is_err(), "opening-only C mutation rejected");
    let mut changed = statement.clone(); changed.setup_id = alternate_setup;
    assert!(stage1b_verify_composed(&key, &descriptor, &circuit, &changed, &opening, &gkr_bytes,
        statement.commitment, statement.setup_id).is_err(), "opening-only setup mutation rejected");
    let mut changed_descriptor = descriptor.clone(); changed_descriptor[0] ^= 1;
    let mut changed = statement.clone(); changed.corpus_id = Some(same_x_smoke_corpus_id(&changed_descriptor));
    assert!(stage1b_verify_composed(&key, &changed_descriptor, &circuit, &changed, &opening, &gkr_bytes,
        statement.commitment, statement.setup_id).is_err(), "GKR-bound descriptor mutation rejected");
    let mut changed = statement.clone(); changed.claims[0].point[0] += Fr::one();
    assert!(stage1b_verify_composed(&key, &descriptor, &circuit, &changed, &opening, &gkr_bytes,
        statement.commitment, statement.setup_id).is_err(), "derived point mutation rejected");
    let mut changed = statement.clone(); changed.claims[1].value += Fr::one();
    assert!(stage1b_verify_composed(&key, &descriptor, &circuit, &changed, &opening, &gkr_bytes,
        statement.commitment, statement.setup_id).is_err(), "projected value mutation rejected");
    let mut changed = statement.clone(); changed.claims[3].point[0] += Fr::one();
    assert!(stage1b_verify_composed(&key, &descriptor, &circuit, &changed, &opening, &gkr_bytes,
        statement.commitment, statement.setup_id).is_err(), "duplicate claim 3 point mutation rejected");
    let mut changed = statement.clone(); changed.claims[4].value += Fr::one();
    assert!(stage1b_verify_composed(&key, &descriptor, &circuit, &changed, &opening, &gkr_bytes,
        statement.commitment, statement.setup_id).is_err(), "duplicate claim 4 value mutation rejected");
    let mut changed = statement.clone(); changed.claims[5].value += Fr::one();
    assert!(stage1b_verify_composed(&key, &descriptor, &circuit, &changed, &opening, &gkr_bytes,
        statement.commitment, statement.setup_id).is_err(), "duplicate claim 5 value mutation rejected");
    let mut changed = statement.clone(); changed.claims[6].point[0] += Fr::one();
    assert!(stage1b_verify_composed(&key, &descriptor, &circuit, &changed, &opening, &gkr_bytes,
        statement.commitment, statement.setup_id).is_err(), "duplicate claim 6 point mutation rejected");
    println!("STAGE1B_FRESH_RECEIVER_PASS statement_bytes={} gkr_bytes={} opening_bytes={} mutants=17",
        statement_bytes.len(), gkr_bytes.len(), opening_bytes.len());
}

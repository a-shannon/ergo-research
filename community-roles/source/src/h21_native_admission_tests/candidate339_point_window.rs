//! Bounded physical H21 point-role GKR window. A held native producer supplies
//! 16 actual owner banks; this is not the all-owner X or a common PCS opening.
use super::*;
use ark_ff::{One, Zero};
use std::io::Write as _;
use std::os::windows::fs::MetadataExt;
use crate::{gkr::{self, GkrError, GkrProof, InputClaim}, point_membership,
    sparse::{self, Circuit}, sparse_stream_boolean, transcript::Transcript,
    work_tree_layout as layout};
use crate::packed_owner_assembly::H21PointProjection;

const FIRST_OWNER: usize = 844_672;
const COPIES: usize = 16;
const POINT_BITS: usize = 8_192;
const POINT_OFFSET: usize = 786_432;
const DOMAIN: &[u8] = b"h21-physical-point-window16-gkr-v1";

fn c343_timing(stage: &str, owner: Option<usize>, started: std::time::Instant)
    -> Result<(), String> {
    let seconds = started.elapsed().as_secs_f64();
    if let Some(owner) = owner {
        println!("C343_TIMING stage={stage} owner={owner} seconds={seconds:.6}");
    } else {
        println!("C343_TIMING stage={stage} seconds={seconds:.6}");
    }
    std::io::stdout().flush().map_err(|e| e.to_string())
}

fn transcript(root: [u8; 32], total: [u8; 28], first_owner: usize) -> Transcript {
    let mut t = Transcript::new(DOMAIN);
    t.append_bytes(b"h21-physical-parent-root", &root);
    t.append_bytes(b"h21-physical-parent-total", &total);
    t.append_u64(b"h21-physical-first-owner", first_owner as u64);
    t.append_u64(b"h21-physical-owner-count", COPIES as u64);
    t.append_u64(b"h21-physical-role", 3);
    t
}

fn verify_window(circuit: &Circuit, proof: &GkrProof, t: &mut Transcript)
    -> Result<InputClaim, GkrError> {
    let shape = sparse::validate_h21_point_window(circuit)?;
    gkr::verify_with_wiring(&[17], 1 << 18, proof, t,
        |t| sparse::bind(circuit, sparse::H21_POINT_WINDOW_LOG_COPIES, t),
        |_, r, u, v| sparse::wiring(circuit, &shape, r, u, v))
}

fn weight(point: &[Fr], index: usize) -> Fr {
    point.iter().enumerate().fold(Fr::one(), |acc, (bit, coordinate)| {
        acc * if (index >> bit) & 1 == 1 { *coordinate } else { Fr::one() - coordinate }
    })
}

struct HeldPointWindow<'p, 'a> {
    _producer: &'p NativeOwnerProducer<'a>,
    projection: H21PointProjection<'p, 'a>,
    rows: Vec<NativePackedRow>,
    circuit: Circuit,
    root: [u8; 32],
    total: [u8; 28],
    first_owner: usize,
}

impl<'p, 'a> HeldPointWindow<'p, 'a> {
    fn new(producer: &'p NativeOwnerProducer<'a>, plan: &WorkTreeHistoryPlan,
        prefix: &NativePrefix, first_owner: usize) -> Result<Self, String> {
        if first_owner % COPIES != 0 || first_owner.checked_add(COPIES)
            .map_or(true, |end| end > plan.slots()) {
            return Err("H21 point window owner alignment/range".into());
        }
        let projection = producer.h21_point_projection()?;
        let circuit = point_membership::build()?.circuit;
        sparse::validate_h21_point_window(&circuit).map_err(|e| e.to_string())?;
        let mut rows = Vec::new();
        rows.try_reserve_exact(COPIES).map_err(|_| "H21 point window row allocation")?;
        for owner in first_owner..first_owner + COPIES {
            let produce_started = std::time::Instant::now();
            let row = producer.produce(owner)?;
            c343_timing("produce", Some(owner), produce_started)?;
            let identity_started = std::time::Instant::now();
            row.validate_identity_for_history_test(plan, prefix, owner)?;
            if row.packed_bytes().len() != OWNER_ROW_BYTES {
                return Err("H21 point window packed row length".into());
            }
            let header = prefix.header(owner + 1)?;
            let fields = crate::serializer::Fields::from_header(&header)?;
            let expected = point_membership::witness(fields.pk, fields.w)?;
            if expected.len() != POINT_BITS { return Err("H21 point witness extent".into()); }
            for (local, bit) in expected.into_iter().enumerate() {
                let wire = projection.global_wire(owner, local)?;
                if wire != (owner << 20) + POINT_OFFSET + local
                    || ((row.packed_bytes()[(POINT_OFFSET + local) / 8]
                        >> ((POINT_OFFSET + local) % 8)) & 1 != 0) != bit {
                    return Err(format!("H21 point bank source/author mismatch owner={owner} local={local}"));
                }
            }
            c343_timing("identity", Some(owner), identity_started)?;
            rows.push(row);
        }
        Ok(Self { _producer: producer, projection, rows, circuit,
            root: prefix.root(), total: prefix.total_be28(), first_owner })
    }

    fn bit(&self, copy: usize, local: usize, bank: usize) -> Result<bool, String> {
        if copy >= COPIES || local >= POINT_BITS || bank + POINT_BITS > OWNER_ROW_BITS
            || bank % POINT_BITS != 0 {
            return Err("H21 point source bank/copy bounds".into());
        }
        let bytes = self.rows[copy].packed_bytes();
        let wire = bank + local;
        Ok(bytes[wire / 8] & (1 << (wire % 8)) != 0)
    }

    fn load(&self, copy: usize) -> Result<Vec<Fr>, GkrError> {
        if copy >= COPIES || self.rows[copy].owner() != self.first_owner + copy {
            return Err(GkrError::InvalidInputWidth);
        }
        (0..POINT_BITS).map(|local| self.bit(copy, local, POINT_OFFSET)
            .map(|bit| Fr::from(bit as u64)).map_err(|_| GkrError::InvalidInputWidth)).collect()
    }

    fn dense(&self, point: &[Fr], bank: usize) -> Result<Fr, String> {
        if point.len() != 17 { return Err("H21 point window terminal width".into()); }
        let mut sum = Fr::zero();
        for copy in 0..COPIES { for local in 0..POINT_BITS {
            if self.bit(copy, local, bank)? {
                sum += weight(point, copy * POINT_BITS + local);
            }
        }}
        Ok(sum)
    }

    fn project(&self, terminal: &InputClaim) -> Result<Vec<Fr>, String> {
        if terminal.point.len() != 17 { return Err("H21 point window terminal width".into()); }
        let mut h21_point = terminal.point.clone();
        let high = self.first_owner >> 4;
        h21_point.extend((0..17).map(|bit| Fr::from(((high >> bit) & 1) as u64)));
        let projected = self.projection.project(&h21_point)?;
        let verifier_owned = layout::embed_bank(POINT_OFFSET, POINT_BITS, 21, &h21_point)?;
        if projected != verifier_owned || projected.len() != 41 {
            return Err("H21 point verifier projection differs from source".into());
        }
        Ok(projected)
    }
}

fn c343_header_q14908_join(producer: &NativeOwnerProducer<'_>,
    plan: &WorkTreeHistoryPlan, prefix: &NativePrefix)
    -> Result<super::candidate344_closed_max_cap_census::PlacedReadCensus, String> {
    use crate::header_daa_row_placement::{Relation, RowPlan, SourceRead};
    use crate::h21_scheduled_max_cap::Plan as Scheduled;
    const OWNER: usize = 845_759;
    const ROWS: usize = 1 << 19;
    const WIDTH: usize = 1 << 20;

    let plan_started = std::time::Instant::now();
    let roster = crate::daa_history_roster::DaaHistoryRoster::compile(plan)?;
    let scheduled = Scheduled::eligible08();
    let row_plan = RowPlan::new(&roster, &scheduled)?;
    let batch = row_plan.stage_owner(OWNER)?;
    let target = batch.active_operands().find(|operand|
        operand.relation == Relation::Header && operand.row == OWNER * ROWS + 14_908
            && operand.wire == OWNER * WIDTH + 526_330)
        .ok_or("retained native HEADER NOT q14908/X526330")?;
    c343_timing("header_plan", Some(OWNER), plan_started)?;

    let lease_started = std::time::Instant::now();
    let mut lease = producer.header_source_lease(OWNER)?;
    let value = match batch.resolve_one(target.occurrence, target.side, &lease)? {
        SourceRead::Header { operand, value } if operand == target => value,
        _ => return Err("native HEADER source read unresolved or changed".into()),
    };
    c343_timing("header_lease_read", Some(OWNER), lease_started)?;

    let produce_started = std::time::Instant::now();
    let row = producer.produce(OWNER)?;
    c343_timing("header_produce", Some(OWNER), produce_started)?;
    let identity_started = std::time::Instant::now();
    row.validate_identity_for_history_test(plan, prefix, OWNER)?;
    let local = target.wire - OWNER * WIDTH;
    let packed = row.packed_bytes()[local / 8] & (1 << (local % 8)) != 0;
    if value != packed { return Err("native HEADER lease/packed owner bit mismatch".into()); }
    c343_timing("header_identity", Some(OWNER), identity_started)?;

    let census = super::candidate344_closed_max_cap_census::census_placed_reads(&batch, &lease)?;

    let mutant_started = std::time::Instant::now();
    let admitted = lease.read_count_for_test();
    lease.wrong_author_mutant_for_test();
    let error = batch.resolve_one(target.occurrence, target.side, &lease).err()
        .ok_or("wrong native HEADER author admitted")?;
    if !error.contains("author mismatch before read admission")
        || lease.read_count_for_test() != admitted {
        return Err("wrong native HEADER author reached value read".into());
    }
    c343_timing("header_wrong_author", Some(OWNER), mutant_started)?;
    Ok(census)
}

#[test]
fn c339_window_profile_is_canonical_and_does_not_widen_small_sparse() -> Result<(), String> {
    let mut circuit = point_membership::build()?.circuit;
    if !matches!(sparse::validate(&circuit, 4), Err(GkrError::RepetitionLimit)) {
        return Err("small-profile sparse cap changed".into());
    }
    let shape = sparse::validate_h21_point_window(&circuit).map_err(|e| e.to_string())?;
    if (shape.copies, shape.input_len, shape.row_count) != (16, 1 << 17, 1 << 18) {
        return Err("H21 point window geometry".into());
    }
    circuit.terms[0].gate.c0 += Fr::one();
    if !matches!(sparse::validate_h21_point_window(&circuit), Err(GkrError::InvalidWireIndex)) {
        return Err("altered canonical point relation admitted".into());
    }
    Ok(())
}

#[test]
#[ignore = "one-use pinned frame and bounded GKR runner required"]
fn c339_h21_actual_sixteen_owner_point_gkr() -> Result<(), String> {
    if std::env::var("NIPOPOW_C339_POINT_WINDOW_ACTUAL").as_deref() != Ok("1") {
        return Err("explicit C339 point-window mode required".into());
    }
    let path = std::env::var_os("NIPOPOW_H21_FRAME").ok_or("pinned H21 frame path required")?;
    let path = Path::new(&path);
    if !path.is_absolute() { return Err("H21 frame path must be absolute".into()); }
    let before = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if !before.is_file() || before.file_attributes() & 0x400 != 0 || before.len() != FRAME_BYTES {
        return Err("H21 frame regular-file/length preflight".into());
    }
    let file = File::open(path).map_err(|e| e.to_string())?;
    if file.metadata().map_err(|e| e.to_string())?.len() != FRAME_BYTES {
        return Err("opened H21 frame length".into());
    }
    let prefix_started = std::time::Instant::now();
    let mut frame = FrameReader::new(BufReader::with_capacity(CHUNK, file), FRAME_BYTES)?;
    preamble(&mut frame, 1_827_839, N as u32)?;
    let (prefix, extensions) = {
        let mut headers = HeaderIter::new(&mut frame, N);
        let prefix = NativePrefix::from_raw_iter(N, &mut headers)?;
        if headers.remaining != 0 { return Err("H21 frame RAW records incomplete".into()); }
        (prefix, headers.extensions)
    };
    if prefix.header_count() != N || frame.offset != PREFIX_BYTES || extensions != EXTENSIONS {
        return Err("H21 frame prefix/extension census".into());
    }
    c343_timing("prefix_tree", None, prefix_started)?;
    let finish_started = std::time::Instant::now();
    frame.finish(PREFIX_BYTES, TAIL_BYTES, FRAME_SHA256)?;
    let after = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if after.len() != before.len() || after.modified().map_err(|e| e.to_string())?
        != before.modified().map_err(|e| e.to_string())? {
        return Err("H21 frame changed during read".into());
    }
    c343_timing("frame_finish", None, finish_started)?;

    let plan_started = std::time::Instant::now();
    let plan = WorkTreeHistoryPlan::compile(N as u64, H, prefix.root(), prefix.total_be28())?;
    validate_native_plan_input(&plan, &prefix)?;
    c343_timing("history_plan", None, plan_started)?;
    let producer_started = std::time::Instant::now();
    let producer = NativeOwnerProducer::new_for_history(&plan, &prefix)?;
    c343_timing("producer_constructor", None, producer_started)?;
    let held = HeldPointWindow::new(&producer, &plan, &prefix, FIRST_OWNER)?;
    let mut prover_t = transcript(held.root, held.total, held.first_owner);
    let gkr_started = std::time::Instant::now();
    let (proof, produced) = sparse_stream_boolean::prove_h21_point_window(
        &held.circuit, |copy| held.load(copy), &mut prover_t).map_err(|e| e.to_string())?;
    c343_timing("gkr_prove", None, gkr_started)?;
    let verify_started = std::time::Instant::now();
    let bytes = gkr::encode_proof(&proof)?;
    if bytes.len() != (7 * 17 + 3) * 32 { return Err("H21 point window GKR extent".into()); }
    let decoded = gkr::decode_dimensions(&[17], &bytes)?;
    if decoded != proof { return Err("H21 point window GKR codec".into()); }
    let mut verifier_t = transcript(held.root, held.total, held.first_owner);
    let verified = verify_window(&held.circuit, &decoded, &mut verifier_t)
        .map_err(|e| e.to_string())?;
    c343_timing("gkr_codec_verify", None, verify_started)?;
    let terminal_started = std::time::Instant::now();
    if verified != produced || verified.point.len() != 17
        || held.dense(&verified.point, POINT_OFFSET)? != verified.value {
        return Err("H21 point source/GKR terminal differs".into());
    }
    let projected = held.project(&verified)?;
    if projected.len() != 41 { return Err("H21 point projected X width".into()); }

    // One packed source bit changes while the GKR proof, all other row bytes,
    // circuit, public prefix and owner positions remain fixed.
    let mut changed = held.rows[0].packed_bytes().to_vec();
    changed[POINT_OFFSET / 8] ^= 1;
    let mut one_bit_value = held.dense(&verified.point, POINT_OFFSET)?;
    let contribution = weight(&verified.point, 0);
    if contribution.is_zero() { return Err("isolated source bit has zero terminal weight".into()); }
    one_bit_value += if changed[POINT_OFFSET / 8] & 1 != 0 { contribution } else { -contribution };
    if one_bit_value == verified.value { return Err("one-bit source mutation undetected".into()); }

    let mut wrong_owner_t = transcript(held.root, held.total, held.first_owner + COPIES);
    if verify_window(&held.circuit, &decoded, &mut wrong_owner_t).is_ok() {
        return Err("wrong owner-window transcript admitted".into());
    }
    let mut bank_fault_found = false;
    for bit in 0..7 {
        let alternate = POINT_OFFSET ^ (1 << (13 + bit));
        if held.dense(&verified.point, alternate)? != verified.value {
            let mut mutant = projected.clone();
            mutant[13 + bit] = Fr::one() - mutant[13 + bit];
            if mutant == projected { return Err("wrong-bank coordinate unchanged".into()); }
            bank_fault_found = true;
            break;
        }
    }
    if !bank_fault_found { return Err("no isolated wrong-bank source difference".into()); }
    c343_timing("terminal_and_mutants", None, terminal_started)?;
    println!("C339_POINT_WINDOW_PASS owners=16 input17_to_x41=true gkr_bytes={} same_source=true single_bit_rejected=true wrong_owner_rejected=true wrong_bank_rejected=true full_h21=false", bytes.len());
    std::io::stdout().flush().map_err(|e| e.to_string())?;
    drop(held);
    let placed_census = c343_header_q14908_join(&producer, &plan, &prefix)?;
    println!("C343_TIMING_PASS frame_parses=1 point_owners=16 header_owner=845759 header_q14908=true full_h21=false");
    std::io::stdout().flush().map_err(|e| e.to_string())?;
    super::candidate344_closed_max_cap_census::join_closed_max_to_cap(
        &plan, &prefix, &producer)?;
    println!(
        "C344_MAX_CAP_CENSUS_PASS frame_parses=1 max_owners=7683 cap_imports=448 placed_row_terms={} placed_active_occurrences={} placed_unresolved_occurrences={} placed_unresolved_unique_wires={} global_x_row=false full_h21=false",
        placed_census.row_terms, placed_census.active_occurrences,
        placed_census.unresolved_occurrences, placed_census.unresolved_unique_wires,
    );
    std::io::stdout().flush().map_err(|e| e.to_string())?;
    Ok(())
}

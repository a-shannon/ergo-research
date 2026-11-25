//! Local H21 A/B checkpoint endpoint join. This is source custody, not PCS admission.

use super::*;
use crate::{
    checkpoint_output_layout::CheckpointPublic,
    checkpoint_role4_internal::CheckpointRole4Adapter,
    daa_history_roster::{DaaHistoryRoster, OwnerClass},
    packed_owner_assembly::{HeaderSourceBinding, NativeHeaderSourceLease},
    sparse_stream_roster::EdgeTerm,
    work_tree_layout,
};
use ark_ff::{One, Zero};
use std::os::windows::fs::MetadataExt;

const WIDTH: usize = 1 << 20;
const OWNER_BYTES: usize = WIDTH / 8;
const HEADER_BITS: usize = 514 * 8 + 10;
const UPPER_BITS: usize = 224;
const ENDPOINT_BITS: usize = HEADER_BITS + UPPER_BITS;
const C319_FIXTURE_SHA256: &str =
    "e901b368a23b4356ca7752e4e9898583cecbc1c981b5ca19dd5c2676f848b65f";
const C319_OWNERS: [usize; 4] = [1_810_840, 1_810_841, 1_810_902, 1_810_903];
const C319_ROW_SHA256: [&str; 4] = [
    "7b37554704db4a054b2946b823a88efe3a24703311fd0ba24e3a48429c7708d0",
    "2f59c1cffa65153ba65b43bb7c30d86f318b965de58fd184a9c3b8e64b316974",
    "19ca069f9477120dc7f5f44299d9146cc62f55007c2f0a80a59decec0d873a2a",
    "8bb48ee7e688dad89b5ab3ef619bd5b629a785b4b34a068622110599512562a4",
];
const RAW_A: &[u8] = include_bytes!("../../fixtures/section3-A_control-checkpoint.raw");
const RAW_B: &[u8] = include_bytes!("../../fixtures/section3-B_candidate-checkpoint.raw");

struct Control {
    label: &'static str,
    h: usize,
    f: usize,
    raw: &'static [u8],
    raw_sha256: &'static str,
    floor_decimal: &'static str,
    audit_decimal: &'static str,
}

const CONTROLS: [Control; 2] = [
    Control {
        label: "A",
        h: 1_810_842,
        f: 1_810_905,
        raw: RAW_A,
        raw_sha256: "3af4be948ea36e8438ecb3dfcfe5863b55d8b760373cd9872c2a85b102f168dd",
        floor_decimal: "2745402775092498268160",
        audit_decimal: "1406030148754472960",
    },
    Control {
        label: "B",
        h: 1_810_841,
        f: 1_810_904,
        raw: RAW_B,
        raw_sha256: "0f881c0d2546479acb69fd2970b75fb6e0789c0b28d0c515696f19da1bdef16d",
        floor_decimal: "2745402699639720771584",
        audit_decimal: "1406105601531969536",
    },
];

fn decimal(value: &str) -> Result<BigUint, String> {
    BigUint::parse_bytes(value.as_bytes(), 10).ok_or("C391 decimal control".into())
}

fn be28(value: &BigUint) -> Result<[u8; 28], String> {
    let bytes = value.to_bytes_be();
    if bytes.len() > 28 {
        return Err("C391 work width".into());
    }
    let mut result = [0u8; 28];
    result[28 - bytes.len()..].copy_from_slice(&bytes);
    Ok(result)
}

fn hash(bytes: &[u8]) -> Result<String, String> {
    Ok(hex(&role0_sha256(bytes)?))
}

fn packed_bit(row: &NativePackedRow, owner: usize, physical_wire: usize) -> Result<bool, String> {
    if row.owner() != owner
        || physical_wire / WIDTH != owner
        || row.packed_bytes().len() != OWNER_BYTES
    {
        return Err("C391 packed source owner/width".into());
    }
    let local = physical_wire % WIDTH;
    Ok((row.packed_bytes()[local / 8] >> (local % 8)) & 1 == 1)
}

fn require_packed_bit(
    row: &NativePackedRow,
    owner: usize,
    wire: usize,
    bit: bool,
) -> Result<(), String> {
    if packed_bit(row, owner, wire)? != bit {
        return Err("C391 typed bit differs from packed X".into());
    }
    Ok(())
}

fn expected_bit(control: &Control, floor: &[u8; 28], row: usize) -> Result<bool, String> {
    if row < 514 * 8 {
        Ok((control.raw.get(row / 8).copied().unwrap_or(0) >> (row % 8)) & 1 == 1)
    } else if row < HEADER_BITS {
        Ok((control.raw.len() >> (row - 514 * 8)) & 1 == 1)
    } else if row < ENDPOINT_BITS {
        let bit = row - HEADER_BITS;
        Ok((floor[27 - bit / 8] >> (bit % 8)) & 1 == 1)
    } else {
        Err("C391 checkpoint output row".into())
    }
}

fn read_frame() -> Result<NativePrefix, String> {
    let path = std::env::var_os("NIPOPOW_H21_FRAME").ok_or("C391 H21 frame path required")?;
    let path = Path::new(&path);
    if !path.is_absolute() {
        return Err("C391 H21 frame absolute path".into());
    }
    let before = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if !before.is_file() || before.file_attributes() & 0x400 != 0 || before.len() != FRAME_BYTES {
        return Err("C391 H21 frame regular-file/length".into());
    }
    let file = File::open(path).map_err(|e| e.to_string())?;
    let mut frame = FrameReader::new(BufReader::with_capacity(CHUNK, file), FRAME_BYTES)?;
    preamble(&mut frame, 1_827_839, N as u32)?;
    let (prefix, extensions) = {
        let mut headers = HeaderIter::new(&mut frame, N);
        let prefix = NativePrefix::from_raw_iter(N, &mut headers)?;
        if headers.remaining != 0 {
            return Err("C391 H21 records incomplete".into());
        }
        (prefix, headers.extensions)
    };
    if prefix.header_count() != N || frame.offset != PREFIX_BYTES || extensions != EXTENSIONS {
        return Err("C391 H21 prefix/extents".into());
    }
    frame.finish(PREFIX_BYTES, TAIL_BYTES, FRAME_SHA256)?;
    let after = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if after.len() != before.len()
        || after.modified().map_err(|e| e.to_string())?
            != before.modified().map_err(|e| e.to_string())?
    {
        return Err("C391 H21 frame changed during read".into());
    }
    Ok(prefix)
}

fn checkpoint_edges(
    admitted: &crate::checkpoint_role4_internal::AdmittedCheckpointRole4<'_, '_>,
    binding: &crate::checkpoint_role4_internal::CheckpointRole4Binding,
    owner: usize,
) -> Result<Vec<EdgeTerm>, String> {
    let base = binding.checkpoint.base;
    if binding.checkpoint.live_rows != ENDPOINT_BITS {
        return Err("C391 role4 live-row count".into());
    }
    let end = base
        .checked_add(ENDPOINT_BITS)
        .ok_or("C391 role4 row range")?;
    let mut result = Vec::new();
    let total = admitted.visit_endpoint(binding, true, owner, |edge| {
        if (base..end).contains(&edge.term.row) {
            result.push(edge);
        }
        Ok(())
    })?;
    if result.len() > total {
        return Err("C391 role4 endpoint callback count".into());
    }
    Ok(result)
}

fn check_profile(
    control: &Control,
    other: &Control,
    plan: &WorkTreeHistoryPlan,
    prefix: &NativePrefix,
    producer: &NativeOwnerProducer<'_>,
    rows: &BTreeMap<usize, NativePackedRow>,
) -> Result<(), String> {
    if control.f != control.h + 63
        || control.raw.len() != 220
        || hash(control.raw)? != control.raw_sha256
        || prefix.raw(control.h)? != control.raw
    {
        return Err(format!("C391 {} independent RAW control", control.label));
    }
    let (lower, floor) = prefix.interval(control.f)?;
    let _ = lower;
    let total = BigUint::from_bytes_be(&prefix.total_be28());
    let floor_expected = decimal(control.floor_decimal)?;
    let audit_expected = decimal(control.audit_decimal)?;
    if BigUint::from_bytes_be(&floor) != floor_expected
        || floor_expected >= total
        || &total - &floor_expected != audit_expected
    {
        return Err(format!("C391 {} independent W(f)/F control", control.label));
    }
    let public = CheckpointPublic {
        raw: control.raw.to_vec(),
        floor_work: be28(&floor_expected)?,
        audit_work: be28(&audit_expected)?,
    };
    let adapter = CheckpointRole4Adapter::new(plan, control.h as u64, public)?;
    // The verifier's expected tuple is separate from the adapter's descriptor.
    if adapter
        .admit_query((other.h as u64, other.f as u64))
        .is_ok()
    {
        return Err("C391 cross-profile query substituted".into());
    }
    let admitted = adapter.admit_query((control.h as u64, control.f as u64))?;
    let binding = admitted.descriptor();
    let d = &binding.checkpoint;
    if d.root != prefix.root()
        || d.total != prefix.total_be28()
        || d.headers != N as u64
        || d.h != control.h as u64
        || d.f != control.f as u64
        || d.depth != 64
        || d.slot_log != H
        || d.input_log != 41
        || d.row_log != 41
        || d.live_rows != ENDPOINT_BITS
    {
        return Err("C391 checkpoint descriptor/parent".into());
    }
    let baseline = work_tree_layout::shared_baseline()?;
    if baseline.header_alias_wires.len() != HEADER_BITS + 64
        || baseline.endpoints.upper.len() != UPPER_BITS
    {
        return Err("C391 physical endpoint template widths".into());
    }
    let header_owner = control.h - 1;
    let floor_owner = control.f - 2;
    let header_row = rows.get(&header_owner).ok_or("C391 HEADER row absent")?;
    let floor_row = rows.get(&floor_owner).ok_or("C391 Upper row absent")?;
    let header_binding = HeaderSourceBinding::for_plan(plan, header_owner)?;
    let header_lease = producer.header_source_lease(header_owner)?;
    header_lease.check_binding(&header_binding)?;
    header_lease.check_author()?;
    let work_lease = producer.work_local_lease(floor_owner)?;
    let work_parent = producer.work_local_parent(floor_owner)?;
    let upper_publication = producer.work_upper_publication(floor_owner, &work_lease)?;
    let upper = upper_publication.checked_upper(
        work_parent.root,
        work_parent.total,
        work_parent.profile,
        &work_parent.cut,
        floor_owner,
    )?;
    if upper.len() != UPPER_BITS {
        return Err("C391 complete typed Upper source".into());
    }

    let mut first_header = None;
    let mut first_upper = None;
    for (owner, start, count, row) in [
        (header_owner, 0usize, HEADER_BITS, header_row),
        (floor_owner, HEADER_BITS, UPPER_BITS, floor_row),
    ] {
        let edges = checkpoint_edges(&admitted, &binding, owner)?;
        if edges.len() != count {
            return Err(format!(
                "C391 {} endpoint count owner={owner}",
                control.label
            ));
        }
        for (index, edge) in edges.iter().enumerate() {
            let output_row = start + index;
            let bit = expected_bit(control, &floor, output_row)?;
            let wire = if output_row < HEADER_BITS {
                baseline.header_alias_wires[output_row]
            } else {
                baseline.endpoints.upper[output_row - HEADER_BITS]
            };
            let physical = owner
                .checked_mul(WIDTH)
                .and_then(|base| base.checked_add(wire))
                .ok_or("C391 physical input wire overflow")?;
            if edge.term.row != d.base + output_row
                || edge.source_slot != d.base >> 19
                || edge.family_row != output_row
                || edge.term.gate.left != physical
                || edge.term.gate.right != 0
                || edge.term.gate.c0 != -Fr::from(bit as u64)
                || edge.term.gate.c1 != Fr::one()
                || edge.term.gate.c2 != Fr::zero()
                || edge.term.gate.c3 != Fr::zero()
            {
                return Err(format!(
                    "C391 {} endpoint geometry/coefficient row={output_row}",
                    control.label
                ));
            }
            require_packed_bit(row, owner, physical, bit)?;
            if output_row < HEADER_BITS {
                if header_lease.read_header_bit(&header_binding, physical)? != Some(bit) {
                    return Err(format!(
                        "C391 {} HEADER typed author row={output_row}",
                        control.label
                    ));
                }
                if first_header.is_none() {
                    first_header = Some((physical, bit));
                }
            } else {
                let &(actual, value) = upper
                    .get(output_row - HEADER_BITS)
                    .ok_or("C391 Upper source index")?;
                if actual != physical || value != Fr::from(bit as u64) {
                    return Err(format!(
                        "C391 {} Upper typed author row={output_row}",
                        control.label
                    ));
                }
                if first_upper.is_none() {
                    first_upper = Some((physical, bit));
                }
            }
        }
    }

    // Each rejection changes only one authority or value after the healthy join.
    let mut bad_root = binding.clone();
    bad_root.checkpoint.root[0] ^= 1;
    let mut called = 0usize;
    if admitted
        .visit_endpoint(&bad_root, true, header_owner, |_| {
            called += 1;
            Ok(())
        })
        .is_ok()
        || called != 0
    {
        return Err("C391 wrong root accepted before source read".into());
    }
    let (header_wire, header_bit) = first_header.ok_or("C391 first HEADER endpoint absent")?;
    let wrong_author = NativeHeaderSourceLease::wrong_author_for_test(
        header_binding.clone(),
        header_wire,
        header_bit,
    );
    if wrong_author
        .read_header_bit(&header_binding, header_wire)
        .is_ok()
    {
        return Err("C391 same-value wrong HEADER author accepted".into());
    }
    let mut changed_header = header_row.packed_bytes().to_vec();
    let local = header_wire % WIDTH;
    changed_header[local / 8] ^= 1 << (local % 8);
    let changed_header = header_row.with_packed_bytes_for_test(&changed_header)?;
    if require_packed_bit(&changed_header, header_owner, header_wire, header_bit).is_ok() {
        return Err("C391 changed HEADER X bit accepted".into());
    }
    let (upper_wire, upper_bit) = first_upper.ok_or("C391 first Upper endpoint absent")?;
    let mut changed_upper = floor_row.packed_bytes().to_vec();
    let local = upper_wire % WIDTH;
    changed_upper[local / 8] ^= 1 << (local % 8);
    let changed_upper = floor_row.with_packed_bytes_for_test(&changed_upper)?;
    if require_packed_bit(&changed_upper, floor_owner, upper_wire, upper_bit).is_ok() {
        return Err("C391 changed Upper X bit accepted".into());
    }
    let mut wrong_cut = work_parent.cut.clone();
    if wrong_cut.is_empty() {
        return Err("C391 eligible08 cut identity absent".into());
    }
    wrong_cut[0] ^= 1;
    if upper_publication
        .checked_upper(
            work_parent.root,
            work_parent.total,
            work_parent.profile,
            &wrong_cut,
            floor_owner,
        )
        .is_ok()
    {
        return Err("C391 wrong cut accepted by typed Upper source".into());
    }
    if control.label == "B" {
        // Keep B's valid RAW, h and f, while substituting A's coherent
        // floor/audit pair. Admission alone cannot bind W(f) to B's history.
        let a_floor = be28(&decimal(other.floor_decimal)?)?;
        let a_audit = be28(&decimal(other.audit_decimal)?)?;
        if a_floor == floor {
            return Err("C391 A/B floor controls do not differ".into());
        }
        let swapped = CheckpointPublic {
            raw: control.raw.to_vec(),
            floor_work: a_floor,
            audit_work: a_audit,
        };
        let swapped_adapter = CheckpointRole4Adapter::new(plan, control.h as u64, swapped)
            .map_err(|e| format!("C391 supported B work swap constructor rejected: {e}"))?;
        let swapped_admitted = swapped_adapter
            .admit_query((control.h as u64, control.f as u64))
            .map_err(|e| format!("C391 supported B work swap query rejected: {e}"))?;
        let swapped_binding = swapped_admitted.descriptor();
        let swapped_upper = checkpoint_edges(&swapped_admitted, &swapped_binding, floor_owner)?;
        if swapped_upper.len() != UPPER_BITS {
            return Err("C391 supported B work swap Upper endpoint count".into());
        }
        let mut rejected_row = None;
        for (index, edge) in swapped_upper.iter().enumerate() {
            let a_bit = (a_floor[27 - index / 8] >> (index % 8)) & 1 == 1;
            let b_bit = (floor[27 - index / 8] >> (index % 8)) & 1 == 1;
            if a_bit == b_bit {
                continue;
            }
            let wire = floor_owner * WIDTH + baseline.endpoints.upper[index];
            if edge.term.row != swapped_binding.checkpoint.base + HEADER_BITS + index
                || edge.term.gate.left != wire
                || edge.term.gate.right != 0
                || edge.term.gate.c0 != -Fr::from(a_bit as u64)
                || edge.term.gate.c1 != Fr::one()
                || edge.term.gate.c2 != Fr::zero()
                || edge.term.gate.c3 != Fr::zero()
            {
                return Err("C391 B/A work swap endpoint geometry/coefficient".into());
            }
            let &(actual, typed_value) = upper
                .get(index)
                .ok_or("C391 B/A work swap typed Upper index")?;
            if actual != wire
                || typed_value != Fr::from(b_bit as u64)
                || packed_bit(floor_row, floor_owner, wire)? != b_bit
            {
                return Err("C391 B WorkUpper/packed source control".into());
            }
            if require_packed_bit(floor_row, floor_owner, wire, a_bit).is_ok()
                || typed_value == Fr::from(a_bit as u64)
            {
                return Err("C391 A work coefficient accepted by B source".into());
            }
            rejected_row = Some(index);
            break;
        }
        let rejected_row =
            rejected_row.ok_or("C391 B/A work swap has no differing Upper coefficient")?;
        println!(
            "C391_B_A_WORK_REJECT h={} f={} supported_query=true upper_row={} a_bit={} b_bit={}",
            control.h,
            control.f,
            rejected_row,
            (a_floor[27 - rejected_row / 8] >> (rejected_row % 8)) & 1,
            (floor[27 - rejected_row / 8] >> (rejected_row % 8)) & 1
        );

        // Two genuine HEADER leases expose the same zero padding bit. A's
        // lease cannot answer B's wire even when the carried value is equal.
        let a_header_owner = other.h - 1;
        let a_header_binding = HeaderSourceBinding::for_plan(plan, a_header_owner)?;
        let a_header_lease = producer.header_source_lease(a_header_owner)?;
        let padding_row = control.raw.len() * 8;
        if control.raw.len() != other.raw.len() || padding_row >= 514 * 8 {
            return Err("C391 A/B common HEADER padding row absent".into());
        }
        let local_wire = baseline.header_alias_wires[padding_row];
        let b_wire = header_owner * WIDTH + local_wire;
        let a_wire = a_header_owner * WIDTH + local_wire;
        if header_lease.read_header_bit(&header_binding, b_wire)? != Some(false)
            || a_header_lease.read_header_bit(&a_header_binding, a_wire)? != Some(false)
        {
            return Err("C391 A/B same-value HEADER owner control".into());
        }
        if a_header_lease
            .read_header_bit(&header_binding, b_wire)
            .is_ok()
        {
            return Err("C391 same-value wrong HEADER owner accepted".into());
        }

        // A second producer has the same immutable plan and frame, but its
        // Work LOCAL lease does not belong to the original producer instance.
        let foreign_producer = NativeOwnerProducer::new_for_history(plan, prefix)?;
        let foreign_work_lease = foreign_producer.work_local_lease(floor_owner)?;
        let error = producer
            .work_upper_publication(floor_owner, &foreign_work_lease)
            .err()
            .ok_or("C391 foreign WorkUpper lease accepted")?;
        if error != "Work LOCAL exact producer source identity" {
            return Err(format!(
                "C391 foreign WorkUpper lease rejected for wrong reason: {error}"
            ));
        }
        println!(
            "C391_B_SOURCE_OWNER_REJECT header_same_value=true work_upper_foreign_producer=true"
        );
    }
    println!("C391_PROFILE label={} h={} f={} header_owner={} upper_owner={} header_bits={} upper_bits={} raw_sha256={} floor_work={} audit_work={} typed_author=true same_packed_x=true cross_query_rejected=true wrong_root_rejected=true wrong_author_rejected=true changed_header_rejected=true changed_upper_rejected=true wrong_cut_rejected=true",
        control.label, control.h, control.f, header_owner, floor_owner, HEADER_BITS, UPPER_BITS,
        control.raw_sha256, control.floor_decimal, control.audit_decimal);
    Ok(())
}

/// Replays C319's four exact rows, then checks the actual role4 consumer and typed sources.
#[test]
#[ignore = "C391 H21 actual-frame typed endpoint join requires reviewed bounded runner"]
fn c391_ab_typed_role4_from_pinned_frame() -> Result<(), String> {
    println!(
        "C391_BEGIN frame_sha256={} c319_fixture_sha256={} profiles=2 rows=4 proof=false",
        FRAME_SHA256, C319_FIXTURE_SHA256
    );
    let prefix = read_frame()?;
    println!(
        "C391_FRAME_PASS headers={} root={} total_be28={}",
        prefix.header_count(),
        hex(&prefix.root()),
        hex(&prefix.total_be28())
    );
    let plan = WorkTreeHistoryPlan::compile(N as u64, H, prefix.root(), prefix.total_be28())?;
    validate_native_plan_input(&plan, &prefix)?;
    let roster = DaaHistoryRoster::compile(&plan)?;
    let producer = NativeOwnerProducer::new_for_history(&plan, &prefix)?;
    let mut rows = BTreeMap::new();
    let mut c319_fixture = Vec::with_capacity(C319_OWNERS.len() * OWNER_BYTES);
    for (index, owner) in C319_OWNERS.into_iter().enumerate() {
        if roster.owner_class(owner as u64)? != OwnerClass::Carry {
            return Err(format!("C391 C319 owner {owner} not Carry"));
        }
        let row = producer.produce(owner)?;
        let digest = role0_sha256(row.packed_bytes())?;
        row.validate_identity_for_history_test(&plan, &prefix, owner)?;
        row.validate_source_copy_for_history_test(&row, owner, prefix.root(), prefix.total_be28())?;
        if hex(&digest) != C319_ROW_SHA256[index] {
            return Err(format!("C391 C319 owner {owner} changed"));
        }
        c319_fixture.extend_from_slice(row.packed_bytes());
        if rows.insert(owner, row).is_some() {
            return Err("C391 duplicate C319 owner".into());
        }
    }
    if c319_fixture.len() != 524_288 || hash(&c319_fixture)? != C319_FIXTURE_SHA256 {
        return Err("C391 exact C319 four-row fixture drift".into());
    }
    println!(
        "C391_C319_ROWS_REPLAY owners=1810840,1810841,1810902,1810903 bytes={} sha256={}",
        c319_fixture.len(),
        C319_FIXTURE_SHA256
    );
    check_profile(&CONTROLS[0], &CONTROLS[1], &plan, &prefix, &producer, &rows)?;
    check_profile(&CONTROLS[1], &CONTROLS[0], &plan, &prefix, &producer, &rows)?;
    println!("C391_END profiles=2 rows=4 header_bits=8244 upper_bits=448 c319_replayed=true typed_source=true role4_endpoint=true common_pcs=false full_proof=false client=false");
    Ok(())
}

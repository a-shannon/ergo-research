//! Exact recent continuation in the r4 local mainnet profile, header versions 2 to 4.
//! Mount as a sibling of native_audit inside the full certificate verifier.

use super::{native_audit::AuditedHistory, VerifiedFullStructural};
use crate::{daa_finish, daa_integer::Epoch, daa_regression, native_autolykos_pow, work_tree_work};
use ergo_header_core::{blake2b256, Header};
use num_bigint::{BigInt, BigUint};
use num_traits::ToPrimitive;

const MAGIC: &[u8; 8] = b"NPTAIL01";
const CONTEXT: usize = 1088;
const LOCAL_START: u32 = 845_760;
const K0: u32 = 64;
const MAX_CAP: u128 = 1u128 << 64;
const RAW_LIMIT: usize = 514;
const EPOCH: usize = 128;
const WORKSPACE_EXHAUSTED: &str = "exact tail workspace exhausted";

#[derive(Clone, Copy)]
struct Row { difficulty: u128, timestamp: i64 }

pub(super) struct ExactTail<'a> {
    bootstrap: &'a VerifiedFullStructural,
    wire: &'a [u8],
    query: u32,
    query_raw: Vec<u8>,
    tip_height: u32,
    tip: [u8; 32],
    total: [u8; 28],
}

impl ExactTail<'_> {
    pub(super) fn bootstrap(&self) -> &VerifiedFullStructural { self.bootstrap }
    pub(super) fn query_height(&self) -> u32 { self.query }
    pub(super) fn query_raw(&self) -> &[u8] { &self.query_raw }
    pub(super) fn terminal_height(&self) -> u32 { self.tip_height }
    pub(super) fn terminal_id(&self) -> [u8; 32] { self.tip }
    pub(super) fn total_work(&self) -> [u8; 28] { self.total }
    pub(super) fn canonical_extension(&self) -> &[u8] { self.wire }
}

fn take<'a>(buf: &mut &'a [u8], count: usize) -> Result<&'a [u8], String> {
    let (field, rest) = buf.split_at_checked(count).ok_or("truncated exact tail")?;
    *buf = rest;
    Ok(field)
}

fn word(buf: &mut &[u8]) -> Result<u32, String> {
    Ok(u32::from_be_bytes(take(buf, 4)?.try_into().unwrap()))
}

fn finite_work(bytes: &[u8]) -> Result<u128, String> {
    BigUint::from_bytes_be(bytes).to_u128().ok_or_else(|| "work outside r4 profile".into())
}

fn wire_work(value: u128) -> [u8; 28] {
    let mut bytes = [0; 28];
    bytes[12..].copy_from_slice(&value.to_be_bytes());
    bytes
}

fn difficulty(n_bits: u32) -> Result<u128, String> {
    work_tree_work::native_decode(n_bits)?.to_u128().filter(|d| *d <= MAX_CAP)
        .ok_or_else(|| "difficulty exceeds profile cap".into())
}

fn cap(d: u128) -> Result<u128, String> {
    if d == 0 || d > MAX_CAP { return Err("difficulty exceeds cap grid".into()); }
    let bound = d + d / 2;
    let result = bound.next_power_of_two();
    if result > MAX_CAP { return Err("modern cap exceeds grid".into()); }
    Ok(result)
}

fn modern_header(raw: &[u8]) -> Result<Header, String> {
    if raw.is_empty() || raw.len() > RAW_LIMIT { return Err("modern RAW length".into()); }
    let header = Header::decode(raw, None).map_err(|e| format!("modern header codec: {e:?}"))?;
    if !(2..=4).contains(&header.version) { return Err("unsupported modern header version".into()); }
    Ok(header)
}

fn expected_difficulty(parent_height: u32, rows: &[Row]) -> Result<u128, String> {
    let last = rows.last().ok_or("missing parent")?;
    if parent_height % EPOCH as u32 != 0 { return Ok(last.difficulty); }
    let window = rows.get(rows.len().checked_sub(8 * EPOCH + 1).ok_or("missing DAA endpoints")?..)
        .ok_or("DAA window")?;
    let mut values: [BigInt; 8] = std::array::from_fn(|_| BigInt::from(0));
    for (epoch, ratio) in values.iter_mut().enumerate() {
        let start = window[epoch * EPOCH];
        let end = window[(epoch + 1) * EPOCH];
        let elapsed = end.timestamp.checked_sub(start.timestamp)
            .filter(|s| *s > 0).ok_or("DAA endpoint times")?;
        *ratio = BigInt::from(end.difficulty) * (120_000 * EPOCH as u32) / elapsed;
    }
    let first_end = i64::from(parent_height) - 7 * EPOCH as i64;
    let prediction = daa_regression::native_prediction_oracle(first_end, Epoch::Eip, &values).2;
    daa_finish::native_finish_oracle(Epoch::Eip, &prediction, &values[7], &last.difficulty.into())?
        .to_u128().ok_or_else(|| "modern DAA result exceeds profile".into())
}

fn admissible_geometry(b: u32, query: u32, n: u32) -> Result<u32, String> {
    if b < LOCAL_START || query < b || n > i32::MAX as u32 {
        return Err("unsupported bootstrap, query or tail height".into());
    }
    let first_eligible = query.checked_add(K0).ok_or("query depth overflow")?;
    if n < first_eligible { return Err("exact query lacks temporal depth".into()); }
    Ok(first_eligible - 1)
}

fn validate_child(raw: &[u8], height: u32, parent_id: [u8; 32], rows: &[Row]) -> Result<Row, String> {
    let header = modern_header(raw)?;
    let prev = rows.last().ok_or("missing authenticated parent")?;
    if header.height != height || header.parent_id != parent_id || header.timestamp <= prev.timestamp {
        return Err("modern tail ancestry or time".into());
    }
    let d = difficulty(header.n_bits)?;
    if d != expected_difficulty(height - 1, rows)? { return Err("modern contextual difficulty".into()); }
    native_autolykos_pow::verify_header(&header).map_err(|e| e.to_string())?;
    Ok(Row { difficulty: d, timestamp: header.timestamp })
}

fn authenticated_rows(base: &VerifiedFullStructural, checkpoint: &Header) -> Result<Vec<Row>, String> {
    let context = base.context_nbits_times();
    if context.len() != CONTEXT || context.last() != Some(&(checkpoint.n_bits, checkpoint.timestamp)) {
        return Err("incomplete or inconsistent authenticated context".into());
    }
    let mut rows: Vec<Row> = Vec::with_capacity(CONTEXT);
    for &(bits, timestamp) in context {
        if rows.last().is_some_and(|r| r.timestamp >= timestamp) {
            return Err("authenticated context timestamp order".into());
        }
        rows.push(Row { difficulty: difficulty(bits)?, timestamp });
    }
    Ok(rows)
}

fn requirements(
    b: u32, f: u32, rows: &[Row], wb: u128, ab: u128, t1: u128, t2: u128, total: u128
) -> Result<u128, String> {
    if t1 > t2 || t2 > wb || rows.len() < CONTEXT { return Err("exact summary order".into()); }
    let tail = &rows[CONTEXT..];
    let q_tail = match tail.iter().map(|r| r.difficulty).max() {
        Some(d) => cap(d)?, None => 1,
    };
    let mut required = ab.max(t1 + 17_867 * q_tail)
        .max(t2 + 9_548 * q_tail).max(wb + 2_090 * q_tail);
    let mut work = total;
    let mut suffix_max = 0;
    let mut cursor = rows.len();
    for index in (0..tail.len()).rev() {
        if (b as usize) + index + 1 <= f as usize {
            // Row zero has height b-1087. The inclusive start for origin b+1+index
            // is therefore exactly row index. All difficulties through the tip enter.
            while cursor > index {
                cursor -= 1;
                suffix_max = suffix_max.max(rows[cursor].difficulty);
            }
            required = required.max(work + 2_090 * cap(suffix_max)?);
        }
        work = work.checked_sub(tail[index].difficulty).ok_or("tail work underflow")?;
    }
    if work != wb { return Err("tail work reconstruction".into()); }
    Ok(required)
}

pub(super) fn verify<'a>(
    bootstrap: &'a AuditedHistory<'_>, exact_query: u32, packet: &'a [u8],
) -> Result<ExactTail<'a>, String> {
    let base = bootstrap.history();
    let mut input = packet;
    if take(&mut input, 8)? != MAGIC { return Err("exact tail mode".into()); }
    let x_len = word(&mut input)? as usize;
    if take(&mut input, x_len)? != base.canonical_x() { return Err("foreign bootstrap or profile".into()); }
    if word(&mut input)? != exact_query { return Err("wrong exact query".into()); }
    let n = word(&mut input)?;
    let declared_tip = <[u8; 32]>::try_from(take(&mut input, 32)?).unwrap();
    let b = u32::try_from(base.checkpoint_height()).map_err(|_| "checkpoint height")?;
    let f = admissible_geometry(b, exact_query, n)?;
    let checkpoint = modern_header(base.checkpoint_raw())?;
    if checkpoint.height != b { return Err("checkpoint height mismatch".into()); }
    let mut rows = authenticated_rows(base, &checkpoint)?;
    let (wb, ab, t1, t2) = base.summary();
    let (wb, ab, t1, t2) = (finite_work(&wb)?, finite_work(&ab)?, finite_work(&t1)?, finite_work(&t2)?);
    // n < 2^31 and every admitted D <= 2^64 imply <= 95-bit cumulative work.
    if wb > u128::from(b - 1) * MAX_CAP || t1 > t2 || t2 > wb { return Err("bootstrap work domain".into()); }
    let mut total = wb;
    let mut tip = blake2b256(base.checkpoint_raw());
    let mut query_raw = if exact_query == b { base.checkpoint_raw().to_vec() } else { Vec::new() };
    for height in b + 1..=n {
        let len = u16::from_be_bytes(take(&mut input, 2)?.try_into().unwrap()) as usize;
        let raw = take(&mut input, len)?;
        let row = validate_child(raw, height, tip, &rows)?;
        rows.try_reserve(1).map_err(|_| WORKSPACE_EXHAUSTED)?;
        rows.push(row);
        total += row.difficulty;
        tip = blake2b256(raw);
        if height == exact_query { query_raw = raw.to_vec(); }
    }
    if !input.is_empty() || tip != declared_tip { return Err("terminal identifier or exact extent".into()); }
    if query_raw.is_empty() || total < requirements(b, f, &rows, wb, ab, t1, t2, total)? {
        return Err("exact origin maturity".into());
    }
    Ok(ExactTail { bootstrap: base, wire: packet, query: exact_query, query_raw, tip_height: n,
        tip, total: wire_work(total) })
}

/// An already authenticated bootstrap certificate is a common literal prefix of
/// all complete comparison objects. Equal-work comparisons therefore reduce to
/// comparing the complete canonical extensions supplied to this one invocation.
pub(super) fn select<'a>(
    bootstrap: &'a AuditedHistory<'_>, exact_query: u32, candidates: impl IntoIterator<Item = &'a [u8]>
) -> Result<Option<ExactTail<'a>>, String> {
    let mut winner: Option<ExactTail<'a>> = None;
    for wire in candidates {
        let candidate = match verify(bootstrap, exact_query, wire) {
            Ok(candidate) => candidate,
            Err(error) if error == WORKSPACE_EXHAUSTED => return Err(error),
            Err(_) => continue,
        };
        if winner.as_ref().is_none_or(|old| {
            candidate.total > old.total || (candidate.total == old.total && candidate.wire < old.wire)
        }) {
            winner = Some(candidate);
        }
    }
    Ok(winner)
}

/// Encodes an untrusted candidate for transmission. Admission always runs verify.
pub(super) fn encode<'a>(
    bootstrap: &AuditedHistory<'_>, exact_query: u32, raws: impl IntoIterator<Item = &'a [u8]>,
) -> Result<Vec<u8>, String> {
    let base = bootstrap.history();
    let b = u32::try_from(base.checkpoint_height()).map_err(|_| "checkpoint height")?;
    let x = base.canonical_x();
    let mut out = MAGIC.to_vec();
    let length = u32::try_from(x.len()).map_err(|_| "bootstrap statement too large")?;
    out.extend_from_slice(&length.to_be_bytes());
    out.extend_from_slice(x);
    out.extend_from_slice(&exact_query.to_be_bytes());
    let terminal_offset = out.len();
    out.extend_from_slice(&[0; 36]);
    let mut n = b;
    let mut tip = blake2b256(base.checkpoint_raw());
    for raw in raws {
        if raw.is_empty() || raw.len() > RAW_LIMIT { return Err("modern RAW length".into()); }
        n = n.checked_add(1).filter(|h| *h <= i32::MAX as u32).ok_or("native height range")?;
        out.try_reserve(2 + raw.len()).map_err(|_| "exact tail output capacity")?;
        out.extend_from_slice(&(raw.len() as u16).to_be_bytes());
        out.extend_from_slice(raw);
        tip = blake2b256(raw);
    }
    admissible_geometry(b, exact_query, n)?;
    out[terminal_offset..terminal_offset+4].copy_from_slice(&n.to_be_bytes());
    out[terminal_offset+4..terminal_offset+36].copy_from_slice(&tip);
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    #[test]
    fn actual_modern_retarget_and_native_pow_use_parent_context() {
        let fixture: serde_json::Value = serde_json::from_str(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"), "/fixtures/mainnet-daa-windows-v1.json"
        ))).unwrap();
        let headers: BTreeMap<u32, Vec<u8>> = fixture["headers"].as_array().unwrap().iter().map(|entry| {
            let hex = entry["raw_hex"].as_str().unwrap();
            let raw = hex.as_bytes().chunks_exact(2).map(|digits|
                u8::from_str_radix(std::str::from_utf8(digits).unwrap(), 16).unwrap()).collect();
            (entry["height"].as_u64().unwrap() as u32, raw)
        }).collect();
        for h in [844_673, 844_801] {
            // Only these nine positions feed a modern retarget, including interval endpoints.
            let mut window = vec![Row { timestamp: 0, difficulty: 0 }; 1025];
            for offset in (0..=1024).step_by(128) {
                let header = modern_header(&headers[&(h-1025+offset as u32)]).unwrap();
                window[offset] = Row { timestamp: header.timestamp, difficulty: difficulty(header.n_bits).unwrap() };
            }
            let parent = blake2b256(&headers[&(h-1)]);
            let child = &headers[&h];
            assert!(validate_child(child, h, parent, &window).is_ok());
            assert!(validate_child(child, h, [0; 32], &window).is_err());
            assert!(validate_child(child, h+1, parent, &window).is_err());
            assert!(validate_child(child, h, parent, &window[1..]).is_err());
            let mut fault = child.clone();
            *fault.last_mut().unwrap() ^= 1;
            let failed = validate_child(&fault, h, parent, &window);
            assert!(matches!(failed, Err(ref e) if e == "native PoW strict target rejected"));
            let timestamp = window[0].timestamp;
            window[128].timestamp = timestamp;
            assert!(validate_child(child, h, parent, &window).is_err());
        }
    }

    #[test]
    fn old_and_new_origin_reducer_matches_direct_inclusive_maxima() {
        let b = LOCAL_START + 1024;
        let row = |d| Row { difficulty: d, timestamp: 0 };
        for (prefix_peak, tail_peak) in [(0,0), (1,1), (1087,2), (0,64)] {
            let mut rows = vec![row(1); CONTEXT + 65];
            rows[prefix_peak].difficulty = 31;
            rows[CONTEXT+tail_peak].difficulty = 51;
            let wb = 8_000_000u128;
            let tail = &rows[CONTEXT..];
            let total = wb + tail.iter().map(|r| r.difficulty).sum::<u128>();
            for f in [b, b+1, b+5, b+64] {
                let mut direct = (wb + 2090 * 128).max(7_999_999 + 9548 * 128)
                    .max(7_000_000 + 17867 * 128).max(9_000_000);
                let mut work = wb;
                for (k, record) in tail.iter().enumerate().take((f-b) as usize) {
                    work += record.difficulty;
                    let m = rows[k..].iter().map(|r| r.difficulty).max().unwrap();
                    direct = direct.max(work + 2090 * cap(m).unwrap());
                }
                assert_eq!(requirements(b, f, &rows, wb, 9_000_000, 7_000_000, 7_999_999, total), Ok(direct));
                // With only a modern old-origin term, the inclusive new maximum must be enforced.
                let mut modern = wb + 2090 * 128;
                let mut w = wb;
                for k in 0..(f-b) as usize {
                    w += tail[k].difficulty;
                    modern = modern.max(w + 2090 * cap(rows[k..].iter().map(|r| r.difficulty).max().unwrap()).unwrap());
                }
                assert_eq!(requirements(b,f,&rows,wb,0,0,0,total), Ok(modern));
            }
        }
        assert_eq!(cap(1), Ok(1));
        assert!(cap(MAX_CAP).is_err());
        assert!(admissible_geometry(b,b-1,b+64).is_err());
        assert!(admissible_geometry(b,b,b+63).is_err());
        assert_eq!(admissible_geometry(b,b,b+64), Ok(b+63));
    }
}

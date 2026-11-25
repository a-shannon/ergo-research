//! Native audit adapter, to be mounted under the module owning the full structural verifier.
//! Only that verifier may construct VerifiedFullStructural after canonical full-profile admission.

use super::VerifiedFullStructural;
use crate::native_autolykos_pow;
use crate::native_work_opening::{NativeWorkMembershipContext, NativeWorkOpening, MAX_OPENING_BYTES};
use crate::packed_owner_assembly::NativePrefix;
use crate::work_tree_wiring::Descriptor;
use nipopow_r4_audit_coordinates::{coordinates, Work};

const MAGIC: &[u8; 8] = b"AUDOPEN1";

/// Keeps the exact verified structural object alive after every requested interval passed.
pub(super) struct AuditedHistory<'a> {
    history: &'a VerifiedFullStructural,
}

impl AuditedHistory<'_> {
    pub(super) fn history(&self) -> &VerifiedFullStructural { self.history }
}

fn draws(history: &VerifiedFullStructural) -> Result<Vec<Work>, String> {
    let mut samples = coordinates(
        history.canonical_x(), history.complete_proof(), history.work(), history.following_work()
    ).map_err(str::to_owned)?;
    samples.sort_unstable();
    Ok(samples)
}

fn context(history: &VerifiedFullStructural) -> Result<NativeWorkMembershipContext, String> {
    NativeWorkMembershipContext::new(history.header_count(), history.root(), history.work())
        .map_err(|e| e.to_string())
}

fn take<'a>(input: &mut &'a [u8], count: usize) -> Result<&'a [u8], String> {
    let (head, tail) = input.split_at_checked(count).ok_or("truncated audit openings")?;
    *input = tail;
    Ok(head)
}

pub(super) fn verify<'a>(history: &'a VerifiedFullStructural, input: &[u8])
    -> Result<AuditedHistory<'a>, String>
{
    let samples = draws(history)?;
    check_openings(&context(history)?, &samples, input)?;
    Ok(AuditedHistory { history })
}

fn check_openings(ctx: &NativeWorkMembershipContext, samples: &[Work], mut input: &[u8])
    -> Result<(), String>
{
    if take(&mut input, MAGIC.len())? != MAGIC { return Err("audit opening magic".into()); }
    let count = u32::from_be_bytes(take(&mut input, 4)?.try_into().unwrap()) as usize;
    if count == 0 || count > samples.len() { return Err("audit opening count".into()); }
    let mut cursor = 0usize;
    let mut previous: Option<(u32, Work)> = None;
    for _ in 0..count {
        let len = u16::from_be_bytes(take(&mut input, 2)?.try_into().unwrap()) as usize;
        if len > MAX_OPENING_BYTES { return Err("audit opening length".into()); }
        let opening = take(&mut input, len)?;
        let coord = *samples.get(cursor).ok_or("unused audit opening")?;
        let member = ctx.verify_encoded(coord, opening).map_err(|e| e.to_string())?;
        let pow = native_autolykos_pow::verify_membership(member).map_err(|e| e.to_string())?;
        let member = pow.membership();
        let (lower, upper) = member.interval_be28();
        let position = member.position();
        if let Some((last, end)) = previous {
            if position <= last || lower < end { return Err("unordered audit intervals".into()); }
        }
        // verify_encoded authenticated lower <= coord < upper for the first pending draw.
        // Sorted draws up to upper now share that exact opening and native PoW verdict.
        cursor += samples[cursor..].partition_point(|sample| *sample < upper);
        previous = Some((position, upper));
    }
    if cursor != samples.len() || !input.is_empty() {
        return Err("missing sampled work or trailing opening bytes".into());
    }
    Ok(())
}

fn covering_height(prefix: &NativePrefix, coord: Work) -> Result<usize, String> {
    let (mut lo, mut hi) = (2, prefix.header_count());
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if prefix.interval(mid)?.1 <= coord { lo = mid + 1; } else { hi = mid; }
    }
    let (start, end) = prefix.interval(lo)?;
    if !(start <= coord && coord < end) { return Err("producer missing sampled interval".into()); }
    Ok(lo)
}

pub(super) fn encode_member(
    prefix: &NativePrefix, tree: &Descriptor, ctx: &NativeWorkMembershipContext, height: usize
) -> Result<(Vec<u8>, Work), String> {
    let position = height - 2;
    let (lower, upper) = prefix.interval(height)?;
    let depth = tree.leaves.trailing_zeros() as usize;
    let mut siblings = Vec::with_capacity(depth);
    for level in 0..depth {
        let sibling = (position >> level) ^ 1;
        let digest = if level == 0 { prefix.leaf_digest(sibling)? } else {
            let (base, count) = tree.level(level)?;
            if sibling >= count { return Err("producer sibling outside tree".into()); }
            prefix.node_digest(base + sibling)?
        };
        siblings.push(digest);
    }
    let opening = NativeWorkOpening::new(
        u32::try_from(position).map_err(|_| "producer position outside U32")?,
        lower, upper, prefix.raw(height)?.to_vec(), siblings
    );
    Ok((opening.encode(ctx).map_err(|e| e.to_string())?, upper))
}

/// Export the canonical, minimal set of individually authenticated openings.
/// The retained tree is checked against the exact verified object first.
pub(super) fn produce(history: &VerifiedFullStructural, prefix: &NativePrefix) -> Result<Vec<u8>, String> {
    if prefix.header_count() != history.header_count() || prefix.root() != history.root()
        || prefix.total_be28() != history.work()
    {
        return Err("producer tree differs from verified history".into());
    }
    let samples = draws(history)?;
    let tree = Descriptor::new(history.header_count(), history.root())?;
    let ctx = context(history)?;
    let mut packet = MAGIC.to_vec();
    packet.extend_from_slice(&0u32.to_be_bytes());
    let mut count = 0u32;
    let mut cursor = 0usize;
    while cursor < samples.len() {
        let height = covering_height(prefix, samples[cursor])?;
        let (opening, upper) = encode_member(prefix, &tree, &ctx, height)?;
        let len = u16::try_from(opening.len()).map_err(|_| "producer opening length")?;
        packet.extend_from_slice(&len.to_be_bytes());
        packet.extend_from_slice(&opening);
        count = count.checked_add(1).ok_or("producer opening count")?;
        cursor += samples[cursor..].partition_point(|sample| *sample < upper);
    }
    packet[8..12].copy_from_slice(&count.to_be_bytes());
    Ok(packet)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn first_three() -> Vec<Vec<u8>> {
        let data: serde_json::Value = serde_json::from_str(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/vendor/header-core/fixtures/governance-contiguous-header-packs-v1.json"
        ))).unwrap();
        data["networks"]["mainnet"]["source_headers_hex"].as_array().unwrap()
            .iter().take(3).map(|raw| {
                raw.as_str().unwrap().as_bytes().chunks_exact(2)
                    .map(|digits| u8::from_str_radix(std::str::from_utf8(digits).unwrap(), 16).unwrap())
                    .collect()
            }).collect()
    }

    fn component(raw: Vec<Vec<u8>>) -> (NativePrefix, Descriptor, NativeWorkMembershipContext) {
        let prefix = NativePrefix::from_raw_iter(3, raw.into_iter().map(Ok)).unwrap();
        let tree = Descriptor::new(3, prefix.root()).unwrap();
        let context = NativeWorkMembershipContext::new(3, prefix.root(), prefix.total_be28()).unwrap();
        (prefix, tree, context)
    }

    fn packet(records: &[&[u8]]) -> Vec<u8> {
        let mut bytes = MAGIC.to_vec();
        bytes.extend_from_slice(&(records.len() as u32).to_be_bytes());
        for record in records {
            bytes.extend_from_slice(&(record.len() as u16).to_be_bytes());
            bytes.extend_from_slice(record);
        }
        bytes
    }

    #[test]
    fn real_members_cover_draws_once_and_reject_faults() {
        let (prefix, tree, ctx) = component(first_three());
        let p = prefix.interval(2).unwrap().0;
        let q = prefix.interval(3).unwrap().0;
        let mut before_q = q;
        let i = before_q.iter().rposition(|v| *v != 0).unwrap();
        before_q[i] -= 1;
        before_q[i+1..].fill(255);
        assert_eq!(covering_height(&prefix, before_q).unwrap(), 2);
        assert_eq!(covering_height(&prefix, q).unwrap(), 3);
        assert!(covering_height(&prefix, prefix.total_be28()).is_err());
        let draws = [p, p, before_q, q];
        let (a, _) = encode_member(&prefix, &tree, &ctx, 2).unwrap();
        let (b, _) = encode_member(&prefix, &tree, &ctx, 3).unwrap();
        let valid = packet(&[&a, &b]);
        assert_eq!(check_openings(&ctx, &draws, &valid), Ok(()));
        for bad in [packet(&[]), packet(&[&a]), packet(&[&b]), packet(&[&b, &a]),
                    packet(&[&a, &a]), packet(&[&a, &b, &b])] {
            assert!(check_openings(&ctx, &draws, &bad).is_err());
        }
        for index in [0, 11, 12, 13, valid.len()-1] {
            let mut bad = valid.clone();
            bad[index] ^= 1;
            assert!(check_openings(&ctx, &draws, &bad).is_err());
        }
        let mut extra = valid.clone();
        extra.push(0);
        assert!(check_openings(&ctx, &draws, &extra).is_err());
        assert!(check_openings(&ctx, &draws, &valid[..valid.len()-1]).is_err());
    }

    #[test]
    fn authenticated_terminal_with_bad_pow_is_refused() {
        let mut raws = first_three();
        // The final header's V1 distance can change without invalidating its parent link.
        *raws[2].last_mut().unwrap() ^= 1;
        let (prefix, tree, ctx) = component(raws);
        let coord = prefix.interval(3).unwrap().0;
        let (opening, _) = encode_member(&prefix, &tree, &ctx, 3).unwrap();
        assert!(ctx.verify_encoded(coord, &opening).is_ok());
        let err = check_openings(&ctx, &[coord], &packet(&[&opening])).unwrap_err();
        assert!(err.starts_with("native PoW"), "{err}");
    }
}

//! First modern Score/Cap source-only falsifier. No frame, values or admission.
use super::*;
use crate::{
    gkr::Gate,
    h21_row_support::{MapParameters, ParentMapSources},
    legacy_envelope_map::{LowerBranch, LowerSelector, LowerSource, Map},
    origin_score,
    score_prefix_r_anchor::{self, SourceIdentity},
};
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use std::collections::{BTreeMap, BTreeSet};

const PREVIOUS: usize = 845_758;
const MODERN: usize = 845_759;
const BASE: [usize; 2] = [677_501, 685_693];
const CAP: [usize; 2] = [1_000_770, 1_002_818];
const SCORE_ROW: [usize; 2] = [487_421, 502_652];
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ProposedX { Existing(XWriter), Summary(usize) }

fn decode_hex<const N: usize>(text: &str) -> [u8; N] {
    assert_eq!(text.len(), N * 2);
    let mut out = [0; N];
    for (i, byte) in out.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&text[i * 2..i * 2 + 2], 16).unwrap();
    }
    out
}
fn parent() -> WorkTreeHistoryPlan {
    let root = decode_hex::<32>(
        "93F74871644F3644E8CCA9579C353006CB12FF50064F82E7660AB5AC552A307B",
    );
    let total = decode_hex::<28>(
        "0000000000000000000000000000000000000094E7A1372670000000",
    );
    let p = WorkTreeHistoryPlan::compile(1_827_840, 21, root, total).unwrap();
    assert_eq!(p.descriptor().root, root);
    assert_eq!(p.work_profile().total_be28, total);
    p
}
fn map_parameters() -> [MapParameters; 2] {
    [1_827_840, 1_827_775].map(|cut| MapParameters {
        cut,
        exponent: 55,
        lower: LowerSelector {
            source: LowerSource::HeaderDifficulty { height: 841_729 },
            branch: LowerBranch::Pivot(54),
        },
    })
}
fn summary_source(parent_maps: &ParentMapSources) -> score_prefix_r_anchor::Plan {
    let parameters = map_parameters();
    let maps = parameters.map(|p| {
        Map::new_modern_global_u_selected_lower(
            p.cut, 21, p.exponent, p.lower,
        ).unwrap()
    });
    for context in 0..2 {
        assert_eq!(maps[context].binding(), parent_maps.binding().maps[context],
            "independent conditional Summary Map differs from parent-bound source");
    }
    let identities = [1_827_840, 1_827_775].map(|cut| SourceIdentity {
        // Source-only: this shared label does not authenticate a native frame.
        frame: [0; 32], cut, parent_root: None,
    });
    score_prefix_r_anchor::Plan::new(&maps, identities).unwrap()
}
fn active(gate: &Gate) -> Vec<usize> {
    let mut out = Vec::new();
    if !gate.c1.is_zero() || !gate.c3.is_zero() { out.push(gate.left); }
    if !gate.c2.is_zero() || !gate.c3.is_zero() { out.push(gate.right); }
    out
}
fn expected_summary_bits(context: usize) -> BTreeSet<usize> {
    let layout = origin_score::Layout::new();
    (layout.r.start..=layout.s)
        .map(|local| PREVIOUS * WIDTH + BASE[context] + local)
        .collect()
}
fn summary_bits(terms: &[(usize, Term)]) -> Result<BTreeMap<usize, usize>, String> {
    let mut bits = BTreeMap::new();
    for (context, term) in terms {
        if *context >= 2 || term.row / ROWS != PREVIOUS {
            return Err("c146 Summary context/ROW owner".into());
        }
        let g = &term.gate;
        if g.left == g.right && g.c0.is_zero() && g.c1 == -Fr::one()
            && g.c2.is_zero() && g.c3.is_one()
        {
            if bits.insert(g.left, *context).is_some() {
                return Err("c146 duplicate Summary bit constraint".into());
            }
        }
    }
    for context in 0..2 {
        let actual = bits.iter().filter_map(|(address, c)|
            (*c == context).then_some(*address)).collect::<BTreeSet<_>>();
        if actual != expected_summary_bits(context) {
            return Err(format!("c146 Summary live X shape context {context}"));
        }
    }
    if bits.len() != 902 { return Err("c146 Summary 902-bit census".into()); }
    Ok(bits)
}
fn check_transfer(ledger: &Ledger, bits: &[(usize, usize)]) -> Result<(), String> {
    if ledger.owner != PREVIOUS { return Err("c146 transfer owner".into()); }
    let base = PREVIOUS * WIDTH;
    if ledger.x.first().map(|d| d.start) != Some(base)
        || ledger.x.last().map(|d| d.end) != Some(base + WIDTH)
        || ledger.x.windows(2).any(|w| w[0].end != w[1].start)
    {
        return Err("c146 source X partition hole/overlap".into());
    }
    let mut source = vec![None; WIDTH];
    for domain in &ledger.x {
        if domain.start < base || domain.end > base + WIDTH
            || domain.start >= domain.end {
            return Err("c146 source X domain extent".into());
        }
        for local in domain.start-base..domain.end-base {
            if source[local].replace(ProposedX::Existing(domain.writer)).is_some() {
                return Err("c146 duplicate source X writer".into());
            }
        }
    }
    if source.iter().any(Option::is_none) {
        return Err("c146 source X lease hole".into());
    }
    let mut proposed = source.clone();
    let expected = [expected_summary_bits(0), expected_summary_bits(1)];
    let mut transferred = BTreeMap::new();
    for &(address, context) in bits {
        if context >= 2 || !expected[context].contains(&address) {
            return Err("c146 transferred Summary address/context".into());
        }
        if transferred.insert(address, context).is_some() {
            return Err("c146 duplicate X writer including equal".into());
        }
        let local = address - base;
        if proposed[local] != Some(ProposedX::Existing(XWriter::Header)) {
            return Err("c146 Summary transfer requires HEADER".into());
        }
        proposed[local] = Some(ProposedX::Summary(context));
    }
    if transferred.len() != 902
        || (0..2).any(|c| transferred.iter().filter(|(_, k)| **k == c).count() != 451)
    {
        return Err("c146 incomplete HEADER-to-Summary transfer".into());
    }
    let mut changed = 0;
    for local in 0..WIDTH {
        let address = base + local;
        if let Some(&context) = transferred.get(&address) {
            if proposed[local] != Some(ProposedX::Summary(context))
                || source[local] != Some(ProposedX::Existing(XWriter::Header)) {
                return Err("c146 Summary overlay writer mismatch".into());
            }
            changed += 1;
        } else if proposed[local] != source[local] {
            return Err("c146 unrelated source X domain changed".into());
        }
    }
    if changed != 902 { return Err("c146 Summary overlay change count".into()); }
    Ok(())
}
fn check_summary_rows(ledger: &Ledger, terms: &[(usize, Term)]) -> Result<(), String> {
    let mut rows = BTreeMap::new();
    for (&row, _) in &ledger.rows { rows.insert(row, None); }
    let mut distinct = [BTreeSet::new(), BTreeSet::new()];
    for (context, term) in terms {
        if *context >= 2 || term.row / ROWS != PREVIOUS {
            return Err("c146 Summary ROW owner/context".into());
        }
        let local = term.row - PREVIOUS * ROWS;
        if !(477_074..507_536).contains(&local) {
            return Err("c146 Summary ROW outside private reserved band".into());
        }
        if let Some(previous) = rows.insert(term.row, Some(*context)) {
            if previous != Some(*context) {
                return Err(format!("c146 Summary ROW collision at {local}"));
            }
        }
        distinct[*context].insert(local);
    }
    if distinct.iter().any(|set| set.len() != 453) {
        return Err("c146 Summary 451 unary plus 2 reduction ROWs".into());
    }
    Ok(())
}
fn check_summary_own_reads(
    terms: &[(usize, Term)], bits: &BTreeMap<usize, usize>,
) -> Result<[usize; 2], String> {
    let mut upper = [0; 2];
    for (context, term) in terms {
        for address in active(&term.gate) {
            if bits.get(&address) == Some(context) { continue; }
            if address / WIDTH == 417_789 || address / WIDTH == 845_757 {
                if !(987_450..987_674).contains(&(address % WIDTH)) {
                    return Err("c146 Summary typed Upper local".into());
                }
                upper[*context] += 1;
            } else {
                return Err(format!("c146 Summary own untyped read {address}"));
            }
        }
    }
    if upper.iter().any(|count| *count != 672) {
        return Err("c146 Summary Upper source multiplicity".into());
    }
    Ok(upper)
}
fn scan_existing_reads(
    previous: &Candidate, modern: &Candidate, bits: &BTreeMap<usize, usize>,
) -> Result<[usize; 2], String> {
    let mut seen = [BTreeSet::new(), BTreeSet::new()];
    let predecessor = origin_score::group("predecessor");
    for candidate in [previous, modern] {
        let row_terms = candidate.row_source.iter().map(|c| (c.writer, &c.term));
        let support_terms = candidate.support_source.iter()
            .map(|t| (support_row_writer(t.writer), &t.term));
        for (writer, term) in row_terms.chain(support_terms) {
            let active_reads = active(&term.gate);
            for address in active_reads {
                if let Some(&context) = bits.get(&address) {
                    let local_row = term.row - candidate.owner * ROWS;
                    let index = local_row.checked_sub(SCORE_ROW[context] + predecessor.start)
                        .filter(|i| *i < 225);
                    let expected = index.map(|i|
                        PREVIOUS * WIDTH + BASE[context] + origin_score::Layout::new().r.start + i);
                    if candidate.owner != MODERN
                        || writer != RowWriter::Relocated(Family::Score(context))
                        || expected != Some(address)
                        || term.gate.c1 != -Fr::one()
                        || !term.gate.c2.is_zero() || !term.gate.c3.is_zero()
                        || !seen[context].insert(index.unwrap())
                    {
                        return Err("c146 surviving non-Score.p read of Summary X".into());
                    }
                }
            }
            if candidate.owner == MODERN {
                if let RowWriter::Relocated(Family::Score(context)) = writer {
                    let local_row = term.row - MODERN * ROWS;
                    if let Some(index) = local_row.checked_sub(SCORE_ROW[context] + predecessor.start)
                        .filter(|i| *i < 225)
                    {
                        let left = term.gate.left;
                        if left / WIDTH != MODERN
                            && left != PREVIOUS * WIDTH + BASE[context]
                                + origin_score::Layout::new().r.start + index
                        {
                            return Err("c146 wrong predecessor owner/context/local".into());
                        }
                    }
                }
            }
        }
    }
    if seen.iter().any(|set| set.len() != 225) {
        return Err("c146 incomplete Score.p previous-R read census".into());
    }
    Ok([seen[0].len(), seen[1].len()])
}
fn check_modern_geometry(candidate: &Candidate, ledger: &Ledger) -> Result<(), String> {
    if candidate.owner != MODERN || candidate.class != OwnerClass::Carry
        || ledger.owner != MODERN { return Err("c146 first modern owner/class".into()); }
    let l = origin_score::Layout::new();
    for context in 0..2 {
        let count = |family| candidate.support_source.iter()
            .filter(|t| t.writer == SupportWriter::Relocated(family)).count();
        if count(Family::W(context)) != 448 || count(Family::V(context)) != 65
            || count(Family::Score(context)) == 0
        { return Err("c146 modern Score/W/V source census".into()); }
        let w = candidate.support_source.iter().filter(|t|
            t.writer == SupportWriter::Relocated(Family::W(context))).collect::<Vec<_>>();
        let v = candidate.support_source.iter().filter(|t|
            t.writer == SupportWriter::Relocated(Family::V(context))).collect::<Vec<_>>();
        for k in 0..224 {
            let row = MODERN * ROWS + [491_694, 506_925][context] + k;
            let terms = w.iter().filter(|t| t.term.row == row).collect::<Vec<_>>();
            let own = Gate {left: MODERN * WIDTH + BASE[context] + l.sw.start + k,
                right: 0, c0: Fr::zero(), c1: Fr::one(),
                c2: Fr::zero(), c3: Fr::zero()};
            let source = Gate {left: 0, right: PREVIOUS * WIDTH + 987_450 + k,
                c0: Fr::zero(), c1: Fr::zero(),
                c2: -Fr::one(), c3: Fr::zero()};
            if terms.len() != 2 || !terms.iter().any(|t| t.term.gate == own)
                || !terms.iter().any(|t| t.term.gate == source)
            { return Err("c146 W typed alias".into()); }
        }
        for k in 0..65 {
            let t = v[k];
            let expected = Gate {
                left: MODERN * WIDTH + BASE[context] + l.sv.start + k,
                right: MODERN * WIDTH + CAP[context] + 740 + k,
                c0: Fr::zero(), c1: Fr::one(),
                c2: -Fr::one(), c3: Fr::zero(),
            };
            if t.term.row != MODERN * ROWS + [491_629, 506_860][context] + k
                || t.term.gate != expected
            { return Err("c146 V typed Cap alias".into()); }
        }
        let padding = origin_score::group("padding");
        let terms = candidate.support_source.iter().filter(|t|
            t.writer == SupportWriter::Relocated(Family::Score(context))
                && (MODERN * ROWS + SCORE_ROW[context] + padding.start
                    ..MODERN * ROWS + SCORE_ROW[context] + padding.end).contains(&t.term.row))
            .collect::<Vec<_>>();
        if terms.len() != 54 { return Err("c146 Score 54 padding constraints".into()); }
        for (k, t) in terms.iter().enumerate() {
            let expected = Gate {
                left: MODERN * WIDTH + BASE[context] + 1994 + k,
                right: MODERN * WIDTH + BASE[context],
                c0: Fr::zero(), c1: Fr::one(),
                c2: Fr::zero(), c3: Fr::zero(),
            };
            if t.term.row != MODERN * ROWS + SCORE_ROW[context] + padding.start + k
                || t.term.gate != expected
            { return Err("c146 Score tail not owned-zero constraint".into()); }
        }
        let score = candidate.reservations.iter().filter(|(w, _)|
            *w == SupportWriter::Relocated(Family::Score(context)))
            .map(|(_, range)| range.clone()).collect::<Vec<_>>();
        if score != [BASE[context]..BASE[context]+2048] {
            return Err("c146 Score X lease".into());
        }
        let cap_writer = ScheduledWriter::Cap { context, origin: MODERN + 1 };
        let cap_terms = candidate.support_source.iter().filter(|t|
            t.writer == SupportWriter::Scheduled(cap_writer)).collect::<Vec<_>>();
        if cap_terms.is_empty() || !cap_terms.iter().any(|t|
            active(&t.term.gate).into_iter().any(|a|
                a / WIDTH == 844_670 && (999_424 + context * 673..999_648 + context * 673)
                    .contains(&(a % WIDTH))))
        { return Err("c146 first Cap singleton MAX source".into()); }
        if !ledger.x.iter().any(|d| d.writer == XWriter::Cap(context)
            && d.start == MODERN * WIDTH + CAP[context]
            && d.end == MODERN * WIDTH + CAP[context] + 2048)
        { return Err("c146 Cap X lease".into()); }
    }
    if candidate.reservations.iter().any(|(w, _)|
        matches!(w, SupportWriter::Relocated(Family::W(_) | Family::V(_))))
    { return Err("c146 W/V wrongly own X".into()); }
    Ok(())
}

#[test]
fn c146_first_modern_summary_lease_source_only() {
    let p = parent();
    let parameters = map_parameters();
    let map_sources = ParentMapSources::new(&p, parameters).unwrap();
    map_sources.validate(&p, map_sources.binding()).unwrap();
    let prior = Candidate::stage_from_sources(&p, PREVIOUS, map_sources.sources()).unwrap();
    let modern = Candidate::stage_from_sources(&p, MODERN, map_sources.sources()).unwrap();
    let prior_ledger = close_source_candidate(prior.clone(), PREVIOUS, prior.class).unwrap();
    let modern_ledger = close_source_candidate(modern.clone(), MODERN, modern.class).unwrap();
    assert!(!prior.reservations.iter().any(|(w,_)|
        matches!(w, SupportWriter::Relocated(Family::Score(_) | Family::W(_) | Family::V(_)))));
    let summary = score_prefix_r_anchor::summary_source_terms(&summary_source(&map_sources)).unwrap();
    let bits = summary_bits(&summary).unwrap();
    let original_prior_ledger = prior_ledger.clone();
    check_transfer(&prior_ledger, &bits.iter().map(|(a,c)|(*a,*c)).collect::<Vec<_>>()).unwrap();
    assert_eq!(prior_ledger, original_prior_ledger,
        "source-only overlay changed the original ROW/X ledger");
    check_summary_rows(&prior_ledger, &summary).unwrap();
    let upper_reads = check_summary_own_reads(&summary, &bits).unwrap();
    let previous_reads = scan_existing_reads(&prior, &modern, &bits).unwrap();
    check_modern_geometry(&modern, &modern_ledger).unwrap();
    let row_count = summary.iter().map(|(_,t)|t.row).collect::<BTreeSet<_>>().len();
    assert_eq!(row_count, 906);

    // Mutants are isolated in the source-only checker, before any publication.
    let before_destination = Destination::default();
    let pristine_prior = prior.row_source.clone();
    let pristine_modern = modern.support_source.clone();
    let mut missing = bits.iter().map(|(a,c)|(*a,*c)).collect::<Vec<_>>();
    missing.pop();
    assert_eq!(check_transfer(&prior_ledger, &missing).unwrap_err(),
        "c146 incomplete HEADER-to-Summary transfer");
    let mut duplicate = bits.iter().map(|(a,c)|(*a,*c)).collect::<Vec<_>>();
    duplicate.push(duplicate[0]);
    assert_eq!(check_transfer(&prior_ledger, &duplicate).unwrap_err(),
        "c146 duplicate X writer including equal");
    let mut wrong_row = summary.clone();
    wrong_row[0].1.row = *prior_ledger.rows
        .range(PREVIOUS * ROWS + 477_074..PREVIOUS * ROWS + 507_536)
        .next().expect("coactive reserved-band row").0;
    assert!(check_summary_rows(&prior_ledger, &wrong_row).unwrap_err()
        .starts_with("c146 Summary ROW collision"));
    let mut surviving = prior.clone();
    let header = surviving.row_source.iter_mut()
        .find(|t| t.writer == RowWriter::Header).unwrap();
    header.term.gate.left = *bits.keys().next().unwrap();
    header.term.gate.c1 = Fr::one();
    assert_eq!(scan_existing_reads(&surviving, &modern, &bits).unwrap_err(),
        "c146 surviving non-Score.p read of Summary X");
    let mut wrong_owner = modern.clone();
    let predecessor_row = MODERN * ROWS + SCORE_ROW[0]
        + origin_score::group("predecessor").start;
    let term = wrong_owner.support_source.iter_mut().find(|t|
        t.writer == SupportWriter::Relocated(Family::Score(0))
            && t.term.row == predecessor_row
            && t.term.gate.left / WIDTH == PREVIOUS).unwrap();
    term.term.gate.left -= WIDTH;
    assert_eq!(scan_existing_reads(&prior, &wrong_owner, &bits).unwrap_err(),
        "c146 wrong predecessor owner/context/local");
    for family in [Family::W(0), Family::V(0)] {
        let mut omitted = modern.clone();
        omitted.support_source.retain(|t| t.writer != SupportWriter::Relocated(family));
        assert_eq!(check_modern_geometry(&omitted, &modern_ledger).unwrap_err(),
            "c146 modern Score/W/V source census");
    }
    let mut bad_w = modern.clone();
    bad_w.support_source.iter_mut().find(|t|
        t.writer == SupportWriter::Relocated(Family::W(0))).unwrap()
        .term.gate.c3 = Fr::one();
    assert_eq!(check_modern_geometry(&bad_w, &modern_ledger).unwrap_err(),
        "c146 W typed alias");
    let mut bad_v = modern.clone();
    bad_v.support_source.iter_mut().find(|t|
        t.writer == SupportWriter::Relocated(Family::V(0))).unwrap()
        .term.gate.c0 = Fr::one();
    assert_eq!(check_modern_geometry(&bad_v, &modern_ledger).unwrap_err(),
        "c146 V typed Cap alias");
    let mut bad_padding = modern.clone();
    let padding_row = MODERN * ROWS + SCORE_ROW[0] + origin_score::group("padding").start;
    bad_padding.support_source.iter_mut().find(|t|
        t.writer == SupportWriter::Relocated(Family::Score(0))
            && t.term.row == padding_row).unwrap().term.gate.c2 = Fr::one();
    assert_eq!(check_modern_geometry(&bad_padding, &modern_ledger).unwrap_err(),
        "c146 Score tail not owned-zero constraint");
    assert_eq!(prior.row_source, pristine_prior);
    let tagged_tuples = |terms: &[Tagged]| terms.iter()
        .map(|t| (t.writer, t.term.clone())).collect::<Vec<_>>();
    assert_eq!(tagged_tuples(&modern.support_source), tagged_tuples(&pristine_modern));
    assert_eq!(Destination::default(), before_destination);
    // The native prefix profile pin remains an external frame-derived reference.
    println!("C146_PHASE0_SOURCE_PASS owner_previous={PREVIOUS} owner_modern={MODERN} class_previous={:?} class_modern={:?} summary_bits={} summary_rows={row_count} summary_upper_reads={upper_reads:?} score_previous_reads={previous_reads:?} w_terms=448x2 v_terms=65x2 score_padding=54x2 isolated_mutants=10 frame=false native_profile_checked=false values=false admission=false", prior.class, modern.class, bits.len());
}

// Phase 1 no-frame fixture identity. The digest is deliberately a synthetic
// label: this type cannot authenticate the native frame or grant value loans.
const FIXTURE_FRAME_DIGEST: [u8; 32] = [0x46; 32];
const FIXTURE_NATIVE_PROFILE: [u8; 32] = [
    0x43,0x61,0x55,0x07,0x0c,0x22,0xe5,0x88,0x66,0xc7,0xf4,0xa0,0x43,0xeb,0x1d,0x3e,
    0x71,0x4b,0xbb,0x24,0xe6,0x7e,0x82,0x19,0x56,0x63,0xbe,0x05,0xdb,0xc9,0xd9,0xf3,
];

#[derive(Clone, Debug, PartialEq, Eq)]
struct FixtureParentId {
    frame_digest: [u8; 32],
    root: [u8; 32],
    total: [u8; 28],
    native_profile: [u8; 32],
    maps: [crate::legacy_envelope_map::Binding; 2],
}

#[derive(Clone, Debug)]
struct FixtureCutLease {
    parent: FixtureParentId,
    context: usize,
    parameters: MapParameters,
    map: crate::legacy_envelope_map::Binding,
}

fn fixture_parent_id(parent_maps: &ParentMapSources) -> FixtureParentId {
    let binding = parent_maps.binding();
    FixtureParentId {
        frame_digest: FIXTURE_FRAME_DIGEST,
        root: binding.root,
        total: binding.total,
        native_profile: FIXTURE_NATIVE_PROFILE,
        maps: binding.maps.clone(),
    }
}

fn fixture_cut_lease(parent_maps: &ParentMapSources, context: usize) -> FixtureCutLease {
    assert!(context < 2);
    let parameters = map_parameters()[context];
    FixtureCutLease {
        parent: fixture_parent_id(parent_maps),
        context,
        parameters,
        map: parent_maps.binding().maps[context].clone(),
    }
}

fn validate_fixture_cut_lease(
    parent_maps: &ParentMapSources,
    expected: &FixtureParentId,
    expected_context: usize,
    lease: &FixtureCutLease,
) -> Result<(), String> {
    if lease.parent.frame_digest != expected.frame_digest {
        return Err("c146 fixture-only frame label".into());
    }
    if lease.parent.root != expected.root { return Err("c146 full-parent root".into()); }
    if lease.parent.total != expected.total { return Err("c146 full-parent total".into()); }
    if lease.parent.native_profile != expected.native_profile {
        return Err("c146 native profile".into());
    }
    if lease.parent.maps != expected.maps { return Err("c146 complete parent Map pair".into()); }
    if expected_context >= 2 || lease.context != expected_context {
        return Err("c146 cut Map context".into());
    }
    let context = expected_context;
    if lease.map.n != expected.maps[context].n {
        return Err("c146 cut Map context".into());
    }
    let parameters = map_parameters()[context];
    if lease.parameters.cut != parameters.cut { return Err("c146 exact cut".into()); }
    if lease.parameters.exponent != parameters.exponent { return Err("c146 Map exponent".into()); }
    if lease.parameters.lower.source != parameters.lower.source {
        return Err("c146 selected lower source".into());
    }
    if lease.parameters.lower.branch != parameters.lower.branch {
        return Err("c146 selected lower pivot".into());
    }
    if lease.map.parent_root.is_some() { return Err("c146 symbolic cut root invented".into()); }
    let expected_map = Map::new_modern_global_u_selected_lower(
        parameters.cut, 21, parameters.exponent, parameters.lower,
    )?.binding();
    if lease.map != expected_map {
        return Err("c146 Map mode or complete cut binding".into());
    }
    let binding = parent_maps.binding();
    if lease.parent.root != binding.root || lease.parent.total != binding.total
        || lease.parent.maps != binding.maps {
        return Err("c146 parent identity differs from source binding".into());
    }
    Ok(())
}

fn validate_before_snapshot_publish(
    parent_maps: &ParentMapSources,
    expected: &FixtureParentId,
    expected_context: usize,
    lease: &FixtureCutLease,
    source_snapshot: &[u8],
    destination: &mut Vec<u8>,
) -> Result<(), String> {
    validate_fixture_cut_lease(parent_maps, expected, expected_context, lease)?;
    let mut next = destination.clone();
    next.extend_from_slice(source_snapshot);
    *destination = next;
    Ok(())
}

#[test]
fn c146_phase1_no_frame_parent_cut_identity_and_lease_boundary() {
    let p = parent();
    let parameters = map_parameters();
    let parent_maps = ParentMapSources::new(&p, parameters).unwrap();
    let expected = fixture_parent_id(&parent_maps);
    assert_eq!(expected.frame_digest, FIXTURE_FRAME_DIGEST,
        "fixture digest is a label only; no native frame is opened");
    assert_eq!(expected.root, p.descriptor().root);
    assert_eq!(expected.total, p.work_profile().total_be28);
    assert_eq!(expected.maps[0].parent_root, None);
    assert_eq!(expected.maps[1].parent_root, None);
    assert_ne!(expected.maps[0].n, expected.maps[1].n,
        "the two symbolic cut Maps retain distinct cut lengths");
    parent_maps.validate(&p, parent_maps.binding()).unwrap();

    let source_snapshot = vec![0x91, 0x92, 0x93];
    let mut destination = vec![0xa1];
    let destination_before = destination.clone();
    for context in 0..2 {
        let lease = fixture_cut_lease(&parent_maps, context);
        validate_before_snapshot_publish(&parent_maps, &expected, context, &lease,
            &source_snapshot, &mut destination).unwrap();
    }
    assert_eq!(destination, [destination_before, source_snapshot.clone(), source_snapshot.clone()].concat());

    let mut mutants: Vec<(&str, FixtureCutLease, &str)> = Vec::new();
    let mut changed = fixture_cut_lease(&parent_maps, 0);
    changed.parent.frame_digest[0] ^= 1;
    mutants.push(("frame label", changed, "c146 fixture-only frame label"));
    let mut changed = fixture_cut_lease(&parent_maps, 0);
    changed.parent.root[0] ^= 1;
    mutants.push(("full-parent root", changed, "c146 full-parent root"));
    let mut changed = fixture_cut_lease(&parent_maps, 0);
    changed.parent.total[0] ^= 1;
    mutants.push(("full-parent total", changed, "c146 full-parent total"));
    let mut changed = fixture_cut_lease(&parent_maps, 0);
    changed.parent.native_profile[0] ^= 1;
    mutants.push(("native profile", changed, "c146 native profile"));
    let mut changed = fixture_cut_lease(&parent_maps, 0);
    changed.parent.maps[1].e += 1;
    mutants.push(("parent Map pair", changed, "c146 complete parent Map pair"));
    let mut changed = fixture_cut_lease(&parent_maps, 0);
    changed.context = 1;
    mutants.push(("context", changed, "c146 cut Map context"));
    let mut changed = fixture_cut_lease(&parent_maps, 0);
    changed.parameters.cut -= 1;
    mutants.push(("cut", changed, "c146 exact cut"));
    let mut changed = fixture_cut_lease(&parent_maps, 0);
    changed.parameters.exponent += 1;
    mutants.push(("exponent", changed, "c146 Map exponent"));
    let mut changed = fixture_cut_lease(&parent_maps, 0);
    changed.parameters.lower.source = LowerSource::HeaderDifficulty { height: 841_728 };
    mutants.push(("lower source", changed, "c146 selected lower source"));
    let mut changed = fixture_cut_lease(&parent_maps, 0);
    changed.parameters.lower.branch = LowerBranch::Pivot(53);
    mutants.push(("lower pivot", changed, "c146 selected lower pivot"));
    let mut changed = fixture_cut_lease(&parent_maps, 0);
    changed.map = Map::new_modern_global_u(1827840, 21, 55).unwrap().binding();
    mutants.push(("Map mode", changed, "c146 Map mode or complete cut binding"));
    let mut changed = fixture_cut_lease(&parent_maps, 0);
    changed.map.parent_root = Some(expected.root);
    mutants.push(("invented cut root", changed, "c146 symbolic cut root invented"));

    let mutant_count = mutants.len();
    for (name, mutant, error) in mutants {
        let source_before_failure = source_snapshot.clone();
        let destination_before_failure = destination.clone();
        assert_eq!(validate_before_snapshot_publish(&parent_maps, &expected, 0, &mutant,
            &source_snapshot, &mut destination).unwrap_err(), error, "isolated {name} mutant");
        assert_eq!(source_snapshot, source_before_failure, "source snapshot after {name}");
        assert_eq!(destination, destination_before_failure, "destination snapshot after {name}");
    }
    println!("C146_PHASE1_NO_FRAME_PASS cuts=[1827840,1827775] cut_roots=None fixture_identity=true isolated_identity_cut_map_mutants={mutant_count} snapshots_preserved=true frame=false native_loans=false admission=false");
}

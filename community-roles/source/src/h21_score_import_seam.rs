//! C488 Score import seam and C489 selected Score/Slack admission.
//! Neither selected owner path exports a complete X/ROW proof or client.

use super::*;
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use ark_serialize::CanonicalSerialize;
use std::collections::{BTreeMap, BTreeSet};

const OWNER: usize = 845_887;
const BLOCK: usize = 514;
const ORDERED: usize = 1_028;
const ACTIVE: usize = 804;
const STORED: usize = 805;
const OUTPUTS: usize = 4_096;
const TERMS: usize = 17_090;
const ROWS: usize = 6_742;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Occurrence {
    ordinal: usize,
    context: usize,
    address: usize,
    value: Fr,
    author: ScoreRelationReadAuthor,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PhysicalRead {
    address: usize,
    value: Fr,
    author: ScoreRelationReadAuthor,
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct SourceIdentity {
    owner: usize,
    root: [u8; 32],
    total: [u8; 28],
    profile: [u8; 32],
    cut: Vec<u8>,
    authors: [ScoreReplayAuthor; 2],
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum StoredAuthor {
    Zero,
    Source(ScoreRelationReadAuthor),
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct StoredRead {
    address: usize,
    value: Fr,
    author: StoredAuthor,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct RowLease {
    row: usize,
    context: usize,
    author: ScoreReplayAuthor,
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct Offer {
    identity: SourceIdentity,
    occurrences: Vec<Occurrence>,
    reads: Vec<StoredRead>,
    cells: Vec<(usize, ScoreReplayAuthor, Fr)>,
    terms: Vec<(usize, Term)>,
    rows: Vec<RowLease>,
    digest: [u8; 32],
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct Destination {
    sentinel: u64,
    published: Option<Offer>,
}
struct Closure<'a> {
    source: H21ClosedScoreOwnerRelation<'a>,
    expected: Offer,
}

fn seal(relation: &H21ClosedScoreOwnerRelation<'_>) -> Result<Vec<Occurrence>, String> {
    if relation.owner() != OWNER {
        return Err("c488 owner".into());
    }
    let reads = relation.reads();
    if reads.len() != ORDERED {
        return Err("c488 ordered read census".into());
    }
    let mut out = Vec::with_capacity(ORDERED);
    for (ordinal, &(address, author, value)) in reads.iter().enumerate() {
        if value != Fr::zero() && value != Fr::one() {
            return Err("c488 Boolean read".into());
        }
        let context = ordinal / BLOCK;
        let offset = ordinal % BLOCK;
        let ok = match (offset, author) {
            (0..=224, ScoreRelationReadAuthor::PreviousR { context: c, owner }) => {
                c == context && owner == 845_759
            }
            (
                225..=289,
                ScoreRelationReadAuthor::Cap {
                    context: c,
                    origin,
                    max_owner,
                    cap_owner,
                },
            ) => c == context && origin == 845_888 && max_owner == 844_798 && cap_owner == OWNER,
            (290..=513, ScoreRelationReadAuthor::WorkUpper { owner, height }) => {
                owner == 845_886 && height == 845_888
            }
            _ => false,
        };
        if context >= 2 || !ok {
            return Err("c488 ordered typed occurrence".into());
        }
        out.push(Occurrence {
            ordinal,
            context,
            address,
            value,
            author,
        });
    }
    Ok(out)
}

fn validate_occurrences(values: &[Occurrence]) -> Result<(), String> {
    if values.len() != ORDERED {
        return Err("c488 ordered read census".into());
    }
    for (index, o) in values.iter().enumerate() {
        let context = index / BLOCK;
        let offset = index % BLOCK;
        let expected_address = match offset {
            0..=224 => 845_759 * WIDTH + SCORE_X[context] + score::Layout::new().r.start + offset,
            225..=289 => OWNER * WIDTH + [1_000_770, 1_002_818][context] + 740 + offset - 225,
            _ => 845_886 * WIDTH + 987_450 + offset - 290,
        };
        let ok = o.ordinal == index
            && o.context == context
            && match (offset, o.author) {
                (0..=224, ScoreRelationReadAuthor::PreviousR { context: c, owner }) => {
                    c == context && owner == 845_759
                }
                (
                    225..=289,
                    ScoreRelationReadAuthor::Cap {
                        context: c,
                        origin,
                        max_owner,
                        cap_owner,
                    },
                ) => {
                    c == context && origin == 845_888 && max_owner == 844_798 && cap_owner == OWNER
                }
                (290..=513, ScoreRelationReadAuthor::WorkUpper { owner, height }) => {
                    owner == 845_886 && height == 845_888
                }
                _ => false,
            };
        if context >= 2
            || o.address != expected_address
            || !ok
            || (o.value != Fr::zero() && o.value != Fr::one())
        {
            return Err("c488 ordered typed occurrence".into());
        }
    }
    Ok(())
}

fn dedup(occurrences: &[Occurrence]) -> Result<Vec<PhysicalRead>, String> {
    validate_occurrences(occurrences)?;
    let mut groups: BTreeMap<usize, Vec<Occurrence>> = BTreeMap::new();
    for &o in occurrences {
        groups.entry(o.address).or_default().push(o);
    }
    let mut out = Vec::with_capacity(ACTIVE);
    for (address, group) in groups {
        match group[0].author {
            ScoreRelationReadAuthor::WorkUpper { owner, height } => {
                if group.len() != 2
                    || owner != 845_886
                    || height != 845_888
                    || group[0].context != 0
                    || group[1].context != 1
                    || group[0].value != group[1].value
                    || group[1].author != group[0].author
                {
                    return Err("c488 Work pair identity".into());
                }
            }
            _ => {
                if group.len() != 1 {
                    return Err("c488 non-Work duplicate address".into());
                }
            }
        }
        out.push(PhysicalRead {
            address,
            value: group[0].value,
            author: group[0].author,
        });
    }
    if out.len() != ACTIVE {
        return Err("c488 unique active address census".into());
    }
    Ok(out)
}

fn residuals(terms: &[Term], values: &BTreeMap<usize, Fr>) -> Result<(), String> {
    let mut rows = BTreeMap::new();
    for term in terms {
        let g = &term.gate;
        let l = *values.get(&g.left).ok_or("c488 left read")?;
        let r = *values.get(&g.right).ok_or("c488 right read")?;
        *rows.entry(term.row).or_insert_with(Fr::zero) += g.c0 + g.c1 * l + g.c2 * r + g.c3 * l * r;
    }
    if rows.len() != ROWS || rows.values().any(|v| !v.is_zero()) {
        return Err("c488 Score residual/ROW census".into());
    }
    Ok(())
}

fn offer(relation: &H21ClosedScoreOwnerRelation<'_>) -> Result<Offer, String> {
    let authors = [
        relation.authors()[0].ok_or("c488 Score author0")?,
        relation.authors()[1].ok_or("c488 Score author1")?,
    ];
    for context in 0..2 {
        let expected = ScoreReplayAuthor {
            context,
            origin: 845_888,
            previous_owner: 845_759,
            max_owner: 844_798,
            cap_owner: OWNER,
        };
        if authors[context] != expected {
            return Err("c488 exact ScoreReplayAuthor pair".into());
        }
    }
    let identity = SourceIdentity {
        owner: relation.owner(),
        root: relation.parent_root(),
        total: relation.parent_total(),
        profile: relation.parent_profile(),
        cut: relation.cut_identity().to_vec(),
        authors,
    };
    if identity.owner != OWNER
        || identity.cut != H21EligibleMapStage::descriptor().canonical_identity()
    {
        return Err("c488 source identity".into());
    }
    let cells = relation.cells().to_vec();
    if cells.len() != OUTPUTS {
        return Err("c488 Score output census".into());
    }
    for c in 0..2 {
        for (bit, (address, author, value)) in cells[c * 2048..(c + 1) * 2048].iter().enumerate() {
            if *address != OWNER * WIDTH + SCORE_X[c] + bit
                || *author != authors[c]
                || (*value != Fr::zero() && *value != Fr::one())
            {
                return Err("c488 exact ordered Score output".into());
            }
        }
    }
    let mut terms = Vec::with_capacity(TERMS);
    for c in 0..2 {
        let block = relation.terms(c)?;
        if block.len() != 8_545
            || block.iter().map(|t| t.row).collect::<BTreeSet<_>>().len() != 3_371
        {
            return Err("c488 context Score term/ROW census".into());
        }
        terms.extend(block.iter().cloned().map(|t| (c, t)));
    }
    if terms.len() != TERMS {
        return Err("c488 Score term census".into());
    }
    let occurrences = seal(relation)?;
    for context in 0..2 {
        let outputs = cells[context * 2048..(context + 1) * 2048]
            .iter()
            .map(|x| x.0)
            .collect::<BTreeSet<_>>();
        let imported = occurrences[context * BLOCK..(context + 1) * BLOCK]
            .iter()
            .map(|x| x.address)
            .collect::<BTreeSet<_>>();
        let mut active = BTreeSet::new();
        for (_, t) in terms.iter().filter(|(c, _)| *c == context) {
            let g = &t.gate;
            if !g.c1.is_zero() || !g.c3.is_zero() {
                if !outputs.contains(&g.left) {
                    active.insert(g.left);
                }
            }
            if !g.c2.is_zero() || !g.c3.is_zero() {
                if !outputs.contains(&g.right) {
                    active.insert(g.right);
                }
            }
        }
        if active.contains(&0) || active != imported {
            return Err("c488 context active import support".into());
        }
    }
    let physical = dedup(&occurrences)?;
    let mut reads = Vec::with_capacity(STORED);
    reads.push(StoredRead {
        address: 0,
        value: Fr::zero(),
        author: StoredAuthor::Zero,
    });
    reads.extend(physical.iter().map(|r| StoredRead {
        address: r.address,
        value: r.value,
        author: StoredAuthor::Source(r.author),
    }));
    if reads.len() != STORED {
        return Err("c488 stored read census".into());
    }
    let mut row_map = BTreeMap::new();
    for (c, t) in &terms {
        if let Some(old) = row_map.insert(t.row, (*c, authors[*c])) {
            if old != (*c, authors[*c]) {
                return Err("c488 cross-author ROW collision".into());
            }
        }
    }
    let rows = row_map
        .into_iter()
        .map(|(row, (context, author))| RowLease {
            row,
            context,
            author,
        })
        .collect::<Vec<_>>();
    if rows.len() != ROWS {
        return Err("c488 Score ROW census".into());
    }
    let outputs = cells.iter().map(|x| x.0).collect::<BTreeSet<_>>();
    if outputs.len() != OUTPUTS {
        return Err("c488 duplicate output".into());
    }
    let imported = physical.iter().map(|r| r.address).collect::<BTreeSet<_>>();
    let mut active = BTreeSet::new();
    for (_, t) in &terms {
        for (a, c) in [(t.gate.left, t.gate.c1), (t.gate.right, t.gate.c2)] {
            if !c.is_zero() && !outputs.contains(&a) {
                active.insert(a);
            }
        }
        if !t.gate.c3.is_zero() {
            for a in [t.gate.left, t.gate.right] {
                if !outputs.contains(&a) {
                    active.insert(a);
                }
            }
        }
    }
    if active != imported {
        return Err("c488 active import equality".into());
    }
    let mut values = BTreeMap::from([(0, Fr::zero())]);
    for &(a, _, v) in &cells {
        if values.insert(a, v).is_some() {
            return Err("c488 cell collision".into());
        }
    }
    for r in &physical {
        if values.insert(r.address, r.value).is_some() {
            return Err("c488 read/output collision".into());
        }
    }
    if values.len() != OUTPUTS + STORED {
        return Err("c488 stored read census".into());
    }
    residuals(
        &terms.iter().map(|x| x.1.clone()).collect::<Vec<_>>(),
        &values,
    )?;
    let mut out = Offer {
        identity,
        occurrences,
        reads,
        cells,
        terms,
        rows,
        digest: [0; 32],
    };
    out.digest = digest(&out)?;
    Ok(out)
}

fn pu(b: &mut Vec<u8>, v: usize) -> Result<(), String> {
    b.extend_from_slice(
        &u64::try_from(v)
            .map_err(|_| "c488 usize/u64")?
            .to_be_bytes(),
    );
    Ok(())
}
fn pf(b: &mut Vec<u8>, v: &Fr) -> Result<(), String> {
    let mut x = Vec::new();
    v.serialize_compressed(&mut x).map_err(|e| e.to_string())?;
    if x.len() != 32 {
        return Err("c488 Fr width".into());
    }
    b.extend_from_slice(&x);
    Ok(())
}
fn psa(b: &mut Vec<u8>, a: ScoreReplayAuthor) -> Result<(), String> {
    for v in [
        a.context,
        a.origin,
        a.previous_owner,
        a.max_owner,
        a.cap_owner,
    ] {
        pu(b, v)?;
    }
    Ok(())
}
fn pra(b: &mut Vec<u8>, a: ScoreRelationReadAuthor) -> Result<(), String> {
    match a {
        ScoreRelationReadAuthor::PreviousR { context, owner } => {
            b.push(1);
            pu(b, context)?;
            pu(b, owner)?
        }
        ScoreRelationReadAuthor::Cap {
            context,
            origin,
            max_owner,
            cap_owner,
        } => {
            b.push(2);
            for v in [context, origin, max_owner, cap_owner] {
                pu(b, v)?;
            }
        }
        ScoreRelationReadAuthor::WorkUpper { owner, height } => {
            b.push(3);
            pu(b, owner)?;
            pu(b, height)?
        }
    }
    Ok(())
}
fn digest(o: &Offer) -> Result<[u8; 32], String> {
    let mut b = b"c488-score-import-seam-v2\0".to_vec();
    pu(&mut b, o.identity.owner)?;
    b.extend_from_slice(&o.identity.root);
    b.extend_from_slice(&o.identity.total);
    b.extend_from_slice(&o.identity.profile);
    pu(&mut b, o.identity.cut.len())?;
    b.extend_from_slice(&o.identity.cut);
    for a in o.identity.authors {
        psa(&mut b, a)?;
    }
    pu(&mut b, o.occurrences.len())?;
    for x in &o.occurrences {
        for v in [x.ordinal, x.context, x.address] {
            pu(&mut b, v)?;
        }
        pra(&mut b, x.author)?;
        pf(&mut b, &x.value)?;
    }
    pu(&mut b, o.reads.len())?;
    for x in &o.reads {
        pu(&mut b, x.address)?;
        match x.author {
            StoredAuthor::Zero => b.push(0),
            StoredAuthor::Source(a) => {
                b.push(1);
                pra(&mut b, a)?;
            }
        }
        pf(&mut b, &x.value)?;
    }
    pu(&mut b, o.cells.len())?;
    for (a, author, v) in &o.cells {
        pu(&mut b, *a)?;
        psa(&mut b, *author)?;
        pf(&mut b, v)?;
    }
    pu(&mut b, o.terms.len())?;
    for (c, t) in &o.terms {
        for v in [*c, t.row, t.gate.left, t.gate.right] {
            pu(&mut b, v)?;
        }
        for x in [t.gate.c0, t.gate.c1, t.gate.c2, t.gate.c3] {
            pf(&mut b, &x)?;
        }
    }
    pu(&mut b, o.rows.len())?;
    for r in &o.rows {
        pu(&mut b, r.row)?;
        pu(&mut b, r.context)?;
        psa(&mut b, r.author)?;
    }
    Ok(ergo_header_core::blake2b256(&b))
}

fn source_digest(o: &Offer) -> Result<[u8; 32], String> {
    let mut b = b"c488-native-source-v1\0".to_vec();
    pu(&mut b, o.identity.owner)?;
    b.extend_from_slice(&o.identity.root);
    b.extend_from_slice(&o.identity.total);
    b.extend_from_slice(&o.identity.profile);
    pu(&mut b, o.identity.cut.len())?;
    b.extend_from_slice(&o.identity.cut);
    for a in o.identity.authors {
        psa(&mut b, a)?;
    }
    pu(&mut b, o.occurrences.len())?;
    for x in &o.occurrences {
        for v in [x.ordinal, x.context, x.address] {
            pu(&mut b, v)?;
        }
        pra(&mut b, x.author)?;
        pf(&mut b, &x.value)?;
    }
    Ok(ergo_header_core::blake2b256(&b))
}
fn hex(x: &[u8]) -> String {
    x.iter().map(|b| format!("{b:02X}")).collect()
}
fn check_residual_sensitivity(score: &Offer) -> Result<(), String> {
    if score.terms.len() != TERMS || score.rows.len() != ROWS {
        return Err("c488 sensitivity source census".into());
    }
    let mut values = BTreeMap::from([(0, Fr::zero())]);
    for &(a, _, v) in &score.cells {
        values.insert(a, v);
    }
    for r in &score.reads[1..] {
        values.insert(r.address, r.value);
    }
    let work = score
        .reads
        .iter()
        .find(|r| {
            matches!(
                r.author,
                StoredAuthor::Source(ScoreRelationReadAuthor::WorkUpper { .. })
            )
        })
        .ok_or("c488 Work sensitivity source")?;
    let address = work.address;
    let bit = address % WIDTH - 987_450;
    values.insert(address, Fr::one() - values[&address]);
    let mut residual = BTreeMap::new();
    for (_, t) in &score.terms {
        let g = &t.gate;
        let l = values[&g.left];
        let r = values[&g.right];
        *residual.entry(t.row).or_insert_with(Fr::zero) +=
            g.c0 + g.c1 * l + g.c2 * r + g.c3 * l * r;
    }
    if residual.len() != ROWS {
        return Err("c488 sensitivity ROW census".into());
    }
    for context in 0..2 {
        let row = OWNER * ROW_WIDTH + W_ALIAS_ROW[context] + bit;
        if residual.get(&row).is_none_or(Zero::is_zero) {
            return Err("c488 shared Work residual sensitivity".into());
        }
    }
    Ok(())
}
fn native_reject(closure: &Closure<'_>, offer: Offer, expected: &str) -> Result<(), String> {
    let mut d = Destination {
        sentinel: 7,
        published: None,
    };
    let before = d.clone();
    let error = closure.publish(&mut d, offer).err().unwrap_or_default();
    if error != expected || d != before {
        return Err("c488 native negative boundary/atomicity".into());
    }
    Ok(())
}
const NATIVE_NEGATIVES: usize = 6;

pub(super) fn run_native(
    relation: H21ClosedScoreOwnerRelation<'_>,
    frame_sha: &str,
    max_owners: usize,
    score_owners: usize,
    score_roles: usize,
) -> Result<String, String> {
    if frame_sha.len() != 64
        || !frame_sha.bytes().all(|b| b.is_ascii_hexdigit())
        || (max_owners, score_owners, score_roles) != (7_683, 7_543, 15_083)
    {
        return Err("c488 native evidence census".into());
    }
    let closure = Closure::new(relation)?;
    let source = source_digest(&closure.expected)?;
    let adapter = closure.expected.digest;
    let mut destination = Destination {
        sentinel: 7,
        published: None,
    };
    closure.publish(&mut destination, closure.expected.clone())?;
    check_residual_sensitivity(&closure.expected)?;
    let mut context = closure.expected.clone();
    context.occurrences[804].context = 0;
    native_reject(&closure, context, "c488 ordered typed occurrence")?;
    let mut old = closure.expected.clone();
    old.identity.authors[0].max_owner = 844_671;
    native_reject(&closure, old, "c488 source identity")?;
    for field in 0..4 {
        let mut bad = closure.expected.clone();
        match field {
            0 => bad.identity.root[0] ^= 1,
            1 => bad.identity.total[0] ^= 1,
            2 => bad.identity.profile[0] ^= 1,
            _ => bad.identity.cut[0] ^= 1,
        };
        native_reject(&closure, bad, "c488 source identity")?;
    }
    Ok(format!("C488_NATIVE_SCORE_IMPORT_SEAM_PASS frame_sha256={} max_owners={} score_owners={} score_roles={} owner=845887 contexts=2 ordered_reads=1028 active_addresses=804 stored_reads=805 outputs=4096 terms=17090 rows=6742 max_owner=844798 source_digest={} adapter_digest={} native_negatives={} residual_sensitivity=true score_only=true slack=false full_slice=false native=true full_history=false full_eq26=false header_zero=false all_owner=false common_x=false gkr=false pcs=false proof=false client=false",frame_sha,max_owners,score_owners,score_roles,hex(&source),hex(&adapter),NATIVE_NEGATIVES))
}

impl<'a> Closure<'a> {
    fn new(source: H21ClosedScoreOwnerRelation<'a>) -> Result<Self, String> {
        let expected = offer(&source)?;
        Ok(Self { source, expected })
    }
    fn publish(&self, d: &mut Destination, o: Offer) -> Result<(), String> {
        if d.published.is_some() {
            return Err("c488 replay".into());
        }
        let fresh = offer(&self.source)?;
        if fresh != self.expected {
            return Err("c488 source replay".into());
        }
        if o.identity != fresh.identity {
            return Err("c488 source identity".into());
        }
        if o.reads.len() != STORED
            || o.reads[0]
                != (StoredRead {
                    address: 0,
                    value: Fr::zero(),
                    author: StoredAuthor::Zero,
                })
        {
            return Err("c488 exact structural zero/read census".into());
        }
        validate_occurrences(&o.occurrences)?;
        let p = dedup(&o.occurrences)?;
        let mut derived = vec![StoredRead {
            address: 0,
            value: Fr::zero(),
            author: StoredAuthor::Zero,
        }];
        derived.extend(p.iter().map(|r| StoredRead {
            address: r.address,
            value: r.value,
            author: StoredAuthor::Source(r.author),
        }));
        if o.reads != derived {
            return Err("c488 derived physical reads".into());
        }
        if o.occurrences != fresh.occurrences {
            return Err("c488 exact ordered occurrences".into());
        }
        if o.reads != fresh.reads {
            return Err("c488 exact stored reads".into());
        }
        if o.cells != fresh.cells {
            return Err("c488 exact Score outputs".into());
        }
        if o.terms != fresh.terms {
            return Err("c488 exact Score terms".into());
        }
        if o.rows != fresh.rows {
            return Err("c488 exact typed ROWs".into());
        }
        if o.digest != fresh.digest {
            return Err("c488 exact digest".into());
        }
        validate_offer(&o)?;
        d.published = Some(o);
        Ok(())
    }
}

fn validate_offer(o: &Offer) -> Result<(), String> {
    if o.reads.len() != STORED
        || o.reads[0]
            != (StoredRead {
                address: 0,
                value: Fr::zero(),
                author: StoredAuthor::Zero,
            })
        || o.reads[1..]
            .iter()
            .any(|r| matches!(r.author, StoredAuthor::Zero))
    {
        return Err("c488 exact structural zero/read census".into());
    }
    let p = dedup(&o.occurrences)?;
    let mut reads = vec![StoredRead {
        address: 0,
        value: Fr::zero(),
        author: StoredAuthor::Zero,
    }];
    reads.extend(p.iter().map(|r| StoredRead {
        address: r.address,
        value: r.value,
        author: StoredAuthor::Source(r.author),
    }));
    if reads != o.reads {
        return Err("c488 derived physical reads".into());
    }
    if o.cells.len() != OUTPUTS || o.terms.len() != TERMS || o.rows.len() != ROWS {
        return Err("c488 offer census".into());
    }
    for c in 0..2 {
        if o.rows
            .iter()
            .filter(|r| r.context == c && r.author == o.identity.authors[c])
            .count()
            != 3_371
        {
            return Err("c488 typed ROW context census".into());
        }
    }
    if digest(o)? != o.digest {
        return Err("c488 digest".into());
    }
    Ok(())
}

#[cfg(test)]
fn reject(
    closure: &Closure<'_>,
    expected: &str,
    mutate: impl FnOnce(&mut Offer),
) -> Result<(), String> {
    let mut bad = closure.expected.clone();
    mutate(&mut bad);
    let mut d = Destination {
        sentinel: 7,
        published: None,
    };
    let before = d.clone();
    let err = closure.publish(&mut d, bad).err().unwrap_or_default();
    if err != format!("c488 {expected}") || d != before {
        return Err("c488 negative accepted".into());
    }
    Ok(())
}

#[cfg(test)]
pub(super) fn run_fixture(relation: H21ClosedScoreOwnerRelation<'_>) -> Result<(), String> {
    let closure = Closure::new(relation)?;
    let mut d = Destination {
        sentinel: 7,
        published: None,
    };
    closure.publish(&mut d, closure.expected.clone())?;
    let mut n = 0usize;
    reject(&closure, "ordered typed occurrence", |o| {
        o.occurrences[804].context = 0
    })?;
    n += 1;
    reject(&closure, "ordered typed occurrence", |o| {
        o.occurrences[804].author = ScoreRelationReadAuthor::WorkUpper {
            owner: 845_885,
            height: 845_888,
        }
    })?;
    n += 1;
    reject(&closure, "ordered typed occurrence", |o| {
        o.occurrences[804].author = ScoreRelationReadAuthor::WorkUpper {
            owner: 845_886,
            height: 845_887,
        }
    })?;
    n += 1;
    reject(&closure, "Work pair identity", |o| {
        o.occurrences[804].value = Fr::one() - o.occurrences[804].value
    })?;
    n += 1;
    reject(&closure, "ordered read census", |o| {
        o.occurrences.remove(804);
    })?;
    n += 1;
    reject(&closure, "ordered read census", |o| {
        let x = o.occurrences[804];
        o.occurrences.insert(805, x);
    })?;
    n += 1;
    reject(&closure, "ordered typed occurrence", |o| {
        o.occurrences.swap(289, 290)
    })?;
    n += 1;
    reject(&closure, "exact structural zero/read census", |o| {
        o.reads.pop();
    })?;
    n += 1;
    reject(&closure, "exact Score outputs", |o| {
        o.cells.pop();
    })?;
    n += 1;
    reject(&closure, "exact typed ROWs", |o| {
        o.rows.pop();
    })?;
    n += 1;
    reject(&closure, "exact Score terms", |o| {
        o.terms.pop();
    })?;
    n += 1;
    reject(&closure, "ordered typed occurrence", |o| {
        o.occurrences[0].address += 1
    })?;
    n += 1;
    reject(&closure, "ordered typed occurrence", |o| {
        o.occurrences[0].author = ScoreRelationReadAuthor::PreviousR {
            context: 1,
            owner: 845_759,
        }
    })?;
    n += 1;
    reject(&closure, "ordered typed occurrence", |o| {
        o.occurrences[225].author = ScoreRelationReadAuthor::Cap {
            context: 1,
            origin: 845_888,
            max_owner: 844_798,
            cap_owner: OWNER,
        }
    })?;
    n += 1;
    for field in 0..3 {
        reject(&closure, "ordered typed occurrence", |o| {
            o.occurrences[225].author = match field {
                0 => ScoreRelationReadAuthor::Cap {
                    context: 0,
                    origin: 845_887,
                    max_owner: 844_798,
                    cap_owner: OWNER,
                },
                1 => ScoreRelationReadAuthor::Cap {
                    context: 0,
                    origin: 845_888,
                    max_owner: 844_797,
                    cap_owner: OWNER,
                },
                _ => ScoreRelationReadAuthor::Cap {
                    context: 0,
                    origin: 845_888,
                    max_owner: 844_798,
                    cap_owner: OWNER - 1,
                },
            }
        })?;
        n += 1;
    }
    reject(&closure, "ordered typed occurrence", |o| {
        o.occurrences[0].value = Fr::from(2u64)
    })?;
    n += 1;
    reject(&closure, "derived physical reads", |o| {
        o.reads[1].value = Fr::one() - o.reads[1].value
    })?;
    n += 1;
    reject(&closure, "exact structural zero/read census", |o| {
        o.reads.push(o.reads[1])
    })?;
    n += 1;
    reject(&closure, "exact structural zero/read census", |o| {
        o.reads[0].address = 1
    })?;
    n += 1;
    reject(&closure, "exact structural zero/read census", |o| {
        o.reads[0].value = Fr::one()
    })?;
    n += 1;
    reject(&closure, "exact structural zero/read census", |o| {
        o.reads[0].author = StoredAuthor::Source(ScoreRelationReadAuthor::WorkUpper {
            owner: 845_886,
            height: 845_888,
        })
    })?;
    n += 1;
    reject(&closure, "source identity", |o| {
        o.identity.authors[0] = o.identity.authors[1]
    })?;
    n += 1;
    reject(&closure, "exact digest", |o| o.digest[0] ^= 1)?;
    n += 1;
    reject(&closure, "exact Score outputs", |o| {
        o.cells[0].1 = o.identity.authors[1]
    })?;
    n += 1;
    reject(&closure, "exact typed ROWs", |o| o.rows.push(o.rows[0]))?;
    n += 1;
    reject(&closure, "exact typed ROWs", |o| {
        o.rows[0].author = o.identity.authors[1]
    })?;
    n += 1;
    reject(&closure, "exact Score terms", |o| {
        o.terms[0].1.gate.left += 1
    })?;
    n += 1;
    reject(&closure, "exact Score terms", |o| {
        o.terms[0].1.gate.c1 += Fr::one()
    })?;
    n += 1;
    for field in 0..5 {
        reject(&closure, "source identity", |o| match field {
            0 => o.identity.root[0] ^= 1,
            1 => o.identity.total[0] ^= 1,
            2 => o.identity.profile[0] ^= 1,
            3 => o.identity.cut[0] ^= 1,
            _ => o.identity.owner -= 1,
        })?;
        n += 1;
    }
    check_residual_sensitivity(&closure.expected)?;
    let mut values = BTreeMap::from([(0, Fr::zero())]);
    for &(a, _, v) in &closure.expected.cells {
        values.insert(a, v);
    }
    for r in &closure.expected.reads[1..] {
        values.insert(r.address, r.value);
    }
    let work = closure
        .expected
        .reads
        .iter()
        .find(|r| {
            matches!(
                r.author,
                StoredAuthor::Source(ScoreRelationReadAuthor::WorkUpper { .. })
            )
        })
        .ok_or("c488 Work sensitivity source")?;
    let address = work.address;
    let bit = address % WIDTH - 987_450;
    values.insert(address, Fr::one() - values[&address]);
    let mut sensitivity = BTreeMap::new();
    for (_, t) in &closure.expected.terms {
        let g = &t.gate;
        let l = values[&g.left];
        let r = values[&g.right];
        *sensitivity.entry(t.row).or_insert_with(Fr::zero) +=
            g.c0 + g.c1 * l + g.c2 * r + g.c3 * l * r;
    }
    if sensitivity.len() != ROWS {
        return Err("c488 sensitivity ROW census".into());
    }
    for context in 0..2 {
        let row = OWNER * ROW_WIDTH + W_ALIAS_ROW[context] + bit;
        if sensitivity.get(&row).is_none_or(Zero::is_zero) {
            return Err("c488 shared Work residual sensitivity".into());
        }
    }
    let before = d.clone();
    if closure
        .publish(&mut d, closure.expected.clone())
        .err()
        .as_deref()
        != Some("c488 replay")
        || d != before
    {
        return Err("c488 replay gate".into());
    }
    n += 1;
    if n != 36 {
        return Err("c488 admission negative census".into());
    }
    println!("C488_SYNTHETIC_SCORE_IMPORT_SEAM_PASS owner=845887 contexts=2 ordered_reads=1028 active_addresses=804 stored_reads=805 outputs=4096 terms=17090 rows=6742 negatives={n} residual_sensitivity=true score_only=true slack=false full_slice=false native=false full_history=false full_eq26=false header_zero=false all_owner=false common_x=false gkr=false pcs=false proof=false client=false");
    Ok(())
}

// C489 keeps the C488 Score offer intact. Slack has its own X and ROW authors;
// the generated Map stage is source and collision context, not a selected output.
type C489Stage = super::super::super::h21_eligible_slack::H21EligibleSlackStage;
const C489_OUTPUTS: usize = 4_870;
const C489_TERMS: usize = 17_864;
const C489_ROWS: usize = 7_516;
const C489_SLACK: usize = 774;
const C489_NATIVE_NEGATIVES: usize = 10;

#[derive(Clone, Debug, PartialEq, Eq)]
struct C489SlackCell {
    address: usize,
    context: usize,
    value: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct C489SlackTerm {
    context: usize,
    term: Term,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct C489SlackRow {
    row: usize,
    context: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct C489Offer {
    score: Offer,
    slack_cells: Vec<C489SlackCell>,
    slack_terms: Vec<C489SlackTerm>,
    slack_rows: Vec<C489SlackRow>,
    digest: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct C489Destination {
    sentinel: u64,
    published: Option<C489Offer>,
}

struct C489Closure<F: Fn() -> Result<C489Offer, String>> {
    source: F,
    expected: C489Offer,
}

fn c489_digest(o: &C489Offer) -> Result<[u8; 32], String> {
    let mut bytes = b"c489-native-score-slack-selected-v1\0".to_vec();
    bytes.extend_from_slice(&o.score.digest);
    pu(&mut bytes, o.slack_cells.len())?;
    for cell in &o.slack_cells {
        pu(&mut bytes, cell.address)?;
        pu(&mut bytes, cell.context)?;
        bytes.push(u8::from(cell.value));
    }
    pu(&mut bytes, o.slack_terms.len())?;
    for item in &o.slack_terms {
        pu(&mut bytes, item.context)?;
        let term = &item.term;
        for value in [term.row, term.gate.left, term.gate.right] {
            pu(&mut bytes, value)?;
        }
        for value in [term.gate.c0, term.gate.c1, term.gate.c2, term.gate.c3] {
            pf(&mut bytes, &value)?;
        }
    }
    pu(&mut bytes, o.slack_rows.len())?;
    for row in &o.slack_rows {
        pu(&mut bytes, row.row)?;
        pu(&mut bytes, row.context)?;
    }
    Ok(ergo_header_core::blake2b256(&bytes))
}

fn c489_checked_source(score: Offer, stage: &C489Stage,
    expected_maps: &[crate::legacy_envelope_map::Binding; 2]) -> Result<C489Offer, String> {
    validate_offer(&score)?;
    let map = &stage.map_stage;
    if map.owner != OWNER
        || map.parent_root != score.identity.root
        || map.parent_total != score.identity.total
        || map.parent_profile != score.identity.profile
        || map.cut_identity != score.identity.cut
        || map.cut_identity != H21EligibleMapStage::descriptor().canonical_identity()
        || &map.map_bindings != expected_maps
        || map.map_bindings.iter().any(|binding| binding.parent_root.is_some())
    {
        return Err("c489 Score/Map/Slack parent/cut/owner".into());
    }
    for context in 0..2 {
        for local in H21EligibleMapStage::map_live(context)? {
            if !matches!(map.claims.get(&local),
                Some((H21StageAuthor::Map(found), _)) if *found == context)
            {
                return Err("c489 exact generated Map source".into());
            }
        }
        if map.map_terms[context].is_empty() {
            return Err("c489 missing generated Map ROW source".into());
        }
    }
    if map.claims.len() != 2 * crate::bank53_map::MAP_LIVE {
        return Err("c489 generated Map source census".into());
    }
    let mut expected_score_cells = BTreeMap::new();
    for &(address, author, value) in &score.cells {
        let local = address.checked_sub(OWNER * WIDTH)
            .ok_or("c489 Score output owner")?;
        if expected_score_cells.insert(local, (author, value)).is_some() {
            return Err("c489 duplicate Score source cell".into());
        }
        let offset = local.checked_sub(crate::bank53_map::CONTEXT_INPUT_BASE
            + author.context * 8_192).ok_or("c489 Score context offset")?;
        if crate::bank53_required_writer::required_bank53_writer(OWNER, author.context, offset)
            != Ok(crate::bank53_required_writer::RequiredWriter::ScoreReplay {
                context: author.context,
                endpoint: crate::bank53_required_writer::ScoreEndpointKind::Regular,
            })
        {
            return Err("c489 required Score writer".into());
        }
    }
    if stage.score_cells() != &expected_score_cells {
        return Err("c489 exact joined Score cells".into());
    }
    for context in 0..2 {
        let terms = score.terms.iter().filter(|(c, _)| *c == context)
            .map(|(_, term)| term.clone()).collect::<Vec<_>>();
        if stage.score_rows()[context] != terms {
            return Err("c489 exact joined Score terms".into());
        }
    }
    let ordered_reads = score.occurrences.iter().map(|item|
        (item.address, item.author, item.value)).collect::<Vec<_>>();
    if stage.score_imports() != ordered_reads.as_slice() {
        return Err("c489 exact joined ordered Score reads".into());
    }

    let mut slack_cells = Vec::new();
    let mut slack_terms = Vec::new();
    for context in 0..2 {
        let domain = H21EligibleMapStage::slack_live(context)?;
        if domain.len() != crate::bank53_slack::SLACK_ZERO_COUNT {
            return Err("c489 Slack source width".into());
        }
        for local in domain {
            if !matches!(stage.slack_cells().get(&local),
                Some((H21StageAuthor::Slack(found), false)) if *found == context)
                || map.claims.contains_key(&local)
                || stage.score_cells().contains_key(&local)
            {
                return Err("c489 exact authored-zero Slack X".into());
            }
            let offset = local.checked_sub(crate::bank53_map::CONTEXT_INPUT_BASE
                + context * 8_192).ok_or("c489 Slack context offset")?;
            if crate::bank53_required_writer::required_bank53_writer(OWNER, context, offset)
                != Ok(crate::bank53_required_writer::RequiredWriter::Slack { context })
            {
                return Err("c489 required Slack writer".into());
            }
            slack_cells.push(C489SlackCell {
                address: OWNER * WIDTH + local, context, value: false,
            });
        }
        let canonical = crate::bank53_slack::slack_zero_terms(OWNER, context)?;
        if stage.slack_rows()[context] != canonical {
            return Err("c489 exact authored-zero Slack ROW".into());
        }
        slack_terms.extend(canonical.into_iter().map(|term| C489SlackTerm { context, term }));
    }
    if stage.slack_cells().len() != slack_cells.len() {
        return Err("c489 Slack X extra author".into());
    }
    let mut row_authors = BTreeMap::new();
    for (context, terms) in map.map_terms.iter().enumerate() {
        for term in terms {
            if row_authors.insert(term.row, context).is_some_and(|old| old != context) {
                return Err("c489 Map ROW writer collision".into());
            }
        }
    }
    for row in &score.rows {
        if row_authors.insert(row.row, 2 + row.context).is_some() {
            return Err("c489 Score/Map ROW writer collision".into());
        }
    }
    let mut slack_rows = Vec::new();
    for item in &slack_terms {
        let row = C489SlackRow { row: item.term.row, context: item.context };
        if row_authors.insert(row.row, 4 + row.context).is_some() {
            return Err("c489 Slack ROW writer collision".into());
        }
        slack_rows.push(row);
    }
    let mut result = C489Offer {
        score, slack_cells, slack_terms, slack_rows, digest: [0; 32],
    };
    c489_validate(&result)?;
    result.digest = c489_digest(&result)?;
    Ok(result)
}

fn c489_validate(o: &C489Offer) -> Result<(), String> {
    validate_offer(&o.score)?;
    if o.score.identity.owner != OWNER
        || o.score.identity.cut != H21EligibleMapStage::descriptor().canonical_identity()
    {
        return Err("c489 source identity".into());
    }
    let mut values = BTreeMap::new();
    for read in &o.score.reads {
        if values.insert(read.address, read.value).is_some() {
            return Err("c489 duplicate read address".into());
        }
    }
    let mut outputs = BTreeSet::new();
    for &(address, _, value) in &o.score.cells {
        if !outputs.insert(address) || values.insert(address, value).is_some() {
            return Err("c489 Score X collision".into());
        }
    }
    let mut slack_seen = BTreeSet::new();
    for context in 0..2 {
        for local in H21EligibleMapStage::slack_live(context)? {
            let address = OWNER * WIDTH + local;
            let item = o.slack_cells.iter().find(|item| item.address == address)
                .ok_or("c489 exact authored-zero Slack X")?;
            if item.context != context || item.value
                || !slack_seen.insert(item.address)
                || !outputs.insert(item.address)
                || values.insert(item.address, Fr::zero()).is_some()
            {
                return Err("c489 exact authored-zero Slack X".into());
            }
        }
    }
    if o.slack_cells.len() != slack_seen.len() || slack_seen.len() != C489_SLACK {
        return Err("c489 exact authored-zero Slack X".into());
    }
    if outputs.len() != C489_OUTPUTS || values.len() != C489_OUTPUTS + STORED
        || o.score.occurrences.len() != ORDERED || o.score.reads.len() != STORED
        || o.score.reads[1..].len() != ACTIVE
    {
        return Err("c489 output/read census".into());
    }
    let mut selected_rows = BTreeSet::new();
    for row in &o.score.rows {
        if !selected_rows.insert(row.row) {
            return Err("c489 Score ROW duplicate".into());
        }
    }
    let mut slack_rows = Vec::new();
    let mut slack_terms = 0usize;
    for context in 0..2 {
        let canonical = crate::bank53_slack::slack_zero_terms(OWNER, context)?;
        let offered = o.slack_terms.iter().filter(|item| item.context == context)
            .map(|item| item.term.clone()).collect::<Vec<_>>();
        if offered != canonical {
            return Err("c489 exact authored-zero Slack ROW".into());
        }
        for term in offered {
            if !selected_rows.insert(term.row) {
                return Err("c489 Slack ROW writer collision".into());
            }
            slack_rows.push(C489SlackRow { row: term.row, context });
            slack_terms += 1;
        }
    }
    if o.slack_terms.len() != slack_terms || o.slack_rows != slack_rows
        || slack_rows.len() != C489_SLACK || selected_rows.len() != C489_ROWS
        || o.score.terms.len() + o.slack_terms.len() != C489_TERMS
    {
        return Err("c489 exact typed ROW/term census".into());
    }
    let mut residuals = BTreeMap::new();
    for term in o.score.terms.iter().map(|(_, term)| term)
        .chain(o.slack_terms.iter().map(|item| &item.term))
    {
        let gate = &term.gate;
        let left = *values.get(&gate.left).ok_or("c489 unresolved left read")?;
        let right = *values.get(&gate.right).ok_or("c489 unresolved right read")?;
        *residuals.entry(term.row).or_insert_with(Fr::zero) +=
            gate.c0 + gate.c1 * left + gate.c2 * right + gate.c3 * left * right;
    }
    if residuals.len() != C489_ROWS || residuals.values().any(|value| !value.is_zero()) {
        return Err("c489 nonzero residual/ROW census".into());
    }
    Ok(())
}

impl<F: Fn() -> Result<C489Offer, String>> C489Closure<F> {
    fn new(source: F) -> Result<Self, String> {
        let expected = source()?;
        Ok(Self { source, expected })
    }

    fn publish(&self, destination: &mut C489Destination, offered: C489Offer)
        -> Result<(), String> {
        if destination.published.is_some() {
            return Err("c489 replay".into());
        }
        c489_validate(&offered)?;
        if c489_digest(&offered)? != offered.digest {
            return Err("c489 digest".into());
        }
        let fresh = (self.source)()?;
        if offered.score.identity != fresh.score.identity {
            return Err("c489 source identity".into());
        }
        if fresh != self.expected || offered != fresh {
            return Err("c489 exact source replay".into());
        }
        destination.published = Some(offered);
        Ok(())
    }
}

#[allow(dead_code)]
pub(super) fn run_c489_native<'ctx, 'src, 'max, 'snapshot>(
    stream: &H21ScoreEndpointStream<'ctx, 'src, 'max, 'snapshot>,
    frame_sha: &str,
    max_owners: usize,
    score_owners: usize,
    score_roles: usize,
) -> Result<String, String> {
    if frame_sha.len() != 64 || !frame_sha.bytes().all(|byte| byte.is_ascii_hexdigit())
        || (max_owners, score_owners, score_roles) != (7_683, 7_543, 15_083)
    {
        return Err("c489 native evidence census".into());
    }
    let source = || {
        let relation = stream.closed_owner_relation(OWNER)?;
        let expected_maps = relation.identity.map_bindings.clone();
        let score = offer(&relation)?;
        check_residual_sensitivity(&score)?;
        let joined = stream.context.stage_with_score_slack(OWNER, relation)?;
        c489_checked_source(score, &joined, &expected_maps)
    };
    let closure = C489Closure::new(source)?;
    let mut destination = C489Destination { sentinel: 489, published: None };
    closure.publish(&mut destination, closure.expected.clone())?;
    if destination.published.as_ref() != Some(&closure.expected) {
        return Err("c489 native positive publication".into());
    }
    let published = destination.clone();
    if closure.publish(&mut destination, closure.expected.clone()).err().as_deref()
        != Some("c489 replay") || destination != published
    {
        return Err("c489 native replay atomicity".into());
    }

    let mut native_negatives = 0usize;
    for field in 0..4 {
        let mut stage = stream.context.stage_with_slack(OWNER)?;
        match field {
            0 => stage.map_stage.parent_root[0] ^= 1,
            1 => stage.map_stage.parent_total[0] ^= 1,
            2 => stage.map_stage.parent_profile[0] ^= 1,
            _ => stage.map_stage.cut_identity[0] ^= 1,
        }
        let before = stage.clone();
        let error = stage.admit_score_relation(stream.closed_owner_relation(OWNER)?)
            .err().unwrap_or_default();
        if error != "Eligible08 Score relation parent/cut/owner/duplicate" || stage != before {
            return Err(format!("c489 native same-parent fault {field}: {error}"));
        }
        native_negatives += 1;
    }

    let mut reject_offer = |name: &str, expected: &str,
                            change: fn(&mut C489Offer)| -> Result<(), String> {
        let mut offered = closure.expected.clone();
        change(&mut offered);
        offered.digest = c489_digest(&offered)?;
        let mut target = C489Destination { sentinel: 489, published: None };
        let before = target.clone();
        let error = closure.publish(&mut target, offered).err().unwrap_or_default();
        if error != expected || target != before {
            return Err(format!("c489 native {name}: {error}"));
        }
        native_negatives += 1;
        Ok(())
    };
    reject_offer("missing Slack zero X", "c489 exact authored-zero Slack X",
        |offer| { offer.slack_cells.remove(0); })?;
    reject_offer("nonzero Slack X", "c489 exact authored-zero Slack X",
        |offer| { offer.slack_cells[0].value = true; })?;
    reject_offer("wrong Slack X author", "c489 exact authored-zero Slack X",
        |offer| { offer.slack_cells[0].context = 1; })?;
    reject_offer("missing Slack zero ROW", "c489 exact authored-zero Slack ROW",
        |offer| { offer.slack_terms.remove(0); })?;
    reject_offer("wrong Slack ROW author", "c489 exact authored-zero Slack ROW",
        |offer| { offer.slack_terms[0].context = 1; })?;
    reject_offer("duplicate Slack ROW lease", "c489 exact typed ROW/term census",
        |offer| { offer.slack_rows.push(offer.slack_rows[0]); })?;
    if native_negatives != C489_NATIVE_NEGATIVES {
        return Err("c489 native negative census".into());
    }

    Ok(format!("C489_NATIVE_SCORE_SLACK_SELECTED_PASS frame_sha256={} max_owners={} score_owners={} score_roles={} owner=845887 contexts=2 ordered_reads=1028 active_addresses=804 stored_reads=805 outputs=4870 terms=17864 rows=7516 max_owner=844798 source_digest={} selected_digest={} native_negatives={} residual_sensitivity=true map_generated=true slack_authored_zero=true replay_rejected=true score_only=false slack=true full_slice=false native=true full_history=false full_eq26=false header_zero=false all_owner=false common_x=false gkr=false pcs=false proof=false client=false",
        frame_sha, max_owners, score_owners, score_roles,
        hex(&source_digest(&closure.expected.score)?), hex(&closure.expected.digest),
        C489_NATIVE_NEGATIVES))
}

#[cfg(test)]
pub(super) fn run_c489_fixture<'a, R, S>(relation: R, stage: S) -> Result<(), String>
where
    R: Fn() -> H21ClosedScoreOwnerRelation<'a>,
    S: Fn() -> C489Stage,
{
    let source = || {
        let relation = relation();
        let expected_maps = relation.identity.map_bindings.clone();
        let score = offer(&relation)?;
        check_residual_sensitivity(&score)?;
        let mut joined = stage();
        joined.admit_score_relation(relation)?;
        c489_checked_source(score, &joined, &expected_maps)
    };
    let closure = C489Closure::new(source)?;
    let mut destination = C489Destination { sentinel: 489, published: None };
    closure.publish(&mut destination, closure.expected.clone())?;
    if destination.published.as_ref() != Some(&closure.expected) {
        return Err("c489 fixture positive publication".into());
    }
    let before_replay = destination.clone();
    if closure.publish(&mut destination, closure.expected.clone()).err().as_deref()
        != Some("c489 replay") || destination != before_replay
    {
        return Err("c489 fixture replay rejection".into());
    }
    let reject = |name: &str, expected: &str, change: fn(&mut C489Offer)| -> Result<(), String> {
        let mut offered = closure.expected.clone();
        change(&mut offered);
        offered.digest = c489_digest(&offered)?;
        let mut target = C489Destination { sentinel: 489, published: None };
        let before = target.clone();
        let error = closure.publish(&mut target, offered).err().unwrap_or_default();
        if error != expected || target != before {
            return Err(format!("c489 fixture {name}: {error}"));
        }
        Ok(())
    };
    reject("missing Slack zero cell", "c489 exact authored-zero Slack X",
        |offer| { offer.slack_cells.remove(0); })?;
    reject("foreign Slack zero author", "c489 exact authored-zero Slack X",
        |offer| { offer.slack_cells[0].context = 1; })?;
    reject("missing Slack zero term", "c489 exact authored-zero Slack ROW",
        |offer| { offer.slack_terms.remove(0); })?;
    reject("foreign Slack zero row", "c489 exact authored-zero Slack ROW",
        |offer| { offer.slack_terms[0].context = 1; })?;
    reject("duplicate Slack zero ROW author", "c489 exact typed ROW/term census",
        |offer| { offer.slack_rows.push(offer.slack_rows[0]); })?;
    reject("parent root", "c489 source identity",
        |offer| { offer.score.identity.root[0] ^= 1; offer.score.digest = digest(&offer.score).unwrap(); })?;
    reject("cut", "c489 source identity",
        |offer| { offer.score.identity.cut[0] ^= 1; offer.score.digest = digest(&offer.score).unwrap(); })?;
    reject("Score Work context", "c488 ordered typed occurrence",
        |offer| { offer.score.occurrences[804].context = 0; })?;
    Ok(())
}

// C490 is a no-frame producer-to-physical-consumer seam. The C489 source
// remains the conditional Score/Map/Slack authority; row_support supplies an
// independent relocated physical ROW and X-writer view for the selected owner.
// The conditional source exposes X write reservations, not assignments, so
// values remain C489-authored and this seam does not claim independent value
// derivation from the physical consumer.
#[cfg(test)]
#[derive(Clone, Debug, PartialEq, Eq)]
struct C490PhysicalTerm {
    writer: crate::h21_row_support::Family,
    term: Term,
}

#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum C490XAuthor {
    Score(ScoreReplayAuthor),
    Slack(usize),
}

#[cfg(test)]
#[derive(Clone, Debug, PartialEq, Eq)]
struct C490PhysicalX {
    address: usize,
    writer: crate::h21_row_support::Family,
    author: C490XAuthor,
    value: Fr,
}

#[cfg(test)]
#[derive(Clone, Debug, PartialEq, Eq)]
struct C490Offer {
    selected: C489Offer,
    physical_terms: Vec<C490PhysicalTerm>,
    physical_x: Vec<C490PhysicalX>,
    digest: [u8; 32],
}

#[cfg(test)]
#[derive(Clone, Debug, PartialEq, Eq)]
struct C490Destination {
    sentinel: u64,
    published: Option<C490Offer>,
}

#[cfg(test)]
struct C490Closure<F: Fn() -> Result<C490Offer, String>> {
    source: F,
    expected: C490Offer,
}

#[cfg(test)]
fn c490_family_tag(family: crate::h21_row_support::Family) -> Result<(u8, usize), String> {
    use crate::h21_row_support::Family;
    match family {
        Family::Score(context) if context < 2 => Ok((1, context)),
        Family::Slack(context) if context < 2 => Ok((2, context)),
        Family::V(context) if context < 2 => Ok((3, context)),
        Family::W(context) if context < 2 => Ok((4, context)),
        _ => Err("c490 unexpected physical family".into()),
    }
}

#[cfg(test)]
fn c490_source_family(context: usize, row: usize)
    -> Result<crate::h21_row_support::Family, String> {
    use crate::h21_row_support::Family;
    if context >= 2 { return Err("c490 source family context".into()); }
    let local = row.checked_sub(OWNER * ROW_WIDTH).ok_or("c490 source family owner")?;
    let bands = [
        (Family::Score(context), [487_421, 502_652][context], 4_208),
        (Family::V(context), [491_629, 506_860][context], 65),
        (Family::W(context), [491_694, 506_925][context], 224),
    ];
    let mut matches = bands.iter().filter(|(_, start, len)| (*start..*start + *len).contains(&local));
    let family = matches.next().map(|(family, _, _)| *family)
        .ok_or("c490 source family ROW band")?;
    if matches.next().is_some() { return Err("c490 overlapping source family ROW bands".into()); }
    Ok(family)
}

#[cfg(test)]
fn c490_digest(offer: &C490Offer) -> Result<[u8; 32], String> {
    let mut bytes = b"c490-physical-score-slack-slice-v1\0".to_vec();
    bytes.extend_from_slice(&offer.selected.digest);
    pu(&mut bytes, offer.physical_terms.len())?;
    for item in &offer.physical_terms {
        let (family, context) = c490_family_tag(item.writer)?;
        bytes.push(family);
        pu(&mut bytes, context)?;
        for value in [item.term.row, item.term.gate.left, item.term.gate.right] {
            pu(&mut bytes, value)?;
        }
        for value in [item.term.gate.c0, item.term.gate.c1,
            item.term.gate.c2, item.term.gate.c3] {
            pf(&mut bytes, &value)?;
        }
    }
    pu(&mut bytes, offer.physical_x.len())?;
    for item in &offer.physical_x {
        let (family, context) = c490_family_tag(item.writer)?;
        pu(&mut bytes, item.address)?;
        bytes.push(family);
        pu(&mut bytes, context)?;
        match item.author {
            C490XAuthor::Score(author) => { bytes.push(1); psa(&mut bytes, author)?; }
            C490XAuthor::Slack(author_context) => { bytes.push(2); pu(&mut bytes, author_context)?; }
        }
        pf(&mut bytes, &item.value)?;
    }
    Ok(ergo_header_core::blake2b256(&bytes))
}

#[cfg(test)]
fn c490_field_tag(value: &Fr) -> Result<String, String> {
    let mut bytes = Vec::new();
    pf(&mut bytes, value)?;
    let digest = ergo_header_core::blake2b256(&bytes);
    Ok(hex(&digest[..8]))
}

#[cfg(test)]
fn c490_term_brief(term: &Term) -> Result<String, String> {
    Ok(format!("row={} left={} right={} c0={} c1={} c2={} c3={}",
        term.row, term.gate.left, term.gate.right,
        c490_field_tag(&term.gate.c0)?, c490_field_tag(&term.gate.c1)?,
        c490_field_tag(&term.gate.c2)?, c490_field_tag(&term.gate.c3)?))
}

#[cfg(test)]
fn c490_mismatch_diagnostic(
    expected_terms: &BTreeMap<crate::h21_row_support::Family, Vec<Term>>,
    actual_terms: &BTreeMap<crate::h21_row_support::Family, Vec<Term>>,
    expected_rows: &BTreeSet<(usize, crate::h21_row_support::Family)>,
    actual_rows: &BTreeSet<(usize, crate::h21_row_support::Family)>,
) -> Result<String, String> {
    use crate::h21_row_support::Family;
    let families = [Family::Score(0), Family::Score(1), Family::V(0), Family::V(1),
        Family::W(0), Family::W(1), Family::Slack(0), Family::Slack(1)];
    let mut parts = Vec::new();
    for family in families {
        let expected = expected_terms.get(&family).map(Vec::as_slice).unwrap_or(&[]);
        let actual = actual_terms.get(&family).map(Vec::as_slice).unwrap_or(&[]);
        let first = (0..expected.len().min(actual.len())).find(|&index|
            expected[index] != actual[index]);
        let difference = match first {
            Some(index) => format!(" first_term[{index}] expected=({}) actual=({})",
                c490_term_brief(&expected[index])?, c490_term_brief(&actual[index])?),
            None if expected.len() != actual.len() => format!(
                " first_term[{}] expected={} actual={}", expected.len().min(actual.len()),
                expected.get(expected.len().min(actual.len())).map(c490_term_brief)
                    .transpose()?.unwrap_or_else(|| "<end>".into()),
                actual.get(expected.len().min(actual.len())).map(c490_term_brief)
                    .transpose()?.unwrap_or_else(|| "<end>".into())),
            None => String::new(),
        };
        parts.push(format!("{family:?} expected_len={} actual_len={}{}",
            expected.len(), actual.len(), difference));
    }
    let missing = expected_rows.difference(actual_rows).next();
    let extra = actual_rows.difference(expected_rows).next();
    parts.push(format!("typed_rows expected_count={} actual_count={} missing={missing:?} extra={extra:?}",
        expected_rows.len(), actual_rows.len()));
    Ok(parts.join("; "))
}

#[cfg(test)]
fn c490_checked_source(selected: C489Offer) -> Result<C490Offer, String> {
    use crate::h21_row_support::{Family, Sources, Writer};
    c489_validate(&selected)?;
    let batch = Sources::new()?.stage_sparse_score_owner(OWNER)?;
    if batch.owner() != OWNER {
        return Err("c490 physical owner".into());
    }

    // Compare exact terms per typed producer. Grouping by writer preserves
    // order and multiplicity within each source while allowing independent
    // producer iteration order across contexts.
    let mut expected_terms: BTreeMap<Family, Vec<Term>> = BTreeMap::new();
    for (context, term) in &selected.score.terms {
        let family = c490_source_family(*context, term.row)?;
        let physical = if matches!(family, Family::Score(_) | Family::V(_) | Family::W(_)) {
            term.clone()
        } else {
            crate::h21_row_support::relocate(family, OWNER, term)?
        };
        expected_terms.entry(family).or_default().push(
            physical);
    }
    for item in &selected.slack_terms {
        let family = Family::Slack(item.context);
        expected_terms.entry(family).or_default().push(
            crate::h21_row_support::relocate(family, OWNER, &item.term)?);
    }
    let mut physical_terms: Vec<C490PhysicalTerm> = batch.terms().iter().filter_map(|tagged| {
        match tagged.writer {
            Writer::Relocated(family @ (Family::Score(_) | Family::V(_) |
                Family::W(_) | Family::Slack(_))) =>
                Some(C490PhysicalTerm { writer: family, term: tagged.term.clone() }),
            _ => None,
        }
    }).collect();
    let mut actual_terms: BTreeMap<Family, Vec<Term>> = BTreeMap::new();
    for item in &physical_terms { actual_terms.entry(item.writer).or_default().push(item.term.clone()); }
    let mut expected_rows = BTreeSet::new();
    for row in &selected.score.rows {
        if row.context >= 2 || row.author != selected.score.identity.authors[row.context] {
            return Err("c490 selected Score ROW author".into());
        }
        let source = selected.score.terms.iter()
            .find(|(context, term)| *context == row.context && term.row == row.row)
            .map(|(_, term)| term)
            .ok_or("c490 selected Score ROW/source mismatch")?;
        let family = c490_source_family(row.context, source.row)?;
        if !expected_rows.insert((source.row, family)) {
            return Err("c490 duplicate selected Score ROW author".into());
        }
    }
    for row in &selected.slack_rows {
        if row.context >= 2 { return Err("c490 selected Slack ROW author".into()); }
        let family = Family::Slack(row.context);
        let source = selected.slack_terms.iter()
            .find(|item| item.context == row.context && item.term.row == row.row)
            .map(|item| &item.term)
            .ok_or("c490 selected Slack ROW/source mismatch")?;
        let relocated = crate::h21_row_support::relocate(family, OWNER, source)?;
        if !expected_rows.insert((relocated.row, family)) {
            return Err("c490 duplicate selected Slack ROW author".into());
        }
    }
    let actual_rows = physical_terms.iter().map(|item| (item.term.row, item.writer))
        .collect::<BTreeSet<_>>();
    if actual_terms != expected_terms
        || actual_rows != expected_rows
        || physical_terms.len() != C489_TERMS
        || expected_terms.get(&Family::Score(0)).map(Vec::len) != Some(8_032)
        || expected_terms.get(&Family::Score(1)).map(Vec::len) != Some(8_032)
        || expected_terms.get(&Family::V(0)).map(Vec::len) != Some(65)
        || expected_terms.get(&Family::V(1)).map(Vec::len) != Some(65)
        || expected_terms.get(&Family::W(0)).map(Vec::len) != Some(448)
        || expected_terms.get(&Family::W(1)).map(Vec::len) != Some(448)
        || expected_terms.get(&Family::Slack(0)).map(Vec::len) != Some(387)
        || expected_terms.get(&Family::Slack(1)).map(Vec::len) != Some(387)
    {
        let detail = c490_mismatch_diagnostic(
            &expected_terms, &actual_terms, &expected_rows, &actual_rows)?;
        return Err(format!("c490 exact relocated ROW terms/coefficients/author/multiplicity: {detail}"));
    }

    let mut selected_x: BTreeMap<usize, (Family, C490XAuthor, Fr)> = BTreeMap::new();
    for &(address, author, value) in &selected.score.cells {
        if selected_x.insert(address, (Family::Score(author.context),
            C490XAuthor::Score(author), value)).is_some() {
            return Err("c490 duplicate typed X author".into());
        }
    }
    for cell in &selected.slack_cells {
        if selected_x.insert(cell.address, (Family::Slack(cell.context),
            C490XAuthor::Slack(cell.context),
            if cell.value { Fr::one() } else { Fr::zero() })).is_some() {
            return Err("c490 duplicate typed X author".into());
        }
    }
    if selected_x.len() != C489_OUTPUTS { return Err("c490 physical X census".into()); }

    let mut physical_writers = BTreeMap::new();
    for (writer, wires) in batch.reservations() {
        let family = match writer {
            Writer::Relocated(family @ (Family::Score(_) | Family::Slack(_))) => family,
            _ => continue,
        };
        for local in wires {
            let address = OWNER * WIDTH + local;
            if physical_writers.insert(address, family).is_some() {
                return Err("c490 duplicate physical X writer".into());
            }
        }
    }
    if physical_writers.len() != C489_OUTPUTS || physical_writers.len() != selected_x.len() {
        return Err("c490 physical X reservation census".into());
    }
    let mut physical_x = Vec::with_capacity(C489_OUTPUTS);
    for (address, (family, author, value)) in selected_x {
        if physical_writers.get(&address) != Some(&family) {
            return Err("c490 exact physical X writer/author".into());
        }
        physical_x.push(C490PhysicalX { address, writer: family, author, value });
    }
    physical_terms.shrink_to_fit();
    let mut offer = C490Offer { selected, physical_terms, physical_x, digest: [0; 32] };
    c490_validate(&offer)?;
    offer.digest = c490_digest(&offer)?;
    Ok(offer)
}

#[cfg(test)]
fn c490_validate(offer: &C490Offer) -> Result<(), String> {
    use crate::h21_row_support::Family;
    c489_validate(&offer.selected)?;
    if offer.physical_terms.len() != C489_TERMS
        || offer.physical_x.len() != C489_OUTPUTS
    { return Err("c490 physical census".into()); }
    let mut rows = BTreeSet::new();
    let mut terms: BTreeMap<Family, Vec<Term>> = BTreeMap::new();
    for item in &offer.physical_terms {
        c490_family_tag(item.writer)?;
        terms.entry(item.writer).or_default().push(item.term.clone());
        rows.insert((item.term.row, item.writer));
    }
    let row_count = |family| rows.iter().filter(|(_, writer)| *writer == family).count();
    if rows.len() != C489_ROWS
        || terms.get(&Family::Score(0)).map(Vec::len) != Some(8_032)
        || terms.get(&Family::Score(1)).map(Vec::len) != Some(8_032)
        || terms.get(&Family::V(0)).map(Vec::len) != Some(65)
        || terms.get(&Family::V(1)).map(Vec::len) != Some(65)
        || terms.get(&Family::W(0)).map(Vec::len) != Some(448)
        || terms.get(&Family::W(1)).map(Vec::len) != Some(448)
        || terms.get(&Family::Slack(0)).map(Vec::len) != Some(387)
        || terms.get(&Family::Slack(1)).map(Vec::len) != Some(387)
        || row_count(Family::Score(0)) != 3_082
        || row_count(Family::Score(1)) != 3_082
        || row_count(Family::V(0)) != 65
        || row_count(Family::V(1)) != 65
        || row_count(Family::W(0)) != 224
        || row_count(Family::W(1)) != 224
        || row_count(Family::Slack(0)) != 387
        || row_count(Family::Slack(1)) != 387
    { return Err("c490 physical typed ROW census".into()); }
    let mut authors = BTreeMap::new();
    for item in &offer.physical_x {
        c490_family_tag(item.writer)?;
        let expected = match item.author {
            C490XAuthor::Score(author) if author.context < 2
                && item.writer == Family::Score(author.context) => true,
            C490XAuthor::Slack(context) if context < 2
                && item.writer == Family::Slack(context) && item.value.is_zero() => true,
            _ => false,
        };
        if !expected || authors.insert(item.address, (item.writer, item.author, item.value)).is_some() {
            return Err("c490 physical X author/value/duplicate".into());
        }
    }
    if authors.len() != C489_OUTPUTS { return Err("c490 physical X census".into()); }
    Ok(())
}

#[cfg(test)]
impl<F: Fn() -> Result<C490Offer, String>> C490Closure<F> {
    fn new(source: F) -> Result<Self, String> {
        let expected = source()?;
        Ok(Self { source, expected })
    }
    fn publish(&self, destination: &mut C490Destination, offered: C490Offer)
        -> Result<(), String> {
        if destination.published.is_some() { return Err("c490 replay".into()); }
        c490_validate(&offered)?;
        if c490_digest(&offered)? != offered.digest { return Err("c490 digest".into()); }
        let fresh = (self.source)()?;
        if fresh != self.expected || offered != fresh {
            return Err("c490 exact physical source replay".into());
        }
        destination.published = Some(offered);
        Ok(())
    }
}

#[cfg(test)]
pub(super) fn run_c490_fixture<'a, R, S>(relation: R, stage: S) -> Result<(), String>
where
    R: Fn() -> H21ClosedScoreOwnerRelation<'a>,
    S: Fn() -> C489Stage,
{
    let source = || {
        let relation = relation();
        let expected_maps = relation.identity.map_bindings.clone();
        let score = offer(&relation)?;
        check_residual_sensitivity(&score)?;
        let mut joined = stage();
        joined.admit_score_relation(relation)?;
        c490_checked_source(c489_checked_source(score, &joined, &expected_maps)?)
    };
    let closure = C490Closure::new(source)?;
    let mut destination = C490Destination { sentinel: 490, published: None };
    closure.publish(&mut destination, closure.expected.clone())?;
    if destination.published.as_ref() != Some(&closure.expected) {
        return Err("c490 fixture positive publication".into());
    }
    let reject = |name: &str, expected: &str, change: fn(&mut C490Offer)| -> Result<(), String> {
        let mut offered = closure.expected.clone();
        change(&mut offered);
        offered.digest = c490_digest(&offered)?;
        let mut target = C490Destination { sentinel: 490, published: None };
        let before = target.clone();
        let error = closure.publish(&mut target, offered).err().unwrap_or_default();
        if error != expected || target != before {
            return Err(format!("c490 fixture {name}: {error}"));
        }
        Ok(())
    };
    reject("old cut", "c489 source identity", |o| {
        o.selected.score.identity.cut = crate::h21_scheduled_max_cap::CutDescriptor::diagnostic08()
            .canonical_identity();
        o.selected.score.digest = digest(&o.selected.score).unwrap();
        o.selected.digest = c489_digest(&o.selected).unwrap();
    })?;
    reject("old Slack ROW", "c489 exact authored-zero Slack ROW", |o| {
        o.selected.slack_terms[0].term.row = OWNER * ROW_WIDTH + 491_918;
        o.selected.digest = c489_digest(&o.selected).unwrap();
    })?;
    reject("omitted Score ROW term", "c488 offer census", |o| {
        o.selected.score.terms.remove(0);
        o.selected.score.digest = digest(&o.selected.score).unwrap();
        o.selected.digest = c489_digest(&o.selected).unwrap();
    })?;
    reject("duplicate Slack ROW term", "c489 exact authored-zero Slack ROW", |o| {
        o.selected.slack_terms.push(o.selected.slack_terms[0].clone());
        o.selected.digest = c489_digest(&o.selected).unwrap();
    })?;
    reject("wrong Slack context", "c489 exact authored-zero Slack ROW", |o| {
        o.selected.slack_terms[0].context = 1;
        o.selected.digest = c489_digest(&o.selected).unwrap();
    })?;
    reject("wrong predecessor owner", "c488 ordered typed occurrence", |o| {
        o.selected.score.occurrences[0].author = ScoreRelationReadAuthor::PreviousR {
            context: 0, owner: 845_758,
        };
        o.selected.score.digest = digest(&o.selected.score).unwrap();
        o.selected.digest = c489_digest(&o.selected).unwrap();
    })?;
    reject("duplicate zero author", "c489 exact authored-zero Slack X", |o| {
        o.selected.slack_cells.push(o.selected.slack_cells[0].clone());
        o.selected.digest = c489_digest(&o.selected).unwrap();
    })?;
    reject("physical ROW omission", "c490 physical census", |o| {
        o.physical_terms.remove(0);
    })?;
    reject("physical ROW duplicate", "c490 physical census", |o| {
        o.physical_terms.push(o.physical_terms[0].clone());
    })?;
    reject("V/W family misclassification", "c490 physical typed ROW census", |o| {
        let index = o.physical_terms.iter().position(|item|
            item.writer == crate::h21_row_support::Family::V(0)).unwrap();
        o.physical_terms[index].writer = crate::h21_row_support::Family::Score(0);
    })?;
    reject("old W alias orientation", "c490 exact physical source replay", |o| {
        let item = o.physical_terms.iter_mut().find(|item|
            item.writer == crate::h21_row_support::Family::W(0)
                && item.term.gate.c1 == -Fr::one()
                && item.term.gate.c2.is_zero()).unwrap();
        let work_address = item.term.gate.left;
        item.term.gate.left = 0;
        item.term.gate.right = work_address;
        item.term.gate.c1 = Fr::zero();
        item.term.gate.c2 = -Fr::one();
    })?;
    reject("physical duplicate zero X", "c490 physical X author/value/duplicate", |o| {
        let duplicate = o.physical_x.iter().find(|x|
            matches!(x.author, C490XAuthor::Slack(_))).unwrap().clone();
        let slot = o.physical_x.iter().rposition(|x|
            matches!(x.author, C490XAuthor::Slack(_))).unwrap();
        o.physical_x[slot] = duplicate;
    })?;
    Ok(())
}

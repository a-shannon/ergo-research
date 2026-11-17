//! C487 terminal Score public binding.
//! Production-compiled source/relation code; no GKR, PCS, proof or client claim.

use super::*;
use ark_bn254::Fr;
use ark_ff::{One, PrimeField, Zero};
use ark_serialize::CanonicalSerialize;
use num_bigint::BigUint;
use std::collections::BTreeMap;

use crate::{gkr::Gate, sparse::Term, transcript::Transcript};

const PUBLIC_DOMAIN: &[u8; 29] = b"nipopow-v2-terminal-public-v1";
const AUX_DOMAIN: &[u8] = b"nipopow-v2-terminal-gap-aux-v1";
const TRANSCRIPT_DOMAIN: &[u8] = b"nipopow-v2-terminal-public-binding-v1";
const CONTINUATION: &[u8] = b"nipopow-v2-terminal-public-continuation-v1";
const ORDER_TAG: &[u8] = b"r0-bool-0..224;g-bool-0..223;r0-high;packed-r0-then-g;ab-0..224";
const ABI_BYTES: usize = 256;
const CUT_BYTES: usize = 72;
const AB_BYTES: usize = 29;
const R_BITS: usize = 225;
const G_BITS: usize = 224;
const ROWS: usize = 676;
const TERMS: usize = 1_124;
const G_BASE: usize = 1usize << 41;
const TERMINAL_OWNERS: [usize; 2] = [1_810_904, 1_810_841];
const TERMINAL_ORIGINS: [usize; 2] = [1_810_905, 1_810_842];
const PREVIOUS_OWNERS: [usize; 2] = [1_810_879, 1_810_751];
const MAX_OWNERS: [usize; 2] = [1_809_918, 1_809_790];

#[derive(Clone, Debug, PartialEq, Eq)]
struct RelationDescriptor {
    aux_domain: Vec<u8>,
    g_base: usize,
    g_width: usize,
    g_author: Vec<u8>,
    rows: usize,
    terms: usize,
    order: Vec<u8>,
}

impl RelationDescriptor {
    fn canonical() -> Self {
        Self {
            aux_domain: AUX_DOMAIN.to_vec(),
            g_base: G_BASE,
            g_width: G_BITS,
            g_author: b"TerminalGapAuxV1".to_vec(),
            rows: ROWS,
            terms: TERMS,
            order: ORDER_TAG.to_vec(),
        }
    }

    fn validate(&self) -> Result<(), String> {
        if self != &Self::canonical()
            || self.g_base.checked_add(self.g_width) != Some(G_BASE + G_BITS)
            || self.g_base < (1usize << 41)
        {
            return Err("c487 relation descriptor domain/base/width/author/order".into());
        }
        Ok(())
    }

    fn bind(&self, transcript: &mut Transcript) -> Result<(), String> {
        self.validate()?;
        transcript.append_bytes(b"c487-aux-domain", &self.aux_domain);
        transcript.append_u64(b"c487-g-base", self.g_base as u64);
        transcript.append_u64(b"c487-g-width", self.g_width as u64);
        transcript.append_bytes(b"c487-g-author", &self.g_author);
        transcript.append_u64(b"c487-rows", self.rows as u64);
        transcript.append_u64(b"c487-terms", self.terms as u64);
        transcript.append_bytes(b"c487-order", &self.order);
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PublicRecord {
    context: u8,
    owner: u64,
    origin: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct TerminalPublic {
    root: [u8; 32],
    total: [u8; 28],
    profile: [u8; 32],
    cut: [u8; CUT_BYTES],
    records: [PublicRecord; 2],
    ab: [u8; AB_BYTES],
}

impl TerminalPublic {
    fn from_material(material: &TerminalMaterial) -> Result<Self, String> {
        material.validate_basic()?;
        Ok(Self {
            root: material.root,
            total: material.total,
            profile: material.profile,
            cut: material.cut,
            records: [
                PublicRecord {
                    context: 0,
                    owner: TERMINAL_OWNERS[0] as u64,
                    origin: TERMINAL_ORIGINS[0] as u64,
                },
                PublicRecord {
                    context: 1,
                    owner: TERMINAL_OWNERS[1] as u64,
                    origin: TERMINAL_ORIGINS[1] as u64,
                },
            ],
            ab: encode_u225(&material.value(1)?)?,
        })
    }

    fn encode(&self) -> [u8; ABI_BYTES] {
        let mut out = [0u8; ABI_BYTES];
        let mut at = 0usize;
        put(&mut out, &mut at, PUBLIC_DOMAIN);
        put(&mut out, &mut at, &self.root);
        put(&mut out, &mut at, &self.total);
        put(&mut out, &mut at, &self.profile);
        put(&mut out, &mut at, &self.cut);
        for record in self.records {
            put(&mut out, &mut at, &[record.context]);
            put(&mut out, &mut at, &record.owner.to_be_bytes());
            put(&mut out, &mut at, &record.origin.to_be_bytes());
        }
        put(&mut out, &mut at, &self.ab);
        assert_eq!(at, ABI_BYTES);
        out
    }

    fn decode(bytes: &[u8]) -> Result<Self, String> {
        if bytes.len() != ABI_BYTES {
            return Err("c487 public exact 256-byte ABI".into());
        }
        let mut at = 0usize;
        if take(bytes, &mut at, PUBLIC_DOMAIN.len())? != PUBLIC_DOMAIN {
            return Err("c487 public domain/version".into());
        }
        let root = fixed(take(bytes, &mut at, 32)?)?;
        let total = fixed(take(bytes, &mut at, 28)?)?;
        let profile = fixed(take(bytes, &mut at, 32)?)?;
        let cut = fixed(take(bytes, &mut at, CUT_BYTES)?)?;
        let expected_cut: [u8; CUT_BYTES] = H21EligibleMapStage::descriptor()
            .canonical_identity()
            .try_into()
            .map_err(|_| "c487 public expected cut identity width")?;
        if cut != expected_cut {
            return Err("c487 public canonical Eligible08 cut".into());
        }
        let mut records = Vec::with_capacity(2);
        for expected_context in 0..2u8 {
            let context = take(bytes, &mut at, 1)?[0];
            let owner = u64::from_be_bytes(fixed(take(bytes, &mut at, 8)?)?);
            let origin = u64::from_be_bytes(fixed(take(bytes, &mut at, 8)?)?);
            if context != expected_context
                || owner != TERMINAL_OWNERS[usize::from(context)] as u64
                || origin != TERMINAL_ORIGINS[usize::from(context)] as u64
            {
                return Err("c487 public terminal record".into());
            }
            records.push(PublicRecord {
                context,
                owner,
                origin,
            });
        }
        let ab: [u8; AB_BYTES] = fixed(take(bytes, &mut at, AB_BYTES)?)?;
        if ab[0] & 0xfe != 0 || at != bytes.len() {
            return Err("c487 public canonical U225 AB".into());
        }
        Ok(Self {
            root,
            total,
            profile,
            cut,
            records: records.try_into().map_err(|_| "c487 public record pair")?,
            ab,
        })
    }

    fn ab_value(&self) -> BigUint {
        BigUint::from_bytes_be(&self.ab)
    }

    fn bind(&self, transcript: &mut Transcript) -> Result<(), String> {
        if transcript.challenges() != 0 {
            return Err("c487 public binding after challenge".into());
        }
        transcript.append_bytes(b"c487-public", &self.encode());
        RelationDescriptor::canonical().bind(transcript)
    }
}

fn put<const N: usize>(out: &mut [u8; N], at: &mut usize, bytes: &[u8]) {
    let end = *at + bytes.len();
    out[*at..end].copy_from_slice(bytes);
    *at = end;
}

fn take<'a>(bytes: &'a [u8], at: &mut usize, len: usize) -> Result<&'a [u8], String> {
    let end = (*at)
        .checked_add(len)
        .ok_or("c487 public cursor overflow")?;
    let value = bytes
        .get(*at..end)
        .ok_or_else(|| "c487 public truncated".to_string())?;
    *at = end;
    Ok(value)
}

fn fixed<const N: usize>(bytes: &[u8]) -> Result<[u8; N], String> {
    bytes.try_into().map_err(|_| "c487 fixed field".into())
}

fn encode_u225(value: &BigUint) -> Result<[u8; AB_BYTES], String> {
    if value.bits() > R_BITS as u64 {
        return Err("c487 AB exceeds U225".into());
    }
    let bytes = value.to_bytes_be();
    if bytes.len() > AB_BYTES {
        return Err("c487 AB byte width".into());
    }
    let mut out = [0u8; AB_BYTES];
    out[AB_BYTES - bytes.len()..].copy_from_slice(&bytes);
    if out[0] & 0xfe != 0 {
        return Err("c487 AB high bits".into());
    }
    Ok(out)
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct TerminalCell {
    address: usize,
    value: Fr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct TerminalOccurrence {
    context: usize,
    owner: usize,
    origin: usize,
    author: ScoreReplayAuthor,
    cells: Vec<TerminalCell>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct TerminalMaterial {
    root: [u8; 32],
    total: [u8; 28],
    profile: [u8; 32],
    cut: [u8; CUT_BYTES],
    occurrences: [TerminalOccurrence; 2],
    source_x_identity: [u8; 32],
}

impl TerminalMaterial {
    fn from_stream<'ctx, 'src, 'max, 'snapshot>(
        stream: &H21ScoreEndpointStream<'ctx, 'src, 'max, 'snapshot>,
    ) -> Result<Self, String> {
        let terminal = stream.terminal_r()?;
        let layout = score::Layout::new();
        let mut occurrences = Vec::with_capacity(2);
        let mut identity: Option<([u8; 32], [u8; 28], [u8; 32], [u8; CUT_BYTES])> = None;
        for context in 0..2 {
            let owner = TERMINAL_OWNERS[context];
            let relation = stream.closed_owner_relation(owner)?;
            let cut: [u8; CUT_BYTES] = relation
                .cut_identity()
                .try_into()
                .map_err(|_| "c487 exact cut identity width")?;
            let current = (
                relation.parent_root(),
                relation.parent_total(),
                relation.parent_profile(),
                cut,
            );
            if identity.is_some_and(|expected| expected != current) {
                return Err("c487 terminal pair parent/cut identity".into());
            }
            identity = Some(current);
            let author =
                relation.authors()[context].ok_or("c487 terminal active context author")?;
            let start = owner
                .checked_mul(WIDTH)
                .and_then(|base| base.checked_add(SCORE_X[context] + layout.r.start))
                .ok_or("c487 terminal R address overflow")?;
            let map: BTreeMap<usize, (ScoreReplayAuthor, Fr)> = relation
                .cells()
                .iter()
                .map(|(address, cell_author, value)| (*address, (*cell_author, *value)))
                .collect();
            let cells = (0..R_BITS)
                .map(|bit| {
                    let address = start + bit;
                    let (cell_author, value) = *map
                        .get(&address)
                        .ok_or("c487 terminal R source cell missing")?;
                    if cell_author != author {
                        return Err("c487 terminal R source cell author".into());
                    }
                    Ok(TerminalCell { address, value })
                })
                .collect::<Result<Vec<_>, String>>()?;
            let occurrence = TerminalOccurrence {
                context,
                owner,
                origin: TERMINAL_ORIGINS[context],
                author,
                cells,
            };
            if occurrence.value()? != terminal[context] {
                return Err("c487 terminal R scalar/cell mismatch".into());
            }
            occurrences.push(occurrence);
        }
        let (root, total, profile, cut) = identity.ok_or("c487 terminal source identity")?;
        let mut material = Self {
            root,
            total,
            profile,
            cut,
            occurrences: occurrences
                .try_into()
                .map_err(|_| "c487 terminal occurrence pair")?,
            source_x_identity: [0u8; 32],
        };
        material.source_x_identity = material.recompute_source_x_identity()?;
        material.validate_basic()?;
        Ok(material)
    }

    fn value(&self, context: usize) -> Result<BigUint, String> {
        self.occurrences
            .get(context)
            .ok_or_else(|| "c487 terminal value context".to_string())?
            .value()
    }

    fn validate_basic(&self) -> Result<(), String> {
        let expected_cut: [u8; CUT_BYTES] = H21EligibleMapStage::descriptor()
            .canonical_identity()
            .try_into()
            .map_err(|_| "c487 expected cut identity width")?;
        if self.cut != expected_cut {
            return Err("c487 terminal Eligible08 cut identity".into());
        }
        for context in 0..2 {
            let occurrence = &self.occurrences[context];
            let expected_author = ScoreReplayAuthor {
                context,
                origin: TERMINAL_ORIGINS[context],
                previous_owner: PREVIOUS_OWNERS[context],
                max_owner: MAX_OWNERS[context],
                cap_owner: TERMINAL_OWNERS[context],
            };
            if occurrence.context != context
                || occurrence.owner != TERMINAL_OWNERS[context]
                || occurrence.origin != TERMINAL_ORIGINS[context]
                || occurrence.author != expected_author
                || occurrence.cells.len() != R_BITS
            {
                return Err("c487 terminal occurrence identity".into());
            }
            let start = occurrence
                .owner
                .checked_mul(WIDTH)
                .and_then(|base| base.checked_add(SCORE_X[context] + score::Layout::new().r.start))
                .ok_or("c487 terminal occurrence address overflow")?;
            for (bit, cell) in occurrence.cells.iter().enumerate() {
                if cell.address != start + bit
                    || (cell.value != Fr::zero() && cell.value != Fr::one())
                {
                    return Err("c487 terminal occurrence cell census".into());
                }
            }
        }
        if self.source_x_identity != self.recompute_source_x_identity()? {
            return Err("c487 terminal source-X replay".into());
        }
        Ok(())
    }

    fn recompute_source_x_identity(&self) -> Result<[u8; 32], String> {
        let mut bytes = b"nipopow-v2-terminal-source-x-v1\0".to_vec();
        bytes.extend_from_slice(&self.root);
        bytes.extend_from_slice(&self.total);
        bytes.extend_from_slice(&self.profile);
        bytes.extend_from_slice(&self.cut);
        for occurrence in &self.occurrences {
            for value in [
                occurrence.context,
                occurrence.owner,
                occurrence.origin,
                occurrence.author.context,
                occurrence.author.origin,
                occurrence.author.previous_owner,
                occurrence.author.max_owner,
                occurrence.author.cap_owner,
            ] {
                bytes.extend_from_slice(
                    &u64::try_from(value)
                        .map_err(|_| "c487 source identity usize/u64")?
                        .to_be_bytes(),
                );
            }
            for cell in &occurrence.cells {
                bytes.extend_from_slice(
                    &u64::try_from(cell.address)
                        .map_err(|_| "c487 source address usize/u64")?
                        .to_be_bytes(),
                );
                let bit = if cell.value == Fr::zero() {
                    0
                } else if cell.value == Fr::one() {
                    1
                } else {
                    return Err("c487 source identity nonboolean".into());
                };
                bytes.push(bit);
            }
        }
        Ok(ergo_header_core::blake2b256(&bytes))
    }

    #[cfg(test)]
    fn synthetic(r0: BigUint, total: BigUint, r1: BigUint) -> Result<Self, String> {
        if total.bits() > G_BITS as u64 {
            return Err("c487 synthetic total U224".into());
        }
        let total = encode_u224(&total)?;
        let cut: [u8; CUT_BYTES] = H21EligibleMapStage::descriptor()
            .canonical_identity()
            .try_into()
            .map_err(|_| "c487 synthetic cut identity width")?;
        let mut occurrences = Vec::with_capacity(2);
        for (context, value) in [r0, r1].into_iter().enumerate() {
            if value.bits() > R_BITS as u64 {
                return Err("c487 synthetic R U225".into());
            }
            let owner = TERMINAL_OWNERS[context];
            let start = owner * WIDTH + SCORE_X[context] + score::Layout::new().r.start;
            occurrences.push(TerminalOccurrence {
                context,
                owner,
                origin: TERMINAL_ORIGINS[context],
                author: ScoreReplayAuthor {
                    context,
                    origin: TERMINAL_ORIGINS[context],
                    previous_owner: PREVIOUS_OWNERS[context],
                    max_owner: MAX_OWNERS[context],
                    cap_owner: TERMINAL_OWNERS[context],
                },
                cells: (0..R_BITS)
                    .map(|bit| TerminalCell {
                        address: start + bit,
                        value: Fr::from(value.bit(bit as u64) as u64),
                    })
                    .collect(),
            });
        }
        let mut out = Self {
            root: [0x72; 32],
            total,
            profile: [0x74; 32],
            cut,
            occurrences: occurrences
                .try_into()
                .map_err(|_| "c487 synthetic occurrence pair")?,
            source_x_identity: [0u8; 32],
        };
        out.source_x_identity = out.recompute_source_x_identity()?;
        out.validate_basic()?;
        Ok(out)
    }
}

impl TerminalOccurrence {
    fn value(&self) -> Result<BigUint, String> {
        let mut out = BigUint::from(0u8);
        for (bit, cell) in self.cells.iter().enumerate() {
            if cell.value == Fr::one() {
                out |= BigUint::from(1u8) << bit;
            } else if cell.value != Fr::zero() {
                return Err("c487 terminal occurrence nonboolean".into());
            }
        }
        Ok(out)
    }
}

fn encode_u224(value: &BigUint) -> Result<[u8; 28], String> {
    if value.bits() > G_BITS as u64 {
        return Err("c487 total exceeds U224".into());
    }
    let bytes = value.to_bytes_be();
    let mut out = [0u8; 28];
    out[28 - bytes.len()..].copy_from_slice(&bytes);
    Ok(out)
}

struct BorrowedTerminalSource<'a, 'ctx, 'src, 'max, 'snapshot> {
    stream: &'a H21ScoreEndpointStream<'ctx, 'src, 'max, 'snapshot>,
    material: TerminalMaterial,
}

impl<'a, 'ctx, 'src, 'max, 'snapshot> BorrowedTerminalSource<'a, 'ctx, 'src, 'max, 'snapshot> {
    fn new(
        stream: &'a H21ScoreEndpointStream<'ctx, 'src, 'max, 'snapshot>,
    ) -> Result<Self, String> {
        Ok(Self {
            stream,
            material: TerminalMaterial::from_stream(stream)?,
        })
    }

    fn validate(&self) -> Result<(), String> {
        let expected = TerminalMaterial::from_stream(self.stream)?;
        if self.material != expected {
            return Err("c487 borrowed terminal source replay".into());
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct TerminalRelation {
    material: TerminalMaterial,
    public: TerminalPublic,
    descriptor: RelationDescriptor,
    gap_claims: Vec<GapClaim>,
    terms: Vec<Term>,
    values: BTreeMap<usize, Fr>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PrototypeAuthor {
    TerminalGapAuxV1,
    Unrecognized,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct GapClaim {
    address: usize,
    value: Fr,
    author: PrototypeAuthor,
}

impl TerminalRelation {
    fn new(material: TerminalMaterial, public: TerminalPublic) -> Result<Self, String> {
        material.validate_basic()?;
        if (public.root, public.total, public.profile, public.cut)
            != (
                material.root,
                material.total,
                material.profile,
                material.cut,
            )
        {
            return Err("c487 source/public parent or cut".into());
        }
        let encoded = public.encode();
        if TerminalPublic::decode(&encoded)? != public {
            return Err("c487 public canonical roundtrip".into());
        }
        let gap_claims = expected_gap_claims(&material, &public)?;
        let values = relation_values(&material, &gap_claims)?;
        let r0_addresses = material.occurrences[0]
            .cells
            .iter()
            .map(|cell| cell.address)
            .collect::<Vec<_>>();
        let r1_addresses = material.occurrences[1]
            .cells
            .iter()
            .map(|cell| cell.address)
            .collect::<Vec<_>>();
        let terms = relation_terms(&r0_addresses, &r1_addresses, &public)?;
        let relation = Self {
            material,
            public,
            descriptor: RelationDescriptor::canonical(),
            gap_claims,
            terms,
            values,
        };
        relation.validate()?;
        Ok(relation)
    }

    fn validate(&self) -> Result<(), String> {
        self.material.validate_basic()?;
        self.descriptor.validate()?;
        if (
            self.public.root,
            self.public.total,
            self.public.profile,
            self.public.cut,
        ) != (
            self.material.root,
            self.material.total,
            self.material.profile,
            self.material.cut,
        ) || TerminalPublic::decode(&self.public.encode())? != self.public
        {
            return Err("c487 relation public/source identity".into());
        }
        let expected_gap_claims = expected_gap_claims(&self.material, &self.public)?;
        if self.gap_claims != expected_gap_claims
            || self.values != relation_values(&self.material, &expected_gap_claims)?
        {
            return Err("c487 exact sparse source/auxiliary values".into());
        }
        if self.terms.len() != TERMS {
            return Err("c487 exact term census".into());
        }
        let expected = relation_terms(
            &self.material.occurrences[0]
                .cells
                .iter()
                .map(|cell| cell.address)
                .collect::<Vec<_>>(),
            &self.material.occurrences[1]
                .cells
                .iter()
                .map(|cell| cell.address)
                .collect::<Vec<_>>(),
            &self.public,
        )?;
        if self.terms != expected {
            return Err("c487 exact row/term topology".into());
        }
        let rows = residuals(&self.terms, &self.values)?;
        if rows.len() != ROWS || rows.values().any(|value| !value.is_zero()) {
            return Err("c487 terminal relation residual".into());
        }
        Ok(())
    }
}

fn expected_gap_claims(
    material: &TerminalMaterial,
    public: &TerminalPublic,
) -> Result<Vec<GapClaim>, String> {
    let total = BigUint::from_bytes_be(&public.total);
    let r0 = material.value(0)?;
    if r0 > total {
        return Err("c487 Eq21 terminal bound".into());
    }
    let gap = &total - &r0;
    (0..G_BITS)
        .map(|bit| {
            Ok(GapClaim {
                address: G_BASE.checked_add(bit).ok_or("c487 G address overflow")?,
                value: Fr::from(gap.bit(bit as u64) as u64),
                author: PrototypeAuthor::TerminalGapAuxV1,
            })
        })
        .collect()
}

fn relation_values(
    material: &TerminalMaterial,
    gap_claims: &[GapClaim],
) -> Result<BTreeMap<usize, Fr>, String> {
    let mut values = BTreeMap::new();
    if values.insert(0, Fr::zero()).is_some() {
        return Err("c487 structural zero collision".into());
    }
    for occurrence in &material.occurrences {
        for cell in &occurrence.cells {
            if values.insert(cell.address, cell.value).is_some() {
                return Err("c487 terminal source address collision".into());
            }
        }
    }
    if gap_claims.len() != G_BITS {
        return Err("c487 G claim census".into());
    }
    for (bit, claim) in gap_claims.iter().enumerate() {
        if claim.address != G_BASE + bit
            || claim.author != PrototypeAuthor::TerminalGapAuxV1
            || (claim.value != Fr::zero() && claim.value != Fr::one())
            || values.insert(claim.address, claim.value).is_some()
        {
            return Err("c487 G claim address/author/value".into());
        }
    }
    Ok(values)
}

fn relation_terms(
    r0: &[usize],
    r1: &[usize],
    public: &TerminalPublic,
) -> Result<Vec<Term>, String> {
    if r0.len() != R_BITS || r1.len() != R_BITS {
        return Err("c487 relation R address census".into());
    }
    let zero = Fr::zero();
    let one = Fr::one();
    let mut terms = Vec::with_capacity(TERMS);
    let mut row = 0usize;
    for &address in r0 {
        terms.push(Term {
            row,
            gate: Gate {
                left: address,
                right: address,
                c0: zero,
                c1: -one,
                c2: zero,
                c3: one,
            },
        });
        row += 1;
    }
    for bit in 0..G_BITS {
        let address = G_BASE
            .checked_add(bit)
            .ok_or("c487 G boolean address overflow")?;
        terms.push(Term {
            row,
            gate: Gate {
                left: address,
                right: address,
                c0: zero,
                c1: -one,
                c2: zero,
                c3: one,
            },
        });
        row += 1;
    }
    terms.push(Term {
        row,
        gate: Gate {
            left: r0[R_BITS - 1],
            right: 0,
            c0: zero,
            c1: one,
            c2: zero,
            c3: zero,
        },
    });
    row += 1;
    let total = BigUint::from_bytes_be(&public.total);
    let mut weight = Fr::one();
    for (bit, &address) in r0.iter().enumerate() {
        terms.push(Term {
            row,
            gate: Gate {
                left: address,
                right: 0,
                c0: if bit == 0 {
                    -Fr::from_le_bytes_mod_order(&total.to_bytes_le())
                } else {
                    zero
                },
                c1: weight,
                c2: zero,
                c3: zero,
            },
        });
        weight += weight;
    }
    weight = Fr::one();
    for bit in 0..G_BITS {
        terms.push(Term {
            row,
            gate: Gate {
                left: G_BASE + bit,
                right: 0,
                c0: zero,
                c1: weight,
                c2: zero,
                c3: zero,
            },
        });
        weight += weight;
    }
    row += 1;
    let ab = public.ab_value();
    for (bit, &address) in r1.iter().enumerate() {
        terms.push(Term {
            row,
            gate: Gate {
                left: address,
                right: 0,
                c0: -Fr::from(ab.bit(bit as u64) as u64),
                c1: one,
                c2: zero,
                c3: zero,
            },
        });
        row += 1;
    }
    if row != ROWS || terms.len() != TERMS {
        return Err("c487 relation row/term census".into());
    }
    Ok(terms)
}

fn residuals(terms: &[Term], values: &BTreeMap<usize, Fr>) -> Result<BTreeMap<usize, Fr>, String> {
    let mut rows = BTreeMap::new();
    for term in terms {
        let left = *values
            .get(&term.gate.left)
            .ok_or("c487 relation left lookup")?;
        let right = *values
            .get(&term.gate.right)
            .ok_or("c487 relation right lookup")?;
        *rows.entry(term.row).or_insert_with(Fr::zero) +=
            term.gate.c0 + term.gate.c1 * left + term.gate.c2 * right + term.gate.c3 * left * right;
    }
    Ok(rows)
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Destination {
    public_sha256: Option<[u8; 32]>,
}

impl Destination {
    fn empty() -> Self {
        Self {
            public_sha256: None,
        }
    }
}

struct Closure {
    expected: TerminalRelation,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct TerminalOffer {
    public: [u8; ABI_BYTES],
}

impl Closure {
    fn new(material: TerminalMaterial) -> Result<Self, String> {
        let public = TerminalPublic::from_material(&material)?;
        Ok(Self {
            expected: TerminalRelation::new(material, public)?,
        })
    }

    fn offer(&self) -> TerminalOffer {
        TerminalOffer {
            public: self.expected.public.encode(),
        }
    }

    fn publish(&self, destination: &mut Destination, offered: TerminalOffer) -> Result<(), String> {
        if destination.public_sha256.is_some() {
            return Err("c487 duplicate publication".into());
        }
        let public = TerminalPublic::decode(&offered.public)?;
        if public != self.expected.public {
            return Err("c487 offered public mismatch".into());
        }
        self.expected.validate()?;
        destination.public_sha256 = Some(ergo_header_core::blake2b256(&offered.public));
        Ok(())
    }
}

fn transcript_pair(public: &TerminalPublic) -> Result<([u64; 3], Fr), String> {
    let bytes = public.encode();
    let decoded = TerminalPublic::decode(&bytes)?;
    if decoded.encode() != bytes {
        return Err("c487 cold canonical re-encode".into());
    }
    let mut producer = Transcript::new(TRANSCRIPT_DOMAIN);
    public.bind(&mut producer)?;
    let mut cold = Transcript::new(TRANSCRIPT_DOMAIN);
    decoded.bind(&mut cold)?;
    let producer_counters = [
        producer.challenges(),
        producer.raw_queries(),
        producer.bytes_absorbed(),
    ];
    let cold_counters = [cold.challenges(), cold.raw_queries(), cold.bytes_absorbed()];
    if producer_counters != cold_counters {
        return Err("c487 producer/cold transcript counters".into());
    }
    let producer_next = producer.try_challenge_scalar(CONTINUATION)?;
    let cold_next = cold.try_challenge_scalar(CONTINUATION)?;
    if producer_next != cold_next {
        return Err("c487 producer/cold continuation".into());
    }
    Ok((producer_counters, producer_next))
}

fn reject_internal(
    relation: &TerminalRelation,
    mutate: impl FnOnce(&mut TerminalRelation),
) -> Result<(), String> {
    let mut candidate = relation.clone();
    mutate(&mut candidate);
    if candidate.validate().is_ok() {
        return Err("c487 internal source/relation mutant accepted".into());
    }
    Ok(())
}

fn reject_public(
    closure: &Closure,
    mutate: impl FnOnce(&mut [u8; ABI_BYTES]),
) -> Result<(), String> {
    let mut offer = closure.offer();
    mutate(&mut offer.public);
    let mut destination = Destination::empty();
    let before = destination.clone();
    if closure.publish(&mut destination, offer).is_ok() || destination != before {
        return Err("c487 public negative accepted or destination changed".into());
    }
    Ok(())
}

fn exercise(
    material: TerminalMaterial,
    mut authenticate: impl FnMut(&TerminalMaterial) -> Result<(), String>,
) -> Result<(usize, [u8; 32]), String> {
    authenticate(&material)?;
    let closure = Closure::new(material.clone())?;
    let mut destination = Destination::empty();
    closure.publish(&mut destination, closure.offer())?;
    let public_sha256 = destination
        .public_sha256
        .ok_or("c487 publication digest missing")?;
    transcript_pair(&closure.expected.public)?;
    let mut negatives = 0usize;

    let mut wrong_ab = closure.expected.public.encode();
    wrong_ab[ABI_BYTES - 1] ^= 1;
    let wrong_ab = TerminalPublic::decode(&wrong_ab)?;
    if TerminalRelation::new(material.clone(), wrong_ab).is_ok() {
        return Err("c487 AB bit mutant accepted".into());
    }
    negatives += 1;
    reject_public(&closure, |bytes| bytes[29] ^= 1)?;
    negatives += 1;
    reject_public(&closure, |bytes| bytes[61] ^= 1)?;
    negatives += 1;
    reject_public(&closure, |bytes| bytes[89] ^= 1)?;
    negatives += 1;
    reject_public(&closure, |bytes| bytes[121] ^= 1)?;
    negatives += 1;
    reject_public(&closure, |bytes| bytes[193] = 1)?;
    negatives += 1;
    reject_public(&closure, |bytes| bytes[201] ^= 1)?;
    negatives += 1;
    reject_public(&closure, |bytes| bytes[209] ^= 1)?;
    negatives += 1;

    reject_internal(&closure.expected, |relation| relation.material.root[0] ^= 1)?;
    negatives += 1;
    reject_internal(&closure.expected, |relation| relation.material.cut[0] ^= 1)?;
    negatives += 1;
    reject_internal(&closure.expected, |relation| {
        relation.material.occurrences.swap(0, 1)
    })?;
    negatives += 1;
    reject_internal(&closure.expected, |relation| {
        relation.material.occurrences[0].owner -= 1
    })?;
    negatives += 1;
    reject_internal(&closure.expected, |relation| {
        relation.material.occurrences[1].origin -= 1
    })?;
    negatives += 1;
    reject_internal(&closure.expected, |relation| {
        relation.material.occurrences[0].author.previous_owner -= 1
    })?;
    negatives += 1;
    reject_internal(&closure.expected, |relation| {
        relation.material.occurrences[0].cells.remove(0);
    })?;
    negatives += 1;
    reject_internal(&closure.expected, |relation| {
        let duplicate = relation.material.occurrences[1].cells[0].clone();
        relation.material.occurrences[1].cells.push(duplicate);
    })?;
    negatives += 1;
    reject_internal(&closure.expected, |relation| {
        relation.material.occurrences[0].cells[0].address += 1
    })?;
    negatives += 1;
    reject_internal(&closure.expected, |relation| {
        relation.material.occurrences[0].cells[0].value = Fr::from(2u64)
    })?;
    negatives += 1;
    reject_internal(&closure.expected, |relation| {
        relation.terms[0].gate.c3 = Fr::zero()
    })?;
    negatives += 1;
    reject_internal(&closure.expected, |relation| relation.terms.swap(0, 1))?;
    negatives += 1;
    reject_internal(&closure.expected, |relation| relation.terms.swap(450, 451))?;
    negatives += 1;
    reject_internal(&closure.expected, |relation| {
        let packed = 449 + 1;
        relation.terms[packed].gate.c0 += Fr::one()
    })?;
    negatives += 1;
    reject_internal(&closure.expected, |relation| {
        let first_g_boolean = R_BITS;
        relation.terms[first_g_boolean].gate.left = G_BASE - 1;
        relation.terms[first_g_boolean].gate.right = G_BASE - 1;
    })?;
    negatives += 1;
    reject_internal(&closure.expected, |relation| {
        relation.gap_claims[0].author = PrototypeAuthor::Unrecognized
    })?;
    negatives += 1;
    reject_internal(&closure.expected, |relation| {
        relation.gap_claims[0].address = G_BASE - 1
    })?;
    negatives += 1;
    reject_internal(&closure.expected, |relation| {
        relation.gap_claims[1].address = relation.gap_claims[0].address
    })?;
    negatives += 1;
    reject_internal(&closure.expected, |relation| {
        relation.descriptor.aux_domain.push(0)
    })?;
    negatives += 1;
    reject_internal(&closure.expected, |relation| {
        relation.descriptor.g_base -= 1
    })?;
    negatives += 1;
    reject_internal(&closure.expected, |relation| {
        relation.descriptor.g_width -= 1
    })?;
    negatives += 1;
    reject_internal(&closure.expected, |relation| {
        relation.descriptor.g_author[0] ^= 1
    })?;
    negatives += 1;

    let mut high_values = closure.expected.values.clone();
    let high_address = closure.expected.material.occurrences[0].cells[R_BITS - 1].address;
    high_values.insert(high_address, Fr::one());
    let high_rows = residuals(&closure.expected.terms, &high_values)?;
    if high_rows.get(&(R_BITS + G_BITS)) == Some(&Fr::zero()) {
        return Err("c487 R0 high-bit row insensitive".into());
    }
    negatives += 1;

    let mut coordinated = material.clone();
    let cell = &mut coordinated.occurrences[1].cells[0];
    cell.value = Fr::one() - cell.value;
    coordinated.source_x_identity = coordinated.recompute_source_x_identity()?;
    coordinated.validate_basic()?;
    let coordinated_public = TerminalPublic::from_material(&coordinated)?;
    TerminalRelation::new(coordinated.clone(), coordinated_public)?;
    if authenticate(&coordinated).is_ok() {
        return Err("c487 coordinated source-X/AB mutant kept stream authority".into());
    }
    negatives += 1;

    for bytes in [
        {
            let mut bytes = closure.expected.public.encode().to_vec();
            bytes[ABI_BYTES - AB_BYTES] |= 0x80;
            bytes
        },
        closure.expected.public.encode()[1..].to_vec(),
        {
            let mut bytes = vec![0u8];
            bytes.extend_from_slice(&closure.expected.public.encode());
            bytes
        },
        {
            let mut bytes = closure.expected.public.encode().to_vec();
            bytes.push(0);
            bytes
        },
    ] {
        if TerminalPublic::decode(&bytes).is_ok() {
            return Err("c487 malformed public encoding accepted".into());
        }
        negatives += 1;
    }
    let mut cross_material = material.clone();
    let cross_value = BigUint::from(513u16);
    for (bit, cell) in cross_material.occurrences[1].cells.iter_mut().enumerate() {
        cell.value = Fr::from(cross_value.bit(bit as u64) as u64);
    }
    cross_material.source_x_identity = cross_material.recompute_source_x_identity()?;
    cross_material.validate_basic()?;
    let mut cross_endian = TerminalPublic::from_material(&cross_material)?.encode();
    cross_endian[ABI_BYTES - AB_BYTES..].reverse();
    if cross_endian[ABI_BYTES - AB_BYTES] != 1 {
        return Err("c487 cross-endian fixture first byte".into());
    }
    let cross_endian = TerminalPublic::decode(&cross_endian)?;
    if TerminalRelation::new(cross_material, cross_endian).is_ok() {
        return Err("c487 cross-endian AB equality mutant accepted".into());
    }
    negatives += 1;

    let mut late = Transcript::new(TRANSCRIPT_DOMAIN);
    late.try_challenge_scalar(b"c487-before-public")?;
    let before = [late.challenges(), late.raw_queries(), late.bytes_absorbed()];
    if closure.expected.public.bind(&mut late).is_ok()
        || before != [late.challenges(), late.raw_queries(), late.bytes_absorbed()]
    {
        return Err("c487 late public binding mutation".into());
    }
    negatives += 1;

    let replay = closure
        .publish(&mut destination, closure.offer())
        .expect_err("c487 replay accepted");
    if replay != "c487 duplicate publication" {
        return Err("c487 replay error boundary".into());
    }
    negatives += 1;
    Ok((negatives, public_sha256))
}

struct NativeObservation<'a> {
    frame_sha256: &'a str,
    max_owners: usize,
    score_owners: usize,
    score_roles: usize,
}

impl NativeObservation<'_> {
    fn validate(&self) -> Result<(), String> {
        if self.frame_sha256.len() != 64
            || !self
                .frame_sha256
                .bytes()
                .all(|byte| byte.is_ascii_hexdigit())
            || (self.max_owners, self.score_owners, self.score_roles) != (7_683, 7_543, 15_083)
        {
            return Err("c487 observed native evidence census".into());
        }
        Ok(())
    }
}

fn topology_digest(terms: &[Term]) -> Result<[u8; 32], String> {
    let mut bytes = b"nipopow-v2-terminal-topology-v1\0".to_vec();
    for term in terms {
        for value in [term.row, term.gate.left, term.gate.right] {
            bytes.extend_from_slice(
                &u64::try_from(value)
                    .map_err(|_| "c487 topology usize/u64")?
                    .to_be_bytes(),
            );
        }
        for coefficient in [term.gate.c0, term.gate.c1, term.gate.c2, term.gate.c3] {
            coefficient
                .serialize_compressed(&mut bytes)
                .map_err(|error| format!("c487 topology scalar serialization: {error}"))?;
        }
    }
    Ok(ergo_header_core::blake2b256(&bytes))
}

fn scalar_hex(value: &Fr) -> Result<String, String> {
    let mut bytes = Vec::new();
    value
        .serialize_compressed(&mut bytes)
        .map_err(|error| format!("c487 transcript scalar serialization: {error}"))?;
    Ok(hex(&bytes))
}

pub(super) fn run_native<'ctx, 'src, 'max, 'snapshot>(
    stream: &H21ScoreEndpointStream<'ctx, 'src, 'max, 'snapshot>,
    observed_frame_sha: &str,
    max_owners: usize,
    score_owners: usize,
    score_roles: usize,
) -> Result<String, String> {
    let observed = NativeObservation {
        frame_sha256: observed_frame_sha,
        max_owners,
        score_owners,
        score_roles,
    };
    observed.validate()?;
    let source = BorrowedTerminalSource::new(stream)?;
    source.validate()?;
    let (negatives, public_sha256) = exercise(source.material.clone(), |candidate| {
        let fresh = TerminalMaterial::from_stream(source.stream)?;
        if candidate != &fresh {
            return Err("c487 terminal material differs from fresh stream replay".into());
        }
        Ok(())
    })?;
    let relation = Closure::new(source.material.clone())?;
    let topology_sha256 = topology_digest(&relation.expected.terms)?;
    let (transcript_counters, transcript_challenge) = transcript_pair(&relation.expected.public)?;
    Ok(format!(
        "C487_NATIVE_TERMINAL_PUBLIC_PASS frame_sha256={} max_owners={} score_owners={} score_roles={} abi_bytes={ABI_BYTES} terminal_cells={} gap_cells={G_BITS} rows={ROWS} terms={TERMS} negatives={negatives} source_x_identity={} relation_topology_sha256={} public_sha256={} transcript_counters={},{},{} transcript_challenge={} native=true full_eq26=false gap_final_x=false header_zero=false all_owner=false common_x=false gkr=false pcs=false proof=false client=false",
        observed.frame_sha256,
        observed.max_owners,
        observed.score_owners,
        observed.score_roles,
        2 * R_BITS,
        hex(&source.material.source_x_identity),
        hex(&topology_sha256),
        hex(&public_sha256),
        transcript_counters[0],
        transcript_counters[1],
        transcript_counters[2],
        scalar_hex(&transcript_challenge)?,
    ))
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02X}")).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn c487_terminal_public_synthetic_precursor() -> Result<(), String> {
        let total = BigUint::from(1u8) << 200usize;
        let material = TerminalMaterial::synthetic(
            &total - 1u8,
            total.clone(),
            (BigUint::from(1u8) << 224usize) + 9u8,
        )?;
        let original = material.clone();
        let (negatives, _) = exercise(material, |candidate| {
            if candidate != &original {
                return Err("c487 synthetic immutable source mismatch".into());
            }
            Ok(())
        })?;
        let boundary = TerminalMaterial::synthetic(
            total.clone(),
            total,
            (BigUint::from(1u8) << 223usize) + 3u8,
        )?;
        let boundary = Closure::new(boundary)?;
        let mut packed_mutant = boundary.expected.values.clone();
        let low_r = boundary.expected.material.occurrences[0].cells[0].address;
        if packed_mutant.insert(low_r, Fr::one()) != Some(Fr::zero()) {
            return Err("c487 boundary low R bit fixture".into());
        }
        let packed_rows = residuals(&boundary.expected.terms, &packed_mutant)?;
        if packed_rows.get(&0).is_some_and(|value| !value.is_zero())
            || packed_rows
                .get(&(R_BITS + G_BITS + 1))
                .is_none_or(Fr::is_zero)
        {
            return Err("c487 packed boundary +1 mutant did not isolate packed row".into());
        }
        let over = TerminalMaterial::synthetic(
            (BigUint::from(1u8) << 200usize) + 1u8,
            BigUint::from(1u8) << 200usize,
            BigUint::from(7u8),
        )?;
        if Closure::new(over).is_ok() {
            return Err("c487 over-bound precursor accepted".into());
        }
        println!(
            "C487_SYNTHETIC_PRECURSOR_PASS abi_bytes={ABI_BYTES} rows={ROWS} terms={TERMS} negatives={negatives} packed_boundary_mutant=true native_source=false common_x=false gkr=false pcs=false proof=false client=false"
        );
        Ok(())
    }
}

//! Producer-side evaluation of the inactive DAA lane in historical role 4.
use super::*;
use crate::gkr;
use std::sync::Arc;

const BLOCK_BITS: usize = 13;
const BLOCK: usize = 1 << BLOCK_BITS;
const OWNERS: usize = 1 << 21;
const COUNTS: [usize; 2] = [81_920, 73_728];

fn template(class: OwnerClass) -> Option<usize> {
    match class {
        OwnerClass::M1 => Some(1),
        OwnerClass::Short(_) | OwnerClass::Mature(_) => None,
        OwnerClass::Genesis | OwnerClass::Initial | OwnerClass::Carry |
        OwnerClass::FixedV2 | OwnerClass::Singleton | OwnerClass::Padding => Some(0),
    }
}

impl DaaHistoryRoster<'_> {
    pub(super) fn check_h21_zero_scope(&self) -> Result<(), String> {
        if self.headers() != crate::h21_snapshot::N as u64 || self.slot_log() != 21
            || self.input_log() != 41 || self.row_log() != 40 {
            return Err("H21 inactive DAA parent geometry".into());
        }
        Ok(())
    }

    pub(crate) fn h21_zero_logical_count(&self, owner: usize) -> Result<usize, String> {
        self.check_h21_zero_scope()?;
        Ok(template(self.owner_class(owner as u64)?).map_or(0, |i| COUNTS[i]))
    }

    pub(crate) fn h21_zero_logical_total(&self) -> Result<usize, String> {
        self.check_h21_zero_scope()?;
        let layout = census_owners(&self.schedule)?;
        let mut total = 0;
        census_add(&mut total, layout.inactive_full, COUNTS[0])?;
        census_add(&mut total, layout.m1, COUNTS[1])?;
        Ok(total)
    }
}

// Each block has aligned row and wire starts. The M1 complement renumbers
// its ROWs: the ordinal of a block must come from its own canonical circuit.
#[derive(Clone, Copy)]
struct Band { wire: usize, row_weight: Fr }

fn bands(circuit: &Circuit, index: usize, r: &[Fr]) -> Result<Vec<Band>, String> {
    if circuit.input_len != WIDTH || circuit.row_count != ROWS || circuit.terms.len() != COUNTS[index] {
        return Err("H21 inactive DAA template geometry".into());
    }
    let row_high = gkr::eq_weights(&r[BLOCK_BITS..LOCAL_ROW_LOG]);
    let mut result = Vec::new();
    let mut ordinal = 0;
    for (start, end) in BANKS {
        if start % BLOCK != 0 || end % BLOCK != 0 || end > WIDTH {
            return Err("unaligned inactive DAA bank".into());
        }
        for wire in (start..end).step_by(BLOCK) {
            if index == 1 && M1_IMAGE.contains(&wire) { continue; }
            result.push(Band { wire, row_weight: row_high[ordinal / BLOCK] });
            for left in wire..wire+BLOCK {
                let term = circuit.terms.get(ordinal).ok_or("incomplete inactive DAA template")?;
                let gate = &term.gate;
                if term.row != ordinal || gate.left != left || gate.right != 0 ||
                    [gate.c0,gate.c1,gate.c2,gate.c3] != [Fr::zero(),Fr::one(),Fr::zero(),Fr::zero()] {
                    return Err("inactive DAA canonical row or gate differs".into());
                }
                ordinal += 1;
            }
        }
    }
    if ordinal != circuit.terms.len() { return Err("inactive DAA template extent".into()); }
    Ok(result)
}

pub(crate) struct Family<'r,'p> {
    roster: &'r DaaHistoryRoster<'p>,
    bands: [Vec<Band>; 2],
    row_low: [Fr; BLOCK_BITS],
    local_weights: Vec<Fr>,
    owner_weights: Arc<Vec<Fr>>,
    tag: Fr,
}

enum Weights {
    LocalU(Vec<Fr>),
    UpperU([Vec<Fr>; 2]),
    V([Fr; 2]),
}

pub(crate) struct Round {
    k: usize,
    weights: Weights,
    family: Arc<Vec<Fr>>,
}

impl<'r,'p> Family<'r,'p> {
    pub(crate) fn new(roster: &'r DaaHistoryRoster<'p>, r: &[Fr]) -> Result<Self, String> {
        roster.check_h21_zero_scope()?;
        if r.len() != 41 { return Err("H21 role 4 row point width".into()); }
        let zero = bands(&roster.zero_full.circuit, 0, r)?;
        let complement = bands(&roster.zero_m1_complement.circuit, 1, r)?;
        let row_low = r[..BLOCK_BITS].try_into().map_err(|_| "inactive DAA block point")?;
        Ok(Self { roster, bands: [zero, complement], row_low,
            local_weights: gkr::eq_weights(&r[..BLOCK_BITS]),
            owner_weights: Arc::new(gkr::eq_weights(&r[19..40])),
            // Row = 2^40 + owner*2^19 + 3*2^17 + ordinal.
            tag: r[40] * r[18] * r[17] })
    }

    pub(crate) fn logical_count(&self, owner: usize) -> Result<usize, String> {
        self.roster.h21_zero_logical_count(owner)
    }

    pub(crate) fn round(&self, prefix: &[Fr], v: Option<(&[Fr], Fr)>) -> Result<Round, String> {
        let k = prefix.len();
        if k > LOCAL_INPUT_LOG { return Err("inactive DAA local prefix width".into()); }
        let weights = if let Some((u, left_value)) = v {
            if u.len() != WIDTH { return Err("inactive DAA U weight extent".into()); }
            // All right endpoints are local wire zero. Only the V B-bank
            // is nonzero. This common dot product is prepared outside owners.
            let right_zero: Fr = prefix.iter().map(|x| Fr::one()-x).product();
            let sums = self.bands.each_ref().map(|bands| {
                let mut z = Fr::zero();
                for band in bands {
                    let u_band = &u[band.wire..band.wire+BLOCK];
                    let dot: Fr = self.local_weights.iter().zip(u_band).map(|(a,b)| *a*b).sum();
                    z += band.row_weight * dot;
                }
                right_zero * left_value * z
            });
            Weights::V(sums)
        } else {
            // Folding chi_r on a bound low coordinate contributes its two
            // barycentric terms, even when the coordinate is not Boolean.
            let fixed: Fr = self.row_low.iter().zip(prefix).map(|(r,p)|
                (Fr::one()-r)*(Fr::one()-p)+*r*p).product();
            if k < BLOCK_BITS {
                let mut remaining = gkr::eq_weights(&self.row_low[k..]);
                for weight in &mut remaining { *weight *= fixed; }
                Weights::LocalU(remaining)
            } else {
                let high = gkr::eq_weights(&prefix[BLOCK_BITS..]);
                let banks = self.bands.each_ref().map(|bands| {
                    let mut a = vec![Fr::zero(); WIDTH >> k];
                    for band in bands {
                        a[band.wire >> k] += fixed * band.row_weight *
                            high[(band.wire >> BLOCK_BITS) & (high.len()-1)];
                    }
                    a
                });
                Weights::UpperU(banks)
            }
        };
        Ok(Round { k, weights, family: Arc::clone(&self.owner_weights) })
    }
}

fn product_pairs(a: &[Fr], x: &[Fr]) -> [Fr;3] {
    debug_assert!(a.len() == x.len() && a.len() % 2 == 0);
    let mut p = [Fr::zero(); 3];
    for (a,x) in a.chunks_exact(2).zip(x.chunks_exact(2)) {
        let da = a[1]-a[0];
        let dx = x[1]-x[0];
        p[0] += a[0]*x[0];
        p[1] += a[0]*dx + da*x[0];
        p[2] += da*dx;
    }
    p
}

impl Round {
    /// Ordinary monomial coefficients; at the terminal return the two bank
    /// values (A,B,0). The caller already owns X, including for empty banks.
    pub(crate) fn contribution(&self, family: &Family<'_,'_>, owner: usize, x: &[Fr],
        raw: Option<&[u8]>, u_high: Option<&[Fr]>) -> Result<[Fr;3], String> {
        if !Arc::ptr_eq(&self.family,&family.owner_weights) || owner >= OWNERS
            || x.len() != WIDTH >> self.k || raw.is_some_and(|bits| bits.len() != WIDTH/8)
            || u_high.is_some_and(|high| high.len() != OWNERS)
            || (matches!(self.weights, Weights::V(_)) != u_high.is_some())
            || raw.is_some() == u_high.is_some() {
            return Err("inactive DAA round, owner or projection mismatch".into());
        }
        let Some(index) = template(family.roster.owner_class(owner as u64)?) else {
            return Ok([Fr::zero(); 3]);
        };
        let scale = family.tag * family.owner_weights[owner];
        let result = match &self.weights {
            Weights::LocalU(a) => {
                let bits = raw.ok_or("inactive DAA packed owner missing")?;
                let mut p = [Fr::zero(); 3];
                for band in &family.bands[index] {
                    // k<13: every pair stays inside a single aligned block.
                    // X is projected from these same held original bits.
                    if bits[band.wire/8..(band.wire+BLOCK)/8].iter().all(|&b| b == 0) { continue; }
                    let first = band.wire >> self.k;
                    let add = product_pairs(a, &x[first..first+a.len()]);
                    for j in 0..3 { p[j] += band.row_weight * add[j]; }
                }
                p
            }
            Weights::UpperU(a) if self.k == LOCAL_INPUT_LOG => [a[index][0],Fr::zero(),Fr::zero()],
            Weights::UpperU(a) => product_pairs(&a[index],x),
            Weights::V(d) => {
                let b = d[index] * u_high.ok_or("inactive DAA V owner weights missing")?[owner];
                if self.k == LOCAL_INPUT_LOG { [Fr::zero(),b,Fr::zero()] }
                else { [b,-b,Fr::zero()] }
            }
        };
        Ok(result.map(|v| v * scale))
    }
}

/// Component differential called by the historical producer's bounded check.
/// A deterministic bit vector exercises interpolation and spill across banks.
/// The enclosing measurement separately uses real packed N0 owner bytes.
pub(crate) fn check_component(roster: &DaaHistoryRoster<'_>, r: &[Fr]) -> Result<usize,String> {
    let family = Family::new(roster,r)?;
    let cases = [
        (0,Some(0)),(1,Some(0)),(2,Some(0)),(417791,Some(0)),(1024,Some(0)),(2048,Some(1)),
        (3072,None),(4096,None),(5120,None),(6144,None),(7168,None),(8192,None),
        (9216,None),(844672,None),(crate::h21_snapshot::N,Some(0)),
    ];
    for &(owner,kind) in &cases {
        let expected = kind.map_or(0,|i| COUNTS[i]);
        let mut literal = 0;
        let emitted = roster.visit_h21_zero_lane_owner(owner, |t| {
            if t.row != owner*OWNER_ROWS + 3*ROWS + literal || t.gate.left/WIDTH != owner ||
                t.gate.right != owner*WIDTH {
                return Err("inactive DAA relocated canonical lane".into());
            }
            literal += 1;
            Ok(())
        })?;
        if literal != expected || emitted != literal || family.logical_count(owner)? != expected {
            return Err("inactive DAA class differential".into());
        }
    }
    if roster.h21_zero_logical_count(OWNERS).is_ok() || family.round(&[Fr::one();21],None).is_ok() {
        return Err("inactive DAA out-of-domain input accepted".into());
    }

    let mut bits = vec![0u8;WIDTH/8];
    for wire in [0, BANKS[0].0-1, BANKS[0].0, BANKS[0].0+3, BANKS[0].1, M1_IMAGE.start,
        M1_IMAGE.end-1, M1_IMAGE.end, BANKS[3].1-1, WIDTH-1] {
        bits[wire/8] |= 1 << (wire%8);
    }
    let mut x = (0..WIDTH).map(|i| Fr::from(((bits[i/8]>>(i%8))&1) as u64)).collect::<Vec<_>>();
    let p: Vec<_> = (0..20).map(|i| Fr::from(7+3*i as u64)).collect();
    let u: Vec<_> = (0..20).map(|i| Fr::from(11+2*i as u64)).collect();
    let high: Vec<_> = (0..21).map(|i| Fr::from(19+i as u64)).collect();
    let uw = gkr::eq_weights(&u);
    let uh = gkr::eq_weights(&high);
    let lv = Fr::from(29u64);
    let row_weights = gkr::eq_weights(&r[..17]);
    let templates = [&roster.zero_full.circuit,&roster.zero_m1_complement.circuit];
    let mut checks = 0;
    for k in 0..=20 {
        if matches!(k,0|12|13|20) {
            let ru = family.round(&p[..k],None)?;
            let rv = family.round(&p[..k],Some((&uw,lv)))?;
            let pw = gkr::eq_weights(&p[..k]);
            let zero = vec![Fr::zero();x.len()];
            let mut expected = [([Fr::zero();3],[Fr::zero();3]);2];
            for (class,circuit) in templates.iter().enumerate() {
                // Enumerate the original gates and project each wire directly.
                // This oracle uses neither block factorization nor bank skipping.
                let mut a = vec![Fr::zero();x.len()];
                let mut b = vec![Fr::zero();x.len()];
                for term in &circuit.terms {
                    let w = row_weights[term.row];
                    let g = &term.gate;
                    a[g.left>>k] += w*pw[g.left & (pw.len()-1)]*g.c1;
                    b[g.right>>k] += w*pw[g.right & (pw.len()-1)]*uw[g.left]*g.c1*lv;
                }
                let triple = |values: Vec<Fr>| -> Result<[Fr;3],String> {
                    values.try_into().map_err(|_| "inactive DAA oracle degree".into())
                };
                expected[class] = if k==20 {
                    ([a[0],Fr::zero(),Fr::zero()],[Fr::zero(),b[0],Fr::zero()])
                } else {
                    (triple(gkr::quadratic_message(&a,&zero,&x))?,
                     triple(gkr::quadratic_message(&zero,&b,&x))?)
                };
            }
            for &(owner,kind) in &cases {
                let actual_u = ru.contribution(&family,owner,&x,Some(&bits),None)?;
                let actual_v = rv.contribution(&family,owner,&x,None,Some(&uh))?;
                let (eu,ev) = kind.map_or(([Fr::zero();3],[Fr::zero();3]), |i| expected[i]);
                let row = (1u64<<40) + (owner as u64)*(OWNER_ROWS as u64) + (3*ROWS) as u64;
                let common = eq(&r[LOCAL_ROW_LOG..],row>>LOCAL_ROW_LOG);
                let physical_u = eq(&high,owner as u64);
                if actual_u != eu.map(|v| common*v) || actual_v != ev.map(|v| common*physical_u*v) {
                    return Err(format!("inactive DAA differential owner {owner} depth {k}"));
                }
                checks += 2;
            }
        }
        if let Some(challenge) = p.get(k) { gkr::fold(&mut x,*challenge); }
    }
    Ok(checks)
}

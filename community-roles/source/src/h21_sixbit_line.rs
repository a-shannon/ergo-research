//! Six low-coordinate factors for the H21 log41 packed Boolean line.
use super::{packed_line_add, packed_line_capacity, packed_line_fields, packed_line_tail};
use ark_bn254::Fr;
use ark_ff::{One, Zero};

const LOW: usize = 20;
const SPLIT: usize = 6;
const COEFFICIENTS: usize = SPLIT + 1;
const BYTES_PER_TILE: usize = 1 << (SPLIT - 3);
const TILES: usize = 1 << (LOW - SPLIT);
const TABLE_ENTRIES: usize = BYTES_PER_TILE * 256;
pub(super) const LUT_FIELDS: usize = TABLE_ENTRIES * COEFFICIENTS;
pub(super) const WORK_FIELDS: usize = TILES * COEFFICIENTS;

pub(crate) struct Plan {
    table: Vec<[Fr; COEFFICIENTS]>,
    work: Vec<Fr>,
    u_tail: [Fr; LOW - SPLIT],
    delta_tail: [Fr; LOW - SPLIT],
}

impl Plan {
    pub(crate) fn bound() -> Result<usize, String> {
        // Build: eight seven-coefficient basis polynomials, one subset and scalar factors.
        // Apply: one tile accumulator or the two 21-coefficient arrays in packed_line_tail.
        // 128 fields cover either scratch peak. The returned Vec and its 21 fields are separate.
        [std::mem::size_of::<Vec<Fr>>(), packed_line_fields(LUT_FIELDS)?,
         packed_line_fields(WORK_FIELDS)?, packed_line_fields(LOW + 1)?, packed_line_fields(128)?]
            .into_iter().try_fold(std::mem::size_of::<Self>(), packed_line_add)
    }

    pub(crate) fn new(u: &[Fr], v: &[Fr], limit: usize) -> Result<Self, String> {
        if u.len() != LOW || v.len() != LOW || Self::bound()? > limit {
            return Err("H21 six-bit line geometry or reservation".into());
        }
        let mut table = Vec::<[Fr; COEFFICIENTS]>::new();
        table.try_reserve_exact(TABLE_ENTRIES).map_err(|_| "six-bit table allocation")?;
        packed_line_capacity(table.capacity(), TABLE_ENTRIES)?;
        for position in 0..BYTES_PER_TILE {
            // Each Boolean coordinate of the 64-bit tile contributes a degree-six equality
            // polynomial on u+t(v-u). A byte contributes the sum of its selected bit polynomials.
            let mut basis = [[Fr::zero(); COEFFICIENTS]; 8];
            for (bit, poly) in basis.iter_mut().enumerate() {
                poly[0] = Fr::one();
                let slot = position * 8 + bit;
                for i in 0..SPLIT {
                    let (a,b) = if slot & (1 << i) != 0 {
                        (u[i], v[i] - u[i])
                    } else {
                        (Fr::one() - u[i], u[i] - v[i])
                    };
                    for d in (1..=i+1).rev() { poly[d] = a * poly[d] + b * poly[d-1]; }
                    poly[0] *= a;
                }
            }
            let start = table.len();
            table.push([Fr::zero(); COEFFICIENTS]);
            for mask in 1usize..256 {
                let mut sum = table[start + (mask & (mask - 1))];
                let add = &basis[mask.trailing_zeros() as usize];
                for d in 0..COEFFICIENTS { sum[d] += add[d]; }
                table.push(sum);
            }
        }
        let mut work = Vec::new();
        work.try_reserve_exact(WORK_FIELDS).map_err(|_| "six-bit line work allocation")?;
        packed_line_capacity(work.capacity(), WORK_FIELDS)?;
        Ok(Self { table, work, u_tail: std::array::from_fn(|j| u[SPLIT+j]),
                  delta_tail: std::array::from_fn(|j| v[SPLIT+j] - u[SPLIT+j]) })
    }

    pub(crate) fn apply(&mut self, packed: &[u8]) -> Result<Vec<Fr>, String> {
        if packed.len() != (1 << LOW)/8 { return Err("H21 six-bit line row extent".into()); }
        self.work.clear();
        for tile in packed.chunks_exact(BYTES_PER_TILE) {
            let mut sum = self.table[tile[0] as usize];
            for (pos, &byte) in tile.iter().enumerate().skip(1) {
                let add = &self.table[pos * 256 + byte as usize];
                for d in 0..COEFFICIENTS { sum[d] += add[d]; }
            }
            self.work.extend_from_slice(&sum);
        }
        let mut entries = TILES;
        for i in SPLIT..LOW {
            packed_line_tail(&mut self.work, entries, i, self.u_tail[i-SPLIT], self.delta_tail[i-SPLIT], false)?;
            entries /= 2;
        }
        if entries != 1 || self.work.len() != LOW+1 { return Err("H21 six-bit line coefficient extent".into()); }
        let result = self.work.to_vec();
        packed_line_capacity(result.capacity(), LOW+1)?;
        Ok(result)
    }

    pub(super) fn capacities(&self) -> (usize,usize) {
        (self.table.capacity()*COEFFICIENTS, self.work.capacity())
    }

    pub(super) fn accumulate_edge_owner(&mut self,input: &mut impl super::EdgeInput, owner:usize,
        u_high:&[Fr],v_high:&[Fr],line:&mut [Fr],fast:&mut super::PackedLineStats,
        stats:&mut super::EdgeFullStats)->Result<(),String>{
        let row=input.header_bits(owner)?;
        let start=std::time::Instant::now();
        let local=self.apply(row)?;
        let elapsed=super::EdgeFullStats::ns(start)?;
        super::accumulate_local_line(local,elapsed,LOW,owner,u_high,v_high,line,fast,stats)
    }
}

pub(super) fn selected_edge(
    admission:Option<&super::h21_packed_line::Admission>, input:&mut impl super::EdgeInput,
    u:&[Fr],v:&[Fr],owners:impl IntoIterator<Item=usize>,fast:Option<&mut super::PackedLineStats>,
    stats:&mut super::EdgeFullStats,observe:&mut impl FnMut(super::EdgeFullEvent)->Result<(),String>,
)->Result<Option<Vec<Fr>>,String>{
    if !admission.is_some_and(super::h21_packed_line::Admission::sixbit) { return Ok(None); }
    let fast=fast.ok_or("missing H21 line statistics")?;
    use super::EdgeFullStats;
    use std::time::Instant;
    const OWNERS: usize = 1 << 21;
    if input.width() != 1 << LOW || input.owners() != OWNERS || u.len() != 41 || v.len() != 41
        || fast.plan_reserved_bytes != Plan::bound()? {
        return Err("H21 six-bit edge line input or allocation".into());
    }
    let mut line=vec![Fr::zero();42];
    let build = Instant::now();
    let mut plan = Plan::new(&u[..LOW], &v[..LOW], fast.plan_reserved_bytes)?;
    fast.build_ns = EdgeFullStats::ns(build)?;
    fast.builds = 1;
    (fast.lut_fields, fast.work_fields) = plan.capacities();
    fast.plan_actual_bytes = Plan::bound()?;
    for owner in owners {
        if owner >= OWNERS { return Err("H21 line owner index".into()); }
        plan.accumulate_edge_owner(input,owner,&u[LOW..],&v[LOW..],&mut line,fast,stats)?;
        if (owner+1) % 1024 == 0 {
            super::full_mark(observe,"line",b'p',0,owner+1,0)?;
        }
    }
    Ok(Some(line))
}

pub(super) fn report(role:usize,owners:usize) {
    println!("N0_SIXBIT_LINE_APPLIED {}",serde_json::json!({"role":role,"split_bits":SPLIT,
        "owners":owners,"local_coefficients":owners*(LOW+1),"global_coefficients":42,"plan_builds":1}));
}

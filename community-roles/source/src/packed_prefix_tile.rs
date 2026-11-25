//! Fold original packed Boolean input at a fixed low-coordinate prefix.
//! Each table includes all eight bit weights and up to seven byte-index
//! coordinates. The remaining coordinates multiply a sum once per tile.
use ark_bn254::Fr;
use ark_ff::{One, Zero};

pub(crate) struct PackedPrefixTile {
    rows: Vec<[Fr; 256]>,
    outer: Vec<Fr>,
    group_bytes: usize,
}

impl PackedPrefixTile {
    pub(crate) fn new(prefix: &[Fr]) -> Result<Self, String> {
        if !(4..=20).contains(&prefix.len()) { return Err("packed tile prefix outside 4..20".into()); }
        let split = prefix.len().min(10);
        let low = crate::gkr::eq_weights(&prefix[..3]);
        let mid = crate::gkr::eq_weights(&prefix[3..split]);
        let outer = crate::gkr::eq_weights(&prefix[split..]);
        let mut rows = Vec::new();
        rows.try_reserve_exact(mid.len()).map_err(|_| "packed tile table allocation")?;
        for scale in mid {
            let weights: [Fr; 8] = std::array::from_fn(|bit| low[bit] * scale);
            let mut values = [Fr::zero(); 256];
            for mask in 1usize..256 {
                values[mask] = values[mask & (mask - 1)] + weights[mask.trailing_zeros() as usize];
            }
            rows.push(values);
        }
        let group_bytes = 1usize << (prefix.len() - 3);
        if rows.len() * outer.len() != group_bytes { return Err("packed tile factorization".into()); }
        Ok(Self { rows, outer, group_bytes })
    }

    fn tile_sum(&self, bytes: &[u8]) -> Fr {
        let mut sum = Fr::zero();
        for (&value, row) in bytes.iter().zip(&self.rows) {
            if value != 0 { sum += row[value as usize]; }
        }
        sum
    }

    pub(crate) fn project(&self, bytes: &[u8]) -> Result<Vec<Fr>, String> {
        if bytes.is_empty() || bytes.len() % self.group_bytes != 0 {
            return Err("packed tile input extent".into());
        }
        let count = bytes.len() / self.group_bytes;
        let mut result = Vec::new();
        result.try_reserve_exact(count).map_err(|_| "packed tile result allocation")?;
        for group in bytes.chunks_exact(self.group_bytes) {
            let mut value = Fr::zero();
            if self.outer.len() == 1 {
                value = self.tile_sum(group);
            } else {
                for (chunk, weight) in group.chunks_exact(self.rows.len()).zip(&self.outer) {
                    let partial = self.tile_sum(chunk);
                    if !partial.is_zero() { value += partial * weight; }
                }
            }
            result.push(value);
        }
        Ok(result)
    }

    pub(crate) fn retained_bytes(&self) -> usize {
        self.rows.capacity() * std::mem::size_of::<[Fr; 256]>() +
            self.outer.capacity() * std::mem::size_of::<Fr>()
    }
}

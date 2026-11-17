//! Bounded whole field function. This representation does not authenticate a commitment.
use ark_bn254::Fr;
use ark_ff::{One, Zero};

pub(crate) const MAX_EXTENT: usize = 16384;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Witness {
    extent: usize,
    dimensions: usize,
    declared_cap: usize,
    entries: Box<[(usize, Fr)]>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct FoldWork {
    pub entry_visits: usize,
    pub weight_factors: usize,
    pub aggregation_capacity: usize,
    pub retained_entries: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct LineWork {
    pub entry_visits: usize,
    pub coefficient_updates: usize,
    pub output_scalars: usize,
    pub scratch_scalars: usize,
}

fn dimensions(extent: usize) -> Result<usize, String> {
    if extent == 0 || extent > MAX_EXTENT || !extent.is_power_of_two() {
        return Err("whole witness extent".into());
    }
    Ok(extent.trailing_zeros() as usize)
}

impl Witness {
    pub fn new(extent: usize, declared_cap: usize, entries: Vec<(usize, Fr)>) -> Result<Self, String> {
        let dimensions = dimensions(extent)?;
        if declared_cap > extent { return Err("whole witness declared cap".into()); }
        if entries.capacity() > extent { return Err("whole witness incoming capacity".into()); }
        if entries.len() > declared_cap { return Err("whole witness entry count".into()); }
        let mut previous = None;
        for (index, value) in &entries {
            if *index >= extent { return Err("whole witness index".into()); }
            if value.is_zero() { return Err("whole witness explicit zero".into()); }
            if let Some(old) = previous {
                if *index == old { return Err("whole witness duplicate".into()); }
                if *index < old { return Err("whole witness disorder".into()); }
            }
            previous = Some(*index);
        }
        // into_boxed_slice removes spare logical capacity. During normalization,
        // the bounded caller allocation and a K-entry replacement may coexist.
        Ok(Self { extent, dimensions, declared_cap, entries: entries.into_boxed_slice() })
    }

    pub fn with_admitted<R>(extent: usize, declared_cap: usize, entries: Vec<(usize, Fr)>,
        consumer: impl FnOnce(&Self) -> R) -> Result<R, String> {
        let witness = Self::new(extent, declared_cap, entries)?;
        Ok(consumer(&witness))
    }

    /// Setup/reference conversion only; operations below never use this adapter.
    pub fn from_dense(values: &[Fr], declared_cap: usize) -> Result<Self, String> {
        dimensions(values.len())?;
        if declared_cap > values.len() { return Err("whole witness declared cap".into()); }
        let mut entries = Vec::with_capacity(values.len());
        for (index, value) in values.iter().enumerate() {
            if !value.is_zero() { entries.push((index, *value)); }
        }
        Self::new(values.len(), declared_cap, entries)
    }

    pub fn extent(&self) -> usize { self.extent }
    pub fn dimensions(&self) -> usize { self.dimensions }
    pub fn declared_cap(&self) -> usize { self.declared_cap }
    pub fn entries(&self) -> &[(usize, Fr)] { &self.entries }
    pub fn retained_capacity(&self) -> usize { self.entries.len() }

    pub fn value(&self, index: usize) -> Result<Fr, String> {
        if index >= self.extent { return Err("whole witness query index".into()); }
        Ok(match self.entries.binary_search_by_key(&index, |entry| entry.0) {
            Ok(position) => self.entries[position].1,
            Err(_) => Fr::zero(),
        })
    }

    pub fn query_with<R>(&self, index: usize, consumer: impl FnOnce(Fr) -> R) -> Result<R, String> {
        Ok(consumer(self.value(index)?))
    }

    pub fn fold(&self, prefix: &[Fr]) -> Result<Self, String> {
        Ok(self.fold_counted(prefix)?.0)
    }

    pub fn fold_counted(&self, prefix: &[Fr]) -> Result<(Self, FoldWork), String> {
        if prefix.len() > self.dimensions { return Err("whole witness prefix dimensions".into()); }
        let mut out = Vec::with_capacity(self.entries.len());
        let aggregation_capacity = out.capacity();
        let mut group = None;
        let mut sum = Fr::zero();
        for (index, value) in self.entries.iter() {
            let remaining = index >> prefix.len();
            if group != Some(remaining) {
                if let Some(old) = group { if !sum.is_zero() { out.push((old, sum)); } }
                group = Some(remaining);
                sum = Fr::zero();
            }
            let mut weighted = *value;
            for (bit, coordinate) in prefix.iter().enumerate() {
                weighted *= if index >> bit & 1 == 1 { *coordinate } else { Fr::one() - coordinate };
            }
            sum += weighted;
        }
        if let Some(old) = group { if !sum.is_zero() { out.push((old, sum)); } }
        let extent = self.extent >> prefix.len();
        let retained_entries = out.len();
        // Internally bounded scratch can exceed the reduced extent in capacity.
        // Normalize first, then recheck every canonical invariant through new.
        // Box -> Vec -> Box transfers exact K capacity without a trusted flag.
        let normalized = out.into_boxed_slice().into_vec();
        let result = Self::new(extent, self.declared_cap.min(extent), normalized)?;
        let work = FoldWork { entry_visits: self.entries.len(),
            weight_factors: self.entries.len() * prefix.len(), aggregation_capacity, retained_entries };
        Ok((result, work))
    }

    pub fn mle(&self, point: &[Fr]) -> Result<Fr, String> {
        if point.len() != self.dimensions { return Err("whole witness point dimensions".into()); }
        self.fold(point)?.value(0)
    }

    pub fn line(&self, u: &[Fr], v: &[Fr]) -> Result<Vec<Fr>, String> {
        Ok(self.line_counted(u, v)?.0)
    }

    pub fn line_counted(&self, u: &[Fr], v: &[Fr]) -> Result<(Vec<Fr>, LineWork), String> {
        if u.len() != self.dimensions || v.len() != self.dimensions {
            return Err("whole witness line dimensions".into());
        }
        let mut output = vec![Fr::zero(); self.dimensions + 1];
        let mut polynomial = vec![Fr::zero(); self.dimensions + 1];
        let mut coefficient_updates = 0;
        for (index, value) in self.entries.iter() {
            polynomial.fill(Fr::zero());
            polynomial[0] = *value;
            for bit in 0..self.dimensions {
                let (constant, slope) = if index >> bit & 1 == 1 {
                    (u[bit], v[bit] - u[bit])
                } else { (Fr::one() - u[bit], u[bit] - v[bit]) };
                for degree in (0..=bit+1).rev() {
                    let old = if degree <= bit { polynomial[degree] } else { Fr::zero() };
                    let lower = if degree == 0 { Fr::zero() } else { polynomial[degree-1] };
                    polynomial[degree] = constant * old + slope * lower;
                    coefficient_updates += 1;
                }
            }
            for (sum, coefficient) in output.iter_mut().zip(&polynomial) { *sum += coefficient; }
        }
        let work = LineWork { entry_visits: self.entries.len(), coefficient_updates,
            output_scalars: output.len(), scratch_scalars: polynomial.len() };
        Ok((output, work))
    }
}

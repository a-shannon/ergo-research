//! Bounded source-owned candidate schedule for the conditional global U envelope.
//! This does not authenticate its supplied native D or Map values.
use num_bigint::BigUint;

pub(crate) const K0: usize = 64;
pub(crate) const H21_MAX: u64 = 1 << 21;
pub(crate) const INITIAL_I: u64 = 1_199_990_374_400;
pub(crate) const RESET_CHILD_417792: u64 = 122_702_199_259_136;
pub(crate) const RESET_CHILD_417793: u64 = 122_702_199_259_136;
const LEGACY_CAP: u64 = 843_776;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CandidateSource {
    HeaderDifficulty { height: u64, work_owner: u64 },
    LegacyBound { q: u64, endpoint: u64, map_owner: u64, ell: usize },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SuppliedCandidate {
    pub source: CandidateSource,
    pub value: BigUint,
}

#[derive(Clone, Debug)]
pub(crate) struct Schedule {
    n: u64,
    legacy_q_max: u64,
}

impl Schedule {
    pub(crate) fn new(n: u64) -> Result<Self, String> {
        if !(2..=H21_MAX).contains(&n) {
            return Err("global-U cut outside fixed H21 domain".into());
        }
        let endpoint_limit = n.saturating_add(K0 as u64).min(LEGACY_CAP);
        let legacy_q_max = endpoint_limit / 1024;
        let legacy_q_max = legacy_q_max.saturating_sub(1);
        Ok(Self { n, legacy_q_max })
    }

    pub(crate) fn iter(&self) -> ScheduleIter {
        ScheduleIter { schedule: self.clone(), next_header: 2, next_q: 1, headers_done: false }
    }

    pub(crate) fn legacy_items(&self) -> LegacyIter {
        LegacyIter { next_q: 1, q_max: self.legacy_q_max }
    }
}

pub(crate) struct ScheduleIter {
    schedule: Schedule,
    next_header: u64,
    next_q: u64,
    headers_done: bool,
}

impl Iterator for ScheduleIter {
    type Item = CandidateSource;

    fn next(&mut self) -> Option<Self::Item> {
        if !self.headers_done {
            if self.next_header <= self.schedule.n {
                let height = self.next_header;
                self.next_header += 1;
                return Some(CandidateSource::HeaderDifficulty { height, work_owner: height - 2 });
            }
            self.headers_done = true;
        }
        while self.next_q <= self.schedule.legacy_q_max {
            let q = self.next_q;
            self.next_q += 1;
            if q == 407 { continue; }
            let endpoint = 1024 * (q + 1);
            return Some(CandidateSource::LegacyBound {
                q, endpoint, map_owner: q * 1024 + 959, ell: q.min(8) as usize,
            });
        }
        None
    }
}

pub(crate) struct LegacyIter { next_q: u64, q_max: u64 }

impl Iterator for LegacyIter {
    type Item = CandidateSource;

    fn next(&mut self) -> Option<Self::Item> {
        while self.next_q <= self.q_max {
            let q = self.next_q;
            self.next_q += 1;
            if q == 407 { continue; }
            return Some(CandidateSource::LegacyBound {
                q, endpoint: 1024 * (q + 1), map_owner: q * 1024 + 959,
                ell: q.min(8) as usize,
            });
        }
        None
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct GlobalEnvelope {
    pub n: u64,
    pub max_difficulty: BigUint,
    pub modern_floor: BigUint,
    pub maximum_candidate: BigUint,
    pub exponent: usize,
    pub u: BigUint,
    pub header_count: u64,
    pub legacy_count: u64,
}

pub(crate) fn fold(
    n: u64,
    candidates: impl IntoIterator<Item = SuppliedCandidate>,
) -> Result<GlobalEnvelope, String> {
    let schedule = Schedule::new(n)?;
    let mut supplied = candidates.into_iter();
    let initial = BigUint::from(INITIAL_I);
    // q=0 is this literal I; it is never requested from a historical Map owner.
    let mut max_difficulty = initial.clone();
    let mut maximum_candidate = initial.clone();
    maximum_candidate = maximum_candidate.max(BigUint::from(RESET_CHILD_417792));
    maximum_candidate = maximum_candidate.max(BigUint::from(RESET_CHILD_417793));
    let mut header_count = 0u64;
    let mut legacy_count = 0u64;

    for expected in schedule.iter() {
        let item = supplied.next().ok_or("global-U candidate sequence missing item")?;
        if item.source != expected {
            return Err("global-U candidate id/owner/order mismatch".into());
        }
        match expected {
            CandidateSource::HeaderDifficulty { height, .. } => {
                if item.value == BigUint::from(0u8) { return Err("zero header difficulty".into()); }
                if (height == 417_792 || height == 417_793)
                    && item.value != BigUint::from(RESET_CHILD_417792) {
                    return Err("global-U reset child difficulty mismatch".into());
                }
                max_difficulty = max_difficulty.max(item.value.clone());
                maximum_candidate = maximum_candidate.max(item.value);
                header_count += 1;
            }
            CandidateSource::LegacyBound { .. } => {
                if item.value < initial { return Err("global-U legacy bound below initial".into()); }
                maximum_candidate = maximum_candidate.max(item.value);
                legacy_count += 1;
            }
        }
    }
    if supplied.next().is_some() { return Err("global-U candidate sequence has extra item".into()); }

    let modern_floor = (&max_difficulty * 3u8) / 2u8;
    maximum_candidate = maximum_candidate.max(modern_floor.clone());
    let ceiling = BigUint::from(1u8) << 64usize;
    if maximum_candidate > ceiling { return Err("global-U final envelope exceeds 2^64".into()); }
    let exponent = (0..=64).find(|e| (BigUint::from(1u8) << e) >= maximum_candidate)
        .ok_or("global-U dyadic exponent exceeds 64")?;
    let u = BigUint::from(1u8) << exponent;
    Ok(GlobalEnvelope { n, max_difficulty, modern_floor, maximum_candidate,
        exponent, u, header_count, legacy_count })
}

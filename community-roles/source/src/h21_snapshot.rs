//! Sealed retained-history bootstrap profiles. Each binary admits exactly one
//! pair of history and query heights. The verifier selects it before decoding.
#[cfg(feature = "h21-snapshot-n0")]
pub(crate) const N: usize = 1_819_648;
#[cfg(not(feature = "h21-snapshot-n0"))]
pub(crate) const N: usize = 1_827_840;

#[cfg(feature = "h21-snapshot-n0")]
pub(crate) const H: usize = 1_804_171;
#[cfg(not(feature = "h21-snapshot-n0"))]
pub(crate) const H: usize = 1_810_842;

pub(crate) const F: usize = H + 64 - 1;
pub(crate) const GUARDS: [usize; 2] = [F, H];
pub(crate) const CLIPPED_OWNERS: [usize; 2] = [F - 1, H - 1];
// Origin 845760 forms a singleton, followed by 128-height epochs.
const MODERN_START: usize = 845_760;
const fn spans(guard: usize) -> usize {
    1 + (guard - MODERN_START).div_ceil(128)
}
pub(crate) const SCORE_SPANS: [usize; 2] = [spans(F), spans(H)];
// Both cut termini fall strictly inside distinct epochs in the two profiles.
pub(crate) const SCORE_OWNERS: usize = SCORE_SPANS[0] + 1;
const _: () = assert!((F - MODERN_START) % 128 != 0
    && (H - MODERN_START) % 128 != 0 && spans(F) == spans(H) + 1);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bank53_map::{CutDescriptor, CutProfile, MaturityMode};

    #[test]
    fn retained_calendar_admits_only_the_compiled_snapshot() {
        let modes = [MaturityMode::Sampled, MaturityMode::Exact];
        let cut = CutDescriptor::eligible08();
        let (n, h, f, counts, owners, other_n, other_h) = if cfg!(feature = "h21-snapshot-n0") {
            (1_819_648, 1_804_171, 1_804_234, [7_490, 7_489], 7_491, 1_827_840, 1_810_842)
        } else {
            (1_827_840, 1_810_842, 1_810_905, [7_542, 7_541], 7_543, 1_819_648, 1_804_171)
        };
        assert_eq!(cut.terminals(), [n, h]);
        assert_eq!(cut.guards(), [f, h]);
        assert_eq!((SCORE_SPANS, SCORE_OWNERS), (counts, owners));
        assert!(CutDescriptor::checked(CutProfile::Eligible08, other_n, other_h, other_h + 63, 1024, 64, modes).is_err());
        assert!(CutDescriptor::checked(CutProfile::Eligible08, n, h, f + 1, 1024, 64, modes).is_err());
    }
}

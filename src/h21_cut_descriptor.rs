//! Fixed draft-0.8 cut identities shared by source producers and diagnostics.
//! The identity binds a local source plan; it is not a PCS or proof commitment.

const FIRST: usize = 844_672;
const LAST: usize = 1_827_840;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CutProfile { Diagnostic08, Eligible08 }

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MaturityMode { Sampled, Exact }

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct CutDescriptor {
    profile: CutProfile,
    n: usize,
    h: usize,
    f: usize,
    l: usize,
    k0: usize,
    modes: [MaturityMode; 2],
}

impl CutDescriptor {
    pub(crate) fn diagnostic08() -> Self {
        Self::checked(CutProfile::Diagnostic08, LAST, 1_827_775, 1_827_838,
            1024, 64, [MaturityMode::Sampled, MaturityMode::Exact]).expect("fixed diagnostic cuts")
    }

    pub(crate) fn eligible08() -> Self {
        Self::checked(CutProfile::Eligible08, LAST, 1_810_842, 1_810_905,
            1024, 64, [MaturityMode::Sampled, MaturityMode::Exact]).expect("fixed eligible cuts")
    }

    pub(crate) fn checked(profile: CutProfile, n: usize, h: usize, f: usize,
        l: usize, k0: usize, modes: [MaturityMode; 2]) -> Result<Self, String> {
        let fixed = match profile {
            CutProfile::Diagnostic08 => (1_827_775, 1_827_838),
            CutProfile::Eligible08 => (1_810_842, 1_810_905),
        };
        if n != LAST || (h, f) != fixed || l != 1024 || k0 != 64
            || modes != [MaturityMode::Sampled, MaturityMode::Exact]
            || h.checked_add(k0 - 1) != Some(f)
            || h.checked_add(k0).filter(|v| *v <= n).is_none() {
            return Err("scheduled cut descriptor/profile geometry".into());
        }
        Ok(Self { profile, n, h, f, l, k0, modes })
    }

    pub(crate) fn terminals(self) -> [usize; 2] { [self.n, self.h] }
    pub(crate) fn guards(self) -> [usize; 2] { [self.f, self.h] }
    pub(crate) fn modern_start(self) -> usize { FIRST + self.offset() }
    pub(crate) fn offset(self) -> usize { self.l + self.k0 }

    /// The fixed Eq. 19 maturity for one origin of this exact cut profile.
    pub(crate) fn maturity_value(self, context: usize, origin: usize) -> Result<u64, String> {
        let mode = *self.modes.get(context).ok_or("cut maturity context")?;
        if origin == 0 || origin > self.guards()[context] {
            return Err("cut maturity origin outside guard".into());
        }
        let zone = if origin < 417_792 { 0 } else if origin < 845_760 { 1 } else { 2 };
        Ok(match mode {
            MaturityMode::Sampled => [43_410, 23_155, 4_995][zone],
            MaturityMode::Exact => [17_867, 9_548, 2_090][zone],
        })
    }

    #[cfg(test)]
    pub(crate) fn modes(self) -> [MaturityMode; 2] { self.modes }

    #[cfg(test)]
    pub(crate) fn maturity_mode(self, context: usize) -> Result<crate::origin_score_map::Mode, String> {
        match self.modes.get(context) {
            Some(MaturityMode::Sampled) => Ok(crate::origin_score_map::Mode::Sampled),
            Some(MaturityMode::Exact) => Ok(crate::origin_score_map::Mode::Exact),
            None => Err("scheduled cut descriptor maturity context".into()),
        }
    }

    pub(crate) fn canonical_identity(self) -> Vec<u8> {
        let mut out = b"nipopow-cut-descriptor-08-v1\0".to_vec();
        out.push(match self.profile { CutProfile::Diagnostic08 => 0, CutProfile::Eligible08 => 1 });
        for value in [self.n, self.h, self.f, self.l, self.k0] {
            out.extend_from_slice(&u64::try_from(value).expect("validated fixed cut fits U64").to_be_bytes());
        }
        for mode in self.modes {
            out.push(match mode { MaturityMode::Sampled => 0, MaturityMode::Exact => 1 });
        }
        out
    }
}

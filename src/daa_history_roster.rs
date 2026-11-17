//! Fixed native DAA composition over the work-tree history coordinates.
//! Global authentication and common GKR/PCS consumption remain separate.
use crate::{
    daa_finish::CompiledFinish,
    daa_header_window::{self, Action, SelectedWindow},
    daa_integer::Epoch,
    daa_one_ratio_finish::CompiledOne,
    daa_schedule_wiring::{evaluate_mature_shift, ScheduleDomain},
    daa_work_actions::DaaWorkActions,
    gkr::Gate,
    mapped_daa_plan::MappedDaaPlan,
    mapped_one_daa::MappedM1,
    one_daa_layout::OneDaaLayout,
    short_daa_layout::{Profile, ShortDaaLayout},
    sparse::{self, Circuit, Shape, Term},
    transcript::Transcript,
    wiring::RightIndex,
    work_tree_history_plan::WorkTreeHistoryPlan,
    work_tree_layout,
};
use ark_bn254::Fr;
use ark_ff::{One, Zero};

pub(crate) const LOCAL_INPUT_LOG: usize = 20;
pub(crate) const LOCAL_ROW_LOG: usize = 17;
pub(crate) const SLOT_ROW_LOG: usize = 19;
pub(crate) const WIDTH: usize = 1 << LOCAL_INPUT_LOG;
const ROWS: usize = 1 << LOCAL_ROW_LOG;
const OWNER_ROWS: usize = 1 << SLOT_ROW_LOG;
pub(crate) const BANKS: [(usize, usize); 4] = [
    (663_552, 671_744),
    (688_128, 720_896),
    (819_200, 851_968),
    (991_232, 999_424),
];
const M1_IMAGE: std::ops::Range<usize> = 819_200..827_392;
const A4_ROWS: std::ops::Range<usize> = 348_440..356_632;
const A4_WIRES: std::ops::Range<usize> = 991_232..999_424;
const SHORTS: [Profile; 6] = [
    Profile::M2,
    Profile::M3,
    Profile::M4,
    Profile::M5,
    Profile::M6,
    Profile::M7,
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum OwnerClass {
    Genesis,
    Initial,
    Carry,
    FixedV2,
    Singleton,
    M1,
    Short(Profile),
    Mature(Epoch),
    Padding,
}
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct Counts {
    pub(crate) lanes: [usize; 4],
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct HistoryEndpointCounts {
    pub(crate) candidates: usize,
    pub(crate) alias_sources: usize,
    pub(crate) alias_occurrences: usize,
    pub(crate) lanes: [usize; 4],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct CensusOwners {
    carry: u64,
    fixed: u64,
    singleton: u64,
    m1: u64,
    shorts: [u64; 6],
    mature: [u64; 2],
    padding: u64,
    inactive_full: u64,
}

fn census_sum(values: impl IntoIterator<Item = u64>) -> Result<u64, String> {
    values.into_iter().try_fold(0u64, |a, b| {
        a.checked_add(b).ok_or_else(|| "DAA census sum overflow".to_owned())
    })
}

fn census_owners(schedule: &ScheduleDomain) -> Result<CensusOwners, String> {
    let n = schedule.upper_bound();
    let h = schedule.slot_log();
    if n < 3 || !(2..=21).contains(&h) {
        return Err("DAA census history domain rejected".into());
    }
    let slots = 1u64.checked_shl(u32::try_from(h).map_err(|_| "DAA census shift")?)
        .ok_or("DAA census slot overflow")?;
    if n > slots { return Err("DAA census history exceeds slots".into()); }
    let legacy = daa_header_window::MAINNET_LEGACY_EPOCH_LENGTH;
    let singleton = u64::from(legacy < n);
    let m1_owner = legacy.checked_mul(2).ok_or("DAA census M1 owner overflow")?;
    let m1 = u64::from(m1_owner < n);
    let mut shorts = [0u64; 6];
    for (i, profile) in SHORTS.into_iter().enumerate() {
        let child = u64::try_from(profile.child_height()).map_err(|_| "DAA census short width")?;
        let owner = child.checked_sub(1).ok_or("DAA census short owner")?;
        shorts[i] = u64::from(owner < n);
    }
    let fixed = daa_header_window::V2_RESET_CHILDREN.into_iter().try_fold(0u64, |a, child| {
        let owner = u64::from(child).checked_sub(1).ok_or("DAA census reset owner")?;
        a.checked_add(u64::from(owner < n)).ok_or("DAA census reset count")
    })?;
    // H<=21 bounds the existing clipped progression arithmetic far below u64 overflow.
    let mature = [
        schedule.mature_retarget_count(Epoch::Legacy),
        schedule.mature_retarget_count(Epoch::Eip),
    ];
    let retargets = census_sum([m1, census_sum(shorts)?, census_sum(mature)?])?;
    let equal = n.checked_sub(2).and_then(|v| v.checked_sub(fixed))
        .and_then(|v| v.checked_sub(retargets)).ok_or("DAA census active partition")?;
    let carry = equal.checked_sub(singleton).ok_or("DAA census singleton partition")?;
    let padding = slots.checked_sub(n).ok_or("DAA census padding partition")?;
    let inactive_full = slots.checked_sub(retargets).ok_or("DAA census inactive partition")?;
    if census_sum([1, 1, carry, fixed, singleton, m1, census_sum(shorts)?, census_sum(mature)?, padding])? != slots
        || census_sum([1, 1, carry, fixed, singleton, padding])? != inactive_full
    {
        return Err("DAA census class partition mismatch".into());
    }
    Ok(CensusOwners { carry, fixed, singleton, m1, shorts, mature, padding, inactive_full })
}

fn census_add(out: &mut usize, copies: u64, unit: usize) -> Result<(), String> {
    let copies = usize::try_from(copies).map_err(|_| "DAA census count width")?;
    *out = copies.checked_mul(unit).and_then(|v| out.checked_add(v))
        .ok_or("DAA census lane overflow")?;
    Ok(())
}

fn census_occurrences(
    visit: impl FnOnce(&mut dyn FnMut(Term) -> Result<(), String>) -> Result<usize, String>,
) -> Result<usize, String> {
    let mut count = 0usize;
    let reported = visit(&mut |_| {
        count = count.checked_add(1).ok_or("DAA census occurrence overflow")?;
        Ok(())
    })?;
    if reported != count { return Err("DAA census emitter count mismatch".into()); }
    Ok(count)
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct HeaderCounts {
    pub(crate) emitted: usize,
    pub(crate) omitted_worktree: usize,
    pub(crate) omitted_mature_a4: usize,
    pub(crate) omitted_short_a4: usize,
}

struct LocalRelation {
    circuit: Circuit,
    shape: Shape,
    fingerprint: String,
}
impl LocalRelation {
    fn new(circuit: Circuit) -> Result<Self, String> {
        let shape = sparse::validate(&circuit, 0)
            .map_err(|e| format!("roster local relation rejected: {e:?}"))?;
        let fingerprint = work_tree_layout::hash_terms(&circuit.terms);
        Ok(Self {
            circuit,
            shape,
            fingerprint,
        })
    }
    fn coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
        sparse::wiring(&self.circuit, &self.shape, r, u, v)
            .map_err(|e| format!("roster local wiring rejected: {e:?}"))
    }
}

/// Neither the lane roster nor its native owner masks are caller supplied.
pub(crate) struct DaaHistoryRoster<'a> {
    parent: &'a WorkTreeHistoryPlan,
    schedule: ScheduleDomain,
    numeric: DaaWorkActions<'a>,
    one: Option<OneDaaLayout>,
    shorts: Vec<(Profile, ShortDaaLayout)>,
    zero_full: LocalRelation,
    zero_m1_complement: LocalRelation,
    a4: LocalRelation,
    mature_bindings: [(String, String); 2],
}

impl<'a> DaaHistoryRoster<'a> {
    /// Canonical lane1 source; shared by the inverse and bounded independent
    /// target-selection fixtures. It never emits arithmetic to discard it.
    pub(crate) fn visit_history_alias_source(&self, owner: usize,
        mut sink: impl FnMut(Term) -> Result<(), String>) -> Result<usize, String> {
        let class = self.owner_class(owner as u64)?;
        let low = if class == OwnerClass::M1 { 8 } else { 10 };
        let mut alias = |mut term: Term| {
            if term.row >> low != owner { return Err("history alias source row".into()); }
            term.row = owner.checked_mul(OWNER_ROWS).and_then(|b| b.checked_add(ROWS))
                .and_then(|b| b.checked_add(term.row & ((1 << low) - 1)))
                .ok_or("history alias lane row")?;
            sink(term)
        };
        match class {
            OwnerClass::M1 => self.one.as_ref().ok_or("history M1 alias absent")?.visit_alias_terms(&mut alias),
            OwnerClass::Short(profile) => self.short(profile)?.visit_alias_terms(&mut alias),
            OwnerClass::Mature(epoch) => self.parent.header_boundary().mature_layout(epoch)
                .visit_alias_terms(owner as u64, &mut alias),
            _ => Ok(0),
        }
    }

    pub(crate) fn visit_history_alias_endpoint_terms(&self, left: bool, slot: usize,
        mut sink: impl FnMut(Term) -> Result<(), String>) -> Result<HistoryEndpointCounts, String> {
        let slots = 1usize.checked_shl(self.slot_log() as u32).ok_or("history alias slots")?;
        if slot >= slots { return Err("history DAA endpoint owner".into()); }
        // 2*(d0 + nine backward offsets) + seven early targets. No owner graph.
        let mut targets = [0usize; 27];
        let mut len = 0usize;
        let mut add = |target: usize| -> Result<(), String> {
            if target < self.headers() as usize && target < slots {
                if len == targets.len() { return Err("history alias candidate bound".into()); }
                targets[len] = target; len += 1;
            }
            Ok(())
        };
        if left {
            for epoch in [Epoch::Legacy, Epoch::Eip] {
                add(slot)?;
                for back in 0usize..=8 {
                    let delta = back.checked_mul(epoch.length() as usize).and_then(|v| v.checked_add(1))
                        .ok_or("history alias offset overflow")?;
                    if let Some(target) = slot.checked_add(delta) { add(target)?; }
                }
            }
            for target in [2048usize,3072,4096,5120,6144,7168,8192] { add(target)?; }
        } else { add(slot)?; }
        let mut counts = HistoryEndpointCounts { candidates: len, ..Default::default() };
        targets[..len].sort_unstable();
        let mut previous = None;
        for &owner in &targets[..len] {
            if previous == Some(owner) { continue; } previous = Some(owner);
            if !matches!(self.owner_class(owner as u64)?, OwnerClass::M1 | OwnerClass::Short(_) | OwnerClass::Mature(_)) { continue; }
            counts.alias_sources = counts.alias_sources.checked_add(1).ok_or("history alias source count")?;
            let before = counts.alias_occurrences;
            let reported = self.visit_history_alias_source(owner, |term| {
                counts.alias_occurrences = counts.alias_occurrences.checked_add(1).ok_or("history alias occurrence count")?;
                let endpoint = if left { term.gate.left } else { term.gate.right };
                if endpoint / WIDTH == slot {
                    sink(term)?;
                    counts.lanes[1] = counts.lanes[1].checked_add(1).ok_or("history alias emitted count")?;
                }
                Ok(())
            })?;
            if reported == 0 || reported != counts.alias_occurrences - before {
                return Err("history alias reported source count".into());
            }
        }
        Ok(counts)
    }

    pub(crate) fn visit_history_endpoint_terms(&self, left: bool, slot: usize,
        mut sink: impl FnMut(Term) -> Result<(), String>) -> Result<HistoryEndpointCounts, String> {
        let slots = 1usize.checked_shl(self.slot_log() as u32).ok_or("history DAA slots")?;
        if slot >= slots { return Err("history DAA endpoint owner".into()); }
        let class = self.owner_class(slot as u64)?;
        let mut local_counts = [0usize; 4];
        // Both endpoints of these two lanes are local, including dummy wire0.
        for lane in [0usize, 3] {
            let circuit = match (lane, class) {
                (0, OwnerClass::M1) => Some(self.one.as_ref().ok_or("history M1 local absent")?.mapped_relation()),
                (0, OwnerClass::Short(profile)) => Some(self.short(profile)?.mapped_relation()),
                (0, OwnerClass::Mature(epoch)) => Some(self.parent.header_boundary().mature_layout(epoch).mapped_relation()),
                (3, OwnerClass::M1) => Some(&self.zero_m1_complement.circuit),
                (3, OwnerClass::Short(_) | OwnerClass::Mature(_)) => None,
                (3, _) => Some(&self.zero_full.circuit),
                _ => None,
            };
            if let Some(circuit) = circuit {
                for term in &circuit.terms {
                    let mut gate = term.gate.clone();
                    let base = slot.checked_mul(WIDTH).ok_or("history DAA local input base")?;
                    if gate.left >= WIDTH || gate.right >= WIDTH || term.row >= ROWS {
                        return Err("history DAA local source geometry".into());
                    }
                    gate.left = base.checked_add(gate.left).ok_or("history DAA left overflow")?;
                    gate.right = base.checked_add(gate.right).ok_or("history DAA right overflow")?;
                    let row = slot.checked_mul(OWNER_ROWS).and_then(|b| b.checked_add(lane * ROWS))
                        .and_then(|b| b.checked_add(term.row)).ok_or("history DAA local row")?;
                    sink(Term { row, gate })?;
                    local_counts[lane] = local_counts[lane].checked_add(1).ok_or("history DAA local count")?;
                }
            }
        }
        let mut counts = self.visit_history_alias_endpoint_terms(left, slot, &mut sink)?;
        self.numeric.visit_endpoint_terms(left, slot, |mut term| {
            term.row = term.row.checked_mul(OWNER_ROWS).and_then(|b| b.checked_add(2 * ROWS))
                .ok_or("history DAA numeric row")?;
            sink(term)?;
            counts.lanes[2] = counts.lanes[2].checked_add(1).ok_or("history DAA numeric count")?;
            Ok(())
        })?;
        counts.lanes[0] = local_counts[0]; counts.lanes[3] = local_counts[3];
        Ok(counts)
    }

    pub(crate) fn endpoint_parent(&self)->&WorkTreeHistoryPlan {self.parent}

    #[cfg(test)]
    pub(crate) fn named_m1_alias_endpoints(&self)->Result<crate::one_daa_layout::M1AliasEndpointIndex<'_>,String> {
        if self.headers()!=3073 || self.slot_log()!=12 || self.owner_class(2048)!=Ok(OwnerClass::M1) {
            return Err("DAA named M1 alias scope rejected".into());
        }
        self.one.as_ref().ok_or("DAA M1 layout absent")?.m1_endpoint_index()
    }

    #[cfg(test)]
    pub(crate) fn named_m1_alias_coefficients(&self,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String> {
        if self.headers()!=3073 || self.slot_log()!=12 || r.len()!=32 || u.len()!=32 || v.len()!=32 {
            return Err("DAA named M1 coefficient scope rejected".into());
        }
        let mut projected=r[..8].to_vec();projected.extend_from_slice(&r[19..31]);
        let factor=r[31]*r[17]*(Fr::one()-r[18])
            *r[8..17].iter().fold(Fr::one(),|a,x|a*(Fr::one()-x));
        Ok(self.one.as_ref().ok_or("DAA M1 layout absent")?.alias_coefficients(&projected,u,v)?.map(|x|factor*x))
    }

    #[cfg(test)]
    pub(crate) fn named_m2_alias_endpoints(&self)->Result<crate::short_daa_layout::M2AliasEndpointIndex<'_>,String> {
        if self.headers()!=3073 || self.slot_log()!=12 || self.owner_class(3072)!=Ok(OwnerClass::Short(Profile::M2)) {
            return Err("DAA named M2 alias scope rejected".into());
        }
        self.short(Profile::M2)?.m2_endpoint_index()
    }

    #[cfg(test)]
    pub(crate) fn named_m2_alias_coefficients(&self,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String> {
        if self.headers()!=3073 || self.slot_log()!=12 || r.len()!=32 || u.len()!=32 || v.len()!=32 {
            return Err("DAA named M2 coefficient scope rejected".into());
        }
        let mut projected=r[..10].to_vec();projected.extend_from_slice(&r[19..31]);
        let factor=r[31]*r[17]*(Fr::one()-r[18])
            *r[10..17].iter().fold(Fr::one(),|a,x|a*(Fr::one()-x));
        Ok(self.short(Profile::M2)?.alias_coefficients(&projected,u,v)?.map(|x|factor*x))
    }

    #[cfg(test)]
    pub(crate) fn visit_complete_s2_endpoint_terms(&self,left:bool,slot:usize,
        mut sink:impl FnMut(Term)->Result<(),String>)->Result<usize,String> {
        if self.headers()!=3 || self.slot_log()!=2 || slot>=4 {
            return Err("DAA endpoint complete S2 scope rejected".into());
        }
        let mut count=0usize;
        self.numeric.visit_endpoint_terms(left,slot,|mut t| {
            let owner=t.row;
            t.row=owner.checked_mul(OWNER_ROWS).and_then(|b|b.checked_add(2*ROWS)).ok_or("DAA endpoint numeric row overflow")?;
            sink(t)?;count+=1;Ok(())
        })?;
        // Exactly the S2 inactive lane. Both endpoints are native-owner local.
        for t in &self.zero_full.circuit.terms {
            let mut gate=t.gate.clone();let base=slot*WIDTH;
            gate.left+=base;gate.right+=base;
            let row=slot*OWNER_ROWS+3*ROWS+t.row;
            sink(Term{row,gate})?;count+=1;
        }
        Ok(count)
    }

    #[cfg(test)]
    pub(crate) fn s12_m2_arithmetic_terms(&self)->Result<usize,String> {
        if self.headers()!=3073 || self.slot_log()!=12 {
            return Err("DAA S12 arithmetic count scope rejected".into());
        }
        Ok(self.short(Profile::M2)?.mapped_relation().terms.len())
    }

    #[cfg(test)]
    pub(crate) fn visit_s12_local_endpoint_terms(&self,slot:usize,lane:usize,
        mut sink:impl FnMut(Term)->Result<(),String>)->Result<usize,String> {
        if self.headers()!=3073 || self.slot_log()!=12 || slot>=4096 || !matches!(lane,0|3) {
            return Err("DAA S12 local endpoint scope rejected".into());
        }
        let class=self.owner_class(slot as u64)?;
        let circuit=match (lane,class) {
            (0,OwnerClass::M1)=>Some(self.one.as_ref().ok_or("DAA S12 M1 absent")?.mapped_relation()),
            (0,OwnerClass::Short(Profile::M2))=>Some(self.short(Profile::M2)?.mapped_relation()),
            (0,_)=>None,
            (3,OwnerClass::M1)=>Some(&self.zero_m1_complement.circuit),
            (3,OwnerClass::Short(Profile::M2))=>None,
            (3,_)=>Some(&self.zero_full.circuit),
            _=>unreachable!(),
        };
        let mut count=0;
        if let Some(circuit)=circuit {
            for t in &circuit.terms {
                let mut gate=t.gate.clone();
                gate.left+=slot*WIDTH;gate.right+=slot*WIDTH;
                if gate.left/WIDTH!=slot || gate.right/WIDTH!=slot {
                    return Err("DAA S12 local endpoint escaped owner".into());
                }
                sink(Term{row:slot*OWNER_ROWS+lane*ROWS+t.row,gate})?;count+=1;
            }
        }
        Ok(count)
    }

    #[cfg(test)]
    pub(crate) fn visit_s12_numeric_endpoint_terms(&self,left:bool,slot:usize,
        mut sink:impl FnMut(Term)->Result<(),String>)->Result<usize,String> {
        if self.headers()!=3073 || self.slot_log()!=12 || slot>=4096 {
            return Err("DAA S12 numeric endpoint scope rejected".into());
        }
        self.numeric.visit_endpoint_terms(left,slot,|mut t| {
            t.row=t.row.checked_mul(OWNER_ROWS).and_then(|r|r.checked_add(2*ROWS))
                .ok_or("DAA S12 numeric row overflow")?;
            sink(t)
        })
    }

    pub(crate) fn compile(parent: &'a WorkTreeHistoryPlan) -> Result<Self, String> {
        let n = parent.headers();
        let s = parent.slot_log();
        if n < 3
            || s > 21
            || parent.slots() != 1usize << s
            || parent.header_boundary().history_slots() != n
            || parent.header_boundary().slot_log() != s
        {
            return Err("DAA roster parent geometry mismatch".into());
        }
        let schedule = ScheduleDomain::new(n, s)?;
        let numeric = DaaWorkActions::new(parent)?;
        if numeric.row_log() != s || numeric.input_log() != LOCAL_INPUT_LOG + s {
            return Err("DAA roster numeric geometry mismatch".into());
        }
        let a4 = LocalRelation::new(canonical_a4(parent)?)?;
        let mut mature_bindings = [
            (String::new(), String::new()),
            (String::new(), String::new()),
        ];
        for (i, epoch) in [Epoch::Legacy, Epoch::Eip].into_iter().enumerate() {
            let layout = parent.header_boundary().mature_layout(epoch);
            let circuit = layout.mapped_relation();
            if layout.epoch() != epoch
                || layout.import_count() != 896
                || circuit.input_len != WIDTH
                || circuit.row_count != ROWS
                || layout.a4_anchor_rows() != A4_ROWS
            {
                return Err("DAA roster mature template geometry mismatch".into());
            }
            let mut aliases = Vec::new();
            let first = if epoch == Epoch::Legacy { 9216 } else { 844672 };
            if schedule.contains_mature_retarget(first) == Some(epoch) {
                layout.visit_alias_terms(first, |t| {
                    aliases.push(t);
                    Ok(())
                })?;
                if aliases.len() != 896 {
                    return Err("DAA roster mature import census mismatch".into());
                }
            }
            mature_bindings[i] = (
                work_tree_layout::hash_terms(&circuit.terms),
                work_tree_layout::hash_terms(&aliases),
            );
        }
        let one = if n >= 2049 {
            Some(OneDaaLayout::compile(n, s)?)
        } else {
            None
        };
        let mut shorts = Vec::new();
        for profile in SHORTS {
            if profile.child_height() as u64 <= n {
                shorts.push((profile, ShortDaaLayout::compile(profile, n, s)?));
            }
        }
        let zero_full = LocalRelation::new(zero_template(false)?)?;
        let zero_m1_complement = LocalRelation::new(zero_template(true)?)?;
        Ok(Self {
            parent,
            schedule,
            numeric,
            one,
            shorts,
            zero_full,
            zero_m1_complement,
            a4,
            mature_bindings,
        })
    }
    pub(crate) fn headers(&self) -> u64 {
        self.parent.headers()
    }
    pub(crate) fn slot_log(&self) -> usize {
        self.parent.slot_log()
    }
    pub(crate) fn input_log(&self) -> usize {
        LOCAL_INPUT_LOG + self.slot_log()
    }
    pub(crate) fn row_log(&self) -> usize {
        SLOT_ROW_LOG + self.slot_log()
    }

    pub(crate) fn owner_class(&self, slot: u64) -> Result<OwnerClass, String> {
        if slot >= 1u64 << self.slot_log() {
            return Err("DAA roster owner outside slot domain".into());
        }
        if slot >= self.headers() {
            return Ok(OwnerClass::Padding);
        }
        if slot == 0 {
            return Ok(OwnerClass::Genesis);
        }
        if slot == 1 {
            return Ok(OwnerClass::Initial);
        }
        let child = u32::try_from(slot + 1).map_err(|_| "DAA roster child width overflow")?;
        let native = daa_header_window::for_child_height(child)?;
        Ok(match native.action() {
            Action::Carry => OwnerClass::Carry,
            Action::FixedV2 => OwnerClass::FixedV2,
            Action::Retarget(epoch) => match native.sample_heights().len() {
                1 if slot == 1024 => OwnerClass::Singleton,
                2 if slot == 2048 => OwnerClass::M1,
                3..=8 => {
                    let profile = SHORTS
                        .into_iter()
                        .find(|p| p.child_height() as u64 == slot + 1)
                        .ok_or("DAA roster short owner does not match native schedule")?;
                    OwnerClass::Short(profile)
                }
                9 if self.schedule.contains_mature_retarget(slot) == Some(epoch) => {
                    OwnerClass::Mature(epoch)
                }
                _ => return Err("DAA roster retarget branch unsupported".into()),
            },
        })
    }

    pub(crate) fn admit_one(&self, compiled: &CompiledOne) -> Result<MappedM1, String> {
        self.one
            .as_ref()
            .ok_or("DAA roster M1 absent from history")?
            .admit(compiled)
    }
    pub(crate) fn admit_short(
        &self,
        profile: Profile,
        compiled: &CompiledFinish,
    ) -> Result<MappedDaaPlan, String> {
        self.short(profile)?.admit(compiled)
    }
    pub(crate) fn admit_mature(
        &self,
        selected: &SelectedWindow,
        compiled: &CompiledFinish,
    ) -> Result<MappedDaaPlan, String> {
        let slot = selected
            .child_height()
            .checked_sub(1)
            .ok_or("DAA roster mature child underflow")? as u64;
        let epoch = match self.owner_class(slot)? {
            OwnerClass::Mature(epoch) => epoch,
            _ => return Err("DAA roster selected child is not mature".into()),
        };
        self.parent
            .header_boundary()
            .mature_layout(epoch)
            .admit_selected(selected, compiled)
    }
    fn short(&self, profile: Profile) -> Result<&ShortDaaLayout, String> {
        self.shorts
            .iter()
            .find(|(p, _)| *p == profile)
            .map(|(_, l)| l)
            .ok_or_else(|| "DAA roster short profile absent from history".into())
    }

    /// Raw occurrences from the same immutable schedule and local templates.
    /// Work is bounded by fixed classes, never by the history's owner count.
    pub(crate) fn term_census(&self) -> Result<Counts, String> {
        let owners = census_owners(&self.schedule)?;
        if self.schedule.upper_bound() != self.headers()
            || self.schedule.slot_log() != self.slot_log()
            || self.numeric.row_log() != self.slot_log()
            || self.numeric.input_log() != self.input_log()
            || self.one.is_some() != (owners.m1 == 1)
            || self.shorts.len() != usize::try_from(census_sum(owners.shorts)?)
                .map_err(|_| "DAA census short count width")?
        {
            return Err("DAA census owned geometry mismatch".into());
        }
        let constant = census_occurrences(|sink| self.numeric.visit_owner(1, sink))?;
        let equal = census_occurrences(|sink| self.numeric.visit_owner(2, sink))?;
        if constant.checked_sub(1).and_then(|v| v.checked_mul(2)) != Some(equal) {
            return Err("DAA census numeric units mismatch".into());
        }
        let mut counts = Counts::default();
        census_add(&mut counts.lanes[2], census_sum([1, owners.fixed])?, constant)?;
        census_add(&mut counts.lanes[2], census_sum([owners.carry, owners.singleton])?, equal)?;
        census_add(&mut counts.lanes[3], owners.inactive_full, self.zero_full.circuit.terms.len())?;
        census_add(&mut counts.lanes[3], owners.m1, self.zero_m1_complement.circuit.terms.len())?;
        if let Some(one) = &self.one {
            let owner = daa_header_window::MAINNET_LEGACY_EPOCH_LENGTH
                .checked_mul(2).ok_or("DAA census M1 owner overflow")?;
            if self.owner_class(owner)? != OwnerClass::M1 {
                return Err("DAA census M1 class mismatch".into());
            }
            census_add(&mut counts.lanes[0], owners.m1, one.mapped_relation().terms.len())?;
            let aliases = census_occurrences(|sink| one.visit_alias_terms(sink))?;
            census_add(&mut counts.lanes[1], owners.m1, aliases)?;
        }
        for (profile, copies) in SHORTS.into_iter().zip(owners.shorts) {
            if copies == 0 { continue; }
            let owner = u64::try_from(profile.child_height()).map_err(|_| "DAA census short owner width")?
                .checked_sub(1).ok_or("DAA census short owner underflow")?;
            if self.owner_class(owner)? != OwnerClass::Short(profile) {
                return Err("DAA census short class mismatch".into());
            }
            let short = self.short(profile)?;
            census_add(&mut counts.lanes[0], copies, short.mapped_relation().terms.len())?;
            let aliases = census_occurrences(|sink| short.visit_alias_terms(sink))?;
            census_add(&mut counts.lanes[1], copies, aliases)?;
        }
        for (epoch, copies) in [Epoch::Legacy, Epoch::Eip].into_iter().zip(owners.mature) {
            let mature = self.parent.header_boundary().mature_layout(epoch);
            if mature.epoch() != epoch { return Err("DAA census mature epoch mismatch".into()); }
            census_add(&mut counts.lanes[0], copies, mature.mapped_relation().terms.len())?;
            census_add(&mut counts.lanes[1], copies, mature.import_count())?;
        }
        counts.lanes.iter().try_fold(0usize, |a, b| {
            a.checked_add(*b).ok_or("DAA census total overflow")
        })?;
        Ok(counts)
    }

    /// Emits the complete fixed relation for one owner, never a caller subset.
    pub(crate) fn visit_owner_terms(
        &self,
        slot: u64,
        mut sink: impl FnMut(Term) -> Result<(), String>,
    ) -> Result<Counts, String> {
        let class = self.owner_class(slot)?;
        let owner = usize::try_from(slot).map_err(|_| "DAA roster owner width overflow")?;
        let base = owner
            .checked_mul(WIDTH)
            .ok_or("DAA roster input base overflow")?;
        let mut counts = Counts::default();
        let mut emit = |lane: usize, local_row: usize, gate: Gate| {
            if lane >= 4 || local_row >= ROWS {
                return Err("DAA roster lane row outside profile".into());
            }
            let row = owner
                .checked_mul(OWNER_ROWS)
                .and_then(|b| b.checked_add(lane * ROWS + local_row))
                .ok_or("DAA roster tagged row overflow")?;
            if row >= 1usize << self.row_log()
                || gate.left >= 1usize << self.input_log()
                || gate.right >= 1usize << self.input_log()
            {
                return Err("DAA roster global term outside profile".into());
            }
            sink(Term { row, gate })?;
            counts.lanes[lane] += 1;
            Ok(())
        };
        let arithmetic = match class {
            OwnerClass::M1 => Some(
                self.one
                    .as_ref()
                    .ok_or("DAA roster M1 template missing")?
                    .mapped_relation(),
            ),
            OwnerClass::Short(p) => Some(self.short(p)?.mapped_relation()),
            OwnerClass::Mature(e) => Some(
                self.parent
                    .header_boundary()
                    .mature_layout(e)
                    .mapped_relation(),
            ),
            _ => None,
        };
        if let Some(circuit) = arithmetic {
            for t in &circuit.terms {
                let mut g = t.gate.clone();
                g.left = base
                    .checked_add(g.left)
                    .ok_or("DAA roster arithmetic left overflow")?;
                g.right = base
                    .checked_add(g.right)
                    .ok_or("DAA roster arithmetic right overflow")?;
                emit(0, t.row, g)?;
            }
        }
        let mut alias = |t: Term, low: usize| {
            if t.row >> low != owner {
                return Err("DAA roster alias owner mismatch".into());
            }
            emit(1, t.row & ((1 << low) - 1), t.gate)
        };
        match class {
            OwnerClass::M1 => {
                self.one
                    .as_ref()
                    .ok_or("DAA roster M1 template missing")?
                    .visit_alias_terms(|t| alias(t, 8))?;
            }
            OwnerClass::Short(p) => {
                self.short(p)?.visit_alias_terms(|t| alias(t, 10))?;
            }
            OwnerClass::Mature(e) => {
                self.parent
                    .header_boundary()
                    .mature_layout(e)
                    .visit_alias_terms(slot, |t| alias(t, 10))?;
            }
            _ => (),
        }
        self.numeric.visit_owner(owner, |t| {
            if t.row != owner {
                return Err("DAA roster numeric row owner mismatch".into());
            }
            emit(2, 0, t.gate)
        })?;
        let inactive = match class {
            OwnerClass::Short(_) | OwnerClass::Mature(_) => None,
            OwnerClass::M1 => Some(&self.zero_m1_complement.circuit),
            _ => Some(&self.zero_full.circuit),
        };
        if let Some(circuit) = inactive {
            for t in &circuit.terms {
                let mut gate = t.gate.clone();
                gate.left += base;
                gate.right += base;
                emit(3, t.row, gate)?;
            }
        }
        Ok(counts)
    }

    pub(crate) fn coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
        if r.len() != self.row_log() || u.len() != self.input_log() || v.len() != self.input_log() {
            return Err("DAA roster coefficient point dimensions rejected".into());
        }
        let mut out = [Fr::zero(); 4];
        let project = |low: usize| {
            let mut p = r[..low].to_vec();
            p.extend_from_slice(&r[SLOT_ROW_LOG..]);
            p
        };
        let weight = |low: usize, tag: usize| {
            eq(&r[low..LOCAL_ROW_LOG], 0) * eq(&r[LOCAL_ROW_LOG..SLOT_ROW_LOG], tag as u64)
        };
        if let Some(one) = &self.one {
            accumulate(
                &mut out,
                one.arithmetic_coefficients(&project(14), u, v)?,
                weight(14, 0),
            );
            accumulate(
                &mut out,
                one.alias_coefficients(&project(8), u, v)?,
                weight(8, 1),
            );
        }
        for (_, short) in &self.shorts {
            accumulate(
                &mut out,
                short.arithmetic_coefficients(&project(17), u, v)?,
                weight(17, 0),
            );
            accumulate(
                &mut out,
                short.alias_coefficients(&project(10), u, v)?,
                weight(10, 1),
            );
        }
        for epoch in [Epoch::Legacy, Epoch::Eip] {
            let mature = self.parent.header_boundary().mature_layout(epoch);
            accumulate(
                &mut out,
                mature.arithmetic_coefficients(&project(17), u, v)?,
                weight(17, 0),
            );
            accumulate(
                &mut out,
                mature.alias_coefficients(&project(10), u, v)?,
                weight(10, 1),
            );
        }
        accumulate(
            &mut out,
            self.numeric.coefficients(&r[SLOT_ROW_LOG..], u, v)?,
            weight(0, 2),
        );
        let (full, complement) = self.inactive_weights(
            &r[SLOT_ROW_LOG..],
            &u[LOCAL_INPUT_LOG..],
            &v[LOCAL_INPUT_LOG..],
        )?;
        accumulate(
            &mut out,
            self.zero_full.coefficients(
                &r[..LOCAL_ROW_LOG],
                &u[..LOCAL_INPUT_LOG],
                &v[..LOCAL_INPUT_LOG],
            )?,
            weight(17, 3) * full,
        );
        accumulate(
            &mut out,
            self.zero_m1_complement.coefficients(
                &r[..LOCAL_ROW_LOG],
                &u[..LOCAL_INPUT_LOG],
                &v[..LOCAL_INPUT_LOG],
            )?,
            weight(17, 3) * complement,
        );
        Ok(out)
    }

    fn inactive_weights(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<(Fr, Fr), String> {
        let mut full = joint_diagonal(r, u, v)?;
        for epoch in [Epoch::Legacy, Epoch::Eip] {
            full -= evaluate_mature_shift(epoch, &self.schedule, r, u, v, 0, RightIndex::SameRow)?;
        }
        for (profile, _) in &self.shorts {
            full -= owner_delta(r, u, v, (profile.child_height() - 1) as u64);
        }
        let m1 = if self.one.is_some() {
            owner_delta(r, u, v, 2048)
        } else {
            Fr::zero()
        };
        Ok((full - m1, m1))
    }

    /// Retains the parent's work-tree retirement and adds only short A4 release.
    pub(crate) fn visit_header_terms(
        &self,
        slot: u64,
        mut sink: impl FnMut(Term) -> Result<(), String>,
    ) -> Result<HeaderCounts, String> {
        let release = matches!(self.owner_class(slot)?, OwnerClass::Short(_));
        let base = usize::try_from(slot)
            .ok()
            .and_then(|s| s.checked_mul(OWNER_ROWS))
            .ok_or("DAA roster header row base overflow")?;
        let input_base = usize::try_from(slot)
            .ok()
            .and_then(|s| s.checked_mul(WIDTH))
            .ok_or("DAA roster header input base overflow")?;
        let mut removed = 0usize;
        let counts = self.parent.visit_slot_terms(slot, |t| {
            let local = t
                .row
                .checked_sub(base)
                .ok_or("DAA roster header row precedes owner")?;
            if release && A4_ROWS.contains(&local) {
                validate_a4_identity(&t, base, input_base, removed)?;
                removed += 1;
                Ok(())
            } else {
                sink(t)
            }
        })?;
        if removed != if release { 8192 } else { 0 } || (release && counts.omitted_a4 != 0) {
            return Err("DAA roster short A4 release census mismatch".into());
        }
        Ok(HeaderCounts {
            emitted: counts
                .emitted
                .checked_sub(removed)
                .ok_or("DAA roster header count underflow")?,
            omitted_worktree: counts.omitted_worktree,
            omitted_mature_a4: counts.omitted_a4,
            omitted_short_a4: removed,
        })
    }
    /// Read-only tail of the canonical HEADER relation. The boundary constructor
    /// pins the full fingerprint, validates every endpoint and verifies row
    /// ordering; its immutable borrow makes the two partition searches sound
    /// without another full-template scan in a coefficient callback.
    pub(crate) fn canonical_header_tail(&self) -> Result<&[Term], String> {
        const FINGERPRINT: &str =
            "580f92b15945029ea82a9f1e0b97cfc9917df940380211a8fd6701e39336ab76";
        let boundary = self.parent.header_boundary();
        let source = boundary.canonical_circuit();
        if boundary.fingerprint() != FINGERPRINT
            || boundary.history_slots() != self.headers()
            || boundary.slot_log() != self.slot_log()
            || source.input_len != WIDTH
            || source.row_count != OWNER_ROWS
            || source.terms.len() != 474_755
            || source.terms.last().map(|t| t.row) != Some(406_405)
        {
            return Err("canonical HEADER tail source descriptor rejected".into());
        }
        let start = source.terms.partition_point(|t| t.row < 393_216);
        let end = source.terms.partition_point(|t| t.row < 406_406);
        let tail = &source.terms[start..end];
        if tail.len() != 13_960
            || tail.first().map(|t| t.row) != Some(393_216)
            || tail.last().map(|t| t.row) != Some(406_405)
        {
            return Err("canonical HEADER tail count or row extent rejected".into());
        }
        Ok(tail)
    }

    pub(crate) fn header_coefficients(
        &self,
        r: &[Fr],
        u: &[Fr],
        v: &[Fr],
    ) -> Result<[Fr; 4], String> {
        if r.len() != SLOT_ROW_LOG + self.slot_log()
            || u.len() != self.input_log()
            || v.len() != self.input_log()
        {
            return Err("DAA roster header point dimensions rejected".into());
        }
        let mut out = self.parent.coefficients(r, u, v)?;
        let local = self.a4.coefficients(
            &r[..SLOT_ROW_LOG],
            &u[..LOCAL_INPUT_LOG],
            &v[..LOCAL_INPUT_LOG],
        )?;
        let mask: Fr = self
            .shorts
            .iter()
            .map(|(p, _)| {
                owner_delta(
                    &r[SLOT_ROW_LOG..],
                    &u[LOCAL_INPUT_LOG..],
                    &v[LOCAL_INPUT_LOG..],
                    (p.child_height() - 1) as u64,
                )
            })
            .sum();
        accumulate(&mut out, local, -mask);
        Ok(out)
    }

    pub(crate) fn bind(&self, transcript: &mut Transcript) {
        transcript.append_bytes(b"daa-history-roster", b"native-four-lanes-shared-union-v1");
        self.numeric.bind(transcript); // Includes the complete parent binding.
        for value in [
            self.headers(),
            self.slot_log() as u64,
            self.input_log() as u64,
            self.row_log() as u64,
            LOCAL_ROW_LOG as u64,
            SLOT_ROW_LOG as u64,
            4,
            81920,
            73728,
        ] {
            transcript.append_u64(b"daa-roster-dimension", value);
        }
        for (tag, name) in [
            b"arithmetic".as_slice(),
            b"aliases",
            b"numeric",
            b"inactive",
        ]
        .into_iter()
        .enumerate()
        {
            transcript.append_u64(b"daa-roster-lane-tag", tag as u64);
            transcript.append_bytes(b"daa-roster-lane", name);
        }
        for (start, end) in BANKS {
            transcript.append_u64(b"daa-roster-bank-start", start as u64);
            transcript.append_u64(b"daa-roster-bank-end", end as u64);
        }
        transcript.append_bytes(
            b"daa-roster-inactive-full",
            self.zero_full.fingerprint.as_bytes(),
        );
        transcript.append_bytes(
            b"daa-roster-inactive-m1-complement",
            self.zero_m1_complement.fingerprint.as_bytes(),
        );
        transcript.append_bytes(b"daa-roster-inactive-right", b"owner-local-input0-v1");
        transcript.append_bytes(b"daa-roster-short-release", self.a4.fingerprint.as_bytes());
        transcript.append_bytes(
            b"daa-roster-header-rule",
            b"parent-retirement-plus-m2-m7-a4-only-v1",
        );
        transcript.append_u64(b"daa-roster-m1-present", self.one.is_some() as u64);
        if let Some(one) = &self.one {
            one.bind(transcript);
        }
        transcript.append_u64(b"daa-roster-short-count", self.shorts.len() as u64);
        for (profile, short) in &self.shorts {
            transcript.append_u64(b"daa-roster-short-child", profile.child_height() as u64);
            short.bind(transcript);
        }
        for (i, epoch) in [Epoch::Legacy, Epoch::Eip].into_iter().enumerate() {
            transcript.append_u64(b"daa-roster-mature-period", epoch.length());
            transcript.append_u64(
                b"daa-roster-mature-count",
                self.schedule.mature_retarget_count(epoch),
            );
            transcript.append_bytes(
                b"daa-roster-mature-map",
                self.mature_bindings[i].0.as_bytes(),
            );
            transcript.append_bytes(
                b"daa-roster-mature-imports",
                self.mature_bindings[i].1.as_bytes(),
            );
        }
    }
}

fn accumulate(out: &mut [Fr; 4], value: [Fr; 4], weight: Fr) {
    for (o, x) in out.iter_mut().zip(value) {
        *o += x * weight;
    }
}
fn eq(point: &[Fr], index: u64) -> Fr {
    point.iter().enumerate().fold(Fr::one(), |a, (b, x)| {
        a * if index >> b & 1 == 1 {
            *x
        } else {
            Fr::one() - x
        }
    })
}
fn owner_delta(r: &[Fr], u: &[Fr], v: &[Fr], owner: u64) -> Fr {
    eq(r, owner) * eq(u, owner) * eq(v, owner)
}
fn joint_diagonal(r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<Fr, String> {
    if r.len() != u.len() || r.len() != v.len() {
        return Err("DAA roster joint mask dimensions rejected".into());
    }
    Ok(r.iter().zip(u).zip(v).fold(Fr::one(), |a, ((r, u), v)| {
        a * ((Fr::one() - r) * (Fr::one() - u) * (Fr::one() - v) + *r * *u * *v)
    }))
}
fn zero_template(complement: bool) -> Result<Circuit, String> {
    let mut terms = Vec::new();
    for (start, end) in BANKS {
        for wire in start..end {
            if complement && M1_IMAGE.contains(&wire) {
                continue;
            }
            terms.push(Term {
                row: terms.len(),
                gate: Gate {
                    left: wire,
                    right: 0,
                    c0: Fr::zero(),
                    c1: Fr::one(),
                    c2: Fr::zero(),
                    c3: Fr::zero(),
                },
            });
        }
    }
    if terms.len() != if complement { 73728 } else { 81920 } {
        return Err("DAA roster zero union census changed".into());
    }
    Ok(Circuit {
        input_len: WIDTH,
        row_count: ROWS,
        terms,
    })
}

#[cfg(test)]
pub(crate) struct DaaGroupedVContextForTest<'r, 'p> {
    roster: &'r DaaHistoryRoster<'p>,
    parent_object: usize,
    r: [Fr; 32],
    u: [Fr; 32],
    left_value: Fr,
    z_full: Fr,
    z_m1: Fr,
    r_owner_weights: Vec<Fr>,
    u_owner_weights: Vec<Fr>,
    full_count: usize,
    m1_count: usize,
    template_visits: usize,
}

#[cfg(test)]
fn grouped_v_eq_weight(point: &[Fr], index: usize) -> Result<Fr, String> {
    if point.len() >= usize::BITS as usize
        || index >= 1usize.checked_shl(point.len() as u32).ok_or("grouped V equality extent")?
    {
        return Err("grouped V equality point/index extent".into());
    }
    let mut weight = Fr::one();
    for (bit, coordinate) in point.iter().enumerate() {
        weight *= if (index >> bit) & 1 == 1 {
            *coordinate
        } else {
            Fr::one() - *coordinate
        };
    }
    Ok(weight)
}

#[cfg(test)]
fn grouped_v_zero_z(
    circuit: &Circuit,
    expected_terms: usize,
    complement: bool,
    r_local: &[Fr],
    u_local: &[Fr],
) -> Result<Fr, String> {
    if circuit.input_len != WIDTH
        || circuit.row_count != ROWS
        || circuit.terms.len() != expected_terms
        || r_local.len() != LOCAL_ROW_LOG
        || u_local.len() != LOCAL_INPUT_LOG
    {
        return Err("grouped V inactive template geometry changed".into());
    }
    let row_weights = crate::gkr::eq_weights(r_local);
    if row_weights.len() != ROWS {
        return Err("grouped V inactive row-weight extent".into());
    }
    let mut z = Fr::zero();
    for (ordinal, term) in circuit.terms.iter().enumerate() {
        let gate = &term.gate;
        if term.row != ordinal
            || gate.left >= WIDTH
            || gate.right != 0
            || !gate.c0.is_zero()
            || gate.c1 != Fr::one()
            || !gate.c2.is_zero()
            || !gate.c3.is_zero()
            || (complement && M1_IMAGE.contains(&gate.left))
        {
            return Err("grouped V inactive template term changed".into());
        }
        z += row_weights[term.row] * grouped_v_eq_weight(u_local, gate.left)?;
    }
    Ok(z)
}

#[cfg(test)]
impl<'a> DaaHistoryRoster<'a> {
    pub(crate) fn grouped_v_context_for_test(
        &self,
        r: &[Fr],
        u: &[Fr],
        left_value: Fr,
    ) -> Result<DaaGroupedVContextForTest<'_, 'a>, String> {
        if self.headers() != 3073
            || self.slot_log() != 12
            || self.input_log() != 32
            || self.row_log() != 31
            || r.len() != 32
            || u.len() != 32
        {
            return Err("grouped V inactive context scope or point dimensions".into());
        }
        let mut r_point = [Fr::zero(); 32];
        r_point.copy_from_slice(r);
        let mut u_point = [Fr::zero(); 32];
        u_point.copy_from_slice(u);
        let z_full = grouped_v_zero_z(&self.zero_full.circuit, 81920, false, &r[..17], &u[..20])?;
        let z_m1 = grouped_v_zero_z(
            &self.zero_m1_complement.circuit,
            73728,
            true,
            &r[..17],
            &u[..20],
        )?;
        let context = DaaGroupedVContextForTest {
            roster: self,
            parent_object: self.parent as *const _ as usize,
            r: r_point,
            u: u_point,
            left_value,
            z_full,
            z_m1,
            r_owner_weights: crate::gkr::eq_weights(&r[19..31]),
            u_owner_weights: crate::gkr::eq_weights(&u[20..32]),
            full_count: self.zero_full.circuit.terms.len(),
            m1_count: self.zero_m1_complement.circuit.terms.len(),
            template_visits: self.zero_full.circuit.terms.len()
                + self.zero_m1_complement.circuit.terms.len(),
        };
        let mut inactive_total = 0usize;
        let mut family_contributions = 0usize;
        for owner in 0..4096 {
            let class = self.owner_class(owner as u64)?;
            let count = match class {
                OwnerClass::M1 if owner == 2048 => context.m1_count,
                OwnerClass::Short(Profile::M2) if owner == 3072 => 0,
                OwnerClass::Genesis
                | OwnerClass::Initial
                | OwnerClass::Carry
                | OwnerClass::FixedV2
                | OwnerClass::Singleton
                | OwnerClass::Padding
                    if owner != 2048 && owner != 3072 => context.full_count,
                _ => return Err("grouped V inactive family owner class changed".into()),
            };
            inactive_total = inactive_total.checked_add(count)
                .ok_or("grouped V inactive preflight count overflow")?;
            family_contributions = family_contributions.checked_add(if count != 0 { 1 } else { 0 })
                .ok_or("grouped V family contribution count overflow")?;
        }
        if inactive_total != 335454208 || family_contributions != 4095 {
            return Err("grouped V inactive preflight census changed".into());
        }
        Ok(context)
    }

    pub(crate) fn grouped_v_owner_for_test(
        &self,
        context: &DaaGroupedVContextForTest<'_, 'a>,
        owner: usize,
    ) -> Result<(usize, Fr), String> {
        if !std::ptr::eq(self, context.roster)
            || self.parent as *const _ as usize != context.parent_object
            || self.headers() != 3073
            || self.slot_log() != 12
            || owner >= 4096
            || context.r_owner_weights.len() != 4096
            || context.u_owner_weights.len() != 4096
            || context.full_count != 81920
            || context.m1_count != 73728
            || context.template_visits != 155648
        {
            return Err("grouped V inactive owner context or geometry rejected".into());
        }
        if grouped_v_eq_weight(&context.r[19..31], owner)? != context.r_owner_weights[owner]
            || grouped_v_eq_weight(&context.u[20..32], owner)? != context.u_owner_weights[owner]
        {
            return Err("grouped V inactive owner point binding changed".into());
        }
        let (count, z) = match self.owner_class(owner as u64)? {
            OwnerClass::M1 if owner == 2048 => (context.m1_count, context.z_m1),
            OwnerClass::Short(Profile::M2) if owner == 3072 => (0, Fr::zero()),
            OwnerClass::Genesis
            | OwnerClass::Initial
            | OwnerClass::Carry
            | OwnerClass::FixedV2
            | OwnerClass::Singleton
            | OwnerClass::Padding if owner != 2048 && owner != 3072 => {
                (context.full_count, context.z_full)
            }
            _ => return Err("grouped V inactive family owner class changed".into()),
        };
        if count == 0 {
            return Ok((0, Fr::zero()));
        }
        let family_lane_scale = context.left_value
            * context.r[31]
            * context.r[17]
            * context.r[18]
            * context.r_owner_weights[owner]
            * context.u_owner_weights[owner];
        Ok((count, family_lane_scale * z))
    }
}

#[cfg(test)]
impl<'r, 'p> DaaGroupedVContextForTest<'r, 'p> {
    pub(crate) fn template_visits(&self) -> usize {
        self.template_visits
    }

    pub(crate) fn capacity_bytes(&self) -> usize {
        std::mem::size_of::<Self>()
            .saturating_add(self.r_owner_weights.capacity().saturating_mul(std::mem::size_of::<Fr>()))
            .saturating_add(self.u_owner_weights.capacity().saturating_mul(std::mem::size_of::<Fr>()))
    }
}
/// Pure identity check only: it accepts no release authority and mutates nothing.
pub(crate) fn validate_a4_identity(
    term: &Term,
    row_base: usize,
    input_base: usize,
    index: usize,
) -> Result<(), String> {
    if index >= 8192 {
        return Err("DAA roster A4 anchor index outside range".into());
    }
    let row = row_base
        .checked_add(A4_ROWS.start)
        .and_then(|v| v.checked_add(index))
        .ok_or("DAA roster A4 anchor row overflow")?;
    let left = input_base
        .checked_add(A4_WIRES.start)
        .and_then(|v| v.checked_add(index))
        .ok_or("DAA roster A4 anchor input overflow")?;
    if term.row != row
        || term.gate.left != left
        || term.gate.right != input_base
        || [term.gate.c0, term.gate.c1, term.gate.c2, term.gate.c3]
            != [Fr::zero(), Fr::one(), Fr::zero(), Fr::zero()]
    {
        return Err("DAA roster A4 anchor identity changed".into());
    }
    Ok(())
}

fn canonical_a4(parent: &WorkTreeHistoryPlan) -> Result<Circuit, String> {
    let mut terms = Vec::new();
    for t in parent
        .header_boundary()
        .canonical_circuit()
        .terms
        .iter()
        .filter(|t| A4_ROWS.contains(&t.row))
    {
        validate_a4_identity(t, 0, 0, terms.len())?;
        terms.push(t.clone());
    }
    if terms.len() != 8192 {
        return Err("DAA roster canonical A4 count changed".into());
    }
    Ok(Circuit {
        input_len: WIDTH,
        row_count: OWNER_ROWS,
        terms,
    })
}

#[cfg(test)]
mod census35_tests {
    use super::*;
    use crate::historical_prefix_height_work::HeightWork;

    // Independent literal native schedule, used only for scalar test histograms.
    fn oracle_class(n: u64, owner: u64) -> usize {
        if owner >= n { return 14; }
        if owner == 0 { return 0; }
        if owner == 1 { return 1; }
        if owner == 417791 || owner == 417792 { return 3; }
        if owner == 1024 { return 4; }
        if owner == 2048 { return 5; }
        if owner < 844672 && owner % 1024 == 0 {
            if (3072..=8192).contains(&owner) { return 6 + (owner / 1024 - 3) as usize; }
            if owner >= 9216 { return 12; }
        }
        if owner >= 844672 && owner % 128 == 0 { return 13; }
        2
    }

    fn histogram(n: u64, h: usize) -> [u64; 15] {
        let mut counts = [0u64; 15];
        for owner in 0..1u64 << h { counts[oracle_class(n, owner)] += 1; }
        counts
    }

    fn class_vector(c: CensusOwners) -> [u64; 15] {
        [1, 1, c.carry, c.fixed, c.singleton, c.m1,
            c.shorts[0], c.shorts[1], c.shorts[2], c.shorts[3], c.shorts[4], c.shorts[5],
            c.mature[0], c.mature[1], c.padding]
    }

    fn class_index(c: OwnerClass) -> usize {
        match c {
            OwnerClass::Genesis => 0, OwnerClass::Initial => 1, OwnerClass::Carry => 2,
            OwnerClass::FixedV2 => 3, OwnerClass::Singleton => 4, OwnerClass::M1 => 5,
            OwnerClass::Short(p) => 4 + p.count(),
            OwnerClass::Mature(Epoch::Legacy) => 12, OwnerClass::Mature(Epoch::Eip) => 13,
            OwnerClass::Padding => 14,
        }
    }

    fn emitted(daa: &DaaHistoryRoster<'_>, owner: u64) -> Counts {
        let mut raw = 0usize;
        let counts = daa.visit_owner_terms(owner, |_| {
            raw = raw.checked_add(1).ok_or("test occurrence overflow")?; Ok(())
        }).unwrap();
        assert_eq!(raw, counts.lanes.iter().sum::<usize>());
        counts
    }

    fn weighted(hist: &[u64; 15], units: &[Counts; 15]) -> Counts {
        let mut result = Counts::default();
        for (copies, unit) in hist.iter().zip(units) {
            for (total, count) in result.lanes.iter_mut().zip(unit.lanes) {
                *total += usize::try_from(*copies).unwrap() * count;
            }
        }
        result
    }

    #[test]
    fn census35_scalar_frontiers_match_independent_histogram() {
        for boundary in [4u64, 8, 1024, 2048, 3072, 4096, 5120, 6144, 7168, 8192, 9216,
            417791, 417792, 418816, 844544, 844672, 844800, 1 << 20, 1 << 21]
        {
            for n in [boundary - 1, boundary, boundary + 1, boundary + 2] {
                if !(3..=1 << 21).contains(&n) { continue; }
                let h = n.next_power_of_two().trailing_zeros() as usize;
                let actual = census_owners(&ScheduleDomain::new(n, h).unwrap()).unwrap();
                let expected = histogram(n, h);
                assert_eq!(class_vector(actual), expected, "N{n} H{h}");
                assert_eq!(actual.inactive_full, expected[0] + expected[1] + expected[2]
                    + expected[3] + expected[4] + expected[14]);
            }
        }
        for (n, h) in [(1, 0), (2, 2), (3, 22)] {
            assert!(census_owners(&ScheduleDomain::new(n, h).unwrap()).is_err());
        }
        assert!(ScheduleDomain::new(5, 2).is_err());
    }

    #[test]
    fn census35_raw_occurrences_and_checked_arithmetic() {
        let term = Term { row: 0, gate: Gate { left: 0, right: 0,
            c0: Fr::zero(), c1: Fr::zero(), c2: Fr::zero(), c3: Fr::zero() } };
        assert_eq!(census_occurrences(|sink| {
            sink(term.clone())?; sink(term.clone())?; Ok(2)
        }).unwrap(), 2, "duplicate and zero-coefficient occurrences remain present");
        assert!(census_occurrences(|sink| { sink(term.clone())?; Ok(2) }).is_err());
        assert!(census_sum([u64::MAX, 1]).is_err());
        let mut total = usize::MAX;
        assert!(census_add(&mut total, 1, 1).is_err());
        assert_eq!(total, usize::MAX);
        let mut total = 0usize;
        assert!(census_add(&mut total, u64::MAX, usize::MAX).is_err());
        assert_eq!(total, 0);
    }

    #[test]
    fn census35_small_composite_counts_match_emitted_classes() {
        for (n, h, expected_total) in [(3, 2, 329122usize), (4, 2, 330050), (5, 3, 658658)] {
            // Each iteration drops the full parent before constructing the next.
            let parent = WorkTreeHistoryPlan::compile(n, h, [7; 32], [0; 28]).unwrap();
            let mut daa = DaaHistoryRoster::compile(&parent).unwrap();
            let hist = histogram(n, h);
            let mut reps = [None; 15];
            for owner in 0..1u64 << h { reps[oracle_class(n, owner)].get_or_insert(owner); }
            let mut units = [Counts::default(); 15];
            for (class, owner) in reps.into_iter().enumerate() {
                if let Some(owner) = owner {
                    assert_eq!(class_index(daa.owner_class(owner).unwrap()), class);
                    units[class] = emitted(&daa, owner);
                }
            }
            let actual = daa.term_census().unwrap();
            assert_eq!(actual, weighted(&hist, &units));
            let height = HeightWork::compile_history(&parent).unwrap();
            let mut height_raw = 0usize;
            for owner in 0..1u64 << h {
                height.visit_owner_terms(owner, |_| {
                    height_raw = height_raw.checked_add(1).ok_or("test height count overflow")?; Ok(())
                }).unwrap();
            }
            assert_eq!(height_raw + actual.lanes.iter().sum::<usize>(), expected_total);
            assert_eq!(actual.lanes[2], if n == 3 { 673 } else if n == 4 { 1121 } else { 1569 });
            daa.schedule = ScheduleDomain::new(n + 1, h + 1).unwrap();
            assert!(daa.term_census().is_err(), "a different parent schedule cannot supply counts");
        }
    }

    #[test]
    #[ignore = "bounded H20 DAA template census; separate resource and ROOT runtime admission"]
    fn census35_all_native_classes_match_representative_emitters() {
        const N: u64 = 844673;
        const H: usize = 20;
        let parent = WorkTreeHistoryPlan::compile(N, H, [7; 32], [0; 28]).unwrap();
        let mut daa = DaaHistoryRoster::compile(&parent).unwrap();
        let hist = histogram(N, H);
        let reps = [0, 1, 2, 417791, 1024, 2048, 3072, 4096, 5120, 6144, 7168, 8192,
            9216, 844672, N];
        let mut units = [Counts::default(); 15];
        for (class, owner) in reps.into_iter().enumerate() {
            assert_eq!(oracle_class(N, owner), class);
            assert_eq!(class_index(daa.owner_class(owner).unwrap()), class);
            assert!(hist[class] > 0);
            units[class] = emitted(&daa, owner);
        }
        assert_eq!(daa.term_census().unwrap(), weighted(&hist, &units));
        let one = daa.one.take();
        assert!(daa.term_census().is_err(), "active M1 requires its owned template");
        daa.one = one;
        let short = daa.shorts.pop().unwrap();
        assert!(daa.term_census().is_err(), "active short class requires its owned template");
        daa.shorts.push(short);
    }
}


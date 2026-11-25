//! One pinned native parent -> streamed scalar Global-U -> selected physical Map.
//! Diagnostic only: no global witness commitment, proof, or client is constructed.
//! All 822 final-Map B rows receive symbolic residual and e64 bound checks.
//! Nine physical anchor lanes are compared without assembling a common global X.
use super::*;
use crate::global_u_roster::{self, CandidateSource, Schedule, SuppliedCandidate};
use crate::h21_scheduled_max_cap::CutDescriptor;

#[path = "candidate162_cut_score_source.rs"]
pub(super) mod candidate162_cut_score_source;

fn mark(started: Instant, label: &str) {
    println!(
        "C138_PHASE label={label} elapsed_s={:.6}",
        started.elapsed().as_secs_f64()
    );
    std::io::stdout().flush().expect("flush c138 phase");
}

fn mark140(started: Instant, label: &str) {
    println!(
        "C140_PHASE label={label} elapsed_s={:.6}",
        started.elapsed().as_secs_f64()
    );
    std::io::stdout().flush().expect("flush c140 phase");
}

fn check_packed_map(
    packed: &NativePackedRow,
    symbolic: &crate::legacy_envelope_map::OwnerRow,
    plan: &WorkTreeHistoryPlan,
    map: &Map,
    owner: usize,
    exports: &NativeExports<'_>,
) -> usize {
    assert_eq!(symbolic.owner, owner as u64);
    assert_eq!(symbolic.binding, map.binding());
    packed
        .validate_bank53_map_identity_for_history_test(plan, map, owner, 0)
        .expect("exact packed Map parent/owner/binding/context metadata");
    assert_eq!(packed.owner(), owner);
    assert_eq!(packed.packed_bytes().len(), OWNER_ROW_BYTES);
    for bit in 0..BANK53_MAP_LIVE_BITS {
        assert_eq!(
            packed_bit(packed.packed_bytes(), BANK53_BASE + bit),
            symbolic.bits[bit],
            "owner{owner} Bank53 Map bit{bit}"
        );
    }
    assert!((BANK53_MAP_LIVE_BITS..BANK53_CONTEXT_BITS)
        .all(|bit| !packed_bit(packed.packed_bytes(), BANK53_BASE + bit)));
    let mut own_import_bits = 0usize;
    for import in map
        .imports(owner as u64)
        .unwrap()
        .into_iter()
        .filter(|import| import.owner == owner as u64)
    {
        for bit in 0..import.width {
            assert_eq!(
                packed_bit(packed.packed_bytes(), import.local + bit),
                exports.bit(map.input_index(import, bit).unwrap()).unwrap(),
                "owner{owner} native own import {:?} bit{bit}",
                import.kind
            );
            own_import_bits += 1;
        }
    }
    own_import_bits
}

fn native_inputs(map: &Map, owner: u64, exports: &NativeExports<'_>) -> Result<Inputs, String> {
    let mut inputs = Inputs::default();
    for import in map.imports(owner)? {
        let mut word = BigUint::from(0u8);
        for bit in 0..import.width {
            if exports.bit(map.input_index(import, bit)?)? {
                word |= BigUint::from(1u8) << bit;
            }
        }
        inputs.put(map, import, &BigInt::from(word))?;
    }
    Ok(inputs)
}

// Only one candidate value and one temporary symbolic B row are live at a time.
// fold's missing-item error must never erase the first native source error.
struct NativeCandidates<'a, 'b> {
    schedule: global_u_roster::ScheduleIter,
    prefix: &'a NativePrefix,
    map: &'a Map,
    exports: &'a NativeExports<'b>,
    first_error: Option<String>,
    d_count: u64,
    b_count: u64,
    max_d: Option<(u64, BigUint)>,
    max_b: Option<(u64, BigUint)>,
}

impl NativeCandidates<'_, '_> {
    fn value(&self, source: CandidateSource) -> Result<BigUint, String> {
        match source {
            CandidateSource::HeaderDifficulty { height, work_owner } => {
                if work_owner != height - 2 {
                    return Err("D work owner mismatch".into());
                }
                self.prefix
                    .compact_n_bits(height as usize)
                    .and_then(crate::work_tree_work::native_decode)
            }
            CandidateSource::LegacyBound {
                q,
                endpoint,
                map_owner,
                ell,
            } => {
                if endpoint != 1024 * (q + 1)
                    || map_owner != q * 1024 + 959
                    || ell != q.min(8) as usize
                {
                    return Err("B scheduled tuple mismatch".into());
                }
                let inputs = native_inputs(self.map, map_owner, self.exports)?;
                self.map
                    .generate(map_owner, &inputs)?
                    .bound(self.map)?
                    .to_biguint()
                    .ok_or_else(|| "negative native B bound".into())
            }
        }
    }
}

impl Iterator for NativeCandidates<'_, '_> {
    type Item = SuppliedCandidate;
    fn next(&mut self) -> Option<Self::Item> {
        if self.first_error.is_some() {
            return None;
        }
        let source = self.schedule.next()?;
        let value = match self.value(source) {
            Ok(value) => value,
            Err(error) => {
                self.first_error = Some(format!("native candidate {source:?}: {error}"));
                return None;
            }
        };
        let slot = match source {
            CandidateSource::HeaderDifficulty { height, .. } => {
                self.d_count += 1;
                (&mut self.max_d, height)
            }
            CandidateSource::LegacyBound { q, .. } => {
                self.b_count += 1;
                (&mut self.max_b, q)
            }
        };
        if slot.0.as_ref().map_or(true, |(_, old)| value > *old) {
            *slot.0 = Some((slot.1, value.clone()));
        }
        Some(SuppliedCandidate { source, value })
    }
}

/// Source-derived Global-U result for one short consumer cut. The enclosing
/// H21 parent remains the sole source for both D and native B imports.
#[derive(Clone, Debug)]
pub(super) struct NativeCutU {
    descriptor: CutDescriptor,
    context: usize,
    parent: CutParent,
    pub cut: u64,
    pub envelope: global_u_roster::GlobalEnvelope,
    pub max_d: (u64, BigUint),
    pub max_b: (u64, BigUint),
    pub selected_lower: LowerSelector,
    pub lower_d: BigUint,
    pub lower_owner: u64,
    pub consumer_binding: crate::legacy_envelope_map::Binding,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct CutParent { headers: usize, slot_log: usize, root: [u8;32], total: [u8;28], profile: [u8;32] }
impl CutParent {
    fn native(prefix:&NativePrefix)->Self {
        Self {headers:prefix.header_count(),slot_log:prefix.slot_count().trailing_zeros() as usize,
            root:prefix.root(),total:prefix.total_be28(),profile:prefix.profile()}
    }
}
impl NativeCutU {
    fn validate_identity(&self,descriptor:CutDescriptor,context:usize,parent:CutParent)->Result<(),String> {
        if self.descriptor!=descriptor || self.context!=context || context>=2 {
            return Err("native U descriptor/context".into());
        }
        if self.parent!=parent {return Err("native U source parent".into());}
        if self.cut!=descriptor.terminals()[context] as u64 || self.envelope.n!=self.cut
            || self.consumer_binding.n!=self.cut || self.consumer_binding.h!=21
            || self.consumer_binding.parent_root.is_some() {
            return Err("native U cut/consumer binding".into());
        }
        Ok(())
    }
    pub(super) fn validate_source(&self,descriptor:CutDescriptor,context:usize,
        plan:&WorkTreeHistoryPlan,prefix:&NativePrefix)->Result<(),String> {
        validate_native_plan_input(plan,prefix)?;
        self.validate_identity(descriptor,context,CutParent::native(prefix))
    }
}

/// Fold both c146 consumer cuts from one already constructed native parent.
/// This helper accepts no free candidate values and deliberately leaves each
/// cut Map unbound to the full parent's root.
pub(super) fn fold_native_global_u_cut_pair(
    plan: &WorkTreeHistoryPlan,
    prefix: &NativePrefix,
) -> Result<[NativeCutU; 2], String> {
    fold_native_global_u_with_descriptor(plan,prefix,CutDescriptor::diagnostic08())
}

pub(super) fn fold_native_global_u_cut_pair_eligible08(
    plan:&WorkTreeHistoryPlan,prefix:&NativePrefix,
)->Result<[NativeCutU;2],String> {
    fold_native_global_u_with_descriptor(plan,prefix,CutDescriptor::eligible08())
}

fn fold_native_global_u_with_descriptor(plan:&WorkTreeHistoryPlan,prefix:&NativePrefix,
    descriptor:CutDescriptor,
)->Result<[NativeCutU;2],String> {
    const EXPECTED_LOWER_HEIGHT: u64 = 841_729;
    const EXPECTED_LOWER_OWNER: u64 = 841_727;

    if plan.headers() != 1_827_840 || plan.slot_log() != 21 || plan.slots() != 1 << 21 {
        return Err("c146 Global-U requires the exact H21 source parent".into());
    }
    validate_native_plan_input(plan, prefix)?;
    let exports = NativeExports::new_for_history(plan, prefix)?;
    let parent_map = Map::from_parent(plan, 64)?;
    let mut results = Vec::with_capacity(2);
    for (context,terminal) in descriptor.terminals().into_iter().enumerate() {
        let cut=terminal as u64;
        // B is a historical Map bound. Keep its legacy mode and verify the
        // historical tier range matches c138's full-parent source Map.
        let map = Map::new(cut, plan.slot_log(), 64)?;
        if map.binding().parent_root.is_some() || map.m() != parent_map.m() {
            return Err("c146 cut B Map source geometry/root binding".into());
        }
        let mut stream = NativeCandidates {
            schedule: Schedule::new(cut)?.iter(),
            prefix,
            map: &map,
            exports: &exports,
            first_error: None,
            d_count: 0,
            b_count: 0,
            max_d: None,
            max_b: None,
        };
        let folded = global_u_roster::fold(cut, &mut stream);
        if let Some(error) = stream.first_error.take() {
            return Err(error);
        }
        let envelope = folded?;
        if envelope.header_count != cut - 1
            || envelope.legacy_count != 822
            || stream.b_count != 822
            || stream.d_count != cut - 1
        {
            return Err("c146 native cut candidate census".into());
        }
        let max_d = stream.max_d.take().ok_or("missing native D maximum")?;
        let max_b = stream.max_b.take().ok_or("missing native B maximum")?;
        if envelope.max_difficulty != max_d.1 || envelope.modern_floor != (&max_d.1 * 3u8) / 2u8 {
            return Err("c146 native cut D maximum/floor mismatch".into());
        }
        let independent_max = envelope
            .modern_floor
            .clone()
            .max(max_b.1.clone())
            .max(BigUint::from(global_u_roster::INITIAL_I))
            .max(BigUint::from(global_u_roster::RESET_CHILD_417792))
            .max(BigUint::from(global_u_roster::RESET_CHILD_417793));
        if envelope.maximum_candidate != independent_max {
            return Err("c146 native cut maximum candidate mismatch".into());
        }
        let selected_lower = selected_lower(
            envelope.exponent,
            &max_d,
            &max_b,
            &envelope.maximum_candidate,
        )?;
        if envelope.exponent != 55 || envelope.u != (BigUint::from(1u8) << 55) {
            if descriptor==CutDescriptor::diagnostic08() {
                return Err("c146 native cut did not derive the expected e55 U".into());
            }
            return Err(format!("current pinned U profile unsupported envelope e{} source {selected_lower:?}; expected e55",envelope.exponent));
        }
        if selected_lower.source
            != (LowerSource::HeaderDifficulty {
                height: EXPECTED_LOWER_HEIGHT,
            })
            || selected_lower.branch != LowerBranch::Pivot(54)
        {
            if descriptor==CutDescriptor::diagnostic08() {
                return Err("c146 selected lower is not derived D841729/Pivot54".into());
            }
            return Err(format!("current pinned U profile unsupported selected lower: {selected_lower:?}; expected D841729/Pivot54"));
        }
        let lower_owner = EXPECTED_LOWER_HEIGHT
            .checked_sub(2)
            .ok_or("selected lower D owner underflow")?;
        if lower_owner != EXPECTED_LOWER_OWNER {
            return Err("c146 selected lower D owner mismatch".into());
        }
        let lower_d = prefix
            .compact_n_bits(EXPECTED_LOWER_HEIGHT as usize)
            .and_then(crate::work_tree_work::native_decode)?;
        if lower_d != max_d.1 {
            return Err("re-read selected lower D differs from folded maximum".into());
        }
        let consumer = Map::new_modern_global_u_selected_lower(
            cut,
            plan.slot_log(),
            envelope.exponent,
            selected_lower,
        )?;
        let lower_import = consumer
            .imports(lower_owner)?
            .into_iter()
            .find(|import| import.kind == Kind::Difficulty)
            .ok_or("selected lower owner lacks its native D import")?;
        if lower_import.owner != EXPECTED_LOWER_OWNER
            || lower_import.local != crate::legacy_envelope_map::D_LOCAL
            || lower_import.width != 224
        {
            return Err("selected lower D physical import identity".into());
        }
        let mut imported_d = BigUint::from(0u8);
        for bit in 0..lower_import.width {
            if exports.bit(consumer.input_index(lower_import, bit)?)? {
                imported_d |= BigUint::from(1u8) << bit;
            }
        }
        if imported_d != lower_d {
            return Err("selected lower native import differs from compact D decode".into());
        }
        let consumer_binding = consumer.binding();
        if consumer_binding.parent_root.is_some() {
            return Err("c146 cut consumer Map must not copy parent root".into());
        }
        results.push(NativeCutU {
            descriptor,
            context,
            parent:CutParent::native(prefix),
            cut,
            envelope,
            max_d,
            max_b,
            selected_lower,
            lower_d,
            lower_owner,
            consumer_binding,
        });
    }
    results
        .try_into()
        .map_err(|_| "c146 native cut result count".into())
}

#[test]
fn c165_eligible_u_cut_geometry_without_frame() {
    let descriptor=CutDescriptor::eligible08();
    let legacy:Vec<_>=Schedule::new(1_827_840).unwrap().legacy_items().collect();
    assert_eq!(legacy.len(),822);
    for (context,cut) in descriptor.terminals().into_iter().enumerate() {
        let map=Map::new(cut as u64,21,64).unwrap();
        assert_eq!(map.m(),824);
        assert_eq!(map.binding().parent_root,None);
        let tuples:Vec<_>=Schedule::new(cut as u64).unwrap().legacy_items().collect();
        assert_eq!(tuples,legacy);
        for tuple in &tuples {
            let CandidateSource::LegacyBound {map_owner,..}=*tuple else {unreachable!()};
            let parent=Map::new(1_827_840,21,64).unwrap();
            assert_eq!(map.imports(map_owner).unwrap(),parent.imports(map_owner).unwrap());
            for import in map.imports(map_owner).unwrap() {
                for bit in 0..import.width {
                    assert_eq!(map.input_index(import,bit).unwrap(),parent.input_index(import,bit).unwrap());
                }
            }
        }
        let d=Schedule::new(cut as u64).unwrap().iter()
            .filter(|s|matches!(s,CandidateSource::HeaderDifficulty {..})).count();
        assert_eq!(d,[1_827_839,1_810_841][context]);
    }
}

#[test]
fn c165_eligible_u_independent_cut_folds_and_identity_negatives() {
    let descriptor=CutDescriptor::eligible08();
    let parent=CutParent {headers:1_827_840,slot_log:21,root:[0x65;32],total:[0x66;28],profile:[0x67;32]};
    let mut results=Vec::new();
    for (context,terminal) in descriptor.terminals().into_iter().enumerate() {
        let cut=terminal as u64;
        let mut max_d=(0,BigUint::from(0u8));
        let max_b=(1,BigUint::from(global_u_roster::INITIAL_I));
        let candidates=Schedule::new(cut).unwrap().iter().map(|source| {
            let value=match source {
                CandidateSource::HeaderDifficulty {height,..}=>{
                    let d=if height==1_820_100 {BigUint::from(1u8)<<54}
                        else if height==417_792||height==417_793 {BigUint::from(global_u_roster::RESET_CHILD_417792)}
                        else {BigUint::from(global_u_roster::INITIAL_I)};
                    if d>max_d.1 {max_d=(height,d.clone());}d
                },
                CandidateSource::LegacyBound {..}=>max_b.1.clone(),
            };
            SuppliedCandidate {source,value}
        });
        let envelope=global_u_roster::fold(cut,candidates).unwrap();
        assert_eq!(envelope.header_count,[1_827_839,1_810_841][context]);
        assert_eq!(envelope.legacy_count,822);
        assert_eq!(envelope.max_difficulty,max_d.1);
        let selected_lower=selected_lower(envelope.exponent,&max_d,&max_b,&envelope.maximum_candidate).unwrap();
        let lower_owner=max_d.0-2;
        let consumer=Map::new_modern_global_u_selected_lower(cut,21,envelope.exponent,selected_lower).unwrap();
        let result=NativeCutU {descriptor,context,parent,cut,lower_d:max_d.1.clone(),max_d,max_b,
            envelope,selected_lower,lower_owner,consumer_binding:consumer.binding()};
        result.validate_identity(descriptor,context,parent).unwrap();
        assert!(result.validate_identity(CutDescriptor::diagnostic08(),context,parent).is_err());
        assert!(result.validate_identity(descriptor,1-context,parent).is_err());
        assert!(result.validate_identity(descriptor,2,parent).is_err());
        for field in 0..5 {
            let mut changed=parent;
            match field {0=>changed.headers-=1,1=>changed.slot_log-=1,2=>changed.root[0]^=1,
                3=>changed.total[0]^=1,_=>changed.profile[0]^=1};
            assert_eq!(result.validate_identity(descriptor,context,changed).unwrap_err(),"native U source parent");
        }
        let mut changed=result.clone();changed.cut-=1;changed.envelope.n=changed.cut;
        changed.consumer_binding.n=changed.cut;
        assert_eq!(changed.validate_identity(descriptor,context,parent).unwrap_err(),"native U cut/consumer binding");
        results.push(result);
    }
    // This is a synthetic roster with protocol literals, not native e55 evidence.
    assert_eq!(results[0].envelope.exponent,55);
    assert_eq!(results[1].envelope.exponent,48);
    assert_ne!(results[0].envelope.u,results[1].envelope.u);
}

fn strict_pivot(value: &BigUint, threshold: &BigUint) -> Result<usize, String> {
    if value <= threshold {
        return Err("lower witness must strictly exceed threshold".into());
    }
    let difference = value ^ threshold;
    let pivot = (difference.bits() - 1) as usize;
    if !value.bit(pivot as u64) || threshold.bit(pivot as u64) {
        return Err("lower witness MSB pivot direction".into());
    }
    Ok(pivot)
}

fn selected_lower(
    e: usize,
    max_d: &(u64, BigUint),
    max_b: &(u64, BigUint),
    maximum: &BigUint,
) -> Result<LowerSelector, String> {
    let u = BigUint::from(1u8) << e;
    let half = &u / 2u8;
    if maximum > &u || maximum <= &half {
        return Err("envelope is not minimal dyadic U".into());
    }
    let modern = (&max_d.1 * 3u8) / 2u8;
    if &modern == maximum {
        // floor(3D/2) > U/2 iff D >= ceil((U+2)/3) = floor((U+4)/3).
        let threshold = (&u + 4u8) / 3u8;
        let branch = if max_d.1 == threshold {
            LowerBranch::Equality
        } else {
            LowerBranch::Pivot(strict_pivot(&max_d.1, &threshold)?)
        };
        return Ok(LowerSelector {
            source: LowerSource::HeaderDifficulty { height: max_d.0 },
            branch,
        });
    }
    if &max_b.1 == maximum {
        return Ok(LowerSelector {
            source: LowerSource::LegacyBound { q: max_b.0 },
            branch: LowerBranch::Pivot(strict_pivot(&max_b.1, &half)?),
        });
    }
    for (literal, source) in [
        (global_u_roster::INITIAL_I, LowerSource::InitialI),
        (
            global_u_roster::RESET_CHILD_417792,
            LowerSource::Reset417792,
        ),
        (
            global_u_roster::RESET_CHILD_417793,
            LowerSource::Reset417793,
        ),
    ] {
        if BigUint::from(literal) == *maximum {
            return Ok(LowerSelector {
                source,
                branch: LowerBranch::Literal,
            });
        }
    }
    Err("maximum has no authenticated lower witness".into())
}

#[test]
fn c138_selected_lower_uses_derived_threshold_and_msb() {
    let d = |value: u64| (19, BigUint::from(value));
    let b = |value: u64| (9, BigUint::from(value));
    // e=6: threshold ceil(66/3)=22; Equality and strict MSB branches differ.
    assert_eq!(
        selected_lower(6, &d(22), &b(1), &33u8.into())
            .unwrap()
            .branch,
        LowerBranch::Equality
    );
    assert_eq!(
        selected_lower(6, &d(23), &b(1), &34u8.into())
            .unwrap()
            .branch,
        LowerBranch::Pivot(0)
    );
    let legacy = selected_lower(6, &d(10), &b(40), &40u8.into()).unwrap();
    assert_eq!(legacy.source, LowerSource::LegacyBound { q: 9 });
    assert_eq!(legacy.branch, LowerBranch::Pivot(3));
    assert!(strict_pivot(&32u8.into(), &32u8.into()).is_err());
    assert!(selected_lower(6, &d(20), &b(30), &30u8.into()).is_err());
    let literal = BigUint::from(global_u_roster::RESET_CHILD_417792);
    let e = literal.bits() as usize;
    assert_eq!(
        selected_lower(e, &d(1), &b(1), &literal).unwrap().branch,
        LowerBranch::Literal
    );
}

#[test]
#[ignore = "full pinned H21 frame; bounded pinned runner and independent review required"]
fn h21_pinned_frame_native_global_u_selected_physical_map() {
    let started = Instant::now();
    mark(started, "PREFIX_START");
    let path = std::env::var_os("NIPOPOW_H21_FRAME").expect("pinned frame variable");
    let path = Path::new(&path);
    assert!(path.is_absolute());
    let before = fs::symlink_metadata(path).expect("frame metadata");
    assert!(before.is_file() && !before.file_type().is_symlink());
    assert_eq!(before.len(), FRAME_BYTES);
    let file = File::open(path).expect("open pinned frame");
    assert_eq!(file.metadata().unwrap().len(), FRAME_BYTES);
    let mut frame = FrameReader::new(BufReader::with_capacity(CHUNK, file), FRAME_BYTES).unwrap();
    preamble(&mut frame, 1_827_839, N as u32).expect("exact ERFV preamble");
    let (prefix, extensions) = {
        let mut headers = HeaderIter::new(&mut frame, N);
        let prefix = NativePrefix::from_raw_iter(N, &mut headers).expect("linked native prefix");
        assert_eq!(headers.remaining, 0);
        (prefix, headers.extensions)
    };
    assert_eq!(prefix.header_count(), N);
    assert_eq!(frame.offset, PREFIX_BYTES);
    assert_eq!(extensions, EXTENSIONS);
    frame
        .finish(PREFIX_BYTES, TAIL_BYTES, FRAME_SHA256)
        .expect("entire pinned frame SHA256");
    let after = fs::symlink_metadata(path).unwrap();
    assert!(after.is_file() && !after.file_type().is_symlink());
    assert_eq!(after.len(), FRAME_BYTES);
    assert_eq!(
        after.modified().unwrap(),
        before.modified().unwrap(),
        "frame modification time unchanged across complete authentication"
    );
    mark(started, "PREFIX_SHA256_READY");
    let plan =
        WorkTreeHistoryPlan::compile(N as u64, H, prefix.root(), prefix.total_be28()).unwrap();
    validate_native_plan_input(&plan, &prefix).expect("exact same parent root/total");
    let exports = NativeExports::new_for_history(&plan, &prefix).unwrap();
    mark(started, "PARENT_READY");

    let scalar_started = Instant::now();
    let (envelope, max_d, max_b) = {
        let map = Map::from_parent(&plan, 64).expect("parent-bound diagnostic B map");
        let mut stream = NativeCandidates {
            schedule: Schedule::new(N as u64).unwrap().iter(),
            prefix: &prefix,
            map: &map,
            exports: &exports,
            first_error: None,
            d_count: 0,
            b_count: 0,
            max_d: None,
            max_b: None,
        };
        let folded = global_u_roster::fold(N as u64, &mut stream);
        assert!(
            stream.first_error.is_none(),
            "first source failure: {:?}",
            stream.first_error
        );
        let envelope = folded.expect("complete exact native candidate stream");
        assert_eq!((stream.d_count, stream.b_count), (1_827_839, 822));
        assert_eq!(
            (envelope.header_count, envelope.legacy_count),
            (stream.d_count, stream.b_count)
        );
        let max_d = stream.max_d.take().unwrap();
        let max_b = stream.max_b.take().unwrap();
        assert_eq!(envelope.max_difficulty, max_d.1);
        assert_eq!(envelope.modern_floor, (&max_d.1 * 3u8) / 2u8);
        let independent_max = envelope
            .modern_floor
            .clone()
            .max(max_b.1.clone())
            .max(BigUint::from(global_u_roster::INITIAL_I))
            .max(BigUint::from(global_u_roster::RESET_CHILD_417792))
            .max(BigUint::from(global_u_roster::RESET_CHILD_417793));
        assert_eq!(envelope.maximum_candidate, independent_max);
        (envelope, max_d, max_b)
    };
    let scalar_seconds = scalar_started.elapsed().as_secs_f64();
    let selector = selected_lower(
        envelope.exponent,
        &max_d,
        &max_b,
        &envelope.maximum_candidate,
    )
    .expect("derived true minimality witness");
    println!("C138_SCALAR d_height={} d={} b_q={} b={} modern_floor={} maximum={} e={} u={} selector={selector:?} scalar_s={scalar_seconds:.6}",
        max_d.0, max_d.1, max_b.0, max_b.1, envelope.modern_floor, envelope.maximum_candidate,
        envelope.exponent, envelope.u);
    mark(started, "SCALAR_FOLD_READY");

    // This pinned-frame diagnostic exercises the measured modern-D winner.
    // A different winner is an explicit failed scope expectation, never replaced
    // by an assumed historical height, exponent, B value or selected pivot.
    let height = match selector.source {
        LowerSource::HeaderDifficulty { height } => height,
        other => {
            panic!("pinned-frame physical diagnostic requires measured D winner, got {other:?}")
        }
    };
    let owner = (height - 2) as usize;
    assert_ne!(owner % 1024, 959, "measured D winner must be non-anchor");
    let map = Map::from_parent_modern_global_u(&plan, envelope.exponent, selector).unwrap();
    mark140(started, "B_FINAL_START");
    let b_final_started = Instant::now();
    let mut b_final_count = 0u64;
    let mut b_final_max: Option<(u64, BigUint)> = None;
    let mut b_final_q9_negatives = 0u64;
    {
        let diagnostic = Map::from_parent(&plan, 64).unwrap();
        for source in Schedule::new(N as u64).unwrap().legacy_items() {
            let CandidateSource::LegacyBound {
                q,
                endpoint,
                map_owner,
                ell,
            } = source
            else {
                panic!("legacy iterator emitted non-B source {source:?}")
            };
            assert_eq!(
                (endpoint, map_owner, ell),
                (1024 * (q + 1), q * 1024 + 959, q.min(8) as usize)
            );
            let inputs = native_inputs(&map, map_owner, &exports).unwrap();
            let row = map.generate(map_owner, &inputs).unwrap();
            let failures = map.failures(&row, &inputs).unwrap();
            assert!(
                failures.is_empty(),
                "final Map q={q} owner={map_owner} residuals={failures:?}"
            );
            let bound = row.bound(&map).unwrap().to_biguint().unwrap();
            assert!(
                bound >= BigUint::from(global_u_roster::INITIAL_I),
                "q={q} B below initial I"
            );
            assert!(bound <= envelope.u, "q={q} B exceeds derived U");
            assert_eq!(
                map.imports(map_owner).unwrap(),
                diagnostic.imports(map_owner).unwrap()
            );
            let diagnostic_inputs = native_inputs(&diagnostic, map_owner, &exports).unwrap();
            let diagnostic_row = diagnostic.generate(map_owner, &diagnostic_inputs).unwrap();
            assert_eq!(
                BigInt::from(bound.clone()),
                diagnostic_row.bound(&diagnostic).unwrap(),
                "q={q} final bound differs from same-source e64 scalar-fold bound"
            );
            if b_final_max.as_ref().map_or(true, |(_, old)| bound > *old) {
                b_final_max = Some((q, bound));
            }
            if q == 9 {
                let imported = *map
                    .imports(map_owner)
                    .unwrap()
                    .iter()
                    .find(|import| import.owner == 3070 && import.kind == Kind::Difficulty)
                    .unwrap();
                let mut altered = inputs.clone();
                altered.flip(imported, 0).unwrap();
                let negative = map.failures(&row, &altered).unwrap();
                let failed_rows = negative
                    .iter()
                    .map(|(row, _)| *row)
                    .collect::<BTreeSet<_>>();
                let expected_row = map_owner as usize * (1 << 14) + 8350;
                assert_eq!(
                    failed_rows,
                    BTreeSet::from([expected_row]),
                    "native final-Map q9 isolated D import bit"
                );
                b_final_q9_negatives += 1;
                println!("C140_B_FINAL_NEGATIVE q=9 import_owner=3070 bit=0 expected_row={expected_row} failed_rows=1");
            }
            b_final_count += 1;
            if b_final_count % 64 == 0 {
                println!(
                    "C140_B_FINAL_PROGRESS count={b_final_count} q={q} elapsed_s={:.6}",
                    b_final_started.elapsed().as_secs_f64()
                );
                std::io::stdout().flush().expect("flush B progress");
            }
        }
    }
    assert_eq!(b_final_count, 822);
    assert_eq!(b_final_q9_negatives, 1);
    assert_eq!(b_final_max.as_ref().unwrap(), &max_b);
    let b_final_seconds = b_final_started.elapsed().as_secs_f64();
    println!("C140_B_FINAL_PASS count={b_final_count} q9_negative={b_final_q9_negatives} max_q={} max_b={} final_e={} scalar_equality=true residual_s={b_final_seconds:.6}", max_b.0, max_b.1, envelope.exponent);
    mark140(started, "B_FINAL_READY");
    let imports = map.imports(owner as u64).unwrap();
    assert_eq!(imports.len(), 1, "non-anchor D exact own import census");
    assert_eq!(
        (imports[0].owner, imports[0].kind),
        (owner as u64, Kind::Difficulty)
    );
    let inputs = native_inputs(&map, owner as u64, &exports).unwrap();
    assert_eq!(
        inputs.get(imports[0]).unwrap(),
        BigInt::from(max_d.1.clone())
    );
    let symbolic = map.generate(owner as u64, &inputs).unwrap();
    assert!(map.failures(&symbolic, &inputs).unwrap().is_empty());
    let selected_started = Instant::now();
    let mut anchors_checked = 0usize;
    let mut own_import_bits = 0usize;
    let packed = {
        mark140(started, "PRODUCER_START");
        let producer = NativeOwnerProducer::new_for_history(&plan, &prefix).unwrap();
        mark140(started, "PRODUCER_READY");
        let selected = producer
            .produce_bank53_map_h21_for_test(owner, &map, 0)
            .unwrap();
        let selected_own_bits =
            check_packed_map(&selected, &symbolic, &plan, &map, owner, &exports);
        assert_eq!(selected_own_bits, 224);
        own_import_bits += selected_own_bits;
        assert!(selected
            .validate_bank53_map_identity_for_history_test(&plan, &map, owner, 1)
            .is_err());
        let diagnostic = Map::from_parent(&plan, 64).unwrap();
        assert!(selected
            .validate_bank53_map_identity_for_history_test(&plan, &diagnostic, owner, 0)
            .is_err());
        mark140(started, "SELECTED_ROW_READY");
        for q in [1u64, 2, 3, 4, 5, 6, 7, 9, 823] {
            let anchor_started = Instant::now();
            let anchor = (q * 1024 + 959) as usize;
            let ell = q.min(8) as usize;
            assert_eq!(map.tier(anchor as u64).unwrap(), Some(ell));
            let anchor_inputs = native_inputs(&map, anchor as u64, &exports).unwrap();
            let anchor_symbolic = map.generate(anchor as u64, &anchor_inputs).unwrap();
            let anchor_packed = producer
                .produce_bank53_map_h21_for_test(anchor, &map, 0)
                .unwrap();
            let anchor_own_bits = check_packed_map(
                &anchor_packed,
                &anchor_symbolic,
                &plan,
                &map,
                anchor,
                &exports,
            );
            assert_eq!(anchor_own_bits, 288);
            own_import_bits += anchor_own_bits;
            assert_eq!(
                anchor_packed.class(),
                crate::daa_history_roster::OwnerClass::Carry
            );
            anchors_checked += 1;
            println!("C140_ANCHOR_PASS q={q} owner={anchor} ell={ell} imports={} bytes={} context=0 packed_s={:.6}", map.imports(anchor as u64).unwrap().len(), anchor_packed.packed_bytes().len(), anchor_started.elapsed().as_secs_f64());
            std::io::stdout().flush().expect("flush anchor progress");
            drop(anchor_packed);
        }
        assert_eq!(anchors_checked, 9);
        assert_eq!(own_import_bits, 224 + 9 * 288);
        mark140(started, "ANCHORS_READY");
        selected
    }; // Release the producer and its native caches before consumer construction.
    mark140(started, "PRODUCER_DROPPED");
    let selected_seconds = selected_started.elapsed().as_secs_f64();
    mark(started, "SELECTED_ROW_READY_PRODUCER_DROPPED");

    let consumer_started = Instant::now();
    let foreign = BTreeMap::new();
    assert!(imports.iter().all(|import| import.owner == owner as u64));
    validate_native_bank53_map_consumer(&plan, &prefix, &map, owner, 0, &packed, &foreign)
        .expect("selected-lower physical row and exact empty foreign census");
    let support_bit = match selector.branch {
        LowerBranch::Pivot(bit) => bit,
        LowerBranch::Equality => 0,
        LowerBranch::Literal => unreachable!(),
    };
    let mut altered_inputs = inputs.clone();
    altered_inputs.flip(imports[0], support_bit).unwrap();
    assert!(
        map.failures(&symbolic, &altered_inputs)
            .unwrap()
            .iter()
            .any(|(row, _)| *row
                == owner * (1 << 14)
                    + 10_123
                    + if selector.branch == LowerBranch::Equality {
                        support_bit
                    } else {
                        0
                    }),
        "selected lower relation physically supported by its own imported D"
    );
    let threshold = (&envelope.u + 4u8) / 3u8;
    let other_pivot = (0..224)
        .find(|bit| !threshold.bit(*bit as u64) && selector.branch != LowerBranch::Pivot(*bit))
        .unwrap();
    let wrong_pivot = Map::from_parent_modern_global_u(
        &plan,
        envelope.exponent,
        LowerSelector {
            source: selector.source,
            branch: LowerBranch::Pivot(other_pivot),
        },
    )
    .unwrap();
    // Cheap fixture distinctions only; these do not claim fresh native-consumer
    // mutant rejections. The unchanged c82 test covers that generic boundary.
    assert_ne!(wrong_pivot.binding(), map.binding());
    assert!(wrong_pivot
        .failures(&symbolic, &inputs)
        .unwrap_err()
        .contains("legacy map row binding"));
    assert_ne!(
        packed.owner(),
        owner + 1,
        "isolated requested-owner mismatch"
    );
    let mut wrong_import = packed.clone();
    flip_native_row_bit_for_test(&mut wrong_import, imports[0].local + support_bit).unwrap();
    let native_bit = exports
        .bit(map.input_index(imports[0], support_bit).unwrap())
        .unwrap();
    assert_ne!(
        packed_bit(wrong_import.packed_bytes(), imports[0].local + support_bit),
        native_bit,
        "isolated packed imported-bit disagreement"
    );
    let consumer_seconds = consumer_started.elapsed().as_secs_f64();
    mark(started, "CONSUMER_AND_FIXTURE_CHECKS_READY");
    println!("C140_NATIVE_GLOBAL_U_PILOT_PASS headers={} d_count={} b_count={} d_height={} d={} b_q={} b={} e={} u={} owner={} foreign=0 b_final_count={b_final_count} b_final_q9_negatives={b_final_q9_negatives} anchors={anchors_checked} own_import_bits={own_import_bits} metadata_negatives=2 consumer_calls=1 fixture_negatives=3 selected_lower_negative=1 b_final_s={b_final_seconds:.6} selected_s={selected_seconds:.6} consumer_s={consumer_seconds:.6} frame_sha256={FRAME_SHA256} global_x=false global_row=false pcs=false proof=false client=false",
        N, envelope.header_count, envelope.legacy_count, max_d.0, max_d.1, max_b.0, max_b.1,
        envelope.exponent, envelope.u, owner);
}

#[test]
#[ignore = "full pinned H21 frame; bounded pinned runner and independent review required"]
fn h21_pinned_q9_foreign_d_read_native_consumer() {
    let path = std::env::var_os("NIPOPOW_H21_FRAME").expect("pinned frame variable");
    let path = Path::new(&path);
    assert!(path.is_absolute());
    let before = fs::symlink_metadata(path).expect("frame metadata");
    assert!(before.is_file() && !before.file_type().is_symlink());
    assert_eq!(before.len(), FRAME_BYTES);
    let file = File::open(path).expect("pinned frame");
    assert_eq!(file.metadata().unwrap().len(), FRAME_BYTES);
    let mut frame = FrameReader::new(BufReader::with_capacity(CHUNK, file), FRAME_BYTES).unwrap();
    preamble(&mut frame, 1_827_839, N as u32).expect("exact ERFV preamble");
    let (prefix, extensions) = {
        let mut headers = HeaderIter::new(&mut frame, N);
        let prefix = NativePrefix::from_raw_iter(N, &mut headers).expect("linked native prefix");
        assert_eq!(headers.remaining, 0);
        (prefix, headers.extensions)
    };
    assert_eq!(prefix.header_count(), N);
    let parent_root_hex = prefix
        .root()
        .iter()
        .map(|byte| format!("{byte:02X}"))
        .collect::<String>();
    assert_eq!(
        parent_root_hex, "93F74871644F3644E8CCA9579C353006CB12FF50064F82E7660AB5AC552A307B",
        "c131 pinned native parent root"
    );
    let parent_total = prefix.total_be28();
    let parent_total_hex = parent_total
        .iter()
        .map(|byte| format!("{byte:02X}"))
        .collect::<String>();
    assert_eq!(
        parent_total_hex, "0000000000000000000000000000000000000094E7A1372670000000",
        "c131 pinned native parent total"
    );
    assert_eq!(frame.offset, PREFIX_BYTES);
    assert_eq!(extensions, EXTENSIONS);
    frame
        .finish(PREFIX_BYTES, TAIL_BYTES, FRAME_SHA256)
        .expect("entire pinned frame SHA256");
    let after = fs::symlink_metadata(path).unwrap();
    assert!(after.is_file() && !after.file_type().is_symlink());
    assert_eq!(after.len(), FRAME_BYTES);
    assert_eq!(after.modified().unwrap(), before.modified().unwrap());

    let plan =
        WorkTreeHistoryPlan::compile(N as u64, H, prefix.root(), prefix.total_be28()).unwrap();
    validate_native_plan_input(&plan, &prefix).expect("exact pinned native parent");
    let selector = LowerSelector {
        source: LowerSource::HeaderDifficulty { height: 841_729 },
        branch: LowerBranch::Pivot(54),
    };
    // c140's exact-frame fold already derived e55 and this selector. This
    // focused consumer reuses that result and does not replay the D/B roster.
    let map = Map::from_parent_modern_global_u(&plan, 55, selector).unwrap();
    let raw_selected = Map::new_modern_global_u_selected_lower(N as u64, H, 55, selector).unwrap();
    let owner = 10_175usize;
    assert_eq!(map.tier(owner as u64).unwrap(), Some(8));
    let imports = map.imports(owner as u64).unwrap();
    assert_eq!(imports.len(), 18, "exact q9 typed import census");
    assert_eq!(imports, raw_selected.imports(owner as u64).unwrap());
    assert_eq!(
        map.active_intervals(owner as u64).unwrap(),
        raw_selected.active_intervals(owner as u64).unwrap()
    );
    for import in &imports {
        for bit in 0..import.width {
            assert_eq!(
                map.input_index(*import, bit).unwrap(),
                raw_selected.input_index(*import, bit).unwrap(),
                "parent-bound selected-lower READ address {:?} bit{bit}",
                import
            );
        }
    }
    let d3070 = *imports
        .iter()
        .find(|i| i.owner == 3070 && i.kind == Kind::Difficulty)
        .expect("foreign D3070 import");
    assert_eq!(d3070.width, 224);

    let (q9_row, foreign_rows, reads, d3070_read_count) = {
        let exports = NativeExports::new_for_history(&plan, &prefix).unwrap();
        let inputs = native_inputs(&map, owner as u64, &exports).unwrap();
        let symbolic = map.generate(owner as u64, &inputs).unwrap();
        map.check_row(&symbolic).unwrap();
        let failures = map.failures(&symbolic, &inputs).unwrap();
        assert!(
            failures.is_empty(),
            "native q9 selected-lower symbolic residuals: {failures:?}"
        );

        let producer = NativeOwnerProducer::new_for_history(&plan, &prefix).unwrap();
        let q9_row = producer
            .produce_bank53_map_h21_for_test(owner, &map, 0)
            .unwrap();
        let _own_import_bits = check_packed_map(&q9_row, &symbolic, &plan, &map, owner, &exports);
        let foreign_owners = imports
            .iter()
            .filter(|i| i.owner != owner as u64)
            .map(|i| i.owner as usize)
            .collect::<BTreeSet<_>>();
        let mut foreign_rows = BTreeMap::new();
        for foreign_owner in foreign_owners {
            foreign_rows.insert(foreign_owner, producer.produce(foreign_owner).unwrap());
        }

        let mut reads = BTreeMap::new();
        let mut d3070_read_count = 0usize;
        for import in &imports {
            let source = if import.owner == owner as u64 {
                &q9_row
            } else {
                foreign_rows.get(&(import.owner as usize)).unwrap()
            };
            for bit in 0..import.width {
                let address = map.input_index(*import, bit).unwrap();
                let value = exports.bit(address).unwrap();
                assert!(
                    reads.insert(address, value).is_none(),
                    "duplicate q9 READ address {address}"
                );
                assert_eq!(
                    packed_bit(source.packed_bytes(), import.local + bit),
                    value,
                    "q9 typed native READ owner{} bit{bit}",
                    import.owner
                );
                if import.owner == 3070 && import.kind == Kind::Difficulty {
                    d3070_read_count += 1;
                }
            }
        }
        assert_eq!(reads.len(), 2_592, "all q9 imported READ addresses");
        assert_eq!(d3070_read_count, 224, "all foreign D3070 READ bits");
        (q9_row, foreign_rows, reads, d3070_read_count)
    }; // Drop producer, exports and input scratch before the physical consumer.

    assert_eq!(
        foreign_rows.keys().copied().collect::<BTreeSet<_>>(),
        imports
            .iter()
            .filter(|i| i.owner != owner as u64)
            .map(|i| i.owner as usize)
            .collect::<BTreeSet<_>>(),
        "exact foreign owner row census"
    );
    assert_eq!(reads.len(), 2_592);
    assert_eq!(d3070_read_count, 224);
    validate_native_bank53_map_consumer(&plan, &prefix, &map, owner, 0, &q9_row, &foreign_rows)
        .expect("native q9 foreign-READ physical consumer");

    assert_eq!(
        d3070.local,
        crate::legacy_envelope_map::D_LOCAL,
        "isolated mutation must target foreign D_LOCAL bit0"
    );
    let mut changed_foreign = foreign_rows.clone();
    flip_native_row_bit_for_test(changed_foreign.get_mut(&3070).unwrap(), d3070.local).unwrap();
    let error = validate_native_bank53_map_consumer(
        &plan,
        &prefix,
        &map,
        owner,
        0,
        &q9_row,
        &changed_foreign,
    )
    .unwrap_err();
    assert_eq!(
        error,
        "bank53 Map consumer typed import differs from native export owner3070 bit0"
    );
    println!("C144_Q9_NATIVE_CONSUMER_PASS owner={owner} imports=18 reads={} d3070_bits={} foreign_owners={}",
        reads.len(), d3070_read_count, foreign_rows.len());
    println!("C144_D3070_BIT0_NEGATIVE_PASS error={error}");
}

#[test]
fn h21_synthetic_global_u_bank53_lane_pretest() {
    const N: u64 = 1_827_840;
    const H: usize = 21;
    let root = [0x5au8; 32];
    let total = [0x31u8; 28];
    let plan = WorkTreeHistoryPlan::compile(N, H, root, total).unwrap();
    let map = Map::from_parent_modern_global_u(
        &plan,
        55,
        LowerSelector {
            source: LowerSource::HeaderDifficulty { height: 841_729 },
            branch: LowerBranch::Pivot(54),
        },
    )
    .unwrap();
    assert_eq!((map.n(), map.h()), (N, H));
    assert_eq!(map.binding().parent_root, Some(root));

    for q in [1u64, 2, 3, 4, 5, 6, 7, 9, 823] {
        let owner = 1024 * q + 959;
        let ell = q.min(8) as usize;
        assert_eq!(map.tier(owner).unwrap(), Some(ell), "q={q} owner={owner}");

        let mut expected = BTreeSet::from([Import {
            owner,
            local: crate::legacy_envelope_map::D_LOCAL,
            width: 224,
            kind: Kind::Difficulty,
        }]);
        for i in 0..ell {
            let d_owner = if i + 1 == ell {
                1024 * q + 958
            } else {
                1024 * (q - ell as u64 + 1 + i as u64) + 1022
            };
            let t_owner = 1024 * (q - ell as u64 + i as u64) + 1023;
            expected.insert(Import {
                owner: d_owner,
                local: crate::legacy_envelope_map::D_LOCAL,
                width: 224,
                kind: Kind::Difficulty,
            });
            expected.insert(Import {
                owner: t_owner,
                local: crate::legacy_envelope_map::T_LOCAL,
                width: 64,
                kind: Kind::Timestamp,
            });
        }
        expected.insert(Import {
            owner,
            local: crate::legacy_envelope_map::T_LOCAL,
            width: 64,
            kind: Kind::Timestamp,
        });
        let imports = map
            .imports(owner)
            .unwrap()
            .into_iter()
            .collect::<BTreeSet<_>>();
        assert_eq!(imports, expected, "q={q} exact typed imports");
        assert!(
            imports.iter().all(|import| import.owner < N),
            "q={q} import range"
        );

        validate_h21_bank53_map_lane_for_test(&plan, owner as usize, 0)
            .expect("exact H21 owner/context lane preflight");
        let action = crate::daa_header_window::for_child_height((owner + 1) as u32)
            .unwrap()
            .action();
        println!(
            "C140_LANE q={q} owner={owner} ell={ell} imports={} context=0 action={action:?}",
            imports.len()
        );
    }

    assert_eq!(
        validate_h21_bank53_map_lane_for_test(&plan, 1usize << H, 0).unwrap_err(),
        "H21 Bank53 test owner/context outside reserved domain"
    );
    println!("C140_NEGATIVE invalid_owner={} rejected=true", 1usize << H);
}

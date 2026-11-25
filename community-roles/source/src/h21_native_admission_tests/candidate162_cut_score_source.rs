//! Source-bound scalar Score reducer for the two existing H21 cuts.
//! Authority: draft 0.8 Eq19/21/26, exact local draft read 2026-10-20.
//! Eq26 AB applies only to context 1; context 0 is a sampled Score guard.
//! Test-only: no native frame run, physical Score admission, common X or proof.
use num_bigint::BigUint;
use crate::{
    h21_scheduled_max_cap::{CutDescriptor,ScoreSpan},
    native_v_max_cap_loan::NativeVLoan,
    origin_score_map::maturity,
    packed_owner_assembly::{validate_native_plan_input, NativePrefix},
    work_tree_history_plan::WorkTreeHistoryPlan,
};

const PARENT_HEADERS:usize=1_827_840;

/// Private sealed adapter: production values come only from interval(origin).
/// A separate fixture below supplies explicitly synthetic work coordinates.
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(in crate::h21_native_admission_tests) struct ParentIdentity {
    pub(in crate::h21_native_admission_tests) headers:usize,
    pub(in crate::h21_native_admission_tests) slot_log:usize,
    pub(in crate::h21_native_admission_tests) root:[u8;32],
    pub(in crate::h21_native_admission_tests) total:[u8;28],
    pub(in crate::h21_native_admission_tests) profile:[u8;32],
}
trait WorkSource {
    fn identity(&self)->ParentIdentity;
    fn work(&self,origin:usize)->Result<BigUint,String>;
}
impl WorkSource for NativePrefix {
    fn identity(&self)->ParentIdentity {
        ParentIdentity {headers:self.header_count(),slot_log:self.slot_count().trailing_zeros() as usize,
            root:self.root(),total:self.total_be28(),profile:self.profile()}
    }
    fn work(&self,origin:usize)->Result<BigUint,String> {
        self.interval(origin).map(|(_,upper)|BigUint::from_bytes_be(&upper))
    }
}

#[derive(Clone,Debug,PartialEq,Eq)]
struct ScalarRow {descriptor:CutDescriptor,parent:ParentIdentity,context:usize,origin:usize,w:BigUint,v:BigUint,a:BigUint}

struct CutSource<'a> {
    descriptor:CutDescriptor,
    work:&'a dyn WorkSource,
    parent:ParentIdentity,
    context:usize,
    u:BigUint,
    spans:Vec<ScoreSpan>,
}

#[derive(Clone,Debug,PartialEq,Eq)]
pub(in crate::h21_native_admission_tests) struct CutScore {
    pub(in crate::h21_native_admission_tests) descriptor:CutDescriptor,
    pub(in crate::h21_native_admission_tests) parent:ParentIdentity,
    pub(in crate::h21_native_admission_tests) context:usize,
    pub(in crate::h21_native_admission_tests) terminal:usize,
    pub(in crate::h21_native_admission_tests) last_origin:usize,
    pub(in crate::h21_native_admission_tests) modern_spans:usize,
    pub(in crate::h21_native_admission_tests) global_u:BigUint,
    pub(in crate::h21_native_admission_tests) work_at_cut:BigUint,
    pub(in crate::h21_native_admission_tests) t1:BigUint,
    pub(in crate::h21_native_admission_tests) t2:BigUint,
    pub(in crate::h21_native_admission_tests) premodern:BigUint,
    pub(in crate::h21_native_admission_tests) maximum:BigUint,
    /// Eq21 is a guard only in context 0. Eq26 AB in context 1 may exceed WB.
    pub(in crate::h21_native_admission_tests) sampled_guard:Option<bool>,
}

impl CutSource<'_> {
    fn validate(&self)->Result<(),String> {
        if self.parent!=self.work.identity()||self.parent.headers!=self.descriptor.terminals()[0]||self.parent.slot_log!=21 {
            return Err("Score source parent identity".into());
        }
        if self.context>=2||self.u==BigUint::from(0u8)||self.u>(BigUint::from(1u8)<<64usize) {
            return Err("Score context/global-U range".into());
        }
        let mut next=self.descriptor.modern_start();
        let mut previous=self.u.clone();
        for span in &self.spans {
            if span.first!=next||span.last<span.first||span.last>self.descriptor.guards()[self.context]
                ||span.value==BigUint::from(0u8)||span.value>previous {
                return Err("Score exhaustive V partition/range/monotonicity".into());
            }
            next=span.last+1;previous=span.value.clone();
        }
        if next!=self.descriptor.guards()[self.context]+1 {return Err("Score V partition missing tail".into());}
        Ok(())
    }

    fn row(&self,origin:usize)->Result<ScalarRow,String> {
        if self.context>=2||origin==0||origin>self.descriptor.guards()[self.context] {
            return Err("Score source origin/context".into());
        }
        let v=if origin<self.descriptor.modern_start() {self.u.clone()} else {
            let j=self.spans.partition_point(|s|s.last<origin);
            let span=self.spans.get(j).filter(|s|s.first<=origin).ok_or("Score source missing origin V")?;
            span.value.clone()
        };
        let w=self.work.work(origin)?;
        if w.bits()>224 {return Err("Score W source U224".into());}
        let mode=self.descriptor.maturity_mode(self.context)?;
        let a=&w+&v*maturity(mode,origin as u64);
        if a.bits()>225 {return Err("Score source U225".into());}
        Ok(ScalarRow {descriptor:self.descriptor,parent:self.parent,context:self.context,origin,w,v,a})
    }

    /// No destination row can substitute a different cut or an omitted origin.
    fn validate_destination(&self,expected_origin:usize,row:&ScalarRow)->Result<(),String> {
        if row.descriptor!=self.descriptor {return Err("Score destination descriptor".into());}
        if row.context!=self.context||row.origin!=expected_origin {
            return Err("Score destination context/origin".into());
        }
        if row.parent!=self.parent {return Err("Score destination parent".into());}
        if *row!=self.row(expected_origin)? {return Err("Score destination source/value".into());}
        Ok(())
    }

    /// Exhaustive equivalence argument (not an inference from finite fixtures):
    /// NativePrefix sums positive native D, so W(i+1)>W(i), with W(1)=0.
    /// Before MODERN, V is the one source-folded U. Split at 417791 and
    /// 845759, the exact maturity boundaries. Thereafter Prepared verifies
    /// every D in each difficulty epoch is equal. For i in [a+1088,b+1088]
    /// from an epoch [a,b], Eq19's lower endpoint remains in that epoch;
    /// therefore max(D[i-1088..terminal]) is its Prepared suffix MAX, and
    /// gridceil(floor(3 MAX/2)) is constant throughout that whole interval.
    /// Modern maturity is constant. Every Score interval thus has constant
    /// m*V and strictly increasing W; its maximum is its right endpoint.
    /// The spans partition every modern origin without gaps, including the
    /// singleton and the clipped final span. The two old-zone endpoints plus
    /// those modern endpoints exhaust the maximum. No V monotonicity alone
    /// is used to discard an interior origin.
    fn reduce(&self,compressed:bool)->Result<CutScore,String> {
        self.validate()?;
        let mut maximum=BigUint::from(0u8);
        let mut premodern=BigUint::from(0u8);
        let mut consume=|i|->Result<(),String> {
            let row=self.row(i)?;
            if i<self.descriptor.modern_start() {premodern=premodern.clone().max(row.a.clone());}
            maximum=maximum.clone().max(row.a);Ok(())
        };
        if compressed {
            consume(417_791)?;consume(self.descriptor.modern_start()-1)?;
            for span in &self.spans {consume(span.last)?;}
        } else {
            let mut previous=BigUint::from(0u8);
            for i in 1..=self.descriptor.guards()[self.context] {
                let current=self.work.work(i)?;
                if (i==1&&current!=BigUint::from(0u8))||(i>1&&current<=previous) {
                    return Err("Score zero-genesis/positive work source".into());
                }
                previous=current;consume(i)?;
            }
        }
        let work_at_cut=self.work.work(self.descriptor.terminals()[self.context])?;
        Ok(CutScore {descriptor:self.descriptor,parent:self.parent,context:self.context,terminal:self.descriptor.terminals()[self.context],
            last_origin:self.descriptor.guards()[self.context],modern_spans:self.spans.len(),global_u:self.u.clone(),t1:self.work.work(417_791)?,
            t2:self.work.work(self.descriptor.modern_start()-1)?,premodern,maximum:maximum.clone(),
            sampled_guard:if self.context==0 {Some(maximum<=work_at_cut)}else{None},work_at_cut})
    }
}

/// No caller supplies U, W, V, Prepared, cut, maturity, expected AB or total.
/// NativePrefix custody remains the caller's separate authentication boundary.
/// This entry point has not been executed on the pinned native frame.
fn reduce_native_cut_pair(plan:&WorkTreeHistoryPlan,prefix:&NativePrefix)->Result<[CutScore;2],String> {
    reduce_native_with_descriptor(plan,prefix,CutDescriptor::diagnostic08())
}

pub(in crate::h21_native_admission_tests) fn reduce_native_cut_pair_eligible08(plan:&WorkTreeHistoryPlan,prefix:&NativePrefix)->Result<[CutScore;2],String> {
    reduce_native_with_descriptor(plan,prefix,CutDescriptor::eligible08())
}

fn reduce_native_with_descriptor(plan:&WorkTreeHistoryPlan,prefix:&NativePrefix,
    descriptor:CutDescriptor,
)->Result<[CutScore;2],String> {
    validate_native_plan_input(plan,prefix)?;
    let diagnostic=descriptor==CutDescriptor::diagnostic08();
    let cuts=if diagnostic {super::fold_native_global_u_cut_pair(plan,prefix)?}
        else {super::fold_native_global_u_cut_pair_eligible08(plan,prefix)?};
    let v=if diagnostic {NativeVLoan::issue(plan,prefix)?}
        else {NativeVLoan::issue_eligible08(plan,prefix)?}; // one full D replay for both cuts
    let mut results=Vec::with_capacity(2);
    for context in 0..2 {
        cuts[context].validate_source(descriptor,context,plan,prefix)?;
        let spans=if diagnostic {v.score_spans(plan,prefix,context)?}
            else {v.score_spans_eligible08(plan,prefix,context)?};
        let source=CutSource {descriptor,work:prefix,parent:prefix.identity(),context,u:cuts[context].envelope.u.clone(),spans};
        // Use the exhaustive interval argument above only for this validated
        // NativePrefix/Prepared route, never for an arbitrary caller's words.
        results.push(source.reduce(true)?);
    }
    results.try_into().map_err(|_|"Score native result pair".into())
}

/// A scalar result is not an Eq21 admission when the explicit guard is false.
/// The existing fixed diagnostic geometry need not satisfy that guard.
pub(in crate::h21_native_admission_tests) fn admit_sampled_guard(expected:CutDescriptor,result:&CutScore)->Result<(),String> {
    if result.descriptor!=expected||result.context!=0||result.terminal!=expected.terminals()[0]||result.last_origin!=expected.guards()[0]
        ||result.sampled_guard!=Some(true)||result.maximum>result.work_at_cut {
        return Err("Score sampled Eq21 guard".into());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::h21_scheduled_max_cap::Prepared;
    // Independent diagnostic oracle pins, never production cut geometry.
    const TERMINAL:[usize;2]=[1_827_840,1_827_775];
    const LAST_ORIGIN:[usize;2]=[1_827_838,1_827_775];
    const MODERN:usize=845_760;

    // Entire H21 domain, with D constant in each actual scheduled epoch and
    // generally falling, with future high epochs that dominate earlier D.
    // Integer oracle does not call Score/Cap/Prepared arithmetic helpers.
    fn epoch(h:usize)->usize {if h==844_672 {0}else{1+(h-844_673)/128}}
    fn difficulty(h:usize)->u64 {
        let j=epoch(h);10_000-j as u64+if j==3000||j==6000 {10_000}else{0}
    }
    struct Fixture {prefix:Vec<u64>,prepared:Prepared}
    impl Fixture {
        fn new()->Self {
            let mut prefix=vec![0u64;TERMINAL[0]+1];
            for h in 2..=TERMINAL[0] {
                let d=if h<844_672 {1}else{difficulty(h)};
                prefix[h]=prefix[h-1]+d;
            }
            let prepared=Prepared::from_d_iter((844_672..=TERMINAL[0]).map(|h|(h,BigUint::from(difficulty(h))))).unwrap();
            Self {prefix,prepared}
        }
        fn source(&self,context:usize)->CutSource<'_> {
            self.source_for(CutDescriptor::diagnostic08(),context)
        }
        fn source_for(&self,descriptor:CutDescriptor,context:usize)->CutSource<'_> {
            let spans=if descriptor==CutDescriptor::diagnostic08() {self.prepared.score_spans(context).unwrap()}
                else {Prepared::from_d_iter_eligible08((844_672..=PARENT_HEADERS)
                    .map(|h|(h,BigUint::from(difficulty(h))))).unwrap().score_spans(context).unwrap()};
            CutSource {descriptor,work:self,parent:self.identity(),context,u:BigUint::from(32_768u64),spans}
        }
        fn independent_suffix(&self,context:usize)->Vec<u64> {
            let mut suffix=vec![0u64;TERMINAL[context]+2];
            for h in (844_672..=TERMINAL[context]).rev() {
                suffix[h]=difficulty(h).max(suffix[h+1]);
            }
            suffix
        }
        fn independent(&self,context:usize)->(u64,u64) {
            self.independent_for(CutDescriptor::diagnostic08(),context)
        }
        fn independent_for(&self,descriptor:CutDescriptor,context:usize)->(u64,u64) {
            // A per-height reverse fold is independent of Prepared's epoch
            // projection. Spell out dyadic ceil and maturity independently.
            let terminal=descriptor.terminals()[context];
            let mut suffix=vec![0u64;terminal+2];
            for h in (844_672..=terminal).rev() {suffix[h]=difficulty(h).max(suffix[h+1]);}
            let mut maximum=0u64;let mut old=0u64;
            for i in 1..=descriptor.guards()[context] {
                let v=if i<MODERN {32_768}else {
                    let floor=3*suffix[i-1088]/2;
                    floor.next_power_of_two()
                };
                let m=match (context,i) {
                    (0,1..=417_791)=>43_410,(0,417_792..=845_759)=>23_155,(0,_)=>4_995,
                    (1,1..=417_791)=>17_867,(1,417_792..=845_759)=>9_548,(1,_)=>2_090,
                    _=>unreachable!(),
                };
                let a=self.prefix[i]+m*v;
                maximum=maximum.max(a);if i<MODERN {old=old.max(a);}
            }
            (maximum,old)
        }
    }
    impl WorkSource for Fixture {
        fn identity(&self)->ParentIdentity {
            let mut total=[0u8;28];total[20..].copy_from_slice(&self.prefix[TERMINAL[0]].to_be_bytes());
            ParentIdentity {headers:TERMINAL[0],slot_log:21,root:[0x62;32],total,profile:[0x63;32]}
        }
        fn work(&self,origin:usize)->Result<BigUint,String> {
            self.prefix.get(origin).map(|n|BigUint::from(*n)).ok_or("fixture work absent".into())
        }
    }

    #[test]
    fn c162_full_domain_all_origin_matches_retained_and_independent_arithmetic() {
        let fixture=Fixture::new();
        for context in 0..2 {
            let source=fixture.source(context);
            let all=source.reduce(false).unwrap();
            let retained=source.reduce(true).unwrap();
            assert_eq!(all,retained);
            assert_eq!(all.global_u,source.u);
            assert_eq!(all.modern_spans,source.spans.len());
            let (maximum,old)=fixture.independent(context);
            assert_eq!(all.maximum,BigUint::from(maximum));
            assert_eq!(all.premodern,BigUint::from(old));
            assert_eq!(all.t1,BigUint::from(fixture.prefix[417_791]));
            assert_eq!(all.t2,BigUint::from(fixture.prefix[845_759]));
            if context==0 {
                assert_eq!(all.sampled_guard,Some(all.maximum<=all.work_at_cut));
                assert_eq!(admit_sampled_guard(CutDescriptor::diagnostic08(),&all).is_ok(),all.maximum<=all.work_at_cut);
            }
            else {assert!(all.maximum>all.work_at_cut);assert_eq!(all.sampled_guard,None);}
        }
    }

    #[test]
    fn c162_singleton_seams_maturities_and_clipped_tail_cover_every_origin() {
        let fixture=Fixture::new();
        for context in 0..2 {
            let source=fixture.source(context);
            let suffix=fixture.independent_suffix(context);
            assert_eq!(source.spans.len(),if context==0 {7674}else{7673});
            assert_eq!((source.spans[0].first,source.spans[0].last),(845_760,845_760));
            assert_eq!((source.spans[1].first,source.spans[1].last),(845_761,845_888));
            let tail=source.spans.last().unwrap();
            assert_eq!(tail.last,LAST_ORIGIN[context]);
            assert!(tail.last-tail.first<127);
            for i in [1,417_791,417_792,845_759,845_760,845_761,845_888,845_889,tail.first,tail.last] {
                let row=source.row(i).unwrap();
                let expected_v=if i<MODERN {32_768}else{(3*suffix[i-1088]/2).next_power_of_two()};
                let m=if context==0 {if i<417_792 {43_410}else if i<MODERN {23_155}else{4_995}}
                    else if i<417_792 {17_867}else if i<MODERN {9_548}else{2_090};
                assert_eq!(row.v,BigUint::from(expected_v));
                assert_eq!(row.a,BigUint::from(fixture.prefix[i]+m*expected_v));
                source.validate_destination(i,&row).unwrap();
            }
            assert!(source.row(LAST_ORIGIN[context]+1).is_err());
        }
    }

    #[test]
    fn c162_omitted_interior_value_destination_and_different_cut_are_rejected() {
        let fixture=Fixture::new();
        let source=fixture.source(1);let other=fixture.source(0);
        let interior=845_800;
        assert!(!source.spans.iter().any(|s|s.last==interior));
        let row=source.row(interior).unwrap();
        let mut bad=row.clone();bad.v+=1u8;
        bad.a=&bad.w+&bad.v*2_090u64; // coordinated Score change cannot hide V drift
        assert_eq!(source.validate_destination(interior,&bad).unwrap_err(),"Score destination source/value");
        let mut bad=row.clone();bad.origin+=1;
        assert_eq!(source.validate_destination(interior,&bad).unwrap_err(),"Score destination context/origin");
        let mut bad=row.clone();bad.context=0;
        assert_eq!(source.validate_destination(interior,&bad).unwrap_err(),"Score destination context/origin");
        assert_eq!(source.validate_destination(interior,&other.row(interior).unwrap()).unwrap_err(),"Score destination context/origin");
        let mut bad=row.clone();bad.w+=1u8;bad.a+=1u8;
        assert_eq!(source.validate_destination(interior,&bad).unwrap_err(),"Score destination source/value");
        let mut bad=row.clone();bad.parent.root[0]^=1;
        assert_eq!(source.validate_destination(interior,&bad).unwrap_err(),"Score destination parent");
        for field in 0..5 {
            let mut altered=fixture.source(1);
            match field {0=>altered.parent.headers-=1,1=>altered.parent.slot_log-=1,
                2=>altered.parent.root[0]^=1,3=>altered.parent.total[0]^=1,_=>altered.parent.profile[0]^=1};
            assert_eq!(altered.validate().unwrap_err(),"Score source parent identity");
        }
        // Same U and same long shared initial spans do not authorize cut swap.
        let swapped=CutSource {descriptor:source.descriptor,work:&fixture,parent:fixture.identity(),context:1,u:source.u.clone(),spans:other.spans};
        assert_eq!(swapped.validate().unwrap_err(),"Score exhaustive V partition/range/monotonicity");
        let mut missing=fixture.source(1);missing.spans.remove(1);
        assert_eq!(missing.validate().unwrap_err(),"Score exhaustive V partition/range/monotonicity");
        // Tampering with D inside the source epoch of an omitted origin must
        // fail before any retained-endpoint compression can be constructed.
        let altered=Prepared::from_d_iter((844_672..=TERMINAL[0]).map(|h| {
            (h,BigUint::from(difficulty(h)+u64::from(h==interior-1088)))
        }));
        assert_eq!(altered.err().unwrap(),"scheduled D changes within epoch");
    }

    #[test]
    fn c165_eligible_dense_compressed_and_independent_all_height_arithmetic() {
        let fixture=Fixture::new();
        let descriptor=CutDescriptor::eligible08();
        assert_eq!(descriptor.terminals(),[1_827_840,1_810_842]);
        assert_eq!(descriptor.guards(),[1_810_905,1_810_842]);
        assert_eq!(descriptor.modern_start(),845_760);
        assert!(descriptor.maturity_mode(2).is_err());
        for context in 0..2 {
            let source=fixture.source_for(descriptor,context);
            let dense=source.reduce(false).unwrap();
            assert_eq!(dense,source.reduce(true).unwrap());
            assert_eq!(dense.global_u,source.u);
            assert_eq!(dense.modern_spans,source.spans.len());
            let (maximum,old)=fixture.independent_for(descriptor,context);
            assert_eq!(dense.maximum,BigUint::from(maximum));
            assert_eq!(dense.premodern,BigUint::from(old));
            assert_eq!(source.spans.len(),[7542,7541][context]);
            assert_eq!(source.spans.first().map(|s|(s.first,s.last)),Some((845_760,845_760)));
            assert_eq!(source.spans.last().unwrap().last,descriptor.guards()[context]);
            assert_eq!(dense.terminal,descriptor.terminals()[context]);
            assert_eq!(dense.last_origin,descriptor.guards()[context]);
            assert_eq!(dense.t1,BigUint::from(fixture.prefix[417_791]));
            assert_eq!(dense.t2,BigUint::from(fixture.prefix[845_759]));
            if context==1 {assert!(dense.maximum>dense.work_at_cut);assert_eq!(dense.sampled_guard,None);}
        }
    }

    struct FlatFixture {prefix:Vec<u64>,peak:bool}
    impl FlatFixture {
        fn new()->Self {Self::with_peak(false)}
        fn with_peak(peak:bool)->Self {
            let mut fixture=Self {prefix:vec![0;PARENT_HEADERS+1],peak};
            for h in 2..=PARENT_HEADERS {fixture.prefix[h]=fixture.prefix[h-1]+fixture.difficulty(h);}
            fixture
        }
        fn difficulty(&self,h:usize)->u64 {
            if self.peak&&(1_820_033..=1_820_160).contains(&h) {64}else{16}
        }
        fn source(&self,descriptor:CutDescriptor,context:usize)->CutSource<'_> {
            // The peak is after eligible h, and is a whole scheduled epoch.
            let values=(844_672..=PARENT_HEADERS).map(|h|(h,BigUint::from(self.difficulty(h))));
            let prepared=Prepared::from_d_iter_with_descriptor(descriptor,values).unwrap();
            // A tiny scalar fixture scale: independently fold each cut's D.
            // The separate c138 roster fixture includes real protocol literals.
            let maximum=(2..=descriptor.terminals()[context]).map(|h|self.difficulty(h)).max().unwrap();
            let u=(3*maximum/2).next_power_of_two();
            CutSource {descriptor,work:self,parent:self.identity(),context,u:BigUint::from(u),
                spans:prepared.score_spans(context).unwrap()}
        }
    }
    impl WorkSource for FlatFixture {
        fn identity(&self)->ParentIdentity {
            let mut total=[0u8;28];total[20..].copy_from_slice(&self.prefix[PARENT_HEADERS].to_be_bytes());
            ParentIdentity {headers:PARENT_HEADERS,slot_log:21,root:[0x65;32],total,profile:[0x66;32]}
        }
        fn work(&self,origin:usize)->Result<BigUint,String> {
            self.prefix.get(origin).map(|w|BigUint::from(*w)).ok_or("flat fixture absent".into())
        }
    }

    #[test]
    fn c165_flat_d_eligible_guard_pass_diagnostic_fail_and_exact_ab_separate() {
        let fixture=FlatFixture::new();
        for descriptor in [CutDescriptor::diagnostic08(),CutDescriptor::eligible08()] {
            let source=fixture.source(descriptor,0);
            let score=source.reduce(false).unwrap();
            assert_eq!(score,source.reduce(true).unwrap());
            // Independent per-height arithmetic; D=16 gives ceil(3D/2)=32.
            let mut maximum=0u64;
            for i in 1..=descriptor.guards()[0] {
                let m=if i<417_792 {43_410}else if i<845_760 {23_155}else{4_995};
                maximum=maximum.max(16*(i-1) as u64+32*m);
            }
            assert_eq!(score.maximum,BigUint::from(maximum));
            assert_eq!(admit_sampled_guard(descriptor,&score).is_ok(),descriptor==CutDescriptor::eligible08());
            let exact=fixture.source(descriptor,1).reduce(true).unwrap();
            assert!(exact.maximum>exact.work_at_cut);
            assert!(admit_sampled_guard(descriptor,&exact).is_err());
            let wrong=if descriptor==CutDescriptor::eligible08() {CutDescriptor::diagnostic08()}else{CutDescriptor::eligible08()};
            assert!(admit_sampled_guard(wrong,&score).is_err());
        }
    }

    #[test]
    fn c165_eligible_descriptor_context_parent_and_coordinated_values_reject() {
        let fixture=Fixture::new();let descriptor=CutDescriptor::eligible08();
        let source=fixture.source_for(descriptor,1);let interior=845_800;
        let row=source.row(interior).unwrap();
        let mut bad=row.clone();bad.descriptor=CutDescriptor::diagnostic08();
        assert_eq!(source.validate_destination(interior,&bad).unwrap_err(),"Score destination descriptor");
        let mut bad=row.clone();bad.context=0;
        assert_eq!(source.validate_destination(interior,&bad).unwrap_err(),"Score destination context/origin");
        let mut bad=row.clone();bad.parent.profile[0]^=1;
        assert_eq!(source.validate_destination(interior,&bad).unwrap_err(),"Score destination parent");
        let mut bad=row.clone();bad.v+=1u8;bad.a=&bad.w+&bad.v*2_090u64;
        assert_eq!(source.validate_destination(interior,&bad).unwrap_err(),"Score destination source/value");
        let mut bad=row.clone();bad.w+=1u8;bad.a+=1u8;
        assert_eq!(source.validate_destination(interior,&bad).unwrap_err(),"Score destination source/value");
        let mut missing=fixture.source_for(descriptor,1);missing.spans.remove(1);
        assert_eq!(missing.validate().unwrap_err(),"Score exhaustive V partition/range/monotonicity");
        let mut wrong=fixture.source_for(descriptor,1);wrong.descriptor=CutDescriptor::diagnostic08();
        assert_eq!(wrong.validate().unwrap_err(),"Score V partition missing tail");
        let mut changed=fixture.source_for(descriptor,1);changed.parent.total[0]^=1;
        assert_eq!(changed.validate().unwrap_err(),"Score source parent identity");
        let altered=Prepared::from_d_iter_eligible08((844_672..=PARENT_HEADERS).map(|h| {
            (h,BigUint::from(difficulty(h)+u64::from(h==interior-1088)))
        }));
        assert_eq!(altered.err().unwrap(),"scheduled D changes within epoch");
    }

    #[test]
    fn c165_peak_after_eligible_h_changes_only_context_zero_suffix_and_u() {
        let fixture=FlatFixture::new();let changed=FlatFixture::with_peak(true);let descriptor=CutDescriptor::eligible08();
        for context in 0..2 {
            let base=fixture.source(descriptor,context);
            let peak=changed.source(descriptor,context);
            let base_row=base.row(1_810_000).unwrap();
            let peak_row=peak.row(1_810_000).unwrap();
            if context==0 {
                assert_ne!(base_row.v,peak_row.v);assert_ne!(base.u,peak.u);
                assert_ne!(base.reduce(true).unwrap().maximum,peak.reduce(true).unwrap().maximum);
            } else {
                assert_eq!((&base_row.w,&base_row.v,&base_row.a),(&peak_row.w,&peak_row.v,&peak_row.a));
                assert_eq!(base.u,peak.u);
                let a=base.reduce(true).unwrap();let b=peak.reduce(true).unwrap();
                assert_eq!((a.maximum,a.work_at_cut),(b.maximum,b.work_at_cut));
            }
            assert_eq!(base.validate_destination(1_810_000,&peak_row).unwrap_err(),"Score destination parent");
        }
    }
}

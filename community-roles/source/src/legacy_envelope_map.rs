//! Symbolic diagnostic map. Imported native Boolean/decode premises are retained,
//! not established here. No dense X, Circuit, proof or protocol-U admission.
use ark_bn254::Fr;
use ark_ff::{BigInteger, One, PrimeField, Zero};
use num_bigint::{BigInt, BigUint, Sign};
use num_traits::{Signed, ToPrimitive};
use std::collections::BTreeMap;
use crate::{gkr::Gate, sparse::Term, wiring::{evaluate_shift, RightIndex}};

pub(crate) const BASE: usize = 655654;
pub(crate) const BANK: usize = 7898;
pub(crate) const RATIO: usize = 656327;
pub(crate) const PRED: usize = 660351;
pub(crate) const SMAX: usize = 661133;
pub(crate) const D_LOCAL: usize = 987674;
pub(crate) const T_LOCAL: usize = 525330;
pub(crate) const I: u128 = 1199990374400;
pub(crate) const TE: i64 = 122880000;
const P: i64 = 1000000000;
const CONTRACT: &str = "1AC18112EC82D0E770D6501EACA59A15194EAA1BE756CADBC8F9312E8EE9EDE6";
const MODERN_GLOBAL_U_CONTRACT: &str = "MODERN_GLOBAL_U_D_UPPER_FLOOR_2U_PLUS_1_OVER_3_B_UPPER_U_V2";
const MODERN_GLOBAL_U_SELECTED_LOWER_CONTRACT: &str = "MODERN_GLOBAL_U_SELECTED_LOWER_D_GE_CEIL_U_PLUS_2_OVER_3_B_GT_FLOOR_U_OVER_2_V1";
const WIDTH: u64 = 1 << 20;
const ROWS: u64 = 1 << 14;
#[cfg(test)]
const FILTERED_HELPER_BASE: usize = 671744;
#[cfg(test)]
const FILTERED_LIVE: usize = 5757;

fn f(x: i64) -> Fr {
    if x < 0 { -Fr::from(x.unsigned_abs()) } else { Fr::from(x as u64) }
}
fn fc(x: u128) -> Fr { Fr::from_le_bytes_mod_order(&x.to_le_bytes()) }
pub(crate) fn eq(p: &[Fr], x: u64) -> Fr {
    p.iter().enumerate().fold(Fr::one(), |a, (b, z)| {
        a * if (x >> b) & 1 == 1 { *z } else { Fr::one() - z }
    })
}
fn joint(r: &[Fr], u: &[Fr], v: &[Fr]) -> Fr {
    r.iter().zip(u).zip(v).fold(Fr::one(), |a, ((r, u), v)| {
        a * ((Fr::one()-r)*(Fr::one()-u)*(Fr::one()-v) + r*u*v)
    })
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Binding {
    pub(crate) n: u64,
    pub(crate) h: usize,
    pub(crate) e: usize,
    pub(crate) parent_root: Option<[u8;32]>,
    d_upper_mode: DUpperMode,
    lower_selector: Option<LowerSelector>,
    contract: &'static str,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum DUpperMode { LegacyDiagnostic, ModernGlobalU, ModernGlobalUSelectedLower }
// Descriptor-only mutants isolate private equality fields. They cannot mint
// a Map, complete native source, reader view or verifier-success handle.
#[cfg(test)]
impl Binding {
    pub(crate) fn mutated_private_field_for_test(&self, field: usize) -> Self {
        let mut wrong = self.clone();
        match field {
            0 => wrong.d_upper_mode = match self.d_upper_mode {
                DUpperMode::ModernGlobalUSelectedLower => DUpperMode::ModernGlobalU,
                _ => DUpperMode::ModernGlobalUSelectedLower,
            },
            1 => wrong.lower_selector = None,
            2 => {
                let selector = wrong.lower_selector.as_mut().expect("selected lower fixture");
                let LowerSource::HeaderDifficulty { height } = &mut selector.source
                    else { panic!("header lower fixture"); };
                *height = height.checked_add(1).expect("fixture height");
            },
            3 => wrong.lower_selector.as_mut().expect("selected lower fixture").branch = LowerBranch::Equality,
            4 => {
                let selector = wrong.lower_selector.as_mut().expect("selected lower fixture");
                let LowerBranch::Pivot(pivot) = selector.branch else { panic!("pivot fixture"); };
                selector.branch = LowerBranch::Pivot(pivot.checked_sub(2).expect("fixture pivot"));
            },
            5 => wrong.contract = "isolated-map-binding-test-contract",
            _ => panic!("unknown private binding field"),
        }
        wrong
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum LowerSource {
    HeaderDifficulty { height: u64 },
    LegacyBound { q: u64 },
    InitialI,
    Reset417792,
    Reset417793,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum LowerBranch { Literal, Equality, Pivot(usize) }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct LowerSelector { pub(crate) source: LowerSource, pub(crate) branch: LowerBranch }
#[derive(Clone, Debug)]
pub(crate) struct Map { binding: Binding }
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Kind { Difficulty, Timestamp }
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Import {
    pub(crate) owner: u64,
    pub(crate) local: usize,
    pub(crate) width: usize,
    pub(crate) kind: Kind,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Owner { Destination, Shift { d: u64, low: u64 } }
#[derive(Clone, Copy, Debug)]
enum Word { Bits { owner: Owner, base: usize, width: usize }, Constant(u128) }
impl Word {
    fn bit(self, b: usize) -> Self {
        match self {
            Self::Bits { owner, base, width } if b < width =>
                Self::Bits { owner, base: base+b, width: 1 },
            Self::Bits { .. } => Self::Constant(0),
            Self::Constant(x) => Self::Constant(if b < 128 { (x>>b)&1 } else {0}),
        }
    }
}
fn local(base: usize, width: usize) -> Word {
    Word::Bits { owner: Owner::Destination, base, width }
}
fn source(d: u64, low: u64, base: usize, width: usize) -> Word {
    Word::Bits { owner: Owner::Shift {d,low}, base, width }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Scope { All, Work, Anchor(usize), ExactOwner(u64) }

impl Map {
    pub(crate) fn new(n: u64, h: usize, e: usize) -> Result<Self, String> {
        if usize::BITS != 64 { return Err("symbolic map requires 64-bit indices".into()); }
        if !(3..=i32::MAX as u64).contains(&n) || h > 31 || e > 64 {
            return Err("symbolic descriptor range".into());
        }
        let canonical = (64-(n-1).leading_zeros()) as usize;
        if h != canonical { return Err("symbolic canonical owner geometry".into()); }
        let modulus = BigUint::from_bytes_le(&Fr::MODULUS.to_bytes_le());
        if modulus <= (BigUint::from(1u8)<<155) {
            return Err("diagnostic field bound".into());
        }
        Ok(Self {binding: Binding {n,h,e,parent_root:None,
            d_upper_mode:DUpperMode::LegacyDiagnostic,lower_selector:None,contract:CONTRACT}})
    }
    pub(crate) fn new_modern_global_u(n:u64,h:usize,e:usize)->Result<Self,String> {
        let mut map=Self::new(n,h,e)?;
        map.binding.d_upper_mode=DUpperMode::ModernGlobalU;
        map.binding.contract=MODERN_GLOBAL_U_CONTRACT;
        Ok(map)
    }
    pub(crate) fn new_modern_global_u_selected_lower(
        n:u64,h:usize,e:usize,selector:LowerSelector,
    )->Result<Self,String> {
        let mut map=Self::new_modern_global_u(n,h,e)?;
        map.validate_lower_selector(selector)?;
        map.binding.d_upper_mode=DUpperMode::ModernGlobalUSelectedLower;
        map.binding.lower_selector=Some(selector);
        map.binding.contract=MODERN_GLOBAL_U_SELECTED_LOWER_CONTRACT;
        Ok(map)
    }
    // This is only a parent-identity binding, not an authenticated native join.
    pub(crate) fn from_parent(
        parent: &crate::work_tree_history_plan::WorkTreeHistoryPlan, e: usize,
    ) -> Result<Self, String> {
        let n = parent.headers();
        let h = parent.slot_log();
        Self::native_geometry(n,h)?;
        parent.descriptor().validate()?;
        if parent.descriptor().headers as u64 != n ||
            parent.descriptor().slots as u64 != 1u64<<h {
            return Err("native parent descriptor geometry".into());
        }
        let mut map = Self::new(n,h,e)?;
        map.binding.parent_root = Some(parent.descriptor().root);
        Ok(map)
    }
    pub(crate) fn from_parent_modern_global_u(
        parent: &crate::work_tree_history_plan::WorkTreeHistoryPlan,
        e: usize,
        selector: LowerSelector,
    ) -> Result<Self,String> {
        let n=parent.headers();
        let h=parent.slot_log();
        Self::native_geometry(n,h)?;
        parent.descriptor().validate()?;
        if parent.descriptor().headers as u64 != n ||
            parent.descriptor().slots as u64 != 1u64<<h {
            return Err("native parent descriptor geometry".into());
        }
        let mut map=Self::new_modern_global_u_selected_lower(n,h,e,selector)?;
        map.binding.parent_root=Some(parent.descriptor().root);
        Ok(map)
    }
    fn validate_lower_selector(&self,selector:LowerSelector)->Result<(),String> {
        use crate::global_u_roster::{CandidateSource,Schedule};
        use LowerBranch::{Equality,Literal,Pivot};
        let threshold=match selector.source {
            LowerSource::HeaderDifficulty {height} => {
                let schedule=Schedule::new(self.n())?;
                let expected=schedule.iter().find(|x|matches!(x,CandidateSource::HeaderDifficulty {height:h, ..} if *h==height));
                if expected.is_none() {return Err("selected lower D source outside canonical schedule".into());}
                lower_d_threshold(self.binding.e)
            }
            LowerSource::LegacyBound {q} => {
                let schedule=Schedule::new(self.n())?;
                let expected=schedule.legacy_items().find(|x|matches!(x,CandidateSource::LegacyBound {q:found, ..} if *found==q));
                if expected.is_none() {return Err("selected lower B source outside canonical schedule".into());}
                lower_b_threshold(self.binding.e)
            }
            LowerSource::InitialI | LowerSource::Reset417792 | LowerSource::Reset417793 => lower_b_threshold(self.binding.e),
        };
        let d_source=matches!(selector.source,LowerSource::HeaderDifficulty{..});
        let width=if d_source {224} else if matches!(selector.source,LowerSource::LegacyBound{..}) {92} else {0};
        match (selector.source,selector.branch) {
            (LowerSource::HeaderDifficulty{..},Equality)=>Ok(()),
            (LowerSource::HeaderDifficulty{..},Pivot(k)) |
            (LowerSource::LegacyBound{..},Pivot(k)) => {
                if k>=width {return Err("selected lower pivot outside source width".into());}
                if threshold.bit(k as u64) {return Err("selected lower pivot threshold bit must be zero".into());}
                Ok(())
            }
            (LowerSource::LegacyBound{..},Equality)=>Err("selected lower B has no equality branch".into()),
            (LowerSource::HeaderDifficulty{..},Literal) |
            (LowerSource::LegacyBound{..},Literal)=>Err("selected lower dynamic source cannot use literal branch".into()),
            (LowerSource::InitialI,Literal) => {
                if BigUint::from(crate::global_u_roster::INITIAL_I)<=threshold {Err("selected lower literal does not exceed U threshold".into())} else {Ok(())}
            }
            (LowerSource::Reset417792,Literal) => {
                if BigUint::from(crate::global_u_roster::RESET_CHILD_417792)<=threshold {Err("selected lower literal does not exceed U threshold".into())} else {Ok(())}
            }
            (LowerSource::Reset417793,Literal) => {
                if BigUint::from(crate::global_u_roster::RESET_CHILD_417793)<=threshold {Err("selected lower literal does not exceed U threshold".into())} else {Ok(())}
            }
            (_,Equality|Pivot(_))=>Err("fixed selected lower source requires literal branch".into()),
        }
    }
    fn selected_lower_owner(&self)->Option<u64> {
        match self.binding.lower_selector?.source {
            LowerSource::HeaderDifficulty{height}=>Some(height-2),
            LowerSource::LegacyBound{q}=>Some(q*1024+959),
            LowerSource::InitialI|LowerSource::Reset417792|LowerSource::Reset417793=>None,
        }
    }
    fn selected_lower_word(&self)->Option<(Word,usize,BigUint)> {
        let selector=self.binding.lower_selector?;
        match selector.source {
            LowerSource::HeaderDifficulty{..}=>Some((local(D_LOCAL,224),224,lower_d_threshold(self.binding.e))),
            LowerSource::LegacyBound{..}=>Some((local(SMAX,92),92,lower_b_threshold(self.binding.e))),
            LowerSource::InitialI|LowerSource::Reset417792|LowerSource::Reset417793=>None,
        }
    }
    pub(crate) fn native_geometry(n: u64, h: usize) -> Result<(),String> {
        if n > 1<<21 || h > 21 {
            return Err("native parent admission HOLD above 2^21".into());
        }
        Self::new(n,h,0)?;
        if BigUint::from_bytes_le(&Fr::MODULUS.to_bytes_le()) <=
            (BigUint::from(1u8)<<225) {
            return Err("retained native field bound".into());
        }
        Ok(())
    }
    pub(crate) fn binding(&self) -> Binding { self.binding.clone() }
    #[cfg(test)]
    pub(crate) fn selected_lower_descriptor(&self) -> Option<LowerSelector> {
        self.binding.lower_selector
    }
    pub(crate) fn n(&self) -> u64 { self.binding.n }
    pub(crate) fn h(&self) -> usize { self.binding.h }
    pub(crate) fn slots(&self) -> u64 { 1<<self.h() }
    pub(crate) fn cap(&self) -> BigInt { BigInt::from(1u8)<<self.binding.e }
    fn d_upper_bound(&self) -> u128 {
        let u=1u128<<self.binding.e;
        match self.binding.d_upper_mode {
            DUpperMode::LegacyDiagnostic=>u,
            DUpperMode::ModernGlobalU | DUpperMode::ModernGlobalUSelectedLower=>(2*u+1)/3,
        }
    }
    pub(crate) fn m(&self) -> u64 { (self.n()+64).min(843776)/1024 }
    fn owner(&self, s: u64) -> Result<(),String> {
        if s >= self.slots() { Err("owner outside symbolic domain".into()) } else { Ok(()) }
    }
    pub(crate) fn tier(&self, s: u64) -> Result<Option<usize>,String> {
        self.owner(s)?;
        if self.h()<10 || s%1024!=959 { return Ok(None); }
        let q=s/1024;
        Ok(if q<self.m() && q!=407 {Some(q.min(8) as usize)} else {None})
    }
    fn resolve(&self, s: u64, owner: Owner) -> Result<u64,String> {
        self.owner(s)?;
        let target=match owner {
            Owner::Destination=>s,
            Owner::Shift {d,low}=>{
                if s%1024!=959 {return Err("import destination is not an anchor".into());}
                (s/1024).checked_sub(d).and_then(|q|q.checked_mul(1024))
                    .and_then(|q|q.checked_add(low)).ok_or("import owner underflow")?
            }
        };
        self.owner(target)?;
        Ok(target)
    }
    fn index(&self, s: u64, owner: Owner, local: usize) -> Result<usize,String> {
        if local >= WIDTH as usize {return Err("local input coordinate".into());}
        let target=self.resolve(s,owner)?;
        usize::try_from(target.checked_mul(WIDTH).and_then(|x|x.checked_add(local as u64))
            .ok_or("input coordinate overflow")?).map_err(|_|"input index overflow".into())
    }
    pub(crate) fn input_index(&self, imp: Import, bit: usize) -> Result<usize,String> {
        self.validate_import(imp)?;
        if bit>=imp.width {return Err("import bit range".into());}
        self.index(imp.owner,Owner::Destination,imp.local+bit)
    }
    fn validate_import(&self, imp: Import) -> Result<(),String> {
        self.owner(imp.owner)?;
        match imp.kind {
            Kind::Difficulty if imp.local==D_LOCAL && imp.width==224 && imp.owner<self.n()-1=>Ok(()),
            Kind::Timestamp if imp.local==T_LOCAL && imp.width==64 && imp.owner<self.n()=>Ok(()),
            _=>Err("typed import does not name a retained genuine endpoint".into()),
        }
    }
    fn import(&self, s:u64, word:Word) -> Result<Import,String> {
        let Word::Bits {owner,base,width}=word else {return Err("literal is not an import".into())};
        let kind=if base==D_LOCAL {Kind::Difficulty} else if base==T_LOCAL {Kind::Timestamp}
            else {return Err("unsupported original input word".into())};
        let imp=Import {owner:self.resolve(s,owner)?,local:base,width,kind};
        self.validate_import(imp)?;
        Ok(imp)
    }
    pub(crate) fn imports(&self, s:u64) -> Result<Vec<Import>,String> {
        self.owner(s)?;
        let mut out=Vec::new();
        if s<self.n()-1 {out.push(self.import(s,local(D_LOCAL,224))?);}
        if let Some(ell)=self.tier(s)? {
            for i in 0..ell {
                let (d,end,start,_)=ratio_words(ell,i);
                out.push(self.import(s,d)?);
                out.push(self.import(s,end)?);
                out.push(self.import(s,start)?);
            }
        }
        out.sort();out.dedup();Ok(out)
    }
    pub(crate) fn active_intervals(&self,s:u64)->Result<Vec<(usize,usize)>,String> {
        self.owner(s)?;
        let mut out=Vec::new();
        if s<self.n()-1 {out.push((BASE,BASE+673));}
        if let Some(ell)=self.tier(s)? {
            if ell>0 {
                out.push((RATIO,RATIO+ell*503));
                if ell>=2 {out.push((PRED,PRED+782));}
                out.push((SMAX,SMAX+278));
            }
        }
        Ok(out)
    }
    pub(crate) fn check_row(&self,row:&OwnerRow)->Result<(),String> {
        self.owner(row.owner)?;
        if row.binding!=self.binding || row.bits.len()!=BANK {
            return Err("legacy map row binding".into());
        }
        Ok(())
    }
    pub(crate) fn generate(&self,s:u64,inputs:&Inputs)->Result<OwnerRow,String> {
        self.owner(s)?;
        let mut row=OwnerRow {owner:s,binding:self.binding(),bits:vec![false;BANK]};
        // Needed imports must exist; no implicit zero default.
        for imp in self.imports(s)? {inputs.get(imp)?;}
        if s<self.n()-1 {
            let d=read(self,s,&row,inputs,local(D_LOCAL,224))?;
            row.assign_cmp(&BigInt::from(self.d_upper_bound()),&d,224,BASE,BASE+224)?;
            row.assign_or(&d,224,BASE+449)?;
        }
        if let Some(ell)=self.tier(s)? {
            for i in 0..ell {
                let (d,end,start,offset)=ratio_words(ell,i);
                let a=read(self,s,&row,inputs,d)?*TE;
                let delta=read(self,s,&row,inputs,end)?-read(self,s,&row,inputs,start)?+offset;
                if delta<=BigInt::from(0) {return Err("ratio delta must be positive".into());}
                let q=&a/&delta;
                let r=&a-&q*&delta;
                let b=RATIO+503*i;
                for (base,width,n) in [(b,91,a),(b+91,64,delta.clone()),
                    (b+155,91,q),(b+246,64,r.clone())] {row.put(base,width,&n)?;}
                row.assign_or(&delta,64,b+310)?;
                row.assign_cmp(&r,&delta,64,b+374,b+438)?;
            }
            if ell>=2 {
                let (coeff,den,k)=polynomial(ell);
                let mut n=BigInt::from(k);
                for (i,c) in coeff.iter().enumerate().take(ell-1) {
                    n+=row.get(RATIO+503*i+155,91)?*(*c);
                }
                n+=row.get(RATIO+503*(ell-1)+155,91)?*(8*P*(ell as i64-1));
                row.assign_prediction(&n,den)?;
            }
            if ell>0 {
                let (mag,sign)=if ell==1 {(row.get(RATIO+155,91)?,false)}
                    else {(row.get(PRED+262,92)?,row.bit(PRED+354)?)};
                row.assign_cmp(&BigInt::from(I),&mag,92,SMAX+93,SMAX+185)?;
                let use_c=!sign && row.bit(SMAX+277)?;
                row.set_bit(SMAX+92,use_c)?;
                row.put(SMAX,92,&if use_c {mag} else {BigInt::from(I)})?;
            }
        }
        Ok(row)
    }
    pub(crate) fn terms(&self,s:u64)->Result<Vec<Term>,String> {
        self.owner(s)?;
        // Resolve/validate all source addresses before emitting anything.
        self.imports(s)?;
        let mut sink=Literal {map:self,owner:s,terms:Vec::new(),error:None};
        let active=self.active_intervals(s)?;
        for i in 0..BANK {
            let wire=BASE+i;
            if active.iter().any(|&(a,b)|a<=wire && wire<b) {
                let left=self.index(s,Owner::Destination,wire)?;
                sink.terms.push(Term {row:(s*ROWS+i as u64) as usize,
                    gate:Gate {left,right:left,c0:Fr::zero(),c1:-Fr::one(),
                        c2:Fr::zero(),c3:Fr::one()}});
            } else {sink.linear(i,local(wire,1),Fr::one());}
        }
        if s<self.n()-1 {emit_guard(&mut sink,self.d_upper_bound());}
        if let Some(ell)=self.tier(s)? {
            emit_tier(&mut sink,ell);
            if matches!(self.binding.d_upper_mode,DUpperMode::ModernGlobalU|DUpperMode::ModernGlobalUSelectedLower) {
                emit_b_upper(&mut sink,ell,self.binding.e);
            }
        }
        if self.selected_lower_owner()==Some(s) {
            if let (Some(selector),Some((word,width,threshold)))=(self.binding.lower_selector,self.selected_lower_word()) {
                emit_selected_lower(&mut sink,word,width,&threshold,selector.branch);
            }
        }
        if let Some(e)=sink.error {return Err(e);}
        Ok(sink.terms)
    }
    // Test-only producer for the proposed finite relation F. This validates
    // the complete source relation and typed import descriptors before
    // discarding any of the source bank's explicit zero-cell terms.
    #[cfg(test)]
    pub(crate) fn filtered_terms(&self,s:u64)->Result<Vec<Term>,String> {
        self.owner(s)?;
        let source=self.terms(s)?;
        self.filter_source_terms(s,source)
    }
    // Kept separate so tests can inject one malformed source term and verify
    // that the filter rejects it before remapping or omission.
    #[cfg(test)]
    pub(crate) fn filter_source_terms(
        &self,s:u64,source:Vec<Term>,
    )->Result<Vec<Term>,String> {
        self.owner(s)?;
        let imports=self.imports(s)?;
        if source.len()>200_000 {return Err("filtered relation owner term cap".into());}
        let active=self.active_intervals(s)?;
        let bank_zero=Fr::zero();
        let one=Fr::one();
        let mut out=Vec::with_capacity(source.len().min(10_000));
        for mut term in source {
            let source_row=u64::try_from(term.row).map_err(|_|"filtered relation row coordinate")?;
            let row_owner=source_row/ROWS;
            let row_local=(source_row%ROWS) as usize;
            if row_owner!=s || row_local>=ROWS as usize {
                return Err("filtered relation row/input owner collision".into());
            }
            if row_local<BANK {
                let wire=BASE+row_local;
                let is_active=active.iter().any(|&(lo,hi)|lo<=wire && wire<hi);
                let expected_left=self.index(s,Owner::Destination,wire)?;
                let expected_right=if is_active {expected_left}
                    else {self.index(s,Owner::Destination,0)?};
                if term.gate.left!=expected_left || term.gate.right!=expected_right {
                    return Err("filtered relation malformed bank input shape".into());
                }
                if is_active {
                    if term.gate.c0!=bank_zero || term.gate.c1!=-one ||
                        term.gate.c2!=bank_zero || term.gate.c3!=one {
                        return Err("filtered relation malformed active Boolean bank gate".into());
                    }
                } else {
                    if term.gate.c0!=bank_zero || term.gate.c1!=one ||
                        term.gate.c2!=bank_zero || term.gate.c3!=bank_zero {
                        return Err("filtered relation malformed dropped zero-cell gate".into());
                    }
                    continue;
                }
            }
            for index in [term.gate.left,term.gate.right] {
                let (input_owner,input_local)=self.filtered_input(index,s,&imports)?;
                if input_owner==s && (BASE..BASE+FILTERED_LIVE).contains(&input_local) {
                    let packed=FILTERED_HELPER_BASE+(input_local-BASE);
                    let moved=input_owner.checked_mul(WIDTH)
                        .and_then(|base|base.checked_add(packed as u64))
                        .and_then(|z|usize::try_from(z).ok())
                        .ok_or("filtered relation packed helper coordinate overflow")?;
                    if (moved as u64)/WIDTH!=input_owner {
                        return Err("filtered relation packed helper owner collision".into());
                    }
                    if index==term.gate.left {term.gate.left=moved;}
                    if index==term.gate.right {term.gate.right=moved;}
                }
            }
            let packed_row=s.checked_mul(ROWS).and_then(|base|base.checked_add(row_local as u64))
                .and_then(|z|usize::try_from(z).ok())
                .ok_or("filtered relation packed row coordinate overflow")?;
            if (packed_row as u64)/ROWS!=s || (packed_row as u64)%ROWS!=row_local as u64 {
                return Err("filtered relation packed row owner collision".into());
            }
            term.row=packed_row;
            out.push(term);
        }
        Ok(out)
    }
    #[cfg(test)]
    fn filtered_input(
        &self,index:usize,row_owner:u64,imports:&[Import],
    )->Result<(u64,usize),String> {
        let index=u64::try_from(index).map_err(|_|"filtered relation input coordinate")?;
        let owner=index/WIDTH;
        let local=(index%WIDTH) as usize;
        self.owner(owner)?;
        if (FILTERED_HELPER_BASE..FILTERED_HELPER_BASE+FILTERED_LIVE).contains(&local) {
            return Err("filtered relation source already uses packed helper coordinate".into());
        }
        if (BASE..BASE+BANK).contains(&local) {
            if owner!=row_owner {return Err("filtered relation foreign helper input".into());}
            if local>=BASE+FILTERED_LIVE {return Err("filtered relation retired helper input".into());}
        }
        if owner!=row_owner && !imports.iter().any(|imp| {
            imp.owner==owner && imp.local<=local && local<imp.local+imp.width
        }) {
            return Err("filtered relation foreign input outside typed imports".into());
        }
        Ok((owner,local))
    }
    pub(crate) fn failures(&self,row:&OwnerRow,inputs:&Inputs)->Result<Vec<(usize,Fr)>,String> {
        self.failures_with(row,inputs,&self.terms(row.owner)?)
    }
    pub(crate) fn failures_with(
        &self,row:&OwnerRow,inputs:&Inputs,terms:&[Term],
    )->Result<Vec<(usize,Fr)>,String> {
        self.check_row(row)?;
        let mut sums=BTreeMap::<usize,Fr>::new();
        for t in terms {
            let mut z=t.gate.c0;
            // c0/c1 placeholder values are never read.
            if !t.gate.c1.is_zero() {z+=t.gate.c1*value(self,row,inputs,t.gate.left)?;}
            if !t.gate.c2.is_zero() {z+=t.gate.c2*value(self,row,inputs,t.gate.right)?;}
            if !t.gate.c3.is_zero() {
                z+=t.gate.c3*value(self,row,inputs,t.gate.left)?
                    *value(self,row,inputs,t.gate.right)?;
            }
            *sums.entry(t.row).or_insert(Fr::zero())+=z;
        }
        Ok(sums.into_iter().filter(|(_,z)|!z.is_zero()).collect())
    }
    pub(crate) fn coefficients(&self,r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String> {
        self.points(r,u,v)?;
        let mut a=Analytic {map:self,r,u,v,scope:Scope::All,coeff:[Fr::zero();4],
            cache:BTreeMap::new(),placement:None,error:None};
        a.bank(0,BANK,false,Scope::All,Fr::one())?;
        a.bank(0,673,false,Scope::Work,-Fr::one())?;
        a.bank(0,673,true,Scope::Work,Fr::one())?;
        a.scope=Scope::Work;emit_guard(&mut a,self.d_upper_bound());
        if self.h()>=10 {
            for ell in 1..=8 {
                a.scope=Scope::Anchor(ell);
                for (base,len) in [(RATIO,ell*503),(PRED,if ell>=2 {782}else{0}),(SMAX,278)] {
                    if len==0 {continue;}
                    a.bank(base-BASE,base-BASE+len,false,Scope::Anchor(ell),-Fr::one())?;
                    a.bank(base-BASE,base-BASE+len,true,Scope::Anchor(ell),Fr::one())?;
                }
                emit_tier(&mut a,ell);
                if matches!(self.binding.d_upper_mode,DUpperMode::ModernGlobalU|DUpperMode::ModernGlobalUSelectedLower) {
                    emit_b_upper(&mut a,ell,self.binding.e);
                }
            }
        }
        if let (Some(owner),Some(selector),Some((word,width,threshold)))=(
            self.selected_lower_owner(),self.binding.lower_selector,self.selected_lower_word()) {
            a.scope=Scope::ExactOwner(owner);
            emit_selected_lower(&mut a,word,width,&threshold,selector.branch);
        }
        Ok(a.coeff)
    }
    // Analytic equation callback for the same test-only F producer above.
    // Its separate emitter path intentionally excludes the old Map's global
    // linear bank and retired cells.
    #[cfg(test)]
    pub(crate) fn filtered_coefficients(
        &self,r:&[Fr],u:&[Fr],v:&[Fr],
    )->Result<[Fr;4],String> {
        if (self.n(),self.h(),self.binding.e)!=(1984,11,47) ||
            self.binding.d_upper_mode!=DUpperMode::ModernGlobalUSelectedLower ||
            self.binding.lower_selector!=Some(LowerSelector {
                source:LowerSource::Reset417792,branch:LowerBranch::Literal,
            }) || self.binding.parent_root.is_none() {
            return Err("filtered relation requires the frozen N1984 parent profile".into());
        }
        self.points(r,u,v)?;
        let placement=CoefficientPlacement {
            row_base:0,helper_base:FILTERED_HELPER_BASE,row_bits:14,live:FILTERED_LIVE,
        };
        let mut a=Analytic {map:self,r,u,v,scope:Scope::All,
            coeff:[Fr::zero();4],cache:BTreeMap::new(),
            placement:Some(placement),error:None};
        a.bank(0,673,true,Scope::Work,Fr::one())?;
        a.scope=Scope::Work;
        emit_guard(&mut a,self.d_upper_bound());
        a.bank(RATIO-BASE,RATIO-BASE+503,true,Scope::Anchor(1),Fr::one())?;
        a.bank(SMAX-BASE,SMAX-BASE+278,true,Scope::Anchor(1),Fr::one())?;
        a.scope=Scope::Anchor(1);
        emit_tier(&mut a,1);
        emit_b_upper(&mut a,1,self.binding.e);
        if let Some(error)=a.error {return Err(error);}
        Ok(a.coeff)
    }
    // Source-only H21 equation diagnostic for one owner. This deliberately
    // remains separate from the frozen N1984 callback and makes no physical
    // Bank53 overlay or authenticated-witness claim.
    #[cfg(test)]
    pub(crate) fn filtered_coefficients_h21_source_only_diagnostic(
        &self,owner:u64,r:&[Fr],u:&[Fr],v:&[Fr],
    )->Result<[Fr;4],String> {
        if (self.n(),self.h(),self.binding.e)!=(1_827_840,21,47) ||
            self.binding.d_upper_mode!=DUpperMode::ModernGlobalU ||
            self.binding.lower_selector.is_some() || self.binding.parent_root.is_some() ||
            !matches!(owner/1024,8|9) || owner%1024!=959 {
            return Err("source-only filtered equation diagnostic requires H21 q8/q9 anchor".into());
        }
        self.points(r,u,v)?;
        let ell=self.tier(owner)?.ok_or("H21 diagnostic owner has no anchor tier")?;
        if ell!=8 {return Err("H21 diagnostic owner is not tier8".into());}
        let placement=CoefficientPlacement {
            row_base:0,helper_base:FILTERED_HELPER_BASE,row_bits:14,live:FILTERED_LIVE,
        };
        let mut a=Analytic {map:self,r,u,v,scope:Scope::All,
            coeff:[Fr::zero();4],cache:BTreeMap::new(),
            placement:Some(placement),error:None};
        a.bank(0,673,true,Scope::Work,Fr::one())?;
        a.scope=Scope::Work;
        emit_guard(&mut a,self.d_upper_bound());
        a.scope=Scope::Anchor(ell);
        for (base,len) in [
            (RATIO,ell*503),
            (PRED,if ell>=2 {782}else{0}),
            (SMAX,278),
        ] {
            if len!=0 {
                a.bank(base-BASE,base-BASE+len,true,Scope::Anchor(ell),Fr::one())?;
            }
        }
        emit_tier(&mut a,ell);
        emit_b_upper(&mut a,ell,self.binding.e);
        if let Some(error)=a.error {return Err(error);}
        Ok(a.coeff)
    }
    #[cfg(test)]
    pub(crate) fn bank53_coefficients(
        &self,context:usize,r:&[Fr],u:&[Fr],v:&[Fr],
    )->Result<[Fr;4],String> {
        if context>=2 {return Err("bank53 context outside two lanes".into());}
        self.bank53_coefficients_at(context,409600+context*32768,r,u,v)
    }
    /// Same physical X relation, with a caller-owned ROW placement. The
    /// canonical H21 structural roster supplies and binds that placement.
    #[cfg(test)]
    pub(crate) fn bank53_coefficients_at(
        &self,context:usize,row_base:usize,r:&[Fr],u:&[Fr],v:&[Fr],
    )->Result<[Fr;4],String> {
        if context>=2 {return Err("bank53 context outside two lanes".into());}
        if self.h()>21 {return Err("bank53 owner geometry above H21".into());}
        if (r.len(),u.len(),v.len())!=(19+self.h(),20+self.h(),20+self.h()) {
            return Err("bank53 physical coefficient dimensions".into());
        }
        let placement=CoefficientPlacement {
            row_base,
            helper_base:671744+context*8192,
            row_bits:19,
            live:5757,
        };
        let row_end=placement.row_base.checked_add(ROWS as usize)
            .ok_or("bank53 physical row placement overflow")?;
        if row_end>1<<placement.row_bits
            || placement.helper_base+8192>WIDTH as usize {
            return Err("bank53 physical lane outside owner".into());
        }
        let mut a=Analytic {map:self,r,u,v,scope:Scope::All,coeff:[Fr::zero();4],
            cache:BTreeMap::new(),placement:Some(placement),error:None};
        // The original [5757,7898) bank tail contains only zero gates. It is
        // retired so the score input may occupy that physical space.
        a.bank(0,placement.live,false,Scope::All,Fr::one())?;
        a.bank(0,673,false,Scope::Work,-Fr::one())?;
        a.bank(0,673,true,Scope::Work,Fr::one())?;
        a.scope=Scope::Work;emit_guard(&mut a,self.d_upper_bound());
        if self.h()>=10 {
            for ell in 1..=8 {
                a.scope=Scope::Anchor(ell);
                for (base,len) in [(RATIO,ell*503),(PRED,if ell>=2 {782}else{0}),(SMAX,278)] {
                    if len==0 {continue;}
                    a.bank(base-BASE,base-BASE+len,false,Scope::Anchor(ell),-Fr::one())?;
                    a.bank(base-BASE,base-BASE+len,true,Scope::Anchor(ell),Fr::one())?;
                }
                emit_tier(&mut a,ell);
                if matches!(self.binding.d_upper_mode,DUpperMode::ModernGlobalU|DUpperMode::ModernGlobalUSelectedLower) {
                    emit_b_upper(&mut a,ell,self.binding.e);
                }
            }
        }
        if let (Some(owner),Some(selector),Some((word,width,threshold)))=(
            self.selected_lower_owner(),self.binding.lower_selector,self.selected_lower_word()) {
            a.scope=Scope::ExactOwner(owner);
            emit_selected_lower(&mut a,word,width,&threshold,selector.branch);
        }
        if let Some(error)=a.error {return Err(error);}
        Ok(a.coeff)
    }
    // First c130 falsifier only: one upper-only q9 relation, not a global
    // callback or an authenticated native-parent projection. The algebra path
    // never constructs or consumes the literal Map/Bank53 term stream.
    #[cfg(test)]
    pub(crate) fn q9_relocated_coefficients_diagnostic(
        &self,r:&[Fr],u:&[Fr],v:&[Fr],
    )->Result<[Fr;4],String> {
        const OWNER:u64=10175;
        if (self.n(),self.h(),self.binding.e)!=(1_827_840,21,55)
            || self.binding.d_upper_mode!=DUpperMode::ModernGlobalU
            || self.binding.lower_selector.is_some() || self.binding.parent_root.is_some() {
            return Err("q9 projection requires H21 e55 upper-only fixture profile".into());
        }
        if (r.len(),u.len(),v.len())!=(40,41,41) {
            return Err("q9 projection physical coefficient dimensions".into());
        }
        if self.tier(OWNER)?!=Some(8) {return Err("q9 projection tier".into());}
        let placement=CoefficientPlacement {
            row_base:477074,helper_base:671744,row_bits:19,live:5757,
        };
        let scope=Scope::ExactOwner(OWNER);
        let mut a=Analytic {map:self,r,u,v,scope,coeff:[Fr::zero();4],
            cache:BTreeMap::new(),placement:Some(placement),error:None};
        // At ell8, guard673 + ratio4024 + pred782 + smax278 exhaust the
        // contiguous live bank. Only the old 2141-cell zero tail is retired.
        a.bank(0,placement.live,true,scope,Fr::one())?;
        emit_guard(&mut a,self.d_upper_bound());
        emit_tier(&mut a,8);
        emit_b_upper(&mut a,8,self.binding.e);
        if let Some(error)=a.error {return Err(error);}
        Ok(a.coeff)
    }
    fn points(&self,r:&[Fr],u:&[Fr],v:&[Fr])->Result<(),String> {
        if (r.len(),u.len(),v.len())!=(14+self.h(),20+self.h(),20+self.h()) {
            Err("symbolic coefficient dimensions".into())
        } else {Ok(())}
    }
    fn bounds(&self,ell:usize)->(u64,u64) {
        if ell==8 {(8,self.m())} else {(ell as u64,((ell+1) as u64).min(self.m()))}
    }
    // At most one shifted historical import. RightIndex::SameRow preserves
    // the destination-owner placeholder, which is not a value-zero assertion.
    fn kernel(&self,scope:Scope,r:&[Fr],u:&[Fr],v:&[Fr],left:Owner,right:Owner)->Fr {
        match scope {
            Scope::All=> {assert_eq!((left,right),(Owner::Destination,Owner::Destination));joint(r,u,v)},
            Scope::Work=> {
                assert_eq!((left,right),(Owner::Destination,Owner::Destination));
                evaluate_shift(r,u,v,0,0,self.n()-1,0,RightIndex::SameRow).unwrap()
            },
            Scope::Anchor(ell)=>{
                if self.h()<10 {return Fr::zero();}
                let (l,hi)=self.bounds(ell);
                let (d,ul,vl,swap)=match (left,right) {
                    (Owner::Destination,Owner::Destination)=>(0,959,959,false),
                    (Owner::Shift{d,low},Owner::Destination)=>(d,low,959,false),
                    (Owner::Destination,Owner::Shift{d,low})=>(d,959,low,true),
                    _=>panic!("two independently shifted imports require another construction"),
                };
                let lo=l.max(d);
                if lo>=hi {return Fr::zero();}
                let (uq,vq)=if swap {(&v[10..],&u[10..])} else {(&u[10..],&v[10..])};
                let mut z=evaluate_shift(&r[10..],uq,vq,d,lo,hi,0,RightIndex::SameRow).unwrap();
                if lo<=407 && 407<hi {
                    z-=eq(&r[10..],407)*eq(uq,407-d)*eq(vq,407);
                }
                z*eq(&r[..10],959)*eq(&u[..10],ul)*eq(&v[..10],vl)
            }
            Scope::ExactOwner(owner)=>{
                let Ok(left_owner)=self.resolve(owner,left) else {return Fr::zero();};
                let Ok(right_owner)=self.resolve(owner,right) else {return Fr::zero();};
                eq(r,owner)*eq(u,left_owner)*eq(v,right_owner)
            }
        }
    }
    pub(crate) fn owner_kernel(
        &self,scope:Scope,r:&[Fr],u:&[Fr],v:&[Fr],d:u64,low:u64,
    )->Result<Fr,String> {
        if (r.len(),u.len(),v.len())!=(self.h(),self.h(),self.h()) {
            return Err("owner kernel dimensions".into());
        }
        if low>=1024 {return Err("owner kernel low coordinate".into());}
        if let Scope::Anchor(ell)=scope {
            if ell>8 {return Err("owner kernel tier".into());}
        }
        let left=if scope==Scope::Anchor(0) || matches!(scope,Scope::Anchor(_)) {
            Owner::Shift {d,low}
        } else {
            if d!=0 {return Err("non-anchor shift".into());}
            Owner::Destination
        };
        Ok(self.kernel(scope,r,u,v,left,Owner::Destination))
    }
}
fn lower_d_threshold(e:usize)->BigUint {
    ((BigUint::from(1u8)<<e)+BigUint::from(4u8))/BigUint::from(3u8)
}
fn lower_b_threshold(e:usize)->BigUint {
    (BigUint::from(1u8)<<e)/BigUint::from(2u8)
}
fn ratio_words(ell:usize,i:usize)->(Word,Word,Word,i64) {
    assert!((1..=8).contains(&ell) && i<ell);
    if i+1==ell {
        (source(0,958,D_LOCAL,224),source(0,959,T_LOCAL,64),
            source(1,1023,T_LOCAL,64),64)
    } else {
        let d=(ell-1-i) as u64;
        (source(d,1022,D_LOCAL,224),source(d,1023,T_LOCAL,64),
            source(d+1,1023,T_LOCAL,64),0)
    }
}
fn polynomial(ell:usize)->([i64;7],i64,i64) {
    assert!((2..=8).contains(&ell));
    let mut c=[0i64;7];
    for (i,z) in c.iter_mut().enumerate().take(ell-1) {
        *z=4*P*(3*(i as i64+1)-ell as i64-2);
    }
    let l=ell as i64;
    (c,2*P*l*(l-1),4*P*l*(l-1)+1024*(l+1)*l*(l-1))
}

trait Algebra {
    fn constant(&mut self,row:usize,c:Fr);
    fn linear(&mut self,row:usize,a:Word,c:Fr);
    fn product(&mut self,row:usize,a:Word,b:Word,c:Fr);
    fn signed(&mut self,row:usize,a:Word,sign:Word,c:Fr) {
        self.linear(row,a,c);self.product(row,sign,a,-f(2)*c);
    }
}
struct Literal<'a> {map:&'a Map,owner:u64,terms:Vec<Term>,error:Option<String>}
impl Literal<'_> {
    fn term(&mut self,row:usize,left:Owner,lb:usize,right:Owner,rb:usize,k:usize,c:Fr) {
        if c.is_zero() || self.error.is_some() {return;}
        let indices=self.map.index(self.owner,left,lb)
            .and_then(|l|self.map.index(self.owner,right,rb).map(|r|(l,r)));
        match indices {
            Err(e)=>self.error=Some(e),
            Ok((left,right))=>{
                let mut cs=[Fr::zero();4];cs[k]=c;
                self.terms.push(Term {row:(self.owner*ROWS+row as u64) as usize,
                    gate:Gate {left,right,c0:cs[0],c1:cs[1],c2:cs[2],c3:cs[3]}});
            }
        }
    }
}
impl Algebra for Literal<'_> {
    fn constant(&mut self,r:usize,c:Fr) {
        self.term(r,Owner::Destination,0,Owner::Destination,0,0,c);
    }
    fn linear(&mut self,r:usize,a:Word,c:Fr) {
        match a {
            Word::Constant(x)=>self.constant(r,c*fc(x)),
            Word::Bits{owner,base,width}=>{
                let mut k=c;
                for b in 0..width {self.term(r,owner,base+b,Owner::Destination,0,1,k);k+=k;}
            }
        }
    }
    fn product(&mut self,r:usize,a:Word,b:Word,c:Fr) {
        match (a,b) {
            (Word::Constant(x),_)=>self.linear(r,b,c*fc(x)),
            (_,Word::Constant(x))=>self.linear(r,a,c*fc(x)),
            (Word::Bits{owner:lo,base:lb,width:lw},Word::Bits{owner:ro,base:rb,width:rw})=>{
                let mut l=c;
                for i in 0..lw {
                    let mut k=l;
                    for j in 0..rw {self.term(r,lo,lb+i,ro,rb+j,3,k);k+=k;}
                    l+=l;
                }
            }
        }
    }
}
#[derive(Clone,Copy)]
struct CoefficientPlacement {
    row_base:usize,helper_base:usize,row_bits:usize,live:usize,
}
struct Analytic<'a> {
    map:&'a Map,r:&'a[Fr],u:&'a[Fr],v:&'a[Fr],scope:Scope,coeff:[Fr;4],
    cache:BTreeMap<(u8,usize,u64,u64,u64,u64),Fr>,
    placement:Option<CoefficientPlacement>,error:Option<String>,
}
impl Analytic<'_> {
    fn layout(&self)->CoefficientPlacement {
        self.placement.unwrap_or(CoefficientPlacement {
            row_base:0,helper_base:BASE,row_bits:14,live:BANK,
        })
    }
    fn row_weight(&self,row:usize)->Fr {
        let p=self.layout();eq(&self.r[..p.row_bits],(p.row_base+row) as u64)
    }
    fn word_base(&mut self,owner:Owner,base:usize,width:usize)->Option<usize> {
        let Some(p)=self.placement else {return Some(base);};
        let Some(end)=base.checked_add(width) else {
            self.error=Some("bank53 word extent overflow".into());return None;
        };
        if end>WIDTH as usize {
            self.error=Some("bank53 word outside physical owner".into());return None;
        }
        if base<BASE+BANK && end>BASE {
            if owner!=Owner::Destination || base<BASE || end>BASE+p.live {
                self.error=Some("bank53 word touches retired Map tail or foreign helper".into());
                return None;
            }
            Some(p.helper_base+base-BASE)
        } else {Some(base)}
    }
    fn owner(&mut self,left:Owner,right:Owner)->Fr {
        let scope=match self.scope {
            Scope::All=>(0,0),Scope::Work=>(1,0),Scope::Anchor(e)=>(2,e),
            Scope::ExactOwner(owner)=>(3,owner as usize),
        };
        let pair=|o|match o {Owner::Destination=>(0,959),Owner::Shift{d,low}=>(d+1,low)};
        let a=pair(left);let b=pair(right);
        let key=(scope.0,scope.1,a.0,a.1,b.0,b.1);
        if let Some(z)=self.cache.get(&key) {return *z;}
        let z=self.map.kernel(self.scope,&self.r[self.layout().row_bits..],
            &self.u[20..],&self.v[20..],left,right);
        self.cache.insert(key,z);z
    }
    fn weight(p:&[Fr],base:usize,width:usize)->Fr {
        let mut k=Fr::one();let mut z=Fr::zero();
        for b in 0..width {z+=k*eq(p,(base+b) as u64);k+=k;}
        z
    }
    fn bank(&mut self,a:usize,b:usize,boolean:bool,scope:Scope,scale:Fr)->Result<(),String> {
        let p=self.layout();
        if a>b || b>p.live {return Err("bank53 analytic bank extent".into());}
        self.scope=scope;
        let k=self.owner(Owner::Destination,Owner::Destination)*scale;
        if k.is_zero() {return Ok(());}
        let mut rp=self.r[..p.row_bits].to_vec();rp.resize(20,Fr::zero());
        let offset=p.helper_base.checked_sub(p.row_base)
            .ok_or("bank53 analytic row/input offset")?;
        let z=evaluate_shift(&self.u[..20],&rp,&self.v[..20],offset as u64,
            (p.helper_base+a) as u64,(p.helper_base+b) as u64,0,
            if boolean {RightIndex::SameRow}else{RightIndex::GlobalZero})?;
        if boolean {self.coeff[1]-=k*z;self.coeff[3]+=k*z;}
        else {self.coeff[1]+=k*z;}
        Ok(())
    }
}
impl Algebra for Analytic<'_> {
    fn constant(&mut self,row:usize,c:Fr) {
        if c.is_zero() {return;}
        let k=self.owner(Owner::Destination,Owner::Destination);
        let row_weight=self.row_weight(row);
        self.coeff[0]+=k*row_weight*eq(&self.u[..20],0)*eq(&self.v[..20],0)*c;
    }
    fn linear(&mut self,row:usize,a:Word,c:Fr) {
        if c.is_zero() {return;}
        match a {
            Word::Constant(x)=>self.constant(row,c*fc(x)),
            Word::Bits{owner,base,width}=>{
                let Some(base)=self.word_base(owner,base,width) else {return;};
                let k=self.owner(owner,Owner::Destination);
                if k.is_zero() {return;}
                let row_weight=self.row_weight(row);
                self.coeff[1]+=k*row_weight
                    *Self::weight(&self.u[..20],base,width)*eq(&self.v[..20],0)*c;
            }
        }
    }
    fn product(&mut self,row:usize,a:Word,b:Word,c:Fr) {
        if c.is_zero() {return;}
        match (a,b) {
            (Word::Constant(x),_)=>self.linear(row,b,c*fc(x)),
            (_,Word::Constant(x))=>self.linear(row,a,c*fc(x)),
            (Word::Bits{owner:lo,base:lb,width:lw},Word::Bits{owner:ro,base:rb,width:rw})=>{
                let Some(lb)=self.word_base(lo,lb,lw) else {return;};
                let Some(rb)=self.word_base(ro,rb,rw) else {return;};
                let k=self.owner(lo,ro);
                if k.is_zero() {return;}
                let row_weight=self.row_weight(row);
                self.coeff[3]+=k*row_weight
                    *Self::weight(&self.u[..20],lb,lw)*Self::weight(&self.v[..20],rb,rw)*c;
            }
        }
    }
}
fn cmp(s:&mut impl Algebra,row:usize,width:usize,l:Word,r:Word,diff:usize,borrow:usize) {
    s.linear(row,local(borrow,1),Fr::one());
    for bit in 0..width {
        s.linear(row+1+bit,l.bit(bit),Fr::one());
        s.linear(row+1+bit,r.bit(bit),-Fr::one());
        s.linear(row+1+bit,local(borrow+bit,1),-Fr::one());
        s.linear(row+1+bit,local(diff+bit,1),-Fr::one());
        s.linear(row+1+bit,local(borrow+bit+1,1),f(2));
    }
}
fn or_rows(s:&mut impl Algebra,row:usize,a:Word,z:usize,width:usize) {
    s.linear(row,local(z,1),Fr::one());s.linear(row,a.bit(0),-Fr::one());
    for bit in 1..width {
        s.linear(row+bit,local(z+bit,1),Fr::one());
        s.linear(row+bit,a.bit(bit),-Fr::one());
        s.linear(row+bit,local(z+bit-1,1),-Fr::one());
        s.product(row+bit,a.bit(bit),local(z+bit-1,1),Fr::one());
    }
}
fn emit_guard(s:&mut impl Algebra,upper:u128) {
    cmp(s,7898,224,Word::Constant(upper),local(D_LOCAL,224),BASE,BASE+224);
    s.linear(7898+225,local(BASE+448,1),Fr::one());
    or_rows(s,7898+227,local(D_LOCAL,224),BASE+449,224);
    s.linear(7898+451,local(BASE+672,1),Fr::one());s.constant(7898+451,-Fr::one());
}
fn emit_prediction(s:&mut impl Algebra,ell:usize,polynomial_row:bool) {
    let b=PRED;let row=9422;
    let n=local(b,130);let sn=local(b+130,1);
    let q=local(b+131,92);let sq=local(b+223,1);
    let rem=local(b+224,37);let sr=local(b+261,1);
    let c=local(b+262,92);let sc=local(b+354,1);
    let (coeff,den,k)=polynomial(ell);
    if polynomial_row {
        s.signed(row,n,sn,Fr::one());
        for (i,c) in coeff.iter().enumerate().take(ell-1) {
            s.linear(row,local(RATIO+503*i+155,91),f(-*c));
        }
        s.linear(row,local(RATIO+503*(ell-1)+155,91),f(-8*P*(ell as i64-1)));
        s.constant(row,f(-k));
    }
    s.signed(row+1,n,sn,Fr::one());s.signed(row+1,q,sq,f(-den));
    s.signed(row+1,rem,sr,-Fr::one());
    s.signed(row+2,c,sc,Fr::one());s.signed(row+2,q,sq,-Fr::one());
    s.linear(row+2,local(b+706,1),-Fr::one());
    s.linear(row+3,local(b+706,1),Fr::one());
    s.linear(row+3,local(b+613,1),-Fr::one());
    s.product(row+3,sr,local(b+613,1),Fr::one());
    let fields=[(n,sn,355,130),(q,sq,485,92),(rem,sr,577,37),(c,sc,614,92)];
    let mut at=4;
    for (mag,_,z,width) in fields {
        or_rows(s,row+at,mag,b+z,width);at+=width;
    }
    assert_eq!(at,355);
    for (i,(_,sign,z,width)) in fields.into_iter().enumerate() {
        s.linear(row+355+i,sign,Fr::one());
        s.product(row+355+i,sign,local(b+z+width-1,1),-Fr::one());
    }
    for (at,sign,nz) in [(359,sq,b+576),(360,sr,b+613)] {
        s.product(row+at,local(nz,1),sign,Fr::one());
        s.product(row+at,local(nz,1),sn,-Fr::one());
    }
    cmp(s,row+361,37,rem,Word::Constant(den as u128),b+707,b+744);
    s.linear(row+399,local(b+781,1),Fr::one());s.constant(row+399,-Fr::one());
}
fn emit_smax(s:&mut impl Algebra,ell:usize) {
    let (mag,sign)=if ell==1 {(local(RATIO+155,91),Word::Constant(0))}
        else {(local(PRED+262,92),local(PRED+354,1))};
    let b=SMAX;let row=9822;
    cmp(s,row,92,Word::Constant(I),mag,b+93,b+185);
    s.linear(row+93,local(b+92,1),Fr::one());
    s.linear(row+93,local(b+277,1),-Fr::one());
    s.product(row+93,sign,local(b+277,1),Fr::one());
    for bit in 0..92 {
        s.linear(row+94+bit,local(b+bit,1),Fr::one());
        s.linear(row+94+bit,Word::Constant(I).bit(bit),-Fr::one());
        s.product(row+94+bit,local(b+92,1),mag.bit(bit),-Fr::one());
        s.product(row+94+bit,local(b+92,1),Word::Constant(I).bit(bit),Fr::one());
    }
}
fn emit_b_upper(s:&mut impl Algebra,ell:usize,e:usize) {
    if ell==0 {return;}
    let mut row=10032;
    for bit in e+1..92 {
        s.linear(row,local(SMAX+bit,1),Fr::one());
        row+=1;
    }
    for bit in 0..e {
        s.product(row,local(SMAX+e,1),local(SMAX+bit,1),Fr::one());
        row+=1;
    }
    debug_assert_eq!(row,10123);
}
fn emit_selected_lower(
    s:&mut impl Algebra,word:Word,width:usize,threshold:&BigUint,branch:LowerBranch,
) {
    let start=10123usize;
    match branch {
        LowerBranch::Literal=>{},
        LowerBranch::Equality=>{
            for bit in 0..width {
                s.linear(start+bit,word.bit(bit),Fr::one());
                if threshold.bit(bit as u64) {s.constant(start+bit,-Fr::one());}
            }
        }
        LowerBranch::Pivot(k)=>{
            s.linear(start,word.bit(k),Fr::one());s.constant(start,-Fr::one());
            for bit in k+1..width {
                s.linear(start+bit-k,word.bit(bit),Fr::one());
                if threshold.bit(bit as u64) {s.constant(start+bit-k,-Fr::one());}
            }
        }
    }
}
fn emit_tier(s:&mut impl Algebra,ell:usize) {
    if ell==0 {return;}
    for i in 0..ell {
        let (d,end,start,offset)=ratio_words(ell,i);
        let b=RATIO+503*i;let row=8350+134*i;
        s.linear(row,local(b,91),Fr::one());s.linear(row,d,f(-TE));
        s.linear(row+1,local(b+91,64),Fr::one());s.linear(row+1,end,-Fr::one());
        s.linear(row+1,start,Fr::one());s.constant(row+1,f(-offset));
        s.linear(row+2,local(b,91),Fr::one());
        s.product(row+2,local(b+155,91),local(b+91,64),-Fr::one());
        s.linear(row+2,local(b+246,64),-Fr::one());
        or_rows(s,row+3,local(b+91,64),b+310,64);
        s.linear(row+67,local(b+373,1),Fr::one());s.constant(row+67,-Fr::one());
        cmp(s,row+68,64,local(b+246,64),local(b+91,64),b+374,b+438);
        s.linear(row+133,local(b+502,1),Fr::one());s.constant(row+133,-Fr::one());
    }
    if ell>=2 {emit_prediction(s,ell,true);}
    emit_smax(s,ell);
    // Ordered older endpoints, then anchor: exactly ell+1 full64-bit imports.
    for i in 0..ell {
        s.linear(10008+i,source((ell-i) as u64,1023,T_LOCAL+63,1),Fr::one());
    }
    s.linear(10008+ell,source(0,959,T_LOCAL+63,1),Fr::one());
}

#[derive(Clone, Default)]
pub(crate) struct Inputs { words:BTreeMap<Import,Vec<bool>> }
impl Inputs {
    pub(crate) fn put(&mut self,map:&Map,imp:Import,n:&BigInt)->Result<(),String> {
        map.validate_import(imp)?;
        if n.sign()==Sign::Minus || n.bits()>imp.width as u64 {
            return Err("original import width or sign; truncation forbidden".into());
        }
        self.words.insert(imp,(0..imp.width).map(|b|((n>>b)&BigInt::from(1))==BigInt::from(1)).collect());
        Ok(())
    }
    pub(crate) fn get(&self,imp:Import)->Result<BigInt,String> {
        let bits=self.words.get(&imp).ok_or_else(||format!("missing typed import {imp:?}"))?;
        Ok(bits.iter().enumerate().fold(BigInt::from(0),|n,(b,z)|
            if *z {n+(BigInt::from(1)<<b)} else {n}))
    }
    pub(crate) fn bit(&self,owner:u64,local:usize)->Result<bool,String> {
        for (imp,bits) in &self.words {
            if imp.owner==owner && imp.local<=local && local<imp.local+imp.width {
                return Ok(bits[local-imp.local]);
            }
        }
        Err(format!("missing original coordinate owner{owner} local{local}"))
    }
    pub(crate) fn flip(&mut self,imp:Import,bit:usize)->Result<(),String> {
        if bit>=imp.width {return Err("original bit range".into());}
        let bits=self.words.get_mut(&imp).ok_or("missing original mutation target")?;
        bits[bit]=!bits[bit];Ok(())
    }
}
#[derive(Clone)]
pub(crate) struct OwnerRow {
    pub(crate) owner:u64,
    pub(crate) binding:Binding,
    pub(crate) bits:Vec<bool>,
}
impl OwnerRow {
    pub(crate) fn bit(&self,local:usize)->Result<bool,String> {
        let i=local.checked_sub(BASE).ok_or("helper below reserved bank")?;
        self.bits.get(i).copied().ok_or_else(||"helper outside reserved bank".into())
    }
    pub(crate) fn set_bit(&mut self,local:usize,value:bool)->Result<(),String> {
        let i=local.checked_sub(BASE).ok_or("helper below reserved bank")?;
        *self.bits.get_mut(i).ok_or("helper outside reserved bank")?=value;Ok(())
    }
    pub(crate) fn flip(&mut self,local:usize)->Result<(),String> {
        self.set_bit(local,!self.bit(local)?)
    }
    pub(crate) fn get(&self,base:usize,width:usize)->Result<BigInt,String> {
        let mut n=BigInt::from(0);
        for b in 0..width {if self.bit(base+b)? {n+=BigInt::from(1)<<b;}}
        Ok(n)
    }
    pub(crate) fn put(&mut self,base:usize,width:usize,n:&BigInt)->Result<(),String> {
        if n.sign()==Sign::Minus || n.bits()>width as u64 {
            return Err("helper width or sign; truncation forbidden".into());
        }
        for b in 0..width {
            self.set_bit(base+b,((n>>b)&BigInt::from(1))==BigInt::from(1))?;
        }
        Ok(())
    }
    fn assign_cmp(&mut self,l:&BigInt,r:&BigInt,width:usize,diff:usize,borrow:usize)->Result<(),String> {
        self.set_bit(borrow,false)?;
        let mut carry=0i8;
        for bit in 0..width {
            let a=((l>>bit)&BigInt::from(1)).to_i8().unwrap();
            let b=((r>>bit)&BigInt::from(1)).to_i8().unwrap();
            let raw=a-b-carry;
            self.set_bit(diff+bit,raw.rem_euclid(2)==1)?;
            carry=i8::from(raw<0);self.set_bit(borrow+bit+1,carry==1)?;
        }
        Ok(())
    }
    fn assign_or(&mut self,n:&BigInt,width:usize,z:usize)->Result<(),String> {
        let mut yes=false;
        for bit in 0..width {
            yes|=((n>>bit)&BigInt::from(1))==BigInt::from(1);
            self.set_bit(z+bit,yes)?;
        }
        Ok(())
    }
    fn signed_put(&mut self,base:usize,width:usize,sign:usize,n:&BigInt)->Result<(),String> {
        self.put(base,width,&n.abs())?;self.set_bit(sign,n.sign()==Sign::Minus)
    }
    pub(crate) fn signed_get(&self,base:usize,width:usize,sign:usize)->Result<BigInt,String> {
        let n=self.get(base,width)?;Ok(if self.bit(sign)? {-n}else{n})
    }
    pub(crate) fn assign_prediction(&mut self,n:&BigInt,den:i64)->Result<(),String> {
        let q=n/den;let r=n-&q*den;
        let c=&q+BigInt::from(u8::from(r>BigInt::from(0)));
        for (base,width,sign,z) in [(PRED,130,PRED+130,n.clone()),
            (PRED+131,92,PRED+223,q),(PRED+224,37,PRED+261,r.clone()),
            (PRED+262,92,PRED+354,c)] {self.signed_put(base,width,sign,&z)?;}
        for (base,width,z) in [(PRED,130,PRED+355),(PRED+131,92,PRED+485),
            (PRED+224,37,PRED+577),(PRED+262,92,PRED+614)] {
            self.assign_or(&self.get(base,width)?,width,z)?;
        }
        self.set_bit(PRED+706,r>BigInt::from(0))?;
        self.assign_cmp(&r.abs(),&BigInt::from(den),37,PRED+707,PRED+744)?;
        Ok(())
    }
    pub(crate) fn assign_prediction_component(&mut self,n:&BigInt,ell:usize)->Result<(),String> {
        if !(2..=8).contains(&ell) {return Err("prediction component tier".into());}
        self.assign_prediction(n,polynomial(ell).1)?;
        let mag=self.get(PRED+262,92)?;
        self.assign_cmp(&BigInt::from(I),&mag,92,SMAX+93,SMAX+185)?;
        let select=!self.bit(PRED+354)? && self.bit(SMAX+277)?;
        self.set_bit(SMAX+92,select)?;
        self.put(SMAX,92,&if select {mag}else{BigInt::from(I)})
    }
    pub(crate) fn bound(&self,map:&Map)->Result<BigInt,String> {
        map.check_row(self)?;
        Ok(match map.tier(self.owner)? {
            Some(ell) if ell>0=>self.get(SMAX,92)?,
            Some(0)=>BigInt::from(I),
            _=>BigInt::from(0),
        })
    }
}
fn read(map:&Map,s:u64,row:&OwnerRow,inputs:&Inputs,a:Word)->Result<BigInt,String> {
    match a {
        Word::Constant(x)=>Ok(BigInt::from(x)),
        Word::Bits{owner:Owner::Destination,base,width} if (BASE..BASE+BANK).contains(&base)=>
            row.get(base,width),
        _=>inputs.get(map.import(s,a)?),
    }
}
fn value(map:&Map,row:&OwnerRow,inputs:&Inputs,index:usize)->Result<Fr,String> {
    let owner=index as u64/WIDTH;let local=index%WIDTH as usize;
    map.owner(owner)?;
    let b=if owner==row.owner && (BASE..BASE+BANK).contains(&local) {row.bit(local)?}
        else {inputs.bit(owner,local)?};
    Ok(Fr::from(u64::from(b)))
}
// Component diagnostics explicitly omit the tier polynomial, never full-tier SAT.
pub(crate) fn prediction_component_terms(map:&Map,s:u64,ell:usize)->Result<Vec<Term>,String> {
    map.owner(s)?;
    if !(2..=8).contains(&ell) {return Err("prediction component tier".into());}
    let mut out=Literal {map,owner:s,terms:Vec::new(),error:None};
    emit_prediction(&mut out,ell,false);emit_smax(&mut out,ell);
    if let Some(e)=out.error {return Err(e);}
    Ok(out.terms)
}

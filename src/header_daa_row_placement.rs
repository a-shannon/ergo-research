//! Fixed ROW19 placement with a bounded native HEADER source-read join.
//! No complete X assignment, proof admission or owner seal.
use ark_bn254::Fr;
use std::{collections::{BTreeMap,BTreeSet},sync::Arc};
use ark_ff::Zero;
use blake2::{Blake2b,Digest,digest::consts::U32};
use crate::{daa_history_roster::{DaaHistoryRoster,OwnerClass,BANKS},
    header_scheduled_retirement::Merge,h21_scheduled_max_cap::{Plan as Scheduled,Writer},
    packed_owner_assembly::{HeaderSourceBinding,NativeDaaSourceLease,NativeHeaderSourceLease,
        NativeFirstAnchorPacked,
        NativePackedRow,NativePointMembershipSourceLease,NativeOwnerAuthorCensus,
        NativePhysicalAuthor,NativeAuthoredCell,NativeTypedAuthor,NativeTypedAuthorLease,
        Eligible08MapPairLease,Eligible08MapSlackAnchorBundle,Eligible08MapSourceView,
        NativeMixedMapHeaderRow},
    sparse::Term};

const ROWS:usize=1<<19;
const WIDTH:usize=1<<20;
const OWNERS:usize=1<<21;
pub(super) const RELATIONS:usize=11;
const MAP_SOURCE:[(usize,usize);2]=[(409600,419947),(442368,452715)];
const MAP_DESTINATION:[(usize,usize);2]=[(477074,487421),(492305,502652)];
const MAP_TERMS:usize=7579;
const TERM_LIMIT:usize=1_500_000;
const CAP0_OWNER:usize=845_759;
const CAP0_ORIGIN:usize=845_760;
const CAP0_BASE:usize=1_000_770;
const CAP1_BASE:usize=1_002_818;
const CAP_BITS:usize=2_048;
const FOREIGN_MAX_OWNER:usize=844_670;
const FOREIGN_MAX_BASE:[usize;2]=[999_424,1_000_097];
const FOREIGN_MAX_BITS:usize=224;
const POINT_MEMBERSHIP_OWNER:usize=845_759;
const POINT_MEMBERSHIP_COUNT:usize=528;
const POINT_MEMBERSHIP_OFFSET:usize=crate::segment_points::POINT_OFFSET;
const POINT_MEMBERSHIP_WIDTH:usize=crate::point_membership::POINT_WIDTH;
// The fixed point layout reserves wire zero, then allocates both compressed
// 33-byte source points before any auxiliary witness wires.
const POINT_MEMBERSHIP_SOURCE_START:usize=1;
const POINT_MEMBERSHIP_SOURCE_END:usize=POINT_MEMBERSHIP_SOURCE_START+POINT_MEMBERSHIP_COUNT;
const TYPED_MATURE_EIP_OWNER:usize=844_672;
const TYPED_CARRY_OWNER:usize=TYPED_MATURE_EIP_OWNER+1;
const TYPED_MATURE_SERIALIZER_SOURCES:[usize;9]=[
    843_647,843_775,843_903,844_031,844_159,844_287,844_415,844_543,844_671,
];
const TYPED_CARRY_SOURCES:[usize;2]=[TYPED_MATURE_EIP_OWNER-1,TYPED_MATURE_EIP_OWNER];
const TYPED_WORK_START:usize=987_674;
const TYPED_WORK_BITS:usize=224;
const FOREIGN_DAA_SOURCE_OWNERS:[usize;2]=[845_757,845_758];
const FOREIGN_DAA_OCCURRENCES:usize=224;
const FOREIGN_DAA_ROW_ANCHOR:usize=262_144;
const FOREIGN_DAA_WORK_START:usize=987_674;
const WORDS:[u64;24]=[19,20,21,40,41,393216,406406,507536,520726,477074,507536,
    12554,131072,131264,166664,179218,95480,108315,132096,166665,393216,262144,475136,466944];

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(super) enum Relation {Header,DaaLane(usize),Scheduled(Writer),Map(usize)}
impl Relation {
    fn slot(self,owner:usize)->Result<usize,String> {
        match self {
            Self::Header=>Ok(0),Self::DaaLane(lane)if lane<4=>Ok(1+lane),
            Self::Scheduled(Writer::Max{context,end})if context<2&&end==owner+2=>Ok(5+context),
            Self::Scheduled(Writer::Cap{context,origin})if context<2&&origin==owner+1=>Ok(7+context),
            Self::Map(context)if context<2=>Ok(9+context),
            _=>Err("ROW relation identity".into()),
        }
    }
}

#[cfg(test)]
mod c383_typed_author_join_tests {
    use super::*;

    fn fixture()->(crate::work_tree_history_plan::WorkTreeHistoryPlan,
        Batch,[NativeTypedAuthorLease<'static>;2]) {
        let plan=crate::work_tree_history_plan::WorkTreeHistoryPlan::compile(
            1_827_840,21,[0x5a;32],[0x42;28]).unwrap();
        let binding=HeaderSourceBinding::for_plan(&plan,TYPED_CARRY_OWNER).unwrap();
        let leases=std::array::from_fn(|index|
            NativeTypedAuthorLease::synthetic_carry_for_test(binding.clone(),
                TYPED_CARRY_SOURCES[index]));
        let local=TYPED_CARRY_OWNER*WIDTH;
        let mut terms=vec![Entry{relation:Relation::Header,term:Term{row:TYPED_CARRY_OWNER*ROWS,
            gate:crate::gkr::Gate{left:local,right:0,c0:Fr::from(0u64),
                c1:Fr::from(1u64),c2:Fr::from(0u64),c3:Fr::from(0u64)}}}];
        for bit in 0..TYPED_WORK_BITS {
            for &owner in &TYPED_CARRY_SOURCES {
                terms.push(Entry{relation:Relation::DaaLane(2),term:Term{
                    row:TYPED_CARRY_OWNER*ROWS+262_144,
                    gate:crate::gkr::Gate{left:owner*WIDTH+TYPED_WORK_START+bit,
                        right:0,c0:Fr::from(0u64),c1:Fr::from(1u64),
                        c2:Fr::from(0u64),c3:Fr::from(0u64)}}});
            }
        }
        let batch=Batch{owner:TYPED_CARRY_OWNER,class:OwnerClass::Carry,
            layout:Layout::fixed().digest(),source:binding,terms,
            expected:[0;RELATIONS],relations:[None;RELATIONS]};
        (plan,batch,leases)
    }

    #[test]
    fn c383_typed_author_join_no_frame_mutants() {
        let (plan,batch,leases)=fixture();
        let context=TypedAuthorJoinPlan::new(&plan).unwrap();
        let stage=batch.join_typed_author_reads(&context,&[&leases[0],&leases[1]]).unwrap();
        assert!(std::ptr::eq(stage.batch(),&batch));
        assert_eq!(stage.reads().count(),1+2*TYPED_WORK_BITS);
        let mut known=0;
        let mut open=0;
        for read in stage.reads() {
            match *read {
                NativeTypedAuthorRead::Known{operand,cell}=>{
                    assert_eq!(cell.wire(),operand.wire);
                    assert_eq!(cell.author(),NativeTypedAuthor::Tree);
                    assert!(!cell.value());
                    known+=1;
                }
                NativeTypedAuthorRead::Open{operand}=>{
                    assert_eq!(operand.wire,TYPED_CARRY_OWNER*WIDTH);
                    open+=1;
                }
            }
        }
        assert_eq!((known,open),(448,1));
        assert!(batch.join_typed_author_reads(&context,&[&leases[0]]).is_err(),
            "missing source lease must fail");
        assert!(batch.join_typed_author_reads(&context,&[&leases[0],&leases[0]]).is_err(),
            "duplicate source lease must fail");

        let mut wrong=leases.clone();wrong[0].wrong_author_for_test();
        assert!(batch.join_typed_author_reads(&context,&[&wrong[0],&wrong[1]]).is_err(),
            "same-zero wrong HEADER author must fail before stage");
        let mut wrong=leases.clone();wrong[0].wrong_parent_for_test();
        assert!(batch.join_typed_author_reads(&context,&[&wrong[0],&wrong[1]]).is_err());
        let mut wrong=leases.clone();wrong[0].wrong_source_owner_for_test();
        assert!(batch.join_typed_author_reads(&context,&[&wrong[0],&wrong[1]]).is_err());
        let mut wrong=leases.clone();wrong[0].missing_cell_for_test();
        assert!(batch.join_typed_author_reads(&context,&[&wrong[0],&wrong[1]]).is_err());
        let mut wrong=leases.clone();wrong[0].duplicate_cell_for_test();
        assert!(batch.join_typed_author_reads(&context,&[&wrong[0],&wrong[1]]).is_err());

        let mut missing=batch.clone();missing.terms.pop();
        assert!(missing.join_typed_author_reads(&context,&[&leases[0],&leases[1]]).is_err());
        let mut duplicate=batch.clone();duplicate.terms.push(duplicate.terms[1].clone());
        assert!(duplicate.join_typed_author_reads(&context,&[&leases[0],&leases[1]]).is_err());
        let mut wrong_row=batch.clone();wrong_row.terms[1].term.row+=1;
        assert!(wrong_row.join_typed_author_reads(&context,&[&leases[0],&leases[1]]).is_err());
        let mut wrong_relation=batch.clone();wrong_relation.terms[1].relation=Relation::Header;
        assert!(wrong_relation.join_typed_author_reads(&context,&[&leases[0],&leases[1]]).is_err());
        let mut wrong_wire=batch.clone();wrong_wire.terms[1].term.gate.left+=TYPED_WORK_BITS;
        assert!(wrong_wire.join_typed_author_reads(&context,&[&leases[0],&leases[1]]).is_err());
        let mut wrong_flags=batch.clone();wrong_flags.terms[1].term.gate.c3=Fr::from(1u64);
        assert!(wrong_flags.join_typed_author_reads(&context,&[&leases[0],&leases[1]]).is_err());
        let mut wrong_side=batch.clone();
        let wire=wrong_side.terms[1].term.gate.left;
        wrong_side.terms[1].term.gate.left=0;
        wrong_side.terms[1].term.gate.right=wire;
        wrong_side.terms[1].term.gate.c1=Fr::from(0u64);
        wrong_side.terms[1].term.gate.c2=Fr::from(1u64);
        assert!(wrong_side.join_typed_author_reads(&context,&[&leases[0],&leases[1]]).is_err());

        // The final gate is independent of the read iterator: a dropped or
        // duplicated occurrence cannot be published even with a valid lease.
        let mut dropped=stage.reads.clone();dropped.pop();
        assert!(checked_typed_author_stage(&batch,dropped).is_err());
        let mut doubled=stage.reads.clone();doubled.push(doubled[1]);
        assert!(checked_typed_author_stage(&batch,doubled).is_err());

        // The same typed admission also covers the resolved local Mature(Eip)
        // partition. Repeated ROW occurrences may read one physical writer.
        let (mature_plan,mature_source)=crate::packed_owner_assembly::
            c377_mature_eip_source_matrix_tests::resolved_fixture();
        let mature_binding=HeaderSourceBinding::for_plan(&mature_plan,TYPED_MATURE_EIP_OWNER)
            .unwrap();
        let mature_lease=mature_source.typed_author_lease(&mature_binding).unwrap();
        let mature_base=TYPED_MATURE_EIP_OWNER*WIDTH;
        let make_term=|wire|Entry{relation:Relation::Header,term:Term{
            row:TYPED_MATURE_EIP_OWNER*ROWS,
            gate:crate::gkr::Gate{left:wire,right:0,c0:Fr::from(0u64),
                c1:Fr::from(1u64),c2:Fr::from(0u64),c3:Fr::from(0u64)}}};
        let header_wire=mature_base+671_744;
        let mature_batch=Batch{owner:TYPED_MATURE_EIP_OWNER,
            class:OwnerClass::Mature(crate::daa_integer::Epoch::Eip),
            layout:Layout::fixed().digest(),source:mature_binding,
            terms:vec![make_term(header_wire),make_term(mature_base+989_730),
                make_term(mature_base+BANKS[0].0),make_term(header_wire),
                make_term((TYPED_MATURE_EIP_OWNER-1)*WIDTH+TYPED_WORK_START)],
            expected:[0;RELATIONS],relations:[None;RELATIONS]};
        let mature_context=TypedAuthorJoinPlan::new(&mature_plan).unwrap();
        let mature=mature_batch.join_typed_author_reads(&mature_context,&[&mature_lease]).unwrap();
        let authors=mature.reads().map(|read|match *read {
            NativeTypedAuthorRead::Known{cell,..}=>Some((cell.author(),cell.value())),
            NativeTypedAuthorRead::Open{..}=>None,
        }).collect::<Vec<_>>();
        assert_eq!(authors,vec![Some((NativeTypedAuthor::Header,false)),
            Some((NativeTypedAuthor::Tree,false)),Some((NativeTypedAuthor::Daa,false)),
            Some((NativeTypedAuthor::Header,false)),None]);
    }
}

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(super) enum OperandSide {Left,Right}

/// Ordinal is the retained term occurrence, including constant-only terms.
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(super) struct ActiveOperand {
    pub occurrence:usize,
    pub relation:Relation,
    pub row:usize,
    pub side:OperandSide,
    pub wire:usize,
    pub c1_active:bool,
    pub c2_active:bool,
    pub c3_active:bool,
}

pub(super) struct ActiveOperandIter<'a> {
    entries:std::iter::Enumerate<std::slice::Iter<'a,Entry>>,
    pending_right:Option<ActiveOperand>,
}
fn active_operands_for_term(occurrence:usize,relation:Relation,term:&Term)
    ->[Option<ActiveOperand>;2] {
    let gate=&term.gate;
    let c1_active=!gate.c1.is_zero();let c2_active=!gate.c2.is_zero();
    let c3_active=!gate.c3.is_zero();
    let left=(c1_active||c3_active).then_some(ActiveOperand{occurrence,
        relation,row:term.row,side:OperandSide::Left,
        wire:gate.left,c1_active,c2_active:false,c3_active});
    let right=(c2_active||c3_active).then_some(ActiveOperand{occurrence,
        relation,row:term.row,side:OperandSide::Right,
        wire:gate.right,c1_active:false,c2_active,c3_active});
    [left,right]
}
impl Iterator for ActiveOperandIter<'_> {
    type Item=ActiveOperand;
    fn next(&mut self)->Option<Self::Item> {
        if let Some(right)=self.pending_right.take(){return Some(right);}
        loop {
            let(occurrence,entry)=self.entries.next()?;
            let [left,right]=active_operands_for_term(occurrence,entry.relation,&entry.term);
            match(left,right){
                (Some(left),right)=>{self.pending_right=right;return Some(left);}
                (None,Some(right))=>return Some(right),
                (None,None)=>continue,
            }
        }
    }
}

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(super) enum UnresolvedRead {ForeignOwner,UnqualifiedLocal}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(super) enum SourceRead {
    Header{operand:ActiveOperand,value:bool},
    Unresolved{operand:ActiveOperand,reason:UnresolvedRead},
}

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(super) struct DaaRead {pub operand:ActiveOperand,pub value:bool}

/// One source-derived ROW batch and every active read of this owner's DAA
/// banks. Foreign-owner and local non-bank reads remain open. Neither
/// component is exposed until this partial source join succeeds.
pub(super) struct DaaReadBatch {batch:Batch,reads:Vec<DaaRead>}
impl DaaReadBatch {
    pub(super) fn batch(&self)->&Batch {&self.batch}
    pub(super) fn daa_reads(&self)->impl ExactSizeIterator<Item=&DaaRead> {self.reads.iter()}
}

/// One typed result for each active operand, in canonical operand order.
/// Values qualified by HEADER, DAA, or either exact Cap overlay are resolved;
/// foreign-owner and other unqualified local cells remain explicit open obligations.
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(super) enum NativeRead {
    Header{operand:ActiveOperand,value:bool},
    Daa{operand:ActiveOperand,value:bool},
    PointMembership{operand:ActiveOperand,value:bool},
    Cap0{operand:ActiveOperand,author:Writer,value:bool},
    Cap1{operand:ActiveOperand,author:Writer,value:bool},
    /// Authenticated foreign MAX read retained per ROW occurrence. It never
    /// becomes a local X claim and is never checked against destination bytes.
    ForeignMax{operand:ActiveOperand,cell:ForeignMaxCellView},
    /// A same-parent native Work-D endpoint read used by numeric DAA lane 2.
    /// It remains foreign to destination X and is not a DAA-bank zero claim.
    ForeignDaaLane2{operand:ActiveOperand,source_owner:usize,wire:usize,value:bool},
    Unresolved{operand:ActiveOperand,reason:UnresolvedRead},
}
impl NativeRead {
    pub(super) fn operand(self)->ActiveOperand {
        match self {
            Self::Header{operand,..}|Self::Daa{operand,..}
            |Self::PointMembership{operand,..}|Self::Cap0{operand,..}
            |Self::Cap1{operand,..}|Self::ForeignMax{operand,..}
            |Self::ForeignDaaLane2{operand,..}|Self::Unresolved{operand,..}=>operand,
        }
    }
    fn qualified_value(self)->Result<bool,String> {
        match self {
            Self::Header{value,..}|Self::Daa{value,..}
            |Self::PointMembership{value,..}|Self::Cap0{value,..}
            |Self::Cap1{value,..}=>Ok(value),
            Self::ForeignMax{operand,cell} if cell.wire==operand.wire=>Ok(cell.value),
            Self::ForeignDaaLane2{operand,wire,value,..} if wire==operand.wire=>Ok(value),
            Self::Unresolved{..}=>Err("coactive ROW unresolved ordinary source read".into()),
            _=>Err("coactive ROW foreign read wire/source mismatch".into()),
        }
    }
}

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(super) struct ForeignMaxCellView {
    pub(crate) wire:usize,pub(crate) context:usize,pub(crate) end:usize,
    pub(crate) bit:usize,pub(crate) author:crate::h21_scheduled_max_cap::MaxReplayAuthor,
    pub(crate) value:bool,
}

/// Complete immutable ROW batch and its all-or-nothing native source-read join.
/// This is a partial read join, not a complete X assignment, proof admission,
/// owner seal, or coefficient adapter.
pub(super) struct NativeReadBatch {batch:Batch,reads:Vec<NativeRead>}
impl NativeReadBatch {
    pub(super) fn batch(&self)->&Batch {&self.batch}
    pub(super) fn reads(&self)->impl ExactSizeIterator<Item=&NativeRead> {self.reads.iter()}
}

/// A producer-authored read of one canonical active occurrence. `Open` is a
/// retained obligation, never an inferred HEADER bit or local X claim.
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(super) enum NativeTypedAuthorRead {
    Known{operand:ActiveOperand,cell:NativeAuthoredCell},
    Open{operand:ActiveOperand},
}
impl NativeTypedAuthorRead {
    fn operand(self)->ActiveOperand {
        match self {Self::Known{operand,..}|Self::Open{operand}=>operand}
    }
}

pub(super) struct NativeTypedAuthorReadStage<'a> {
    batch:&'a Batch,reads:Vec<NativeTypedAuthorRead>,
}
impl NativeTypedAuthorReadStage<'_> {
    pub(super) fn reads(&self)->impl ExactSizeIterator<Item=&NativeTypedAuthorRead> {
        self.reads.iter()
    }
    pub(super) fn batch(&self)->&Batch {self.batch}
}

fn checked_typed_author_stage<'a>(
    batch:&'a Batch,reads:Vec<NativeTypedAuthorRead>,
)->Result<NativeTypedAuthorReadStage<'a>,String> {
    let mut expected=batch.active_operands();
    for read in &reads {
        if Some(read.operand())!=expected.next() {
            return Err("typed author missing/duplicate/reordered ROW occurrence".into());
        }
    }
    if expected.next().is_some() {
        return Err("typed author missing ROW occurrence".into());
    }
    Ok(NativeTypedAuthorReadStage{batch,reads})
}

fn check_mature_serializer_operand(
    operand:ActiveOperand,cell:NativeAuthoredCell,
)->Result<(),String> {
    if operand.side!=OperandSide::Left || operand.relation!=Relation::DaaLane(1)
        || cell.wire()!=operand.wire || !operand.c1_active
        || operand.c2_active || operand.c3_active {
        return Err("typed Mature serializer active occurrence/side/branch/wire".into());
    }
    Ok(())
}

fn admit_mature_serializer_occurrence(
    operand:ActiveOperand,cell:NativeAuthoredCell,
)->Result<NativeTypedAuthorRead,String> {
    check_mature_serializer_operand(operand,cell)?;
    if cell.author()!=NativeTypedAuthor::Header {
        return Err("typed Mature serializer wrong physical author at occurrence".into());
    }
    Ok(NativeTypedAuthorRead::Known{operand,cell})
}

#[cfg(test)]
fn mutant_skip_mature_serializer_author_for_test(
    operand:ActiveOperand,cell:NativeAuthoredCell,
)->Result<NativeTypedAuthorRead,String> {
    check_mature_serializer_operand(operand,cell)?;
    Ok(NativeTypedAuthorRead::Known{operand,cell})
}

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(super) enum NativeXAuthor {Header,Daa,Cap0(Writer),Cap1(Writer),PointMembership}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(super) struct NativeXClaim {pub wire:usize,pub author:NativeXAuthor,pub value:bool}

/// Census every active operand in the fixed point bank before any value read.
/// The returned indexes preserve the canonical active-operand order.
fn prepare_point_membership_operands(
    batch:&Batch,owner:usize,
)->Result<Vec<(usize,ActiveOperand)>,String> {
    if owner!=POINT_MEMBERSHIP_OWNER || batch.owner!=owner {
        return Err("point membership ROW owner".into());
    }
    let base=owner.checked_mul(WIDTH)
        .and_then(|base|base.checked_add(POINT_MEMBERSHIP_OFFSET))
        .ok_or("point membership physical base overflow")?;
    let bank_end=base.checked_add(POINT_MEMBERSHIP_WIDTH)
        .ok_or("point membership physical end overflow")?;
    let source_start=base.checked_add(POINT_MEMBERSHIP_SOURCE_START)
        .ok_or("point membership source start overflow")?;
    let source_end=base.checked_add(POINT_MEMBERSHIP_SOURCE_END)
        .ok_or("point membership source end overflow")?;
    let mut seen=BTreeSet::new();
    let mut selected=Vec::with_capacity(POINT_MEMBERSHIP_COUNT);
    for (index,operand) in batch.active_operands().enumerate() {
        if !(base..bank_end).contains(&operand.wire) {continue;}
        if !(source_start..source_end).contains(&operand.wire) {
            return Err("point membership ROW non-source wire in point bank".into());
        }
        if operand.relation!=Relation::Header {
            return Err("point membership ROW relation overlap".into());
        }
        if !seen.insert(operand.wire) {
            return Err("point membership duplicate physical wire".into());
        }
        selected.push((index,operand));
    }
    if selected.len()!=POINT_MEMBERSHIP_COUNT {
        return Err("point membership active ROW census count".into());
    }
    Ok(selected)
}

/// An atomic, owner-local partial X/ROW stage. The complete canonical ROW
/// batch and all active occurrences travel with unique source-owned X claims.
/// Open reads remain explicit; this does not assign the rest of X or admit a
/// witness, commitment, transcript, or proof.
pub(super) struct NativePartialXRowStage<'a> {
    row:&'a NativePackedRow,batch:Batch,reads:Vec<NativeRead>,claims:Vec<NativeXClaim>,
}
impl NativePartialXRowStage<'_> {
    pub(super) fn batch(&self)->&Batch {&self.batch}
    pub(super) fn reads(&self)->impl ExactSizeIterator<Item=&NativeRead> {self.reads.iter()}
    pub(super) fn claims(&self)->impl ExactSizeIterator<Item=&NativeXClaim> {self.claims.iter()}
    pub(super) fn row_owner(&self)->usize {self.row.owner()}

    /// Join every locally resolved ROW claim to the complete physical X row.
    /// Foreign typed reads remain reads of their own source owner.
    pub(super) fn join_physical_census(
        &self,expected:&HeaderSourceBinding,census:&NativeOwnerAuthorCensus,
    )->Result<[usize;6],String> {
        if self.row.owner()!=845_759 || &self.batch.source!=expected {
            return Err("physical X/ROW owner or source binding mismatch".into());
        }
        census.check_complete(expected,self.row)?;
        let base=self.row.owner().checked_mul(WIDTH)
            .ok_or("physical X/ROW owner base overflow")?;
        let mut counts=[0usize;6];
        for local in 0..WIDTH {
            let wire=base.checked_add(local).ok_or("physical X/ROW wire overflow")?;
            let (author,value)=census.checked_cell(expected,self.row,wire)?;
            let packed=(self.row.packed_bytes()[local/8]>>(local%8))&1!=0;
            if value!=packed {return Err("physical X/ROW packed value mismatch".into());}
            let index=match author {
                NativePhysicalAuthor::Header=>0,
                NativePhysicalAuthor::PointMembership=>1,
                NativePhysicalAuthor::Tree=>2,
                NativePhysicalAuthor::Daa=>3,
                NativePhysicalAuthor::Bank53=>4,
                NativePhysicalAuthor::Cap=>5,
            };
            counts[index]=counts[index].checked_add(1)
                .ok_or("physical X/ROW author count overflow")?;
        }
        if counts!=[536_622,8_192,401_362,81_920,16_384,4_096] {
            return Err("physical X/ROW author partition mismatch".into());
        }
        for claim in &self.claims {
            let local=claim.wire.checked_sub(base).filter(|local|*local<WIDTH)
                .ok_or("physical X/ROW local claim outside owner")?;
            let (author,value)=census.checked_cell(expected,self.row,claim.wire)?;
            let expected_author=match claim.author {
                NativeXAuthor::Header=>NativePhysicalAuthor::Header,
                NativeXAuthor::PointMembership=>NativePhysicalAuthor::PointMembership,
                NativeXAuthor::Daa=>NativePhysicalAuthor::Daa,
                NativeXAuthor::Cap0(_)|NativeXAuthor::Cap1(_)=>NativePhysicalAuthor::Cap,
            };
            if author!=expected_author || value!=claim.value ||
                value!=((self.row.packed_bytes()[local/8]>>(local%8))&1!=0) {
                return Err("physical X/ROW local claim author or value mismatch".into());
            }
        }
        Ok(counts)
    }
}

fn prepare_foreign_max_reads(
    batch:&Batch,source:&HeaderSourceBinding,owner:usize,
    lease:&crate::packed_owner_assembly::Eligible08ForeignMaxReadLease,
)->Result<Vec<Option<ForeignMaxCellView>>,String> {
    lease.require_destination(source,owner)?;
    let mut counts=[0usize;2];
    let mut seen=[vec![false;FOREIGN_MAX_BITS],vec![false;FOREIGN_MAX_BITS]];
    let mut reads=vec![None;batch.active_operands().count()];
    for (index,operand) in batch.active_operands().enumerate() {
        let context=match operand.relation {
            Relation::Scheduled(Writer::Cap{context,origin})
                if origin==owner+1 && context<2=>context,
            _=>continue,
        };
        if operand.wire/ WIDTH != FOREIGN_MAX_OWNER {continue;}
        let base=FOREIGN_MAX_OWNER.checked_mul(WIDTH)
            .and_then(|x|x.checked_add(FOREIGN_MAX_BASE[context]))
            .ok_or("partial X/ROW foreign MAX wire overflow")?;
        let bit=operand.wire.checked_sub(base)
            .filter(|bit|*bit<FOREIGN_MAX_BITS)
            .ok_or("partial X/ROW foreign MAX out-of-domain occurrence")?;
        if seen[context][bit] {return Err("partial X/ROW duplicate foreign MAX occurrence".into());}
        let cell=lease.cell(context,bit)
            .ok_or("partial X/ROW foreign MAX missing typed source cell")?;
        let expected_wire=FOREIGN_MAX_OWNER*WIDTH+FOREIGN_MAX_BASE[context]+bit;
        if cell.context!=context || cell.bit!=bit || cell.end!=FOREIGN_MAX_OWNER+2
            || cell.wire!=expected_wire || operand.wire!=expected_wire
            || cell.author!=crate::h21_scheduled_max_cap::MaxReplayAuthor::Scheduled(
                Writer::Max{context,end:FOREIGN_MAX_OWNER+2}) {
            return Err("partial X/ROW foreign MAX occurrence/order/author/value".into());
        }
        reads[index]=Some(cell);
        seen[context][bit]=true;
        counts[context]+=1;
    }
    if counts!=[FOREIGN_MAX_BITS;2] || seen.iter().any(|context|context.iter().any(|bit|!*bit)) {
        return Err("partial X/ROW foreign MAX exact per-context occurrence census".into());
    }
    Ok(reads)
}

fn prepare_foreign_daa_lane2_reads(
    batch:&Batch,source:&HeaderSourceBinding,owner:usize,
    leases:[&crate::packed_owner_assembly::ForeignDaaWorkReadLease;2],
)->Result<Vec<Option<(usize,usize)>>,String> {
    if owner!=CAP0_OWNER || batch.owner!=owner || batch.class!=OwnerClass::Carry
        || batch.source!=*source {
        return Err("foreign DAA lane2 destination batch identity".into());
    }
    let work=crate::work_tree_layout::Endpoints::new().work;
    if work!=(FOREIGN_DAA_WORK_START..FOREIGN_DAA_WORK_START+FOREIGN_DAA_OCCURRENCES)
        .collect::<Vec<_>>() {
        return Err("foreign numeric DAA Work-D endpoint geometry changed".into());
    }
    for (index,lease) in leases.iter().enumerate() {
        lease.require_destination(source,owner)?;
        if lease.source_owner()!=FOREIGN_DAA_SOURCE_OWNERS[index] {
            return Err("foreign DAA lane2 source lease order/duplicate".into());
        }
    }
    let mut counts=[0usize;2];
    let mut wires=[BTreeSet::new(),BTreeSet::new()];
    let mut reads=vec![None;batch.active_operands().count()];
    for (index,operand) in batch.active_operands().enumerate() {
        if operand.relation!=Relation::DaaLane(2) {continue;}
        let source_owner=operand.wire/WIDTH;
        if source_owner==owner {continue;}
        let Some(source_index)=FOREIGN_DAA_SOURCE_OWNERS.iter().position(|owner|*owner==source_owner)
            else {return Err("foreign DAA lane2 source owner outside exact lease set".into());};
        if leases[source_index].source_owner()!=source_owner
            || operand.wire.checked_sub(source_owner*WIDTH)
                .filter(|local|(FOREIGN_DAA_WORK_START..
                    FOREIGN_DAA_WORK_START+FOREIGN_DAA_OCCURRENCES).contains(local)).is_none()
            || !wires[source_index].insert(operand.wire) {
            return Err("foreign DAA lane2 occurrence/source owner/duplicate wire".into());
        }
        reads[index]=Some((source_index,operand.wire));
        counts[source_index]+=1;
    }
    if counts!=[FOREIGN_DAA_OCCURRENCES;2]
        || wires.iter().any(|set|set.len()!=FOREIGN_DAA_OCCURRENCES) {
        return Err("foreign DAA lane2 exact source-owner occurrence census".into());
    }
    Ok(reads)
}

#[cfg(test)]
mod c367_foreign_daa_work_preflight_tests {
    use super::*;
    use ark_ff::One;
    use crate::daa_history_roster::OwnerClass;
    use crate::packed_owner_assembly::ForeignDaaWorkReadLease;
    use std::collections::BTreeSet;

    fn fixture()->(Batch,HeaderSourceBinding,[ForeignDaaWorkReadLease;2]) {
        let destination=HeaderSourceBinding::diagnostic_for_test(CAP0_OWNER);
        let leases=std::array::from_fn(|index| {
            let owner=FOREIGN_DAA_SOURCE_OWNERS[index];
            ForeignDaaWorkReadLease::synthetic_for_test(destination.clone(),owner,
                std::array::from_fn(|bit|bit==index))
        });
        let mut terms=Vec::new();
        for bit in 0..FOREIGN_DAA_OCCURRENCES {
            for owner in [FOREIGN_DAA_SOURCE_OWNERS[1],FOREIGN_DAA_SOURCE_OWNERS[0]] {
                let wire=owner*WIDTH+FOREIGN_DAA_WORK_START+bit;
                terms.push(Entry{relation:Relation::DaaLane(2),term:Term{row:CAP0_OWNER*ROWS+
                FOREIGN_DAA_ROW_ANCHOR,gate:crate::gkr::Gate{left:wire,right:0,
                        c0:Fr::zero(),c1:if owner==FOREIGN_DAA_SOURCE_OWNERS[1]
                            {Fr::one()}else{-Fr::one()},c2:Fr::zero(),c3:Fr::zero()}}});
            }
        }
        let batch=Batch{owner:CAP0_OWNER,class:OwnerClass::Carry,layout:Layout::fixed().digest(),
            source:destination.clone(),terms,expected:[0;RELATIONS],relations:[None;RELATIONS]};
        (batch,destination,leases)
    }

    fn run(batch:&Batch,destination:&HeaderSourceBinding,
        leases:&[ForeignDaaWorkReadLease;2])->Result<Vec<Option<(usize,usize)>>,String> {
        prepare_foreign_daa_lane2_reads(batch,destination,CAP0_OWNER,
            [&leases[0],&leases[1]])
    }

    #[test]
    fn c367_exact_numeric_work_source_census_and_author_fail_closed() {
        let (batch,destination,leases)=fixture();
        let reads=run(&batch,&destination,&leases).unwrap();
        assert_eq!(reads.iter().flatten().count(),448);
        let mut wires=[BTreeSet::new(),BTreeSet::new()];
        for entry in reads.iter().flatten(){wires[entry.0].insert(entry.1);}
        assert_eq!(wires.map(|set|set.len()),[224,224]);

        let mut swapped=leases.clone();swapped.swap(0,1);
        assert!(run(&batch,&destination,&swapped).is_err());
        let duplicate_lease=[leases[0].clone(),leases[0].clone()];
        assert!(run(&batch,&destination,&duplicate_lease).is_err());
        let wrong_destination=destination.mutated_field_for_test(0);
        assert!(run(&batch,&wrong_destination,&leases).is_err());
        for mutate in [0,1,2,3] {
            let mut wrong=leases.clone();
            match mutate {
                0=>wrong[0].mutate_source_owner_for_test(845_756),
                1=>wrong[0].mutate_source_parent_for_test(),
                2=>wrong[0].mutate_source_identity_for_test(),
                _=>wrong[0].mutate_value_for_test(),
            }
            assert!(run(&batch,&destination,&wrong).is_err());
        }
        let mut wrong_author=leases.clone();wrong_author[1].mutate_author_for_test();
        assert!(run(&batch,&destination,&wrong_author).is_err());

        let mut missing=batch.clone();missing.terms.pop();
        assert!(run(&missing,&destination,&leases).is_err());
        let mut duplicate=batch.clone();duplicate.terms.push(duplicate.terms[0].clone());
        assert!(run(&duplicate,&destination,&leases).is_err());
        let mut third_foreign_owner=batch.clone();
        let third_owner=845_756;
        let third_wire=third_owner*WIDTH+FOREIGN_DAA_WORK_START;
        third_foreign_owner.terms.push(Entry{relation:Relation::DaaLane(2),term:Term{
            row:CAP0_OWNER*ROWS+FOREIGN_DAA_ROW_ANCHOR,
            gate:crate::gkr::Gate{left:third_wire,right:0,c0:Fr::zero(),c1:Fr::one(),
                c2:Fr::zero(),c3:Fr::zero()}}});
        assert!(run(&third_foreign_owner,&destination,&leases).is_err());
        let mut wrong_lane=batch.clone();
        wrong_lane.terms[0].term.gate.left=FOREIGN_DAA_SOURCE_OWNERS[0]*WIDTH+BANKS[2].0;
        assert!(run(&wrong_lane,&destination,&leases).is_err());
    }
}

#[cfg(test)]
mod c365_foreign_max_preflight_tests {
    use super::*;
    use ark_ff::{One,Zero};

    type SyntheticLease=crate::packed_owner_assembly::Eligible08ForeignMaxReadLease;
    fn fixture()->(Batch,SyntheticLease,HeaderSourceBinding) {
        let binding=HeaderSourceBinding::diagnostic_for_test(CAP0_OWNER);
        let mut terms=Vec::new();
        let mut cells=Vec::new();
        for context in 0..2 {
            for bit in 0..FOREIGN_MAX_BITS {
                let writer=Writer::Cap{context,origin:CAP0_OWNER+1};
                let wire=FOREIGN_MAX_OWNER*WIDTH+FOREIGN_MAX_BASE[context]+bit;
                terms.push(Entry{relation:Relation::Scheduled(writer),term:Term{row:terms.len(),
                    gate:crate::gkr::Gate{left:wire,right:0,c0:Fr::zero(),c1:Fr::one(),
                        c2:Fr::zero(),c3:Fr::zero()}}});
                cells.push(crate::packed_owner_assembly::Eligible08ForeignMaxCell::synthetic_for_test(
                    wire,context,FOREIGN_MAX_OWNER+2,bit,
                    crate::h21_scheduled_max_cap::MaxReplayAuthor::Scheduled(
                        Writer::Max{context,end:FOREIGN_MAX_OWNER+2}),bit%2==0));
            }
        }
        let batch=Batch{owner:CAP0_OWNER,class:OwnerClass::Carry,layout:Layout::fixed().digest(),
            source:binding.clone(),terms,expected:[0;RELATIONS],relations:[None;RELATIONS]};
        (batch,SyntheticLease::synthetic_for_test(binding.clone(),FOREIGN_MAX_OWNER,cells),binding)
    }

    #[test]
    fn c365_synthetic_foreign_max_preflight_binds_448_occurrences_before_reads() {
        let (batch,lease,binding)=fixture();
        let reads=prepare_foreign_max_reads(&batch,&binding,CAP0_OWNER,&lease).unwrap();
        assert_eq!(reads.len(),448);
        for (index,operand) in batch.active_operands().enumerate() {
            let context=match operand.relation {
                Relation::Scheduled(Writer::Cap{context,..})=>context,_=>unreachable!(),
            };
            let bit=operand.wire-(FOREIGN_MAX_OWNER*WIDTH+FOREIGN_MAX_BASE[context]);
            let cell=reads[index].unwrap();
            assert_eq!((cell.context,cell.bit,cell.wire,cell.value),
                (context,bit,operand.wire,bit%2==0));
        }
        let mut shuffled=batch.clone();shuffled.terms.swap(0,1);shuffled.terms.swap(100,300);
        assert!(prepare_foreign_max_reads(&shuffled,&binding,CAP0_OWNER,&lease).is_ok());
        let wrong_binding=binding.mutated_field_for_test(0);
        assert!(prepare_foreign_max_reads(&batch,&wrong_binding,CAP0_OWNER,&lease).is_err());
        assert!(prepare_foreign_max_reads(&batch,&binding,CAP0_OWNER+1,&lease).is_err());

        let mut wrong_wire=fixture().1;wrong_wire.mutate_first_cell_wire_for_test();
        assert!(prepare_foreign_max_reads(&batch,&binding,CAP0_OWNER,&wrong_wire).is_err());
        let mut wrong_order=fixture().1;wrong_order.swap_first_two_cells_for_test();
        assert!(prepare_foreign_max_reads(&batch,&binding,CAP0_OWNER,&wrong_order).is_err());
        let mut wrong_author=fixture().1;wrong_author.mutate_first_cell_author_for_test();
        assert!(prepare_foreign_max_reads(&batch,&binding,CAP0_OWNER,&wrong_author).is_err());
        let mut missing=fixture().1;missing.truncate_cells_for_test(447);
        assert!(prepare_foreign_max_reads(&batch,&binding,CAP0_OWNER,&missing).is_err());
        let mut duplicate=batch.clone();
        duplicate.terms[0].term.gate.left=duplicate.terms[1].term.gate.left;
        assert!(prepare_foreign_max_reads(&duplicate,&binding,CAP0_OWNER,&lease).is_err());
        let mut missing_occurrence=batch.clone();missing_occurrence.terms.pop();
        assert!(prepare_foreign_max_reads(&missing_occurrence,&binding,CAP0_OWNER,&lease).is_err());
    }
}

/// One active ROW operand whose local wire is authored by the first modern
/// Cap0 producer. The private writer field keeps Cap0 provenance attached to
/// the claim; it is not a general X assignment.
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(super) struct Cap0OverlayClaim {
    operand:ActiveOperand,
    author:Writer,
    value:bool,
}
impl Cap0OverlayClaim {
    pub(super) fn operand(&self)->ActiveOperand {self.operand}
    pub(super) fn author(&self)->Writer {self.author}
    pub(super) fn value(&self)->bool {self.value}
}

/// A source-only Cap0 overlay over the canonical owner ROW batch. It retains
/// the exact placed Cap0 producer rows and all 2,048 typed source cells. Only
/// active Cap0-relation operands inside Cap0's declared local X domain receive
/// claims; every other operand remains outside this overlay and open. The
/// open count below covers only Cap0-relation operands outside Cap0's domain,
/// not all open reads in the retained ROW batch.
#[derive(Clone)]
pub(super) struct Cap0RowOverlay {
    batch:Batch,
    binding:HeaderSourceBinding,
    source_rows:Vec<Term>,
    source_cells:Vec<(usize,bool)>,
    claims:Vec<Cap0OverlayClaim>,
    cap0_relation_active_occurrences:usize,
    open_cap0_relation_occurrences:usize,
}
impl Cap0RowOverlay {
    pub(super) fn owner(&self)->usize {self.batch.owner}
    pub(super) fn batch(&self)->&Batch {&self.batch}
    pub(super) fn source_row_count(&self)->usize {self.source_rows.len()}
    pub(super) fn source_cells(&self)->impl ExactSizeIterator<Item=&(usize,bool)> {
        self.source_cells.iter()
    }
    pub(super) fn claims(&self)->impl ExactSizeIterator<Item=&Cap0OverlayClaim> {
        self.claims.iter()
    }
    pub(super) fn cap0_relation_active_occurrences(&self)->usize {
        self.cap0_relation_active_occurrences
    }
    pub(super) fn open_cap0_relation_occurrences(&self)->usize {
        self.open_cap0_relation_occurrences
    }

    /// Recheck the occurrence-preserving claim ledger against the retained
    /// canonical ROW batch and typed Cap0 cells. This checker never reads the
    /// NativePackedRow parent assignment.
    pub(super) fn validate(&self)->Result<(),String> {
        let writer=Writer::Cap{context:0,origin:CAP0_ORIGIN};
        if self.batch.owner!=CAP0_OWNER || self.batch.class!=OwnerClass::Carry
            || self.batch.source!=self.binding
            || self.batch.layout!=Layout::fixed().digest() {
            return Err("Cap0 ROW overlay binding/owner/layout".into());
        }
        let placed=self.batch.terms().filter_map(|(relation,term)|
            (relation==Relation::Scheduled(writer)).then(||term.clone())).collect::<Vec<_>>();
        if self.source_rows.len()!=6_419 || placed!=self.source_rows {
            return Err("Cap0 ROW overlay exact source-row order/multiplicity".into());
        }
        if self.source_cells.len()!=CAP_BITS || self.source_cells.iter().enumerate().any(|(i,(wire,_))|
            *wire!=CAP0_BASE+i) {
            return Err("Cap0 ROW overlay exact source-cell domain/order".into());
        }
        let mut expected=Vec::new();
        let mut active_occurrences=0usize;
        for operand in self.batch.active_operands().filter(|op|op.relation==Relation::Scheduled(writer)) {
            active_occurrences=active_occurrences.checked_add(1)
                .ok_or("Cap0 ROW overlay active occurrence overflow")?;
            if let Some(local)=operand.wire.checked_sub(CAP0_OWNER*WIDTH)
                .filter(|local|(CAP0_BASE..CAP0_BASE+CAP_BITS).contains(local)) {
                let value=self.source_cells[local-CAP0_BASE].1;
                expected.push(Cap0OverlayClaim{operand,author:writer,value});
            }
        }
        let open_occurrences=active_occurrences.checked_sub(expected.len())
            .ok_or("Cap0 ROW overlay open occurrence underflow")?;
        if active_occurrences!=self.cap0_relation_active_occurrences
            || open_occurrences!=self.open_cap0_relation_occurrences
            || expected!=self.claims {
            return Err("Cap0 ROW overlay active occurrence/source claim census".into());
        }
        Ok(())
    }

    fn matches_batch(&self,batch:&Batch)->bool {
        self.batch.owner==batch.owner && self.batch.class==batch.class
            && self.batch.layout==batch.layout && self.batch.source==batch.source
            && self.batch.expected==batch.expected && self.batch.relations==batch.relations
            && self.batch.terms.len()==batch.terms.len()
            && self.batch.terms.iter().zip(&batch.terms)
                .all(|(left,right)|left.relation==right.relation && left.term==right.term)
    }

    #[cfg(test)]
    pub(super) fn remove_first_claim_for_test(&mut self) {if !self.claims.is_empty(){self.claims.remove(0);}}
    #[cfg(test)]
    pub(super) fn duplicate_first_claim_for_test(&mut self) {if let Some(first)=self.claims.first().copied(){self.claims.push(first);}}
    #[cfg(test)]
    pub(super) fn duplicate_first_claim_with_conflicting_value_for_test(&mut self) {
        if let Some(mut first)=self.claims.first().copied(){first.value=!first.value;self.claims.push(first);}
    }
    #[cfg(test)]
    pub(super) fn flip_first_claim_for_test(&mut self) {if let Some(first)=self.claims.first_mut(){first.value=!first.value;}}
    #[cfg(test)]
    pub(super) fn change_first_author_for_test(&mut self,author:Writer) {if let Some(first)=self.claims.first_mut(){first.author=author;}}
    #[cfg(test)]
    pub(super) fn change_first_domain_for_test(&mut self) {if let Some(first)=self.claims.first_mut(){first.operand.wire=CAP0_OWNER*WIDTH+CAP0_BASE+CAP_BITS;}}
    #[cfg(test)]
    pub(super) fn change_binding_for_test(
        &mut self,plan:&crate::work_tree_history_plan::WorkTreeHistoryPlan,owner:usize,
    )->Result<(),String> {self.binding=HeaderSourceBinding::for_plan(plan,owner)?;Ok(())}
    #[cfg(test)]
    pub(super) fn change_self_consistent_binding_for_test(
        &mut self,plan:&crate::work_tree_history_plan::WorkTreeHistoryPlan,owner:usize,
    )->Result<(),String> {
        let binding=HeaderSourceBinding::for_plan(plan,owner)?;
        self.batch.source=binding.clone();
        self.binding=binding;
        Ok(())
    }
}

/// Source-owned local Cap1 occurrence; foreign MAX imports remain open.
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(super) struct Cap1OverlayClaim {
    operand:ActiveOperand,
    author:Writer,
    value:bool,
}
impl Cap1OverlayClaim {
    pub(super) fn operand(&self)->ActiveOperand {self.operand}
    pub(super) fn author(&self)->Writer {self.author}
    pub(super) fn value(&self)->bool {self.value}
}

/// The second context's exact placed ROW source and 2,048 typed local cells.
/// Its claims cover only active Cap1 operands inside Cap1's declared X domain.
#[derive(Clone)]
pub(super) struct Cap1RowOverlay {
    batch:Batch,
    binding:HeaderSourceBinding,
    source_rows:Vec<Term>,
    source_cells:Vec<(usize,bool)>,
    claims:Vec<Cap1OverlayClaim>,
    cap1_relation_active_occurrences:usize,
    open_cap1_relation_occurrences:usize,
}
impl Cap1RowOverlay {
    pub(super) fn owner(&self)->usize {self.batch.owner}
    pub(super) fn batch(&self)->&Batch {&self.batch}
    pub(super) fn source_row_count(&self)->usize {self.source_rows.len()}
    pub(super) fn source_cells(&self)->impl ExactSizeIterator<Item=&(usize,bool)> {
        self.source_cells.iter()
    }
    pub(super) fn claims(&self)->impl ExactSizeIterator<Item=&Cap1OverlayClaim> {
        self.claims.iter()
    }
    pub(super) fn cap1_relation_active_occurrences(&self)->usize {
        self.cap1_relation_active_occurrences
    }
    pub(super) fn open_cap1_relation_occurrences(&self)->usize {
        self.open_cap1_relation_occurrences
    }

    /// Recompute the ordered occurrence ledger from retained ROW terms and
    /// source cells. This never treats the parent's HEADER-zero area as Cap1.
    pub(super) fn validate(&self)->Result<(),String> {
        let writer=Writer::Cap{context:1,origin:CAP0_ORIGIN};
        if self.batch.owner!=CAP0_OWNER || self.batch.class!=OwnerClass::Carry
            || self.batch.source!=self.binding
            || self.batch.layout!=Layout::fixed().digest() {
            return Err("Cap1 ROW overlay binding/owner/layout".into());
        }
        let placed=self.batch.terms().filter_map(|(relation,term)|
            (relation==Relation::Scheduled(writer)).then(||term.clone())).collect::<Vec<_>>();
        if self.source_rows.len()!=6_419 || placed!=self.source_rows {
            return Err("Cap1 ROW overlay exact source-row order/multiplicity".into());
        }
        if self.source_cells.len()!=CAP_BITS || self.source_cells.iter().enumerate().any(|(i,(wire,_))|
            *wire!=CAP1_BASE+i) {
            return Err("Cap1 ROW overlay exact source-cell domain/order".into());
        }
        let mut expected=Vec::new();
        let mut active_occurrences=0usize;
        for operand in self.batch.active_operands().filter(|op|op.relation==Relation::Scheduled(writer)) {
            active_occurrences=active_occurrences.checked_add(1)
                .ok_or("Cap1 ROW overlay active occurrence overflow")?;
            if let Some(local)=operand.wire.checked_sub(CAP0_OWNER*WIDTH)
                .filter(|local|(CAP1_BASE..CAP1_BASE+CAP_BITS).contains(local)) {
                expected.push(Cap1OverlayClaim{operand,author:writer,
                    value:self.source_cells[local-CAP1_BASE].1});
            }
        }
        let open_occurrences=active_occurrences.checked_sub(expected.len())
            .ok_or("Cap1 ROW overlay open occurrence underflow")?;
        if active_occurrences!=self.cap1_relation_active_occurrences
            || open_occurrences!=self.open_cap1_relation_occurrences
            || expected!=self.claims {
            return Err("Cap1 ROW overlay active occurrence/source claim census".into());
        }
        Ok(())
    }

    fn matches_batch(&self,batch:&Batch)->bool {
        self.batch.owner==batch.owner && self.batch.class==batch.class
            && self.batch.layout==batch.layout && self.batch.source==batch.source
            && self.batch.expected==batch.expected && self.batch.relations==batch.relations
            && self.batch.terms.len()==batch.terms.len()
            && self.batch.terms.iter().zip(&batch.terms)
                .all(|(left,right)|left.relation==right.relation && left.term==right.term)
    }

    #[cfg(test)]
    pub(super) fn remove_first_claim_for_test(&mut self) {if !self.claims.is_empty(){self.claims.remove(0);}}
    #[cfg(test)]
    pub(super) fn duplicate_first_claim_for_test(&mut self) {
        if let Some(first)=self.claims.first().copied(){self.claims.push(first);}
    }
    #[cfg(test)]
    pub(super) fn duplicate_first_claim_with_conflicting_value_for_test(&mut self) {
        if let Some(mut first)=self.claims.first().copied(){first.value=!first.value;self.claims.push(first);}
    }
    #[cfg(test)]
    pub(super) fn flip_first_claim_for_test(&mut self) {
        if let Some(first)=self.claims.first_mut(){first.value=!first.value;}
    }
    #[cfg(test)]
    pub(super) fn flip_first_source_cell_for_test(&mut self) {
        if let Some(first)=self.source_cells.first_mut(){first.1=!first.1;}
        for claim in &mut self.claims {
            if claim.operand.wire==CAP0_OWNER*WIDTH+CAP1_BASE {claim.value=!claim.value;}
        }
    }
    #[cfg(test)]
    pub(super) fn change_first_author_for_test(&mut self,author:Writer) {
        if let Some(first)=self.claims.first_mut(){first.author=author;}
    }
    #[cfg(test)]
    pub(super) fn change_first_domain_for_test(&mut self) {
        if let Some(first)=self.claims.first_mut(){first.operand.wire=CAP0_OWNER*WIDTH+CAP1_BASE+CAP_BITS;}
    }
    #[cfg(test)]
    pub(super) fn change_binding_for_test(
        &mut self,plan:&crate::work_tree_history_plan::WorkTreeHistoryPlan,owner:usize,
    )->Result<(),String> {self.binding=HeaderSourceBinding::for_plan(plan,owner)?;Ok(())}
    #[cfg(test)]
    pub(super) fn change_self_consistent_binding_for_test(
        &mut self,plan:&crate::work_tree_history_plan::WorkTreeHistoryPlan,owner:usize,
    )->Result<(),String> {
        let binding=HeaderSourceBinding::for_plan(plan,owner)?;
        self.batch.source=binding.clone();self.binding=binding;Ok(())
    }
}

/// The descriptor identifies this layout only; it does not bind all sources,
/// a witness, a transcript, or the future common proof relation.
#[derive(Clone,Copy)]
pub(super) struct Layout {paired_map:bool,general_map:bool}
impl Layout {
    pub(super) fn fixed()->Self{Self{paired_map:false,general_map:false}}
    pub(super) fn paired_map()->Self{Self{paired_map:true,general_map:false}}
    pub(super) fn paired_map_general()->Self{Self{paired_map:true,general_map:true}}
    pub(super) fn descriptor(self)->Vec<u8> {
        if self.paired_map {
            let mut out=if self.general_map {b"c451-row19-paired-map-general-v4\0".to_vec()}
                else {b"c439-row19-paired-map-v2\0".to_vec()};
            out.extend_from_slice(&Self::fixed().digest());
            let cut=crate::bank53_map::CutDescriptor::eligible08().canonical_identity();
            out.extend_from_slice(&(cut.len()as u64).to_le_bytes());
            out.extend_from_slice(&cut);
            out.extend_from_slice(&(RELATIONS as u64).to_le_bytes());
            for slot in 0..RELATIONS {out.extend_from_slice(&(slot as u64).to_le_bytes());}
            for context in 0..2 {
                for value in [context,MAP_SOURCE[context].0,MAP_SOURCE[context].1,
                    MAP_DESTINATION[context].0,MAP_DESTINATION[context].1] {
                    out.extend_from_slice(&(value as u64).to_le_bytes());
                }
            }
            if self.general_map {
                out.extend_from_slice(b"all-h21-owner-classes-including-padding-map-zero-equations\0");
            }
            return out;
        }
        let mut out=b"c121a-row19-v1\0".to_vec();
        for word in WORDS {out.extend_from_slice(&word.to_le_bytes());}out
    }
    pub(super) fn digest(self)->[u8;32] {Blake2b::<U32>::digest(self.descriptor()).into()}
    fn f3(q:usize)->Result<usize,String> {
        if q>=132096{return Err("DAA source exceeds f3 envelope".into());}
        Ok(if q<95480{166664+q}else if q<108315{166665+q}else{393216+q-108315})
    }
    fn inverse_f3(q:usize)->Option<usize> {
        match q {166664..=262143=>Some(q-166664),262145..=274979=>Some(q-166665),
            393216..=416996=>Some(q-393216+108315),_=>None}
    }
    fn local(self,class:OwnerClass,relation:Relation,q:usize)->Result<usize,String> {
        match relation {
            Relation::Map(context)if self.paired_map && (self.general_map||class==OwnerClass::Genesis) && context<2
                && (MAP_SOURCE[context].0..MAP_SOURCE[context].1).contains(&q)=>
                Ok(MAP_DESTINATION[context].0+q-MAP_SOURCE[context].0),
            Relation::Header if q<393216=>Ok(q),
            Relation::Header if q<406406=>Ok(507536+q-393216),
            Relation::Header=>Err("HEADER source ROW extent".into()),
            Relation::DaaLane(0)if class==OwnerClass::M1&&q<12554=>Ok(166664+q),
            Relation::DaaLane(1)if class==OwnerClass::M1&&(131072..131264).contains(&q)=>Ok(179218+q-131072),
            Relation::DaaLane(lane)if lane<2&&matches!(class,OwnerClass::Short(_)|OwnerClass::Mature(_))
                && q>>17==lane=>Self::f3(q),
            Relation::DaaLane(2)if q==262144&&matches!(class,
                OwnerClass::Initial|OwnerClass::Carry|OwnerClass::Singleton|OwnerClass::FixedV2)=>Ok(q),
            Relation::DaaLane(3)if !matches!(class,OwnerClass::Short(_)|OwnerClass::Mature(_))
                &&(393216..if class==OwnerClass::M1{466944}else{475136}).contains(&q)=>Ok(q),
            Relation::Scheduled(_)=>Ok(q),
            _=>Err("DAA class/lane source envelope".into()),
        }
    }
    fn place(self,class:OwnerClass,relation:Relation,owner:usize,mut term:Term)->Result<Term,String> {
        relation.slot(owner)?;
        if owner>=OWNERS||term.gate.left>=WIDTH*OWNERS||term.gate.right>=WIDTH*OWNERS {
            return Err("ROW placement owner/X extent".into());
        }
        let q=term.row.checked_sub(owner*ROWS).filter(|q|*q<ROWS).ok_or("ROW source owner mismatch")?;
        let mapped=self.local(class,relation,q)?;
        if mapped>=ROWS || !self.permits_reserved(relation,mapped) {
            return Err("ROW reserved future component".into());
        }
        term.row=owner*ROWS+mapped;Ok(term)
    }
    fn permits_reserved(self,relation:Relation,q:usize)->bool {
        if !(477074..507536).contains(&q) {return true;}
        matches!(relation,Relation::Map(context)if self.paired_map && context<2
            && (MAP_DESTINATION[context].0..MAP_DESTINATION[context].1).contains(&q))
    }
    fn placed(self,class:OwnerClass,relation:Relation,q:usize)->bool {
        match relation {
            Relation::Map(context)=>self.paired_map && (self.general_map||class==OwnerClass::Genesis) && context<2
                && (MAP_DESTINATION[context].0..MAP_DESTINATION[context].1).contains(&q),
            Relation::Header=>q<393216||(507536..520726).contains(&q),
            Relation::DaaLane(0)if class==OwnerClass::M1=>(166664..179218).contains(&q),
            Relation::DaaLane(1)if class==OwnerClass::M1=>(179218..179410).contains(&q),
            Relation::DaaLane(lane)if lane<2&&matches!(class,OwnerClass::Short(_)|OwnerClass::Mature(_))=>
                Self::inverse_f3(q).is_some_and(|original|original>>17==lane),
            Relation::DaaLane(lane)=>self.local(class,Relation::DaaLane(lane),q)==Ok(q),
            Relation::Scheduled(Writer::Max{context,..})if context<2=>
                ([356632,357305][context]..[357305,357978][context]).contains(&q)
                ||([475136,475585][context]..[475585,476034][context]).contains(&q),
            Relation::Scheduled(Writer::Cap{context,..})if context<2=>
                ([357978,360026][context]..[360026,362074][context]).contains(&q)
                ||([476034,476554][context]..[476554,477074][context]).contains(&q),
            _=>false,
        }
    }
    #[cfg(test)]
    pub(super) fn place_for_test(self,class:OwnerClass,relation:Relation,owner:usize,term:Term)
        ->Result<Term,String> {self.place(class,relation,owner,term)}
}

#[derive(Clone,Debug,PartialEq,Eq)]
struct Entry {relation:Relation,term:Term}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(super) enum Producer {Daa,Scheduled(Writer)}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(super) struct DeclaredXDomain {pub producer:Producer,pub start:usize,pub end:usize}
/// Complete immutable output of the three exact producers for one owner.
/// No constructor or append interface accepts caller-authored terms.
#[derive(Clone)]
pub(super) struct Batch {
    owner:usize,class:OwnerClass,layout:[u8;32],source:HeaderSourceBinding,terms:Vec<Entry>,
    expected:[usize;RELATIONS],relations:[Option<Relation>;RELATIONS],
}
/// Structural v2/v4 ROW candidate. There is deliberately no Batch conversion or
/// HEADER/DAA reader: Map-owned X values require a later paired source reader.
#[derive(Clone)]
pub(super) struct PairedMapBatch {
    base:Arc<Batch>,expected_base:Arc<Batch>,
    maps:[Vec<Term>;2],expected_maps:[Vec<Term>;2],map_relations:[Relation;2],
    source:HeaderSourceBinding,class:OwnerClass,layout:[u8;32],expected_layout:[u8;32],
}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(super) struct CoactiveMapRowEvidence {
    pub terms:usize,pub active_reads:usize,
    pub map_helper_reads:usize,pub work_d_reads:usize,
    pub map_source_cells:[usize;2],pub work_d_source_cells:[usize;2],
    pub physical_authors:[usize;6],pub residual_rows:usize,
}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
struct CoactiveMapReadCensus {
    active_reads:usize,
    map_helper_reads:usize,
    work_d_reads:usize,
    map_source_cells:[usize;2],
    work_d_source_cells:[usize;2],
    physical_authors:[usize;6],
}
impl PairedMapBatch {
    pub(super) fn terms(&self)->impl Iterator<Item=(Relation,&Term)> {
        self.base_terms().chain(self.maps.iter().enumerate().flat_map(move |(context,terms)|
            terms.iter().map(move|term|(self.map_relations[context],term))))
    }
    pub(super) fn base_terms(&self)->impl ExactSizeIterator<Item=(Relation,&Term)> {
        self.base.terms()
    }
    /// Replay every term ordinal, including constant-only terms, before
    /// reading the added Map occurrences. Repeated operands stay distinct.
    pub(super) fn active_operands(&self)->impl Iterator<Item=ActiveOperand>+'_ {
        self.terms().enumerate().flat_map(|(occurrence,(relation,term))|
            active_operands_for_term(occurrence,relation,term).into_iter().flatten())
    }
    /// C370 owns its own ordinary batch and read list. Counts alone cannot
    /// authorize adopting those reads into this paired batch.
    pub(super) fn checked_adopt_c370_base(&self,stage:&NativePartialXRowStage<'_>)
        ->Result<(),String> {
        self.checked_adopt_c370_parts(stage.batch(),&stage.reads,stage.row_owner())
    }
    fn checked_adopt_c370_parts(&self,actual:&Batch,reads:&[NativeRead],row_owner:usize)
        ->Result<(),String> {
        self.check_source_tuples()?;
        if self.layout!=Layout::paired_map_general().digest() {
            return Err("paired ROW C370 adoption requires v4 layout".into());
        }
        let expected=self.base.as_ref();
        if row_owner!=expected.owner || actual.owner!=expected.owner
            ||actual.class!=expected.class ||actual.layout!=expected.layout
            ||actual.source!=expected.source ||actual.expected!=expected.expected
            ||actual.relations!=expected.relations ||actual.terms!=expected.terms {
            return Err("paired ROW C370 complete ordinary batch mismatch".into());
        }
        let mut operands=actual.active_operands();
        for read in reads {
            if Some(read.operand())!=operands.next() {
                return Err("paired ROW C370 read occurrence mismatch".into());
            }
        }
        if operands.next().is_some() {
            return Err("paired ROW C370 missing read occurrence".into());
        }
        Ok(())
    }
    fn checked_coactive_map_values(&self,stage:&NativePartialXRowStage<'_>,
        census:&NativeOwnerAuthorCensus,view:&Eligible08MapSourceView<'_>)
        ->Result<CoactiveMapRowEvidence,String> {
        let (reads,values)=self.checked_coactive_map_read_values(stage,census,view)?;
        let (terms,residual_rows)=self.checked_residuals(values.into_iter())?;
        Ok(CoactiveMapRowEvidence{terms,active_reads:reads.active_reads,
            map_helper_reads:reads.map_helper_reads,work_d_reads:reads.work_d_reads,
            map_source_cells:reads.map_source_cells,work_d_source_cells:reads.work_d_source_cells,
            physical_authors:reads.physical_authors,residual_rows})
    }

    /// The checked C454 prefix values are shared with the fifteen-relation
    /// reader. This retains the exact legacy authority path while avoiding a
    /// second full ordinary/Map batch or another active-value vector.
    fn checked_coactive_map_read_values(&self,stage:&NativePartialXRowStage<'_>,
        census:&NativeOwnerAuthorCensus,view:&Eligible08MapSourceView<'_>)
        ->Result<(CoactiveMapReadCensus,Vec<bool>),String> {
        self.checked_adopt_c370_base(stage)?;
        if self.owner()!=CAP0_OWNER || self.class()!=OwnerClass::Carry
            || view.binding()!=&self.source {
            return Err("coactive Map ROW owner/class/retained source".into());
        }
        let physical_authors=stage.join_physical_census(&self.source,census)?;
        census.require_map_view(&self.source,stage.row,view)?;
        let layout=Layout::paired_map_general();
        for context in 0..2 {
            let source=view.checked_terms(&self.source,self.owner(),self.class(),context)?;
            if source.len()!=self.maps[context].len() {
                return Err("coactive Map ROW retained term count".into());
            }
            for (unplaced,placed) in source.iter().zip(&self.maps[context]) {
                if layout.place(self.class(),Relation::Map(context),self.owner(),unplaced.clone())?
                    !=*placed {
                    return Err("coactive Map ROW retained ordered source term".into());
                }
            }
        }
        let mut map_cells:[BTreeMap<usize,bool>;2]=std::array::from_fn(|_|BTreeMap::new());
        let mut map_source_cells=[0usize;2];
        for (context,wire,value) in view.map_cells() {
            if context>=2 || map_cells[context].insert(wire,value).is_some() {
                return Err("coactive Map ROW duplicate/out-of-context source cell".into());
            }
            let (_,physical)=census.checked_map_cell(&self.source,stage.row,view,context,wire)?;
            if physical!=value {return Err("coactive Map ROW source/physical cell value".into());}
            map_source_cells[context]+=1;
        }
        if map_source_cells!=[crate::bank53_map::MAP_LIVE;2] {
            return Err("coactive Map ROW full source-cell census".into());
        }
        let mut work_d:[BTreeMap<usize,bool>;2]=std::array::from_fn(|_|BTreeMap::new());
        let mut work_d_source_cells=[0usize;2];
        let work_base=self.owner().checked_mul(WIDTH)
            .and_then(|base|base.checked_add(crate::legacy_envelope_map::D_LOCAL))
            .ok_or("coactive Map ROW Work-D base overflow")?;
        for (context,wire,value) in view.local_imports() {
            if context>=2 || wire!=work_base+work_d_source_cells[context]
                || work_d[context].insert(wire,value).is_some() {
                return Err("coactive Map ROW ordered local Work-D import".into());
            }
            let (author,physical)=census.checked_cell(&self.source,stage.row,wire)?;
            if author!=NativePhysicalAuthor::Tree || physical!=value {
                return Err("coactive Map ROW Work-D Tree source/physical value".into());
            }
            work_d_source_cells[context]+=1;
        }
        if work_d_source_cells!=[224;2] {
            return Err("coactive Map ROW exact 448 local Work-D imports".into());
        }
        let base_terms=self.base.terms.len();let mut ordinary=stage.reads();
        let mut values=Vec::new();let mut map_helper_reads=0usize;let mut work_d_reads=0usize;
        for operand in self.active_operands() {
            let value=if operand.occurrence<base_terms {
                let read=*ordinary.next().ok_or("coactive Map ROW missing ordinary read")?;
                if read.operand()!=operand {
                    return Err("coactive Map ROW ordinary occurrence order".into());
                }
                read.qualified_value()?
            }else{
                let context=match operand.relation {
                    Relation::Map(context) if context<2=>context,
                    _=>return Err("coactive Map ROW appended relation".into()),
                };
                match (map_cells[context].get(&operand.wire),work_d[context].get(&operand.wire)) {
                    (Some(source),None)=>{
                        let (_,physical)=census.checked_map_cell(&self.source,stage.row,view,
                            context,operand.wire)?;
                        if physical!=*source {
                            return Err("coactive Map ROW Map helper source/packed read".into());
                        }
                        map_helper_reads+=1;physical
                    }
                    (None,Some(source))=>{
                        let (author,physical)=census.checked_cell(&self.source,stage.row,
                            operand.wire)?;
                        if author!=NativePhysicalAuthor::Tree || physical!=*source {
                            return Err("coactive Map ROW Work-D occurrence author/value".into());
                        }
                        work_d_reads+=1;physical
                    }
                    _=>return Err("coactive Map ROW active operand lacks unique retained source".into()),
                }
            };
            values.push(value);
        }
        if ordinary.next().is_some() {
            return Err("coactive Map ROW trailing ordinary read".into());
        }
        let active_reads=values.len();
        Ok((CoactiveMapReadCensus{active_reads,map_helper_reads,work_d_reads,
            map_source_cells,work_d_source_cells,physical_authors},values))
    }
    fn checked_residuals(&self,mut values:impl Iterator<Item=bool>)
        ->Result<(usize,usize),String> {
        let row_base=self.owner().checked_mul(ROWS).ok_or("coactive Map ROW row base")?;
        let mut residuals=vec![Fr::zero();ROWS];let mut terms=0usize;
        for (occurrence,(relation,term)) in self.terms().enumerate() {
            let q=term.row.checked_sub(row_base).filter(|q|*q<ROWS)
                .ok_or("coactive Map ROW term outside owner")?;
            let [left,right]=active_operands_for_term(occurrence,relation,term);
            let left=if left.is_some(){Fr::from(values.next()
                .ok_or("coactive Map ROW missing left value")? as u64)}else{Fr::zero()};
            let right=if right.is_some(){Fr::from(values.next()
                .ok_or("coactive Map ROW missing right value")? as u64)}else{Fr::zero()};
            let gate=&term.gate;
            residuals[q]+=gate.c0+gate.c1*left+gate.c2*right+gate.c3*left*right;
            terms+=1;
        }
        if values.next().is_some() {
            return Err("coactive Map ROW trailing active value".into());
        }
        if let Some((q,_))=residuals.iter().enumerate().find(|(_,value)|!value.is_zero()) {
            return Err(format!("coactive Map ROW nonzero residual q={q}"));
        }
        Ok((terms,ROWS))
    }
    pub(super) fn map_terms(&self,context:usize)->Result<&[Term],String> {
        self.maps.get(context).map(Vec::as_slice).ok_or_else(||"paired ROW Map context".into())
    }
    pub(super) fn counts(&self)->[usize;RELATIONS] {
        let mut counts=self.base.expected;
        for context in 0..2 {counts[9+context]=self.expected_maps[context].len();}counts
    }
    fn relations(&self)->[Option<Relation>;RELATIONS] {
        let mut relations=self.base.relations;
        for context in 0..2 {relations[9+context]=Some(Relation::Map(context));}relations
    }
    pub(super) fn owner(&self)->usize {self.base.owner}
    pub(super) fn class(&self)->OwnerClass {self.class}
    pub(super) fn source_binding(&self)->&HeaderSourceBinding {&self.source}
    pub(super) fn layout_digest(&self)->[u8;32] {self.layout}
    fn check_source_tuples(&self)->Result<(),String> {
        let genesis_layout=self.layout==Layout::paired_map().digest();
        if self.layout!=self.expected_layout
            || (genesis_layout&&(self.base.owner!=0||self.class!=OwnerClass::Genesis))
            || (!genesis_layout&&self.layout!=Layout::paired_map_general().digest())
            || self.base.layout!=Layout::fixed().digest()
            || self.class!=self.base.class || self.source!=self.base.source
            || self.base.owner!=self.expected_base.owner || self.base.class!=self.expected_base.class
            || self.base.layout!=self.expected_base.layout || self.base.source!=self.expected_base.source
            || self.base.expected!=self.expected_base.expected
            || self.base.relations!=self.expected_base.relations
            || self.base.terms!=self.expected_base.terms {
            return Err("paired ROW ordinary source tuples/binding changed".into());
        }
        for context in 0..2 {
            if self.map_relations[context]!=Relation::Map(context)
                || self.maps[context]!=self.expected_maps[context] {
                return Err("paired ROW ordered Map context/source tuples changed".into());
            }
        }
        Ok(())
    }
    #[cfg(test)]
    pub(super) fn map_terms_mut_for_test(&mut self,context:usize)->&mut Vec<Term> {
        &mut self.maps[context]
    }
    #[cfg(test)]
    pub(super) fn map_relation_mut_for_test(&mut self,context:usize)->&mut Relation {
        &mut self.map_relations[context]
    }
    #[cfg(test)]
    pub(super) fn layout_mut_for_test(&mut self)->&mut [u8;32] {&mut self.layout}
    #[cfg(test)]
    pub(super) fn source_binding_mut_for_test(&mut self)->&mut HeaderSourceBinding {&mut self.source}
    #[cfg(test)]
    pub(super) fn class_mut_for_test(&mut self)->&mut OwnerClass {&mut self.class}
    #[cfg(test)]
    pub(super) fn base_term_mut_for_test(&mut self,index:usize)->(&mut Relation,&mut Term) {
        let entry=&mut Arc::make_mut(&mut self.base).terms[index];
        (&mut entry.relation,&mut entry.term)
    }
}
/// A selected early-Carry ROW source, limited to Bank53 reads authenticated
/// by the same producer-owned packed row. All other active operands remain
/// open. This is neither a full ROW value assignment nor an X seal.
pub(super) struct C503EarlyCarryMapHeaderRow<'m> {
    receipt: NativeMixedMapHeaderRow<'m>,
    batch: PairedMapBatch,
    bank53_reads: Vec<C503Bank53Read>,
    open_reads: usize,
}

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(super) enum C503Bank53Author { Map(usize), HeaderZero }

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(super) struct C503Bank53Read {
    pub operand: ActiveOperand,
    pub author: C503Bank53Author,
    pub value: bool,
}

impl<'m> C503EarlyCarryMapHeaderRow<'m> {
    fn require_source_policy(plan: &RowPlan<'_, '_>, owner: usize) -> Result<(), String> {
        let class = plan.roster.owner_class(owner as u64)?;
        crate::bank53_required_writer::require_ordinary_unscored_carry_map_header(
            owner, class, plan.scheduled,
        )
    }

    /// No caller-supplied batch or second Map pair can enter this join.
    pub(super) fn from_producer(
        plan: &RowPlan<'_, '_>, receipt: NativeMixedMapHeaderRow<'m>,
    ) -> Result<Self, String> {
        let owner = receipt.owner();
        Self::require_source_policy(plan, owner)?;
        let binding = receipt.binding().clone();
        let batch = plan.stage_owner_with_map_pair_general(owner, receipt.map_lease())?;
        if batch.owner() != owner || batch.class() != OwnerClass::Carry
            || batch.source_binding() != &binding
            || batch.layout_digest() != Layout::paired_map_general().digest()
        {
            return Err("C503 ROW join same-owner source/layout".into());
        }
        let (bank53_reads, open_reads) = Self::checked_reads(&receipt, &batch)?;
        let joined = Self { receipt, batch, bank53_reads, open_reads };
        joined.validate()?;
        Ok(joined)
    }

    fn checked_reads(
        receipt: &NativeMixedMapHeaderRow<'_>, batch: &PairedMapBatch,
    ) -> Result<(Vec<C503Bank53Read>, usize), String> {
        let owner = receipt.owner();
        let base = owner.checked_mul(WIDTH).ok_or("C503 ROW owner X base overflow")?;
        let mut reads = Vec::new();
        let mut open = 0usize;
        let mut map = [0usize; 2];
        for operand in batch.active_operands() {
            let Some(local) = operand.wire.checked_sub(base).filter(|local| *local < WIDTH)
                else { open += 1; continue; };
            if !(671_744..671_744 + 2 * 8_192).contains(&local) {
                open += 1;
                continue;
            }
            let context = (local - 671_744) / 8_192;
            let offset = (local - 671_744) % 8_192;
            let (author, value) = match crate::bank53_required_writer::required_bank53_writer(
                owner, context, offset).map_err(|error| error.to_string())? {
                crate::bank53_required_writer::RequiredWriter::Map { context: expected }
                    if expected == context => {
                        map[context] += 1;
                        (C503Bank53Author::Map(context),
                            receipt.read_map(receipt.binding(), context, offset)?)
                    }
                crate::bank53_required_writer::RequiredWriter::HeaderZero =>
                    (C503Bank53Author::HeaderZero,
                        receipt.read_header_zero(receipt.binding(), context, offset)?),
                _ => return Err(format!("C503 ROW unsupported Bank53 writer wire{}",
                    operand.wire)),
            };
            reads.push(C503Bank53Read { operand, author, value });
        }
        if map.iter().any(|count| *count < 5_757) || reads.is_empty() || open == 0 {
            return Err("C503 ROW Bank53/open active-read census".into());
        }
        Ok((reads, open))
    }

    pub(super) fn validate(&self) -> Result<(), String> {
        self.batch.check_source_tuples()?;
        if self.batch.owner() != self.receipt.owner()
            || self.batch.source_binding() != self.receipt.binding() {
            return Err("C503 ROW receipt/batch owner or parent drift".into());
        }
        let (expected, open) = Self::checked_reads(&self.receipt, &self.batch)?;
        if expected != self.bank53_reads || open != self.open_reads {
            return Err("C503 ROW missing/reordered/changed active read".into());
        }
        Ok(())
    }

    pub(super) fn bank53_reads(&self) -> &[C503Bank53Read] { &self.bank53_reads }
    pub(super) fn open_read_count(&self) -> usize { self.open_reads }
    pub(super) fn batch(&self) -> &PairedMapBatch { &self.batch }

    #[cfg(test)]
    pub(super) fn batch_mut_for_test(&mut self) -> &mut PairedMapBatch { &mut self.batch }
    #[cfg(test)]
    pub(super) fn bank53_reads_mut_for_test(&mut self) -> &mut Vec<C503Bank53Read> {
        &mut self.bank53_reads
    }
    #[cfg(test)]
    pub(super) fn remove_first_bank53_read_for_test(&mut self) {
        self.bank53_reads.remove(0);
    }

    #[cfg(test)]
    pub(super) fn insert_closed_non_bank53_read_for_test(
        &mut self, operand: ActiveOperand,
    ) -> Result<(), String> {
        let base = self.receipt.owner().checked_mul(WIDTH)
            .ok_or("C503 test owner X base overflow")?;
        let local = operand.wire.checked_sub(base)
            .ok_or("C503 test operand is not owner-local")?;
        if local < WIDTH && (671_744..671_744 + 2 * 8_192).contains(&local) {
            return Err("C503 test operand is Bank53, expected otherwise-open operand".into());
        }
        let active: Vec<_> = self.batch.active_operands().collect();
        let position = active.iter().position(|candidate| *candidate == operand)
            .ok_or("C503 test operand is not an active occurrence")?;
        let insertion = active[..position].iter()
            .filter(|candidate| {
                candidate.wire.checked_sub(base)
                    .is_some_and(|local| (671_744..671_744 + 2 * 8_192).contains(&local))
            })
            .count();
        self.bank53_reads.insert(insertion, C503Bank53Read {
            operand, author: C503Bank53Author::HeaderZero, value: false,
        });
        Ok(())
    }

    #[cfg(test)]
    pub(super) fn remove_closed_non_bank53_read_for_test(
        &mut self, operand: ActiveOperand,
    ) -> Result<(), String> {
        let base = self.receipt.owner().checked_mul(WIDTH)
            .ok_or("C503 test owner X base overflow")?;
        let local = operand.wire.checked_sub(base)
            .ok_or("C503 test operand is not owner-local")?;
        if local < WIDTH && (671_744..671_744 + 2 * 8_192).contains(&local) {
            return Err("C503 test operand is Bank53, expected otherwise-open operand".into());
        }
        if !self.batch.active_operands().any(|candidate| candidate == operand) {
            return Err("C503 test operand is not an active occurrence".into());
        }
        let matching: Vec<_> = self.bank53_reads.iter().enumerate()
            .filter(|(_, read)| read.operand == operand).map(|(index, read)| (index, *read))
            .collect();
        if matching.len() != 1
            || matching[0].1.author != C503Bank53Author::HeaderZero
            || matching[0].1.value
        {
            return Err("C503 test forged non-Bank53 closed read is absent or ambiguous".into());
        }
        self.bank53_reads.remove(matching[0].0);
        Ok(())
    }
}

/// Initial owner 1 can read only the Bank53 operands backed by its own
/// producer-captured Map/HEADER-zero row. The other operands stay open.
/// This is a partial ROW source, not a complete X assignment.
pub(super) struct C506InitialMapHeaderRow<'m> {
    receipt: NativeMixedMapHeaderRow<'m>,
    batch: PairedMapBatch,
    bank53_reads: Vec<C503Bank53Read>,
    open_reads: usize,
}

impl<'m> C506InitialMapHeaderRow<'m> {
    /// No caller-supplied Map pair, ROW batch or read vector enters this join.
    pub(super) fn from_producer(
        plan: &RowPlan<'_, '_>, receipt: NativeMixedMapHeaderRow<'m>,
    ) -> Result<Self, String> {
        let owner = receipt.owner();
        if owner != 1 || receipt.row().owner() != 1
            || receipt.row().class() != OwnerClass::Initial {
            return Err("C506 ROW join requires Initial owner 1".into());
        }
        let binding = receipt.binding().clone();
        receipt.row().require_header_source_binding(
            &binding, owner, OwnerClass::Initial,
        )?;
        let batch = plan.stage_owner_with_map_pair_general(owner, receipt.map_lease())?;
        if batch.owner() != owner || batch.class() != OwnerClass::Initial
            || batch.source_binding() != &binding
            || batch.layout_digest() != Layout::paired_map_general().digest() {
            return Err("C506 ROW join same-owner source/class/layout".into());
        }
        let (bank53_reads, open_reads) =
            C503EarlyCarryMapHeaderRow::checked_reads(&receipt, &batch)?;
        let joined = Self { receipt, batch, bank53_reads, open_reads };
        joined.validate()?;
        Ok(joined)
    }

    pub(super) fn validate(&self) -> Result<(), String> {
        self.batch.check_source_tuples()?;
        if self.receipt.owner() != 1 || self.receipt.row().owner() != 1
            || self.receipt.row().class() != OwnerClass::Initial
            || self.batch.owner() != 1 || self.batch.class() != OwnerClass::Initial
            || self.batch.source_binding() != self.receipt.binding()
            || self.batch.layout_digest() != Layout::paired_map_general().digest() {
            return Err("C506 ROW receipt/batch owner, class or parent drift".into());
        }
        self.receipt.row().require_header_source_binding(
            self.receipt.binding(), 1, OwnerClass::Initial,
        )?;
        let (expected, open) =
            C503EarlyCarryMapHeaderRow::checked_reads(&self.receipt, &self.batch)?;
        if expected != self.bank53_reads || open != self.open_reads {
            return Err("C506 ROW missing/reordered/changed active read".into());
        }
        Ok(())
    }

    pub(super) fn bank53_reads(&self) -> &[C503Bank53Read] { &self.bank53_reads }
    pub(super) fn open_read_count(&self) -> usize { self.open_reads }
    pub(super) fn batch(&self) -> &PairedMapBatch { &self.batch }

    #[cfg(test)]
    pub(super) fn batch_mut_for_test(&mut self) -> &mut PairedMapBatch {
        &mut self.batch
    }
    #[cfg(test)]
    pub(super) fn bank53_reads_mut_for_test(&mut self) -> &mut Vec<C503Bank53Read> {
        &mut self.bank53_reads
    }
}
const ANCHOR_OWNER:usize=417_790;
pub(super) const ANCHOR_RELATIONS:usize=15;
// Occurrence order is Map0, Map1, Score0, Score1, Slack0, Slack1; physical
// geometry is context-interleaved and must not redefine that traversal.
const ANCHOR_SOURCE:[(usize,usize);6]=[
    (409600,419947),(442368,452715),(487421,491918),
    (502652,507149),(438496,438883),(471264,471651),
];
const ANCHOR_DESTINATION:[(usize,usize);6]=[
    (477074,487421),(492305,502652),(487421,491918),
    (502652,507149),(491918,492305),(507149,507536),
];

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(super) enum AnchorRelation {Ordinary(Relation),Map(usize),ScoreAnchor(usize),Slack(usize)}
impl AnchorRelation {
    fn slot(self,owner:usize)->Result<usize,String> {
        match self {
            Self::Ordinary(relation)=>relation.slot(owner).and_then(|slot|
                if slot<9 {Ok(slot)}else{Err("v3 ordinary relation identity".into())}),
            Self::Map(context)if context<2=>Ok(9+context),
            Self::ScoreAnchor(context)if context<2=>Ok(11+context),
            Self::Slack(context)if context<2=>Ok(13+context),
            _=>Err("v3 anchor relation identity".into()),
        }
    }
    fn bank(index:usize)->Self {
        match index {0..=1=>Self::Map(index),2..=3=>Self::ScoreAnchor(index-2),
            4..=5=>Self::Slack(index-4),_=>unreachable!("six checked lists")}
    }
}

/// Opt-in identity. Neither v1/v2 descriptor nor the shared RELATIONS changes.
pub(super) struct AnchorLayout;
impl AnchorLayout {
    pub(super) fn descriptor()->Vec<u8> {
        let mut out=b"c448-row19-eligible08-first-anchor-v3\0".to_vec();
        out.extend_from_slice(&Layout::fixed().digest());
        let cut=crate::bank53_map::CutDescriptor::eligible08().canonical_identity();
        out.extend_from_slice(&(cut.len()as u64).to_le_bytes());out.extend_from_slice(&cut);
        for value in [ANCHOR_OWNER,ANCHOR_RELATIONS] {
            out.extend_from_slice(&(value as u64).to_le_bytes());
        }
        for slot in 0..ANCHOR_RELATIONS {out.extend_from_slice(&(slot as u64).to_le_bytes());}
        for index in 0..6 {
            for value in [index+9,ANCHOR_SOURCE[index].0,ANCHOR_SOURCE[index].1,
                ANCHOR_DESTINATION[index].0,ANCHOR_DESTINATION[index].1] {
                out.extend_from_slice(&(value as u64).to_le_bytes());
            }
        }
        out
    }
    pub(super) fn digest()->[u8;32] {Blake2b::<U32>::digest(Self::descriptor()).into()}
    fn place(index:usize,mut term:Term)->Result<Term,String> {
        let q=term.row.checked_sub(ANCHOR_OWNER*ROWS).filter(|q|
            (ANCHOR_SOURCE[index].0..ANCHOR_SOURCE[index].1).contains(q))
            .ok_or("v3 checked source ROW envelope/owner")?;
        if term.gate.left>=WIDTH*OWNERS||term.gate.right>=WIDTH*OWNERS {
            return Err("v3 checked source X extent".into());
        }
        term.row=ANCHOR_OWNER*ROWS+ANCHOR_DESTINATION[index].0+q-ANCHOR_SOURCE[index].0;
        Ok(term)
    }
    fn placed(relation:AnchorRelation,q:usize)->bool {
        match relation {
            AnchorRelation::Ordinary(r)=>Layout::fixed().placed(OwnerClass::Carry,r,q)
                && Layout::fixed().permits_reserved(r,q),
            _=>relation.slot(ANCHOR_OWNER).ok().filter(|slot|*slot>=9)
                .is_some_and(|slot|(ANCHOR_DESTINATION[slot-9].0..ANCHOR_DESTINATION[slot-9].1).contains(&q)),
        }
    }
}

/// C455 adds a separately versioned fifteen-relation identity. The legacy
/// `Relation`, `RELATIONS`, and v1-v4 layouts remain unchanged.
pub(super) const COMPLETE_RELATIONS:usize=15;
const COMPLETE_OWNER:usize=CAP0_OWNER;
const COMPLETE_SOURCE_INTERVALS:[(usize,usize);6]=[
    (409600,419947),(442368,452715),(487421,491918),
    (502652,507149),(438496,438883),(471264,471651),
];
const COMPLETE_DESTINATION_INTERVALS:[(usize,usize);6]=[
    (477074,487421),(492305,502652),(487421,491918),
    (502652,507149),(491918,492305),(507149,507536),
];

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(super) enum CompleteRelation {
    Ordinary(Relation),
    Map(usize),
    Score(usize),
    Slack(usize),
}
impl CompleteRelation {
    fn from_paired(relation:Relation)->Self {
        match relation {Relation::Map(context)=>Self::Map(context),other=>Self::Ordinary(other)}
    }
    fn slot(self,owner:usize)->Result<usize,String> {
        match self {
            Self::Ordinary(relation)=>relation.slot(owner).and_then(|slot|
                if slot<9 {Ok(slot)}else{Err("v5 ordinary relation identity".into())}),
            Self::Map(context)if context<2=>Ok(9+context),
            Self::Score(context)if context<2=>Ok(11+context),
            Self::Slack(context)if context<2=>Ok(13+context),
            _=>Err("v5 modern relation identity".into()),
        }
    }
    fn legacy_relation(self)->Option<Relation> {
        match self {
            Self::Ordinary(relation)=>Some(relation),
            Self::Map(context)=>Some(Relation::Map(context)),
            Self::Score(_)|Self::Slack(_)=>None,
        }
    }
}

/// Versioned C455 placement descriptor. Only ROW coordinates move; X wires
/// remain the exact source wires. Its identity includes the predecessor v4,
/// selected owner/class, Eligible08 cut, all fifteen slots, and six intervals.
pub(super) struct CompleteLayout;
impl CompleteLayout {
    fn descriptor_parts(owner:usize,class:&str,predecessor:[u8;32],cut:&[u8],
        slots:&[usize;COMPLETE_RELATIONS],source:&[(usize,usize);6],
        destination:&[(usize,usize);6])->Vec<u8> {
        let mut out=b"c455-row19-selected-modern-score-slack-v5\0".to_vec();
        out.extend_from_slice(&predecessor);
        out.extend_from_slice(&(cut.len() as u64).to_le_bytes());
        out.extend_from_slice(cut);
        out.extend_from_slice(&(owner as u64).to_le_bytes());
        out.extend_from_slice(&(class.len() as u64).to_le_bytes());
        out.extend_from_slice(class.as_bytes());
        out.extend_from_slice(&(COMPLETE_RELATIONS as u64).to_le_bytes());
        for slot in slots {out.extend_from_slice(&(*slot as u64).to_le_bytes());}
        for index in 0..6 {
            out.extend_from_slice(&((9+index) as u64).to_le_bytes());
            for value in [source[index].0,source[index].1,
                destination[index].0,destination[index].1] {
                out.extend_from_slice(&(value as u64).to_le_bytes());
            }
        }
        out
    }
    pub(super) fn descriptor()->Vec<u8> {
        let cut=crate::bank53_map::CutDescriptor::eligible08().canonical_identity();
        let slots=std::array::from_fn(|slot|slot);
        Self::descriptor_parts(COMPLETE_OWNER,"Carry",Layout::paired_map_general().digest(),
            &cut,&slots,&COMPLETE_SOURCE_INTERVALS,&COMPLETE_DESTINATION_INTERVALS)
    }
    pub(super) fn digest()->[u8;32] {Blake2b::<U32>::digest(Self::descriptor()).into()}
    fn place(index:usize,mut term:Term)->Result<Term,String> {
        let (start,end)=*COMPLETE_SOURCE_INTERVALS.get(index)
            .ok_or("v5 modern source interval index")?;
        let q=term.row.checked_sub(COMPLETE_OWNER*ROWS)
            .filter(|q|(start..end).contains(q)).ok_or("v5 checked source ROW interval/owner")?;
        if term.gate.left>=WIDTH*OWNERS || term.gate.right>=WIDTH*OWNERS {
            return Err("v5 checked source X extent".into());
        }
        let (destination_start,destination_end)=COMPLETE_DESTINATION_INTERVALS[index];
        let relative=q.checked_sub(start).ok_or("v5 source ROW interval underflow")?;
        if let Some(placed)=destination_start.checked_add(relative) {
            if placed>=destination_end {return Err("v5 destination ROW interval overflow".into());}
            term.row=COMPLETE_OWNER*ROWS+placed;
        } else {return Err("v5 destination ROW interval overflow".into());}
        Ok(term)
    }
    fn placed(class:OwnerClass,relation:CompleteRelation,q:usize)->bool {
        match relation {
            CompleteRelation::Ordinary(ordinary)=>{
                let predecessor=Layout::paired_map_general();
                predecessor.placed(class,ordinary,q)&&predecessor.permits_reserved(ordinary,q)
            }
            CompleteRelation::Map(context)if context<2=>{
                let (start,end)=COMPLETE_DESTINATION_INTERVALS[context];(start..end).contains(&q)
            }
            CompleteRelation::Score(context)if context<2=>{
                let (start,end)=COMPLETE_DESTINATION_INTERVALS[2+context];(start..end).contains(&q)
            }
            CompleteRelation::Slack(context)if context<2=>{
                let (start,end)=COMPLETE_DESTINATION_INTERVALS[4+context];(start..end).contains(&q)
            }
            _=>false,
        }
    }
}

/// A zero-copy wrapper over the C454 ordinary+Map prefix plus four checked
/// modern families. Only the 774 relocated Slack terms are owned here.
pub(super) struct CompleteBatch<'a,'s> {
    base:&'a PairedMapBatch,
    view:&'a crate::packed_owner_assembly::Eligible08CompleteRowSourceView<'s>,
    score_terms:[&'a [Term];2],
    slack_terms:[Vec<Term>;2],
    expected:[usize;COMPLETE_RELATIONS],
    relations:[Option<CompleteRelation>;COMPLETE_RELATIONS],
}
impl<'a,'s> CompleteBatch<'a,'s> {
    pub(super) fn checked_from_retained_map(base:&'a PairedMapBatch,
        view:&'a crate::packed_owner_assembly::Eligible08CompleteRowSourceView<'s>)
        ->Result<Self,String> {
        if base.owner()!=COMPLETE_OWNER||base.class()!=OwnerClass::Carry
            ||base.layout_digest()!=Layout::paired_map_general().digest()
            ||view.binding()!=base.source_binding() {
            return Err("v5 retained owner/class/v4 layout/source binding".into());
        }
        let score_terms=[view.score_terms(0)?,view.score_terms(1)?];
        let slack0=view.slack_terms(0)?.iter().cloned()
            .map(|term|CompleteLayout::place(4,term)).collect::<Result<Vec<_>,_>>()?;
        let slack1=view.slack_terms(1)?.iter().cloned()
            .map(|term|CompleteLayout::place(5,term)).collect::<Result<Vec<_>,_>>()?;
        let base_terms=base.terms().count();
        let combined=base_terms.checked_add(score_terms[0].len())
            .and_then(|count|count.checked_add(score_terms[1].len()))
            .and_then(|count|count.checked_add(slack0.len()))
            .and_then(|count|count.checked_add(slack1.len()))
            .filter(|count|*count<=TERM_LIMIT).ok_or("v5 combined per-owner term bound")?;
        if combined<base_terms {return Err("v5 combined term count overflow".into());}
        let mut expected=[0;COMPLETE_RELATIONS];
        expected[..RELATIONS].copy_from_slice(&base.counts());
        expected[11]=score_terms[0].len();expected[12]=score_terms[1].len();
        expected[13]=slack0.len();expected[14]=slack1.len();
        let base_relations=base.relations();
        let mut relations=[None;COMPLETE_RELATIONS];
        for (slot,relation) in base_relations.into_iter().enumerate() {
            relations[slot]=relation.map(CompleteRelation::from_paired);
        }
        relations[11]=Some(CompleteRelation::Score(0));
        relations[12]=Some(CompleteRelation::Score(1));
        relations[13]=Some(CompleteRelation::Slack(0));
        relations[14]=Some(CompleteRelation::Slack(1));
        let batch=Self{base,view,score_terms,slack_terms:[slack0,slack1],expected,relations};
        batch.check_source_tuples()?;
        Ok(batch)
    }
    pub(super) fn terms(&self)->impl Iterator<Item=(CompleteRelation,&Term)>+'_ {
        self.base.terms().map(|(relation,term)|(CompleteRelation::from_paired(relation),term))
            .chain(self.score_terms[0].iter().map(|term|(CompleteRelation::Score(0),term)))
            .chain(self.score_terms[1].iter().map(|term|(CompleteRelation::Score(1),term)))
            .chain(self.slack_terms[0].iter().map(|term|(CompleteRelation::Slack(0),term)))
            .chain(self.slack_terms[1].iter().map(|term|(CompleteRelation::Slack(1),term)))
    }
    pub(super) fn active_operands(&self)->CompleteActiveOperandIter<impl Iterator<Item=(CompleteRelation,&Term)>+'_> {
        CompleteActiveOperandIter{terms:self.terms().enumerate(),pending_right:None}
    }
    pub(super) fn owner(&self)->usize {self.base.owner()}
    pub(super) fn class(&self)->OwnerClass {self.base.class()}
    pub(super) fn source_binding(&self)->&HeaderSourceBinding {self.base.source_binding()}
    pub(super) fn layout_digest(&self)->[u8;32] {CompleteLayout::digest()}
    pub(super) fn counts(&self)->[usize;COMPLETE_RELATIONS] {self.expected}
    fn check_source_tuples(&self)->Result<(),String> {
        if self.owner()!=COMPLETE_OWNER||self.class()!=OwnerClass::Carry
            ||self.base.layout_digest()!=Layout::paired_map_general().digest()
            ||self.view.binding()!=self.source_binding() {
            return Err("v5 exact retained source view/base identity".into());
        }
        self.base.check_source_tuples()?;
        let mut expected=[0;COMPLETE_RELATIONS];
        expected[..RELATIONS].copy_from_slice(&self.base.counts());
        let mut relations=[None;COMPLETE_RELATIONS];
        for (slot,relation) in self.base.relations().into_iter().enumerate() {
            relations[slot]=relation.map(CompleteRelation::from_paired);
        }
        for context in 0..2 {
            let score=self.view.score_terms(context)?;
            if score.len()!=self.score_terms[context].len()
                ||!std::ptr::eq(score.as_ptr(),self.score_terms[context].as_ptr()) {
                return Err("v5 retained Score slice identity/count".into());
            }
            for term in score {
                if CompleteLayout::place(2+context,term.clone())?!=*term {
                    return Err("v5 ordered modern Score source tuple".into());
                }
            }
            let slack=self.view.slack_terms(context)?;
            if slack.len()!=self.slack_terms[context].len() {
                return Err("v5 retained Slack source tuple count".into());
            }
            for (staged,source) in self.slack_terms[context].iter().zip(slack) {
                if staged!=&CompleteLayout::place(4+context,source.clone())? {
                    return Err("v5 ordered modern Slack source tuple".into());
                }
            }
            expected[11+context]=score.len();expected[13+context]=slack.len();
            relations[11+context]=Some(CompleteRelation::Score(context));
            relations[13+context]=Some(CompleteRelation::Slack(context));
        }
        if expected!=self.expected||relations!=self.relations {
            return Err("v5 fifteen-slot source counts/relation identity".into());
        }
        Ok(())
    }
}

/// Regular owner 845887 joins the checked Score/Slack producer directly. This
/// is a separate structural layout identity from selected-owner C455; every
/// X operand remains open because this batch has no same-row physical receipt.
const C509_OWNER:usize=845_887;
const C509_RELATIONS:usize=15;
pub(super) const C509_ROW_STRIDE:usize=ROWS;
const C513_TERMS:usize=520_693;
const C513_ACTIVE_READS:usize=730_942;
const C509_SOURCE_INTERVALS:[(usize,usize);6]=[
    (409600,419947),(442368,452715),(487421,491918),
    (502652,507149),(438496,438883),(471264,471651),
];
const C509_DESTINATION_INTERVALS:[(usize,usize);6]=[
    (477074,487421),(492305,502652),(487421,491918),
    (502652,507149),(491918,492305),(507149,507536),
];

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(super) enum C509Relation {
    Ordinary(Relation),Map(usize),Score(usize),Slack(usize),
}
impl C509Relation {
    fn slot(self,owner:usize)->Result<usize,String> {
        match self {
            Self::Ordinary(relation)=>relation.slot(owner).and_then(|slot|
                if slot<9 {Ok(slot)} else {Err("C509 ordinary relation slot".into())}),
            Self::Map(context)if context<2=>Ok(9+context),
            Self::Score(context)if context<2=>Ok(11+context),
            Self::Slack(context)if context<2=>Ok(13+context),
            _=>Err("C509 context/relation slot".into()),
        }
    }
}

#[derive(Clone,Debug,PartialEq,Eq)]
struct C509Entry {relation:C509Relation,term:Term}

struct C509RegularLayout;
impl C509RegularLayout {
    fn descriptor()->Vec<u8> {
        let cut=crate::bank53_map::CutDescriptor::eligible08().canonical_identity();
        let mut out=b"c509-row19-regular-845887-score-slack-v1\0".to_vec();
        out.extend_from_slice(&Layout::paired_map_general().digest());
        out.extend_from_slice(&(cut.len() as u64).to_le_bytes());out.extend_from_slice(&cut);
        out.extend_from_slice(&(C509_OWNER as u64).to_le_bytes());
        out.extend_from_slice(&(C509_RELATIONS as u64).to_le_bytes());
        for slot in 0..C509_RELATIONS {out.extend_from_slice(&(slot as u64).to_le_bytes());}
        for index in 0..6 {
            out.extend_from_slice(&((9+index) as u64).to_le_bytes());
            for value in [C509_SOURCE_INTERVALS[index].0,C509_SOURCE_INTERVALS[index].1,
                C509_DESTINATION_INTERVALS[index].0,C509_DESTINATION_INTERVALS[index].1] {
                out.extend_from_slice(&(value as u64).to_le_bytes());
            }
        }
        out
    }
    fn digest()->[u8;32] {Blake2b::<U32>::digest(Self::descriptor()).into()}
    fn place(index:usize,mut term:Term)->Result<Term,String> {
        let (start,end)=*C509_SOURCE_INTERVALS.get(index)
            .ok_or("C509 source interval index")?;
        let q=term.row.checked_sub(C509_OWNER*ROWS)
            .filter(|q|(start..end).contains(q)).ok_or("C509 source ROW interval/owner")?;
        if term.gate.left>=WIDTH*OWNERS||term.gate.right>=WIDTH*OWNERS {
            return Err("C509 source X extent".into());
        }
        let (destination_start,destination_end)=C509_DESTINATION_INTERVALS[index];
        let placed=destination_start.checked_add(q-start)
            .filter(|placed|*placed<destination_end).ok_or("C509 destination interval")?;
        term.row=C509_OWNER*ROWS+placed;Ok(term)
    }
    fn require_destination(index:usize,term:&Term)->Result<(),String> {
        let (start,end)=*C509_DESTINATION_INTERVALS.get(index)
            .ok_or("C509 destination interval index")?;
        let q=term.row.checked_sub(C509_OWNER*ROWS)
            .filter(|q|(start..end).contains(q)).ok_or("C509 placed family destination interval")?;
        if q>=ROWS||term.gate.left>=WIDTH*OWNERS||term.gate.right>=WIDTH*OWNERS {
            return Err("C509 placed family ROW/X extent".into());
        }
        Ok(())
    }
    fn intervals_disjoint(intervals:&[(usize,usize);6])->bool {
        (0..intervals.len()).all(|left|(left+1..intervals.len()).all(|right|
            intervals[left].1<=intervals[right].0||intervals[right].1<=intervals[left].0))
    }
}

/// Fifteen-slot structural consumer borrowing one exact regular source view.
/// Terms are copied only after being read from that view and are replayed
/// against it on every public observation; no second Map lease is accepted.
pub(super) struct C509RegularBatch<'a,'s> {
    source:&'a crate::packed_owner_assembly::C509RegularRowSourceView<'s>,
    binding:HeaderSourceBinding,
    terms:Vec<C509Entry>,
    counts:[usize;C509_RELATIONS],
}

/// Selected-owner arithmetic output. The values' physical authority belongs
/// to the caller's separate source-token join; this table grants none.
pub(super) struct C513SelectedNumericRow {
    binding:HeaderSourceBinding,
    layout:[u8;32],
    terms:usize,
    active_reads:usize,
    counts:[usize;C509_RELATIONS],
    residuals:Vec<Fr>,
}
impl C513SelectedNumericRow {
    pub(super) fn binding(&self)->&HeaderSourceBinding {&self.binding}
    pub(super) fn layout_digest(&self)->[u8;32] {self.layout}
    pub(super) fn terms(&self)->usize {self.terms}
    pub(super) fn active_reads(&self)->usize {self.active_reads}
    pub(super) fn counts(&self)->[usize;C509_RELATIONS] {self.counts}
    pub(super) fn residuals(&self)->&[Fr] {&self.residuals}
}

impl<'a,'s> C509RegularBatch<'a,'s> {
    pub(super) fn checked_from_source(
        source:&'a crate::packed_owner_assembly::C509RegularRowSourceView<'s>,
        expected:&HeaderSourceBinding,
    )->Result<Self,String> {
        if !c509_source_identity(source.owner()?,source.binding()?,expected)
            ||!C509RegularLayout::intervals_disjoint(&C509_SOURCE_INTERVALS)
            ||!C509RegularLayout::intervals_disjoint(&C509_DESTINATION_INTERVALS) {
            return Err("C509 regular source owner/binding/layout intervals".into());
        }
        // Force the view to revalidate and retain its typed candidate/read
        // custody. These are not promoted to physical values by this batch.
        let _candidate_cells=source.candidate_cells()?;
        let _selected_open_reads=source.selected_open_reads()?;
        let _map_bindings=source.map_bindings()?;
        let (terms,counts)=Self::rebuild(source)?;
        Ok(Self{source,binding:expected.clone(),terms,counts})
    }
    fn rebuild(source:&crate::packed_owner_assembly::C509RegularRowSourceView<'_>)
        ->Result<(Vec<C509Entry>,[usize;C509_RELATIONS]),String> {
        let owner=source.owner()?;
        if owner!=C509_OWNER{return Err("C509 retained source owner".into());}
        let mut terms=Vec::new();let mut counts=[0usize;C509_RELATIONS];
        let mut row_relation=BTreeMap::<usize,usize>::new();
        let mut append=|relation:C509Relation,term:Term|->Result<(),String>{
            let slot=relation.slot(owner)?;
            let row_base=owner.checked_mul(ROWS).ok_or("C509 row owner overflow")?;
            if term.row.checked_sub(row_base).filter(|q|*q<ROWS).is_none() {
                return Err("C509 placed term outside owner ROW".into());
            }
            if term.gate.left>=WIDTH*OWNERS||term.gate.right>=WIDTH*OWNERS {
                return Err("C509 placed term outside X domain".into());
            }
            c509_claim_row_relation(&mut row_relation,term.row,slot)?;
            counts[slot]=counts[slot].checked_add(1).ok_or("C509 term count overflow")?;
            terms.push(C509Entry{relation,term});Ok(())
        };
        for (relation,term) in source.terms()? {
            // The source view retains RowPlan::stage_owner output, which is
            // already in its fixed layout. Validate and preserve those exact
            // coordinates; applying fixed placement again would double-map it.
            append(C509Relation::Ordinary(relation),term.clone())?;
        }
        let map_layout=Layout::paired_map_general();
        for context in 0..2 {
            for term in source.map_terms(context)? {
                let placed=map_layout.place(OwnerClass::Carry,Relation::Map(context),owner,
                    term.clone())?;
                C509RegularLayout::require_destination(context,&placed)?;
                append(C509Relation::Map(context),placed)?;
            }
        }
        for context in 0..2 {
            for term in source.score_terms(context)? {
                let placed=C509RegularLayout::place(2+context,term.clone())?;
                C509RegularLayout::require_destination(2+context,&placed)?;
                append(C509Relation::Score(context),placed)?;
            }
        }
        for context in 0..2 {
            for term in source.slack_terms(context)? {
                let placed=C509RegularLayout::place(4+context,term.clone())?;
                C509RegularLayout::require_destination(4+context,&placed)?;
                append(C509Relation::Slack(context),placed)?;
            }
        }
        if terms.len()>TERM_LIMIT||counts[9]==0||counts[10]==0
            ||counts[11]==0||counts[12]==0||counts[13]==0||counts[14]==0 {
            return Err("C509 exact regular Score/Slack term census".into());
        }
        Ok((terms,counts))
    }
    fn check_source_tuples(&self)->Result<(),String> {
        if !c509_source_identity(self.source.owner()?,self.source.binding()?,&self.binding) {
            return Err("C509 source parent/owner binding".into());
        }
        let (expected,counts)=Self::rebuild(self.source)?;
        if !c509_same_ordered_entries(&expected,&self.terms)||counts!=self.counts {
            return Err("C509 ordered fifteen-slot source tuples/counts".into());
        }
        Ok(())
    }
    pub(super) fn terms(&self)->Result<impl Iterator<Item=(C509Relation,&Term)>+'_ ,String> {
        self.check_source_tuples()?;
        Ok(self.terms.iter().map(|entry|(entry.relation,&entry.term)))
    }
    pub(super) fn active_operands(&self)->Result<impl Iterator<Item=C509ActiveOperand>+'_ ,String> {
        self.check_source_tuples()?;
        Ok(self.terms.iter().enumerate().flat_map(|(occurrence,entry)|
            c509_active_operands_for_term(occurrence,entry.relation,&entry.term)
                .into_iter().flatten()))
    }
    pub(super) fn owner(&self)->Result<usize,String> {
        self.check_source_tuples()?;Ok(C509_OWNER)
    }
    pub(super) fn source_binding(&self)->Result<&HeaderSourceBinding,String> {
        self.check_source_tuples()?;Ok(&self.binding)
    }
    pub(super) fn layout_digest(&self)->Result<[u8;32],String> {
        self.check_source_tuples()?;Ok(C509RegularLayout::digest())
    }
    pub(super) fn counts(&self)->Result<[usize;C509_RELATIONS],String> {
        self.check_source_tuples()?;Ok(self.counts)
    }
    pub(super) fn checked_numeric_row(&self,active:&[C509ActiveOperand],
        values:impl ExactSizeIterator<Item=bool>)->Result<C513SelectedNumericRow,String> {
        // Rebuild and compare the borrowed source once. Do not call public
        // batch observations here: each would repeat that complete replay.
        self.check_source_tuples()?;
        if self.binding.owner()!=C509_OWNER || self.terms.len()!=C513_TERMS
            || active.len()!=C513_ACTIVE_READS {
            return Err("C513 exact owner845887 term/active-read census".into());
        }
        let (residuals,counts)=c513_checked_numeric_terms(
            C509_OWNER,ROWS,&self.terms,active,values)?;
        if counts!=self.counts {
            return Err("C513 numeric fifteen-relation term counts".into());
        }
        Ok(C513SelectedNumericRow{binding:self.binding.clone(),
            layout:C509RegularLayout::digest(),terms:self.terms.len(),
            active_reads:active.len(),counts,residuals})
    }
    #[cfg(test)]
    fn terms_mut_for_test(&mut self)->&mut Vec<C509Entry> {&mut self.terms}
}

fn c509_same_ordered_entries(expected:&[C509Entry],observed:&[C509Entry])->bool {
    expected==observed
}
fn c509_claim_row_relation(rows:&mut BTreeMap<usize,usize>,row:usize,slot:usize)
    ->Result<(),String> {
    if let Some(prior)=rows.get(&row) {
        if *prior!=slot {return Err("C509 cross-relation ROW collision".into());}
    } else {rows.insert(row,slot);}
    Ok(())
}
fn c509_source_identity(owner:usize,actual:&HeaderSourceBinding,
    expected:&HeaderSourceBinding)->bool {
    owner==C509_OWNER&&expected.owner()==C509_OWNER&&actual==expected
}

/// The ordinal is global in C509 iteration order, including duplicate terms.
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(super) struct C514Role1EdgeIdentity {
    pub occurrence:usize,pub relation:C509Relation,pub slot:usize,
}

/// A single checked ROW block, retaining the source batch for its lifetime.
/// Neither these edges nor their identities confer physical X-value authority.
pub(super) struct C514Role1EdgeBatch<'b,'a,'s> {
    batch:&'b C509RegularBatch<'a,'s>,
    edges:Vec<crate::sparse_stream_roster::EdgeTerm>,
    sidecar:Vec<C514Role1EdgeIdentity>,
}
impl<'b,'a,'s> C514Role1EdgeBatch<'b,'a,'s> {
    pub(super) fn checked_from_batch(batch:&'b C509RegularBatch<'a,'s>)->Result<Self,String> {
        batch.check_source_tuples()?;
        if batch.binding.owner()!=C509_OWNER || batch.terms.len()!=C513_TERMS {
            return Err("C514 selected ROW owner/term census".into());
        }
        let (edges,sidecar)=c514_adapt_entries(C509_OWNER,&batch.terms)?;
        c514_check_entries(C509_OWNER,&batch.terms,&edges,&sidecar)?;
        Ok(Self{batch,edges,sidecar})
    }
    pub(super) fn edges(&self)->&[crate::sparse_stream_roster::EdgeTerm] {&self.edges}
    pub(super) fn sidecar(&self)->&[C514Role1EdgeIdentity] {&self.sidecar}
    pub(super) fn binding(&self)->&HeaderSourceBinding {&self.batch.binding}
    pub(super) fn layout_digest(&self)->[u8;32] {C509RegularLayout::digest()}
    pub(super) fn counts(&self)->[usize;C509_RELATIONS] {self.batch.counts}
}

fn c514_adapt_entries(owner:usize,entries:&[C509Entry])
    ->Result<(Vec<crate::sparse_stream_roster::EdgeTerm>,Vec<C514Role1EdgeIdentity>),String> {
    if owner!=C509_OWNER {return Err("C514 selected ROW owner".into());}
    let base=owner.checked_mul(ROWS).ok_or("C514 ROW base overflow")?;
    let mut edges=Vec::with_capacity(entries.len());
    let mut sidecar=Vec::with_capacity(entries.len());
    for (occurrence,entry) in entries.iter().enumerate() {
        let family_row=entry.term.row.checked_sub(base).filter(|q|*q<ROWS)
            .ok_or("C514 ROW outside selected owner")?;
        let slot=entry.relation.slot(owner)?;
        edges.push(crate::sparse_stream_roster::EdgeTerm{
            source_slot:owner,family_row,term:entry.term.clone()});
        sidecar.push(C514Role1EdgeIdentity{occurrence,relation:entry.relation,slot});
    }
    Ok((edges,sidecar))
}

fn c514_check_entries(owner:usize,entries:&[C509Entry],
    edges:&[crate::sparse_stream_roster::EdgeTerm],sidecar:&[C514Role1EdgeIdentity])
    ->Result<(),String> {
    if owner!=C509_OWNER || entries.len()!=edges.len() || entries.len()!=sidecar.len() {
        return Err("C514 owner/ordered lengths".into());
    }
    for (occurrence,((entry,edge),identity)) in entries.iter().zip(edges).zip(sidecar).enumerate() {
        let slot=entry.relation.slot(owner)?;
        if *identity!=(C514Role1EdgeIdentity{occurrence,relation:entry.relation,slot})
            || edge.source_slot!=owner || edge.term!=entry.term
            || crate::sparse_stream_roster::global_edge_row(edge.source_slot,edge.family_row,
                21,19,0,&[19])?!=entry.term.row {
            return Err(format!("C514 ordered ROW/relation/term mismatch at {occurrence}"));
        }
    }
    Ok(())
}

#[cfg(test)]
mod c514_edge_adapter_tests {
    use super::*;
    use crate::gkr::Gate;

    fn fixture()->Vec<C509Entry> {
        // Explicit geometry and independently specified tuples, including a
        // foreign left-wire owner and a repeated identical occurrence.
        let row=845_887usize*524_288+17;
        let term=Term{row,gate:Gate{left:123usize*1_048_576+7,
            right:845_887usize*1_048_576+11,c0:Fr::from(2u64),
            c1:Fr::from(3u64),c2:Fr::from(5u64),c3:Fr::from(7u64)}};
        vec![C509Entry{relation:C509Relation::Map(1),term:term.clone()},
            C509Entry{relation:C509Relation::Map(1),term}]
    }
    #[test]
    fn c514_golden_geometry_foreign_left_owner_and_duplicate() {
        let entries=fixture();let (edges,identities)=c514_adapt_entries(845_887,&entries).unwrap();
        assert_eq!(edges.len(),2);assert_eq!(edges[0].source_slot,845_887);
        assert_eq!(edges[0].family_row,17);
        assert_eq!(edges[0].term.row,845_887usize*524_288+17);
        assert_eq!(edges[0].term.gate.left,123usize*1_048_576+7);
        assert_eq!(edges[0].term.gate.right,845_887usize*1_048_576+11);
        assert_eq!((edges[0].term.gate.c0,edges[0].term.gate.c1,
            edges[0].term.gate.c2,edges[0].term.gate.c3),
            (Fr::from(2u64),Fr::from(3u64),Fr::from(5u64),Fr::from(7u64)));
        assert_eq!(edges[0].term,edges[1].term);
        assert_eq!(identities,vec![
            C514Role1EdgeIdentity{occurrence:0,relation:C509Relation::Map(1),slot:10},
            C514Role1EdgeIdentity{occurrence:1,relation:C509Relation::Map(1),slot:10}]);
        assert!(c514_check_entries(845_887,&entries,&edges,&identities).is_ok());
    }
    #[test]
    fn c514_rejects_independent_geometry_identity_and_binding_mutations() {
        let entries=fixture();let (edges,identities)=c514_adapt_entries(845_887,&entries).unwrap();
        for delta in [-1isize,1] {
            let mut changed=edges.clone();changed[0].family_row=changed[0].family_row.checked_add_signed(delta).unwrap();
            assert!(c514_check_entries(845_887,&entries,&changed,&identities).is_err());
            let mut changed=edges.clone();changed[0].term.row=changed[0].term.row.checked_add_signed(delta).unwrap();
            assert!(c514_check_entries(845_887,&entries,&changed,&identities).is_err());
        }
        let mut changed=edges.clone();changed[0].source_slot=845_886;
        assert!(c514_check_entries(845_887,&entries,&changed,&identities).is_err());
        assert!(c514_adapt_entries(845_886,&entries).is_err());
        for field in 0..3 {
            let mut changed=identities.clone();
            match field {0=>changed[0].occurrence=1,1=>changed[0].relation=C509Relation::Map(0),
                2=>changed[0].slot=9,_=>unreachable!()}
            assert!(c514_check_entries(845_887,&entries,&edges,&changed).is_err());
        }
        let mut changed=entries.clone();changed[0].relation=C509Relation::Map(2);
        assert!(c514_adapt_entries(845_887,&changed).is_err());
        let binding=HeaderSourceBinding::diagnostic_for_test(845_887);
        let wrong=HeaderSourceBinding::diagnostic_for_test(845_886);
        assert!(c509_source_identity(845_887,&binding,&binding));
        assert!(!c509_source_identity(845_887,&wrong,&binding));
        assert!(!c509_source_identity(845_886,&binding,&binding));
        for field in 0..5 {
            let changed=binding.mutated_field_for_test(field);
            assert!(!c509_source_identity(845_887,&changed,&binding),"binding field {field}");
        }
    }
}

/// Compile-time API/borrow gate: the batch lifetime is tied to the exact
/// source view returned by ScoredOwnerPackingView, with no second lease input.
#[allow(dead_code)]
fn c509_typed_api_borrow_gate<'a,'s>(
    source:&'a crate::packed_owner_assembly::C509RegularRowSourceView<'s>,
    expected:&HeaderSourceBinding,
)->Result<C509RegularBatch<'a,'s>,String> {
    C509RegularBatch::checked_from_source(source,expected)
}

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(super) struct C509ActiveOperand {
    pub occurrence:usize,pub relation:C509Relation,pub row:usize,
    pub side:OperandSide,pub wire:usize,
    pub c1_active:bool,pub c2_active:bool,pub c3_active:bool,
}
fn c509_active_operands_for_term(occurrence:usize,relation:C509Relation,term:&Term)
    ->[Option<C509ActiveOperand>;2] {
    let gate=&term.gate;let c1_active=!gate.c1.is_zero();
    let c2_active=!gate.c2.is_zero();let c3_active=!gate.c3.is_zero();
    let left=(c1_active||c3_active).then_some(C509ActiveOperand{occurrence,relation,
        row:term.row,side:OperandSide::Left,wire:gate.left,c1_active,c2_active:false,c3_active});
    let right=(c2_active||c3_active).then_some(C509ActiveOperand{occurrence,relation,
        row:term.row,side:OperandSide::Right,wire:gate.right,c1_active:false,c2_active,c3_active});
    [left,right]
}

/// Shared arithmetic and ordered-input predicate, also exercised by small
/// data-only fixtures. It does not mint or emulate any native source token.
fn c513_checked_numeric_terms(owner:usize,row_count:usize,terms:&[C509Entry],
    active:&[C509ActiveOperand],mut values:impl ExactSizeIterator<Item=bool>)
    ->Result<(Vec<Fr>,[usize;C509_RELATIONS]),String> {
    if row_count==0 || row_count>ROWS || values.len()!=active.len() {
        return Err("C513 numeric ROW/value input width".into());
    }
    let row_base=owner.checked_mul(ROWS).ok_or("C513 numeric ROW owner base overflow")?;
    let mut residuals=vec![Fr::zero();row_count];
    let mut counts=[0usize;C509_RELATIONS];
    let mut reads=0usize;
    for (occurrence,entry) in terms.iter().enumerate() {
        let term=&entry.term;
        let q=term.row.checked_sub(row_base).filter(|q|*q<row_count)
            .ok_or("C513 term outside selected owner ROW")?;
        let slot=entry.relation.slot(owner)?;
        counts[slot]=counts[slot].checked_add(1).ok_or("C513 relation term count overflow")?;
        let mut operands=[Fr::zero();2];
        for (side,wanted) in c509_active_operands_for_term(occurrence,entry.relation,term)
            .into_iter().enumerate() {
            if let Some(wanted)=wanted {
                if active.get(reads)!=Some(&wanted) {
                    return Err(format!("C513 missing/reordered/changed active tuple index={reads}"));
                }
                // Tuple identity must be checked before the associated source
                // value is consumed, including equal-zero and repeated wires.
                operands[side]=Fr::from(values.next()
                    .ok_or("C513 missing active operand value")? as u64);
                reads+=1;
            }
        }
        let gate=&term.gate;
        residuals[q]+=gate.c0+gate.c1*operands[0]+gate.c2*operands[1]
            +gate.c3*operands[0]*operands[1];
    }
    if reads!=active.len() {
        return Err("C513 trailing active operand tuple".into());
    }
    if values.next().is_some() {
        return Err("C513 trailing active operand value".into());
    }
    // Terms sharing a ROW may cancel. Decide only after the complete sum,
    // retaining the entire table, including rows without emitted terms.
    if let Some((q,_))=residuals.iter().enumerate().find(|(_,value)|!value.is_zero()) {
        return Err(format!("C513 nonzero selected ROW residual q={q}"));
    }
    Ok((residuals,counts))
}

#[cfg(test)]
mod c513_numeric_row_tests {
    use super::*;
    use crate::gkr::Gate;
    use std::cell::Cell;

    // Data-only arithmetic examples, without any source view or native token.
    // The expected active tuples are written independently of their extractor.
    fn fixture()->(Vec<C509Entry>,Vec<C509ActiveOperand>,Vec<bool>) {
        let base=C509_OWNER*ROWS;
        let left=C509_OWNER*WIDTH+7;let right=C509_OWNER*WIDTH+11;
        let relation=C509Relation::Ordinary(Relation::Header);
        let entry=|q,c0,c1,c2,c3,same_wire|C509Entry{relation,term:Term{row:base+q,
            gate:Gate{left,right:if same_wire{left}else{right},c0,c1,c2,c3}}};
        let z=Fr::zero();let one=Fr::from(1u64);
        let terms=vec![entry(0,one,z,z,z,false),entry(0,z,-one,z,z,false),
            entry(1,-one,z,one,z,false),entry(2,-one,z,z,one,true),
            entry(2,z,one,one,-Fr::from(2u64),false)];
        let operand=|occurrence,q,side,wire,c1_active,c2_active,c3_active|
            C509ActiveOperand{occurrence,relation,row:base+q,side,wire,
                c1_active,c2_active,c3_active};
        let active=vec![
            operand(1,0,OperandSide::Left,left,true,false,false),
            operand(2,1,OperandSide::Right,right,false,true,false),
            operand(3,2,OperandSide::Left,left,false,false,true),
            operand(3,2,OperandSide::Right,left,false,false,true),
            operand(4,2,OperandSide::Left,left,true,false,true),
            operand(4,2,OperandSide::Right,right,false,true,true),
        ];
        (terms,active,vec![true;6])
    }

    #[test]
    fn c513_no_frame_constants_both_active_sides_and_zero_padding() {
        let (terms,active,values)=fixture();
        let (rows,counts)=c513_checked_numeric_terms(C509_OWNER,4,&terms,&active,
            values.iter().copied()).unwrap();
        assert_eq!(rows,vec![Fr::zero();4]);
        assert_eq!(counts[0],5);assert!(counts[1..].iter().all(|count|*count==0));
        // The constant-only term contributes one even with no operands; a
        // later term cancels it. Rejecting an intermediate partial sum is wrong.
        assert!(c513_checked_numeric_terms(C509_OWNER,4,&terms[..1],&[],
            std::iter::empty::<bool>()).unwrap_err().contains("nonzero selected ROW residual q=0"));
        let mut missing_c0=terms.clone();missing_c0[0].term.gate.c0=Fr::zero();
        assert!(c513_checked_numeric_terms(C509_OWNER,4,&missing_c0,&active,
            values.iter().copied()).is_err());
        for index in 0..values.len() {
            let mut changed=values.clone();changed[index]=false;
            assert!(c513_checked_numeric_terms(C509_OWNER,4,&terms,&active,changed.into_iter())
                .unwrap_err().contains("nonzero selected ROW residual"),
                "every active left/right occurrence is value-sensitive: {index}");
        }
        let mut two_nonzero=vec![terms[0].clone(),terms[0].clone()];
        two_nonzero[0].term.row=C509_OWNER*ROWS+3;
        two_nonzero[1].term.row=C509_OWNER*ROWS+1;
        assert!(c513_checked_numeric_terms(C509_OWNER,4,&two_nonzero,&[],
            std::iter::empty::<bool>()).unwrap_err().ends_with("q=1"),
            "report the first nonzero ROW after the complete accumulation");
    }

    #[test]
    fn c513_no_frame_each_tuple_field_precedes_its_value_read() {
        let (terms,active,values)=fixture();
        for field in 0..8 {
            let mut changed=active.clone();
            match field {
                0=>changed[0].occurrence=0,
                1=>changed[0].relation=C509Relation::Map(0),
                2=>changed[0].row+=1,
                3=>changed[0].side=OperandSide::Right,
                4=>changed[0].wire+=1,
                5=>changed[0].c1_active=false,
                6=>changed[0].c2_active=true,
                7=>changed[0].c3_active=true,
                _=>unreachable!(),
            }
            let consumed=Cell::new(0usize);
            let observed=values.iter().copied().inspect(|_|consumed.set(consumed.get()+1));
            assert!(c513_checked_numeric_terms(C509_OWNER,4,&terms,&changed,observed)
                .unwrap_err().contains("active tuple index=0"),"isolated tuple field {field}");
            assert_eq!(consumed.get(),0,"tuple rejection must precede source value consumption");
        }
        let mut changed=active.clone();changed.last_mut().unwrap().occurrence+=1;
        let consumed=Cell::new(0usize);
        assert!(c513_checked_numeric_terms(C509_OWNER,4,&terms,&changed,
            values.iter().copied().inspect(|_|consumed.set(consumed.get()+1))).is_err());
        assert_eq!(consumed.get(),5,"the last tuple is checked before its own value");
        // Equal wires and equal values remain two distinct c3 occurrences.
        let mut reversed=active.clone();reversed.swap(2,3);
        assert_eq!(reversed[2].wire,reversed[3].wire);
        assert!(c513_checked_numeric_terms(C509_OWNER,4,&terms,&reversed,
            values.iter().copied()).is_err());
    }

    #[test]
    fn c513_no_frame_missing_extra_reordered_tuples_and_owner_row_bounds() {
        let (terms,active,values)=fixture();
        let mut missing=active.clone();missing.pop();
        assert!(c513_checked_numeric_terms(C509_OWNER,4,&terms,&missing,
            values[..values.len()-1].iter().copied()).unwrap_err().contains("active tuple index=5"));
        let mut extra=active.clone();extra.push(active[0]);
        let mut extra_values=values.clone();extra_values.push(true);
        assert_eq!(c513_checked_numeric_terms(C509_OWNER,4,&terms,&extra,extra_values.into_iter())
            .unwrap_err(),"C513 trailing active operand tuple");
        let mut duplicate=active.clone();duplicate[1]=duplicate[0];
        assert!(c513_checked_numeric_terms(C509_OWNER,4,&terms,&duplicate,
            values.iter().copied()).is_err());
        let mut reordered=active.clone();reordered.swap(0,1);
        assert!(c513_checked_numeric_terms(C509_OWNER,4,&terms,&reordered,
            values.iter().copied()).is_err());
        for row in [C509_OWNER*ROWS-1,C509_OWNER*ROWS+4] {
            let mut wrong=terms.clone();wrong[0].term.row=row;
            let consumed=Cell::new(0usize);
            assert_eq!(c513_checked_numeric_terms(C509_OWNER,4,&wrong,&active,
                values.iter().copied().inspect(|_|consumed.set(consumed.get()+1)))
                .unwrap_err(),"C513 term outside selected owner ROW");
            assert_eq!(consumed.get(),0);
        }
    }

    // ExactSizeIterator is a safe trait, so the final next() checks must also
    // reject an iterator whose advertised remaining length is inaccurate.
    struct AdvertisedValues {inner:std::vec::IntoIter<bool>,remaining:usize}
    impl Iterator for AdvertisedValues {
        type Item=bool;
        fn next(&mut self)->Option<bool> {
            let value=self.inner.next();
            if value.is_some(){self.remaining=self.remaining.saturating_sub(1);}value
        }
        fn size_hint(&self)->(usize,Option<usize>) {(self.remaining,Some(self.remaining))}
    }
    impl ExactSizeIterator for AdvertisedValues {fn len(&self)->usize {self.remaining}}

    #[test]
    fn c513_no_frame_missing_and_trailing_values_are_checked_independently() {
        let (terms,active,values)=fixture();
        assert_eq!(c513_checked_numeric_terms(C509_OWNER,4,&terms,&active,
            values[..values.len()-1].iter().copied()).unwrap_err(),
            "C513 numeric ROW/value input width");
        let mut extra=values.clone();extra.push(false);
        assert_eq!(c513_checked_numeric_terms(C509_OWNER,4,&terms,&active,
            extra.iter().copied()).unwrap_err(),"C513 numeric ROW/value input width");
        let short=AdvertisedValues{inner:values[..values.len()-1].to_vec().into_iter(),
            remaining:active.len()};
        assert_eq!(c513_checked_numeric_terms(C509_OWNER,4,&terms,&active,short)
            .unwrap_err(),"C513 missing active operand value");
        let long=AdvertisedValues{inner:extra.into_iter(),remaining:active.len()};
        assert_eq!(c513_checked_numeric_terms(C509_OWNER,4,&terms,&active,long)
            .unwrap_err(),"C513 trailing active operand value");
    }

    #[test]
    fn c513_no_frame_numeric_result_getters_and_retained_table_size() {
        let (terms,active,values)=fixture();
        let (residuals,counts)=c513_checked_numeric_terms(C509_OWNER,ROWS,&terms,&active,
            values.into_iter()).unwrap();
        let binding=HeaderSourceBinding::diagnostic_for_test(C509_OWNER);
        let layout=C509RegularLayout::digest();
        let row=C513SelectedNumericRow{binding:binding.clone(),layout,terms:terms.len(),
            active_reads:active.len(),counts,residuals};
        assert_eq!(row.binding(),&binding);assert_eq!(row.layout_digest(),layout);
        assert_eq!(row.terms(),5);assert_eq!(row.active_reads(),6);assert_eq!(row.counts(),counts);
        assert_eq!(row.residuals().len(),524_288);assert!(row.residuals().iter().all(Zero::is_zero));
        assert_eq!(std::mem::size_of::<Fr>(),32);
        assert_eq!(row.residuals.len()*std::mem::size_of::<Fr>(),16*1024*1024);
        assert!(row.residuals.capacity()>=row.residuals.len());
        println!("C513_DATA_ONLY_LAYOUT result_size={} active_tuple_size={} fr_size={} residual_len={} residual_capacity={} residual_bytes={} native_source=false physical_authority=false",
            std::mem::size_of::<C513SelectedNumericRow>(),std::mem::size_of::<C509ActiveOperand>(),
            std::mem::size_of::<Fr>(),row.residuals.len(),row.residuals.capacity(),
            row.residuals.capacity()*std::mem::size_of::<Fr>());
    }
}

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(super) struct CompleteActiveOperand {
    pub occurrence:usize,pub relation:CompleteRelation,pub row:usize,
    pub side:OperandSide,pub wire:usize,
    pub c1_active:bool,pub c2_active:bool,pub c3_active:bool,
}
impl CompleteActiveOperand {
    fn matches_legacy(self,other:ActiveOperand)->bool {
        self.relation.legacy_relation()==Some(other.relation)
            &&self.occurrence==other.occurrence&&self.row==other.row
            &&self.side==other.side&&self.wire==other.wire
            &&self.c1_active==other.c1_active&&self.c2_active==other.c2_active
            &&self.c3_active==other.c3_active
    }
}
pub(super) struct CompleteActiveOperandIter<I> {
    terms:std::iter::Enumerate<I>,pending_right:Option<CompleteActiveOperand>,
}
fn complete_active_operands_for_term(occurrence:usize,relation:CompleteRelation,term:&Term)
    ->[Option<CompleteActiveOperand>;2] {
    let gate=&term.gate;
    let c1_active=!gate.c1.is_zero();let c2_active=!gate.c2.is_zero();
    let c3_active=!gate.c3.is_zero();
    let left=(c1_active||c3_active).then_some(CompleteActiveOperand{occurrence,relation,
        row:term.row,side:OperandSide::Left,wire:gate.left,c1_active,c2_active:false,c3_active});
    let right=(c2_active||c3_active).then_some(CompleteActiveOperand{occurrence,relation,
        row:term.row,side:OperandSide::Right,wire:gate.right,c1_active:false,c2_active,c3_active});
    [left,right]
}
impl<'a,I> Iterator for CompleteActiveOperandIter<I>
where I:Iterator<Item=(CompleteRelation,&'a Term)> {
    type Item=CompleteActiveOperand;
    fn next(&mut self)->Option<Self::Item> {
        if let Some(right)=self.pending_right.take(){return Some(right);}
        loop {
            let(occurrence,(relation,term))=self.terms.next()?;
            let [left,right]=complete_active_operands_for_term(occurrence,relation,term);
            match(left,right){
                (Some(left),right)=>{self.pending_right=right;return Some(left);}
                (None,Some(right))=>return Some(right),
                (None,None)=>continue,
            }
        }
    }
}

#[derive(Clone,Copy,Debug,PartialEq,Eq,PartialOrd,Ord)]
enum CompleteScoreImportKind {PreviousR,Cap,WorkUpper}
#[derive(Clone,Copy,Debug,PartialEq,Eq,PartialOrd,Ord)]
struct CompleteScoreImportKey {context:usize,kind:CompleteScoreImportKind,wire:usize}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
struct CompleteScoreImportRecord {value:bool}
struct CompleteScoreImportCensus {
    records:BTreeMap<CompleteScoreImportKey,CompleteScoreImportRecord>,
    by_kind:[usize;3],
}
impl CompleteScoreImportCensus {
    fn from_view(view:&crate::packed_owner_assembly::Eligible08CompleteRowSourceView<'_>)
        ->Result<Self,String> {
        let records=view.score_imports()?;
        Self::from_records(records.map(|record|
            (record.context(),record.kind(),record.wire(),record.value())))
    }
    fn from_records(records:impl Iterator<Item=(usize,
        crate::packed_owner_assembly::Eligible08ScoreImportKind,usize,Fr)>)->Result<Self,String> {
        use crate::packed_owner_assembly::Eligible08ScoreImportKind as SourceKind;
        let mut checked=BTreeMap::new();let mut by_kind=[0usize;3];
        let mut by_context=[[0usize;3];2];
        let previous_bases=[677_501usize,685_693];
        let cap_bases=[CAP0_BASE,CAP1_BASE];
        let mut ordinal=0usize;
        for (context,source_kind,wire,value) in records {
            let context_block=ordinal/514;let context_offset=ordinal%514;
            let (expected_kind,expected_local)=if context_offset<225 {
                (SourceKind::PreviousR{owner:COMPLETE_OWNER-1},
                    previous_bases.get(context_block).copied()
                        .and_then(|base|base.checked_add(1_318+context_offset)))
            }else if context_offset<290 {
                let bit=context_offset-225;
                (SourceKind::Cap{owner:COMPLETE_OWNER,origin:CAP0_ORIGIN,
                    max_owner:FOREIGN_MAX_OWNER},cap_bases.get(context_block).copied()
                        .and_then(|base|base.checked_add(740+bit)))
            }else{
                let bit=context_offset-290;
                (SourceKind::WorkUpper{owner:COMPLETE_OWNER-1,height:CAP0_ORIGIN},
                    Some(987_450+bit))
            };
            let expected_owner=match expected_kind {
                SourceKind::Cap{owner,..}=>owner,
                SourceKind::PreviousR{owner}|SourceKind::WorkUpper{owner,..}=>owner,
            };
            let expected_wire=expected_owner.checked_mul(WIDTH)
                .and_then(|base|expected_local.and_then(|local|base.checked_add(local)))
                .ok_or("v5 ordered Score import expected wire overflow")?;
            if context_block>=2||context!=context_block||source_kind!=expected_kind||wire!=expected_wire {
                return Err("v5 reordered/mismatched Score import context/kind/wire".into());
            }
            ordinal=ordinal.checked_add(1).ok_or("v5 Score import ordinal overflow")?;
            if context>=2||wire>=WIDTH*OWNERS {
                return Err("v5 Score import context/physical wire extent".into());
            }
            let (kind,index,owner,local_start,width)=match source_kind {
                SourceKind::PreviousR{owner}=>{
                    let start=previous_bases[context].checked_add(1_318)
                        .ok_or("v5 PreviousR local wire overflow")?;
                    (CompleteScoreImportKind::PreviousR,0,owner,start,225)
                }
                SourceKind::Cap{owner,origin,max_owner}=>{
                    if origin!=CAP0_ORIGIN||max_owner!=FOREIGN_MAX_OWNER {
                        return Err("v5 Cap source origin/preceding MAX owner".into());
                    }
                    let start=cap_bases[context].checked_add(740)
                        .ok_or("v5 Cap local wire overflow")?;
                    (CompleteScoreImportKind::Cap,1,owner,start,65)
                }
                SourceKind::WorkUpper{owner,height}=>{
                    if height!=CAP0_ORIGIN {
                        return Err("v5 WorkUpper source height".into());
                    }
                    (CompleteScoreImportKind::WorkUpper,2,owner,987_450,224)
                }
            };
            let expected_owner=match kind {
                CompleteScoreImportKind::Cap=>COMPLETE_OWNER,
                CompleteScoreImportKind::PreviousR|CompleteScoreImportKind::WorkUpper=>COMPLETE_OWNER-1,
            };
            let owner_base=expected_owner.checked_mul(WIDTH).ok_or("v5 import owner base overflow")?;
            let local=wire.checked_sub(owner_base).filter(|_|owner==expected_owner)
                .ok_or("v5 Score import source owner/wire mismatch")?;
            let local_end=local_start.checked_add(width).ok_or("v5 import range overflow")?;
            if !(local_start..local_end).contains(&local) {
                return Err("v5 Score import source-kind/context/wire mismatch".into());
            }
            let value=if value.is_zero(){false}else if value==Fr::from(1u64){true}
                else{return Err("v5 Score import non-Boolean source value".into());};
            let key=CompleteScoreImportKey{context,kind,wire};
            if checked.insert(key,CompleteScoreImportRecord{value}).is_some() {
                return Err("v5 duplicate Score import source record".into());
            }
            by_kind[index]=by_kind[index].checked_add(1).ok_or("v5 Score import count overflow")?;
            by_context[context][index]=by_context[context][index]
                .checked_add(1).ok_or("v5 Score import context count overflow")?;
        }
        if ordinal!=1_028||by_kind!=[450,130,448]||by_context!=[[225,65,224],[225,65,224]]
            ||checked.len()!=1_028 {
            return Err("v5 exact ordered Score import census by context/kind".into());
        }
        Ok(Self{records:checked,by_kind})
    }
    fn record_counts(&self)->[usize;3] {self.by_kind}
    fn read(&self,context:usize,kind:CompleteScoreImportKind,wire:usize)
        ->Result<bool,String> {
        self.records.get(&CompleteScoreImportKey{context,kind,wire}).map(|record|record.value)
            .ok_or_else(||"v5 active Score operand lacks context/kind-qualified retained import".into())
    }
}

struct CompleteTypedSourceCells {
    score_values:BTreeMap<(usize,usize),bool>,
    slack_values:BTreeMap<(usize,usize),bool>,
    score_counts:[usize;2],
    slack_counts:[usize;2],
}
fn complete_score_author(context:usize)->crate::packed_owner_assembly::ScoreReplayAuthor {
    crate::packed_owner_assembly::ScoreReplayAuthor{context,origin:CAP0_ORIGIN,
        previous_owner:COMPLETE_OWNER-1,max_owner:FOREIGN_MAX_OWNER,cap_owner:COMPLETE_OWNER}
}
impl CompleteTypedSourceCells {
    fn checked(batch:&CompleteBatch<'_,'_>,stage:&NativePartialXRowStage<'_>,
        census:&NativeOwnerAuthorCensus,
        view:&crate::packed_owner_assembly::Eligible08CompleteRowSourceView<'_>)
        ->Result<Self,String> {
        use crate::packed_owner_assembly::{Bank53TypedAuthor,Eligible08SlackCellAuthor};
        let source=batch.source_binding();let mut score_values=BTreeMap::new();
        let mut slack_values=BTreeMap::new();let mut score_counts=[0usize;2];
        let mut slack_counts=[0usize;2];
        for (wire,author,value) in view.score_cells() {
            let context=author.context;
            if context>=2||author!=complete_score_author(context) {
                return Err("v5 retained Score cell author/context".into());
            }
            let boolean=if value.is_zero(){false}else if value==Fr::from(1u64){true}
                else{return Err("v5 retained Score cell non-Boolean value".into());};
            let (physical_author,physical)=census.checked_score_slack_cell(
                source,stage.row,view,context,wire)?;
            if physical_author!=Bank53TypedAuthor::Score(author)||physical!=boolean
                ||score_values.insert((context,wire),boolean).is_some() {
                return Err("v5 typed Score source/physical/packed cell mismatch".into());
            }
            score_counts[context]=score_counts[context].checked_add(1)
                .ok_or("v5 Score source-cell count overflow")?;
        }
        for (wire,author,value) in view.slack_cells() {
            let context=match author {
                Eligible08SlackCellAuthor::Slack(context)=>context,
                Eligible08SlackCellAuthor::Unrecognized=>return Err("v5 untyped Slack cell".into()),
            };
            if context>=2||value {
                return Err("v5 retained Slack cell context/nonzero value".into());
            }
            let (physical_author,physical)=census.checked_score_slack_cell(
                source,stage.row,view,context,wire)?;
            if physical_author!=Bank53TypedAuthor::Slack(context)||physical
                ||slack_values.insert((context,wire),value).is_some() {
                return Err("v5 typed Slack source/physical/packed cell mismatch".into());
            }
            slack_counts[context]=slack_counts[context].checked_add(1)
                .ok_or("v5 Slack source-cell count overflow")?;
        }
        if score_counts!=[2_048,2_048]||slack_counts!=[387,387] {
            return Err("v5 exact typed Score/Slack source-cell counts".into());
        }
        Ok(Self{score_values,slack_values,score_counts,slack_counts})
    }
}

#[derive(Clone,Debug,PartialEq,Eq)]
pub(super) struct CompleteRowEvidence {
    pub terms:usize,
    pub active_reads:usize,
    pub residual_rows:usize,
    /// Six source/destination intervals admitted by the source tuple and ROW checks.
    pub checked_ranges:[(usize,usize,usize,usize);6],
    pub physical_authors:[usize;6],
    pub map_helper_reads:usize,
    pub work_d_reads:usize,
    pub map_source_cells:[usize;2],
    pub work_d_source_cells:[usize;2],
    pub score_source_cells:[usize;2],
    pub slack_source_cells:[usize;2],
    /// Map0, Map1, Score0, Score1, Slack0, Slack1 typed source cells.
    pub typed_bank53_authors:[usize;6],
    /// PreviousR, local Cap, WorkUpper retained import records.
    pub import_records_by_kind:[usize;3],
    /// PreviousR and WorkUpper active occurrences, preserving context counts.
    pub foreign_occurrences_by_kind:[usize;2],
    pub local_cap_occurrences:usize,
    pub open_reads:usize,
    pub pending_reads:usize,
}

#[derive(Default)]
struct CompleteModernReadCounts {
    foreign_by_kind:[usize;2],
    foreign_by_context:[[usize;2];2],
    cap_by_context:[usize;2],
}
fn increment_complete_count(count:&mut usize)->Result<(),String> {
    *count=count.checked_add(1).ok_or("v5 active occurrence count overflow")?;Ok(())
}

impl<'a,'s> CompleteBatch<'a,'s> {
    fn checked_modern_value(&self,operand:CompleteActiveOperand,
        stage:&NativePartialXRowStage<'_>,census:&NativeOwnerAuthorCensus,
        view:&crate::packed_owner_assembly::Eligible08CompleteRowSourceView<'_>,
        imports:&CompleteScoreImportCensus,cells:&CompleteTypedSourceCells,
        counts:&mut CompleteModernReadCounts)->Result<bool,String> {
        use crate::packed_owner_assembly::Bank53TypedAuthor;
        match operand.relation {
            CompleteRelation::Score(context)if context<2=>{
                let owner=operand.wire/WIDTH;let local=operand.wire%WIDTH;
                if owner==COMPLETE_OWNER {
                    let cap_start=[CAP0_BASE,CAP1_BASE][context]
                        .checked_add(740).ok_or("v5 Cap operand start overflow")?;
                    let cap_end=cap_start.checked_add(65).ok_or("v5 Cap operand end overflow")?;
                    if (cap_start..cap_end).contains(&local) {
                        let imported=imports.read(context,CompleteScoreImportKind::Cap,operand.wire)?;
                        let (author,physical)=census.checked_cell(self.source_binding(),stage.row,
                            operand.wire)?;
                        if author!=NativePhysicalAuthor::Cap||physical!=imported {
                            return Err("v5 local Cap publication/physical author/value".into());
                        }
                        increment_complete_count(&mut counts.cap_by_context[context])?;
                        return Ok(physical);
                    }
                    let (author,physical)=census.checked_score_slack_cell(self.source_binding(),
                        stage.row,view,context,operand.wire)?;
                    let source=cells.score_values.get(&(context,operand.wire))
                        .ok_or("v5 local Score operand lacks retained typed source cell")?;
                    if author!=Bank53TypedAuthor::Score(complete_score_author(context))
                        ||source!=&physical {
                        return Err("v5 local Score typed source/physical/packed read".into());
                    }
                    return Ok(physical);
                }
                if owner!=COMPLETE_OWNER-1 {
                    return Err("v5 Score foreign X owner is outside retained sources".into());
                }
                let previous_start=[677_501usize,685_693][context]
                    .checked_add(1_318).ok_or("v5 PreviousR operand start overflow")?;
                let previous_end=previous_start.checked_add(225)
                    .ok_or("v5 PreviousR operand end overflow")?;
                let upper_end=987_450usize.checked_add(224)
                    .ok_or("v5 WorkUpper operand end overflow")?;
                let (kind,index)=if (previous_start..previous_end).contains(&local) {
                    (CompleteScoreImportKind::PreviousR,0)
                }else if (987_450..upper_end).contains(&local) {
                    (CompleteScoreImportKind::WorkUpper,1)
                }else{
                    return Err("v5 foreign Score operand lacks PreviousR/WorkUpper source".into());
                };
                let value=imports.read(context,kind,operand.wire)?;
                increment_complete_count(&mut counts.foreign_by_kind[index])?;
                increment_complete_count(&mut counts.foreign_by_context[context][index])?;
                Ok(value)
            }
            CompleteRelation::Slack(context)if context<2=>{
                if operand.wire/WIDTH!=COMPLETE_OWNER {
                    return Err("v5 Slack operand must be selected-owner local".into());
                }
                let (author,physical)=census.checked_score_slack_cell(self.source_binding(),
                    stage.row,view,context,operand.wire)?;
                let source=cells.slack_values.get(&(context,operand.wire))
                    .ok_or("v5 Slack operand lacks retained typed zero source")?;
                if author!=Bank53TypedAuthor::Slack(context)||physical||*source {
                    return Err("v5 Slack typed source/physical/packed nonzero read".into());
                }
                Ok(false)
            }
            _=>Err("v5 active operand outside modern Score/Slack relations".into()),
        }
    }

    fn checked_complete_residuals(&self,mut values:impl Iterator<Item=bool>)
        ->Result<(usize,usize),String> {
        let row_base=self.owner().checked_mul(ROWS).ok_or("v5 ROW owner base overflow")?;
        let mut residuals=vec![Fr::zero();ROWS];let mut terms=0usize;
        for (occurrence,(relation,term)) in self.terms().enumerate() {
            let q=term.row.checked_sub(row_base).filter(|q|*q<ROWS)
                .ok_or("v5 physical ROW term owner")?;
            let [left,right]=complete_active_operands_for_term(occurrence,relation,term);
            let left=if left.is_some(){Fr::from(values.next()
                .ok_or("v5 missing active left operand value")? as u64)}else{Fr::zero()};
            let right=if right.is_some(){Fr::from(values.next()
                .ok_or("v5 missing active right operand value")? as u64)}else{Fr::zero()};
            let gate=&term.gate;
            residuals[q]+=gate.c0+gate.c1*left+gate.c2*right+gate.c3*left*right;
            terms=terms.checked_add(1).ok_or("v5 relation term count overflow")?;
        }
        if values.next().is_some() {return Err("v5 trailing active operand value".into());}
        if let Some((q,_))=residuals.iter().enumerate().find(|(_,value)|!value.is_zero()) {
            return Err(format!("v5 nonzero ROW residual q={q}"));
        }
        Ok((terms,ROWS))
    }

    fn checked_coactive_values(&self,stage:&NativePartialXRowStage<'_>,
        census:&NativeOwnerAuthorCensus,
        view:&crate::packed_owner_assembly::Eligible08CompleteRowSourceView<'_>)
        ->Result<CompleteRowEvidence,String> {
        if !std::ptr::eq(self.view,view)||view.binding()!=self.source_binding() {
            return Err("v5 complete source view must retain exact batch custody".into());
        }
        // The sink view has already checked and retained the publication chain;
        // consume its cached ordered records once, with context/kind/wire keys.
        let imports=CompleteScoreImportCensus::from_view(view)?;
        let map_view=view.map_view();
        let (map_reads,mut values)=self.base.checked_coactive_map_read_values(
            stage,census,&map_view)?;
        census.require_complete_row_view(self.source_binding(),stage.row,view)?;
        let cells=CompleteTypedSourceCells::checked(self,stage,census,view)?;

        // Compare each C454 prefix occurrence against the same full v5 ordinal,
        // side, ROW, wire, relation, and activation flags before extending it.
        let mut complete_operands=self.active_operands();let mut prefix_count=0usize;
        for legacy in self.base.active_operands() {
            let complete=complete_operands.next().ok_or("v5 complete prefix operand omitted")?;
            if !complete.matches_legacy(legacy) {
                return Err("v5 C454 prefix active occurrence identity changed".into());
            }
            prefix_count=prefix_count.checked_add(1).ok_or("v5 prefix count overflow")?;
        }
        if prefix_count!=values.len()||prefix_count!=map_reads.active_reads {
            return Err("v5 C454 prefix active read count".into());
        }

        let mut modern_counts=CompleteModernReadCounts::default();
        for operand in complete_operands {
            let value=self.checked_modern_value(operand,stage,census,view,&imports,&cells,
                &mut modern_counts)?;
            values.push(value);
        }
        if modern_counts.foreign_by_kind!=[450,448]
            ||modern_counts.foreign_by_context!=[[225,224],[225,224]]
            ||modern_counts.cap_by_context!=[65,65] {
            return Err("v5 exact active foreign/Cap occurrence census".into());
        }
        let active_reads=values.len();
        let (terms,residual_rows)=self.checked_complete_residuals(values.into_iter())?;
        let expected_terms=self.expected.iter().try_fold(0usize,|sum,count|
            sum.checked_add(*count).ok_or("v5 expected term count overflow"))?;
        if terms!=expected_terms||residual_rows!=ROWS {
            return Err("v5 complete relation term/residual census".into());
        }
        let map_source_cells=map_reads.map_source_cells;
        let work_d_source_cells=map_reads.work_d_source_cells;
        let score_source_cells=cells.score_counts;
        let slack_source_cells=cells.slack_counts;
        let typed_bank53_authors=[map_source_cells[0],map_source_cells[1],
            score_source_cells[0],score_source_cells[1],slack_source_cells[0],slack_source_cells[1]];
        let local_cap_occurrences=modern_counts.cap_by_context[0]
            .checked_add(modern_counts.cap_by_context[1]).ok_or("v5 Cap occurrence count overflow")?;
        let checked_ranges=std::array::from_fn(|index| {
            let (source_start,source_end)=COMPLETE_SOURCE_INTERVALS[index];
            let (destination_start,destination_end)=COMPLETE_DESTINATION_INTERVALS[index];
            (source_start,source_end,destination_start,destination_end)
        });
        Ok(CompleteRowEvidence{terms,active_reads,residual_rows,checked_ranges,
            physical_authors:map_reads.physical_authors,
            map_helper_reads:map_reads.map_helper_reads,work_d_reads:map_reads.work_d_reads,
            map_source_cells,work_d_source_cells,score_source_cells,slack_source_cells,
            typed_bank53_authors,import_records_by_kind:imports.record_counts(),
            foreign_occurrences_by_kind:modern_counts.foreign_by_kind,
            local_cap_occurrences,open_reads:0,pending_reads:0})
    }
}

fn anchor_source_lists<'a>(bundle:&'a Eligible08MapSlackAnchorBundle,
    source:&HeaderSourceBinding,
)->Result<[&'a [Term];6],String> {
    if bundle.map_slack().map_lease().binding()!=source {
        return Err("v3 exact ordinary/Bank53 source binding".into());
    }
    // These are checked opaque source interfaces, including native predecessor,
    // exact Map identities, author census and ordered independent Score replay.
    bundle.checked_score_cells(source,ANCHOR_OWNER,OwnerClass::Carry)?;
    let lists=[bundle.map_slack().map_lease().terms(0)?,
        bundle.map_slack().map_lease().terms(1)?,
        bundle.checked_score_terms(source,ANCHOR_OWNER,OwnerClass::Carry,0)?,
        bundle.checked_score_terms(source,ANCHOR_OWNER,OwnerClass::Carry,1)?,
        bundle.map_slack().checked_slack_terms(source,ANCHOR_OWNER,OwnerClass::Carry,0)?,
        bundle.map_slack().checked_slack_terms(source,ANCHOR_OWNER,OwnerClass::Carry,1)?];
    if lists[2].is_empty()||lists[3].is_empty()||lists[4].len()!=387||lists[5].len()!=387 {
        return Err("v3 checked Score/Slack source census".into());
    }
    Ok(lists)
}

/// Structural admission only. No packed-row, typed reader, proof or physical
/// writer receipt is exposed. The checked bundle remains borrowed by the stage.
#[derive(Clone)]
pub(super) struct AnchorBatch<'a> {
    base:Arc<Batch>,expected_base:Arc<Batch>,bundle:&'a Eligible08MapSlackAnchorBundle,
    bank:[Vec<Term>;6],bank_relations:[AnchorRelation;6],
    source:HeaderSourceBinding,class:OwnerClass,layout:[u8;32],
}
impl AnchorBatch<'_> {
    pub(super) fn owner(&self)->usize {self.base.owner}
    pub(super) fn class(&self)->OwnerClass {self.class}
    pub(super) fn source_binding(&self)->&HeaderSourceBinding {&self.source}
    pub(super) fn layout_digest(&self)->[u8;32] {self.layout}
    pub(super) fn terms(&self)->impl Iterator<Item=(AnchorRelation,&Term)> {
        self.base.terms().map(|(r,t)|(AnchorRelation::Ordinary(r),t))
            .chain(self.bank.iter().enumerate().flat_map(move|(index,terms)|
                terms.iter().map(move|term|(self.bank_relations[index],term))))
    }
    fn check_source_tuples(&self)->Result<[usize;ANCHOR_RELATIONS],String> {
        if self.owner()!=ANCHOR_OWNER||self.class!=OwnerClass::Carry
            ||self.base.class!=self.class||self.base.source!=self.source
            ||self.base.layout!=Layout::fixed().digest()
            ||self.base.owner!=self.expected_base.owner||self.base.class!=self.expected_base.class
            ||self.base.layout!=self.expected_base.layout||self.base.source!=self.expected_base.source
            ||self.base.expected!=self.expected_base.expected
            ||self.base.relations!=self.expected_base.relations
            ||self.base.terms!=self.expected_base.terms {
            return Err("v3 exact ordinary source tuples/binding".into());
        }
        let lists=anchor_source_lists(self.bundle,&self.source)?;
        let mut expected=[0;ANCHOR_RELATIONS];expected[..9].copy_from_slice(&self.base.expected[..9]);
        for index in 0..6 {
            if self.bank_relations[index]!=AnchorRelation::bank(index)
                ||self.bank[index].len()!=lists[index].len() {
                return Err("v3 ordered Bank53 relation/source census".into());
            }
            // Compare the complete Term (row, both wires, all coefficients).
            // Preserve repeated monomials and every constant/zero-valued term.
            for (staged,source) in self.bank[index].iter().zip(lists[index]) {
                if staged!=&AnchorLayout::place(index,source.clone())? {
                    return Err("v3 ordered Bank53 source tuples".into());
                }
            }
            expected[9+index]=lists[index].len();
        }
        Ok(expected)
    }
}

/// One atomic v3 admission. All preaggregation claims are checked before the
/// only mutation; failed admission leaves every registry field unchanged.
#[derive(Clone,Debug,PartialEq,Eq)]
pub(super) struct AnchorRowRegistry {
    source:HeaderSourceBinding,committed:bool,rows:Vec<u8>,
}
impl AnchorRowRegistry {
    fn check(&self,batch:&AnchorBatch<'_>)->Result<Vec<u8>,String> {
        if self.committed {return Err("v3 duplicate complete producer batch".into());}
        if batch.owner()!=ANCHOR_OWNER||batch.class!=OwnerClass::Carry
            ||batch.layout!=AnchorLayout::digest()||batch.source!=self.source {
            return Err("v3 ROW owner/class/layout/source binding".into());
        }
        let mut rows=vec![0u8;ROWS];let mut counts=[0;ANCHOR_RELATIONS];
        let mut placement_valid=true;let mut count=0;
        // Collision precedes source-tuple/placement checks and aggregation.
        // Equal-zero gates still claim their relation's physical ROW.
        for (relation,term) in batch.terms() {
            count+=1;if count>TERM_LIMIT {return Err("v3 per-owner term bound".into());}
            let slot=relation.slot(ANCHOR_OWNER)?;
            let q=term.row.checked_sub(ANCHOR_OWNER*ROWS).filter(|q|*q<ROWS)
                .ok_or("v3 physical ROW owner")?;
            if term.gate.left>=WIDTH*OWNERS||term.gate.right>=WIDTH*OWNERS {
                return Err("v3 physical X extent".into());
            }
            counts[slot]+=1;let tag=(slot+1)as u8;
            if rows[q]!=0&&rows[q]!=tag {return Err("v3 cross-relation ROW collision".into());}
            rows[q]=tag;placement_valid &= AnchorLayout::placed(relation,q);
        }
        if counts!=batch.check_source_tuples()? {return Err("v3 source omission/duplicate".into());}
        if !placement_valid {return Err("v3 ROW placement/reservation".into());}
        Ok(rows)
    }
    pub(super) fn commit(&mut self,batch:&AnchorBatch<'_>)->Result<(),String> {
        let rows=self.check(batch)?;self.rows=rows;self.committed=true;Ok(())
    }
    pub(super) fn distinct_rows(&self)->usize {self.rows.iter().filter(|tag|**tag!=0).count()}
}

/// Separate v3 occurrence identity; constant-only terms retain their ordinal.
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(super) struct AnchorActiveOperand {
    pub occurrence:usize,pub relation:AnchorRelation,pub row:usize,
    pub side:OperandSide,pub wire:usize,
    pub c1_active:bool,pub c2_active:bool,pub c3_active:bool,
}
pub(super) struct AnchorActiveOperandIter<I> {
    terms:std::iter::Enumerate<I>,pending_right:Option<AnchorActiveOperand>,
}
impl<'a,I:Iterator<Item=(AnchorRelation,&'a Term)>> Iterator for AnchorActiveOperandIter<I> {
    type Item=AnchorActiveOperand;
    fn next(&mut self)->Option<Self::Item> {
        if let Some(right)=self.pending_right.take(){return Some(right);}
        loop {
            let(occurrence,(relation,term))=self.terms.next()?;let gate=&term.gate;
            let c1_active=!gate.c1.is_zero();let c2_active=!gate.c2.is_zero();
            let c3_active=!gate.c3.is_zero();
            let left=(c1_active||c3_active).then_some(AnchorActiveOperand{
                occurrence,relation,row:term.row,side:OperandSide::Left,wire:gate.left,
                c1_active,c2_active:false,c3_active});
            let right=(c2_active||c3_active).then_some(AnchorActiveOperand{
                occurrence,relation,row:term.row,side:OperandSide::Right,wire:gate.right,
                c1_active:false,c2_active,c3_active});
            match(left,right){(Some(left),right)=>{self.pending_right=right;return Some(left);}
                (None,Some(right))=>return Some(right),(None,None)=>continue}
        }
    }
}
impl AnchorBatch<'_> {
    pub(super) fn active_operands(&self)->impl Iterator<Item=AnchorActiveOperand>+'_ {
        AnchorActiveOperandIter{terms:self.terms().enumerate(),pending_right:None}
    }
}

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(super) enum AnchorSourceKind {Header,Tree,Daa,WorkUpper,WorkD,Unqualified}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(super) enum AnchorLocalDomain {Daa,Tree,Unqualified}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(super) enum AnchorCellAuthor {Map(usize),ScoreAnchor(usize),Slack(usize)}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(super) enum AnchorRead {
    Bank53{operand:AnchorActiveOperand,author:AnchorCellAuthor,value:bool},
    Header{operand:AnchorActiveOperand,value:bool},
    OpenLocal{operand:AnchorActiveOperand,domain:AnchorLocalDomain,
        expected:AnchorSourceKind},
    OpenForeign{operand:AnchorActiveOperand,source_owner:usize,expected:AnchorSourceKind},
}
impl AnchorRead {
    pub(super) fn operand(&self)->AnchorActiveOperand {
        match *self {Self::Bank53{operand,..}|Self::Header{operand,..}
            |Self::OpenLocal{operand,..}|Self::OpenForeign{operand,..}=>operand}
    }
}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
struct AnchorCell {wire:usize,author:AnchorCellAuthor,value:bool}
/// This view can only be made from the source-owned checked typed interfaces.
/// Its ordered partition also validates authored false, independently of reads.
#[derive(Clone)]
struct AnchorSourceView<'b> {
    bundle:&'b Eligible08MapSlackAnchorBundle,binding:HeaderSourceBinding,
    cells:Vec<AnchorCell>,imports:std::collections::BTreeMap<usize,AnchorSourceKind>,
}
impl<'b> AnchorSourceView<'b> {
    fn checked(bundle:&'b Eligible08MapSlackAnchorBundle,binding:&HeaderSourceBinding)
        ->Result<Self,String> {
        let maps=bundle.map_slack().map_lease().checked_cells(binding,ANCHOR_OWNER,OwnerClass::Carry)?;
        let scores=bundle.checked_score_cells(binding,ANCHOR_OWNER,OwnerClass::Carry)?;
        let slack=bundle.map_slack().checked_slack_cells(binding,ANCHOR_OWNER,OwnerClass::Carry)?;
        if maps.len()!=2*5757||scores.len()!=2*2048||slack.len()!=2*387 {
            return Err("v3 typed Map/ScoreAnchor/Slack census".into());
        }
        let mut cells=Vec::with_capacity(16384);
        for context in 0..2 {
            for offset in 0..5757 {
                let cell=&maps[context*5757+offset];
                if cell.context()!=context||cell.offset()!=offset {
                    return Err("v3 typed Map context/offset".into());
                }
                cells.push(AnchorCell{wire:cell.physical_wire(),
                    author:AnchorCellAuthor::Map(context),value:cell.value()});
            }
            for offset in 0..2048 {
                let cell=&scores[context*2048+offset];
                if cell.context()!=context {return Err("v3 typed ScoreAnchor context".into());}
                cells.push(AnchorCell{wire:cell.physical_wire(),
                    author:AnchorCellAuthor::ScoreAnchor(context),value:cell.value()});
            }
            for offset in 0..387 {
                let cell=&slack[context*387+offset];
                if cell.context()!=context {return Err("v3 typed Slack context".into());}
                cells.push(AnchorCell{wire:cell.physical_wire(),
                    author:AnchorCellAuthor::Slack(context),value:cell.value()});
            }
        }
        let mut imports=std::collections::BTreeMap::new();
        for import in bundle.map_slack().map_lease().imports() {
            use crate::packed_owner_assembly::MapPairSourceAuthor;
            let kind=match import.author() {MapPairSourceAuthor::Header=>AnchorSourceKind::Header,
                MapPairSourceAuthor::Tree=>AnchorSourceKind::Tree};
            if imports.insert(import.physical_wire(),kind).is_some_and(|old|old!=kind) {
                return Err("v3 conflicting typed imported source".into());
            }
        }
        let view=Self{bundle,binding:binding.clone(),cells,imports};view.check_partition()?;Ok(view)
    }
    fn check_partition(&self)->Result<(),String> {
        if self.binding.owner()!=ANCHOR_OWNER||self.cells.len()!=16384 {
            return Err("v3 complete typed source owner/partition".into());
        }
        for (index,cell) in self.cells.iter().enumerate() {
            let context=index/8192;let offset=index%8192;
            let author=match offset {0..=5756=>AnchorCellAuthor::Map(context),
                5757..=7804=>AnchorCellAuthor::ScoreAnchor(context),
                _=>AnchorCellAuthor::Slack(context)};
            if cell.wire!=ANCHOR_OWNER*WIDTH+671744+index||cell.author!=author
                ||matches!(author,AnchorCellAuthor::Slack(_))&&cell.value {
                return Err("v3 typed source wire/author/context/value partition".into());
            }
        }
        Ok(())
    }
    fn cell(&self,wire:usize)->Option<AnchorCell> {
        wire.checked_sub(ANCHOR_OWNER*WIDTH+671744)
            .and_then(|index|self.cells.get(index)).copied()
    }
}

fn anchor_packed_bit(bytes:&[u8],wire:usize)->Result<bool,String> {
    let local=wire.checked_sub(ANCHOR_OWNER*WIDTH).filter(|local|*local<WIDTH)
        .ok_or("v3 local packed source owner")?;
    if bytes.len()!=WIDTH/8 {return Err("v3 packed source width".into());}
    Ok((bytes[local/8]>>(local%8))&1!=0)
}
fn anchor_resolve(operand:AnchorActiveOperand,source:&AnchorSourceView<'_>,bytes:&[u8],
    header:Option<&NativeHeaderSourceLease>)->Result<AnchorRead,String> {
    let source_owner=operand.wire/WIDTH;
    let expected=if operand.relation==AnchorRelation::Ordinary(Relation::DaaLane(2))
        &&[ANCHOR_OWNER-1,ANCHOR_OWNER-2].contains(&source_owner)
        &&(TYPED_WORK_START..TYPED_WORK_START+TYPED_WORK_BITS).contains(&(operand.wire%WIDTH)) {
        AnchorSourceKind::WorkD
    }else{source.imports.get(&operand.wire).copied().unwrap_or_else(||
        if source_owner==ANCHOR_OWNER-1&&(987450..987674).contains(&(operand.wire%WIDTH)) {
            AnchorSourceKind::WorkUpper
        }else{AnchorSourceKind::Unqualified})};
    if source_owner!=ANCHOR_OWNER {
        return Ok(AnchorRead::OpenForeign{operand,source_owner,expected});
    }
    if let Some(cell)=source.cell(operand.wire) {
        if anchor_packed_bit(bytes,operand.wire)?!=cell.value {
            return Err("v3 typed Bank53 read/final packed bit".into());
        }
        return Ok(AnchorRead::Bank53{operand,author:cell.author,value:cell.value});
    }
    if let Some(header)=header {
        if let Some(value)=header.read_header_bit(&source.binding,operand.wire)? {
            if anchor_packed_bit(bytes,operand.wire)?!=value {
                return Err("v3 HEADER read/final packed bit".into());
            }
            return Ok(AnchorRead::Header{operand,value});
        }
    }
    let local=operand.wire%WIDTH;
    let (domain,expected)=if BANKS.iter().any(|&(start,end)|(start..end).contains(&local)) {
        (AnchorLocalDomain::Daa,AnchorSourceKind::Daa)
    }else if expected==AnchorSourceKind::Tree {(AnchorLocalDomain::Tree,expected)}
    else {(AnchorLocalDomain::Unqualified,expected)};
    Ok(AnchorRead::OpenLocal{operand,domain,expected})
}
fn check_anchor_projection(batch:&AnchorBatch<'_>,source:&AnchorSourceView<'_>,
    owner:usize,class:OwnerClass,bytes:&[u8],header:Option<&NativeHeaderSourceLease>,
    reads:&[AnchorRead])->Result<(),String> {
    if owner!=ANCHOR_OWNER||class!=OwnerClass::Carry||batch.owner()!=owner||batch.class()!=class
        ||batch.layout!=AnchorLayout::digest()||batch.source!=source.binding
        ||!std::ptr::eq(batch.bundle,source.bundle)||bytes.len()!=WIDTH/8 {
        return Err("v3 read exact owner/class/layout/binding/bundle".into());
    }
    source.check_partition()?;
    if let Some(header)=header {header.check_binding(&source.binding)?;header.check_author()?;}
    // Final physical equality covers the entire partition, even unread cells.
    for cell in &source.cells {
        if anchor_packed_bit(bytes,cell.wire)?!=cell.value {
            return Err("v3 complete typed source/final packed partition".into());
        }
        if let Some(header)=header {
            if header.read_header_bit(&source.binding,cell.wire)?.is_some() {
                return Err("v3 Bank53 cannot retain HEADER authorship".into());
            }
        }
    }
    let mut actual=reads.iter();
    for operand in batch.active_operands() {
        if actual.next()!=Some(&anchor_resolve(operand,source,bytes,header)?) {
            return Err("v3 exact active read occurrence/order/side/author/value".into());
        }
    }
    if actual.next().is_some(){return Err("v3 extra active read occurrence".into());}
    Ok(())
}
fn project_anchor_reads(batch:&AnchorBatch<'_>,source:&AnchorSourceView<'_>,bytes:&[u8],
    header:Option<&NativeHeaderSourceLease>)->Result<Vec<AnchorRead>,String> {
    let reads=batch.active_operands().map(|operand|anchor_resolve(operand,source,bytes,header))
        .collect::<Result<Vec<_>,_>>()?;
    check_anchor_projection(batch,source,ANCHOR_OWNER,OwnerClass::Carry,bytes,header,&reads)?;
    Ok(reads)
}
fn commit_anchor_projection(registry:&mut AnchorRowRegistry,batch:&AnchorBatch<'_>,
    source:&AnchorSourceView<'_>,owner:usize,class:OwnerClass,bytes:&[u8],
    header:Option<&NativeHeaderSourceLease>,reads:&[AnchorRead])->Result<(),String> {
    check_anchor_projection(batch,source,owner,class,bytes,header,reads)?;
    registry.commit(batch)
}

/// Native custody is retained for the full lifetime of this opaque admission.
/// No generic row, synthetic custody or caller-authored read list enters here.
pub(super) struct NativeAnchorReadStage<'a,'b> {
    packed:&'a NativeFirstAnchorPacked<'b>,batch:AnchorBatch<'b>,
    reads:Vec<AnchorRead>,registry:AnchorRowRegistry,
}
impl NativeAnchorReadStage<'_,'_> {
    pub(super) fn batch(&self)->&AnchorBatch<'_> {&self.batch}
    pub(super) fn reads(&self)->impl ExactSizeIterator<Item=&AnchorRead> {self.reads.iter()}
    pub(super) fn registry(&self)->&AnchorRowRegistry {&self.registry}
    pub(super) fn packed(&self)->&NativePackedRow {self.packed.row()}
}

/// The roster and physical Tree permission are checked once against this exact
/// immutable plan. Repeated joins still validate each batch and producer lease.
pub(super) struct TypedAuthorJoinPlan<'p> {
    plan:&'p crate::work_tree_history_plan::WorkTreeHistoryPlan,
    mature_class:OwnerClass,carry_class:OwnerClass,tree_mask:Vec<bool>,
}
impl<'p> TypedAuthorJoinPlan<'p> {
    pub(super) fn new(
        plan:&'p crate::work_tree_history_plan::WorkTreeHistoryPlan,
    )->Result<Self,String> {
        let roster=DaaHistoryRoster::compile(plan)?;
        let mature_class=roster.owner_class(TYPED_MATURE_EIP_OWNER as u64)?;
        let carry_class=roster.owner_class(TYPED_CARRY_OWNER as u64)?;
        if mature_class!=OwnerClass::Mature(crate::daa_integer::Epoch::Eip)
            || carry_class!=OwnerClass::Carry {
            return Err("typed author join source schedule".into());
        }
        // The admitted Work Tree replacement template is owner-independent.
        // Check that equality before sharing one mask across Carry's two sources.
        let tree_mask=plan.physical_assignment_replacement_mask(
            TYPED_CARRY_SOURCES[0] as u64)?;
        let second=plan.physical_assignment_replacement_mask(
            TYPED_CARRY_SOURCES[1] as u64)?;
        if tree_mask.len()!=WIDTH || second!=tree_mask {
            return Err("typed author Tree source masks differ or have wrong width".into());
        }
        Ok(Self{plan,mature_class,carry_class,tree_mask})
    }
}
impl Batch {
    pub(super) fn require_owner_parent(&self,
        plan:&crate::work_tree_history_plan::WorkTreeHistoryPlan,owner:usize)
        ->Result<(),String> {
        if self.owner!=owner || self.class!=DaaHistoryRoster::compile(plan)?.owner_class(owner as u64)?
            || self.source!=HeaderSourceBinding::for_plan(plan,owner)? {
            return Err("ROW occurrence exact owner/parent/cut/layout".into());
        }
        Ok(())
    }
    pub(super) fn terms(&self)->impl ExactSizeIterator<Item=(Relation,&Term)> {
        self.terms.iter().map(|e|(e.relation,&e.term))
    }
    pub(super) fn active_operands(&self)->ActiveOperandIter<'_> {
        ActiveOperandIter{entries:self.terms.iter().enumerate(),pending_right:None}
    }
    /// Upgrade only the 864 actual Mature(Eip) DAA alias source reads. Each
    /// producer lease is bound to its own HEADER row; all other open reads
    /// retain their previous status. No owner-X publication follows.
    pub(super) fn join_mature_serializer_author_reads<'a>(
        &'a self,context:&TypedAuthorJoinPlan<'_>,
        local:&NativeTypedAuthorLease<'_>,
        foreign:&[&NativeTypedAuthorLease<'_>],
    )->Result<NativeTypedAuthorReadStage<'a>,String> {
        if self.owner!=TYPED_MATURE_EIP_OWNER || foreign.len()!=TYPED_MATURE_SERIALIZER_SOURCES.len() {
            return Err("typed Mature serializer exact owner/source count".into());
        }
        if self.terms.iter().filter(|entry|entry.relation==Relation::DaaLane(1)).count()!=896 {
            return Err("typed Mature serializer exact alias term count".into());
        }
        let mut stage=self.join_typed_author_reads(context,&[local])?;
        for (lease,&owner) in foreign.iter().zip(TYPED_MATURE_SERIALIZER_SOURCES.iter()) {
            if lease.source_owner()!=owner {
                return Err("typed Mature serializer source order/owner".into());
            }
            lease.check_binding(context.plan,&self.source)?;
        }
        let layout=context.plan.header_boundary().mature_layout(crate::daa_integer::Epoch::Eip);
        let mut aliases=Vec::with_capacity(896);
        let count=layout.visit_alias_terms(self.owner as u64,|term|{aliases.push(term);Ok(())})?;
        if count!=896 || aliases.len()!=896 {
            return Err("typed Mature serializer exact alias census".into());
        }
        let mut lane=self.terms.iter().enumerate()
            .filter(|(_,entry)|entry.relation==Relation::DaaLane(1));
        let mut expected=Vec::with_capacity(864);
        let mut seen=BTreeSet::new();
        for alias in aliases {
            let (occurrence,entry)=lane.next().ok_or("typed Mature serializer missing alias occurrence")?;
            if alias.row>>10!=self.owner
                || entry.term!=self.layout_for_alias(alias)? {
                return Err("typed Mature serializer alias occurrence/order/side/branch".into());
            }
            let gate=&entry.term.gate;
            if gate.left/WIDTH!=self.owner {
                if gate.c0!=Fr::zero() || gate.c1!=Fr::from(1u64)
                    || gate.c2!=-Fr::from(1u64) || gate.c3!=Fr::zero()
                    || gate.right/WIDTH!=self.owner
                    || !TYPED_MATURE_SERIALIZER_SOURCES.contains(&(gate.left/WIDTH))
                    || !seen.insert(gate.left) {
                    return Err("typed Mature serializer foreign alias relation/author geometry".into());
                }
                expected.push((occurrence,gate.left));
            }
        }
        if lane.next().is_some() || expected.len()!=864 || seen.len()!=864 {
            return Err("typed Mature serializer missing/duplicate/surplus alias".into());
        }
        let mut wanted=expected.into_iter().peekable();
        for read in &mut stage.reads {
            let NativeTypedAuthorRead::Open{operand}=*read else {continue};
            if wanted.peek().is_some_and(|(ordinal,_)|*ordinal==operand.occurrence) {
                let (_,wire)=wanted.next().ok_or("typed Mature serializer occurrence underflow")?;
                if operand.side!=OperandSide::Left || operand.relation!=Relation::DaaLane(1)
                    || operand.wire!=wire || !operand.c1_active
                    || operand.c2_active || operand.c3_active {
                    return Err("typed Mature serializer active occurrence/side/branch".into());
                }
                let owner=wire/WIDTH;
                let index=TYPED_MATURE_SERIALIZER_SOURCES.iter().position(|&at|at==owner)
                    .ok_or("typed Mature serializer source owner")?;
                let cell=foreign[index].read_cell(&self.source,wire)?
                    .ok_or("typed Mature serializer missing producer cell")?;
                *read=admit_mature_serializer_occurrence(operand,cell)?;
            }
        }
        if wanted.next().is_some() {
            return Err("typed Mature serializer missing active occurrence".into());
        }
        checked_typed_author_stage(self,stage.reads)
    }
    fn layout_for_alias(&self,alias:Term)->Result<Term,String> {
        let row=self.owner.checked_mul(ROWS)
            .and_then(|base|base.checked_add((1<<17)+(alias.row&1023)))
            .ok_or("typed Mature serializer placed alias ROW overflow")?;
        Layout::fixed().place(self.class,Relation::DaaLane(1),self.owner,
            Term{row,gate:alias.gate})
    }
    /// Join only source-owned Mature(Eip) local cells or Carry's two foreign
    /// Tree Work endpoints to the immutable canonical occurrence stream.
    /// Every other read remains `Open`; no X witness or residual is emitted.
    pub(super) fn join_typed_author_reads<'a>(
        &'a self,context:&TypedAuthorJoinPlan<'_>,
        leases:&[&NativeTypedAuthorLease<'_>],
    )->Result<NativeTypedAuthorReadStage<'a>,String> {
        let plan=context.plan;
        let expected_class=match self.owner {
            TYPED_MATURE_EIP_OWNER=>context.mature_class,
            TYPED_CARRY_OWNER=>context.carry_class,
            _=>return Err("typed author join unsupported owner; reads remain open".into()),
        };
        if self.class!=expected_class
            || self.source!=HeaderSourceBinding::for_plan(plan,self.owner)? {
            return Err("typed author ROW occurrence exact owner/parent/cut/layout".into());
        }
        let source_owners:&[usize]=match (self.owner,self.class) {
            (TYPED_MATURE_EIP_OWNER,OwnerClass::Mature(crate::daa_integer::Epoch::Eip))=>
                &[TYPED_MATURE_EIP_OWNER],
            (TYPED_CARRY_OWNER,OwnerClass::Carry)=>&TYPED_CARRY_SOURCES,
            _=>return Err("typed author join unsupported owner/class; reads remain open".into()),
        };
        if leases.len()!=source_owners.len() {
            return Err("typed author join missing/duplicate source lease".into());
        }
        for (lease,&source_owner) in leases.iter().zip(source_owners) {
            if lease.source_owner()!=source_owner {
                return Err("typed author join source lease order/owner".into());
            }
            lease.check_binding(plan,&self.source)?;
        }
        // Decide all ROW occurrences from the plan, roster, BANKS and Work
        // geometry before consulting any producer-supplied value or author.
        let mut prepared=Vec::new();
        let mut foreign_seen=BTreeSet::new();
        for operand in self.active_operands() {
            let physical_owner=operand.wire/WIDTH;
            let local=operand.wire%WIDTH;
            let selected=if self.owner==TYPED_MATURE_EIP_OWNER
                && physical_owner==self.owner {
                let daa=BANKS.iter().any(|&(lo,hi)|(lo..hi).contains(&local));
                if daa && context.tree_mask[local] {
                    return Err("typed Mature(Eip) Tree/DAA physical author overlap".into());
                }
                let author=if daa {NativeTypedAuthor::Daa}
                    else if context.tree_mask[local] {NativeTypedAuthor::Tree}
                    else {NativeTypedAuthor::Header};
                Some((0,author))
            } else if self.owner==TYPED_CARRY_OWNER && physical_owner!=self.owner {
                if operand.relation!=Relation::DaaLane(2)
                    || operand.side!=OperandSide::Left
                    || operand.row!=self.owner*ROWS+262_144
                    || !operand.c1_active || operand.c2_active || operand.c3_active
                    || !(TYPED_WORK_START..TYPED_WORK_START+TYPED_WORK_BITS).contains(&local) {
                    return Err("typed Carry foreign ROW relation/row/side/wire/flags".into());
                }
                let entry=self.terms.get(operand.occurrence)
                    .ok_or("typed Carry foreign occurrence outside batch")?;
                let gate=&entry.term.gate;
                if entry.relation!=operand.relation || entry.term.row!=operand.row
                    || gate.left!=operand.wire || gate.right!=0 || !gate.c0.is_zero()
                    || gate.c1.is_zero() || !gate.c2.is_zero() || !gate.c3.is_zero() {
                    return Err("typed Carry foreign EqualParent gate identity".into());
                }
                let index=source_owners.iter().position(|&owner|owner==physical_owner)
                    .ok_or("typed Carry foreign source outside adjacent pair")?;
                if !context.tree_mask[local] || !foreign_seen.insert(operand.wire) {
                    return Err("typed Carry foreign non-Tree/duplicate Work occurrence".into());
                }
                Some((index,NativeTypedAuthor::Tree))
            } else {None};
            prepared.push(selected);
        }
        if self.owner==TYPED_CARRY_OWNER {
            if foreign_seen.len()!=2*TYPED_WORK_BITS
                || TYPED_CARRY_SOURCES.iter().any(|&owner|
                    (0..TYPED_WORK_BITS).any(|bit|
                        !foreign_seen.contains(&(owner*WIDTH+TYPED_WORK_START+bit)))) {
                return Err("typed Carry foreign Work missing occurrence".into());
            }
        }
        let mut reads=Vec::with_capacity(prepared.len());
        for (operand,selected) in self.active_operands().zip(prepared.into_iter()) {
            match selected {
                Some((index,expected_author))=>{
                    let cell=leases[index].read_cell(&self.source,operand.wire)?
                        .ok_or("typed author active cell missing producer")?;
                    if cell.wire()!=operand.wire || cell.author()!=expected_author {
                        return Err("typed author active cell wrong physical writer".into());
                    }
                    reads.push(NativeTypedAuthorRead::Known{operand,cell});
                }
                None=>reads.push(NativeTypedAuthorRead::Open{operand}),
            }
        }
        checked_typed_author_stage(self,reads)
    }
    pub(super) fn visit_active_operands(
        &self,mut sink:impl FnMut(ActiveOperand)->Result<(),String>,
    )->Result<usize,String> {
        let mut count=0usize;
        for operand in self.active_operands() {
            count=count.checked_add(1).ok_or("active operand count overflow")?;
            sink(operand)?;
        }
        Ok(count)
    }
    fn resolve_verified(&self,lease:&NativeHeaderSourceLease,operand:ActiveOperand)
        ->Result<SourceRead,String> {
        let base=self.owner.checked_mul(WIDTH).ok_or("HEADER read owner overflow")?;
        if !(base..base+WIDTH).contains(&operand.wire) {
            return Ok(SourceRead::Unresolved{operand,reason:UnresolvedRead::ForeignOwner});
        }
        match lease.read_header_bit(&self.source,operand.wire)? {
            Some(value)=>Ok(SourceRead::Header{operand,value}),
            None=>Ok(SourceRead::Unresolved{operand,reason:UnresolvedRead::UnqualifiedLocal}),
        }
    }
    /// Resolve only local reads backed by the exact native HEADER assignment.
    /// Foreign and other-author cells remain typed open obligations.
    pub(super) fn visit_source_reads(&self,lease:&NativeHeaderSourceLease,
        mut sink:impl FnMut(SourceRead)->Result<(),String>)->Result<usize,String> {
        lease.check_binding(&self.source)?;
        lease.check_author()?;
        let mut count=0usize;
        for operand in self.active_operands() {
            let read=self.resolve_verified(lease,operand)?;
            count=count.checked_add(1).ok_or("HEADER source read count overflow")?;
            sink(read)?;
        }
        Ok(count)
    }
    /// One qualified local HEADER value, without assigning any other wire.
    pub(super) fn header_bit(&self,lease:&NativeHeaderSourceLease,wire:usize)
        ->Result<Option<bool>,String> {
        lease.check_binding(&self.source)?;
        lease.check_author()?;
        let base=self.owner.checked_mul(WIDTH).ok_or("HEADER read owner overflow")?;
        if !(base..base+WIDTH).contains(&wire) {return Ok(None);}
        lease.read_header_bit(&self.source,wire)
    }
    pub(super) fn resolve_one(&self,occurrence:usize,side:OperandSide,
        lease:&NativeHeaderSourceLease)->Result<SourceRead,String> {
        lease.check_binding(&self.source)?;
        lease.check_author()?;
        let operand=self.active_operands().find(|op|op.occurrence==occurrence&&op.side==side)
            .ok_or("inactive or missing ROW operand occurrence")?;
        self.resolve_verified(lease,operand)
    }
    fn checked_daa_reads(&self,lease:&NativeDaaSourceLease<'_,'_>)->Result<Vec<DaaRead>,String> {
        lease.check_binding(&self.source)?;
        lease.check_author()?;
        let base=self.owner.checked_mul(WIDTH).ok_or("DAA active-read owner overflow")?;
        let mut reads=Vec::new();
        for operand in self.active_operands() {
            let Some(local)=operand.wire.checked_sub(base).filter(|local|*local<WIDTH) else {continue;};
            if !BANKS.iter().any(|&(start,end)|(start..end).contains(&local)){continue;}
            let value=lease.read_daa_bit(&self.source,operand.wire)?
                .ok_or("DAA active bank read lacks source author")?;
            reads.push(DaaRead{operand,value});
        }
        Ok(reads)
    }
    /// Reuse an already checked canonical batch for isolated read-boundary
    /// checks. Every call checks both leases before reading any value.
    pub(super) fn checked_native_reads(&self,header:&NativeHeaderSourceLease,
        daa:&NativeDaaSourceLease<'_,'_>)->Result<Vec<NativeRead>,String> {
        header.check_binding(&self.source)?;
        daa.check_binding(&self.source)?;
        header.check_author()?;
        daa.check_author()?;

        let base=self.owner.checked_mul(WIDTH).ok_or("native read owner overflow")?;
        let mut reads=Vec::new();
        for operand in self.active_operands() {
            let Some(local)=operand.wire.checked_sub(base).filter(|local|*local<WIDTH) else {
                reads.push(NativeRead::Unresolved{operand,reason:UnresolvedRead::ForeignOwner});
                continue;
            };
            if BANKS.iter().any(|&(start,end)|(start..end).contains(&local)) {
                let value=daa.read_daa_bit(&self.source,operand.wire)?
                    .ok_or("DAA active bank read lacks source author")?;
                if header.read_header_bit(&self.source,operand.wire)?.is_some() {
                    return Err("DAA active bank read has concurrent HEADER claim".into());
                }
                reads.push(NativeRead::Daa{operand,value});
            } else {
                match header.read_header_bit(&self.source,operand.wire)? {
                    Some(value)=>reads.push(NativeRead::Header{operand,value}),
                    None=>reads.push(NativeRead::Unresolved{operand,reason:UnresolvedRead::UnqualifiedLocal}),
                }
            }
        }
        debug_assert_eq!(reads.len(),self.active_operands().count());
        Ok(reads)
    }
    #[cfg(test)]
    fn source_binding_for_test(&self)->HeaderSourceBinding {self.source.clone()}
    /// Partial producer declarations, not leases inferred from gate reads.
    /// HEADER domains and complete X writer qualification remain out of scope.
    pub(super) fn declared_x_domains(&self)->Vec<DeclaredXDomain> {
        let mut out=Vec::new();let base=self.owner*WIDTH;
        // Inactive-zero constraints do not make write_retarget a producer.
        if matches!(self.class,OwnerClass::M1|OwnerClass::Short(_)|OwnerClass::Mature(_)) {
            for(start,end)in BANKS{out.push(DeclaredXDomain{producer:Producer::Daa,start:base+start,end:base+end});}
        }
        for relation in self.relations[5..].iter().flatten() {
            if let Relation::Scheduled(writer)=*relation {
                let(start,len)=match writer {Writer::Max{context,..}=>([999424,1000097][context],673),
                    Writer::Cap{context,..}=>([1000770,1002818][context],2048)};
                out.push(DeclaredXDomain{producer:Producer::Scheduled(writer),start:base+start,end:base+start+len});
            }
        }out
    }
    /// Add Carry and FullZero DAA domains only when their exact native producer
    /// supplied the matching four-bank author. Retarget declarations stay on
    /// their existing path and still require their retarget lease.
    pub(super) fn declared_x_domains_with_daa_source(
        &self,
        lease:&NativeDaaSourceLease<'_,'_>,
    )->Result<Vec<DeclaredXDomain>,String> {
        if self.source.owner()!=self.owner {
            return Err("DAA source domain owner/binding mismatch".into());
        }
        lease.check_binding(&self.source)?;
        lease.check_author()?;
        let mut out=self.declared_x_domains();
        if self.class==OwnerClass::Carry {
            lease.check_carry_zero_source(&self.source)?;
            let base=self.owner.checked_mul(WIDTH).ok_or("Carry DAA domain owner overflow")?;
            for(start,end)in BANKS {
                out.push(DeclaredXDomain{producer:Producer::Daa,start:base+start,end:base+end});
            }
        } else if matches!(self.class,OwnerClass::Genesis|OwnerClass::Initial|OwnerClass::FixedV2
            |OwnerClass::Singleton|OwnerClass::Padding) {
            lease.check_full_zero_source(&self.source)?;
            let base=self.owner.checked_mul(WIDTH).ok_or("FullZero DAA domain owner overflow")?;
            for(start,end)in BANKS {
                out.push(DeclaredXDomain{producer:Producer::Daa,start:base+start,end:base+end});
            }
        }
        Ok(out)
    }
}

#[cfg(test)]
mod c520_full_zero_daa_domain_consumer_tests {
    use super::*;

    fn batch(owner:usize,class:OwnerClass,source:HeaderSourceBinding)->Batch {
        Batch{owner,class,layout:Layout::fixed().digest(),source,terms:Vec::new(),
            expected:[0;RELATIONS],relations:[None;RELATIONS]}
    }

    #[test]
    fn full_zero_classes_declare_exact_four_daa_domains() {
        // The small producer is only a lifetime anchor for the explicit
        // cfg(test) synthetic lease. These root/total/profile/cut bindings and
        // class overrides are test data, not H21 production authority.
        let input=crate::packed_owner_assembly_tests::legacy_prefix_for_test();
        let plan=crate::packed_owner_assembly_tests::legacy_assembly_plan_for_test();
        let producer=crate::packed_owner_assembly::NativeOwnerProducer::new_for_history(plan,input).unwrap();
        let cases=[(0,OwnerClass::Genesis),(1,OwnerClass::Initial),
            (417_791,OwnerClass::FixedV2),(417_792,OwnerClass::FixedV2),
            (1_024,OwnerClass::Singleton),(1_827_840,OwnerClass::Padding)];

        for (owner,class) in cases {
            let binding=HeaderSourceBinding::diagnostic_for_test(owner);
            let lease=NativeDaaSourceLease::synthetic_full_zero_for_test(
                &producer,binding.clone(),class);
            let domains=batch(owner,class,binding).declared_x_domains_with_daa_source(&lease).unwrap();
            let actual=domains.iter().filter(|domain|domain.producer==Producer::Daa)
                .map(|domain|(domain.start,domain.end)).collect::<Vec<_>>();
            let base=owner*WIDTH;
            let expected=BANKS.iter().map(|&(start,end)|(base+start,base+end))
                .collect::<Vec<_>>();
            assert_eq!(actual,expected,"FullZero DAA intervals owner{owner}/{class:?}");
            assert_eq!(domains.len(),4,"no other domain is added owner{owner}/{class:?}");
        }
    }

    #[test]
    fn full_zero_consumer_rejects_wrong_class_payload_owner_author_and_binding() {
        // This N=3073 producer is only a borrow anchor; cfg(test) constructors
        // mint synthetic author leases. No fixture below asserts native H21.
        let input=crate::packed_owner_assembly_tests::legacy_prefix_for_test();
        let plan=crate::packed_owner_assembly_tests::legacy_assembly_plan_for_test();
        let producer=crate::packed_owner_assembly::NativeOwnerProducer::new_for_history(plan,input).unwrap();

        // Carry and M1 retain their distinct CarryZero/retarget payloads.
        for (owner,class) in [(2,OwnerClass::Carry),(2_048,OwnerClass::M1)] {
            let binding=HeaderSourceBinding::diagnostic_for_test(owner);
            let wrong_payload=NativeDaaSourceLease::synthetic_full_zero_for_test(
                &producer,binding.clone(),class);
            assert!(batch(owner,class,binding).declared_x_domains_with_daa_source(&wrong_payload).is_err(),
                "FullZero must not authorize {class:?}");
        }

        let owner=0;
        let binding=HeaderSourceBinding::diagnostic_for_test(owner);
        let valid=NativeDaaSourceLease::synthetic_full_zero_for_test(
            &producer,binding.clone(),OwnerClass::Genesis);

        let wrong_owner=batch(owner+1,OwnerClass::Genesis,binding.clone());
        assert!(wrong_owner.declared_x_domains_with_daa_source(&valid).is_err(),
            "Batch owner must match its source binding");

        let mut wrong_author=NativeDaaSourceLease::synthetic_full_zero_for_test(
            &producer,binding.clone(),OwnerClass::Genesis);
        wrong_author.wrong_author_mutant_for_test();
        assert!(batch(owner,OwnerClass::Genesis,binding.clone())
            .declared_x_domains_with_daa_source(&wrong_author).is_err());

        let wrong_binding=binding.mutated_field_for_test(3);
        assert!(batch(owner,OwnerClass::Genesis,wrong_binding)
            .declared_x_domains_with_daa_source(&valid).is_err(),
            "lease must match the complete source binding, including cut");
    }
}

#[cfg(test)]
mod c397_mature_serializer_author_tests {
    use super::*;

    #[test]
    fn no_frame_exact_foreign_alias_occurrences_and_author_mutants() {
        // This is checker sensitivity only. The synthetic zero leases are not
        // producer authority; the ignored H21 test mints the real leases.
        let (plan,resolved)=crate::packed_owner_assembly::
            c377_mature_eip_source_matrix_tests::resolved_fixture();
        let binding=HeaderSourceBinding::for_plan(&plan,TYPED_MATURE_EIP_OWNER).unwrap();
        let local=resolved.typed_author_lease(&binding).unwrap();
        let roster=DaaHistoryRoster::compile(&plan).unwrap();
        let native=crate::daa_header_window::for_child_height(
            (TYPED_MATURE_EIP_OWNER+1) as u32).unwrap();
        assert_eq!(native.action(),crate::daa_header_window::Action::Retarget(
            crate::daa_integer::Epoch::Eip));
        assert_eq!(native.sample_heights().len(),TYPED_MATURE_SERIALIZER_SOURCES.len());
        for (&height,&owner) in native.sample_heights().iter()
            .zip(TYPED_MATURE_SERIALIZER_SOURCES.iter()) {
            assert_eq!(height as usize,owner+1);
            assert_eq!(roster.owner_class(owner as u64).unwrap(),OwnerClass::Carry);
        }
        let scheduled=Scheduled::eligible08();
        let row_plan=RowPlan::new(&roster,&scheduled).unwrap();
        let batch=row_plan.stage_owner(TYPED_MATURE_EIP_OWNER).unwrap();
        let context=TypedAuthorJoinPlan::new(&plan).unwrap();
        let leases=TYPED_MATURE_SERIALIZER_SOURCES.iter().map(|&owner|
            NativeTypedAuthorLease::synthetic_mature_serializer_for_test(
                &plan,binding.clone(),owner)).collect::<Vec<_>>();
        let refs=leases.iter().collect::<Vec<_>>();
        let stage=batch.join_mature_serializer_author_reads(&context,&local,&refs).unwrap();
        assert_eq!(stage.reads().count(),1_289_184);
        assert_eq!(stage.reads().filter(|read|matches!(read,
            NativeTypedAuthorRead::Known{operand,..} if operand.wire/WIDTH!=TYPED_MATURE_EIP_OWNER))
            .count(),864);
        assert_eq!(stage.reads().filter(|read|matches!(read,NativeTypedAuthorRead::Open{..}))
            .count(),0);
        let (operand,cell)=stage.reads().find_map(|read|match *read {
            NativeTypedAuthorRead::Known{operand,cell}
                if operand.wire/WIDTH!=TYPED_MATURE_EIP_OWNER=>Some((operand,cell)),
            _=>None,
        }).unwrap();
        assert!(!cell.value(),"synthetic equal-zero author discriminant");
        let wrong=cell.with_author_for_test(NativeTypedAuthor::Daa);
        assert_eq!((wrong.wire(),wrong.value()),(cell.wire(),cell.value()));
        assert!(admit_mature_serializer_occurrence(operand,wrong)
            .err().unwrap().contains("wrong physical author at occurrence"));
        assert!(mutant_skip_mature_serializer_author_for_test(operand,wrong).is_ok(),
            "removing only occurrence author comparison admits equal-zero retag");

        let mut wrong=leases.clone();wrong[0].wrong_author_for_test();
        let wrong_refs=wrong.iter().collect::<Vec<_>>();
        assert!(batch.join_mature_serializer_author_reads(&context,&local,&wrong_refs)
            .err().unwrap().contains("destination/author"));
        let mut wrong=leases.clone();wrong[0].wrong_parent_for_test();
        let wrong_refs=wrong.iter().collect::<Vec<_>>();
        assert!(batch.join_mature_serializer_author_reads(&context,&local,&wrong_refs).is_err());
        let mut wrong=leases.clone();wrong[0].missing_cell_for_test();
        let wrong_refs=wrong.iter().collect::<Vec<_>>();
        assert!(batch.join_mature_serializer_author_reads(&context,&local,&wrong_refs).is_err());
        let mut wrong=leases.clone();wrong[0].duplicate_cell_for_test();
        let wrong_refs=wrong.iter().collect::<Vec<_>>();
        assert!(batch.join_mature_serializer_author_reads(&context,&local,&wrong_refs).is_err());

        let first=batch.terms.iter().position(|entry|entry.relation==Relation::DaaLane(1))
            .unwrap();
        let mut missing=batch.clone();missing.terms.remove(first);
        assert!(missing.join_mature_serializer_author_reads(&context,&local,&refs)
            .err().unwrap().contains("exact alias term count"));
        let mut duplicate=batch.clone();duplicate.terms.insert(first,
            duplicate.terms[first].clone());
        assert!(duplicate.join_mature_serializer_author_reads(&context,&local,&refs)
            .err().unwrap().contains("exact alias term count"));
        let mut wrong_side=batch.clone();
        let gate=&mut wrong_side.terms[first].term.gate;
        std::mem::swap(&mut gate.left,&mut gate.right);
        std::mem::swap(&mut gate.c1,&mut gate.c2);
        assert!(wrong_side.join_mature_serializer_author_reads(&context,&local,&refs)
            .err().unwrap().contains("alias occurrence/order/side/branch"));
    }
}

pub(super) struct RowPlan<'r,'p> {roster:&'r DaaHistoryRoster<'p>,scheduled:&'r Scheduled,header:Merge<'r,'p>,layout:Layout}
impl<'r,'p> RowPlan<'r,'p> {
    pub(super) fn new(roster:&'r DaaHistoryRoster<'p>,scheduled:&'r Scheduled)->Result<Self,String> {
        if scheduled.descriptor()!=crate::bank53_map::CutDescriptor::eligible08() {
            return Err("HEADER source ROW plan requires exact Eligible08 cut".into());
        }
        Ok(Self{roster,scheduled,header:Merge::new(roster,scheduled)?,layout:Layout::fixed()})
    }
    /// Apply the same physical placement used by `stage_owner` to one source
    /// DAA term. This narrow accessor supports source-to-ledger comparison; it
    /// does not admit terms into a batch or alter the registry.
    pub(super) fn place_daa_source_term(&self,owner:usize,term:Term)->Result<(Relation,Term),String> {
        let q=term.row.checked_sub(owner*ROWS).filter(|q|*q<ROWS).ok_or("DAA source owner")?;
        let relation=Relation::DaaLane(q>>17);
        let class=self.roster.owner_class(owner as u64)?;
        Ok((relation,self.layout.place(class,relation,owner,term)?))
    }
    // Each producer is visited once per call. Counts come from its actual
    // complete source interface, not a caller-supplied fixture or row mask.
    fn visit_sources(&self,owner:usize,mut sink:impl FnMut(Relation,Term)->Result<(),String>)
        ->Result<[usize;RELATIONS],String> {
        let header=self.header.header_terms(owner)?;let mut expected=[0;RELATIONS];
        expected[0]=header.terms.len();for term in header.terms{sink(Relation::Header,term)?;}
        let daa=self.roster.visit_owner_terms(owner as u64,|term| {
            let q=term.row.checked_sub(owner*ROWS).filter(|q|*q<ROWS).ok_or("DAA source owner")?;
            sink(Relation::DaaLane(q>>17),term)
        })?;
        expected[1..5].copy_from_slice(&daa.lanes);
        let scheduled=self.scheduled.visit_owner(owner,|writer,term|sink(Relation::Scheduled(writer),term))?;
        expected[5..7].copy_from_slice(&scheduled.max);expected[7..9].copy_from_slice(&scheduled.cap);Ok(expected)
    }
    pub(super) fn stage_owner(&self,owner:usize)->Result<Batch,String> {
        let class=self.roster.owner_class(owner as u64)?;let mut terms=Vec::new();
        let mut actual=[0;RELATIONS];let mut relations=[None;RELATIONS];
        let expected=self.visit_sources(owner,|relation,term| {
            let slot=relation.slot(owner)?;
            if relations[slot].is_some_and(|r|r!=relation){return Err("source relation identity changed".into());}
            relations[slot]=Some(relation);actual[slot]+=1;
            if terms.len()>=TERM_LIMIT{return Err("ROW stage per-owner term bound".into());}
            terms.push(Entry{relation,term:self.layout.place(class,relation,owner,term)?});Ok(())
        })?;
        if expected!=actual{return Err("source emission multiplicity".into());}
        let source=HeaderSourceBinding::for_plan(self.roster.endpoint_parent(),owner)?;
        let batch=Batch{owner,class,layout:self.layout.digest(),source,terms,expected,relations};
        // No output is returned before the whole candidate has passed the
        // same atomic ownership checks used by the downstream registry.
        self.registry(owner)?.check(&batch)?;Ok(batch)
    }
    /// First-anchor structural ROW stage only. The borrowed source bundle and
    /// the ordinary batch keep their v1 source binding; v3 versions placement.
    pub(super) fn stage_owner_with_anchor<'a>(&self,owner:usize,
        bundle:&'a Eligible08MapSlackAnchorBundle,
    )->Result<AnchorBatch<'a>,String> {
        if owner!=ANCHOR_OWNER||self.roster.owner_class(owner as u64)?!=OwnerClass::Carry {
            return Err("v3 requires owner 417790/Carry".into());
        }
        let source=HeaderSourceBinding::for_plan(self.roster.endpoint_parent(),owner)?;
        let lists=anchor_source_lists(bundle,&source)?;
        let base=Arc::new(self.stage_owner(owner)?);
        // Rewalk the complete ordinary producers, including empty scheduled
        // slots, against the exact staged tuples before freezing the base.
        let mut ordinary=base.terms.iter();
        let expected=self.visit_sources(owner,|relation,term| {
            let staged=ordinary.next().ok_or("v3 ordinary source omitted term")?;
            if staged.relation!=relation
                ||staged.term!=Layout::fixed().place(OwnerClass::Carry,relation,owner,term)? {
                return Err("v3 ordinary source ordered tuple mismatch".into());
            }
            Ok(())
        })?;
        if ordinary.next().is_some()||expected!=base.expected||base.source!=source {
            return Err("v3 ordinary source census/binding".into());
        }
        if base.terms.len()+lists.iter().map(|terms|terms.len()).sum::<usize>()>TERM_LIMIT {
            return Err("v3 combined per-owner term bound".into());
        }
        let mut bank:[Vec<Term>;6]=std::array::from_fn(|_|Vec::new());
        for index in 0..6 {
            bank[index]=lists[index].iter().cloned().map(|term|AnchorLayout::place(index,term))
                .collect::<Result<Vec<_>,_>>()?;
        }
        let batch=AnchorBatch{expected_base:Arc::clone(&base),base,bundle,bank,
            bank_relations:std::array::from_fn(AnchorRelation::bank),source,
            class:OwnerClass::Carry,layout:AnchorLayout::digest()};
        self.registry_with_anchor(owner)?.check(&batch)?;
        Ok(batch)
    }
    pub(super) fn registry_with_anchor(&self,owner:usize)->Result<AnchorRowRegistry,String> {
        if owner!=ANCHOR_OWNER||self.roster.owner_class(owner as u64)?!=OwnerClass::Carry {
            return Err("v3 registry requires owner 417790/Carry".into());
        }
        Ok(AnchorRowRegistry{
            source:HeaderSourceBinding::for_plan(self.roster.endpoint_parent(),owner)?,
            committed:false,rows:vec![0;ROWS]})
    }
    /// The only native v3 read admission takes the specialized writer receipt.
    /// Its exact borrowed bundle supplies the structural and typed projections.
    pub(super) fn stage_owner_with_anchor_reads<'a,'b>(&self,owner:usize,
        packed:&'a NativeFirstAnchorPacked<'b>,header:Option<&NativeHeaderSourceLease>,
    )->Result<NativeAnchorReadStage<'a,'b>,String> {
        let binding=HeaderSourceBinding::for_plan(self.roster.endpoint_parent(),owner)?;
        if owner!=ANCHOR_OWNER||packed.binding()!=&binding {
            return Err("v3 native receipt exact plan/owner binding".into());
        }
        packed.row().require_header_source_binding(&binding,owner,OwnerClass::Carry)?;
        let batch=self.stage_owner_with_anchor(owner,packed.bundle())?;
        let source=AnchorSourceView::checked(packed.bundle(),packed.binding())?;
        let reads=project_anchor_reads(&batch,&source,packed.row().packed_bytes(),header)?;
        let mut registry=self.registry_with_anchor(owner)?;
        commit_anchor_projection(&mut registry,&batch,&source,packed.row().owner(),
            packed.row().class(),packed.row().packed_bytes(),header,&reads)?;
        Ok(NativeAnchorReadStage{packed,batch,reads,registry})
    }
    /// Admit only the checked Genesis Map pair. The source remains v1-bound;
    /// the separate v2 identity describes only the combined ROW placement.
    pub(super) fn stage_owner_with_map_pair(&self,owner:usize,lease:&Eligible08MapPairLease)
        ->Result<PairedMapBatch,String> {
        if owner!=0 {
            return Err("paired ROW gate requires owner 0/Genesis".into());
        }
        let class=self.roster.owner_class(owner as u64)?;
        if class!=OwnerClass::Genesis {
            return Err("paired ROW gate requires owner 0/Genesis".into());
        }
        // Reject a wrong or malformed lease before materializing the ordinary
        // HEADER/DAA/Scheduled batch. Valid admission still stages it once.
        let source=HeaderSourceBinding::for_plan(self.roster.endpoint_parent(),owner)?;
        if lease.binding()!=&source {return Err("paired ROW exact v1 source binding".into());}
        lease.checked_cells(&source,owner,class)?;
        use crate::legacy_envelope_map::{Map,LowerSelector,LowerSource,LowerBranch};
        for context in 0..2 {
            let expected=Map::new_modern_global_u_selected_lower(
                [1_827_840,1_810_842][context],21,55,LowerSelector{
                    source:LowerSource::HeaderDifficulty{height:841_729},
                    branch:LowerBranch::Pivot(54)})?.binding();
            if lease.map_binding(context)?!=&expected {
                return Err("paired ROW exact 55/55 Eligible08 Map binding".into());
            }
        }
        let base=Arc::new(self.stage_owner(owner)?);
        if base.class!=class || base.source!=source {
            return Err("paired ROW ordinary source binding/class changed".into());
        }
        let layout=Layout::paired_map();
        let mut maps:[Vec<Term>;2]=[Vec::new(),Vec::new()];
        for context in 0..2 {
            let terms=lease.terms(context)?;
            if terms.len()!=MAP_TERMS {return Err("paired ROW retained Map term census".into());}
            maps[context]=terms.iter().cloned().map(|term|
                layout.place(class,Relation::Map(context),owner,term))
                .collect::<Result<Vec<_>,_>>()?;
        }
        if base.terms.len()+maps.iter().map(Vec::len).sum::<usize>()>TERM_LIMIT {
            return Err("paired ROW per-owner term bound".into());
        }
        let batch=PairedMapBatch{expected_base:Arc::clone(&base),class:base.class,
            base,source,expected_maps:maps.clone(),maps,
            map_relations:[Relation::Map(0),Relation::Map(1)],layout:layout.digest(),
            expected_layout:layout.digest()};
        self.registry_with_map_pair(owner)?.check_map_pair(&batch)?;
        Ok(batch)
    }
    /// Structural v4 ROW admission for every current H21 owner class. The
    /// sealed source lease alone supplies the source-derived Map selectors;
    /// padding Map zero equations are retained without claiming X authorship.
    pub(super) fn stage_owner_with_map_pair_general(&self,owner:usize,
        lease:&Eligible08MapPairLease)->Result<PairedMapBatch,String> {
        let class=self.roster.owner_class(owner as u64)?;
        let source=HeaderSourceBinding::for_plan(self.roster.endpoint_parent(),owner)?;
        if lease.binding()!=&source {return Err("general paired ROW exact v1 source binding".into());}
        // This checks both ordered contexts, exact source terms, typed foreign
        // imports, parent/cut/owner/class and source Map bindings before staging.
        lease.checked_cells(&source,owner,class)?;
        let base=Arc::new(self.stage_owner(owner)?);
        let mut ordinary=base.terms.iter();
        let expected=self.visit_sources(owner,|relation,term| {
            let staged=ordinary.next().ok_or("general paired ROW ordinary source omitted term")?;
            if staged.relation!=relation
                ||staged.term!=Layout::fixed().place(class,relation,owner,term)? {
                return Err("general paired ROW ordinary ordered source tuples changed".into());
            }
            Ok(())
        })?;
        if ordinary.next().is_some()||expected!=base.expected||base.class!=class||base.source!=source {
            return Err("general paired ROW ordinary source census/binding/class".into());
        }
        let layout=Layout::paired_map_general();
        let mut maps:[Vec<Term>;2]=[Vec::new(),Vec::new()];
        let mut term_count=base.terms.len();
        for context in 0..2 {
            let terms=lease.terms(context)?;
            term_count=term_count.checked_add(terms.len())
                .filter(|count|*count<=TERM_LIMIT).ok_or("general paired ROW per-owner term bound")?;
            // Counts vary by owner, context and selected-lower branch. The
            // checked ordered source list is the census, including zero terms.
            maps[context]=terms.iter().cloned().map(|term|
                layout.place(class,Relation::Map(context),owner,term))
                .collect::<Result<Vec<_>,_>>()?;
        }
        let batch=PairedMapBatch{expected_base:Arc::clone(&base),class,
            base,source,expected_maps:maps.clone(),maps,
            map_relations:[Relation::Map(0),Relation::Map(1)],layout:layout.digest(),
            expected_layout:layout.digest()};
        self.registry_with_map_pair_general(owner)?.check_map_pair(&batch)?;
        Ok(batch)
    }
    /// The coactive owner's Map terms come from the completed sink itself.
    /// No second Map producer or caller-assembled pair lease is minted here.
    pub(super) fn stage_owner_with_retained_map_general(&self,owner:usize,
        view:&Eligible08MapSourceView<'_>)->Result<PairedMapBatch,String> {
        let class=self.roster.owner_class(owner as u64)?;
        let source=HeaderSourceBinding::for_plan(self.roster.endpoint_parent(),owner)?;
        if owner!=CAP0_OWNER || class!=OwnerClass::Carry || view.binding()!=&source {
            return Err("retained Map ROW exact coactive owner/class/source".into());
        }
        let base=Arc::new(self.stage_owner(owner)?);
        let mut ordinary=base.terms.iter();
        let expected=self.visit_sources(owner,|relation,term| {
            let staged=ordinary.next().ok_or("retained Map ROW ordinary source omitted term")?;
            if staged.relation!=relation
                ||staged.term!=Layout::fixed().place(class,relation,owner,term)? {
                return Err("retained Map ROW ordinary ordered source tuples changed".into());
            }
            Ok(())
        })?;
        if ordinary.next().is_some()||expected!=base.expected||base.class!=class||base.source!=source {
            return Err("retained Map ROW ordinary source census/binding/class".into());
        }
        let layout=Layout::paired_map_general();
        let mut maps:[Vec<Term>;2]=[Vec::new(),Vec::new()];
        let mut term_count=base.terms.len();
        for context in 0..2 {
            let terms=view.checked_terms(&source,owner,class,context)?;
            term_count=term_count.checked_add(terms.len())
                .filter(|count|*count<=TERM_LIMIT).ok_or("retained Map ROW per-owner term bound")?;
            maps[context]=terms.iter().cloned().map(|term|
                layout.place(class,Relation::Map(context),owner,term))
                .collect::<Result<Vec<_>,_>>()?;
        }
        let batch=PairedMapBatch{expected_base:Arc::clone(&base),class,
            base,source,expected_maps:maps.clone(),maps,
            map_relations:[Relation::Map(0),Relation::Map(1)],layout:layout.digest(),
            expected_layout:layout.digest()};
        self.registry_with_map_pair_general(owner)?.check_map_pair(&batch)?;
        Ok(batch)
    }
    /// Join only the exact first-modern Cap0 source into this owner's active
    /// ROW occurrences. The native Cap lease and ROW batch are both checked
    /// against the same plan; no value is read from or compared with the
    /// parent's HEADER-zero Cap region in NativePackedRow.
    pub(super) fn stage_owner_cap0_overlay(&self,owner:usize,
        plan:&crate::work_tree_history_plan::WorkTreeHistoryPlan,
        prefix:&crate::packed_owner_assembly::NativePrefix,
        cap:&crate::h21_scheduled_max_cap::FirstModernCapLease)
        ->Result<Cap0RowOverlay,String> {
        if owner!=CAP0_OWNER {return Err("Cap0 ROW overlay fixed owner".into());}
        cap.require_native_parent(plan,prefix)?;
        let binding=HeaderSourceBinding::for_plan(plan,owner)?;
        let batch=self.stage_owner(owner)?;
        batch.require_owner_parent(plan,owner)?;
        if batch.source!=binding || batch.owner!=CAP0_OWNER || batch.class!=OwnerClass::Carry {
            return Err("Cap0 ROW overlay ROW parent/cut/layout/owner".into());
        }
        let writer=Writer::Cap{context:0,origin:CAP0_ORIGIN};
        let source=cap.cap_rows(0)?;
        if source.len()!=6_419 {return Err("Cap0 ROW overlay source row count".into());}
        let class=self.roster.owner_class(owner as u64)?;
        let source_rows=source.into_iter().map(|term|
            self.layout.place(class,Relation::Scheduled(writer),owner,term))
            .collect::<Result<Vec<_>,_>>()?;
        let placed_rows=batch.terms().filter_map(|(relation,term)|
            (relation==Relation::Scheduled(writer)).then(||term.clone())).collect::<Vec<_>>();
        if source_rows!=placed_rows {
            return Err("Cap0 ROW overlay source/consumer ordered rows".into());
        }
        let source_cells=cap.cap_cells(0)?;
        if source_cells.len()!=CAP_BITS || source_cells.iter().enumerate().any(|(i,(wire,_))|
            *wire!=CAP0_BASE+i) {
            return Err("Cap0 ROW overlay source-cell identity".into());
        }
        let mut claims=Vec::new();
        let mut active_occurrences=0usize;
        for operand in batch.active_operands().filter(|op|op.relation==Relation::Scheduled(writer)) {
            active_occurrences=active_occurrences.checked_add(1)
                .ok_or("Cap0 ROW overlay active occurrence overflow")?;
            if let Some(local)=operand.wire.checked_sub(CAP0_OWNER*WIDTH)
                .filter(|local|(CAP0_BASE..CAP0_BASE+CAP_BITS).contains(local)) {
                claims.push(Cap0OverlayClaim {
                    operand,author:writer,value:source_cells[local-CAP0_BASE].1,
                });
            }
        }
        let open_occurrences=active_occurrences.checked_sub(claims.len())
            .ok_or("Cap0 ROW overlay open occurrence underflow")?;
        let overlay=Cap0RowOverlay{batch,binding,source_rows,source_cells,claims,
            cap0_relation_active_occurrences:active_occurrences,
            open_cap0_relation_occurrences:open_occurrences};
        overlay.validate()?;
        Ok(overlay)
    }
    /// Preserve all Cap1 source rows and cells, but claim only its exact local
    /// X domain. The MAX imports in Cap1's rows remain unresolved here.
    pub(super) fn stage_owner_cap1_overlay(&self,owner:usize,
        plan:&crate::work_tree_history_plan::WorkTreeHistoryPlan,
        prefix:&crate::packed_owner_assembly::NativePrefix,
        cap:&crate::h21_scheduled_max_cap::FirstModernCapLease)
        ->Result<Cap1RowOverlay,String> {
        if owner!=CAP0_OWNER {return Err("Cap1 ROW overlay fixed owner".into());}
        cap.require_native_parent(plan,prefix)?;
        let binding=HeaderSourceBinding::for_plan(plan,owner)?;
        let batch=self.stage_owner(owner)?;
        batch.require_owner_parent(plan,owner)?;
        if batch.source!=binding || batch.owner!=CAP0_OWNER || batch.class!=OwnerClass::Carry {
            return Err("Cap1 ROW overlay ROW parent/cut/layout/owner".into());
        }
        let writer=Writer::Cap{context:1,origin:CAP0_ORIGIN};
        let source=cap.cap_rows(1)?;
        if source.len()!=6_419 {return Err("Cap1 ROW overlay source row count".into());}
        let class=self.roster.owner_class(owner as u64)?;
        let source_rows=source.into_iter().map(|term|
            self.layout.place(class,Relation::Scheduled(writer),owner,term))
            .collect::<Result<Vec<_>,_>>()?;
        let placed_rows=batch.terms().filter_map(|(relation,term)|
            (relation==Relation::Scheduled(writer)).then(||term.clone())).collect::<Vec<_>>();
        if source_rows!=placed_rows {
            return Err("Cap1 ROW overlay source/consumer ordered rows".into());
        }
        let source_cells=cap.cap_cells(1)?;
        if source_cells.len()!=CAP_BITS || source_cells.iter().enumerate().any(|(i,(wire,_))|
            *wire!=CAP1_BASE+i) {
            return Err("Cap1 ROW overlay source-cell identity".into());
        }
        let mut claims=Vec::new();
        let mut active_occurrences=0usize;
        for operand in batch.active_operands().filter(|op|op.relation==Relation::Scheduled(writer)) {
            active_occurrences=active_occurrences.checked_add(1)
                .ok_or("Cap1 ROW overlay active occurrence overflow")?;
            if let Some(local)=operand.wire.checked_sub(CAP0_OWNER*WIDTH)
                .filter(|local|(CAP1_BASE..CAP1_BASE+CAP_BITS).contains(local)) {
                claims.push(Cap1OverlayClaim{operand,author:writer,
                    value:source_cells[local-CAP1_BASE].1});
            }
        }
        let open_occurrences=active_occurrences.checked_sub(claims.len())
            .ok_or("Cap1 ROW overlay open occurrence underflow")?;
        let overlay=Cap1RowOverlay{batch,binding,source_rows,source_cells,claims,
            cap1_relation_active_occurrences:active_occurrences,
            open_cap1_relation_occurrences:open_occurrences};
        overlay.validate()?;
        Ok(overlay)
    }
    /// Test-only bridge from the raw HEADER occurrences retained by the Cap
    /// publication to this plan's placed Header occurrences. Equality is
    /// ordered and multiplicity-preserving at both boundaries.
    pub(super) fn check_raw_header_placement(&self,owner:usize,raw:&[Term],batch:&Batch)
        ->Result<Vec<Term>,String> {
        if batch.owner!=owner || batch.class!=self.roster.owner_class(owner as u64)? {
            return Err("C355 placed RowPlan owner/class".into());
        }
        let retained=self.header.header_terms(owner)?.terms;
        if retained.as_slice()!=raw {return Err("C355 raw Cap HEADER source order/multiplicity".into());}
        let class=self.roster.owner_class(owner as u64)?;
        let placed=raw.iter().cloned().map(|term|
            self.layout.place(class,Relation::Header,owner,term)).collect::<Result<Vec<_>,_>>()?;
        let staged=batch.terms().filter_map(|(relation,term)|
            (relation==Relation::Header).then(||term.clone())).collect::<Vec<_>>();
        if placed!=staged {return Err("C355 placed RowPlan HEADER occurrences".into());}
        Ok(placed)
    }
    pub(super) fn stage_owner_with_daa_reads(&self,owner:usize,
        lease:&NativeDaaSourceLease<'_,'_>)->Result<DaaReadBatch,String> {
        let batch=self.stage_owner(owner)?;
        let reads=batch.checked_daa_reads(lease)?;
        Ok(DaaReadBatch{batch,reads})
    }
    /// Stage the canonical complete batch, then join every active operand to
    /// its qualified native source. Both leases are fully checked against the
    /// batch binding before the first value read. Local bank cells require the
    /// DAA author and must be absent from the HEADER mask; other local cells
    /// resolve only when HEADER-qualified. Foreign and unqualified cells stay
    /// typed open. No partial batch or read vector is returned on failure.
    pub(super) fn stage_owner_with_native_reads(&self,owner:usize,
        header:&NativeHeaderSourceLease,daa:&NativeDaaSourceLease<'_,'_>)
        ->Result<NativeReadBatch,String> {
        let batch=self.stage_owner(owner)?;
        let reads=batch.checked_native_reads(header,daa)?;
        Ok(NativeReadBatch{batch,reads})
    }
    /// Assemble the first source-owned owner-X/ROW fragment. Validate the
    /// packed row and both producer leases against the complete parent/profile/
    /// cut/layout/owner/class identity before any value read. A byte per local
    /// wire deduplicates resolved occurrences without assuming their values or
    /// authors from equal packed bits. Failed joins publish no partial stage.
    pub(super) fn stage_owner_partial_x_row<'a>(&self,owner:usize,row:&'a NativePackedRow,
        header:&NativeHeaderSourceLease,daa:&NativeDaaSourceLease<'_,'_>)
        ->Result<NativePartialXRowStage<'a>,String> {
        self.stage_owner_partial_x_row_with_cap0_option(owner,row,header,daa,None)
    }
    /// Join a checked Cap0 overlay to the same canonical batch at active
    /// operand resolution while preserving the legacy C362 consumer.
    pub(super) fn stage_owner_partial_x_row_with_cap0<'a>(&self,owner:usize,
        row:&'a NativePackedRow,header:&NativeHeaderSourceLease,
        daa:&NativeDaaSourceLease<'_,'_>,cap0:&Cap0RowOverlay)
        ->Result<NativePartialXRowStage<'a>,String> {
        self.stage_owner_partial_x_row_with_cap0_option(owner,row,header,daa,Some(cap0))
    }
    pub(super) fn stage_owner_partial_x_row_with_cap01<'a>(&self,owner:usize,
        row:&'a NativePackedRow,header:&NativeHeaderSourceLease,
        daa:&NativeDaaSourceLease<'_,'_>,cap0:&Cap0RowOverlay,cap1:&Cap1RowOverlay)
        ->Result<NativePartialXRowStage<'a>,String> {
        self.stage_owner_partial_x_row_with_cap_options(owner,row,header,daa,Some(cap0),Some(cap1))
    }
    pub(super) fn stage_owner_partial_x_row_with_cap01_and_foreign_max<'a>(
        &self,owner:usize,row:&'a NativePackedRow,header:&NativeHeaderSourceLease,
        daa:&NativeDaaSourceLease<'_,'_>,cap0:&Cap0RowOverlay,cap1:&Cap1RowOverlay,
        max:&crate::packed_owner_assembly::Eligible08ForeignMaxReadLease,
    )->Result<NativePartialXRowStage<'a>,String> {
        self.stage_owner_partial_x_row_with_cap_options_and_foreign_max(
            owner,row,header,daa,Some(cap0),Some(cap1),Some(max))
    }
    pub(super) fn stage_owner_partial_x_row_with_cap01_and_foreign_max_and_daa_lane2<'a>(
        &self,owner:usize,row:&'a NativePackedRow,header:&NativeHeaderSourceLease,
        daa:&NativeDaaSourceLease<'_,'_>,cap0:&Cap0RowOverlay,cap1:&Cap1RowOverlay,
        max:&crate::packed_owner_assembly::Eligible08ForeignMaxReadLease,
        foreign_daa:&[crate::packed_owner_assembly::ForeignDaaWorkReadLease;2],
    )->Result<NativePartialXRowStage<'a>,String> {
        self.stage_owner_partial_x_row_with_sources(owner,row,header,daa,
            Some(cap0),Some(cap1),Some(max),Some(foreign_daa),None)
    }
    pub(super) fn stage_owner_partial_x_row_with_cap01_and_foreign_max_and_daa_lane2_and_point<'a>(
        &self,owner:usize,row:&'a NativePackedRow,header:&NativeHeaderSourceLease,
        daa:&NativeDaaSourceLease<'_,'_>,cap0:&Cap0RowOverlay,cap1:&Cap1RowOverlay,
        max:&crate::packed_owner_assembly::Eligible08ForeignMaxReadLease,
        foreign_daa:&[crate::packed_owner_assembly::ForeignDaaWorkReadLease;2],
        point:&NativePointMembershipSourceLease,
    )->Result<NativePartialXRowStage<'a>,String> {
        self.stage_owner_partial_x_row_with_sources(owner,row,header,daa,
            Some(cap0),Some(cap1),Some(max),Some(foreign_daa),Some(point))
    }
    fn stage_owner_partial_x_row_with_cap0_option<'a>(&self,owner:usize,row:&'a NativePackedRow,
        header:&NativeHeaderSourceLease,daa:&NativeDaaSourceLease<'_,'_>,
        cap0:Option<&Cap0RowOverlay>)->Result<NativePartialXRowStage<'a>,String> {
        self.stage_owner_partial_x_row_with_cap_options(owner,row,header,daa,cap0,None)
    }
    fn stage_owner_partial_x_row_with_cap_options<'a>(&self,owner:usize,row:&'a NativePackedRow,
        header:&NativeHeaderSourceLease,daa:&NativeDaaSourceLease<'_,'_>,
        cap0:Option<&Cap0RowOverlay>,cap1:Option<&Cap1RowOverlay>)
        ->Result<NativePartialXRowStage<'a>,String> {
        self.stage_owner_partial_x_row_with_cap_options_and_foreign_max(
            owner,row,header,daa,cap0,cap1,None)
    }
    fn stage_owner_partial_x_row_with_cap_options_and_foreign_max<'a>(
        &self,owner:usize,row:&'a NativePackedRow,
        header:&NativeHeaderSourceLease,daa:&NativeDaaSourceLease<'_,'_>,
        cap0:Option<&Cap0RowOverlay>,cap1:Option<&Cap1RowOverlay>,
        foreign_max:Option<&crate::packed_owner_assembly::Eligible08ForeignMaxReadLease>,
    )->Result<NativePartialXRowStage<'a>,String> {
        self.stage_owner_partial_x_row_with_sources(owner,row,header,daa,cap0,cap1,foreign_max,None,None)
    }
    fn stage_owner_partial_x_row_with_sources<'a>(
        &self,owner:usize,row:&'a NativePackedRow,
        header:&NativeHeaderSourceLease,daa:&NativeDaaSourceLease<'_,'_>,
        cap0:Option<&Cap0RowOverlay>,cap1:Option<&Cap1RowOverlay>,
        foreign_max:Option<&crate::packed_owner_assembly::Eligible08ForeignMaxReadLease>,
        foreign_daa:Option<&[crate::packed_owner_assembly::ForeignDaaWorkReadLease;2]>,
        point_membership:Option<&NativePointMembershipSourceLease>,
    )->Result<NativePartialXRowStage<'a>,String> {
        let source=HeaderSourceBinding::for_plan(self.roster.endpoint_parent(),owner)?;
        let class=self.roster.owner_class(owner as u64)?;
        row.require_header_source_binding(&source,owner,class)?;
        header.check_binding(&source)?;
        daa.check_binding(&source)?;
        header.check_author()?;
        daa.check_author()?;
        let batch=self.stage_owner(owner)?;
        if batch.source!=source {return Err("partial X/ROW canonical source binding".into());}
        // Keep legacy wrappers unchanged. The point-enabled wrapper proves its
        // complete ROW census and source authority before the first value read.
        let point_operands=if let Some(lease)=point_membership {
            let operands=prepare_point_membership_operands(&batch,owner)?;
            lease.check_binding(&source)?;
            lease.check_author()?;
            Some(operands)
        } else {None};
        if let Some(overlay)=cap0 {
            overlay.validate()?;
            if overlay.owner()!=owner || overlay.batch.source!=source || !overlay.matches_batch(&batch) {
                return Err("partial X/ROW Cap0 binding/batch mismatch".into());
            }
            row.require_cap0_source(
                &overlay.binding,
                Writer::Cap{context:0,origin:CAP0_ORIGIN},
                &overlay.source_cells,
            )?;
        }
        if let Some(overlay)=cap1 {
            overlay.validate()?;
            if overlay.owner()!=owner || overlay.batch.source!=source || !overlay.matches_batch(&batch) {
                return Err("partial X/ROW Cap1 binding/batch mismatch".into());
            }
            row.require_cap1_source(
                &overlay.binding,
                Writer::Cap{context:1,origin:CAP0_ORIGIN},
                &overlay.source_cells,
            )?;
        }
        // Resolve and validate the complete foreign MAX occurrence ledger
        // before the first HEADER or DAA value read.
        let foreign_max_reads=foreign_max.map(|lease|
            prepare_foreign_max_reads(&batch,&source,owner,lease)).transpose()?;
        let foreign_daa_reads=foreign_daa.map(|leases|
            prepare_foreign_daa_lane2_reads(&batch,&source,owner,
                [&leases[0],&leases[1]])).transpose()?;
        let reads=batch.checked_native_reads(header,daa)?;
        let mut reads=reads;
        if let (Some(lease),Some(point_operands))=(point_membership,point_operands) {
            let row_base=owner.checked_mul(WIDTH).ok_or("point membership row base overflow")?;
            for (index,operand) in point_operands {
                if !matches!(reads.get(index),Some(NativeRead::Unresolved{
                    operand:actual,reason:UnresolvedRead::UnqualifiedLocal}) if *actual==operand) {
                    return Err("partial X/ROW point membership overlaps another author".into());
                }
                let value=lease.read_point_bit(&source,operand.wire)?;
                let local=operand.wire.checked_sub(row_base)
                    .ok_or("point membership local wire underflow")?;
                let packed=(row.packed_bytes()[local/8]>>(local%8))&1!=0;
                if packed!=value {return Err("point membership packed value mismatch".into());}
                reads[index]=NativeRead::PointMembership{operand,value};
            }
        }
        if let Some(overlay)=cap0 {
            let writer=Writer::Cap{context:0,origin:CAP0_ORIGIN};
            let owner_base=owner.checked_mul(WIDTH).ok_or("partial X/ROW Cap0 owner overflow")?;
            let mut claims=overlay.claims.iter().peekable();
            for (operand,read) in batch.active_operands().zip(reads.iter_mut()) {
                if operand.relation!=Relation::Scheduled(writer) {continue;}
                let in_domain=operand.wire.checked_sub(owner_base)
                    .is_some_and(|local|(CAP0_BASE..CAP0_BASE+CAP_BITS).contains(&local));
                if in_domain {
                    let claim=claims.next().ok_or("partial X/ROW missing Cap0 occurrence claim")?;
                    if claim.operand!=operand || claim.author!=writer {
                        return Err("partial X/ROW Cap0 occurrence/author mismatch".into());
                    }
                    if !matches!(*read,NativeRead::Unresolved{
                        operand:actual,reason:UnresolvedRead::UnqualifiedLocal} if actual==operand) {
                        return Err("partial X/ROW Cap0 overlaps another native author".into());
                    }
                    *read=NativeRead::Cap0{operand,author:claim.author,value:claim.value};
                } else if claims.peek().is_some_and(|claim|claim.operand==operand) {
                    return Err("partial X/ROW Cap0 out-of-domain occurrence claim".into());
                }
            }
            if claims.next().is_some() {return Err("partial X/ROW unused Cap0 occurrence claim".into());}
        }
        if let Some(overlay)=cap1 {
            let writer=Writer::Cap{context:1,origin:CAP0_ORIGIN};
            let owner_base=owner.checked_mul(WIDTH).ok_or("partial X/ROW Cap1 owner overflow")?;
            let mut claims=overlay.claims.iter().peekable();
            for (operand,read) in batch.active_operands().zip(reads.iter_mut()) {
                if operand.relation!=Relation::Scheduled(writer) {continue;}
                let in_domain=operand.wire.checked_sub(owner_base)
                    .is_some_and(|local|(CAP1_BASE..CAP1_BASE+CAP_BITS).contains(&local));
                if in_domain {
                    let claim=claims.next().ok_or("partial X/ROW missing Cap1 occurrence claim")?;
                    if claim.operand!=operand || claim.author!=writer {
                        return Err("partial X/ROW Cap1 occurrence/author mismatch".into());
                    }
                    if !matches!(*read,NativeRead::Unresolved{
                        operand:actual,reason:UnresolvedRead::UnqualifiedLocal} if actual==operand) {
                        return Err("partial X/ROW Cap1 overlaps another native author".into());
                    }
                    *read=NativeRead::Cap1{operand,author:claim.author,value:claim.value};
                } else if claims.peek().is_some_and(|claim|claim.operand==operand) {
                    return Err("partial X/ROW Cap1 out-of-domain occurrence claim".into());
                }
            }
            if claims.next().is_some() {return Err("partial X/ROW unused Cap1 occurrence claim".into());}
        }
        if let Some(prepared)=foreign_max_reads {
            for ((operand,read),cell) in batch.active_operands().zip(reads.iter_mut())
                .zip(prepared.into_iter()) {
                if let Some(cell)=cell {
                    if !matches!(*read,NativeRead::Unresolved{operand:actual,
                        reason:UnresolvedRead::ForeignOwner} if actual==operand) {
                        return Err("partial X/ROW foreign MAX occurrence/source conflict".into());
                    }
                    *read=NativeRead::ForeignMax{operand,cell};
                }
            }
        }
        if let Some(prepared)=foreign_daa_reads {
            for ((operand,read),cell) in batch.active_operands().zip(reads.iter_mut())
                .zip(prepared.into_iter()) {
                if let Some((source_index,wire))=cell {
                    let value=foreign_daa.ok_or("foreign DAA lease disappeared")?[source_index]
                        .read(&source,owner,wire)?;
                    let source_owner=FOREIGN_DAA_SOURCE_OWNERS[source_index];
                    if !matches!(*read,NativeRead::Unresolved{operand:actual,
                        reason:UnresolvedRead::ForeignOwner} if actual==operand) {
                        return Err("foreign DAA lane2 occurrence/source conflict".into());
                    }
                    *read=NativeRead::ForeignDaaLane2{operand,source_owner,wire,value};
                }
            }
        }
        let base=owner.checked_mul(WIDTH).ok_or("partial X/ROW owner overflow")?;
        let mut local_claims=vec![0u8;WIDTH];
        let mut seen=0usize;
        for (operand,read) in batch.active_operands().zip(reads.iter()) {
            seen+=1;
            let local=operand.wire.checked_sub(base).filter(|local|*local<WIDTH);
            let code=match *read {
                NativeRead::Header{operand:actual,value} => {
                    if actual!=operand || local.map_or(true,|local|
                        BANKS.iter().any(|&(start,end)|(start..end).contains(&local))) {
                        return Err("partial X/ROW HEADER occurrence/domain".into());
                    }
                    Some(if value{2}else{1})
                }
                NativeRead::Daa{operand:actual,value} => {
                    if actual!=operand || local.map_or(true,|local|
                        !BANKS.iter().any(|&(start,end)|(start..end).contains(&local))) {
                        return Err("partial X/ROW DAA occurrence/domain".into());
                    }
                    Some(if value{4}else{3})
                }
                NativeRead::PointMembership{operand:actual,value} => {
                    if actual!=operand || operand.relation!=Relation::Header
                        || local.map_or(true,|local|
                            !(POINT_MEMBERSHIP_OFFSET+POINT_MEMBERSHIP_SOURCE_START..
                                POINT_MEMBERSHIP_OFFSET+POINT_MEMBERSHIP_SOURCE_END).contains(&local)) {
                        return Err("partial X/ROW point membership occurrence/domain".into());
                    }
                    Some(if value{10}else{9})
                }
                NativeRead::Cap0{operand:actual,author,value} => {
                    if actual!=operand || author!=(Writer::Cap{context:0,origin:CAP0_ORIGIN})
                        || operand.relation!=Relation::Scheduled(author)
                        || local.map_or(true,|local|!(CAP0_BASE..CAP0_BASE+CAP_BITS).contains(&local)) {
                        return Err("partial X/ROW Cap0 occurrence/author/domain".into());
                    }
                    Some(if value{6}else{5})
                }
                NativeRead::Cap1{operand:actual,author,value} => {
                    if actual!=operand || author!=(Writer::Cap{context:1,origin:CAP0_ORIGIN})
                        || operand.relation!=Relation::Scheduled(author)
                        || local.map_or(true,|local|!(CAP1_BASE..CAP1_BASE+CAP_BITS).contains(&local)) {
                        return Err("partial X/ROW Cap1 occurrence/author/domain".into());
                    }
                    Some(if value{8}else{7})
                }
                NativeRead::ForeignMax{operand:actual,cell} => {
                    let context=match operand.relation {
                        Relation::Scheduled(Writer::Cap{context,origin})
                            if origin==owner+1 && context<2=>context,
                        _=>return Err("partial X/ROW foreign MAX relation/context".into()),
                    };
                    if actual!=operand || cell.context!=context
                        || cell.end!=FOREIGN_MAX_OWNER+2 || operand.wire!=cell.wire
                        || operand.wire/WIDTH!=FOREIGN_MAX_OWNER || local.is_some()
                        || cell.author!=crate::h21_scheduled_max_cap::MaxReplayAuthor::Scheduled(
                            Writer::Max{context,end:FOREIGN_MAX_OWNER+2}) {
                        return Err("partial X/ROW foreign MAX occurrence/author/domain".into());
                    }
                    None
                }
                NativeRead::ForeignDaaLane2{operand:actual,source_owner,wire,..} => {
                    if actual!=operand || operand.relation!=Relation::DaaLane(2)
                        || source_owner!=operand.wire/WIDTH
                        || !FOREIGN_DAA_SOURCE_OWNERS.contains(&source_owner)
                        || operand.wire!=wire
                         || wire.checked_sub(source_owner*WIDTH)
                             .filter(|local|(FOREIGN_DAA_WORK_START..
                                 FOREIGN_DAA_WORK_START+FOREIGN_DAA_OCCURRENCES).contains(local)).is_none()
                         || local.is_some() {
                        return Err("partial X/ROW foreign DAA lane2 occurrence/author/domain".into());
                    }
                    None
                }
                NativeRead::Unresolved{operand:actual,reason:UnresolvedRead::ForeignOwner} => {
                    if actual!=operand || local.is_some() {
                        return Err("partial X/ROW foreign open occurrence".into());
                    }
                    None
                }
                NativeRead::Unresolved{operand:actual,reason:UnresolvedRead::UnqualifiedLocal} => {
                    if actual!=operand || local.is_none() {
                        return Err("partial X/ROW local open occurrence".into());
                    }
                    None
                }
            };
            if let Some(code)=code {
                let local=local.ok_or("partial X/ROW resolved foreign wire")?;
                let packed=(row.packed_bytes()[local/8]>>(local%8))&1!=0;
                if packed != (code==2 || code==4 || code==6 || code==8 || code==10) {
                    return Err("partial X/ROW native packed value mismatch".into());
                }
                let slot=&mut local_claims[local];
                if *slot!=0 && *slot!=code {
                    return Err("partial X/ROW duplicate author/value conflict".into());
                }
                *slot=code;
            }
        }
        if seen!=reads.len() || seen!=batch.active_operands().count() {
            return Err("partial X/ROW active occurrence count".into());
        }
        let mut claims=Vec::new();
        for (local,code) in local_claims.into_iter().enumerate() {
            let (author,value)=match code {
                0=>continue,1=>(NativeXAuthor::Header,false),2=>(NativeXAuthor::Header,true),
                3=>(NativeXAuthor::Daa,false),4=>(NativeXAuthor::Daa,true),
                5=>(NativeXAuthor::Cap0(Writer::Cap{context:0,origin:CAP0_ORIGIN}),false),
                6=>(NativeXAuthor::Cap0(Writer::Cap{context:0,origin:CAP0_ORIGIN}),true),
                7=>(NativeXAuthor::Cap1(Writer::Cap{context:1,origin:CAP0_ORIGIN}),false),
                8=>(NativeXAuthor::Cap1(Writer::Cap{context:1,origin:CAP0_ORIGIN}),true),
                9=>(NativeXAuthor::PointMembership,false),10=>(NativeXAuthor::PointMembership,true),
                _=>return Err("partial X/ROW claim encoding".into()),
            };
            claims.push(NativeXClaim{wire:base+local,author,value});
        }
        Ok(NativePartialXRowStage{row,batch,reads,claims})
    }
    pub(super) fn registry(&self,owner:usize)->Result<RowRegistry,String> {
        Ok(RowRegistry{owner,class:self.roster.owner_class(owner as u64)?,layout:self.layout.digest(),
            source:HeaderSourceBinding::for_plan(self.roster.endpoint_parent(),owner)?,
            committed:false,rows:vec![0;ROWS],relations:[None;RELATIONS]})
    }
    pub(super) fn registry_with_map_pair(&self,owner:usize)->Result<RowRegistry,String> {
        if owner!=0 || self.roster.owner_class(owner as u64)?!=OwnerClass::Genesis {
            return Err("paired ROW registry requires owner 0/Genesis".into());
        }
        let mut registry=self.registry(owner)?;
        registry.layout=Layout::paired_map().digest();Ok(registry)
    }
    pub(super) fn registry_with_map_pair_general(&self,owner:usize)->Result<RowRegistry,String> {
        let mut registry=self.registry(owner)?;
        registry.layout=Layout::paired_map_general().digest();Ok(registry)
    }
    /// Independent fifteen-slot C455 registry. The existing v1-v4 registry
    /// retains its eleven-slot relation array unchanged.
    pub(super) fn registry_with_complete(&self,owner:usize)
        ->Result<CompleteRowRegistry,String> {
        let class=self.roster.owner_class(owner as u64)?;
        if owner!=COMPLETE_OWNER||class!=OwnerClass::Carry {
            return Err("v5 registry requires owner845759/Carry".into());
        }
        Ok(CompleteRowRegistry{owner,class,layout:CompleteLayout::digest(),
            source:HeaderSourceBinding::for_plan(self.roster.endpoint_parent(),owner)?,
            committed:false,rows:vec![0;ROWS],relations:[None;COMPLETE_RELATIONS]})
    }
}

/// One complete batch per owner. Relation tags are independent of equal gates
/// or witness values; multiple monomials of the same relation/ROW are allowed.
#[derive(Clone,Debug,PartialEq,Eq)]
pub(super) struct RowRegistry {
    owner:usize,class:OwnerClass,layout:[u8;32],source:HeaderSourceBinding,committed:bool,
    rows:Vec<u8>,relations:[Option<Relation>;RELATIONS],
}
impl RowRegistry {
    fn check(&self,batch:&Batch)->Result<(Vec<u8>,[Option<Relation>;RELATIONS]),String> {
        if batch.layout!=Layout::fixed().digest() {
            return Err("ROW batch owner/class/layout: ordinary requires v1".into());
        }
        self.check_entries(batch.owner,batch.class,batch.layout,&batch.source,
            &batch.expected,&batch.relations,batch.terms())
    }
    fn check_map_pair(&self,batch:&PairedMapBatch)
        ->Result<(Vec<u8>,[Option<Relation>;RELATIONS]),String> {
        batch.check_source_tuples()?;
        if batch.layout!=Layout::paired_map().digest()
            &&batch.layout!=Layout::paired_map_general().digest() {
            return Err("paired ROW batch requires v2/v4 layout".into());
        }
        self.check_entries(batch.owner(),batch.class,batch.layout,&batch.source,
            &batch.counts(),&batch.relations(),batch.terms())
    }
    // One collision/placement engine serves both versioned entry points. All
    // output is local until the final commit, including every rejection path.
    fn check_entries<'a>(&self,owner:usize,class:OwnerClass,layout:[u8;32],
        source:&HeaderSourceBinding,expected:&[usize;RELATIONS],
        expected_relations:&[Option<Relation>;RELATIONS],
        entries:impl Iterator<Item=(Relation,&'a Term)>)
        ->Result<(Vec<u8>,[Option<Relation>;RELATIONS]),String> {
        if self.committed{return Err("duplicate complete producer batch".into());}
        if(owner,class,layout,source)!=(self.owner,self.class,self.layout,&self.source) {
            return Err("ROW batch owner/class/layout".into());
        }
        let placement=if layout==Layout::fixed().digest(){Layout::fixed()}
            else if layout==Layout::paired_map().digest(){Layout::paired_map()}
            else if layout==Layout::paired_map_general().digest(){Layout::paired_map_general()}
            else{return Err("ROW unknown layout version".into());};
        let mut rows=vec![0u8;ROWS];let mut relations=[None;RELATIONS];let mut counts=[0;RELATIONS];
        let mut placement_valid=true;let mut term_count=0;
        // Detect semantic collisions before considering placement ranges or
        // counts: restoring the old HEADER tail must expose the real collision.
        for (relation,term) in entries {
            term_count+=1;
            if term_count>TERM_LIMIT {return Err("ROW batch per-owner term bound".into());}
            let slot=relation.slot(self.owner)?;
            let q=term.row.checked_sub(self.owner*ROWS).filter(|q|*q<ROWS).ok_or("ROW batch physical owner")?;
            if term.gate.left>=WIDTH*OWNERS||term.gate.right>=WIDTH*OWNERS{return Err("ROW batch X extent".into());}
            if relations[slot].is_some_and(|r|r!=relation){return Err("ROW relation identity changed".into());}
            relations[slot]=Some(relation);counts[slot]+=1;
            let tag=(slot+1)as u8;
            if rows[q]!=0&&rows[q]!=tag{return Err("cross-relation ROW collision".into());}
            rows[q]=tag;
            placement_valid &= placement.placed(self.class,relation,q)
                && placement.permits_reserved(relation,q);
        }
        if &counts!=expected||&relations!=expected_relations{return Err("ROW batch omission/duplicate".into());}
        if !placement_valid {return Err("ROW batch placement/reservation".into());}
        Ok((rows,relations))
    }
    pub(super) fn commit(&mut self,batch:&Batch)->Result<(),String> {
        let(rows,relations)=self.check(batch)?;
        self.rows=rows;self.relations=relations;self.committed=true;Ok(())
    }
    pub(super) fn commit_map_pair(&mut self,batch:&PairedMapBatch)->Result<(),String> {
        let(rows,relations)=self.check_map_pair(batch)?;
        self.rows=rows;self.relations=relations;self.committed=true;Ok(())
    }
    pub(super) fn commit_coactive_map_pair(&mut self,batch:&PairedMapBatch,
        stage:&NativePartialXRowStage<'_>,census:&NativeOwnerAuthorCensus,
        view:&Eligible08MapSourceView<'_>)->Result<CoactiveMapRowEvidence,String> {
        let(rows,relations)=self.check_map_pair(batch)?;
        let evidence=batch.checked_coactive_map_values(stage,census,view)?;
        self.rows=rows;self.relations=relations;self.committed=true;Ok(evidence)
    }
    #[cfg(test)]
    pub(super) fn check_map_pair_for_test(&self,batch:&PairedMapBatch)->Result<(),String> {
        self.check_map_pair(batch).map(|_|())
    }
    #[cfg(test)]
    pub(super) fn row_tag_for_test(&self,q:usize)->u8 {self.rows[q]}
    pub(super) fn distinct_rows(&self)->usize{self.rows.iter().filter(|r|**r!=0).count()}
}

/// Atomic C455 registry with a separate fifteen-slot identity. It owns the
/// selected ROW tags only; no partial mutation escapes a failed source/read
/// check, and a second complete commit is rejected.
#[derive(Clone,Debug,PartialEq,Eq)]
pub(super) struct CompleteRowRegistry {
    owner:usize,class:OwnerClass,layout:[u8;32],source:HeaderSourceBinding,committed:bool,
    rows:Vec<u8>,relations:[Option<CompleteRelation>;COMPLETE_RELATIONS],
}
impl CompleteRowRegistry {
    fn check(&self,batch:&CompleteBatch<'_,'_>)
        ->Result<(Vec<u8>,[Option<CompleteRelation>;COMPLETE_RELATIONS]),String> {
        if self.committed {return Err("v5 duplicate complete producer batch".into());}
        if batch.owner()!=self.owner||batch.class()!=self.class
            ||batch.layout_digest()!=self.layout||batch.source_binding()!=&self.source {
            return Err("v5 ROW owner/class/layout/source binding".into());
        }
        batch.check_source_tuples()?;
        self.check_entries(batch.owner(),batch.class(),batch.layout_digest(),
            batch.source_binding(),&batch.expected,&batch.relations,batch.terms())
    }
    fn check_entries<'a>(&self,owner:usize,class:OwnerClass,layout:[u8;32],
        source:&HeaderSourceBinding,expected:&[usize;COMPLETE_RELATIONS],
        expected_relations:&[Option<CompleteRelation>;COMPLETE_RELATIONS],
        entries:impl Iterator<Item=(CompleteRelation,&'a Term)>)
        ->Result<(Vec<u8>,[Option<CompleteRelation>;COMPLETE_RELATIONS]),String> {
        if self.committed {return Err("v5 duplicate complete producer batch".into());}
        if (owner,class,layout,source)!=(self.owner,self.class,self.layout,&self.source) {
            return Err("v5 ROW owner/class/layout/source binding".into());
        }
        if layout!=CompleteLayout::digest()||owner!=COMPLETE_OWNER||class!=OwnerClass::Carry {
            return Err("v5 fifteen-relation layout identity".into());
        }
        let row_base=owner.checked_mul(ROWS).ok_or("v5 ROW owner base overflow")?;
        let mut rows=vec![0u8;ROWS];let mut relations=[None;COMPLETE_RELATIONS];
        let mut counts=[0usize;COMPLETE_RELATIONS];let mut placement_valid=true;
        let mut term_count=0usize;
        // Collision checks include every ordinary v4 term and precede the
        // placement verdict, preserving C454's failure ordering.
        for (relation,term) in entries {
            term_count=term_count.checked_add(1).ok_or("v5 term count overflow")?;
            if term_count>TERM_LIMIT {return Err("v5 per-owner term bound".into());}
            let slot=relation.slot(owner)?;
            let q=term.row.checked_sub(row_base).filter(|q|*q<ROWS)
                .ok_or("v5 physical ROW owner")?;
            if term.gate.left>=WIDTH*OWNERS||term.gate.right>=WIDTH*OWNERS {
                return Err("v5 physical X extent".into());
            }
            if relations[slot].is_some_and(|prior|prior!=relation) {
                return Err("v5 relation identity changed".into());
            }
            relations[slot]=Some(relation);
            counts[slot]=counts[slot].checked_add(1).ok_or("v5 slot count overflow")?;
            let tag=(slot+1)as u8;
            if rows[q]!=0&&rows[q]!=tag {return Err("v5 cross-relation ROW collision".into());}
            rows[q]=tag;
            placement_valid &= CompleteLayout::placed(class,relation,q);
        }
        if counts!=*expected||relations!=*expected_relations {
            return Err("v5 fifteen-slot omission/duplicate".into());
        }
        if !placement_valid {return Err("v5 ROW placement/reservation".into());}
        Ok((rows,relations))
    }
    pub(super) fn commit_complete_coactive(&mut self,batch:&CompleteBatch<'_,'_>,
        stage:&NativePartialXRowStage<'_>,census:&NativeOwnerAuthorCensus,
        view:&crate::packed_owner_assembly::Eligible08CompleteRowSourceView<'_>)
        ->Result<CompleteRowEvidence,String> {
        let (rows,relations)=self.check(batch)?;
        let evidence=batch.checked_coactive_values(stage,census,view)?;
        self.rows=rows;self.relations=relations;self.committed=true;Ok(evidence)
    }
    pub(super) fn distinct_rows(&self)->usize {self.rows.iter().filter(|tag|**tag!=0).count()}
    #[cfg(test)]
    pub(super) fn row_tag_for_test(&self,q:usize)->u8 {self.rows[q]}
}

#[cfg(test)]
#[path="header_daa_row_placement_tests.rs"]
mod tests;

#[cfg(test)]
mod c448_anchor_stage_tests {
    use super::*;
    use ark_ff::One;
    use crate::work_tree_history_plan::WorkTreeHistoryPlan;

    fn reject_unchanged(registry:&AnchorRowRegistry,bad:&AnchorBatch<'_>,message:&str) {
        let mut candidate=registry.clone();let before=candidate.clone();
        let error=candidate.commit(bad).expect_err(message);
        assert!(!error.is_empty(),"{message}");assert_eq!(candidate,before,"{message}");
    }

    fn literal_place(index:usize,source:&Term)->Term {
        // Independent literal relocation oracle; Score is already placed.
        let offset=[67474isize,49937,0,0,53422,35885][index];
        let mut expected=source.clone();
        expected.row=usize::try_from(source.row as isize+offset).unwrap();expected
    }

    fn check_frozen_descriptors() {
        let mut v1=b"c121a-row19-v1\0".to_vec();
        for word in [19u64,20,21,40,41,393216,406406,507536,520726,477074,507536,
            12554,131072,131264,166664,179218,95480,108315,132096,166665,393216,262144,475136,466944] {
            v1.extend_from_slice(&word.to_le_bytes());
        }
        assert_eq!(Layout::fixed().descriptor(),v1);
        let mut cut=b"nipopow-cut-descriptor-08-v1\0".to_vec();cut.push(1);
        for word in [1_827_840u64,1_810_842,1_810_905,1_024,64] {
            cut.extend_from_slice(&word.to_be_bytes());
        }
        cut.extend([0,1]);
        let mut v2=b"c439-row19-paired-map-v2\0".to_vec();
        v2.extend_from_slice(&Blake2b::<U32>::digest(&v1));
        v2.extend_from_slice(&(cut.len()as u64).to_le_bytes());v2.extend_from_slice(&cut);
        v2.extend_from_slice(&11u64.to_le_bytes());
        for slot in 0..11u64 {v2.extend_from_slice(&slot.to_le_bytes());}
        for word in [0u64,409600,419947,477074,487421,1,442368,452715,492305,502652] {
            v2.extend_from_slice(&word.to_le_bytes());
        }
        assert_eq!(Layout::paired_map().descriptor(),v2);
        assert_eq!(Layout::fixed().digest(),<[u8;32]>::from(Blake2b::<U32>::digest(&v1)));
        assert_eq!(Layout::paired_map().digest(),<[u8;32]>::from(Blake2b::<U32>::digest(&v2)));
    }

    #[test]
    fn c448_owner417790_anchor_stage_no_frame()->Result<(),String> {
        let owner=417_790;
        let parent=WorkTreeHistoryPlan::compile(1_827_840,21,[0x43;32],[0x44;28])?;
        let roster=DaaHistoryRoster::compile(&parent)?;
        let scheduled=Scheduled::eligible08();let plan=RowPlan::new(&roster,&scheduled)?;
        let bundle=Eligible08MapSlackAnchorBundle::synthetic_for_plan_for_test(&parent)?;
        let binding=HeaderSourceBinding::for_plan(&parent,owner)?;
        let batch=plan.stage_owner_with_anchor(owner,&bundle)?;
        let registry=plan.registry_with_anchor(owner)?;
        check_frozen_descriptors();
        assert_eq!(RELATIONS,11);assert_eq!(ANCHOR_RELATIONS,15);
        assert_eq!(batch.owner(),owner);assert_eq!(batch.class(),OwnerClass::Carry);
        assert_eq!(batch.source_binding(),&binding);
        assert_ne!(batch.layout_digest(),Layout::fixed().digest());
        assert_ne!(batch.layout_digest(),Layout::paired_map().digest());
        assert_eq!(batch.base.layout,Layout::fixed().digest());
        assert_eq!(batch.base.expected[5..9],[0;4]);
        let ordinary=plan.stage_owner(owner)?;
        assert_eq!(batch.base.terms,ordinary.terms);
        assert_eq!(batch.base.expected,ordinary.expected);
        let sources=anchor_source_lists(&bundle,&binding)?;
        for index in 0..6 {
            assert_eq!(batch.bank[index].len(),sources[index].len());
            for (staged,source) in batch.bank[index].iter().zip(sources[index]) {
                assert_eq!(staged,&literal_place(index,source),"ordered tuple list={index}");
            }
        }
        let mut traversal=batch.terms();
        for entry in &ordinary.terms {
            assert_eq!(traversal.next(),Some((AnchorRelation::Ordinary(entry.relation),&entry.term)));
        }
        for index in 0..6 {for term in &batch.bank[index] {
            assert_eq!(traversal.next(),Some((AnchorRelation::bank(index),term)));
        }}
        assert!(traversal.next().is_none());
        let expected=batch.check_source_tuples()?;
        assert_eq!(expected[13..15],[387,387]);
        let mut committed=registry.clone();committed.commit(&batch)?;
        assert!(committed.distinct_rows()>0);
        reject_unchanged(&committed,&batch,"second complete batch");

        // Each checked family/context has isolated omission, duplicate, role,
        // order, row and gate mutations. No caller-authored production path.
        for index in 0..6 {
            let mut bad=batch.clone();bad.bank[index].remove(0);
            reject_unchanged(&registry,&bad,"omitted family term");
            let mut bad=batch.clone();let duplicate=bad.bank[index][0].clone();
            bad.bank[index].push(duplicate);
            reject_unchanged(&registry,&bad,"duplicated family term");
            let mut bad=batch.clone();bad.bank_relations[index]=AnchorRelation::bank((index+1)%6);
            reject_unchanged(&registry,&bad,"cross-role family term");
            let mut bad=batch.clone();
            let distinct=(1..bad.bank[index].len()).find(|&j|bad.bank[index][j]!=bad.bank[index][0])
                .expect("each source list has distinct ordered tuples");
            bad.bank[index].swap(0,distinct);
            reject_unchanged(&registry,&bad,"reordered family term");
            let mut bad=batch.clone();bad.bank[index][0].row+=1;
            reject_unchanged(&registry,&bad,"relocated family term");
            let mut bad=batch.clone();bad.bank[index][0].gate.left^=1;
            reject_unchanged(&registry,&bad,"changed family gate wire");
            let mut bad=batch.clone();bad.bank[index][0].gate.right^=1;
            reject_unchanged(&registry,&bad,"changed family right gate wire");
            for coefficient in 0..4 {
                let mut bad=batch.clone();let gate=&mut bad.bank[index][0].gate;
                match coefficient {0=>gate.c0+=Fr::one(),1=>gate.c1+=Fr::one(),
                    2=>gate.c2+=Fr::one(),_=>gate.c3+=Fr::one()}
                reject_unchanged(&registry,&bad,"changed family coefficient");
            }
        }
        // All synthetic Slack bits are authored zero. Removing one such term
        // must still fail the source/order census before registry mutation.
        assert!(bundle.map_slack().checked_slack_cells(&binding,owner,OwnerClass::Carry)?
            .iter().all(|cell|!cell.value()));
        for index in 4..6 {
            let mut bad=batch.clone();bad.bank[index].remove(386);
            reject_unchanged(&registry,&bad,"omitted authored-zero Slack term");
        }
        for pair in [(0,1),(2,3),(4,5)] {
            let mut bad=batch.clone();bad.bank.swap(pair.0,pair.1);
            reject_unchanged(&registry,&bad,"swapped family contexts");
        }
        for field in 0..6 {
            let mut bad=batch.clone();bad.source=binding.mutated_field_for_test(field);
            reject_unchanged(&registry,&bad,"changed parent binding field");
        }
        let mut bad=batch.clone();bad.class=OwnerClass::Genesis;
        reject_unchanged(&registry,&bad,"wrong owner class");
        let mut bad=batch.clone();Arc::make_mut(&mut bad.base).owner+=1;
        reject_unchanged(&registry,&bad,"wrong owner");
        for layout in [Layout::fixed().digest(),Layout::paired_map().digest()] {
            let mut bad=batch.clone();bad.layout=layout;
            reject_unchanged(&registry,&bad,"old layout rejects v3");
        }
        assert!(plan.stage_owner_with_anchor(owner+1,&bundle).is_err());
        assert!(plan.registry_with_anchor(0).is_err());
        // A source-checked bundle with another actual plan is not admissible.
        let other=WorkTreeHistoryPlan::compile(1_827_840,21,[0x45;32],[0x44;28])?;
        let other_bundle=Eligible08MapSlackAnchorBundle::synthetic_for_plan_for_test(&other)?;
        assert!(plan.stage_owner_with_anchor(owner,&other_bundle).is_err());
        let mut v1=ordinary.clone();v1.layout=AnchorLayout::digest();
        assert!(plan.registry(owner)?.commit(&v1).is_err());
        // Both existing v1/v2 entry points share this closed version engine.
        // Even a coherent registry/batch digest mutation cannot introduce v3.
        let mut old=plan.registry(owner)?;old.layout=AnchorLayout::digest();
        assert!(old.check_entries(owner,OwnerClass::Carry,AnchorLayout::digest(),
            &binding,&ordinary.expected,&ordinary.relations,ordinary.terms())
            .unwrap_err().contains("unknown layout version"));
        let mut bad=batch.clone();Arc::make_mut(&mut bad.base).terms[0].term.gate.c0+=Fr::one();
        reject_unchanged(&registry,&bad,"ordinary source tuple changed");

        // Actual DAA collision, detected before invalid source placement.
        let daa=batch.base.terms.iter().find(|entry|matches!(entry.relation,Relation::DaaLane(_)))
            .expect("Carry emits DAA");
        let mut bad=batch.clone();bad.bank[0][0].row=daa.term.row;
        assert!(registry.check(&bad).unwrap_err().contains("cross-relation ROW collision"));
        reject_unchanged(&registry,&bad,"Map into actual DAA ROW");
        // Restore an actual HEADER-tail row into an existing DAA row.
        let daa_rows:BTreeSet<_>=batch.base.terms.iter().filter(|entry|
            matches!(entry.relation,Relation::DaaLane(_))).map(|entry|entry.term.row).collect();
        let tail=batch.base.terms.iter().enumerate().find(|(_,entry)|
            entry.relation==Relation::Header&&entry.term.row>=owner*ROWS+507536
            &&daa_rows.contains(&(entry.term.row-114320))).map(|(index,_)|index)
            .expect("restored HEADER tail overlaps actual DAA");
        let mut bad=batch.clone();Arc::make_mut(&mut bad.base).terms[tail].term.row-=114320;
        assert!(registry.check(&bad).unwrap_err().contains("cross-relation ROW collision"));
        reject_unchanged(&registry,&bad,"restored HEADER tail");
        // Equal-zero polynomial overlap is still two distinct relation claims.
        let mut bad=batch.clone();
        let daa_index=bad.base.terms.iter().position(|entry|matches!(entry.relation,Relation::DaaLane(_))).unwrap();
        let base=Arc::make_mut(&mut bad.base);let zero=&mut base.terms[daa_index].term;
        zero.gate.c0=Fr::zero();zero.gate.c1=Fr::zero();
        zero.gate.c2=Fr::zero();zero.gate.c3=Fr::zero();
        bad.bank[0][0]=zero.clone();
        assert!(registry.check(&bad).unwrap_err().contains("cross-relation ROW collision"));
        reject_unchanged(&registry,&bad,"equal-zero distinct-relation collision");
        println!("C448_ANCHOR_STAGE_NO_FRAME_PASS owner=417790 relations=15 source_checked_synthetic=true physical_authorship=false reader=false proof=false");
        Ok(())
    }
}

#[cfg(test)]
mod c448b_anchor_reader_tests {
    use super::*;
    use crate::{gkr::Gate,work_tree_history_plan::WorkTreeHistoryPlan};

    // These types have no conversion to a native writer receipt or stage.
    struct SyntheticAnchorCustody<'b> {
        source:AnchorSourceView<'b>,bytes:Vec<u8>,owner:usize,class:OwnerClass,
    }
    struct SyntheticAnchorReadStage<'b> {
        batch:AnchorBatch<'b>,reads:Vec<AnchorRead>,registry:AnchorRowRegistry,
    }
    fn stage_synthetic<'b>(plan:&RowPlan<'_,'_>,custody:&SyntheticAnchorCustody<'b>)
        ->Result<SyntheticAnchorReadStage<'b>,String> {
        let batch=plan.stage_owner_with_anchor(custody.owner,custody.source.bundle)?;
        let reads=project_anchor_reads(&batch,&custody.source,&custody.bytes,None)?;
        let mut registry=plan.registry_with_anchor(custody.owner)?;
        commit_anchor_projection(&mut registry,&batch,&custody.source,custody.owner,
            custody.class,&custody.bytes,None,&reads)?;
        Ok(SyntheticAnchorReadStage{batch,reads,registry})
    }
    fn reject_unchanged(registry:&AnchorRowRegistry,batch:&AnchorBatch<'_>,
        custody:&SyntheticAnchorCustody<'_>,reads:&[AnchorRead],message:&str) {
        let mut candidate=registry.clone();let before=candidate.clone();
        assert!(commit_anchor_projection(&mut candidate,batch,&custody.source,custody.owner,
            custody.class,&custody.bytes,None,reads).is_err(),"{message}");
        assert_eq!(candidate,before,"atomic rejection: {message}");
    }
    fn reject_header_unchanged(registry:&AnchorRowRegistry,batch:&AnchorBatch<'_>,
        custody:&SyntheticAnchorCustody<'_>,reads:&[AnchorRead],
        header:&NativeHeaderSourceLease,expected_error:&str) {
        let mut candidate=registry.clone();let before=candidate.clone();
        let error=commit_anchor_projection(&mut candidate,batch,&custody.source,custody.owner,
            custody.class,&custody.bytes,Some(header),reads).unwrap_err();
        assert!(error.contains(expected_error),"expected {expected_error}, got {error}");
        assert_eq!(candidate,before,"atomic HEADER rejection: {expected_error}");
    }
    fn with_operand(read:AnchorRead,operand:AnchorActiveOperand)->AnchorRead {
        match read {
            AnchorRead::Bank53{author,value,..}=>AnchorRead::Bank53{operand,author,value},
            AnchorRead::Header{value,..}=>AnchorRead::Header{operand,value},
            AnchorRead::OpenLocal{domain,expected,..}=>AnchorRead::OpenLocal{operand,domain,expected},
            AnchorRead::OpenForeign{source_owner,expected,..}=>
                AnchorRead::OpenForeign{operand,source_owner,expected},
        }
    }
    #[test]
    fn c448_owner417790_anchor_reader_no_frame()->Result<(),String> {
        let parent=WorkTreeHistoryPlan::compile(1_827_840,21,[0x43;32],[0x44;28])?;
        let roster=DaaHistoryRoster::compile(&parent)?;
        let scheduled=Scheduled::eligible08();let plan=RowPlan::new(&roster,&scheduled)?;
        let bundle=Eligible08MapSlackAnchorBundle::synthetic_for_plan_for_test(&parent)?;
        let binding=HeaderSourceBinding::for_plan(&parent,ANCHOR_OWNER)?;
        let source=AnchorSourceView::checked(&bundle,&binding)?;
        let mut custody=SyntheticAnchorCustody{source,bytes:vec![0;WIDTH/8],
            owner:ANCHOR_OWNER,class:OwnerClass::Carry};
        for cell in &custody.source.cells {
            if cell.value {let local=cell.wire%WIDTH;custody.bytes[local/8]|=1<<(local%8);}
        }
        let stage=stage_synthetic(&plan,&custody)?;
        assert!(stage.registry.committed);assert!(stage.registry.distinct_rows()>0);
        let registry=plan.registry_with_anchor(ANCHOR_OWNER)?;
        let batch=&stage.batch;let mut reads=stage.reads;
        assert_eq!(reads.len(),batch.active_operands().count());
        assert!(reads.iter().any(|read|matches!(read,AnchorRead::OpenForeign{..})));
        assert!(reads.iter().any(|read|matches!(read,AnchorRead::OpenLocal{..})));
        let work_d=reads.iter().position(|read|matches!(read,
            AnchorRead::OpenForeign{expected:AnchorSourceKind::WorkD,..}))
            .expect("numeric DAA lane2 retains a typed foreign Work-D obligation");
        for read in &reads {
            let operand=read.operand();
            if operand.relation==AnchorRelation::Ordinary(Relation::DaaLane(2))
                &&[ANCHOR_OWNER-1,ANCHOR_OWNER-2].contains(&(operand.wire/WIDTH))
                &&(TYPED_WORK_START..TYPED_WORK_START+TYPED_WORK_BITS)
                    .contains(&(operand.wire%WIDTH)) {
                assert!(matches!(*read,AnchorRead::OpenForeign{source_owner,
                    expected:AnchorSourceKind::WorkD,..}if source_owner==operand.wire/WIDTH));
            }
        }
        let saved_work_d=reads[work_d];
        if let AnchorRead::OpenForeign{operand,source_owner,..}=saved_work_d {
            reads[work_d]=AnchorRead::OpenForeign{operand,source_owner,
                expected:AnchorSourceKind::Header};
        }
        reject_unchanged(&registry,batch,&custody,&reads,"foreign Work-D source kind retagged HEADER");
        reads[work_d]=saved_work_d;
        {
            // Only a test-shaped lease is used here. Choose an actual active
            // local HEADER operand outside every Bank53, DAA and Tree domain.
            let tree_mask=parent.physical_assignment_replacement_mask(ANCHOR_OWNER as u64)?;
            let operand=batch.active_operands().find(|operand| {
                let local=operand.wire%WIDTH;
                operand.wire/WIDTH==ANCHOR_OWNER
                    &&operand.relation==AnchorRelation::Ordinary(Relation::Header)
                    &&custody.source.cell(operand.wire).is_none()
                    &&!BANKS.iter().any(|&(start,end)|(start..end).contains(&local))
                    &&!tree_mask[local]
            }).expect("ordinary batch has an active local HEADER operand outside other authors");
            assert!(!anchor_packed_bit(&custody.bytes,operand.wire)?);
            let header=NativeHeaderSourceLease::wrong_author_for_test(
                binding.clone(),operand.wire,false).native_author_shape_for_test();
            let header_reads=project_anchor_reads(batch,&custody.source,&custody.bytes,Some(&header))?;
            assert!(header_reads.iter().any(|read|*read==AnchorRead::Header{operand,value:false}));
            let mut qualified=0;
            for read in &header_reads {
                if let AnchorRead::Header{operand:read_operand,value}=*read {
                    assert_eq!(read_operand.wire,operand.wire);
                    assert_eq!(value,anchor_packed_bit(&custody.bytes,read_operand.wire)?);
                    qualified+=1;
                }
            }
            assert!(qualified>0);assert!(header.read_count_for_test()>0);
            let mut header_registry=registry.clone();
            commit_anchor_projection(&mut header_registry,batch,&custody.source,custody.owner,
                custody.class,&custody.bytes,Some(&header),&header_reads)?;
            assert!(header_registry.committed);

            let mut wrong_author=header.clone();wrong_author.wrong_author_mutant_for_test();
            reject_header_unchanged(&registry,batch,&custody,&header_reads,&wrong_author,
                "HEADER source author mismatch before read admission");
            let mut wrong_value=header.clone();
            wrong_value.flip_source_value_for_test(operand.wire%WIDTH);
            reject_header_unchanged(&registry,batch,&custody,&header_reads,&wrong_value,
                "v3 HEADER read/final packed bit");
            let bank_zero=custody.source.cells.iter().find(|cell|!cell.value)
                .expect("Bank53 retains authored-zero cells");
            assert!(!anchor_packed_bit(&custody.bytes,bank_zero.wire)?);
            let false_header=NativeHeaderSourceLease::wrong_author_for_test(
                binding.clone(),bank_zero.wire,false).native_author_shape_for_test();
            reject_header_unchanged(&registry,batch,&custody,&header_reads,&false_header,
                "v3 Bank53 cannot retain HEADER authorship");
        }
        for context in 0..2 {for author in [AnchorCellAuthor::Map(context),
            AnchorCellAuthor::ScoreAnchor(context),AnchorCellAuthor::Slack(context)] {
            assert!(reads.iter().any(|read|matches!(*read,
                AnchorRead::Bank53{author:a,..}if a==author)));
            // Wrong authors are rejected even where the physical value is zero.
            let index=reads.iter().position(|read|matches!(*read,
                AnchorRead::Bank53{author:a,value:false,..}if a==author))
                .expect("each typed context has authored-zero read occurrences");
            let saved=reads[index];let operand=saved.operand();
            reads[index]=AnchorRead::Bank53{operand,
                author:match author {AnchorCellAuthor::Map(c)=>AnchorCellAuthor::ScoreAnchor(c),
                    AnchorCellAuthor::ScoreAnchor(c)=>AnchorCellAuthor::Slack(c),
                    AnchorCellAuthor::Slack(c)=>AnchorCellAuthor::Map(c)},value:false};
            reject_unchanged(&registry,batch,&custody,&reads,"same-zero wrong typed author");
            reads[index]=saved;
        }}
        let saved=custody.source.cells[0];
        custody.source.cells[0].author=AnchorCellAuthor::Map(1);
        reject_unchanged(&registry,batch,&custody,&reads,"wrong source context");
        custody.source.cells[0]=saved;
        custody.source.cells[1]=saved;
        reject_unchanged(&registry,batch,&custody,&reads,"duplicate source cell");
        custody.source.cells[1]=AnchorCell{wire:saved.wire+1,
            author:AnchorCellAuthor::Map(0),value:false};
        // Restore the exact source bit, which need not be false.
        custody.source.cells[1].value=anchor_packed_bit(&custody.bytes,saved.wire+1)?;
        let cell=custody.source.cells.pop().unwrap();
        reject_unchanged(&registry,batch,&custody,&reads,"missing source cell");
        custody.source.cells.push(cell);
        let local=saved.wire%WIDTH;custody.bytes[local/8]^=1<<(local%8);
        reject_unchanged(&registry,batch,&custody,&reads,"one final packed bit");
        custody.bytes[local/8]^=1<<(local%8);
        for field in 0..6 {
            custody.source.binding=binding.mutated_field_for_test(field);
            reject_unchanged(&registry,batch,&custody,&reads,"wrong complete parent binding");
        }
        custody.source.binding=binding.clone();
        custody.owner+=1;reject_unchanged(&registry,batch,&custody,&reads,"wrong owner");
        custody.owner-=1;custody.class=OwnerClass::Genesis;
        reject_unchanged(&registry,batch,&custody,&reads,"wrong class");
        custody.class=OwnerClass::Carry;
        let mut wrong=batch.clone();wrong.layout=Layout::fixed().digest();
        reject_unchanged(&registry,&wrong,&custody,&reads,"v1 layout");
        let mut wrong=batch.clone();wrong.layout=Layout::paired_map().digest();
        reject_unchanged(&registry,&wrong,&custody,&reads,"v2 layout");
        let missing=reads.remove(1);
        reject_unchanged(&registry,batch,&custody,&reads,"missing occurrence");
        reads.insert(1,missing);reads.push(reads[0]);
        reject_unchanged(&registry,batch,&custody,&reads,"duplicate occurrence");
        reads.pop();reads.swap(0,1);
        reject_unchanged(&registry,batch,&custody,&reads,"swapped occurrences");reads.swap(0,1);
        let pair=reads.windows(2).position(|pair|
            pair[0].operand().occurrence==pair[1].operand().occurrence
            &&pair[0].operand().side==OperandSide::Left&&pair[1].operand().side==OperandSide::Right)
            .expect("c3 exposes left before right");
        reads.swap(pair,pair+1);
        reject_unchanged(&registry,batch,&custody,&reads,"right before left");reads.swap(pair,pair+1);
        let index=reads.iter().position(|read|read.operand().occurrence>0).unwrap();
        let saved=reads[index];let mut operand=saved.operand();operand.occurrence-=1;
        reads[index]=with_operand(saved,operand);
        reject_unchanged(&registry,batch,&custody,&reads,"collapsed occurrence ordinal");
        reads[index]=saved;
        for index in [reads.iter().position(|read|matches!(read,AnchorRead::OpenForeign{..})).unwrap(),
            reads.iter().position(|read|matches!(read,AnchorRead::Bank53{value:false,..})).unwrap()] {
            let saved=reads[index];reads[index]=AnchorRead::Header{operand:saved.operand(),value:false};
            reject_unchanged(&registry,batch,&custody,&reads,"foreign/Bank53 zero retagged HEADER");
            reads[index]=saved;
        }
        // A compact independent ordinal oracle includes an actual constant-only
        // term and a c3 term with repeated wires; neither gets collapsed.
        let term=|c1,c2,c3|Term{row:ANCHOR_OWNER*ROWS,gate:Gate{left:1,right:1,
            c0:Fr::from(1u64),c1:Fr::from(c1),c2:Fr::from(c2),c3:Fr::from(c3)}};
        let terms=[term(0u64,0u64,0u64),term(0,0,1),term(1,0,0)];
        let operands=AnchorActiveOperandIter{terms:terms.iter()
            .map(|term|(AnchorRelation::Map(0),term)).enumerate(),pending_right:None}
            .collect::<Vec<_>>();
        assert_eq!(operands.iter().map(|o|(o.occurrence,o.side)).collect::<Vec<_>>(),
            vec![(1,OperandSide::Left),(1,OperandSide::Right),(2,OperandSide::Left)]);
        assert_eq!(operands[0].wire,operands[1].wire);
        // C448a retains the source/order/relocation/collision regression matrix;
        // this selector adds only the read and atomic projection boundary.
        reject_unchanged(&stage.registry,batch,&custody,&reads,"second registry commit");
        let other_bundle=bundle.clone();let original=custody.source.bundle;
        custody.source.bundle=&other_bundle;
        reject_unchanged(&registry,batch,&custody,&reads,"equal bundle is not exact borrowed bundle");
        custody.source.bundle=original;
        println!("C448B_ANCHOR_READER_NO_FRAME_PASS owner=417790 relations=15 source_checked_synthetic=true physical_authorship=false typed_reader=true proof=false client=false");
        Ok(())
    }
}

#[cfg(test)]
mod c369_point_membership_preflight_tests {
    use super::*;
    use ark_ff::{One,Zero};
    use crate::gkr::Gate;

    fn fixture()->Batch {
        let owner=POINT_MEMBERSHIP_OWNER;
        let source=HeaderSourceBinding::diagnostic_for_test(owner);
        let mut terms=Vec::with_capacity(POINT_MEMBERSHIP_COUNT);
        for bit in POINT_MEMBERSHIP_SOURCE_START..POINT_MEMBERSHIP_SOURCE_END {
            let wire=owner*WIDTH+POINT_MEMBERSHIP_OFFSET+bit;
            terms.push(Entry{relation:Relation::Header,term:Term{row:owner*ROWS+bit,
                gate:Gate{left:wire,right:wire,c0:Fr::zero(),c1:Fr::one(),
                    c2:Fr::zero(),c3:Fr::zero()}}});
        }
        let mut expected=[0usize;RELATIONS];
        let mut relations=[None;RELATIONS];
        expected[0]=terms.len();relations[0]=Some(Relation::Header);
        Batch{owner,class:OwnerClass::Carry,layout:Layout::fixed().digest(),source,
            terms,expected,relations}
    }

    #[test]
    fn point_membership_census_accepts_exact_distinct_local_header_operands() {
        let batch=fixture();
        let operands=prepare_point_membership_operands(&batch,POINT_MEMBERSHIP_OWNER).unwrap();
        assert_eq!(operands.len(),POINT_MEMBERSHIP_COUNT);
        assert!(operands.iter().enumerate().all(|(index,(ordinal,operand))|
            *ordinal==index && operand.relation==Relation::Header));
    }

    #[test]
    fn point_membership_census_rejects_missing_duplicate_wrong_relation_and_wire() {
        let original=fixture();
        let mut missing=original.clone();
        missing.terms.pop();
        assert!(prepare_point_membership_operands(&missing,POINT_MEMBERSHIP_OWNER).is_err());

        let mut duplicate=original.clone();
        duplicate.terms[1].term.gate.left=duplicate.terms[0].term.gate.left;
        assert!(prepare_point_membership_operands(&duplicate,POINT_MEMBERSHIP_OWNER).is_err());

        let mut wrong_relation=original.clone();
        wrong_relation.terms[0].relation=Relation::DaaLane(0);
        assert!(prepare_point_membership_operands(&wrong_relation,POINT_MEMBERSHIP_OWNER).is_err());

        let mut wrong_wire=original.clone();
        wrong_wire.terms[0].term.gate.left=
            POINT_MEMBERSHIP_OWNER*WIDTH+POINT_MEMBERSHIP_OFFSET+POINT_MEMBERSHIP_WIDTH;
        assert!(prepare_point_membership_operands(&wrong_wire,POINT_MEMBERSHIP_OWNER).is_err());
        let mut auxiliary_wire=original.clone();
        auxiliary_wire.terms[0].term.gate.left=
            POINT_MEMBERSHIP_OWNER*WIDTH+POINT_MEMBERSHIP_OFFSET+POINT_MEMBERSHIP_SOURCE_END;
        assert!(prepare_point_membership_operands(&auxiliary_wire,POINT_MEMBERSHIP_OWNER).is_err());
        let mut reserved_zero=original.clone();
        reserved_zero.terms[0].term.gate.left=
            POINT_MEMBERSHIP_OWNER*WIDTH+POINT_MEMBERSHIP_OFFSET;
        assert!(prepare_point_membership_operands(&reserved_zero,POINT_MEMBERSHIP_OWNER).is_err());
        assert!(prepare_point_membership_operands(&original,POINT_MEMBERSHIP_OWNER+1).is_err());
    }

    // The point lease has no synthetic constructor in this module. Its producer
    // tests cover binding and author mutants; consumer value-mismatch rejection
    // remains an actual-frame integration test gap.
}

#[cfg(test)]
#[path="c425_owner_row_tests.rs"]
mod c425_owner_row_tests;

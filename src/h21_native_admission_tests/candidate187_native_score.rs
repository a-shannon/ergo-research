//! One-use bounded native MAX to modern Score endpoint diagnostic. No synthetic
//! source seeds, HEADER retirement, global X/ROW, PCS, proof or client here.
use super::*;
use ark_ff::{One, Zero};
use crate::packed_owner_assembly::{H21EligibleContext, RequiredAuthor};
use crate::h21_scheduled_max_cap::{Eligible08NativeSnapshot, MaxReplayAuthor, MaxStep, MaxStream,
    Plan as MaxPlan, Writer};

const SCORE_X: [usize;2] = [677_501,685_693];
const CAP_X: [usize;2] = [1_000_770,1_002_818];
const C512_PREVIOUS_OWNER: usize = 845_759;
const C512_CONSUMER_OWNER: usize = 845_887;
const C512_WIRE_WIDTH: usize = 1 << 20;
const C512_ROW_STRIDE: usize = crate::header_daa_row_placement::C509_ROW_STRIDE;
const C512_PREVIOUS_R_BITS: usize = 225;
const C512D_WORK_D_OWNERS: [usize;2] = [845_885,845_886];
const C512D_WORK_UPPER_OWNER: usize = 845_886;
const C512D_WORK_BITS: usize = 224;
const C512D_WORK_D_LOCAL: usize = 987_674;
const C512D_WORK_UPPER_LOCAL: usize = 987_450;

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
enum C512dWorkFamily { WorkD{owner:usize}, WorkUpper{context:usize} }

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
struct C512dWorkJoinedRead {
    operand: crate::header_daa_row_placement::C509ActiveOperand,
    family: C512dWorkFamily,
    value: bool,
}

fn c512d_exact_physical_work_projection(
    owner:usize,local:usize,cells:&[(usize,Fr)],
)->Result<Vec<bool>,String> {
    if cells.len()!=C512D_WORK_BITS {
        return Err("C512d complete physical Work endpoint count".into());
    }
    let base=owner.checked_mul(C512_WIRE_WIDTH)
        .and_then(|wire|wire.checked_add(local))
        .ok_or("C512d physical Work base overflow")?;
    let mut values=Vec::with_capacity(C512D_WORK_BITS);
    for (bit,&(wire,value)) in cells.iter().enumerate() {
        if wire!=base.checked_add(bit).ok_or("C512d physical Work wire overflow")? {
            return Err("C512d physical Work endpoint owner/order/coordinate".into());
        }
        values.push(if value.is_zero(){false}else if value.is_one(){true}
            else{return Err("C512d physical Work value is not Boolean".into())});
    }
    Ok(values)
}

/// The caller must obtain these three projections from the checked LOCAL rows
/// held by two endpoint-author leases and an Upper publication from the second.
/// This matcher preserves C509 occurrence identity; every matched occurrence
/// must still pass c512d_require_work_tree_claims against its actual token.
fn c512d_join_work_reads(
    active:&[crate::header_daa_row_placement::C509ActiveOperand],
    typed_score_reads:&[(usize,crate::packed_owner_assembly::ScoreRelationReadAuthor,Fr)],
    d_845885:&[(usize,Fr)],d_845886:&[(usize,Fr)],upper_845886:&[(usize,Fr)],
)->Result<Vec<C512dWorkJoinedRead>,String> {
    use crate::header_daa_row_placement::{C509Relation,Relation,OperandSide};
    use crate::packed_owner_assembly::ScoreRelationReadAuthor;
    let d0=c512d_exact_physical_work_projection(
        C512D_WORK_D_OWNERS[0],C512D_WORK_D_LOCAL,d_845885)?;
    let d1=c512d_exact_physical_work_projection(
        C512D_WORK_D_OWNERS[1],C512D_WORK_D_LOCAL,d_845886)?;
    let upper=c512d_exact_physical_work_projection(
        C512D_WORK_UPPER_OWNER,C512D_WORK_UPPER_LOCAL,upper_845886)?;
    let upper_base=C512D_WORK_UPPER_OWNER.checked_mul(C512_WIRE_WIDTH)
        .and_then(|wire|wire.checked_add(C512D_WORK_UPPER_LOCAL))
        .ok_or("C512d WorkUpper base overflow")?;
    let mut typed_counts=BTreeMap::<usize,usize>::new();
    for &(wire,author,value) in typed_score_reads {
        let in_upper=(upper_base..upper_base+C512D_WORK_BITS).contains(&wire);
        let is_work_upper=matches!(author,ScoreRelationReadAuthor::WorkUpper{..});
        if !in_upper&&!is_work_upper {continue;}
        let ScoreRelationReadAuthor::WorkUpper{owner,height}=author else {
            return Err("C512d WorkUpper typed source kind".into());
        };
        if owner!=C512D_WORK_UPPER_OWNER||height!=owner+2||!in_upper {
            return Err("C512d WorkUpper typed owner/height/coordinate".into());
        }
        let bit=if value.is_zero(){false}else if value.is_one(){true}
            else{return Err("C512d WorkUpper typed value is not Boolean".into())};
        if bit!=upper[wire-upper_base] {
            return Err("C512d typed WorkUpper differs from physical row".into());
        }
        let count=typed_counts.entry(wire).or_insert(0);
        *count=count.checked_add(1).ok_or("C512d typed WorkUpper count overflow")?;
        if *count>2 {return Err("C512d excess typed WorkUpper read".into());}
    }
    if typed_counts.len()!=C512D_WORK_BITS
        ||(0..C512D_WORK_BITS).any(|bit|typed_counts.get(&(upper_base+bit))!=Some(&2)) {
        return Err("C512d exact two typed WorkUpper reads per wire".into());
    }

    let mut occurrence_keys=BTreeSet::new();
    let mut family_wires=BTreeSet::new();
    let mut counts=[0usize;4];
    let mut joined=Vec::with_capacity(4*C512D_WORK_BITS);
    for &operand in active {
        let owner=operand.wire/C512_WIRE_WIDTH;
        if !C512D_WORK_D_OWNERS.contains(&owner) {continue;}
        let side_active=match operand.side {
            OperandSide::Left=>operand.c1_active||operand.c3_active,
            OperandSide::Right=>operand.c2_active||operand.c3_active,
        };
        if operand.row/C512_ROW_STRIDE!=C512_CONSUMER_OWNER||!side_active {
            return Err("C512d C509 Work ROW owner or active side".into());
        }
        let local=operand.wire%C512_WIRE_WIDTH;
        let (group,family,value)=match (owner,operand.relation) {
            (845_885,C509Relation::Ordinary(Relation::DaaLane(2)))
                if (C512D_WORK_D_LOCAL..C512D_WORK_D_LOCAL+C512D_WORK_BITS).contains(&local) =>
                (0,C512dWorkFamily::WorkD{owner},d0[local-C512D_WORK_D_LOCAL]),
            (845_886,C509Relation::Ordinary(Relation::DaaLane(2)))
                if (C512D_WORK_D_LOCAL..C512D_WORK_D_LOCAL+C512D_WORK_BITS).contains(&local) =>
                (1,C512dWorkFamily::WorkD{owner},d1[local-C512D_WORK_D_LOCAL]),
            (845_886,C509Relation::Score(context)) if context<2
                &&(C512D_WORK_UPPER_LOCAL..C512D_WORK_UPPER_LOCAL+C512D_WORK_BITS).contains(&local) =>
                (2+context,C512dWorkFamily::WorkUpper{context},
                    upper[local-C512D_WORK_UPPER_LOCAL]),
            _=>return Err("C512d foreign Work operand family/context/coordinate".into()),
        };
        let side=match operand.side{OperandSide::Left=>0u8,OperandSide::Right=>1u8};
        if !occurrence_keys.insert((operand.occurrence,side))
            ||!family_wires.insert((group,operand.wire)) {
            return Err("C512d duplicate Work occurrence or wire, including zero".into());
        }
        counts[group]+=1;
        joined.push(C512dWorkJoinedRead{operand,family,value});
    }
    if counts!=[C512D_WORK_BITS;4]||joined.len()!=4*C512D_WORK_BITS {
        return Err("C512d exact 896 active Work occurrences".into());
    }
    for (group,owner,local) in [
        (0,C512D_WORK_D_OWNERS[0],C512D_WORK_D_LOCAL),
        (1,C512D_WORK_D_OWNERS[1],C512D_WORK_D_LOCAL),
        (2,C512D_WORK_UPPER_OWNER,C512D_WORK_UPPER_LOCAL),
        (3,C512D_WORK_UPPER_OWNER,C512D_WORK_UPPER_LOCAL),
    ] {
        let base=owner*C512_WIRE_WIDTH+local;
        if (0..C512D_WORK_BITS).any(|bit|!family_wires.contains(&(group,base+bit))) {
            return Err("C512d missing physical Work coordinate occurrence".into());
        }
    }
    Ok(joined)
}

/// The occurrence matcher closes the read geometry. Physical authority is
/// supplied separately, once per occurrence, by the selector's actual opaque
/// endpoint tokens. Equal projection values cannot replace this callback.
fn c512d_require_work_tree_claims(
    joined:&[C512dWorkJoinedRead],
    mut checked_endpoint:impl FnMut(usize)->Result<(
        crate::packed_owner_assembly::NativePhysicalAuthor,Fr,
    ),String>,
)->Result<[usize;4],String> {
    use crate::header_daa_row_placement::{C509Relation,Relation};
    use crate::packed_owner_assembly::NativePhysicalAuthor;
    if joined.len()!=4*C512D_WORK_BITS {
        return Err("C512j exact 896 Work claim reads required".into());
    }
    let mut counts=[0usize;4];
    for read in joined {
        let (group,owner,local)=match (read.family,read.operand.relation) {
            (C512dWorkFamily::WorkD{owner},C509Relation::Ordinary(Relation::DaaLane(2)))
                if C512D_WORK_D_OWNERS.contains(&owner) =>
                (usize::from(owner==C512D_WORK_D_OWNERS[1]),owner,C512D_WORK_D_LOCAL),
            (C512dWorkFamily::WorkUpper{context},C509Relation::Score(score_context))
                if context<2 && context==score_context =>
                (2+context,C512D_WORK_UPPER_OWNER,C512D_WORK_UPPER_LOCAL),
            _=>return Err("C512j Work claim read family/context".into()),
        };
        if read.operand.wire/C512_WIRE_WIDTH!=owner
            || !(local..local+C512D_WORK_BITS).contains(
                &(read.operand.wire%C512_WIRE_WIDTH)) {
            return Err("C512j Work claim read source owner/coordinate".into());
        }
        let (author,value)=checked_endpoint(read.operand.wire)?;
        if author!=NativePhysicalAuthor::Tree || value!=Fr::from(read.value as u64) {
            return Err("C512j actual Tree endpoint author/value differs from Work read".into());
        }
        counts[group]+=1;
    }
    if counts!=[C512D_WORK_BITS;4] {
        return Err("C512j exact four Work claim read families".into());
    }
    Ok(counts)
}

/// Count every foreign read of either Work endpoint window, regardless of
/// relation or source owner. The narrow matcher may only claim these closed
/// when its 896 matched and token-checked reads cover this entire demand.
fn c512d_require_no_foreign_work_open(
    active:&[crate::header_daa_row_placement::C509ActiveOperand], joined_len:usize,
)->Result<(),String> {
    let foreign=active.iter().filter(|operand| {
        let owner=operand.wire/C512_WIRE_WIDTH;
        let local=operand.wire%C512_WIRE_WIDTH;
        owner!=C512_CONSUMER_OWNER &&
            ((C512D_WORK_D_LOCAL..C512D_WORK_D_LOCAL+C512D_WORK_BITS).contains(&local)
            ||(C512D_WORK_UPPER_LOCAL..C512D_WORK_UPPER_LOCAL+C512D_WORK_BITS).contains(&local))
    }).count();
    if foreign!=4*C512D_WORK_BITS || joined_len!=foreign {
        return Err("C512d foreign Work-D/Upper active demand remains open".into());
    }
    Ok(())
}

fn c512d_require_work_parent(
    candidate:&crate::packed_owner_assembly::HeaderSourceBinding,
    c509:&crate::packed_owner_assembly::HeaderSourceBinding,
    source:&crate::packed_owner_assembly::HeaderSourceBinding,
    parent:&crate::h21_work_local_source::Parent,owner:usize,
    root:[u8;32],total:[u8;28],cut:&[u8],headers:u64,slots:usize,
)->Result<(),String> {
    if !C512D_WORK_D_OWNERS.contains(&owner)||owner>=slots
        ||candidate.owner()!=C512_CONSUMER_OWNER||candidate!=c509
        ||source.owner()!=owner||source.profile()!=candidate.profile()
        ||!candidate.matches_sink(root,total,candidate.profile(),cut,C512_CONSUMER_OWNER)
        ||!source.matches_sink(root,total,candidate.profile(),cut,owner)
        ||parent.root!=root||parent.total!=total||parent.profile!=candidate.profile()
        ||parent.cut.as_slice()!=cut||parent.headers!=headers||parent.slots!=slots {
        return Err("C512d Work source/consumer parent, owner, or layout".into());
    }
    Ok(())
}

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
struct C512PreviousRJoinedRead {
    operand: crate::header_daa_row_placement::C509ActiveOperand,
    context: usize,
    value: bool,
}

/// Bind the active C509 operands to their typed Score-relation reads without
/// consulting a frame, packed row, or physical-author census.
fn c512_join_previous_r_reads(
    active_operands: &[crate::header_daa_row_placement::C509ActiveOperand],
    reads: &[(usize,crate::packed_owner_assembly::ScoreRelationReadAuthor,Fr)],
)->Result<Vec<C512PreviousRJoinedRead>,String> {
    use crate::header_daa_row_placement::{C509Relation,OperandSide};
    use crate::packed_owner_assembly::ScoreRelationReadAuthor;

    let layout=crate::origin_score::Layout::new();
    if layout.r.start!=1_318||layout.r.end!=1_543
        ||layout.r.end-layout.r.start!=C512_PREVIOUS_R_BITS {
        return Err("C512 PreviousR exact Score-R coordinate range".into());
    }
    let mut expected=BTreeSet::new();
    for context in 0..2 {
        let base=C512_PREVIOUS_OWNER.checked_mul(C512_WIRE_WIDTH)
            .and_then(|base|base.checked_add(SCORE_X[context]))
            .and_then(|base|base.checked_add(layout.r.start))
            .ok_or("C512 PreviousR expected wire overflow")?;
        for bit in 0..C512_PREVIOUS_R_BITS {
            expected.insert((context,base.checked_add(bit)
                .ok_or("C512 PreviousR expected coordinate overflow")?));
        }
    }

    let mut active_by_wire=BTreeMap::new();
    let mut active_occurrences=BTreeSet::new();
    for operand in active_operands {
        let owner=operand.wire/C512_WIRE_WIDTH;
        if owner!=C512_PREVIOUS_OWNER { continue; }
        let context=match operand.relation {
            C509Relation::Score(context)=>context,
            _=>return Err("C512 PreviousR active operand outside Score relation".into()),
        };
        if context>=2||!expected.contains(&(context,operand.wire)) {
            return Err("C512 PreviousR active context/owner/R coordinate".into());
        }
        let side=match operand.side { OperandSide::Left=>0u8,OperandSide::Right=>1u8 };
        if !active_occurrences.insert((operand.occurrence,side)) {
            return Err("C512 duplicate PreviousR active occurrence".into());
        }
        if active_by_wire.insert((context,operand.wire),*operand).is_some() {
            return Err("C512 duplicate PreviousR active wire".into());
        }
    }
    if active_by_wire.len()!=2*C512_PREVIOUS_R_BITS
        ||(0..2).any(|context|active_by_wire.keys()
            .filter(|(found_context,_)|*found_context==context).count()!=C512_PREVIOUS_R_BITS) {
        return Err("C512 exact active PreviousR occurrence census".into());
    }

    let mut typed_by_wire=BTreeMap::new();
    for &(wire,author,value) in reads {
        let expected_wire=expected.iter().any(|(_,expected_wire)|*expected_wire==wire);
        let author_targets_owner=matches!(author,
            ScoreRelationReadAuthor::PreviousR{owner:C512_PREVIOUS_OWNER,..});
        if !expected_wire&&!author_targets_owner { continue; }
        let (context,owner)=match author {
            ScoreRelationReadAuthor::PreviousR{context,owner}=>(context,owner),
            _=>return Err("C512 PreviousR typed Score-read author".into()),
        };
        if owner!=C512_PREVIOUS_OWNER||context>=2||!expected.contains(&(context,wire)) {
            return Err("C512 PreviousR typed owner/context/R coordinate".into());
        }
        let bit=if value.is_zero(){false}else if value.is_one(){true}
            else{return Err("C512 PreviousR typed read is not Boolean".into());};
        if typed_by_wire.insert((context,wire),bit).is_some() {
            return Err("C512 duplicate PreviousR typed Score read".into());
        }
    }
    if typed_by_wire.len()!=2*C512_PREVIOUS_R_BITS
        ||(0..2).any(|context|typed_by_wire.keys()
            .filter(|(found_context,_)|*found_context==context).count()!=C512_PREVIOUS_R_BITS) {
        return Err("C512 exact typed PreviousR read census".into());
    }

    let mut joined=Vec::with_capacity(2*C512_PREVIOUS_R_BITS);
    for (context,wire) in expected {
        let operand=active_by_wire.remove(&(context,wire))
            .ok_or("C512 missing active PreviousR occurrence")?;
        let value=typed_by_wire.remove(&(context,wire))
            .ok_or("C512 missing typed PreviousR Score read")?;
        joined.push(C512PreviousRJoinedRead{operand,context,value});
    }
    if !active_by_wire.is_empty()||!typed_by_wire.is_empty() {
        return Err("C512 trailing PreviousR occurrence/read".into());
    }
    Ok(joined)
}

fn c512_require_shared_binding(
    candidate_binding:&crate::packed_owner_assembly::HeaderSourceBinding,
    c509_binding:&crate::packed_owner_assembly::HeaderSourceBinding,
    physical_binding:&crate::packed_owner_assembly::HeaderSourceBinding,
    root:[u8;32],total:[u8;28],cut:&[u8],
)->Result<(),String> {
    let profile=candidate_binding.profile();
    if candidate_binding.owner()!=C512_CONSUMER_OWNER
        ||candidate_binding!=c509_binding
        ||physical_binding.owner()!=C512_PREVIOUS_OWNER
        ||physical_binding.profile()!=profile
        ||!candidate_binding.matches_sink(root,total,profile,cut,C512_CONSUMER_OWNER)
        ||!physical_binding.matches_sink(root,total,profile,cut,C512_PREVIOUS_OWNER) {
        return Err("C512 source/consumer parent, candidate, owner, or layout binding".into());
    }
    Ok(())
}

fn c512_require_physical_score_read(
    joined:&C512PreviousRJoinedRead,
    context:usize,
    wire:usize,
    author:crate::packed_owner_assembly::Bank53TypedAuthor,
    value:bool,
)->Result<(),String> {
    use crate::packed_owner_assembly::{Bank53TypedAuthor,ScoreReplayAuthor};
    let expected=Bank53TypedAuthor::Score(ScoreReplayAuthor{
        context:joined.context,origin:845_760,previous_owner:845_758,
        max_owner:844_670,cap_owner:C512_PREVIOUS_OWNER,
    });
    if context!=joined.context||wire!=joined.operand.wire||author!=expected
        ||value!=joined.value {
        return Err("C512 physical PreviousR owner/context/R coordinate/value".into());
    }
    Ok(())
}

const C512H_COUNTS:[usize;6]=[729_148,450,448,224,224,448];
const C512H_MAX_OWNER:usize=844_798;
const C512H_MAX_LOCAL:[usize;2]=[999_424,1_000_097];

/// The operand vector retains occurrence, relation, ROW, side and source wire.
/// These small records retain physical family/author and value at the same index.
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
struct C512hReadTag { family:u8, author:u8, value:bool }

fn c512h_occurrence_key(operand:&crate::header_daa_row_placement::C509ActiveOperand)
    ->(usize,u8) {
    use crate::header_daa_row_placement::OperandSide;
    (operand.occurrence,match operand.side {OperandSide::Left=>0,OperandSide::Right=>1})
}

fn c512h_family(operand:&crate::header_daa_row_placement::C509ActiveOperand)
    ->Result<(usize,usize),String> {
    use crate::header_daa_row_placement::{C509Relation,Relation,OperandSide};
    let owner=operand.wire/C512_WIRE_WIDTH;
    let local=operand.wire%C512_WIRE_WIDTH;
    let active=match operand.side {
        OperandSide::Left=>(operand.c1_active||operand.c3_active)&&!operand.c2_active,
        OperandSide::Right=>(operand.c2_active||operand.c3_active)&&!operand.c1_active,
    };
    if operand.row/C512_ROW_STRIDE!=C512_CONSUMER_OWNER || !active {
        return Err("C512h active occurrence ROW/side/flags".into());
    }
    match (owner,operand.relation) {
        (C512_CONSUMER_OWNER,_)=>Ok((0,0)),
        (C512_PREVIOUS_OWNER,C509Relation::Score(context)) if context<2
            && (SCORE_X[context]+1_318..SCORE_X[context]+1_543).contains(&local)=>Ok((1,context)),
        (C512H_MAX_OWNER,C509Relation::Ordinary(Relation::Scheduled(
            Writer::Cap{context,origin}))) if context<2 && origin==845_888
            && (C512H_MAX_LOCAL[context]..C512H_MAX_LOCAL[context]+224).contains(&local)=>Ok((2,context)),
        (845_885,C509Relation::Ordinary(Relation::DaaLane(2)))
            if (C512D_WORK_D_LOCAL..C512D_WORK_D_LOCAL+224).contains(&local)=>Ok((3,0)),
        (845_886,C509Relation::Ordinary(Relation::DaaLane(2)))
            if (C512D_WORK_D_LOCAL..C512D_WORK_D_LOCAL+224).contains(&local)=>Ok((4,0)),
        (845_886,C509Relation::Score(context)) if context<2
            && (C512D_WORK_UPPER_LOCAL..C512D_WORK_UPPER_LOCAL+224).contains(&local)=>Ok((5,context)),
        _=>Err("C512h unknown physical source owner/relation/context/coordinate".into()),
    }
}

/// Private core permits small data-only fixtures. Only the wrapper below is
/// used by the native selector, with the immutable full occurrence census.
fn c512h_join_core(
    active:&[crate::header_daa_row_placement::C509ActiveOperand], expected:[usize;6],
    mut read:impl FnMut(&crate::header_daa_row_placement::C509ActiveOperand,usize,usize)
        ->Result<(u8,bool),String>,
)->Result<Vec<C512hReadTag>,String> {
    if active.len()!=expected.iter().sum::<usize>() {
        return Err("C512h exact active physical read count".into());
    }
    let mut counts=[0usize;6];let mut previous=None;
    let mut tags=Vec::with_capacity(active.len());
    for operand in active {
        let key=c512h_occurrence_key(operand);
        if previous.is_some_and(|previous|previous>=key) {
            return Err("C512h duplicate or reordered active occurrence, including zero".into());
        }
        previous=Some(key);
        let (family,context)=c512h_family(operand)?;
        let (author,value)=read(operand,family,context)?;
        if !match family {0=>author<4,1=>author==4,2=>author==5,_=>author==6} {
            return Err("C512h physical author does not match source family".into());
        }
        counts[family]+=1;
        tags.push(C512hReadTag{family:family as u8,author,value});
    }
    if counts!=expected {return Err("C512h complete six-family occurrence partition".into());}
    Ok(tags)
}

fn c512h_join_physical_reads(
    active:&[crate::header_daa_row_placement::C509ActiveOperand],
    read:impl FnMut(&crate::header_daa_row_placement::C509ActiveOperand,usize,usize)
        ->Result<(u8,bool),String>,
)->Result<Vec<C512hReadTag>,String> {
    c512h_join_core(active,C512H_COUNTS,read)
}

fn c512h_require_source_binding(
    candidate:&crate::packed_owner_assembly::HeaderSourceBinding,
    source:&crate::packed_owner_assembly::HeaderSourceBinding,owner:usize,
    root:[u8;32],total:[u8;28],cut:&[u8],
)->Result<(),String> {
    if ![845_887,845_759,844_798,845_885,845_886].contains(&owner)
        || !candidate.matches_sink(root,total,candidate.profile(),cut,845_887)
        || !source.matches_sink(root,total,candidate.profile(),cut,owner) {
        return Err("C512h source binding owner/root/total/profile/cut/layout".into());
    }
    Ok(())
}

// This is a capability domain, not an equal-value lookup. The full-owner
// domains require the actual checked regular/C374 census; the two other
// domains are limited to their opaque MAX and Tree endpoint writers.
fn c514_source_family(wire:usize)->Result<usize,String> {
    let owner=wire/C512_WIRE_WIDTH;let local=wire%C512_WIRE_WIDTH;
    match owner {
        845_887=>Ok(0),
        845_759=>Ok(1),
        844_798 if (999_424..1_000_097).contains(&local)
            ||(1_000_097..1_000_770).contains(&local)=>Ok(2),
        845_885|845_886 if (987_450..987_674).contains(&local)
            ||(987_674..987_898).contains(&local)=>Ok(3+usize::from(owner==845_886)),
        _=>Err(format!("no checked native capability source_owner={owner} local={local}")),
    }
}

fn c514_qualify_native_demands(
    demands:&[crate::sparse_stream_roster::C514Demand],
    bindings:[&crate::packed_owner_assembly::HeaderSourceBinding;5],
    root:[u8;32],total:[u8;28],cut:&[u8],
)->Result<(),String> {
    for (index,owner) in [845_887,845_759,844_798,845_885,845_886].into_iter().enumerate() {
        c512h_require_source_binding(bindings[0],bindings[index],owner,root,total,cut)
            .map_err(|error|format!("C514 source_owner={owner} {error}"))?;
    }
    let mut missing=0usize;
    let mut inventory=String::new();
    let mut truncated=false;
    for demand in demands {
        if let Err(error)=c514_source_family(demand.coordinate) {
            missing+=1;
            let entry=format!("coordinate={} term_index={} side={:?} {error};",
                demand.coordinate,demand.term_index,demand.side);
            if inventory.len()+entry.len()<=32*1024 {
                inventory.push_str(&entry);
            } else {truncated=true;}
        }
    }
    if missing!=0 {
        return Err(format!("C514 source gap count={missing} inventory_complete={} {inventory}",
            !truncated));
    }
    Ok(())
}

fn c514_native_mode_allowed(c512h:bool,modes:[bool;17])->bool {
    c512h&&modes==[true,true,false,false,false,false,false,false,false,
        false,false,false,false,false,false,false,false]
}

#[test]
fn c514_native_capability_qualification_no_frame() {
    use crate::packed_owner_assembly::HeaderSourceBinding;
    use crate::sparse_stream_roster::{C514Demand,C514DemandSide};
    let (root,total,profile,cut)=([1u8;32],[2u8;28],[3u8;32],vec![4u8;8]);
    let sources=[845_887,845_759,844_798,845_885,845_886].map(|owner|
        HeaderSourceBinding::from_sink_for_test(root,total,profile,cut.clone(),owner));
    let bindings=std::array::from_fn(|index|&sources[index]);
    let zero=C514Demand{term_index:7,side:C514DemandSide::LeftEven,
        coordinate:845_887*C512_WIRE_WIDTH};
    // Qualification is value-independent: a demanded authored zero is still
    // present, and a missing neighbour cannot be omitted on account of zero.
    c514_qualify_native_demands(&[zero],bindings,root,total,&cut).unwrap();
    for (owner,local) in [(845_759,0),(844_798,999_424),(844_798,1_000_769),
        (845_885,987_450),(845_886,987_897)] {
        let demand=C514Demand{coordinate:owner*C512_WIRE_WIDTH+local,..zero};
        c514_qualify_native_demands(&[demand],bindings,root,total,&cut).unwrap();
    }
    for (owner,local) in [(845_888,0),(844_798,999_423),(844_798,1_000_770),
        (845_885,987_449),(845_886,987_898)] {
        let demand=C514Demand{coordinate:owner*C512_WIRE_WIDTH+local,..zero};
        let error=c514_qualify_native_demands(&[zero,demand],bindings,root,total,&cut).unwrap_err();
        assert!(error.contains(&format!("coordinate={}",demand.coordinate)));
        assert!(error.contains("term_index=7 side=LeftEven"));
        assert!(error.contains(&format!("source_owner={owner}")));
    }
    let first=C514Demand{term_index:11,side:C514DemandSide::LeftEven,
        coordinate:844_798*C512_WIRE_WIDTH+999_423};
    let second=C514Demand{term_index:19,side:C514DemandSide::Right,
        coordinate:845_885*C512_WIRE_WIDTH+987_898};
    let error=c514_qualify_native_demands(&[zero,first,second],bindings,root,total,&cut)
        .unwrap_err();
    assert!(error.contains("source gap count=2 inventory_complete=true"));
    assert!(error.contains(&format!("coordinate={} term_index=11 side=LeftEven",first.coordinate)));
    assert!(error.contains(&format!("coordinate={} term_index=19 side=Right",second.coordinate)));
    for index in 0..5 {
        for field in 0..6 {
            let detached=sources[index].mutated_field_for_test(field);
            let mut wrong=bindings;wrong[index]=&detached;
            assert!(c514_qualify_native_demands(&[zero],wrong,root,total,&cut).is_err(),
                "every source must retain owner/root/total/profile/cut/layout");
        }
    }
    // Exercise source demand timing, without using the polynomial as an
    // oracle: both members of an active all-zero pair must reach the reader.
    use crate::sparse_stream_roster::{EdgeTerm,c514_selected_u0_contribution};
    let edge=EdgeTerm{source_slot:845_887,family_row:0,term:crate::sparse::Term{
        row:845_887*C512_ROW_STRIDE,gate:crate::gkr::Gate{
            left:zero.coordinate,right:0,c0:Fr::zero(),c1:Fr::one(),
            c2:Fr::zero(),c3:Fr::zero()}}};
    let qualified=std::cell::Cell::new(false);let mut reads=Vec::new();
    let r=(2u64..42).map(Fr::from).collect::<Vec<_>>();
    c514_selected_u0_contribution(&[edge.clone()],&r,20,21,19,0,&[19],|demands|{
        assert_eq!(demands.len(),2);
        c514_qualify_native_demands(demands,bindings,root,total,&cut)?;
        qualified.set(true);Ok(())
    },|wire|{assert!(qualified.get());reads.push(wire);Ok(false)}).unwrap();
    assert_eq!(reads,vec![zero.coordinate,zero.coordinate+1]);
    let mut missing=edge;missing.term.gate.left=845_885*C512_WIRE_WIDTH+987_898;
    reads.clear();qualified.set(false);
    assert!(c514_selected_u0_contribution(&[missing],&r,20,21,19,0,&[19],|demands|
        c514_qualify_native_demands(demands,bindings,root,total,&cut),
        |wire|{reads.push(wire);Ok(false)}).is_err());
    assert!(reads.is_empty(),"all demands must qualify before even an authored-zero read");
}

#[test]
fn c514_native_mode_exclusions_no_frame() {
    let exact=[true,true,false,false,false,false,false,false,false,
        false,false,false,false,false,false,false,false];
    assert!(c514_native_mode_allowed(true,exact));
    assert!(!c514_native_mode_allowed(false,exact));
    for index in 0..exact.len() {
        let mut wrong=exact;wrong[index]=!wrong[index];
        assert!(!c514_native_mode_allowed(true,wrong));
    }
}

/// Reject foreign or off-range typed records even when a narrower matcher
/// would ignore them and their value is zero.
fn c512h_cap_value_range(context:usize)->Option<std::ops::Range<usize>> {
    let q=crate::certified_modern_cap::Layout::new().q;
    // H21 Score aliases only the canonical 65-bit q rail of each local Cap.
    if context>=2 || q!=(740..805) {return None;}
    Some(CAP_X[context]+q.start..CAP_X[context]+q.end)
}

fn c512h_check_typed_score_sources(
    reads:&[(usize,crate::packed_owner_assembly::ScoreRelationReadAuthor,Fr)],
)->Result<(),String> {
    use crate::packed_owner_assembly::ScoreRelationReadAuthor;
    for &(wire,author,value) in reads {
        if !(value.is_zero()||value.is_one()) {return Err("C512h nonboolean typed Score read".into());}
        let owner=wire/C512_WIRE_WIDTH;let local=wire%C512_WIRE_WIDTH;
        let valid=match author {
            ScoreRelationReadAuthor::PreviousR{context,owner:source}=>context<2
                && source==C512_PREVIOUS_OWNER && owner==source
                && (SCORE_X[context]+1_318..SCORE_X[context]+1_543).contains(&local),
            ScoreRelationReadAuthor::WorkUpper{owner:source,height}=>source==845_886
                && owner==source && height==845_888
                && (C512D_WORK_UPPER_LOCAL..C512D_WORK_UPPER_LOCAL+224).contains(&local),
            ScoreRelationReadAuthor::Cap{context,origin,max_owner,cap_owner}=>context<2
                && origin==845_888 && max_owner==844_798 && cap_owner==845_887
                && owner==845_887
                && c512h_cap_value_range(context).is_some_and(|range|range.contains(&local)),
        };
        if !valid {return Err("C512h typed Score source owner/height/context/coordinate".into());}
    }
    Ok(())
}

fn c512h_check_typed_cap_census(
    reads:&[(usize,crate::packed_owner_assembly::ScoreRelationReadAuthor,Fr)],
)->Result<(),String> {
    use crate::packed_owner_assembly::ScoreRelationReadAuthor;
    c512h_check_typed_score_sources(reads)?;
    let mut claimed=[[false;65];2];
    for &(wire,author,_) in reads {
        if let ScoreRelationReadAuthor::Cap{context,..}=author {
            let range=c512h_cap_value_range(context).ok_or("C512h canonical local Cap q rail")?;
            let bit=wire%C512_WIRE_WIDTH-range.start;
            if claimed[context][bit] {return Err("C512h duplicate typed local Cap q bit, including zero".into());}
            claimed[context][bit]=true;
        }
    }
    if claimed.iter().flatten().any(|claimed|!*claimed) {
        return Err("C512h exact65 typed local Cap q bits per context".into());
    }
    Ok(())
}

fn c512h_check_selected_score_reads(
    selected:impl Iterator<Item=(usize,crate::packed_owner_assembly::OpenScoredReadAuthor,Fr)>,
    typed:&[(usize,crate::packed_owner_assembly::ScoreRelationReadAuthor,Fr)],
)->Result<(),String> {
    use crate::packed_owner_assembly::{ScoreRelationReadAuthor,OpenScoredReadAuthor};
    c512h_check_typed_score_sources(typed)?;
    let key=|wire,author|match author {
        ScoreRelationReadAuthor::PreviousR{context,..}=>Some((0u8,context,wire)),
        ScoreRelationReadAuthor::WorkUpper{..}=>Some((1u8,0,wire)),
        ScoreRelationReadAuthor::Cap{..}=>None,
    };
    let mut remaining=BTreeMap::<(u8,usize,usize),(bool,usize)>::new();
    for &(wire,author,value) in typed {
        let Some(key)=key(wire,author) else {continue;};
        let bit=value.is_one();
        if let Some((previous,count))=remaining.get_mut(&key) {
            if *previous!=bit {return Err("C512h conflicting typed Score value".into());}
            *count+=1;
        } else {remaining.insert(key,(bit,1));}
    }
    for (wire,author,value) in selected {
        let author=match author {
            OpenScoredReadAuthor::PreviousR{context,owner}=>ScoreRelationReadAuthor::PreviousR{context,owner},
            OpenScoredReadAuthor::WorkUpper{owner,height}=>ScoreRelationReadAuthor::WorkUpper{owner,height},
            _=>continue,
        };
        c512h_check_typed_score_sources(&[(wire,author,value)])?;
        let (expected,count)=remaining.get_mut(&key(wire,author).expect("selected Score source key"))
            .ok_or("C512h extra selected PreviousR/Upper record")?;
        if *count==0 || *expected!=value.is_one() {
            return Err("C512h selected PreviousR/Upper multiplicity/value".into());
        }
        *count-=1;
    }
    if remaining.values().any(|(_,count)|*count!=0) {
        return Err("C512h missing selected PreviousR/Upper record".into());
    }
    Ok(())
}

fn c512h_typed_max_core(
    reads:impl Iterator<Item=(usize,crate::packed_owner_assembly::OpenScoredReadAuthor,Fr)>,
    per_context:usize,
)->Result<BTreeMap<(usize,usize),bool>,String> {
    use crate::packed_owner_assembly::OpenScoredReadAuthor;
    let mut values=BTreeMap::new();let mut counts=[0usize;2];
    for (wire,author,value) in reads {
        if wire/C512_WIRE_WIDTH!=C512H_MAX_OWNER
            && !matches!(author,OpenScoredReadAuthor::Max{..}) {continue;}
        let OpenScoredReadAuthor::Max{context,end}=author else {
            return Err("C512h typed MAX source kind".into());
        };
        if context>=2 || end!=844_800 || wire/C512_WIRE_WIDTH!=C512H_MAX_OWNER
            || !(C512H_MAX_LOCAL[context]..C512H_MAX_LOCAL[context]+224)
                .contains(&(wire%C512_WIRE_WIDTH)) {
            return Err("C512h typed MAX owner/context/end/coordinate".into());
        }
        let bit=if value.is_zero(){false}else if value.is_one(){true}
            else{return Err("C512h nonboolean typed MAX read".into());};
        if values.insert((context,wire),bit).is_some() {
            return Err("C512h duplicate typed MAX read, including zero".into());
        }
        counts[context]+=1;
    }
    if counts!=[per_context;2] {return Err("C512h exact typed MAX census".into());}
    Ok(values)
}

fn c512h_require_max_read(context:usize,wire:usize,typed:&BTreeMap<(usize,usize),bool>,
    author:MaxReplayAuthor,value:bool)->Result<bool,String> {
    if context>=2 || author!=MaxReplayAuthor::Scheduled(Writer::Max{context,end:844_800})
        || typed.get(&(context,wire))!=Some(&value) {
        return Err("C512h actual scheduled MAX author/context/end/value".into());
    }
    Ok(value)
}

#[test]
fn c512h_small_physical_partition_and_typed_mutants_no_frame() {
    use crate::header_daa_row_placement::{C509ActiveOperand,C509Relation,Relation,OperandSide};
    use crate::packed_owner_assembly::{OpenScoredReadAuthor,ScoreRelationReadAuthor,HeaderSourceBinding};
    let mut active=Vec::new();
    let mut add=|relation,owner,local| {
        let occurrence=active.len();
        active.push(C509ActiveOperand{occurrence,relation,
            row:C512_CONSUMER_OWNER*C512_ROW_STRIDE+occurrence,
            side:OperandSide::Left,wire:owner*C512_WIRE_WIDTH+local,
            c1_active:true,c2_active:false,c3_active:false});
    };
    add(C509Relation::Ordinary(Relation::Header),845_887,10);
    add(C509Relation::Score(0),845_759,SCORE_X[0]+1_318);
    for context in 0..2 {add(C509Relation::Ordinary(Relation::Scheduled(
        Writer::Cap{context,origin:845_888})),844_798,C512H_MAX_LOCAL[context]);}
    add(C509Relation::Ordinary(Relation::DaaLane(2)),845_885,C512D_WORK_D_LOCAL);
    add(C509Relation::Ordinary(Relation::DaaLane(2)),845_886,C512D_WORK_D_LOCAL);
    for context in 0..2 {add(C509Relation::Score(context),845_886,C512D_WORK_UPPER_LOCAL);}
    drop(add);
    let counts=[1,1,2,1,1,2];
    let honest=|_:&C509ActiveOperand,family:usize,_|Ok((match family {0=>0,1=>4,2=>5,_=>6},false));
    let tags=c512h_join_core(&active,counts,honest).unwrap();
    assert_eq!(tags.len(),8);assert!(tags.iter().all(|tag|!tag.value));
    assert!(tags.iter().all(|tag|match tag.family {0=>tag.author<4,1=>tag.author==4,
        2=>tag.author==5,_=>tag.author==6}));
    let mut right=active.clone();right[0].side=OperandSide::Right;
    right[0].c1_active=false;right[0].c2_active=true;
    c512h_join_core(&right,counts,honest).unwrap();
    right[0].c1_active=true;
    assert!(c512h_join_core(&right,counts,honest).is_err(),"right read cannot carry left-only flags");
    assert!(c512h_join_physical_reads(&active,honest).is_err(),"toy counts cannot enter native wrapper");
    for fault in 0..active.len() {
        let mut missing=active.clone();missing.remove(fault);
        assert!(c512h_join_core(&missing,counts,honest).is_err());
        let mut duplicate=active.clone();duplicate.insert(fault,active[fault]);
        assert!(c512h_join_core(&duplicate,counts,honest).is_err());
        let mut repeated=active.clone();repeated[fault].occurrence=active[0].occurrence;
        if fault>0 {assert!(c512h_join_core(&repeated,counts,honest).is_err());}
        assert!(c512h_join_core(&active,counts,|operand,family,context|
            if operand.occurrence==fault {Err("isolated physical source failure".into())}
            else {honest(operand,family,context)}).is_err());
        assert!(c512h_join_core(&active,counts,|operand,family,context|
            if operand.occurrence==fault {Ok((7,false))}
            else {honest(operand,family,context)}).is_err());
        let mut replaced=active.clone();
        let substitute=if fault==0 {active[1]} else {active[0]};
        replaced[fault].wire=substitute.wire;replaced[fault].relation=substitute.relation;
        assert!(c512h_join_core(&replaced,counts,honest).is_err(),
            "family omission hidden by an extra other-family zero at occurrence {fault}");
    }
    for fault in 0..7 {
        let mut wrong=active.clone();
        match fault {
            0=>wrong[0].row=845_887*C512_WIRE_WIDTH,
            1=>wrong[0].c1_active=false,
            2=>wrong[0].c2_active=true,
            3=>wrong[1].wire-=C512_WIRE_WIDTH,
            4=>wrong[2].relation=C509Relation::Ordinary(Relation::Scheduled(Writer::Cap{context:0,origin:845_889})),
            5=>wrong[4].relation=C509Relation::Ordinary(Relation::DaaLane(1)),
            6=>wrong[6].relation=C509Relation::Score(2),
            _=>unreachable!(),
        }
        assert!(c512h_join_core(&wrong,counts,honest).is_err(),"isolated family/ROW/side fault {fault}");
    }
    let root=[1;32];let total=[2;28];let profile=[3;32];let cut=vec![4,5];
    let candidate=HeaderSourceBinding::from_sink_for_test(root,total,profile,cut.clone(),845_887);
    for owner in [845_887,845_759,844_798,845_885,845_886] {
        let source=HeaderSourceBinding::from_sink_for_test(root,total,profile,cut.clone(),owner);
        c512h_require_source_binding(&candidate,&source,owner,root,total,&cut).unwrap();
        for field in 0..6 {
            assert!(c512h_require_source_binding(&candidate,&source.mutated_field_for_test(field),
                owner,root,total,&cut).is_err());
            assert!(c512h_require_source_binding(&candidate.mutated_field_for_test(field),&source,
                owner,root,total,&cut).is_err());
        }
    }
    let previous=ScoreRelationReadAuthor::PreviousR{context:0,owner:845_759};
    let previous_wire=845_759*C512_WIRE_WIDTH+SCORE_X[0]+1_318;
    c512h_check_typed_score_sources(&[(previous_wire,previous,Fr::zero())]).unwrap();
    for (wire,author) in [
        (previous_wire-C512_WIRE_WIDTH,ScoreRelationReadAuthor::PreviousR{context:0,owner:845_758}),
        (previous_wire+225,previous),
        (845_885*C512_WIRE_WIDTH+C512D_WORK_UPPER_LOCAL,
            ScoreRelationReadAuthor::WorkUpper{owner:845_885,height:845_887}),
        (845_886*C512_WIRE_WIDTH+C512D_WORK_UPPER_LOCAL,
            ScoreRelationReadAuthor::WorkUpper{owner:845_886,height:845_887}),
    ] {assert!(c512h_check_typed_score_sources(&[(wire,author,Fr::zero())]).is_err());}
    let upper_wire=845_886*C512_WIRE_WIDTH+C512D_WORK_UPPER_LOCAL;
    let typed_score=vec![(previous_wire,previous,Fr::zero()),
        (upper_wire,ScoreRelationReadAuthor::WorkUpper{owner:845_886,height:845_888},Fr::zero()),
        (upper_wire,ScoreRelationReadAuthor::WorkUpper{owner:845_886,height:845_888},Fr::zero())];
    let selected_score=vec![(previous_wire,OpenScoredReadAuthor::PreviousR{context:0,owner:845_759},Fr::zero()),
        (upper_wire,OpenScoredReadAuthor::WorkUpper{owner:845_886,height:845_888},Fr::zero()),
        (upper_wire,OpenScoredReadAuthor::WorkUpper{owner:845_886,height:845_888},Fr::zero())];
    c512h_check_selected_score_reads(selected_score.iter().copied(),&typed_score).unwrap();
    let mut conflicting_score=typed_score.clone();conflicting_score[2].2=Fr::one();
    assert!(c512h_check_selected_score_reads(selected_score.iter().copied(),&conflicting_score).is_err(),
        "repeated typed Upper wire cannot carry conflicting values");
    for fault in 0..7 {
        let mut wrong=selected_score.clone();
        match fault {
            0=>{wrong.pop();},1=>wrong.push(selected_score[1]),
            2=>wrong.push((previous_wire-C512_WIRE_WIDTH,
                OpenScoredReadAuthor::PreviousR{context:0,owner:845_758},Fr::zero())),
            3=>wrong[1].1=OpenScoredReadAuthor::WorkUpper{owner:845_886,height:845_887},
            4=>wrong[0].0+=225,5=>wrong[0].2=Fr::one(),6=>wrong[0].2=Fr::from(2u64),
            _=>unreachable!(),
        }
        assert!(c512h_check_selected_score_reads(wrong.into_iter(),&typed_score).is_err(),
            "isolated selected Score record fault {fault}");
    }
    let max=(0..2).map(|context|(844_798*C512_WIRE_WIDTH+C512H_MAX_LOCAL[context],
        OpenScoredReadAuthor::Max{context,end:844_800},Fr::zero())).collect::<Vec<_>>();
    let typed=c512h_typed_max_core(max.iter().copied(),1).unwrap();
    assert!(c512h_typed_max_core(max.iter().copied(),224).is_err());
    for fault in 0..8 {
        let mut wrong=max.clone();
        match fault {
            0=>{wrong.pop();},1=>wrong.push(max[0]),2=>wrong[0].0-=C512_WIRE_WIDTH,
            3=>wrong[0].1=OpenScoredReadAuthor::Max{context:2,end:844_800},
            4=>wrong[0].1=OpenScoredReadAuthor::Max{context:0,end:844_801},
            5=>wrong[0].0+=224,6=>wrong[0].2=Fr::from(2u64),
            7=>wrong[0].1=OpenScoredReadAuthor::PreviousR{context:0,owner:845_759},_=>unreachable!(),
        }
        assert!(c512h_typed_max_core(wrong.into_iter(),1).is_err(),"isolated typed MAX fault {fault}");
    }
    c512h_require_max_read(0,max[0].0,&typed,MaxReplayAuthor::Scheduled(
        Writer::Max{context:0,end:844_800}),false).unwrap();
    for (author,value) in [
        (MaxReplayAuthor::NativeWorkD{height:844_800},false),
        (MaxReplayAuthor::Scheduled(Writer::Max{context:1,end:844_800}),false),
        (MaxReplayAuthor::Scheduled(Writer::Max{context:0,end:844_801}),false),
        (MaxReplayAuthor::Scheduled(Writer::Max{context:0,end:844_800}),true),
    ] {assert!(c512h_require_max_read(0,max[0].0,&typed,author,value).is_err());}
}

#[test]
fn c512h_typed_local_cap_projection_and_census_no_frame() {
    use crate::packed_owner_assembly::ScoreRelationReadAuthor;
    let owner=845_887usize;let base=owner*C512_WIRE_WIDTH;
    let author=|context|ScoreRelationReadAuthor::Cap{context,origin:845_888,
        max_owner:844_798,cap_owner:owner};
    let mut reads=Vec::new();
    for context in 0..2 {
        assert_eq!(c512h_cap_value_range(context),Some(CAP_X[context]+740..CAP_X[context]+805));
        // Literal H21 producer projection, independent of the range helper.
        for bit in 0..65 {reads.push((base+[1_000_770,1_002_818][context]+740+bit,
            author(context),Fr::from((bit%2)as u64)));}
    }
    c512h_check_typed_cap_census(&reads).unwrap();assert_eq!(reads.len(),130);
    let mut offrange=reads.clone();offrange.push((base+7,author(0),Fr::zero()));
    assert!(c512h_check_typed_score_sources(&offrange).is_err(),
        "local owner alone cannot authorize an extra off-range zero Cap record");
    for local in [CAP_X[0]+739,CAP_X[0]+805] {
        assert!(c512h_check_typed_score_sources(&[(base+local,author(0),Fr::zero())]).is_err());
    }
    let mut wrong_context=reads.clone();wrong_context[0].1=author(1);
    assert!(c512h_check_typed_score_sources(&wrong_context).is_err(),
        "context tag must match its physical Cap q cell");
    let mut invalid_context=reads.clone();invalid_context[0].1=author(2);
    assert!(c512h_check_typed_score_sources(&invalid_context).is_err());
    let mut missing_zero=reads.clone();missing_zero.pop();
    assert!(c512h_check_typed_cap_census(&missing_zero).is_err());
    let mut duplicate_zero=reads.clone();duplicate_zero.push(reads[0]);
    assert!(c512h_check_typed_cap_census(&duplicate_zero).is_err());
    let mut swapped_context_cells=reads.clone();
    swapped_context_cells[0].0=base+CAP_X[1]+740;
    assert!(c512h_check_typed_score_sources(&swapped_context_cells).is_err());
}

#[test]
fn c512h_retained_type_sizes_and_capacities_no_frame() {
    use crate::header_daa_row_placement::C509ActiveOperand;
    let active=Vec::<C509ActiveOperand>::with_capacity(8);
    let tags=Vec::<C512hReadTag>::with_capacity(8);
    assert!(std::mem::size_of::<C512hReadTag>()<=4);
    println!("C512H_RETAINED_LAYOUT active_size={} tag_size={} active_len={} active_capacity={} tag_len={} tag_capacity={} full_active_bytes={} full_tag_bytes={} numeric_rows_bytes={} source_custody_not_measured=true whole_job_bound=false",
        std::mem::size_of::<C509ActiveOperand>(),std::mem::size_of::<C512hReadTag>(),
        active.len(),active.capacity(),tags.len(),tags.capacity(),
        730_942*std::mem::size_of::<C509ActiveOperand>(),730_942*std::mem::size_of::<C512hReadTag>(),
        524_288*std::mem::size_of::<Fr>());
}

fn c431_ordered_terms_match<'a,'b>(
    mut expected:impl Iterator<Item=(usize,(crate::header_daa_row_placement::Relation,
        &'a crate::sparse::Term))>,
    mut observed:impl Iterator<Item=(usize,(crate::header_daa_row_placement::Relation,
        &'b crate::sparse::Term))>,
)->bool {
    loop {
        match (expected.next(),observed.next()) {
            (Some((left_ordinal,(left_relation,left_term))),
                Some((right_ordinal,(right_relation,right_term))))
                if left_ordinal==right_ordinal && left_relation==right_relation
                    && left_term==right_term=>{},
            (None,None)=>return true,
            _=>return false,
        }
    }
}

fn c432_ordered_boundary_matches(
    expected:&[(usize,crate::packed_owner_assembly::NativePhysicalAuthor,bool)],
    observed:&[(usize,crate::packed_owner_assembly::NativePhysicalAuthor,bool)],
)->bool {
    expected==observed
}

fn c432_work_d_overlap_matches(expected:&[(usize,bool)],observed:&[(usize,bool)])->bool {
    expected==observed
}

fn integer_word(bits:&[bool],range:std::ops::Range<usize>)->BigUint {
    assert!(range.end<=bits.len());
    range.enumerate().fold(BigUint::from(0u8),|mut value,(bit,local)| {
        if bits[local] {value|=BigUint::from(1u8)<<bit;} value
    })
}

fn phase(label:&str,started:Instant) {
    println!("C187_PHASE label={label} elapsed_s={:.6}",started.elapsed().as_secs_f64());
    std::io::stdout().flush().expect("flush c187 phase");
}

fn calendar()->Vec<(usize,[Option<MaxStep>;2])> {
    // Independent literal endpoint partition, including unequal terminal cuts.
    let mut literal:BTreeMap<usize,[Option<MaxStep>;2]>=BTreeMap::new();
    let mut counts=[0;2];let mut edges=[0;2];
    for (context,terminal) in [(0,1_827_840usize),(1,1_810_842usize)] {
        let mut ends=vec![844_672];
        for start in (844_673..=terminal).step_by(128) {ends.push((start+127).min(terminal));}
        counts[context]=ends.len();edges[context]=ends.len()-1;
        for (index,&end) in ends.iter().enumerate() {
            literal.entry(end-2).or_insert([None;2])[context]=Some(MaxStep {
                end,next:ends.get(index+1).map(|next|next-2)});
        }
    }
    assert_eq!(counts,[7682,7550]);assert_eq!(edges,[7681,7549]);
    let literal:Vec<_>=literal.into_iter().rev().collect();
    assert_eq!(literal.len(),7683);
    assert_eq!(literal.iter().filter(|(_,steps)|steps.iter().all(Option::is_some)).count(),7549);
    assert_eq!(literal,MaxPlan::eligible08().max_calendar());
    assert_eq!(literal.first().unwrap().0,1827838);assert_eq!(literal[1].0,1827710);
    assert_eq!(literal.last().unwrap().0,844670);
    assert_eq!(literal.iter().find(|(owner,_)|*owner==1810814).unwrap().1,
        [Some(MaxStep{end:1810816,next:Some(1810942)}),Some(MaxStep{end:1810816,next:Some(1810840)})]);
    literal
}

fn score_calendar()->Vec<(usize,[Option<(usize,usize)>;2])> {
    // Height-space oracle independent of Prepared::score_spans and stream.next_owner.
    let mut owners:BTreeMap<usize,[Option<(usize,usize)>;2]>=BTreeMap::new();
    for (context,guard) in [(0,1_810_905usize),(1,1_810_842usize)] {
        owners.entry(845_759).or_insert([None;2])[context]=Some((845_760,845_760));
        for first in (845_761..=guard).step_by(128) {
            let last=(first+127).min(guard);
            owners.entry(last-1).or_insert([None;2])[context]=Some((first,last));
        }
    }
    let out:Vec<_>=owners.into_iter().collect();
    assert_eq!(out.len(),7543);
    assert_eq!(out.iter().filter(|(_,roles)|roles[0].is_some()).count(),7542);
    assert_eq!(out.iter().filter(|(_,roles)|roles[1].is_some()).count(),7541);
    assert_eq!(out.first().unwrap().0,845_759);
    assert_eq!(out.last().unwrap().0,1_810_904);
    assert_eq!(out.iter().find(|(o,_)|*o==1_810_841).unwrap().1,
        [None,Some((1_810_753,1_810_842))]);
    assert_eq!(out.iter().find(|(o,_)|*o==1_810_879).unwrap().1,
        [Some((1_810_753,1_810_880)),None]);
    assert_eq!(out.last().unwrap().1,[Some((1_810_881,1_810_905)),None]);
    out
}

#[test]
fn c187_native_score_no_frame_calendar_preflight() {
    let owners=calendar();
    assert_eq!(owners.iter().filter(|(_,steps)|steps[0].is_some_and(|step|step.next.is_none())).count(),1);
    assert_eq!(owners.iter().filter(|(_,steps)|steps[1].is_some_and(|step|step.next.is_none())).count(),1);
    let endpoints=score_calendar();
    assert_eq!(endpoints.iter().filter(|(_,roles)|roles.iter().all(Option::is_some)).count(),7540);
    println!("C187_PREFLIGHT_PASS max_union=7683 score_union=7543 score_roles=15083 score_shared=7540 tails=[25,90] native_execution=false");
}

#[cfg(test)]
#[test]
fn c512b_previous_r_physical_join_isolated_no_frame_mutants() {
    use crate::header_daa_row_placement::{C509ActiveOperand,C509Relation,OperandSide};
    use crate::packed_owner_assembly::{Bank53TypedAuthor,ScoreRelationReadAuthor,ScoreReplayAuthor};
    use crate::packed_owner_assembly::HeaderSourceBinding;

    let layout=crate::origin_score::Layout::new();
    let mut active=Vec::new();
    let mut reads=Vec::new();
    for context in 0..2 {
        let base=C512_PREVIOUS_OWNER*C512_WIRE_WIDTH+SCORE_X[context]+layout.r.start;
        for bit in 0..C512_PREVIOUS_R_BITS {
            let occurrence=context*C512_PREVIOUS_R_BITS+bit;
            let wire=base+bit;
            active.push(C509ActiveOperand{occurrence,
                relation:C509Relation::Score(context),
                row:C512_CONSUMER_OWNER*C512_ROW_STRIDE+occurrence,
                side:OperandSide::Left,wire,c1_active:true,c2_active:false,c3_active:false});
            reads.push((wire,ScoreRelationReadAuthor::PreviousR{
                context,owner:C512_PREVIOUS_OWNER},Fr::from((occurrence%2) as u64)));
        }
    }
    let joined=c512_join_previous_r_reads(&active,&reads).unwrap();
    assert_eq!(joined.len(),450);
    assert_eq!((0..2).map(|context|joined.iter()
        .filter(|read|read.context==context).count()).collect::<Vec<_>>(),vec![225,225]);
    assert_eq!(joined.iter().filter(|read|!read.value).count(),225,
        "authored zero values stay in the joined occurrence census");
    assert_eq!(joined[0].operand.occurrence,0);
    assert_eq!(joined[0].operand.wire,reads[0].0);
    assert!(!joined[0].value);

    let mut missing_active=active.clone();
    missing_active.pop();
    assert!(c512_join_previous_r_reads(&missing_active,&reads).is_err());
    let mut duplicate_active=active.clone();
    duplicate_active.push(active[0]);
    assert!(c512_join_previous_r_reads(&duplicate_active,&reads).is_err());
    let mut wrong_active_owner=active.clone();
    wrong_active_owner[0].wire-=C512_WIRE_WIDTH;
    assert!(c512_join_previous_r_reads(&wrong_active_owner,&reads).is_err());
    let mut wrong_active_context=active.clone();
    wrong_active_context[0].relation=C509Relation::Score(1);
    assert!(c512_join_previous_r_reads(&wrong_active_context,&reads).is_err());
    let mut wrong_active_r=active.clone();
    wrong_active_r[0].wire+=C512_PREVIOUS_R_BITS+50;
    assert!(c512_join_previous_r_reads(&wrong_active_r,&reads).is_err());

    let mut missing_read=reads.clone();
    missing_read.remove(0);
    assert!(c512_join_previous_r_reads(&active,&missing_read).is_err());
    let mut duplicate_read=reads.clone();
    duplicate_read.push(reads[0]);
    assert!(c512_join_previous_r_reads(&active,&duplicate_read).is_err());
    let mut wrong_read_owner=reads.clone();
    wrong_read_owner[0].1=ScoreRelationReadAuthor::PreviousR{context:0,owner:845_758};
    assert!(c512_join_previous_r_reads(&active,&wrong_read_owner).is_err());
    let mut wrong_read_context=reads.clone();
    wrong_read_context[0].1=ScoreRelationReadAuthor::PreviousR{context:1,owner:C512_PREVIOUS_OWNER};
    assert!(c512_join_previous_r_reads(&active,&wrong_read_context).is_err());
    let mut wrong_read_r=reads.clone();
    wrong_read_r[0].0+=C512_PREVIOUS_R_BITS+50;
    assert!(c512_join_previous_r_reads(&active,&wrong_read_r).is_err());
    let mut non_boolean=reads.clone();
    non_boolean[0].2=Fr::from(2u64);
    assert!(c512_join_previous_r_reads(&active,&non_boolean).is_err());

    let physical_score_author=ScoreReplayAuthor{
        context:0,origin:845_760,previous_owner:845_758,
        max_owner:844_670,cap_owner:C512_PREVIOUS_OWNER};
    let physical_author=Bank53TypedAuthor::Score(physical_score_author);
    assert!(c512_require_physical_score_read(&joined[0],0,joined[0].operand.wire,
        physical_author,joined[0].value).is_ok());
    assert!(c512_require_physical_score_read(&joined[0],1,joined[0].operand.wire,
        physical_author,joined[0].value).is_err());
    assert!(c512_require_physical_score_read(&joined[0],0,joined[0].operand.wire+1,
        physical_author,joined[0].value).is_err());
    assert!(c512_require_physical_score_read(&joined[0],0,joined[0].operand.wire,
        physical_author,!joined[0].value).is_err());
    let wrong_physical_author=Bank53TypedAuthor::Score(ScoreReplayAuthor{
        context:0,origin:845_760,previous_owner:845_757,
        max_owner:844_670,cap_owner:C512_PREVIOUS_OWNER});
    assert!(c512_require_physical_score_read(&joined[0],0,joined[0].operand.wire,
        wrong_physical_author,joined[0].value).is_err());
    let wrong_physical_context=Bank53TypedAuthor::Score(ScoreReplayAuthor{
        context:1,..physical_score_author});
    assert!(c512_require_physical_score_read(&joined[0],0,joined[0].operand.wire,
        wrong_physical_context,joined[0].value).is_err());
    let wrong_physical_origin=Bank53TypedAuthor::Score(ScoreReplayAuthor{
        origin:845_761,..physical_score_author});
    assert!(c512_require_physical_score_read(&joined[0],0,joined[0].operand.wire,
        wrong_physical_origin,joined[0].value).is_err());
    let wrong_physical_max=Bank53TypedAuthor::Score(ScoreReplayAuthor{
        max_owner:844_671,..physical_score_author});
    assert!(c512_require_physical_score_read(&joined[0],0,joined[0].operand.wire,
        wrong_physical_max,joined[0].value).is_err());
    let wrong_physical_cap=Bank53TypedAuthor::Score(ScoreReplayAuthor{
        cap_owner:C512_PREVIOUS_OWNER+1,..physical_score_author});
    assert!(c512_require_physical_score_read(&joined[0],0,joined[0].operand.wire,
        wrong_physical_cap,joined[0].value).is_err());

    let root=[0x51;32];
    let total=[0x52;28];
    let profile=[0x53;32];
    let cut=vec![0x54,0x55];
    let candidate=HeaderSourceBinding::from_sink_for_test(
        root,total,profile,cut.clone(),C512_CONSUMER_OWNER);
    let c509=candidate.clone();
    let physical=HeaderSourceBinding::from_sink_for_test(
        root,total,profile,cut.clone(),C512_PREVIOUS_OWNER);
    assert!(c512_require_shared_binding(&candidate,&c509,&physical,root,total,&cut).is_ok());
    let wrong_candidate=HeaderSourceBinding::from_sink_for_test(
        [0x61;32],total,profile,cut.clone(),C512_CONSUMER_OWNER);
    assert!(c512_require_shared_binding(&wrong_candidate,&c509,&physical,root,total,&cut).is_err());
    let wrong_consumer_owner=candidate.mutated_field_for_test(5);
    assert!(c512_require_shared_binding(&wrong_consumer_owner,&c509,&physical,
        root,total,&cut).is_err());
    let wrong_c509=candidate.mutated_field_for_test(0);
    assert!(c512_require_shared_binding(&candidate,&wrong_c509,&physical,root,total,&cut).is_err());
    for field in 0..5 {
        let wrong_physical=physical.mutated_field_for_test(field);
        assert!(c512_require_shared_binding(&candidate,&c509,&wrong_physical,
            root,total,&cut).is_err(),"C512 isolated physical binding field {field}");
    }
    let wrong_source_owner=HeaderSourceBinding::from_sink_for_test(
        root,total,profile,cut,C512_PREVIOUS_OWNER-1);
    assert!(c512_require_shared_binding(&candidate,&c509,&wrong_source_owner,root,total,
        &[0x54,0x55]).is_err());
}

#[cfg(test)]
#[test]
fn c512d_work_occurrence_matcher_isolated_no_frame_mutants() {
    use crate::header_daa_row_placement::{C509ActiveOperand,C509Relation,OperandSide,Relation};
    use crate::packed_owner_assembly::ScoreRelationReadAuthor;
    use crate::h21_work_local_source::Parent;
    use crate::packed_owner_assembly::HeaderSourceBinding;

    let mut active=Vec::new();
    let mut typed=Vec::new();
    let mut d0=Vec::new();let mut d1=Vec::new();let mut upper=Vec::new();
    for bit in 0..C512D_WORK_BITS {
        d0.push((C512D_WORK_D_OWNERS[0]*C512_WIRE_WIDTH+C512D_WORK_D_LOCAL+bit,
            Fr::from((bit%2) as u64)));
        d1.push((C512D_WORK_D_OWNERS[1]*C512_WIRE_WIDTH+C512D_WORK_D_LOCAL+bit,
            Fr::from((bit%3==0) as u64)));
        upper.push((C512D_WORK_UPPER_OWNER*C512_WIRE_WIDTH+C512D_WORK_UPPER_LOCAL+bit,
            Fr::from((bit%4==0) as u64)));
    }
    let mut add=|relation:C509Relation,wire:usize| {
        let occurrence=active.len();
        active.push(C509ActiveOperand{occurrence,relation,
            row:C512_CONSUMER_OWNER*C512_ROW_STRIDE+occurrence,
            side:OperandSide::Left,wire,c1_active:true,c2_active:false,c3_active:false});
    };
    for &(wire,_) in &d0 {add(C509Relation::Ordinary(Relation::DaaLane(2)),wire);}
    for &(wire,_) in &d1 {add(C509Relation::Ordinary(Relation::DaaLane(2)),wire);}
    for context in 0..2 {
        for &(wire,value) in &upper {
            add(C509Relation::Score(context),wire);
            typed.push((wire,ScoreRelationReadAuthor::WorkUpper{
                owner:C512D_WORK_UPPER_OWNER,height:C512D_WORK_UPPER_OWNER+2},value));
        }
    }
    drop(add);
    let joined=c512d_join_work_reads(&active,&typed,&d0,&d1,&upper).unwrap();
    assert_eq!(joined.len(),896);
    {
        use crate::packed_owner_assembly::NativePhysicalAuthor;
        let mut calls=Vec::new();
        let counts=c512d_require_work_tree_claims(&joined,|wire| {
            let index=calls.len();
            calls.push(wire);
            assert_eq!(wire,joined[index].operand.wire);
            Ok((NativePhysicalAuthor::Tree,Fr::from(joined[index].value as u64)))
        }).unwrap();
        assert_eq!(counts,[224;4]);
        assert_eq!(calls,joined.iter().map(|read|read.operand.wire).collect::<Vec<_>>(),
            "every occurrence, including zeroes and repeated Upper reads, consults a token");
        let mut wire_calls=BTreeMap::<usize,usize>::new();
        for wire in calls { *wire_calls.entry(wire).or_insert(0)+=1; }
        for &(wire,_) in d0.iter().chain(&d1) {
            assert_eq!(wire_calls.get(&wire),Some(&1));
        }
        for &(wire,_) in &upper {
            assert_eq!(wire_calls.get(&wire),Some(&2),
                "both Score contexts consult the same Upper claim token");
        }
        for fault in 0..joined.len() {
            let mut calls=0;
            assert!(c512d_require_work_tree_claims(&joined,|_| {
                let index=calls; calls+=1;
                if index==fault { return Err("isolated missing actual endpoint claim".into()); }
                Ok((NativePhysicalAuthor::Tree,Fr::from(joined[index].value as u64)))
            }).is_err(),"isolated missing token read occurrence {fault}");
            assert_eq!(calls,fault+1);
            let mut calls=0;
            assert!(c512d_require_work_tree_claims(&joined,|_| {
                let index=calls; calls+=1;
                let value=joined[index].value ^ (index==fault);
                Ok((NativePhysicalAuthor::Tree,Fr::from(value as u64)))
            }).is_err(),"isolated token value mismatch occurrence {fault}");
            assert_eq!(calls,fault+1);
        }
        for fault in [0,224,448,672] {
            for non_boolean in [false,true] {
                let mut calls=0;
                assert!(c512d_require_work_tree_claims(&joined,|_| {
                    let index=calls; calls+=1;
                    let value=Fr::from(joined[index].value as u64);
                    Ok(if index!=fault {(NativePhysicalAuthor::Tree,value)}
                        else if non_boolean {(NativePhysicalAuthor::Tree,Fr::from(2u64))}
                        else {(NativePhysicalAuthor::Header,value)})
                }).is_err(),"isolated claim author/Boolean fault family at {fault}");
                assert_eq!(calls,fault+1);
            }
        }
        let mut calls=0;
        assert!(c512d_require_work_tree_claims(&joined[..895],|_| {
            calls+=1; Ok((NativePhysicalAuthor::Tree,Fr::zero()))
        }).is_err());
        assert_eq!(calls,0,"an incomplete occurrence set cannot gain claim authority");
        let mut extra=joined.clone();extra.push(joined[0]);
        assert!(c512d_require_work_tree_claims(&extra,|_| {
            Ok((NativePhysicalAuthor::Tree,Fr::zero()))
        }).is_err(),"an extra occurrence cannot gain claim authority");
        for fault in 0..8 {
            let mut mutated=joined.clone();
            match fault {
                0=>mutated[0].family=C512dWorkFamily::WorkD{owner:845_884},
                1=>mutated[0].operand.relation=C509Relation::Ordinary(Relation::DaaLane(1)),
                2=>mutated[0].operand.wire-=C512_WIRE_WIDTH,
                3=>mutated[0].operand.wire+=C512D_WORK_BITS,
                4=>mutated[448].family=C512dWorkFamily::WorkUpper{context:2},
                5=>mutated[448].family=C512dWorkFamily::WorkUpper{context:1},
                6=>{
                    mutated[0].family=C512dWorkFamily::WorkD{owner:845_886};
                    mutated[0].operand.wire+=C512_WIRE_WIDTH;
                },
                7=>mutated[448].operand.wire+=C512D_WORK_BITS,
                _=>unreachable!(),
            }
            let mut calls=0;
            assert!(c512d_require_work_tree_claims(&mutated,|_| {
                let index=calls;calls+=1;
                Ok((NativePhysicalAuthor::Tree,Fr::from(mutated[index].value as u64)))
            }).is_err(),"isolated claim consumer family/owner/coordinate/count fault {fault}");
        }
    }
    c512d_require_no_foreign_work_open(&active,joined.len()).unwrap();
    let mut unexpected_foreign_work=active.clone();
    unexpected_foreign_work.push(C509ActiveOperand{
        occurrence:active.len(),relation:C509Relation::Ordinary(Relation::DaaLane(1)),
        row:C512_CONSUMER_OWNER*C512_ROW_STRIDE+active.len(),side:OperandSide::Left,
        wire:845_884*C512_WIRE_WIDTH+C512D_WORK_D_LOCAL,
        c1_active:true,c2_active:false,c3_active:false,
    });
    assert_eq!(c512d_join_work_reads(&unexpected_foreign_work,&typed,&d0,&d1,&upper)
        .unwrap().len(),896,"narrow matcher alone cannot claim an extra foreign source");
    assert!(c512d_require_no_foreign_work_open(&unexpected_foreign_work,joined.len()).is_err(),
        "C512d full foreign Work demand must reject an unexpected owner/relation");
    assert_eq!(joined.iter().filter(|read|!read.value).count(),
        112+149+336,"physical zeroes remain explicit source reads");
    assert_eq!(joined.iter().filter(|read|read.family==
        C512dWorkFamily::WorkUpper{context:0}).count(),224);
    assert_eq!(joined.iter().filter(|read|read.family==
        C512dWorkFamily::WorkUpper{context:1}).count(),224);
    assert_eq!(joined[0].operand.occurrence,0);
    assert_eq!(joined[895].operand.occurrence,895);

    let mut missing=active.clone();missing.pop();
    assert!(c512d_join_work_reads(&missing,&typed,&d0,&d1,&upper).is_err());
    let mut duplicate_zero=active.clone();duplicate_zero.push(active[0]);
    assert!(c512d_join_work_reads(&duplicate_zero,&typed,&d0,&d1,&upper).is_err());
    let mut wrong_owner=active.clone();wrong_owner[0].wire-=C512_WIRE_WIDTH;
    assert!(c512d_join_work_reads(&wrong_owner,&typed,&d0,&d1,&upper).is_err());
    let mut wrong_daa=active.clone();wrong_daa[0].relation=C509Relation::Ordinary(Relation::DaaLane(1));
    assert!(c512d_join_work_reads(&wrong_daa,&typed,&d0,&d1,&upper).is_err());
    let mut wrong_context=active.clone();wrong_context[448].relation=C509Relation::Score(1);
    assert!(c512d_join_work_reads(&wrong_context,&typed,&d0,&d1,&upper).is_err());
    let mut wrong_upper=active.clone();wrong_upper[448].wire+=C512D_WORK_BITS;
    assert!(c512d_join_work_reads(&wrong_upper,&typed,&d0,&d1,&upper).is_err());
    let mut wrong_d_owner=active.clone();wrong_d_owner[224].wire+=C512_WIRE_WIDTH;
    assert!(c512d_join_work_reads(&wrong_d_owner,&typed,&d0,&d1,&upper).is_err());
    let mut wrong_row=active.clone();wrong_row[0].row-=C512_ROW_STRIDE;
    assert!(c512d_join_work_reads(&wrong_row,&typed,&d0,&d1,&upper).is_err());
    let mut x_stride_row=active.clone();x_stride_row[0].row=C512_CONSUMER_OWNER*C512_WIRE_WIDTH;
    assert!(c512d_join_work_reads(&x_stride_row,&typed,&d0,&d1,&upper).is_err(),
        "X wire width cannot replace the canonical C509 ROW stride");
    let mut inactive_side=active.clone();inactive_side[0].c1_active=false;
    assert!(c512d_join_work_reads(&inactive_side,&typed,&d0,&d1,&upper).is_err());

    let mut missing_typed=typed.clone();missing_typed.pop();
    assert!(c512d_join_work_reads(&active,&missing_typed,&d0,&d1,&upper).is_err());
    let mut duplicate_typed_zero=typed.clone();
    duplicate_typed_zero.push(typed[1]);
    assert!(c512d_join_work_reads(&active,&duplicate_typed_zero,&d0,&d1,&upper).is_err());
    let mut wrong_typed_kind=typed.clone();wrong_typed_kind[0].1=
        ScoreRelationReadAuthor::PreviousR{context:0,owner:C512_PREVIOUS_OWNER};
    assert!(c512d_join_work_reads(&active,&wrong_typed_kind,&d0,&d1,&upper).is_err());
    let mut wrong_typed_owner=typed.clone();wrong_typed_owner[0].1=
        ScoreRelationReadAuthor::WorkUpper{owner:845_885,height:845_888};
    assert!(c512d_join_work_reads(&active,&wrong_typed_owner,&d0,&d1,&upper).is_err());
    let mut extra_foreign_upper=typed.clone();
    extra_foreign_upper.push((845_885*C512_WIRE_WIDTH+C512D_WORK_UPPER_LOCAL,
        ScoreRelationReadAuthor::WorkUpper{owner:845_885,height:845_887},Fr::zero()));
    assert!(c512d_join_work_reads(&active,&extra_foreign_upper,&d0,&d1,&upper).is_err());
    let mut wrong_typed_height=typed.clone();wrong_typed_height[0].1=
        ScoreRelationReadAuthor::WorkUpper{owner:845_886,height:845_887};
    assert!(c512d_join_work_reads(&active,&wrong_typed_height,&d0,&d1,&upper).is_err());
    let mut wrong_typed_value=typed.clone();wrong_typed_value[0].2=Fr::one()-typed[0].2;
    assert!(c512d_join_work_reads(&active,&wrong_typed_value,&d0,&d1,&upper).is_err());
    let mut nonboolean_typed=typed.clone();nonboolean_typed[0].2=Fr::from(2u64);
    assert!(c512d_join_work_reads(&active,&nonboolean_typed,&d0,&d1,&upper).is_err());

    let mut missing_d=d0.clone();missing_d.pop();
    assert!(c512d_join_work_reads(&active,&typed,&missing_d,&d1,&upper).is_err());
    let mut duplicate_physical_zero=d0.clone();duplicate_physical_zero.push(d0[0]);
    assert!(c512d_join_work_reads(&active,&typed,&duplicate_physical_zero,&d1,&upper).is_err());
    let mut wrong_d_wire=d1.clone();wrong_d_wire[0].0+=C512_WIRE_WIDTH;
    assert!(c512d_join_work_reads(&active,&typed,&d0,&wrong_d_wire,&upper).is_err());
    let mut nonboolean_d=d0.clone();nonboolean_d[0].1=Fr::from(2u64);
    assert!(c512d_join_work_reads(&active,&typed,&nonboolean_d,&d1,&upper).is_err());
    let mut wrong_upper_wire=upper.clone();wrong_upper_wire[0].0+=1;
    assert!(c512d_join_work_reads(&active,&typed,&d0,&d1,&wrong_upper_wire).is_err());
    let mut wrong_upper_value=upper.clone();wrong_upper_value[0].1=Fr::one()-upper[0].1;
    assert!(c512d_join_work_reads(&active,&typed,&d0,&d1,&wrong_upper_value).is_err());

    let root=[0x61;32];let total=[0x62;28];let profile=[0x63;32];
    let cut=vec![0x64,0x65];let headers=1_827_840u64;let slots=1usize<<21;
    let candidate=HeaderSourceBinding::from_sink_for_test(
        root,total,profile,cut.clone(),C512_CONSUMER_OWNER);
    let parent=Parent{root,total,profile,headers,slots,cut:cut.clone()};
    for owner in C512D_WORK_D_OWNERS {
        let source=HeaderSourceBinding::from_sink_for_test(
            root,total,profile,cut.clone(),owner);
        assert!(c512d_require_work_parent(&candidate,&candidate,&source,&parent,
            owner,root,total,&cut,headers,slots).is_ok());
        let wrong_source=source.mutated_field_for_test(4);
        assert!(c512d_require_work_parent(&candidate,&candidate,&wrong_source,&parent,
            owner,root,total,&cut,headers,slots).is_err());
        let wrong_c509=candidate.mutated_field_for_test(0);
        assert!(c512d_require_work_parent(&candidate,&wrong_c509,&source,&parent,
            owner,root,total,&cut,headers,slots).is_err());
        for field in 0..5 {
            let wrong_source=source.mutated_field_for_test(field);
            assert!(c512d_require_work_parent(&candidate,&candidate,&wrong_source,&parent,
                owner,root,total,&cut,headers,slots).is_err());
        }
        let mut wrong_parent=parent.clone();wrong_parent.root=[0x71;32];
        assert!(c512d_require_work_parent(&candidate,&candidate,&source,&wrong_parent,
            owner,root,total,&cut,headers,slots).is_err());
        let mut wrong_parent=parent.clone();wrong_parent.total=[0x72;28];
        assert!(c512d_require_work_parent(&candidate,&candidate,&source,&wrong_parent,
            owner,root,total,&cut,headers,slots).is_err());
        let mut wrong_parent=parent.clone();wrong_parent.profile=[0x73;32];
        assert!(c512d_require_work_parent(&candidate,&candidate,&source,&wrong_parent,
            owner,root,total,&cut,headers,slots).is_err());
        let mut wrong_parent=parent.clone();wrong_parent.cut.push(0x74);
        assert!(c512d_require_work_parent(&candidate,&candidate,&source,&wrong_parent,
            owner,root,total,&cut,headers,slots).is_err());
        let mut wrong_parent=parent.clone();wrong_parent.headers+=1;
        assert!(c512d_require_work_parent(&candidate,&candidate,&source,&wrong_parent,
            owner,root,total,&cut,headers,slots).is_err());
        let mut wrong_parent=parent.clone();wrong_parent.slots-=1;
        assert!(c512d_require_work_parent(&candidate,&candidate,&source,&wrong_parent,
            owner,root,total,&cut,headers,slots).is_err());
        let wrong_owner=owner-1;
        assert!(c512d_require_work_parent(&candidate,&candidate,&source,&parent,
            wrong_owner,root,total,&cut,headers,slots).is_err());
    }
}

fn c432_no_frame_geometry_and_fold_fixture() {
    use ark_ff::{Field,One,Zero};
    let endpoints=&crate::work_tree_layout::shared_baseline()
        .expect("C432 immutable endpoint layout").endpoints;
    assert_eq!(endpoints.upper,(987_450..987_674).collect::<Vec<_>>());
    assert_eq!(endpoints.work,(987_674..987_898).collect::<Vec<_>>());
    assert_eq!(endpoints.exponent,(987_898..988_154).collect::<Vec<_>>());
    let domains=[
        crate::h21_work_local_source::operand_domain(845_757).unwrap(),
        crate::h21_work_local_source::operand_domain(845_758).unwrap(),
    ];
    for (index,owner) in [845_757usize,845_758].into_iter().enumerate() {
        let base=owner*(1<<20);
        for local in [987_672usize,987_673,987_898,987_899] {
            assert_eq!(domains[index].iter().filter(|wire|**wire==base+local).count(),1,
                "C432 exact WorkLocal boundary operand owner={owner} local={local}");
            assert!(!domains[1-index].contains(&(base+local)),
                "C432 source owner separation owner={owner} local={local}");
        }
        for local in [987_672usize,987_673,987_674,987_675,987_896,987_897,987_898,987_899] {
            assert!(domains[index].contains(&(base+local)),
                "C432 first/last Work-D quartet source domain owner={owner} local={local}");
        }
    }
    let alpha=Fr::from(7u64);
    let a=[Fr::from(3u64),Fr::from(5u64),Fr::from(11u64),Fr::from(13u64)];
    let b=[Fr::from(17u64),Fr::from(19u64),Fr::from(23u64),Fr::from(29u64)];
    let x=[Fr::from(31u64),Fr::from(37u64),Fr::from(41u64),Fr::from(43u64)];
    let folded=|v:[Fr;4]| [v[0]+alpha*(v[1]-v[0]),v[2]+alpha*(v[3]-v[2])];
    let af=folded(a);let bf=folded(b);let xf=folded(x);
    let candidate=crate::gkr::quadratic_message(&af,&bf,&xf);
    let direct=|t:Fr| {
        let chi=|bit:usize| if bit==0 {Fr::one()-alpha} else {alpha};
        let lambda=|bit:usize| if bit==0 {Fr::one()-t} else {t};
        (0..4).fold(Fr::zero(),|sum,index| {
            let b0=index&1;let b1=(index>>1)&1;
            let x_block=(Fr::one()-t)*xf[0]+t*xf[1];
            sum+chi(b0)*lambda(b1)*(a[index]*x_block+b[index])
        })
    };
    let y0=direct(Fr::zero());let y1=direct(Fr::one());let y2=direct(Fr::from(2u64));
    let half=Fr::from(2u64).inverse().unwrap();
    let oracle=[y0,y1-y0-(y2-Fr::from(2u64)*y1+y0)*half,
        (y2-Fr::from(2u64)*y1+y0)*half];
    assert_eq!(candidate,oracle,"C432 source-only three-point p1 oracle");
    let sibling_a=[Fr::from(5u64),Fr::zero()];
    let sibling_b=[Fr::zero(),Fr::zero()];
    let sibling_x=[Fr::from(3u64),Fr::from(7u64)];
    let sibling_p=crate::gkr::quadratic_message(&sibling_a,&sibling_b,&sibling_x);
    let omitted_x=[sibling_x[0],Fr::zero()];
    assert_ne!(crate::gkr::quadratic_message(&sibling_a,&sibling_b,&omitted_x),sibling_p,
        "C432 isolated zero-A1 sibling X omission changes quartet interpolation");
    println!("C432_NO_FRAME_SOURCE_GEOMETRY_PASS owners=2 boundary_bits=8 first_last_work_quartets=true p1_oracle=true zero_A1_sibling_X_omission_rejected=true frame=false");
}

#[test]
fn c432_no_frame_source_geometry_and_fold_fixture() {
    c432_no_frame_geometry_and_fold_fixture();
}

fn c434_fold_octet(values:[Fr;8],alpha:Fr,beta:Fr)->[Fr;2] {
    let wa=[Fr::one()-alpha,alpha];
    let wb=[Fr::one()-beta,beta];
    std::array::from_fn(|slot| {
        let mut out=Fr::zero();
        for b1 in 0..2 {for b0 in 0..2 {
            out+=wb[b1]*wa[b0]*values[4*slot+2*b1+b0];
        }}
        out
    })
}

#[test]
fn c434_no_frame_octet_geometry_and_source_domains() {
    let endpoints=&crate::work_tree_layout::shared_baseline()
        .expect("C434 immutable WorkTree endpoint layout").endpoints;
    assert_eq!(endpoints.exponent,(987_898..988_154).collect::<Vec<_>>());
    let closure=|start:usize,end:usize| (start&!7usize,(end+7)&!7usize);
    assert_eq!(closure(987_674,987_898),(987_672,987_904));
    assert_eq!(closure(999_424,999_648),(999_424,999_648));
    assert_eq!(closure(1_000_097,1_000_321),(1_000_096,1_000_328));
    assert_ne!((987_674&!3usize,(987_898+3)&!3usize),
        closure(987_674,987_898),"C434 four-wire closure cannot replace octet closure");
    for owner in [845_757usize,845_758] {
        let domain=crate::h21_work_local_source::operand_domain(owner)
            .expect("C434 exact checked WorkLocal operand domain");
        assert_eq!(domain.len(),1_184);
        let base=owner*(1<<20);
        for local in 987_900usize..987_904 {
            assert_eq!(domain.iter().filter(|wire|**wire==base+local).count(),1,
                "C434 source-only Exponent tail domain");
        }
        let mut omitted=domain.clone();
        omitted.retain(|wire|*wire!=base+987_903);
        assert!(!(987_900usize..987_904).all(|local|omitted.contains(&(base+local))),
            "C434 missing final Tree-domain bit mutant");
    }
    let context1=MaxReplayAuthor::Scheduled(Writer::Max{context:1,end:844_672});
    let wrong_context=MaxReplayAuthor::Scheduled(Writer::Max{context:0,end:844_672});
    let tail_wire=844_670*(1<<20)+1_000_327;
    let context1_tag_matches=|wire:usize,author:MaxReplayAuthor|
        wire/(1<<20)==844_670 && (1_000_097..1_000_770).contains(&(wire%(1<<20)))
            && author==MaxReplayAuthor::Scheduled(Writer::Max{context:1,end:844_672});
    assert!(context1_tag_matches(tail_wire,context1),"C434 scheduled MAX context1 tail");
    assert!(!context1_tag_matches(tail_wire,wrong_context),
        "C434 wrong MAX context tag mutant rejected");
    assert!((1_000_324usize..1_000_328).all(|wire|(1_000_097..1_000_770).contains(&wire)),
        "C434 MAX tail lies in the full scheduled context1 lease");
    println!("C434_NO_FRAME_OCTET_GEOMETRY_PASS work_new_tree=8 max_new=4 frame=false");
}

#[test]
fn c434_no_frame_octet_algebra_and_transcript() {
    use ark_ff::{Field,One,Zero};
    let alpha=Fr::from(7u64);let beta=Fr::from(11u64);
    let mut a=[Fr::zero();8];let b=[Fr::zero();8];let mut x=[Fr::zero();8];
    a[0]=Fr::from(3u64);x[7]=Fr::one();
    let af=c434_fold_octet(a,alpha,beta);
    let bf=c434_fold_octet(b,alpha,beta);
    let xf=c434_fold_octet(x,alpha,beta);
    let candidate=crate::gkr::quadratic_message(&af,&bf,&xf);
    let direct=|t:Fr| {
        let mut x_at=Fr::zero();
        for index in 0..8 {
            let wa=if index&1==0 {Fr::one()-alpha}else{alpha};
            let wb=if index&2==0 {Fr::one()-beta}else{beta};
            let wt=if index&4==0 {Fr::one()-t}else{t};
            x_at+=wa*wb*wt*x[index];
        }
        (0..8).fold(Fr::zero(),|sum,index| {
            let wa=if index&1==0 {Fr::one()-alpha}else{alpha};
            let wb=if index&2==0 {Fr::one()-beta}else{beta};
            let wt=if index&4==0 {Fr::one()-t}else{t};
            sum+wa*wb*wt*(a[index]*x_at+b[index])
        })
    };
    let y0=direct(Fr::zero());let y1=direct(Fr::one());let y2=direct(Fr::from(2u64));
    let half=Fr::from(2u64).inverse().expect("C434 two invertible in Fr");
    let quad=(y2-Fr::from(2u64)*y1+y0)*half;
    let oracle=[y0,y1-y0-quad,quad];
    assert_eq!(candidate,oracle,"C434 source-only original-octet three-point oracle");
    let mut omitted_x=x;omitted_x[7]=Fr::zero();
    let dropped=crate::gkr::quadratic_message(&af,&bf,
        &c434_fold_octet(omitted_x,alpha,beta));
    assert_ne!(candidate,dropped,"C434 zero-A2 sibling X omission changes coefficients");
    assert_eq!(candidate[0]+crate::gkr::eval_polynomial(&candidate,Fr::one()),
        dropped[0]+crate::gkr::eval_polynomial(&dropped,Fr::one()),
        "C434 endpoint identity alone does not catch sibling X omission");
    let mut parity_a=a;parity_a.swap(0,4);
    assert_ne!(crate::gkr::quadratic_message(&c434_fold_octet(parity_a,alpha,beta),&bf,&xf),
        candidate,"C434 isolated octet parity mutant");
    let mut omitted_a=a;omitted_a[0]=Fr::zero();
    assert_ne!(crate::gkr::quadratic_message(&c434_fold_octet(omitted_a,alpha,beta),&bf,&xf),
        candidate,"C434 isolated A-active term omission");
    let mut prefix=crate::transcript::Transcript::new(b"nipopow-c434-no-frame-octet-v1");
    prefix.append_bytes(b"c434-fixture",b"alpha7-beta11-octet");
    let mut altered_prefix=prefix.clone();
    crate::gkr::append_polynomial(&mut prefix,b"gkr-sumcheck-polynomial",
        &[Fr::from(2u64),Fr::from(3u64),Fr::from(5u64)]);
    let frozen_beta=prefix.challenge_scalar(b"gkr-sumcheck-challenge");
    crate::gkr::append_polynomial(&mut altered_prefix,b"gkr-sumcheck-polynomial",
        &[Fr::from(2u64),Fr::from(4u64),Fr::from(5u64)]);
    assert_ne!(frozen_beta,altered_prefix.challenge_scalar(b"gkr-sumcheck-challenge"),
        "C434 mutated prior polynomial changes transcript-derived beta");
    let mut regular=prefix.clone();
    crate::gkr::append_polynomial(&mut regular,b"gkr-sumcheck-polynomial",&candidate);
    let challenge3=regular.challenge_scalar(b"gkr-sumcheck-challenge");
    let mut extra_index=prefix.clone();
    crate::gkr::append_usize(&mut extra_index,b"gkr-layer-index",1);
    crate::gkr::append_polynomial(&mut extra_index,b"gkr-sumcheck-polynomial",&candidate);
    assert_ne!(challenge3,extra_index.challenge_scalar(b"gkr-sumcheck-challenge"),
        "C434 extra layer index rejected by frozen transcript replay");
    println!("C434_NO_FRAME_OCTET_ALGEBRA_PASS sibling_x_omission_rejected=true transcript_mutants_rejected=true frame=false");
}

#[test]
#[ignore = "one-use native Score frame run requires exact-source runner prelaunch review"]
fn c187_native_full_max_score_from_pinned_frame() {
    native_max_score_from_pinned_frame(false, false, false, false, false, false, false, false);
}

#[test]
#[ignore = "one-use native R450 sink run requires exact-source runner prelaunch review"]
fn c208_native_r450_mint_to_owner845759_from_pinned_frame() {
    native_max_score_from_pinned_frame(true, false, false, false, false, false, false, false);
}

#[test]
#[ignore = "one-use native Cap/Upper sink run requires exact-source runner prelaunch review"]
fn c210_native_cap_upper_to_owner845759_from_pinned_frame() {
    native_max_score_from_pinned_frame(true, true, false, false, false, false, false, false);
}

#[test]
#[ignore = "C390 full source join requires exact pinned H21 frame and independent prelaunch review"]
fn c390_native_scored_owner_join_from_pinned_frame() {
    native_max_score_from_pinned_frame(false, false, true, false, false, false, false, false);
}

#[test]
#[ignore = "C396 native packed source requires exact pinned H21 frame and independent prelaunch review"]
fn c396_native_scored_owner_packed_source_from_pinned_frame() {
    native_max_score_from_pinned_frame(false, false, false, true, false, false, false, false);
}

#[test]
#[ignore = "C445 two-owner packed source requires exact pinned H21 frame and independent prelaunch review"]
fn c445_authentic_regular_score_owners_846015_and_1810879() {
    native_max_score_from_pinned_frame_mode(
        false, false, false, false, false, false, false, false, true, false, false, false, false, false,
    );
}

#[test]
#[ignore = "exact pinned H21 frame; reviewed bounded single-owner C453 ROW reader runner required"]
fn c453_authentic_carry845759_retained_map_row_reader() {
    native_max_score_from_pinned_frame_mode(
        true, true, false, false, false, false, false, false, false, true, false, false, false, false,
    );
}

#[test]
#[ignore = "exact pinned H21 frame; reviewed bounded single-owner C455 ROW reader runner required"]
fn c455_authentic_carry845759_modern_score_slack_row_reader() {
    native_max_score_from_pinned_frame_mode(
        true, true, false, false, false, false, false, false, false, false, true, false, false, false,
    );
}

#[test]
#[ignore = "one-use C487 native terminal-public binding; exact source/runner review required"]
fn c487_native_terminal_public_binding_from_pinned_frame() {
    native_max_score_from_pinned_frame_mode(
        false, false, false, false, false, false, false, false, false, false, false, true, false, false,
    );
}

#[test]
#[ignore = "one-use C488 native Score import seam; exact source/runner review required"]
fn c488_native_score_import_seam_owner845887_from_pinned_frame() {
    native_max_score_from_pinned_frame_mode(
        false, false, false, false, false, false, false, false, false, false, false, false, true, false,
    );
}

#[test]
#[ignore = "one-use C489 native selected Score/Slack join; exact source/runner review required"]
fn c489_native_score_slack_owner845887_from_pinned_frame() {
    native_max_score_from_pinned_frame_mode(
        false, false, false, false, false, false, false, false, false, false, false, false, false, true,
    );
}

#[test]
#[ignore = "one-use C511 native regular ROW join; exact pinned H21 frame and independent prelaunch review required"]
fn c511_native_regular_row_owner845887_from_pinned_frame() {
    native_max_score_from_pinned_frame_mode_inner(
        false, false, false, false, false, false, false, false,
        false, false, false, false, false, false, true, false, false,
    );
}

#[test]
#[ignore = "one-use C512b integrated previous-R physical join requires exact source review and EIP resource release"]
fn c512b_native_previous_r_physical_join_from_pinned_frame() {
    native_max_score_from_pinned_frame_mode_inner(
        true, true, false, false, false, false, false, false,
        false, false, false, false, false, false, true, true, false,
    );
}

#[test]
#[ignore = "HOLD: C512j Work-D/Upper actual Tree-claim join needs fresh bounded runner, cost admission and independent review"]
fn c512d_native_work_physical_join_from_pinned_frame() {
    native_max_score_from_pinned_frame_mode_inner(
        true, true, false, false, false, false, false, false,
        false, false, false, false, false, false, true, true, true,
    );
}

#[test]
#[ignore = "HOLD: one historical C512h physical-read plus C513 numeric-ROW diagnostic; fresh reviewed runner and resource admission required"]
fn c512h_native_selected_owner_physical_reads_and_numeric_row() {
    native_max_score_from_pinned_frame_mode_extended(
        true,true,false,false,false,false,false,false,false,
        false,false,false,false,false,false,false,false,true,false,false,false,
    );
}

#[test]
#[ignore = "HOLD: C514 selected ROW U0 requires pure tests, independent source review, fresh claim, bounded runner and new resource admission"]
fn c514_native_selected_owner_u0_contribution_from_pinned_frame() {
    native_max_score_from_pinned_frame_mode_extended(
        true,true,false,false,false,false,false,false,false,
        false,false,false,false,false,false,false,false,true,true,false,false,
    );
}

#[test]
#[ignore = "one-use C517 terminal-closed regular ROW diagnostic; independent review and fresh resource admission required"]
fn c517_native_closed_regular_owner845887_from_pinned_frame() {
    native_max_score_from_pinned_frame_mode_extended(
        false,false,false,false,false,false,false,false,false,
        false,false,false,false,false,false,false,false,false,false,true,false,
    );
}

#[test]
#[ignore = "one-use C518 same-stream physical C514 U0 diagnostic; exact source and runner review required"]
fn c518_native_same_stream_physical_u0_owner845887_from_pinned_frame() {
    native_max_score_from_pinned_frame_mode_extended(
        false,false,false,false,false,false,false,false,false,
        false,false,false,false,false,false,false,false,false,false,false,true,
    );
}

#[test]
#[ignore = "pinned full H21 frame; bounded C430 native Carry residual runner and review required"]
fn c430_authentic_carry845759_dense_residual_admission() {
    native_max_score_from_pinned_frame(true, true, false, false, true, false, false, false);
}

#[test]
#[ignore = "C431 authentic first-U diagnostic; exact pinned frame runner/review required"]
fn c431_authentic_carry845759_first_u_pair_diagnostic() {
    native_max_score_from_pinned_frame(true, true, false, false, true, true, false, false);
}

#[test]
#[ignore = "C432 second U authentic diagnostic; exact pinned H21 runner/review required"]
fn c433_authentic_carry845759_second_u_tree_author_diagnostic() {
    c432_no_frame_geometry_and_fold_fixture();
    native_max_score_from_pinned_frame(true, true, false, false, true, true, true, false);
}

#[test]
#[ignore = "C434 third U authentic diagnostic; exact pinned H21 runner/review required"]
fn c434_authentic_carry845759_third_u_tree_author_diagnostic() {
    c432_no_frame_geometry_and_fold_fixture();
    native_max_score_from_pinned_frame(true, true, false, false, true, true, true, true);
}

fn native_max_score_from_pinned_frame(
    r450: bool, cap_upper: bool, scored_owner: bool, packed_scored_owner: bool,
    dense_residual: bool, first_u: bool, second_u: bool, third_u: bool,
) {
    native_max_score_from_pinned_frame_mode(
        r450, cap_upper, scored_owner, packed_scored_owner,
        dense_residual, first_u, second_u, third_u, false, false, false, false, false, false,
    );
}

fn native_max_score_from_pinned_frame_mode(
    r450: bool, cap_upper: bool, scored_owner: bool, packed_scored_owner: bool,
    dense_residual: bool, first_u: bool, second_u: bool, third_u: bool, c445: bool,
    c453: bool, c455: bool, c487: bool, c488: bool, c489: bool,
) {
    native_max_score_from_pinned_frame_mode_inner(
        r450, cap_upper, scored_owner, packed_scored_owner,
        dense_residual, first_u, second_u, third_u, c445,
        c453, c455, c487, c488, c489, false, false, false,
    );
}

fn native_max_score_from_pinned_frame_mode_inner(
    r450: bool, cap_upper: bool, scored_owner: bool, packed_scored_owner: bool,
    dense_residual: bool, first_u: bool, second_u: bool, third_u: bool, c445: bool,
    c453: bool, c455: bool, c487: bool, c488: bool, c489: bool, c511_regular_row: bool,
    c512_previous_r_physical_join: bool, c512d_work_physical_join: bool,
) {
    native_max_score_from_pinned_frame_mode_extended(
        r450,cap_upper,scored_owner,packed_scored_owner,dense_residual,first_u,second_u,third_u,
        c445,c453,c455,c487,c488,c489,c511_regular_row,c512_previous_r_physical_join,
        c512d_work_physical_join,false,false,false,false,
    );
}

fn native_max_score_from_pinned_frame_mode_extended(
    r450:bool,cap_upper:bool,scored_owner:bool,packed_scored_owner:bool,
    dense_residual:bool,first_u:bool,second_u:bool,third_u:bool,c445:bool,
    c453:bool,c455:bool,c487:bool,c488:bool,c489:bool,c511_regular_row:bool,
    c512_previous_r_physical_join:bool,c512d_work_physical_join:bool,c512h:bool,c514:bool,c517:bool,c518:bool,
) {
    assert!(!c518 || !(r450 || cap_upper || scored_owner || packed_scored_owner
        || dense_residual || first_u || second_u || third_u || c445 || c453 || c455
        || c487 || c488 || c489 || c511_regular_row || c512_previous_r_physical_join
        || c512d_work_physical_join || c512h || c514 || c517),
        "C518 requires its isolated same-stream physical source mode");
    assert!(!c517 || !(r450 || cap_upper || scored_owner || packed_scored_owner
        || dense_residual || first_u || second_u || third_u || c445 || c453 || c455
        || c487 || c488 || c489 || c511_regular_row || c512_previous_r_physical_join
        || c512d_work_physical_join || c512h || c514),
        "C517 requires its isolated terminal-closed source mode");
    assert!(!c514 || c514_native_mode_allowed(c512h,[r450,cap_upper,scored_owner,
        packed_scored_owner,dense_residual,first_u,second_u,third_u,c445,c453,c455,
        c487,c488,c489,c511_regular_row,c512_previous_r_physical_join,c512d_work_physical_join]),
        "C514 requires the isolated same-frame H producer path");
    assert!(!c514 || !(c517 || c518),"C514 U0 and C517/C518 modes are exclusive");
    assert!(!c512h || (r450&&cap_upper&&!scored_owner&&!packed_scored_owner&&!dense_residual
        &&!first_u&&!second_u&&!third_u&&!c445&&!c453&&!c455&&!c487&&!c488&&!c489
        &&!c511_regular_row&&!c512_previous_r_physical_join&&!c512d_work_physical_join),
        "C512h requires its isolated same-frame physical producer path");
    assert!(!third_u || second_u,"C434 third U requires the admitted second U");
    assert!(!c487 || !(r450 || cap_upper || scored_owner || packed_scored_owner
        || dense_residual || first_u || second_u || third_u || c445 || c453 || c455),
        "C487 terminal binding requires an isolated native mode");
    assert!(!c488 || !(r450 || cap_upper || scored_owner || packed_scored_owner
        || dense_residual || first_u || second_u || third_u || c445 || c453 || c455 || c487),
        "C488 Score import requires an isolated native mode");
    assert!(!c489 || !(r450 || cap_upper || scored_owner || packed_scored_owner
        || dense_residual || first_u || second_u || third_u || c445 || c453 || c455 || c487 || c488),
        "C489 Score/Slack join requires an isolated native mode");
    assert!(!c511_regular_row || c512_previous_r_physical_join
        || !(r450 || cap_upper || scored_owner || packed_scored_owner
        || dense_residual || first_u || second_u || third_u || c445 || c453 || c455 || c487 || c488 || c489),
        "C511 regular ROW join requires an isolated native mode");
    assert!(!c512_previous_r_physical_join || (c511_regular_row && r450 && cap_upper
        && !scored_owner && !packed_scored_owner && !dense_residual && !first_u
        && !second_u && !third_u && !c445 && !c453 && !c455 && !c487 && !c488 && !c489),
        "C512b integrated PreviousR physical join requires its one exact producer path");
    assert!(!c512d_work_physical_join || c512_previous_r_physical_join,
        "C512d Work physical join requires the same-frame C512b producer path");
    assert!(!(c453 || c455) || (r450 && cap_upper && !scored_owner && !packed_scored_owner
        && !dense_residual && !first_u && !second_u && !third_u && !c445));
    let mut c512_c509_retained=None;
    let mut c512h_retained=None;
    let started=Instant::now();let owners=calendar();phase("frame_start",started);
    let path=std::env::var_os("NIPOPOW_H21_FRAME").expect("pinned frame environment");
    let path=Path::new(&path);assert!(path.is_absolute());
    let before=fs::symlink_metadata(path).expect("frame metadata");
    assert!(before.is_file() && !before.file_type().is_symlink());
    assert_eq!(before.len(),FRAME_BYTES);
    let file=File::open(path).expect("open existing pinned frame");
    assert_eq!(file.metadata().unwrap().len(),FRAME_BYTES);
    let mut frame=FrameReader::new(BufReader::with_capacity(CHUNK,file),FRAME_BYTES).expect("frame SHA setup");
    preamble(&mut frame,1_827_839,N as u32).expect("pinned ERFV preamble");
    let (prefix,extensions)={
        let mut headers=HeaderIter::new(&mut frame,N);
        let prefix=NativePrefix::from_raw_iter(N,&mut headers).expect("single linked native H21 prefix");
        assert_eq!(headers.remaining,0);(prefix,headers.extensions)
    };
    assert_eq!(prefix.header_count(),N);assert_eq!(frame.offset,PREFIX_BYTES);assert_eq!(extensions,EXTENSIONS);
    frame.finish(PREFIX_BYTES,TAIL_BYTES,FRAME_SHA256).expect("whole existing frame exact SHA");
    let c487_observed_frame_sha=c487.then(||FRAME_SHA256.to_owned());
    let c488_observed_frame_sha=c488.then(||FRAME_SHA256.to_owned());
    let c489_observed_frame_sha=c489.then(||FRAME_SHA256.to_owned());
    let after=fs::symlink_metadata(path).expect("frame restat");
    assert!(after.is_file() && !after.file_type().is_symlink());
    assert_eq!(after.len(),before.len());assert_eq!(after.modified().unwrap(),before.modified().unwrap());
    phase("frame_verified",started);
    let plan=WorkTreeHistoryPlan::compile(N as u64,H,prefix.root(),prefix.total_be28()).expect("native H21 plan");
    validate_native_plan_input(&plan,&prefix).expect("native plan/prefix identity");
    phase("plan_verified",started);
    let snapshot=Eligible08NativeSnapshot::new(&plan,&prefix).expect("native immutable Eligible08 snapshot");
    let producer=NativeOwnerProducer::new_for_history(&plan,&prefix).expect("native producer");
    let mut stream=MaxStream::new(&plan,&prefix,&snapshot).expect("native MAX-only stream");
    assert_eq!(stream.remaining_owners(),7683);assert!(stream.retained_capacity_bytes()<2*1024*1024);
    phase("ready",started);
    println!("C187_MAX_CALENDAR context0_owners=7682 context1_owners=7550 union=7683 shared=7549 retained_capacity_bytes={}",stream.retained_capacity_bytes());
    assert_eq!(stream.push_native(&producer,owners[1].0).unwrap_err(),"streamed MAX exact descending owner");
    assert_eq!(stream.remaining_owners(),7683);
    assert_eq!(stream.closed_owner_cells(owners[0].0).unwrap_err(),"streamed MAX incomplete closure");
    println!("C187_MAX_ORDER_REJECT owner={} remaining=7683 replay_unavailable=true",owners[1].0);
    for (index,(owner,_)) in owners.iter().enumerate() {
        if index==owners.len()-1 {
            assert_eq!(stream.remaining_owners(),1);
            assert_eq!(stream.closed_owner_cells(owners[0].0).unwrap_err(),"streamed MAX incomplete closure");
            println!("C187_MAX_PARTIAL_REPLAY_REJECT owners=7682 remaining=1");
        }
        stream.push_native(&producer,*owner).expect("native MAX owner append");
        assert_eq!(stream.remaining_owners(),owners.len()-index-1);
        if [1,32,128,7683].contains(&(index+1)) {
            println!("C187_MAX_PROGRESS owners={} remaining={} elapsed_s={:.6}",index+1,stream.remaining_owners(),started.elapsed().as_secs_f64());
            std::io::stdout().flush().expect("flush c187 MAX progress");
        }
    }
    assert_eq!(stream.remaining_owners(),0);
    let exports=NativeExports::new_for_history(&plan,&prefix).expect("independent native scalar exports");
    for owner in [844670,844798,1810814,1810840,1827838] {
        let cells=stream.closed_owner_cells(owner).expect("complete MAX-only replay");
        let lease=producer.native_work_d_lease(owner).expect("native D sample lease");
        producer.require_work_d_lease(owner,&lease).expect("native D source replay");
        let d=lease.checked_cells(&snapshot.parent(),owner).expect("native D exact224");
        assert_eq!(d.len(),224);
        let expected_lease=snapshot.owner_lease(owner).expect("immutable scheduled sample");
        assert_eq!(d,expected_lease.work_d().unwrap().cells());
        let mut expected:Vec<_>=d.iter().map(|&(wire,value)| {
            assert_eq!(value,Fr::from(exports.bit(wire).expect("native export D")as u64));
            (wire,MaxReplayAuthor::NativeWorkD{height:owner+2},value)
        }).collect();
        expected.extend(expected_lease.cells().into_iter().filter(|(_,writer,_)|matches!(writer,Writer::Max{..}))
            .map(|(wire,writer,value)|(wire,MaxReplayAuthor::Scheduled(writer),value)));
        assert_eq!(cells,expected);
        assert!(cells.iter().all(|(_,_,value)|value.is_zero()||value.is_one()));
        assert_eq!(cells.iter().map(|(wire,_,_)|*wire).collect::<BTreeSet<_>>().len(),cells.len());
        println!("C187_MAX_REPLAY owner={owner} d_cells=224 max_cells={} total_cells={}",cells.len()-224,cells.len());
    }
    assert_eq!(stream.closed_owner_cells(844671).unwrap_err(),"streamed MAX replay inactive owner");
    phase("replay_verified",started);
    println!("C187_NATIVE_MAX_READY owners=7683 samples=5 retained_capacity_bytes={}",stream.retained_capacity_bytes());

    let context=H21EligibleContext::new(&plan,&prefix).expect("native Eligible08 pair");
    phase("score_context_ready",started);
    let mut score=context.score_endpoint_stream(&stream).expect("native first-modern Score seed");
    let endpoints=score_calendar();
    assert_eq!(score.remaining_owners(),7542);
    assert_eq!(score.next_owner(),Some(endpoints[1].0));
    assert_eq!(score.record_payload_bytes(),2*256);
    assert_eq!(score.terminal_r().unwrap_err(),"Score endpoint incomplete R closure");
    assert_eq!(score.closed_owner_cells(845_759).unwrap_err(),"Score endpoint incomplete R closure");
    assert_eq!(score.closed_owner_relation(845_759).err().unwrap(),
        "Score endpoint incomplete R closure");
    assert_eq!(score.push_native(endpoints[2].0).unwrap_err(),"Score endpoint exact ascending owner");
    assert_eq!(score.remaining_owners(),7542);
    assert_eq!(score.next_owner(),Some(endpoints[1].0));
    phase("score_seed_verified",started);
    for (index,(owner,_)) in endpoints.iter().enumerate().skip(1) {
        assert_eq!(score.next_owner(),Some(*owner),"Score owner index {index}");
        if index==endpoints.len()-1 {
            assert_eq!(score.remaining_owners(),1);
            assert_eq!(score.closed_owner_cells(845_759).unwrap_err(),
                "Score endpoint incomplete R closure");
            println!("C187_SCORE_PARTIAL_REPLAY_REJECT owners=7542 remaining=1");
        }
        score.push_native(*owner).expect("native Score endpoint append");
        assert_eq!(score.remaining_owners(),endpoints.len()-index-1);
        if [1,32,128,7542].contains(&index) {
            println!("C187_SCORE_PROGRESS appended={} total_owners={} remaining={} elapsed_s={:.6}",
                index,index+1,score.remaining_owners(),started.elapsed().as_secs_f64());
            std::io::stdout().flush().expect("flush c187 Score progress");
        }
    }
    assert!(score.is_closed());
    assert_eq!(score.next_owner(),None);
    assert_eq!(score.remaining_owners(),0);
    assert_eq!(score.record_payload_bytes(),15_083*256);
    assert!(score.retained_capacity_bytes()<16*1024*1024,
        "local Score record/lease capacity only");
    let terminal=score.terminal_r().expect("both native Score guards closed");
    assert!(terminal.iter().all(|r|!r.is_zero() && r.bits()<=225));
    phase("score_closed",started);

    if c518 {
        use ark_ff::{BigInteger,PrimeField};
        // Diagnostic vector only; it is not a public transcript challenge.
        let r=(2u64..42).map(Fr::from).collect::<Vec<_>>();
        let (polynomial,metrics,qualified,reads)=score.c518_selected_u0(&r)
            .expect("C518 one terminal-closed source and five physical families");
        assert_eq!(metrics.term_visits,520_693);
        assert_eq!(qualified,reads,"C518 every qualified demand is physically read");
        assert_eq!(qualified.iter().sum::<usize>(),metrics.demands);
        assert!(qualified.iter().all(|count|*count>0));
        assert!((polynomial[0]+polynomial[0]+polynomial[1]+polynomial[2]).is_zero(),
            "C518 authored source bits satisfy the selected Boolean ROW sum");
        let mut polynomial_bytes=Vec::with_capacity(96);
        for value in &polynomial {polynomial_bytes.extend(value.into_bigint().to_bytes_le());}
        let coefficient_sha256=hex(&role0_sha256(&polynomial_bytes)
            .expect("C518 polynomial diagnostic digest"));
        println!("C518_SAME_STREAM_PHYSICAL_U0_PASS owner=845887 terms={} demands={} family_order=[845887,845759,844798,845885,845886] qualified={qualified:?} reads={reads:?} unique_coordinates={} duplicate_loads={} coefficient_sha256={coefficient_sha256} r=fixed_2_through_41 boolean_sum_zero=true same_stream=true previous_r_owner=845759 max_owner=844798 work_owners=[845885,845886] full_role1=false global_x=false gkr=false pcs=false proof=false client=false production=false",
            metrics.term_visits,metrics.demands,metrics.unique_coordinates,metrics.duplicate_loads);
        phase("c518_same_stream_physical_u0_verified",started);
        return;
    }

    if c517 {
        const OWNER:usize=845_887;
        const ROWS:usize=1<<19;
        let carrier=score.closed_regular_carrier()
            .expect("C517 terminal-closed source and same-context census carrier");
        let slot_counts=carrier.with_c514(|edges,sidecar| {
            assert_eq!(edges.len(),520_693,"C517 exact ordered C509 term occurrences");
            assert_eq!(sidecar.len(),520_693,"C517 exact ordered C514 identity occurrences");
            let mut counts=[0usize;15];
            let mut previous_rank=0usize;
            for (ordinal,(edge,identity)) in edges.iter().zip(sidecar).enumerate() {
                assert_eq!(identity.occurrence,ordinal,"C517 complete source occurrence ordinal");
                assert_eq!(edge.source_slot,OWNER,"C517 exact owner source slot");
                assert!(identity.slot<counts.len(),"C517 fifteen-slot identity bound");
                let rank=match identity.relation {
                    crate::header_daa_row_placement::C509Relation::Ordinary(_)=>0,
                    crate::header_daa_row_placement::C509Relation::Map(context)=>1+context,
                    crate::header_daa_row_placement::C509Relation::Score(context)=>3+context,
                    crate::header_daa_row_placement::C509Relation::Slack(context)=>5+context,
                };
                assert!(previous_rank<=rank,"C517 ordinary/Map/Score/Slack source order");
                previous_rank=rank;
                match identity.relation {
                    crate::header_daa_row_placement::C509Relation::Ordinary(_)=>
                        assert!(identity.slot<9,"C517 ordinary relation slot"),
                    crate::header_daa_row_placement::C509Relation::Map(context)=>
                        assert_eq!(identity.slot,9+context,"C517 Map context slot"),
                    crate::header_daa_row_placement::C509Relation::Score(context)=>
                        assert_eq!(identity.slot,11+context,"C517 Score context slot"),
                    crate::header_daa_row_placement::C509Relation::Slack(context)=>
                        assert_eq!(identity.slot,13+context,"C517 Slack context slot"),
                }
                counts[identity.slot]+=1;
                assert!(edge.family_row<ROWS,"C517 local ROW coordinate bound");
                assert_eq!(edge.term.row,OWNER*ROWS+edge.family_row,
                    "C517 edge term retains exact source ROW coordinate");
                assert!(edge.term.gate.left<(1usize<<41),"C517 left X-domain coordinate");
                assert!(edge.term.gate.right<(1usize<<41),"C517 right X-domain coordinate");
            }
            assert_eq!(counts.iter().sum::<usize>(),520_693);
            assert!(counts[9..].iter().all(|count|*count>0),
                "C517 Map/Score/Slack context slots remain represented");
            counts
        }).expect("C517 checked C509 batch and scoped C514 edge consumer");
        println!("C517_TERMINAL_CLOSED_REGULAR_ROW_PASS owner=845887 term_occurrences=520693 relation_slots=15 slot_counts={slot_counts:?} source_order=true duplicate_occurrences_preserved=true source_binding_and_layout_checked=true full_u0=false physical_x=false global_x=false gkr=false pcs=false proof=false client=false production=false");
        phase("c517_closed_regular_row_verified",started);
        return;
    }

    if c489 {
        let score_roles=endpoints.iter().map(|(_,roles)|roles.iter()
            .filter(|role|role.is_some()).count()).sum();
        let marker=score.c489_native_score_slack_join(
            c489_observed_frame_sha.as_deref().expect("C489 verified frame evidence"),
            owners.len(),endpoints.len(),score_roles)
            .expect("C489 native selected Score/Slack join");
        println!("{marker}");phase("c489_score_slack_complete",started);return;
    }

    if c488 {
        let score_roles=endpoints.iter().map(|(_,roles)|roles.iter().filter(|role|role.is_some()).count()).sum();
        let marker=score.c488_native_score_import(
            c488_observed_frame_sha.as_deref().expect("C488 verified frame evidence"),
            owners.len(),endpoints.len(),score_roles).expect("C488 native Score import seam");
        println!("{marker}");phase("c488_score_import_complete",started);return;
    }

    if c487 {
        let score_roles=endpoints.iter().map(|(_,roles)|
            roles.iter().filter(|role|role.is_some()).count()).sum();
        let marker=score.c487_terminal_public_binding(
            c487_observed_frame_sha.as_deref().expect("C487 verified frame evidence"),
            owners.len(),endpoints.len(),score_roles)
            .expect("C487 source-owned terminal public binding");
        println!("{marker}");
        phase("c487_terminal_public_complete",started);
        return;
    }

    if c445 {
        assert!(!scored_owner && !packed_scored_owner);
        let cases = [
            (846_015usize, [true, true], 20_480usize,
                [(846_016usize, 845_887usize, 844_926usize, 846_015usize),
                 (846_016usize, 845_887usize, 844_926usize, 846_015usize)]),
            (1_810_879usize, [true, false], 16_384usize,
                [(1_810_880usize, 1_810_751usize, 1_809_790usize, 1_810_879usize),
                 (0usize, 0usize, 0usize, 0usize)]),
        ];
        for (owner, active, expected_cells, tuples) in cases {
            let schedule = crate::packed_owner_assembly::Eligible08RegularScoreOwner::classify(owner)
                .expect("C445 regular Eligible08 Score owner classification");
            assert_eq!(schedule.active(), active);
            assert_eq!(schedule.typed_cell_count(), expected_cells);
            assert_eq!(schedule.previous_r_owner(), tuples[0].1);
            assert_eq!(schedule.max_owner(), tuples[0].2);
            let relation = score.closed_owner_relation(owner)
                .expect("terminal-closed native Score relation C445 owner");
            assert_eq!(relation.owner(), owner);
            assert_eq!(relation.parent_root(), plan.descriptor().root);
            assert_eq!(relation.parent_total(), plan.work_profile().total_be28);
            let binding = crate::packed_owner_assembly::HeaderSourceBinding::for_plan(&plan, owner)
                .expect("C445 parent/source binding");
            assert!(binding.matches_sink(relation.parent_root(), relation.parent_total(),
                relation.parent_profile(), relation.cut_identity(), owner));
            for context_index in 0..2 {
                match (active[context_index], relation.authors()[context_index]) {
                    (true, Some(author)) => assert_eq!(
                        (author.context, author.origin, author.previous_owner,
                            author.max_owner, author.cap_owner),
                        (context_index, tuples[context_index].0, tuples[context_index].1,
                            tuples[context_index].2, tuples[context_index].3),
                    ),
                    (false, None) => {},
                    _ => panic!("C445 relation context author mask owner={owner} context={context_index}"),
                }
                assert_eq!(!relation.terms(context_index).unwrap().is_empty(), active[context_index]);
            }
            assert_eq!(relation.cells().len(), active.iter().filter(|is_active| **is_active).count()*2048);
            assert_eq!(relation.reads().len(), active.iter().filter(|is_active| **is_active).count()*(225+65+224));
            let joined = context.join_scored_owner_source(owner, relation, &stream)
                .expect("native Score/Cap source join C445 owner");
            assert_eq!(joined.owner(), owner);
            let terms = joined.source_term_counts().expect("retained C445 source terms");
            assert!(terms.iter().all(|count| *count > 0));
            let header_daa = joined.retained_header_daa_active_operand_count();
            assert!(header_daa > 0);
            let expected_open_reads = joined.selected_open_reads().to_vec();
            assert!(!expected_open_reads.is_empty());
            let selected_open = expected_open_reads.len();
            // At the tail, context 1 keeps local zero Map cells but its cut
            // has passed, so it has no foreign Map read.
            let expected_selected_open = if active[1] { 1_794 } else { 897 };
            assert_eq!(selected_open, expected_selected_open,
                "C445 exact selected open-read census owner={owner}");
            let view = crate::packed_owner_assembly::ScoredOwnerPackingView::from_checked_join(joined)
                .expect("source-retaining C445 packing view");
            let candidate = producer.produce_scored_owner_packed_source_lease(view)
                .expect("ordinary Carry C445 physical packed-source admission");
            assert_eq!(candidate.owner(), owner);
            assert_eq!(candidate.binding().expect("checked C445 row/source binding"), &binding);
            candidate.check_daa_author().expect("retained C445 CarryZero DAA author");
            let packed = candidate.partial_packed_bytes();
            assert_eq!(packed.len(), OWNER_ROW_BITS/8);
            assert_eq!(candidate.source_cells().len(), expected_cells);
            let mut zero_cells = 0usize;
            let mut authors = [0usize; 8];
            for cell in candidate.source_cells() {
                let local = cell.wire() % OWNER_ROW_BITS;
                let bit = ((packed[local/8] >> (local%8)) & 1) != 0;
                assert_eq!(bit, cell.value(), "C445 typed source/packed mismatch wire {}", cell.wire());
                zero_cells += usize::from(!cell.value());
                match cell.author() {
                    crate::packed_owner_assembly::ScoredOwnerPackedAuthor::Map(context) => {
                        assert!(context < 2);
                        authors[context] += 1;
                    }
                    crate::packed_owner_assembly::ScoredOwnerPackedAuthor::Score(author) => {
                        assert!(author.context < 2);
                        assert!(active[author.context]);
                        assert_eq!((author.origin, author.previous_owner, author.max_owner, author.cap_owner),
                            (owner+1, schedule.previous_r_owner(), schedule.max_owner(), owner));
                        authors[2+author.context] += 1;
                    }
                    crate::packed_owner_assembly::ScoredOwnerPackedAuthor::Slack(context) => {
                        assert!(context < 2);
                        authors[4+context] += 1;
                    }
                    crate::packed_owner_assembly::ScoredOwnerPackedAuthor::Cap { context: c, origin } => {
                        assert!(c < 2);
                        assert!(active[c]);
                        assert_eq!(origin, owner+1);
                        authors[6+c] += 1;
                    }
                }
            }
            assert!(zero_cells > 0, "C445 retains zero-valued authored cells");
            assert_eq!(authors, [5757, 5757, 2048*(active[0] as usize), 2048*(active[1] as usize),
                387, 387, 2048*(active[0] as usize), 2048*(active[1] as usize)]);
            assert_eq!(candidate.source_term_counts(), terms);
            assert_eq!(candidate.retained_header_daa_active_operand_count(), header_daa);
            assert_eq!(candidate.selected_open_reads().len(), selected_open);
            assert_eq!(candidate.selected_open_reads(), expected_open_reads.as_slice());
            candidate.require_source_x_conflict_rejected_for_test()
                .expect("C445 pre-existing X claim rejects atomically");
            phase("c445_scored_owner_packed_source_verified", started);
        }
        println!("C445_AUTHENTIC_REGULAR_SCORE_PACKED owner=846015 active_contexts=0,1 cells=20480 frame_parses=1 global_row=false proof=false client=false");
        println!("C445_AUTHENTIC_REGULAR_SCORE_PACKED owner=1810879 active_contexts=0 cells=16384 frame_parses=1 global_row=false proof=false client=false");
        return;
    }

    if c512h {
        use crate::packed_owner_assembly::ScoredOwnerPackingView;
        use crate::header_daa_row_placement::C509RegularBatch;
        let relation=score.closed_owner_relation(845_887).expect("C512h closed regular Score relation");
        let typed=relation.reads().to_vec();
        c512h_check_typed_cap_census(&typed)
            .expect("C512h typed Score domains and exact65 local Cap q bits per context");
        let joined=context.join_scored_owner_source(845_887,relation,&stream)
            .expect("C512h same-context Score/Cap source join");
        let view=ScoredOwnerPackingView::from_checked_join(joined)
            .expect("C512h one checked packing view");
        let census=producer.produce_regular_owner845887_author_census(view)
            .expect("C512h actual regular owner row and zero-inclusive author census");
        let (active,selected,layout,counts)={
            let binding=census.binding().expect("C512h regular binding");
            let source=census.c509_regular_row_source().expect("C512h same-census C509 borrow");
            let batch=C509RegularBatch::checked_from_source(&source,binding)
                .expect("C512h exact fifteen-relation C509 batch");
            let counts=batch.counts().expect("C512h source term counts");
            assert_eq!(counts.iter().sum::<usize>(),520_693);
            let layout=batch.layout_digest().expect("C512h source ROW layout");
            let active=batch.active_operands().expect("C512h exact active tuples").collect::<Vec<_>>();
            assert_eq!(active.len(),730_942);
            let selected=source.selected_open_reads().expect("C512h retained typed open reads").to_vec();
            (active,selected,layout,counts)
        };
        println!("C512H_CONSUMER_RETAINED owner=845887 terms=520693 active={} active_capacity={} selected_typed={} one_candidate=true frame_parses=1 physical_join=false numeric_row=false gkr=false pcs=false",
            active.len(),active.capacity(),selected.len());
        c512h_retained=Some((census,active,typed,selected,layout,counts));
        phase("c512h_regular_writer_and_c509_retained",started);
    }

    if scored_owner || packed_scored_owner || c511_regular_row {
        // The same pinned frame, plan, prefix and closed source streams now
        // traverse the complete C390 producer-to-consumer API exactly once.
        // This still has no global X/ROW admission or proof/client authority.
        let relation = score.closed_owner_relation(845_887)
            .expect("terminal-closed native Score relation owner845887");
        let c512_typed_score_reads=if c512_previous_r_physical_join {
            relation.reads().to_vec()
        }else{Vec::new()};
        for author in relation.authors() {
            let author = author.expect("both Score contexts active at owner845887");
            assert_eq!((author.origin, author.previous_owner,
                author.max_owner, author.cap_owner),
                (845_888, 845_759, 844_798, 845_887));
        }
        let joined = context.join_scored_owner_source(845_887, relation, &stream)
            .expect("native Score/Cap local source join owner845887");
        assert_eq!(joined.owner(), 845_887);
        let terms = joined.source_term_counts().expect("retained exact source terms");
        assert!(terms.iter().all(|count| *count > 0));
        let header_daa = joined.retained_header_daa_active_operand_count();
        assert!(header_daa > 0);
        let selected_open = joined.selected_open_reads().len();
        assert!(selected_open > 2 * (225 + 224 + 224));
        if scored_owner {
            println!("C390_NATIVE_SCORED_OWNER_JOIN owner=845887 source_terms={terms:?} retained_header_daa_active_operands={header_daa} selected_open_reads={selected_open} global_x_row=false proof=false client=false");
            phase("scored_owner_join_verified", started);
            return;
        }
        let expected_open_reads = joined.selected_open_reads().to_vec();
        let view = crate::packed_owner_assembly::ScoredOwnerPackingView::from_checked_join(joined)
            .expect("source-retaining C396 packing view");
        let candidate = producer.produce_scored_owner_packed_source_lease(view)
            .expect("ordinary Carry 845887 physical packed-source admission");
        let binding = crate::packed_owner_assembly::HeaderSourceBinding::for_plan(&plan, 845_887)
            .expect("owner845887 parent binding");
        assert_eq!(candidate.owner(), 845_887);
        assert_eq!(candidate.binding().expect("checked row/source binding"), &binding);
        candidate.check_daa_author().expect("retained CarryZero DAA author");
        let packed = candidate.partial_packed_bytes();
        assert_eq!(packed.len(), OWNER_ROW_BITS / 8);
        assert_eq!(candidate.source_cells().len(), 20_480);
        let mut zero_cells = 0usize;
        for cell in candidate.source_cells() {
            let local = cell.wire() % OWNER_ROW_BITS;
            let bit = ((packed[local / 8] >> (local % 8)) & 1) != 0;
            assert_eq!(bit, cell.value(), "typed source/packed mismatch wire {}", cell.wire());
            zero_cells += usize::from(!cell.value());
        }
        assert!(zero_cells > 0, "zero-valued authored cells remain in the census");
        assert_eq!(candidate.source_term_counts(), terms);
        assert_eq!(candidate.retained_header_daa_active_operand_count(), header_daa);
        assert_eq!(candidate.selected_open_reads().len(), selected_open);
        assert_eq!(candidate.selected_open_reads(), expected_open_reads.as_slice());
        assert!(!candidate.selected_open_reads().is_empty());
        if c511_regular_row {
            use crate::header_daa_row_placement::{
                C509ActiveOperand, C509Relation, OperandSide,
            };

            // Borrow the ROW source from this exact native packed candidate.
            // The C509 batch retains its binding and source view, and never
            // upgrades typed source cells or open imports to physical X.
            let row_source = candidate.c509_regular_row_source()
                .expect("C511 same-candidate regular ROW source view");
            let candidate_binding = candidate.binding()
                .expect("C511 retained candidate binding");
            assert_eq!(candidate_binding, &binding);
            assert_eq!(row_source.owner().expect("C511 source owner"), 845_887);
            assert_eq!(row_source.binding().expect("C511 source binding"), candidate_binding);
            let batch = crate::header_daa_row_placement::C509RegularBatch::checked_from_source(
                &row_source, candidate_binding,
            ).expect("C511 fifteen-slot batch from the same native source");

            let source_ordinary = row_source.terms()
                .expect("C511 ordered ordinary source terms")
                .collect::<Vec<_>>();
            let map_counts = [
                row_source.map_terms(0).expect("C511 Map0 source terms").len(),
                row_source.map_terms(1).expect("C511 Map1 source terms").len(),
            ];
            let score_counts = [
                row_source.score_terms(0).expect("C511 Score0 source terms").len(),
                row_source.score_terms(1).expect("C511 Score1 source terms").len(),
            ];
            let slack_counts = [
                row_source.slack_terms(0).expect("C511 Slack0 source terms").len(),
                row_source.slack_terms(1).expect("C511 Slack1 source terms").len(),
            ];
            assert!(map_counts.iter().all(|count| *count > 0));
            assert!(score_counts.iter().all(|count| *count > 0));
            assert!(slack_counts.iter().all(|count| *count > 0));

            let ordered_terms = batch.terms()
                .expect("C511 revalidated ordered batch terms")
                .collect::<Vec<_>>();
            let counts = batch.counts().expect("C511 fifteen relation counts");
            assert_eq!(ordered_terms.len(), counts.iter().sum::<usize>());
            assert_eq!(counts[..9].iter().sum::<usize>(), source_ordinary.len());
            assert_eq!([counts[9], counts[10]], map_counts);
            assert_eq!([counts[11], counts[12]], score_counts);
            assert_eq!([counts[13], counts[14]], slack_counts);
            assert!(counts[9..].iter().all(|count| *count > 0));
            let source_counts = candidate.source_term_counts();
            assert_eq!(counts[9] + counts[10], source_counts[0]);
            assert_eq!(counts[11] + counts[12], source_counts[1]);
            assert_eq!(counts[13] + counts[14], source_counts[2]);

            // The batch's own revalidation checks every source tuple. Also
            // compare the retained ordinary prefix and ensure the six
            // versioned Map/Score/Slack groups remain in slot order.
            for (index, (relation, term)) in source_ordinary.iter().enumerate() {
                assert_eq!(ordered_terms[index].0, C509Relation::Ordinary(*relation));
                assert_eq!(ordered_terms[index].1, *term);
            }
            let mut previous_rank = 0usize;
            for (relation, _) in &ordered_terms {
                let rank = match *relation {
                    C509Relation::Ordinary(_) => 0,
                    C509Relation::Map(context) => {
                        assert!(context < 2);
                        1 + context
                    }
                    C509Relation::Score(context) => {
                        assert!(context < 2);
                        3 + context
                    }
                    C509Relation::Slack(context) => {
                        assert!(context < 2);
                        5 + context
                    }
                };
                assert!(previous_rank <= rank, "C511 fifteen-slot term order");
                previous_rank = rank;
            }

            let mut expected_active = Vec::new();
            for (occurrence, (relation, term)) in ordered_terms.iter().enumerate() {
                let c1_active = !term.gate.c1.is_zero();
                let c2_active = !term.gate.c2.is_zero();
                let c3_active = !term.gate.c3.is_zero();
                if c1_active || c3_active {
                    expected_active.push(C509ActiveOperand {
                        occurrence, relation: *relation, row: term.row,
                        side: OperandSide::Left, wire: term.gate.left,
                        c1_active, c2_active: false, c3_active,
                    });
                }
                if c2_active || c3_active {
                    expected_active.push(C509ActiveOperand {
                        occurrence, relation: *relation, row: term.row,
                        side: OperandSide::Right, wire: term.gate.right,
                        c1_active: false, c2_active, c3_active,
                    });
                }
            }
            let active_operands = batch.active_operands()
                .expect("C511 revalidated active operands")
                .collect::<Vec<_>>();
            assert!(!active_operands.is_empty());
            assert_eq!(active_operands, expected_active,
                "C511 occurrence, relation, row, side, wire and active coefficient identity");

            let typed_source_cells = row_source.candidate_cells()
                .expect("C511 retained typed source cells").len();
            assert_eq!(typed_source_cells, 20_480);
            let selected_open_reads = row_source.selected_open_reads()
                .expect("C511 retained selected open reads").len();
            assert_eq!(selected_open_reads, candidate.selected_open_reads().len());

            let source_binding = batch.source_binding()
                .expect("C511 batch source binding");
            assert_eq!(source_binding, candidate_binding);
            assert_eq!(source_binding, &binding);
            let layout_digest = batch.layout_digest()
                .expect("C511 regular ROW layout digest");
            assert_ne!(layout_digest, [0u8; 32]);
            assert_ne!(layout_digest,
                crate::header_daa_row_placement::Layout::paired_map_general().digest());
            assert_eq!(batch.layout_digest().expect("C511 stable layout digest"), layout_digest);
            let layout_digest_hex = layout_digest.iter()
                .map(|byte| format!("{byte:02x}"))
                .collect::<String>();

            if c512_previous_r_physical_join {
                let ordered_terms_len=ordered_terms.len();
                drop(ordered_terms);
                drop(source_ordinary);
                drop(batch);
                drop(row_source);
                let active_previous_r_candidates=active_operands.iter()
                    .filter(|operand|operand.wire/C512_WIRE_WIDTH==C512_PREVIOUS_OWNER).count();
                c512_c509_retained=Some((candidate,active_operands,c512_typed_score_reads));
                println!("C512B_C509_CONSUMER_READY owner=845887 ordered_terms={} active_previous_r_candidates={} frame_parses=1 physical_row=false global_x=false c513_row_gkr=false proof=false client=false",
                    ordered_terms_len,active_previous_r_candidates);
                phase("c512b_c509_consumer_retained",started);
            }else{
                println!(
                    "C511_NATIVE_REGULAR_ROW_PASS selector=c511_native_regular_row_owner845887_from_pinned_frame version=1 frame_parses=1 owner=845887 ordered_terms={} active_operands={} counts={counts:?} source_terms={source_counts:?} typed_source_cells={typed_source_cells} selected_open_reads={selected_open_reads} binding_valid=true layout_digest={layout_digest_hex} complete_owner_row=false physical_x=false global_x=false proof=false client=false production=false",
                    ordered_terms.len(), active_operands.len(),
                );
                phase("c511_regular_row_native_join_verified", started);
                return;
            }
        }else{
            candidate.require_source_x_conflict_rejected_for_test()
                .expect("one pre-existing X claim must reject atomically");
            println!("C396_NATIVE_PARTIAL_SCORED_OWNER_PACKED owner=845887 cells=20480 zero_cells={zero_cells} source_terms={terms:?} retained_header_daa_active_operands={header_daa} selected_open_reads={selected_open} x_conflict_rejected=true complete_slice=false global_proof=false client=false");
            phase("scored_owner_packed_source_verified", started);
            return;
        }
    }

    // An integer oracle consumes the native W interval and closed MAX/Cap V
    // lease. Only its initial P comes from the separately validated premodern
    // anchor; every modern endpoint R is computed without Score bit records.
    let sample_owners=BTreeSet::from([845_759,845_887,1_810_841,1_810_879,1_810_904]);
    let seed=score.closed_owner_cells(845_759).unwrap();
    let layout=crate::origin_score::Layout::new();
    let mut expected_fields=BTreeMap::new();
    for c in 0..2 {
        let seed_bits:Vec<_>=seed.iter().filter(|(_,author,_)|author.context==c)
            .map(|(_,_,value)|value.is_one()).collect();
        assert_eq!(seed_bits.len(),2048);
        let mut previous=integer_word(&seed_bits,layout.p.clone());
        let leases=stream.closed_score_endpoint_leases(c).expect("exact native Cap/MAX spans");
        assert_eq!(leases.len(),[7542,7541][c]);
        let tail=leases.last().unwrap();
        assert_eq!(tail.last_origin()-tail.first_origin()+1,[25,90][c]);
        assert_eq!(tail.max_owner(),[1_809_918,1_809_790][c]);
        for lease in &leases {
            let owner=lease.cap_owner();
            let (_,upper)=prefix.interval(lease.last_origin()).expect("native endpoint WORK");
            let w=BigUint::from_bytes_be(&upper);
            let v=lease.value().clone();
            let candidate=&w+&v*[4_995u64,2_090][c];
            let current=std::cmp::max(previous.clone(),candidate);
            if sample_owners.contains(&owner) {
                assert!(expected_fields.insert((owner,c),
                    (w,v,previous.clone(),current.clone())).is_none());
            }
            previous=current;
        }
        assert_eq!(terminal[c],previous,"native endpoint R context {c}");
    }
    assert_eq!(expected_fields.len(),7);

    // Replay is available only after closure. These samples cover the first
    // modern seed, both-context join, context1 freeze and both clipped tails.
    // Coordinates and four live words are checked, so an all-zero non-seed
    // record cannot masquerade as a correctly authored replay.
    for (owner,roles) in [
        (845_759,vec![(0,845_760,845_758,844_670),(1,845_760,845_758,844_670)]),
        (845_887,vec![(0,845_888,845_759,844_798),(1,845_888,845_759,844_798)]),
        (1_810_841,vec![(1,1_810_842,1_810_751,1_809_790)]),
        (1_810_879,vec![(0,1_810_880,1_810_751,1_809_790)]),
        (1_810_904,vec![(0,1_810_905,1_810_879,1_809_918)]),
    ] {
        let cells=score.closed_owner_cells(owner).expect("closed Score replay sample");
        assert_eq!(cells.len(),roles.len()*2048);
        assert!(cells.iter().all(|(_,_,v)|v.is_zero()||v.is_one()));
        assert_eq!(cells.iter().map(|(wire,_,_)|*wire).collect::<BTreeSet<_>>().len(),cells.len());
        let relation_started=Instant::now();
        let relation=score.closed_owner_relation(owner)
            .expect("terminal-closed native Score relation sample");
        let relation_us=relation_started.elapsed().as_micros();
        assert_eq!(relation.cells(),cells.as_slice(),"native Score relation/replay parity");
        assert_eq!(relation.reads().len(),roles.len()*(225+65+224));
        for context in 0..2 {
            let active=cells.iter().any(|(_,author,_)|author.context==context);
            assert_eq!(!relation.terms(context).unwrap().is_empty(),active,
                "native Score relation active context terms");
        }
        let map_slack_started=Instant::now();
        let mut joined=context.stage_with_slack(owner)
            .expect("native Map/Slack owner admission");
        let map_slack_us=map_slack_started.elapsed().as_micros();
        let score_admit_started=Instant::now();
        joined.admit_score_relation(relation)
            .expect("native Score relation admission");
        let score_admit_us=score_admit_started.elapsed().as_micros();
        let native_sink_lease=if owner==845_759 {
            Some(context.owner_score_slack_lease(joined)
                .expect("native Map/Score/Slack owner sink lease"))
        } else { drop(joined); None };
        for (context,origin,previous_owner,max_owner) in roles {
            let role:Vec<_>=cells.iter().filter(|(_,author,_)|author.context==context).collect();
            assert_eq!(role.len(),2048);
            assert!(role.iter().all(|(_,author,_)|author.origin==origin
                && author.previous_owner==previous_owner && author.max_owner==max_owner
                && author.cap_owner==owner));
            let bits:Vec<_>=role.iter().enumerate().map(|(bit,(wire,_,value))| {
                assert_eq!(*wire,owner*OWNER_ROW_BITS+SCORE_X[context]+bit);
                value.is_one()
            }).collect();
            assert!(bits[crate::origin_score::LIVE..crate::origin_score::INPUT]
                .iter().all(|bit|!*bit),"Score zero padding owner {owner} context {context}");
            let (w,v,p,r)=expected_fields.get(&(owner,context))
                .expect("independent native endpoint oracle sample");
            assert_eq!(integer_word(&bits,layout.sw.clone()),*w,"Score W owner {owner} context {context}");
            assert_eq!(integer_word(&bits,layout.sv.clone()),*v,"Score V owner {owner} context {context}");
            assert_eq!(integer_word(&bits,layout.p.clone()),*p,"Score P owner {owner} context {context}");
            assert_eq!(integer_word(&bits,layout.r.clone()),*r,"Score R owner {owner} context {context}");
            let physical=snapshot.owner_lease(owner).expect("physical Cap owner");
            let physical_cap: BTreeMap<usize,Fr>=physical.cells().into_iter()
                .filter(|(_,writer,_)|*writer==Writer::Cap{context,origin})
                .map(|(wire,_,value)|(wire,value)).collect();
            assert_eq!(physical_cap.len(),2048);
            for bit in 0..65 {
                let wire=owner*OWNER_ROW_BITS+CAP_X[context]+740+bit;
                let value=physical_cap.get(&wire).expect("physical Cap q bit");
                assert_eq!(value.is_one(),v.bit(bit as u64),
                    "Cap q/Score V owner {owner} context {context} bit {bit}");
            }
        }
        println!("C189_PROFILE owner={owner} relation_us={relation_us} map_slack_us={map_slack_us} score_admit_us={score_admit_us}");
        println!("C188_SCORE_STAGE owner={owner} score_cells={} score_reads={} map_slack_join=true",cells.len(),
            cells.len()/2048*(225+65+224));
        println!("C187_SCORE_REPLAY owner={owner} cells={}",cells.len());
        if let Some(lease)=native_sink_lease {
            let mut sink=context.owner_sink_845759()
                .expect("native context-bound owner sink");
            let admitted=sink.admit(lease).expect("native typed owner sink admission");
            let pending=sink.pending_sources();
            assert_eq!(admitted.cell_count(),16_384);
            assert!(admitted.term_count()>774,
                "native canonical Map terms plus Score/Slack ROWs");
            assert_eq!(admitted.pending_read_count(),1_476);
            assert_eq!(pending.len(),1_476);
            assert_eq!(pending.iter().filter(|read|matches!(read.required_author(),
                RequiredAuthor::WorkDifficulty {owner:845_759,height:845_761})).count(),448);
            assert_eq!(pending.iter().filter(|read|matches!(read.required_author(),
                RequiredAuthor::PreviousR {owner:845_758,..})).count(),450);
            assert_eq!(pending.iter().filter(|read|matches!(read.required_author(),
                RequiredAuthor::Cap {origin:845_760,max_owner:844_670,cap_owner:845_759,..})).count(),130);
            assert_eq!(pending.iter().filter(|read|matches!(read.required_author(),
                RequiredAuthor::WorkUpper {owner:845_758,height:845_760})).count(),448);
            let actual_map_wires:Vec<_>=pending.iter()
                .filter(|read|matches!(read.required_author(),
                    RequiredAuthor::WorkDifficulty {..}|RequiredAuthor::HeaderTimestamp {..}))
                .map(|read|read.wire()).collect();
            let map_wire_multiplicity:BTreeMap<usize,usize>=actual_map_wires.iter().fold(
                BTreeMap::new(),|mut counts,wire|{*counts.entry(*wire).or_default()+=1;counts});
            assert_eq!(actual_map_wires.len(),448);
            assert_eq!(map_wire_multiplicity.len(),224);
            assert!(map_wire_multiplicity.values().all(|count|*count==2),
                "both native Map consumers retain each shared Work-D source");
            assert!(pending.iter().all(|read|read.wire() < (1usize<<41)));
            println!("C192_NATIVE_OWNER_SINK owner=845759 cells={} terms={} pending={} map_work_d=448 previous_r=450 cap=130 work_upper=448",
                admitted.cell_count(),admitted.term_count(),admitted.pending_read_count());
            let retained_row19_terms = admitted.term_count();
            let non_work_reads: Vec<_> = sink.pending_sources().iter().filter(|read|
                !matches!(read.required_author(), RequiredAuthor::WorkDifficulty {..})).cloned().collect();
            let joined = context.join_owner_work_local_845759(&mut sink)
                .expect("native context-owned Work LOCAL to both Map D consumers");
            assert_eq!(joined.cell_count(), 16_608);
            assert_eq!(joined.term_count(), retained_row19_terms);
            assert_eq!(joined.pending_read_count(), 1_028);
            assert_eq!(sink.pending_sources(), non_work_reads.as_slice());
            assert_eq!(sink.retained_work_local_counts(), (3265, 1184));
            assert_eq!(context.join_owner_work_local_845759(&mut sink).err().unwrap(),
                "Eligible08 sink Work order/duplicate");
            assert_eq!(sink.pending_sources(), non_work_reads.as_slice());
            println!("C198_NATIVE_WORK_MAP_JOIN owner=845759 height=845761 cells=16608 row19_terms={} pending=1028 resolved_map_reads=448 work_local_terms=3265 work_local_operands=1184 duplicate_rejected=true row19_preserved=true non_work_reads_preserved=true global_x_row=false pcs_proof_client=false",
                retained_row19_terms);
            if r450 {
                phase("r450_sink_start", started);
                sink.c208_native_r450_probe_for_test(&context);
                phase("r450_sink_verified", started);
                if cap_upper {
                    phase("cap_upper_sink_start", started);
                    let closed = stream.closed_native_snapshot(&plan, &prefix)
                        .expect("same-process closed native MAX snapshot");
                    let admission = crate::h21_scheduled_family_ledger::Admission::new(
                        &plan, &prefix, closed).expect("native scheduled source admission");
                    let cap = admission.first_modern_cap_publication(&prefix)
                        .expect("real first-modern Cap publication");
                    sink.c210_native_cap_upper_probe_for_test(&context, cap);
                    phase("cap_upper_sink_verified", started);
                    assert_eq!(sink.pending_cap_max_read_count(), 448);
                    context.join_owner_cap_max_845759(&mut sink, &stream)
                        .expect("closed native MAX supplies every first-Cap import");
                    assert_eq!(sink.pending_cap_max_read_count(), 0);
                    assert_eq!(context.join_owner_cap_max_845759(&mut sink, &stream)
                        .unwrap_err(), "Eligible08 sink Cap MAX order/duplicate");
                    println!("C345_NATIVE_CAP_MAX_JOIN owner=845759 max_owner=844670 imports=448 pending=0 duplicate_rejected=true global_x_row=false pcs_proof_client=false");
                    phase("cap_max_sink_verified", started);

                    // The source-owner MAX replay now resolves the first Cap's
                    // foreign ROW operands, while owner 845759 keeps exactly
                    // the same local X claims. It does not claim owner 844670's
                    // packed X row.
                    use crate::daa_history_roster::DaaHistoryRoster;
                    use crate::header_daa_row_placement::{NativeRead,NativeXAuthor,Relation,RowPlan,UnresolvedRead};
                    let max_reads=context.foreign_max_read_lease_845759(&sink)
                        .expect("closed native MAX/Cap resolution read lease");
                    let expected_max=max_reads.cells().map(|cell|(cell.wire(),cell.value()))
                        .collect::<BTreeMap<_,_>>();
                    assert_eq!(expected_max.len(),448);
                    let first=snapshot.first_modern_cap_lease(&plan,&prefix)
                        .expect("same-parent first modern Cap lease");
                    let roster=DaaHistoryRoster::compile(&plan).expect("native ROW roster");
                    let scheduled=MaxPlan::eligible08();
                    let row_plan=RowPlan::new(&roster,&scheduled).expect("native ROW plan");
                    let cap0=row_plan.stage_owner_cap0_overlay(845_759,&plan,&prefix,&first)
                        .expect("first Cap0 source overlay");
                    let cap1=row_plan.stage_owner_cap1_overlay(845_759,&plan,&prefix,&first)
                        .expect("first Cap1 source overlay");
                    let overlay=sink.packed_overlay_845759(&context)
                        .expect("completed same-parent Eligible08 pre-pack overlay");
                    let (packed,daa,physical_census)=producer.produce_with_carry_zero_daa_cap01_overlay_census_source_lease(
                        845_759,&snapshot,&first,&overlay)
                        .expect("native Map/Score/Slack plus Cap01 packed row and author census");
                    let semantic_packed=sink.reconcile_local_packed_bits_845759(&context,&packed);
                    println!("C373_NATIVE_LOCAL_SEMANTIC_PACKED_JOIN owner=845759 result={semantic_packed:?} full_x_row=false proof=false client=false");
                    std::io::Write::flush(&mut std::io::stdout()).unwrap();
                    assert_eq!(semantic_packed.expect("native sink local semantic bits agree with packed row"),
                        (20_704,674));
                    let header=producer.header_source_lease(845_759)
                        .expect("native HEADER source lease");
                    let header_binding=crate::packed_owner_assembly::HeaderSourceBinding::for_plan(
                        &plan,845_759).expect("first modern HEADER destination binding");
                    let mut header_max_values=BTreeMap::new();
                    for context in 0..2 {
                        for bit in 0..673 {
                            let local=[999_424,1_000_097][context]+bit;
                            let wire=845_759*OWNER_ROW_BITS+local;
                            let value=header.read_header_bit(&header_binding,wire)
                                .expect("first modern HEADER MAX-coordinate source")
                                .expect("inactive MAX window belongs to HEADER");
                            let packed_value=(packed.packed_bytes()[local/8]>>(local%8))&1!=0;
                            assert_eq!(value,packed_value,"HEADER MAX-coordinate source/packed mismatch");
                            assert!(header_max_values.insert(wire,value).is_none());
                        }
                    }
                    assert_eq!(header_max_values.len(),1_346);
                    for local in [1_000_770,1_002_818,1_004_865] {
                        assert_eq!(header.read_header_bit(&header_binding,
                            845_759*OWNER_ROW_BITS+local).unwrap(),None,
                            "active Cap coordinate must never be HEADER-qualified");
                    }
                    let active_max_header=producer.header_source_lease(844_670)
                        .expect("active MAX owner HEADER source lease");
                    let active_max_binding=crate::packed_owner_assembly::HeaderSourceBinding::for_plan(
                        &plan,844_670).expect("active MAX owner binding");
                    for local in [999_424,1_000_096,1_000_097,1_000_769] {
                        assert_eq!(active_max_header.read_header_bit(&active_max_binding,
                            844_670*OWNER_ROW_BITS+local).unwrap(),None,
                            "active MAX coordinate must never be HEADER-qualified");
                    }
                    let before=row_plan.stage_owner_partial_x_row_with_cap01(
                        845_759,&packed,&header,&daa,&cap0,&cap1)
                        .expect("Cap01 partial X/ROW before MAX imports");
                    let after=row_plan.stage_owner_partial_x_row_with_cap01_and_foreign_max(
                        845_759,&packed,&header,&daa,&cap0,&cap1,&max_reads)
                        .expect("closed native MAX resolves Cap01 foreign reads");
                    assert_eq!(before.claims().copied().collect::<Vec<_>>(),
                        after.claims().copied().collect::<Vec<_>>(),
                        "foreign MAX reads must not create local X claims");
                    let old_cap_foreign=before.reads().filter(|read|matches!(read,
                        NativeRead::Unresolved{operand,reason:UnresolvedRead::ForeignOwner}
                            if matches!(operand.relation,Relation::Scheduled(Writer::Cap{context,origin})
                                if context<2 && origin==845_760))).count();
                    assert_eq!(old_cap_foreign,448);
                    let mut per_context=[0usize;2];
                    let mut seen=BTreeSet::new();
                    let mut foreign_open=0usize;
                    let mut local_open=0usize;
                    for read in after.reads() {
                        match *read {
                            NativeRead::ForeignMax{operand,cell} => {
                                let context=match operand.relation {
                                    Relation::Scheduled(Writer::Cap{context,origin})
                                        if context<2 && origin==845_760=>context,
                                    _=>panic!("foreign MAX changed consumer relation"),
                                };
                                assert_eq!(cell.context,context);
                                assert_eq!(cell.wire,operand.wire);
                                assert_eq!(expected_max.get(&cell.wire),Some(&cell.value));
                                assert!(seen.insert(cell.wire));
                                per_context[context]+=1;
                            }
                            NativeRead::Unresolved{reason:UnresolvedRead::ForeignOwner,..}=>foreign_open+=1,
                            NativeRead::Unresolved{reason:UnresolvedRead::UnqualifiedLocal,..}=>local_open+=1,
                            _=>{},
                        }
                    }
                    assert_eq!(per_context,[224,224]);
                    assert_eq!(seen.len(),448);
                    assert_eq!((foreign_open,local_open),(448,528));
                    let header_max_claims=after.claims().filter(|claim|
                        header_max_values.get(&claim.wire)==Some(&claim.value)
                            && claim.author==NativeXAuthor::Header).count();
                    assert_eq!(header_max_claims,1_346);
                    let mut residual=BTreeMap::<(String,usize),(usize,BTreeSet<usize>)>::new();
                    for read in after.reads() {
                        if let NativeRead::Unresolved{operand,..}=*read {
                            let entry=residual.entry((format!("{:?}",operand.relation),
                                operand.wire/(1<<20))).or_insert_with(||(0,BTreeSet::new()));
                            entry.0+=1;
                            entry.1.insert(operand.wire);
                        }
                    }
                    assert_eq!(residual.values().map(|(occurrences,_)|*occurrences).sum::<usize>(),976);
                    let residual_histogram=residual.iter().map(|((relation,source_owner),(occurrences,wires))|
                        format!("{relation}@{source_owner}:{occurrences}/{}",wires.len()))
                        .collect::<Vec<_>>().join(",");
                    println!("C370_RESIDUAL_HISTOGRAM owner=845759 occurrences/distinct_by_relation_source={residual_histogram}");
                    println!("C370_NATIVE_CAP_MAX_ROW_READ_JOIN owner=845759 max_owner=844670 foreign_max_reads=448 per_context=[224,224] other_foreign_open=448 other_local_open=528 local_header_max_claims=1346 foreign_x_claims=0 full_x_row=false proof=false client=false");
                    phase("cap_max_row_reads_verified", started);

                    let native_parent=snapshot.parent();
                    let mut expected_work=BTreeMap::new();
                    for source_owner in [845_757,845_758] {
                        let work=producer.native_work_d_lease(source_owner)
                            .expect("native source Work-D endpoint lease");
                        producer.require_work_d_lease(source_owner,&work)
                            .expect("native source Work-D exact replay");
                        for &(wire,value) in work.checked_cells(&native_parent,source_owner)
                            .expect("same-parent source Work-D cell census") {
                            assert!(expected_work.insert(wire,value==Fr::one()).is_none());
                        }
                    }
                    assert_eq!(expected_work.len(),448);
                    let foreign_daa=[
                        producer.foreign_daa_work_read_lease(845_757,845_759)
                            .expect("same-parent numeric DAA Work-D source owner 845757"),
                        producer.foreign_daa_work_read_lease(845_758,845_759)
                            .expect("same-parent numeric DAA Work-D source owner 845758"),
                    ];
                    let c367=row_plan.stage_owner_partial_x_row_with_cap01_and_foreign_max_and_daa_lane2(
                        845_759,&packed,&header,&daa,&cap0,&cap1,&max_reads,&foreign_daa)
                        .expect("two native Work-D leases close exact numeric DAA occurrences");
                    assert_eq!(before.claims().copied().collect::<Vec<_>>(),
                        c367.claims().copied().collect::<Vec<_>>(),
                        "foreign DAA reads must not create local X claims");
                    let(mut resolved_daa,mut foreign_open,mut local_open)=(0usize,0usize,0usize);
                    let(mut source_counts,mut source_wires)=([0usize;2],[BTreeSet::new(),BTreeSet::new()]);
                    let mut retained_max=0usize;
                    for read in c367.reads() {
                        match *read {
                            NativeRead::ForeignDaaLane2{operand,source_owner,wire,value} => {
                                assert_eq!(operand.relation,Relation::DaaLane(2));
                                assert_eq!(wire,operand.wire);
                                assert_eq!(wire/OWNER_ROW_BITS,source_owner);
                                assert_eq!(expected_work.get(&wire),Some(&value));
                                assert!((987_674..987_898).contains(&(wire%OWNER_ROW_BITS)));
                                let context=match source_owner {845_757=>0,845_758=>1,
                                    _=>panic!("C366 unexpected source owner")};
                                assert!(source_wires[context].insert(wire),"C366 duplicate source wire");
                                source_counts[context]+=1;resolved_daa+=1;
                            }
                            NativeRead::ForeignMax{..}=>retained_max+=1,
                            NativeRead::Unresolved{reason:UnresolvedRead::ForeignOwner,..}=>foreign_open+=1,
                            NativeRead::Unresolved{reason:UnresolvedRead::UnqualifiedLocal,..}=>local_open+=1,
                            _=>{},
                        }
                    }
                    assert_eq!(resolved_daa,448);
                    assert_eq!(source_counts,[224,224]);
                    assert_eq!(source_wires.map(|wires|wires.len()),[224,224]);
                    assert_eq!((retained_max,foreign_open,local_open),(448,0,528));
                    println!("C370_NATIVE_FOREIGN_DAA_WORK_ROW_JOIN owner=845759 sources=[845757,845758] relation_lane=2 source=NativeWorkD resolved=448 per_source=[224,224] distinct_wires=[224,224] prior_foreign_max=448 remaining_foreign_open=0 local_open=528 local_header_max_claims=1346 foreign_x_claims=0 full_x_row=false proof=false client=false");

                    let replacement=plan.physical_assignment_replacement_mask(845_759u64)
                        .expect("native parent replacement mask for local-open census");
                    let mut local_histogram=BTreeMap::<(String,String),(usize,BTreeSet<usize>)>::new();
                    for read in c367.reads() {
                        if let NativeRead::Unresolved{operand,reason:UnresolvedRead::UnqualifiedLocal}=*read {
                            let local=operand.wire%OWNER_ROW_BITS;
                            let domain=if (BANK53_BASE..BANK53_BASE+2*BANK53_CONTEXT_BITS).contains(&local) {
                                "bank53"
                            } else if (crate::segment_points::POINT_OFFSET..
                                crate::header_order::ORDER_OFFSET).contains(&local) {
                                "point-window"
                            } else if (crate::header_order::ORDER_OFFSET..795_648).contains(&local) {
                                "header-order"
                            } else if (999_424..1_004_866).contains(&local) {
                                "scheduled-max-cap"
                            } else if crate::daa_history_roster::BANKS.iter()
                                .any(|&(start,end)|(start..end).contains(&local)) {
                                "daa-bank"
                            } else if replacement[local] {"parent-replacement"}
                            else {"other/unclassified"};
                            let key=(format!("{:?}",operand.relation),domain.to_string());
                            let entry=local_histogram.entry(key).or_insert_with(||(0,BTreeSet::new()));
                            entry.0+=1;entry.1.insert(local);
                        }
                    }
                    let census=local_histogram.iter().map(|((relation,domain),(occurrences,wires))|
                        format!("{relation}/{domain}:{occurrences}/{}",wires.len()))
                        .collect::<Vec<_>>().join(",");
                    assert_eq!(local_histogram.values().map(|(count,_)|*count).sum::<usize>(),528);
                    assert_eq!(census,"Header/point-window:528/528");
                    println!("C370_LOCAL_OPEN_HISTOGRAM owner=845759 physical_local_x_occurrences/distinct_wires={census}");
                    phase("foreign_daa_row_reads_verified", started);

                    // The local MAX-coordinate reads are HEADER-owned at this
                    // inactive MAX owner. Mutate each side independently to
                    // prove the source/packed join rejects a disagreement.
                    let mut packed_header_max_fault=packed.clone();
                    crate::packed_owner_assembly::flip_native_row_bit_for_test(
                        &mut packed_header_max_fault,999_424).expect("flip one HEADER-owned MAX-coordinate bit");
                    assert!(row_plan.stage_owner_partial_x_row_with_cap01_and_foreign_max_and_daa_lane2(
                        845_759,&packed_header_max_fault,&header,&daa,&cap0,&cap1,&max_reads,
                        &foreign_daa).is_err(),
                        "C370 rejects packed-only HEADER MAX-coordinate mutation");
                    let mut header_max_fault=producer.header_source_lease(845_759)
                        .expect("second native HEADER source for source-only mutant");
                    header_max_fault.flip_source_value_for_test(999_424);
                    assert!(row_plan.stage_owner_partial_x_row_with_cap01_and_foreign_max_and_daa_lane2(
                        845_759,&packed,&header_max_fault,&daa,&cap0,&cap1,&max_reads,
                        &foreign_daa).is_err(),
                        "C370 rejects source-only HEADER MAX-coordinate mutation");
                    let mut wrong_header_author=producer.header_source_lease(845_759)
                        .expect("third native HEADER source for author mutant");
                    wrong_header_author.wrong_author_mutant_for_test();
                    assert!(row_plan.stage_owner_partial_x_row_with_cap01_and_foreign_max_and_daa_lane2(
                        845_759,&packed,&wrong_header_author,&daa,&cap0,&cap1,&max_reads,
                        &foreign_daa).is_err(),
                        "C370 rejects wrong HEADER author before read admission");
                    println!("C370_NATIVE_HEADER_MAX_WINDOW owner=845759 source=canonical_header_template resolved=1346 per_context=[673,673] active_max_owner_rejected=true active_cap_window_rejected=true packed_fault_rejected=true source_fault_rejected=true wrong_author_rejected=true local_open=528 full_x_row=false proof=false client=false");
                    phase("header_max_window_verified", started);

                    let old_claims=c367.claims().map(|claim|(claim.wire,(claim.author,claim.value)))
                        .collect::<BTreeMap<_,_>>();
                    assert_eq!(old_claims.len(),c367.claims().len());
                    for (wire,value) in &header_max_values {
                        assert_eq!(old_claims.get(wire),Some(&(NativeXAuthor::Header,*value)));
                    }
                    let mut point_wires=BTreeSet::new();
                    for read in c367.reads() {
                        if let NativeRead::Unresolved{operand,reason:UnresolvedRead::UnqualifiedLocal}=*read {
                            assert_eq!(operand.relation,Relation::Header);
                            assert!(point_wires.insert(operand.wire));
                        }
                    }
                    assert_eq!(point_wires.len(),528);
                    assert!(point_wires.iter().copied().eq((1..=528).map(|bit|
                        845_759*OWNER_ROW_BITS+crate::segment_points::POINT_OFFSET+bit)),
                        "C370 point reads must be the two compressed source points");

                    // The point source comes from the canonical parent header,
                    // independently of these packed destination bytes.
                    let point_binding=crate::packed_owner_assembly::HeaderSourceBinding::for_plan(
                        &plan,845_759).expect("native point destination binding");
                    let point_source=producer.point_membership_source_lease(845_759)
                        .expect("parent-header-derived point membership source");
                    point_source.check_binding(&point_binding).expect("point source parent binding");
                    point_source.check_author().expect("point source author");
                    let c370=row_plan.stage_owner_partial_x_row_with_cap01_and_foreign_max_and_daa_lane2_and_point(
                        845_759,&packed,&header,&daa,&cap0,&cap1,&max_reads,&foreign_daa,
                        &point_source)
                        .expect("independent point source joins 528 local HEADER reads");
                    let point_claims=c370.claims().map(|claim|(claim.wire,(claim.author,claim.value)))
                        .collect::<BTreeMap<_,_>>();
                    assert_eq!(point_claims.len(),c370.claims().len());
                    assert_eq!(point_claims.len(),old_claims.len()+528);
                    for (wire,claim) in &old_claims {
                        assert_eq!(point_claims.get(wire),Some(claim),
                            "C370 must preserve every previous local X claim");
                    }
                    for wire in &point_wires {
                        let value=point_source.read_point_bit(&point_binding,*wire)
                            .expect("independent point witness bit");
                        let local=*wire%OWNER_ROW_BITS;
                        let packed_value=(packed.packed_bytes()[local/8]>>(local%8))&1!=0;
                        assert_eq!(value,packed_value,"point source differs from packed owner row");
                        assert_eq!(point_claims.get(wire),
                            Some(&(NativeXAuthor::PointMembership,value)));
                        assert!(!old_claims.contains_key(wire));
                    }
                    let(mut point_reads,mut retained_foreign_max,mut retained_foreign_daa,
                        mut foreign_open,mut local_open)=(0usize,0usize,0usize,0usize,0usize);
                    let mut resolved_point_wires=BTreeSet::new();
                    for read in c370.reads() {
                        match *read {
                            NativeRead::PointMembership{operand,value}=>{
                                assert_eq!(operand.relation,Relation::Header);
                                assert!(point_wires.contains(&operand.wire));
                                assert_eq!(value,point_source.read_point_bit(
                                    &point_binding,operand.wire).expect("point source read"));
                                assert!(resolved_point_wires.insert(operand.wire));
                                point_reads+=1;
                            }
                            NativeRead::ForeignMax{..}=>retained_foreign_max+=1,
                            NativeRead::ForeignDaaLane2{..}=>retained_foreign_daa+=1,
                            NativeRead::Unresolved{reason:UnresolvedRead::ForeignOwner,..}=>foreign_open+=1,
                            NativeRead::Unresolved{reason:UnresolvedRead::UnqualifiedLocal,..}=>local_open+=1,
                            _=>{},
                        }
                    }
                    assert_eq!(resolved_point_wires,point_wires);
                    assert_eq!((point_reads,retained_foreign_max,retained_foreign_daa,
                        foreign_open,local_open),(528,448,448,0,0));
                    let first_point_wire=*point_wires.iter().next().expect("C370 point read census");
                    let first_point_local=first_point_wire%OWNER_ROW_BITS-
                        crate::segment_points::POINT_OFFSET;
                    let mut wrong_point_value=producer.point_membership_source_lease(845_759)
                        .expect("second parent-derived point source for mutant");
                    wrong_point_value.flip_source_value_for_test(first_point_local);
                    assert!(row_plan.stage_owner_partial_x_row_with_cap01_and_foreign_max_and_daa_lane2_and_point(
                        845_759,&packed,&header,&daa,&cap0,&cap1,&max_reads,&foreign_daa,
                        &wrong_point_value).is_err(),
                        "C370 must reject source-only point value mutation");
                    let mut wrong_packed_point=packed.clone();
                    crate::packed_owner_assembly::flip_native_row_bit_for_test(
                        &mut wrong_packed_point,first_point_wire%OWNER_ROW_BITS)
                        .expect("flip one packed point bit");
                    assert!(row_plan.stage_owner_partial_x_row_with_cap01_and_foreign_max_and_daa_lane2_and_point(
                        845_759,&wrong_packed_point,&header,&daa,&cap0,&cap1,&max_reads,&foreign_daa,
                        &point_source).is_err(),
                        "C370 must reject packed-only point value mutation");
                    let mut wrong_point_parent=producer.point_membership_source_lease(845_759)
                        .expect("third parent-derived point source for binding mutant");
                    wrong_point_parent.mutate_binding_field_for_test(0);
                    assert!(row_plan.stage_owner_partial_x_row_with_cap01_and_foreign_max_and_daa_lane2_and_point(
                        845_759,&packed,&header,&daa,&cap0,&cap1,&max_reads,&foreign_daa,
                        &wrong_point_parent).is_err(),
                        "C370 must reject wrong parent before point read admission");
                    let mut wrong_point_author=producer.point_membership_source_lease(845_759)
                        .expect("fourth parent-derived point source for author mutant");
                    wrong_point_author.wrong_author_mutant_for_test();
                    assert!(row_plan.stage_owner_partial_x_row_with_cap01_and_foreign_max_and_daa_lane2_and_point(
                        845_759,&packed,&header,&daa,&cap0,&cap1,&max_reads,&foreign_daa,
                        &wrong_point_author).is_err(),
                        "C370 must reject wrong point author before read admission");
                    println!("C370_NATIVE_POINT_ROW_X_JOIN owner=845759 source=parent_header_point_membership resolved=528 distinct_wires=528 new_point_claims=528 prior_claims_preserved=true retained_local_header_max=1346 retained_foreign_max=448 retained_foreign_daa=448 remaining_foreign_open=0 remaining_local_open=0 source_point_fault_rejected=true packed_point_fault_rejected=true wrong_parent_rejected=true wrong_author_rejected=true full_x_row=false proof=false client=false");
                    phase("point_membership_row_x_verified", started);
                    let physical_counts=c370.join_physical_census(&point_binding,&physical_census)
                        .expect("complete owner-local physical author census joins ROW claims");
                    assert_eq!(physical_counts,[536_622,8_192,401_362,81_920,16_384,4_096]);
                    println!("C374_NATIVE_PHYSICAL_AUTHOR_CENSUS owner=845759 header={} point={} tree={} daa={} bank53={} cap={} point_row_claims=528 local_owner_x_census=true global_x_row=false proof=false client=false",
                        physical_counts[0],physical_counts[1],physical_counts[2],
                        physical_counts[3],physical_counts[4],physical_counts[5]);
                    std::io::Write::flush(&mut std::io::stdout()).unwrap();
                    phase("physical_author_census_verified",started);

                    if c512h {
                        use crate::packed_owner_assembly::{HeaderSourceBinding,NativeRegularPhysicalAuthor,
                            NativeWorkEndpointAuthor};
                        use crate::header_daa_row_placement::C509RegularBatch;
                        let (regular,active,typed,selected,layout,term_counts)=c512h_retained.as_ref()
                            .expect("C512h retained actual regular writer and source reads");
                        let binding=regular.binding().expect("C512h same regular candidate binding").clone();
                        let root=plan.descriptor().root;let total=plan.work_profile().total_be28;
                        let cut=crate::bank53_map::CutDescriptor::eligible08().canonical_identity();
                        let previous_binding=HeaderSourceBinding::for_plan(&plan,845_759)
                            .expect("C512h same-parent PreviousR binding");
                        c512_require_shared_binding(&binding,&binding,&previous_binding,root,total,&cut)
                            .expect("C512h source/consumer distinct-owner common parent");
                        let previous_view=sink.complete_row_source_view_845759(&context)
                            .expect("C512h actual completed PreviousR source view");
                        assert_eq!(previous_view.binding(),&previous_binding);
                        physical_census.check_complete(&previous_binding,&packed)
                            .expect("C512h C374 source complete before PreviousR reads");
                        c512h_check_typed_score_sources(typed).expect("C512h no extra foreign typed Score record");
                        c512h_check_selected_score_reads(selected.iter()
                            .map(|read|(read.wire,read.author,read.value)),typed)
                            .expect("C512h exact selected PreviousR/Upper multiplicity and values");
                        let previous=c512_join_previous_r_reads(active,typed)
                            .expect("C512h exact450 typed PreviousR occurrences");
                        let previous_by_key=previous.iter().map(|read|
                            (c512h_occurrence_key(&read.operand),read)).collect::<BTreeMap<_,_>>();
                        let max_typed=c512h_typed_max_core(selected.iter()
                            .map(|read|(read.wire,read.author,read.value)),224)
                            .expect("C512h exact448 typed MAX reads including zeroes");
                        let max=producer.produce_scheduled_max_844798(&stream)
                            .expect("C512h actual scheduled MAX writer and1346claim token");
                        c512h_require_source_binding(&binding,max.binding(),844_798,root,total,&cut)
                            .expect("C512h actual MAX same-parent binding");
                        phase("c512h_scheduled_max_writer_retained",started);
                        let work885=producer.work_endpoint_author_lease(845_885)
                            .expect("C512h actual owner845885 Tree endpoint token");
                        phase("c512h_work845885_writer_retained",started);
                        let work886=producer.work_endpoint_author_lease(845_886)
                            .expect("C512h actual owner845886 Tree endpoint token");
                        phase("c512h_work845886_writer_retained",started);
                        for (owner,lease) in [(845_885,&work885),(845_886,&work886)] {
                            c512h_require_source_binding(&binding,lease.binding(),owner,root,total,&cut)
                                .expect("C512h actual Work token common parent");
                            let parent=producer.work_local_parent(owner).expect("C512h Work native parent");
                            c512d_require_work_parent(&binding,&binding,lease.binding(),&parent,owner,
                                root,total,&cut,plan.headers(),plan.slots()).expect("C512h Work exact parent/height");
                        }
                        let upper=producer.work_upper_publication(845_886,
                            work886.checked_local().expect("C512h same captured row Upper borrow"))
                            .expect("C512h actual captured-row Upper publication");
                        let upper_cells=upper.checked_upper(root,total,binding.profile(),&cut,845_886)
                            .expect("C512h exact same-parent Upper projection");
                        let work=c512d_join_work_reads(active,typed,
                            work885.checked_local().expect("C512h owner885 captured LOCAL").d(),
                            work886.checked_local().expect("C512h owner886 captured LOCAL").d(),upper_cells)
                            .expect("C512h Jmatcher exact896 Work occurrences");
                        c512d_require_no_foreign_work_open(active,work.len())
                            .expect("C512h entire foreign Work demand covered");
                        let work_by_key=work.iter().map(|read|(c512h_occurrence_key(&read.operand),read))
                            .collect::<BTreeMap<_,_>>();
                        let mut work_token_reads=[0usize;2];
                        let tags=c512h_join_physical_reads(active,|operand,family,source_context| {
                            match family {
                                0=>{
                                    let (author,value)=regular.checked_cell(operand.wire)?;
                                    let code=match author {NativeRegularPhysicalAuthor::Header=>0,
                                        NativeRegularPhysicalAuthor::Tree=>1,NativeRegularPhysicalAuthor::Daa=>2,
                                        NativeRegularPhysicalAuthor::Scored=>3};
                                    Ok((code,value))
                                },
                                1=>{
                                    let read=previous_by_key.get(&c512h_occurrence_key(operand))
                                        .ok_or("C512h missing exact PreviousR occurrence")?;
                                    if read.operand!=*operand {return Err("C512h detached PreviousR tuple".into());}
                                    let (author,value)=physical_census.checked_score_slack_cell(
                                        &previous_binding,&packed,&previous_view,source_context,operand.wire)?;
                                    c512_require_physical_score_read(read,source_context,operand.wire,author,value)?;
                                    Ok((4,value))
                                },
                                2=>{
                                    let (author,value)=max.checked_max_cell(operand.wire)?;
                                    Ok((5,c512h_require_max_read(source_context,operand.wire,&max_typed,author,value)?))
                                },
                                3|4|5=>{
                                    let read=work_by_key.get(&c512h_occurrence_key(operand))
                                        .ok_or("C512h missing exact Work occurrence")?;
                                    if read.operand!=*operand {return Err("C512h detached Work tuple".into());}
                                    let (token,endpoint)=if family==3 {(0,work885.checked_endpoint(operand.wire)?)}
                                        else {(1,work886.checked_endpoint(operand.wire)?)};
                                    let (author,value)=endpoint;
                                    if author!=NativeWorkEndpointAuthor::Tree || value!=read.value {
                                        return Err("C512h actual Work Tree claim author/value".into());
                                    }
                                    work_token_reads[token]+=1;Ok((6,value))
                                },
                                _=>Err("C512h unsupported physical family".into()),
                            }
                        }).expect("C512h every active occurrence has its actual physical source");
                        assert_eq!(tags.len(),active.len());assert_eq!(work_token_reads,[224,672]);
                        let mut zeroes=[0usize;6];
                        for tag in &tags {zeroes[tag.family as usize]+=usize::from(!tag.value);}
                        println!("C512H_PHYSICAL_READ_JOIN owner=845887 occurrences={} families={C512H_COUNTS:?} authored_zeroes={zeroes:?} work_token_reads={work_token_reads:?} active_capacity={} tag_capacity={} active_bytes={} tag_bytes={} same_candidate=true same_parent=true frame_parses=1 global_x=false gkr=false pcs=false proof=false client=false",
                            active.len(),active.capacity(),tags.capacity(),active.capacity()*std::mem::size_of_val(&active[0]),
                            tags.capacity()*std::mem::size_of::<C512hReadTag>());
                        phase("c512h_all_physical_reads_joined",started);
                        let row_source=regular.c509_regular_row_source().expect("C513 reborrow same opaque regular writer");
                        let batch=C509RegularBatch::checked_from_source(&row_source,&binding)
                            .expect("C513 same-candidate same-term C509 batch");
                        let numeric=batch.checked_numeric_row(active,tags.iter().map(|tag|tag.value))
                            .expect("C513 exact ordered physical reads produce zero ROW residuals");
                        assert_eq!(numeric.binding(),&binding);assert_eq!(numeric.layout_digest(),*layout);
                        assert_eq!(numeric.counts(),*term_counts);assert_eq!(numeric.terms(),520_693);
                        assert_eq!(numeric.active_reads(),730_942);assert_eq!(numeric.residuals().len(),C512_ROW_STRIDE);
                        assert!(numeric.residuals().iter().all(|value|value.is_zero()));
                        println!("C513_SELECTED_NUMERIC_ROW_PASS owner=845887 terms={} active_reads={} residual_rows={} residual_bytes={} nonzero=0 exact_order=true same_candidate=true physical_join=true global_x=false gkr=false pcs=false proof=false client=false production=false",
                            numeric.terms(),numeric.active_reads(),numeric.residuals().len(),
                            numeric.residuals().len()*std::mem::size_of::<Fr>());
                        std::io::Write::flush(&mut std::io::stdout()).unwrap();
                        phase("c513_selected_numeric_row_verified",started);
                        if c514 {
                            use ark_ff::{BigInteger,PrimeField};
                            use crate::header_daa_row_placement::C514Role1EdgeBatch;
                            use crate::sparse_stream_roster::c514_selected_u0_contribution;
                            let edges=C514Role1EdgeBatch::checked_from_batch(&batch)
                                .expect("C514 exact same retained C509 batch and typed sidecar");
                            assert_eq!(edges.binding(),&binding);
                            assert_eq!(edges.layout_digest(),*layout);
                            assert_eq!(edges.counts(),*term_counts);
                            assert_eq!(edges.edges().len(),edges.sidecar().len());
                            // Explicit non-Boolean diagnostic vector, not a public
                            // transcript challenge or a protocol proof claim.
                            let r=(2u64..42).map(Fr::from).collect::<Vec<_>>();
                            let source_bindings=[&binding,&previous_binding,max.binding(),
                                work885.binding(),work886.binding()];
                            let qualification_gap=std::cell::RefCell::new(None::<String>);
                            let result=c514_selected_u0_contribution(edges.edges(),&r,
                                20,21,19,0,&[19],
                                |demands|{
                                    let result=c514_qualify_native_demands(demands,source_bindings,
                                        root,total,&cut);
                                    if let Err(error)=&result {*qualification_gap.borrow_mut()=Some(error.clone());}
                                    result
                                },
                                |wire|match c514_source_family(wire)? {
                                    0=>Ok(regular.checked_cell(wire)?.1),
                                    1=>Ok(physical_census.checked_cell(
                                        &previous_binding,&packed,wire)?.1),
                                    2=>{
                                        let (author,value)=max.checked_max_cell(wire)?;
                                        let context=usize::from(wire%C512_WIRE_WIDTH>=1_000_097);
                                        if author!=MaxReplayAuthor::Scheduled(Writer::Max{
                                            context,end:844_800}) {
                                            return Err("C514 actual scheduled MAX author".into());
                                        }
                                        Ok(value)
                                    },
                                    family @ (3|4)=>{
                                        let (author,value)=if family==3 {work885.checked_endpoint(wire)?}
                                            else {work886.checked_endpoint(wire)?};
                                        if author!=NativeWorkEndpointAuthor::Tree {
                                            return Err("C514 actual Work Tree endpoint author".into());
                                        }
                                        Ok(value)
                                    },
                                    _=>Err("C514 unsupported physical capability".into()),
                                });
                            match result {
                                Err(error)=>{
                                    if qualification_gap.borrow().is_some() {
                                        println!("C514_SELECTED_U0_SOURCE_GAP owner=845887 error={error:?} arithmetic_started=false same_candidate=true same_parent=true frame_parses=1 full_role1=false global_x=false gkr=false pcs=false proof=false client=false production=false");
                                    } else {
                                        println!("C514_SELECTED_U0_FAIL owner=845887 error={error:?} arithmetic_status=not_claimed full_role1=false global_x=false gkr=false pcs=false proof=false client=false production=false");
                                    }
                                    std::io::Write::flush(&mut std::io::stdout()).unwrap();
                                    panic!("C514 selected U0 fail-closed: {error}");
                                },
                                Ok((polynomial,metrics))=>{
                                    // The numeric selected ROW is zero, hence its
                                    // eq(r,row)-weighted Boolean sum is exactly zero.
                                    // The polynomial itself need not be identically zero.
                                    assert!((polynomial[0]+polynomial[0]+polynomial[1]
                                        +polynomial[2]).is_zero(),
                                        "C514 p(0)+p(1) equals selected weighted ROW residual");
                                    let mut polynomial_bytes=Vec::with_capacity(96);
                                    for value in &polynomial {
                                        polynomial_bytes.extend(value.into_bigint().to_bytes_le());
                                    }
                                    let polynomial_sha256=hex(&role0_sha256(&polynomial_bytes)
                                        .expect("C514 polynomial digest"));
                                    let mut diagnostic_binding=b"C514-fixed-r40-2-through-41-v1".to_vec();
                                    diagnostic_binding.extend(root);diagnostic_binding.extend(total);
                                    diagnostic_binding.extend(binding.profile());diagnostic_binding.extend(&cut);
                                    diagnostic_binding.extend(binding.owner().to_le_bytes());
                                    diagnostic_binding.extend(edges.layout_digest());
                                    for value in &r {
                                        diagnostic_binding.extend(value.into_bigint().to_bytes_le());
                                    }
                                    let diagnostic_binding_sha256=hex(&role0_sha256(&diagnostic_binding)
                                        .expect("C514 source-bound diagnostic identity"));
                                    println!("C514_SELECTED_ROW_U0_PASS owner=845887 term_visits={} demands={} unique_coordinates={} loads={} duplicate_loads={} left_slots={} capacity_bytes={} polynomial_sha256={polynomial_sha256} diagnostic_binding_sha256={diagnostic_binding_sha256} r=fixed_2_through_41 boolean_sum_zero=true polynomial_zero_required=false same_candidate=true same_parent=true frame_parses=1 full_role1=false global_x=false gkr=false pcs=false proof=false client=false production=false",
                                        metrics.term_visits,metrics.demands,metrics.unique_coordinates,
                                        metrics.loads,metrics.duplicate_loads,metrics.left_slots,metrics.capacity_bytes);
                                    std::io::Write::flush(&mut std::io::stdout()).unwrap();
                                    phase("c514_selected_row_u0_verified",started);
                                },
                            }
                        }
                        return;
                    }

                    if c512_previous_r_physical_join {
                        use crate::header_daa_row_placement::C509RegularBatch;
                        use crate::packed_owner_assembly::HeaderSourceBinding;
                        let (consumer_candidate,retained_active,typed_score_reads)=
                            c512_c509_retained.as_ref()
                                .expect("C512b retained exact owner845887 candidate and reads");
                        let consumer_row_source=consumer_candidate.c509_regular_row_source()
                            .expect("C512b C509 source from retained consumer candidate");
                        let candidate_binding=consumer_candidate.binding()
                            .expect("C512b retained owner845887 candidate binding").clone();
                        let c509_batch=C509RegularBatch::checked_from_source(
                            &consumer_row_source,&candidate_binding)
                            .expect("C512b checked C509 batch remains tied to exact candidate");
                        let active=c509_batch.active_operands()
                            .expect("C512b retained C509 active operands")
                            .collect::<Vec<_>>();
                        assert_eq!(active.as_slice(),retained_active.as_slice(),
                            "C512b retained checked C509 candidate identity");
                        let c509_binding=c509_batch.source_binding()
                            .expect("C512b consumer source binding").clone();
                        let physical_binding=HeaderSourceBinding::for_plan(&plan,C512_PREVIOUS_OWNER)
                            .expect("C512b owner845759 physical source binding from same plan");
                        let cut=crate::bank53_map::CutDescriptor::eligible08()
                            .canonical_identity();
                        c512_require_shared_binding(&candidate_binding,&c509_binding,
                            &physical_binding,plan.descriptor().root,
                            plan.work_profile().total_be28,&cut)
                            .expect("C512b exact common parent tuple, distinct owners, fixed layout");
                        let joined=c512_join_previous_r_reads(&active,typed_score_reads)
                            .expect("C512b exact 450 C509 PreviousR/typed Score-read join");
                        assert_eq!(joined.len(),450);
                        let view=sink.complete_row_source_view_845759(&context)
                            .expect("C512b completed same-sink owner845759 typed Score view");
                        assert_eq!(view.binding(),&physical_binding,
                            "C512b physical view exact source binding");
                        physical_census.check_complete(&physical_binding,&packed)
                            .expect("C512b complete physical author census before PreviousR reads");
                        let mut per_context=[0usize;2];
                        let mut authored_zeroes=0usize;
                        for read in &joined {
                            let (author,value)=physical_census.checked_score_slack_cell(
                                &physical_binding,&packed,&view,read.context,read.operand.wire)
                                .expect("C512b physical checked Score-R cell");
                            c512_require_physical_score_read(read,read.context,
                                read.operand.wire,author,value)
                                .expect("C512b exact owner845759 Score-R author/value");
                            per_context[read.context]+=1;
                            authored_zeroes+=usize::from(!value);
                        }
                        assert_eq!(per_context,[225,225]);
                        println!("C512B_PREVIOUS_R_PHYSICAL_JOIN owner=845759 consumer=845887 occurrences={} per_context={per_context:?} authored_zeroes={authored_zeroes} physical_author=ScoreReplay origin=845760 previous_owner=845758 max_owner=844670 cap_owner=845759 common_parent_binding=true distinct_owner_bindings=true census_complete=true global_x=false c513_row_gkr=false proof=false client=false production=false",
                            joined.len());
                        std::io::Write::flush(&mut std::io::stdout()).unwrap();
                        phase("c512b_previous_r_physical_join_verified",started);

                        if c512d_work_physical_join {
                            let root = plan.descriptor().root;
                            let total = plan.work_profile().total_be28;
                            let profile = candidate_binding.profile();
                            let headers = plan.headers();
                            let slots = plan.slots();
                            let work885 = producer.work_endpoint_author_lease(C512D_WORK_D_OWNERS[0])
                                .expect("C512j actual owner845885 same-row Tree claim token");
                            let work886 = producer.work_endpoint_author_lease(C512D_WORK_D_OWNERS[1])
                                .expect("C512j actual owner845886 same-row Tree claim token");
                            for (owner, author_lease) in [
                                (C512D_WORK_D_OWNERS[0], &work885),
                                (C512D_WORK_D_OWNERS[1], &work886),
                            ] {
                                assert_eq!(author_lease.check_complete()
                                    .expect("C512j complete same-producer same-row Tree claim census"),448);
                                let source_binding = author_lease.binding();
                                let parent = producer.work_local_parent(owner)
                                    .expect("C512j actual Work claim source same native parent");
                                c512d_require_work_parent(&candidate_binding, &c509_binding,
                                    source_binding, &parent, owner, root, total, &cut,
                                    headers, slots)
                                    .expect("C512j token/consumer common parent and distinct owners");
                            }
                            let upper = producer.work_upper_publication(
                                C512D_WORK_UPPER_OWNER, work886.checked_local()
                                    .expect("C512j Upper borrows the exact captured Work LOCAL row"))
                                .expect("C512j actual owner845886 captured-row WorkUpper publication");
                            let upper_cells = upper.checked_upper(root, total, profile,
                                &cut, C512D_WORK_UPPER_OWNER)
                                .expect("C512j same-parent captured-row WorkUpper cells");
                            let joined_work = c512d_join_work_reads(&active, typed_score_reads,
                                work885.checked_local().expect("C512j checked owner845885 LOCAL row").d(),
                                work886.checked_local().expect("C512j checked owner845886 LOCAL row").d(),
                                upper_cells)
                                .expect("C512j exact 896 C509 Work occurrence projections");
                            let mut token_reads=[0usize;2];
                            let per_family=c512d_require_work_tree_claims(&joined_work,|wire| {
                                use crate::packed_owner_assembly::{
                                    NativePhysicalAuthor,NativeWorkEndpointAuthor,
                                };
                                let (source,endpoint)=match wire/C512_WIRE_WIDTH {
                                    845_885=>(0,work885.checked_endpoint(wire)?),
                                    845_886=>(1,work886.checked_endpoint(wire)?),
                                    _=>return Err("C512j actual Work claim token owner".into()),
                                };
                                token_reads[source]+=1;
                                let (author,value)=endpoint;
                                let author=match author {
                                    NativeWorkEndpointAuthor::Tree=>NativePhysicalAuthor::Tree,
                                };
                                Ok((author,Fr::from(value as u64)))
                            }).expect("C512j every Work occurrence consults its actual Tree claim token");
                            assert_eq!(token_reads,[224,672],
                                "owner845886 Upper claim is checked once per Score context");
                            c512d_require_no_foreign_work_open(&active,joined_work.len())
                                .expect("C512j all foreign Work-D/Upper demands joined to Tree claims");
                            assert_eq!(per_family, [224;4]);
                            let authored_zeroes = joined_work.iter().filter(|read| !read.value).count();
                            println!("C512J_WORK_TREE_CLAIM_JOIN consumer=845887 sources=[845885,845886] occurrences={} per_family={per_family:?} authored_zeroes={authored_zeroes} physical_author=Tree tree_claim_events=[448,448] token_reads={token_reads:?} work_local_rows=2 work_upper_publications=1 same_captured_rows=true common_parent_binding=true distinct_owner_bindings=true source_packed_match=true foreign_work_d_upper_open=0 global_x=false c513_row_gkr=false proof=false client=false production=false",
                                joined_work.len());
                            std::io::Write::flush(&mut std::io::stdout()).unwrap();
                            phase("c512j_work_tree_claim_join_verified", started);
                        }
                    }

                    if c453 {
                        let view=sink.map_source_view_845759(&context)
                            .expect("retained completed Map source view from same sink");
                        let paired=row_plan.stage_owner_with_retained_map_general(845_759,&view)
                            .expect("coactive v4 ROW from retained Map terms");
                        let mut registry=row_plan.registry_with_map_pair_general(845_759)
                            .expect("coactive v4 ROW registry");
                        let before=registry.clone();
                        let evidence=registry.commit_coactive_map_pair(
                            &paired,&c370,&physical_census,&view)
                            .expect("complete coactive Map/ordinary source and residual admission");
                        assert_ne!(registry,before,"C453 single atomic ROW commit");
                        let committed=registry.clone();
                        assert!(registry.commit_coactive_map_pair(
                            &paired,&c370,&physical_census,&view).is_err(),
                            "C453 duplicate commit rejection");
                        assert_eq!(registry,committed,"C453 duplicate leaves committed ROW unchanged");
                        assert_eq!(evidence.map_source_cells,[5_757;2]);
                        assert_eq!(evidence.work_d_source_cells,[224;2]);
                        assert_eq!(evidence.physical_authors,physical_counts);
                        assert_eq!(evidence.residual_rows,1<<19);
                        assert_eq!(evidence.physical_authors[4],16_384);
                        assert_eq!(11_514+4_096+774,16_384);
                        assert!(sink.pending_sources().is_empty());
                        assert_eq!(sink.pending_cap_max_read_count(),0);
                        println!("C453_COACTIVE_MAP_ROW_AUTHENTIC_PASS owner=845759 class=Carry source_binding={:?} map0_binding={:?} map1_binding={:?} row_layout_v4={:?} physical_authors={:?} typed_bank53_map=11514 typed_bank53_score=4096 typed_bank53_slack=774 typed_bank53_header_zero=0 map_source_cells={:?} work_d_source_cells={:?} terms={} active_reads={} map_helper_reads={} work_d_reads={} residual_rows={} nonzero=0 open=0 pending=0 source_packed_match=true row_commits=1 duplicate_commit_rejected=true scope=selected_owner_coactive_map_row_reader score_slack_placement=false all_owner=false pcs=false proof=false client=false",
                            view.binding(),view.map_binding(0).unwrap(),view.map_binding(1).unwrap(),
                            paired.layout_digest(),
                            evidence.physical_authors,evidence.map_source_cells,
                            evidence.work_d_source_cells,evidence.terms,evidence.active_reads,
                            evidence.map_helper_reads,evidence.work_d_reads,evidence.residual_rows);
                        std::io::Write::flush(&mut std::io::stdout()).unwrap();
                        phase("c453_coactive_map_row_verified",started);
                    }

                    if c455 {
                        use crate::header_daa_row_placement::CompleteBatch;
                        sink.c455_retained_upper_fault_rejects_complete_view_for_test(&context)
                            .expect("C455 completed mint rejects one retained Upper source fault and restores custody");
                        let view=sink.complete_row_source_view_845759(&context)
                            .expect("completed same-sink modern Score/Slack source view");
                        let map_view=view.map_view();
                        let paired=row_plan.stage_owner_with_retained_map_general(845_759,&map_view)
                            .expect("C455 exact retained ordinary and Map prefix");
                        let complete=CompleteBatch::checked_from_retained_map(&paired,&view)
                            .expect("C455 fifteen-relation ordered source batch");
                        let mut registry=row_plan.registry_with_complete(845_759)
                            .expect("C455 separate fifteen-relation ROW registry");
                        let before=registry.clone();
                        let evidence=registry.commit_complete_coactive(
                            &complete,&c370,&physical_census,&view)
                            .expect("C455 source-qualified complete selected-owner ROW reader");
                        assert_ne!(registry,before,"C455 single atomic ROW commit");
                        let committed=registry.clone();
                        assert!(registry.commit_complete_coactive(
                            &complete,&c370,&physical_census,&view).is_err(),
                            "C455 duplicate complete ROW commit must fail");
                        assert_eq!(registry,committed,"C455 duplicate leaves committed ROW unchanged");
                        assert_eq!(evidence.residual_rows,1<<19);
                        assert_eq!(evidence.physical_authors,physical_counts);
                        assert_eq!(evidence.map_source_cells,[5_757;2]);
                        assert_eq!(evidence.work_d_source_cells,[224;2]);
                        assert_eq!(evidence.score_source_cells,[2_048;2]);
                        assert_eq!(evidence.slack_source_cells,[387;2]);
                        assert_eq!(evidence.typed_bank53_authors,
                            [5_757,5_757,2_048,2_048,387,387]);
                        assert_eq!(evidence.import_records_by_kind,[450,130,448]);
                        assert_eq!(evidence.foreign_occurrences_by_kind,[450,448]);
                        assert_eq!(evidence.local_cap_occurrences,130);
                        assert_eq!(evidence.checked_ranges,[
                            (409600,419947,477074,487421),
                            (442368,452715,492305,502652),
                            (487421,491918,487421,491918),
                            (502652,507149,502652,507149),
                            (438496,438883,491918,492305),
                            (471264,471651,507149,507536),
                        ]);
                        assert_eq!((evidence.open_reads,evidence.pending_reads),(0,0));
                        assert!(sink.pending_sources().is_empty());
                        assert_eq!(sink.pending_cap_max_read_count(),0);
                        println!("C455_MODERN_SCORE_SLACK_ROW_AUTHENTIC_PASS owner=845759 class=Carry source_binding={:?} row_layout_v5={:?} relation_counts={:?} checked_ranges={:?} physical_authors={:?} typed_bank53_authors={:?} map_source_cells={:?} work_d_source_cells={:?} score_source_cells={:?} slack_source_cells={:?} import_records_by_kind={:?} foreign_occurrences_by_kind={:?} local_cap_occurrences={} terms={} active_reads={} residual_rows={} nonzero=0 open=0 pending=0 retained_upper_fault_rejected=true source_packed_match=true row_commits=1 duplicate_commit_rejected=true source_owner_physical_row_admission=false all_owner=false pcs=false proof=false verifier=false client=false scope=selected_owner_modern_score_slack_row_reader",
                            view.binding(),complete.layout_digest(),complete.counts(),
                            evidence.checked_ranges,
                            evidence.physical_authors,evidence.typed_bank53_authors,
                            evidence.map_source_cells,evidence.work_d_source_cells,
                            evidence.score_source_cells,evidence.slack_source_cells,
                            evidence.import_records_by_kind,evidence.foreign_occurrences_by_kind,
                            evidence.local_cap_occurrences,evidence.terms,evidence.active_reads,
                            evidence.residual_rows);
                        std::io::Write::flush(&mut std::io::stdout()).unwrap();
                        phase("c455_modern_score_slack_row_verified",started);
                    }

                    if dense_residual {
                        use crate::header_daa_row_placement::{ActiveOperand,OperandSide};
                        const RESIDUAL_ROWS:usize=1<<19;
                        const RESIDUAL_OWNER:usize=845_759;
                        let batch=c370.batch();
                        let mut active=batch.active_operands();
                        let mut reads=c370.reads();
                        let base=RESIDUAL_OWNER.checked_mul(RESIDUAL_ROWS)
                            .expect("C430 owner row base");
                        let mut residuals=vec![Fr::zero();RESIDUAL_ROWS];
                        let mut active_count=0usize;
                        let mut term_count=0usize;
                        let mut read_value=|expected:ActiveOperand| -> Fr {
                            let indexed=active.next().expect("C430 missing active operand");
                            assert_eq!(indexed,expected,
                                "C430 canonical ActiveOperand occurrence/relation/row/side/wire/flags");
                            let read=*reads.next().expect("C430 missing typed source read");
                            let (operand,value)=match read {
                                NativeRead::Header{operand,value}
                                |NativeRead::Daa{operand,value}
                                |NativeRead::PointMembership{operand,value}
                                |NativeRead::Cap0{operand,value,..}
                                |NativeRead::Cap1{operand,value,..} => (operand,value),
                                NativeRead::ForeignMax{operand,cell} => {
                                    assert_eq!(cell.wire,operand.wire,
                                        "C430 foreign MAX wire/source identity");
                                    (operand,cell.value)
                                }
                                NativeRead::ForeignDaaLane2{operand,wire,value,..} => {
                                    assert_eq!(wire,operand.wire,
                                        "C430 foreign DAA wire/source identity");
                                    (operand,value)
                                }
                                NativeRead::Unresolved{operand,reason} => panic!(
                                    "C430 unresolved typed source at occurrence={} relation={:?} row={} side={:?} wire={} reason={:?}",
                                    operand.occurrence,operand.relation,operand.row,
                                    operand.side,operand.wire,reason),
                            };
                            assert_eq!(operand,expected,
                                "C430 typed read occurrence/relation/row/side/wire/flags");
                            active_count+=1;
                            Fr::from(value as u64)
                        };
                        for (occurrence,(relation,term)) in batch.terms().enumerate() {
                            let q=term.row.checked_sub(base).filter(|q|*q<RESIDUAL_ROWS)
                                .expect("C430 term outside owner 845759 dense ROW window");
                            let gate=&term.gate;
                            let c1_active=!gate.c1.is_zero();
                            let c2_active=!gate.c2.is_zero();
                            let c3_active=!gate.c3.is_zero();
                            let left=if c1_active||c3_active {
                                read_value(ActiveOperand{occurrence,relation,row:term.row,
                                    side:OperandSide::Left,wire:gate.left,c1_active,
                                    c2_active:false,c3_active})
                            }else{Fr::zero()};
                            let right=if c2_active||c3_active {
                                read_value(ActiveOperand{occurrence,relation,row:term.row,
                                    side:OperandSide::Right,wire:gate.right,c1_active:false,
                                    c2_active,c3_active})
                            }else{Fr::zero()};
                            residuals[q]+=gate.c0+gate.c1*left+gate.c2*right
                                +gate.c3*left*right;
                            term_count+=1;
                        }
                        drop(read_value);
                        assert!(active.next().is_none(),"C430 trailing active operand");
                        assert!(reads.next().is_none(),"C430 trailing typed source read");
                        let mut nonzero=0usize;
                        let mut first_nonzero=None;
                        for (q,value) in residuals.iter().enumerate() {
                            if !value.is_zero() {
                                nonzero+=1;
                                first_nonzero.get_or_insert(q);
                            }
                        }
                        let divergence=first_nonzero.map(|q|{
                            let global_row=base.checked_add(q).expect("C430 global residual row");
                            let mut first_occurrence=None;
                            let mut last_occurrence=None;
                            for (ordinal,(relation,term)) in batch.terms().enumerate() {
                                if term.row==global_row {
                                    let occurrence=(ordinal,relation);
                                    first_occurrence.get_or_insert(occurrence);
                                    last_occurrence=Some(occurrence);
                                }
                            }
                            format!("global_row={global_row} first_batch_occurrence={first_occurrence:?} last_batch_occurrence={last_occurrence:?}")
                        }).unwrap_or_else(||"none".to_string());
                        println!("C430_AUTHENTIC_CARRY_DENSE_RESIDUAL_DIAGNOSTIC owner={RESIDUAL_OWNER} terms={term_count} active={active_count} residual_rows={RESIDUAL_ROWS} nonzero={nonzero} first_local_q={first_nonzero:?} first_divergence={divergence} occurrence_scope=batch_ROW_occurrence_not_causal_attribution source_reads_ordered=true unresolved_rejected=true physical_author_census=true global_x=false proof=false client=false");
                        assert_eq!(nonzero,0,
                            "C430 nonzero dense residual rows; first local q {first_nonzero:?}");
                        println!("C430_AUTHENTIC_CARRY_DENSE_RESIDUAL_PASS owner={RESIDUAL_OWNER} nonzero=0 proof=false client=false");
                        if first_u {
                            use crate::header_daa_row_placement::{NativeRead,OperandSide};
                            use crate::h21_scheduled_max_cap::{MaxReplayAuthor,Writer};
                            use ark_ff::{Field,One};
                            const C431_OWNER:usize=845_759;
                            const C431_ROWS:usize=1<<19;
                            const C431_OWNER_BASE:usize=C431_OWNER*C431_ROWS;
                            let mut transcript=crate::transcript::Transcript::new(
                                b"nipopow-c431-h21-owner845759-first-u-diagnostic-v1");
                            let decode32=|text:&str| -> [u8;32] {
                                assert_eq!(text.len(),64);
                                let mut bytes=[0u8;32];
                                for i in 0..32 {
                                    bytes[i]=u8::from_str_radix(&text[2*i..2*i+2],16)
                                        .expect("fixed C431 digest hex");
                                }
                                bytes
                            };
                            transcript.append_bytes(b"c431-frame-sha256",
                                &decode32(FRAME_SHA256));
                            transcript.append_bytes(b"c431-c430-receipt-sha256",
                                &decode32("618386c36855b629c8913bc32bf7d7bcc744dc4e70d3b5dec3ac4efc09f2de78"));
                            transcript.append_bytes(b"c431-owner-u64le",&845_759u64.to_le_bytes());
                            transcript.append_bytes(b"c431-rows-u64le",&524_288u64.to_le_bytes());
                            transcript.append_bytes(b"c431-terms-u64le",&487_671u64.to_le_bytes());
                            transcript.append_bytes(b"c431-reads-u64le",&690_914u64.to_le_bytes());
                            let r=crate::gkr::output_point(C431_ROWS,&mut transcript);
                            assert_eq!(r.len(),19);
                            let eq_row=|q:usize| -> Fr {
                                r.iter().enumerate().fold(Fr::one(),|acc,(bit,coordinate)|
                                    acc*if (q>>bit)&1==1 {*coordinate} else {Fr::one()-coordinate})
                            };

                            // C374 has already checked every physical author in
                            // this complete local row. Keep its packed bits local;
                            // foreign values below retain their source tags.
                            let mut max_values=BTreeMap::<usize,bool>::new();
                            let max_cells=stream.closed_owner_cells(844_670)
                                .expect("closed native MAX source owner 844670");
                            let valid_max_tag=|wire:usize,context:usize,end:usize,
                                author:MaxReplayAuthor| {
                                let local=wire%OWNER_ROW_BITS;
                                author==MaxReplayAuthor::Scheduled(Writer::Max{context,end})
                                    && wire/OWNER_ROW_BITS==844_670 && context<2
                                    && end==844_672
                                    && ([999_424usize,1_000_097][context]..
                                        [999_424usize,1_000_097][context]+673).contains(&local)
                            };
                            let mut max_count=0usize;
                            for (wire,author,value) in max_cells {
                                if let MaxReplayAuthor::Scheduled(Writer::Max{context,end})=author {
                                    assert!(valid_max_tag(wire,context,end,author),
                                        "C431 MAX author/context/owner tag");
                                    assert!(value==Fr::zero()||value==Fr::one());
                                    assert!(max_values.insert(wire,value.is_one()).is_none(),
                                        "C431 duplicate scheduled MAX source wire");
                                    max_count+=1;
                                }
                            }
                            assert_eq!(max_count,1_346);
                            assert!(!valid_max_tag(844_670*OWNER_ROW_BITS+999_424,1,844_672,
                                MaxReplayAuthor::Scheduled(Writer::Max{context:0,end:844_672})),
                                "C431 isolated wrong MAX context mutant");
                            assert!(!valid_max_tag(844_671*OWNER_ROW_BITS+999_424,0,844_672,
                                MaxReplayAuthor::Scheduled(Writer::Max{context:0,end:844_672})),
                                "C431 isolated wrong MAX owner mutant");
                            let mut work_values=BTreeMap::<usize,bool>::new();
                            for (&wire,&value) in &expected_work {
                                assert!(matches!(wire/OWNER_ROW_BITS,845_757|845_758));
                                assert!(work_values.insert(wire,value).is_none());
                            }
                            assert_eq!(work_values.len(),448);

                            let mut c432_boundary=BTreeMap::<usize,(crate::packed_owner_assembly::NativePhysicalAuthor,bool)>::new();
                            let mut c434_tree_tail=BTreeMap::<usize,(crate::packed_owner_assembly::NativePhysicalAuthor,bool)>::new();
                            if second_u {
                                let expected_boundary=[
                                    (845_757usize,987_672usize,crate::packed_owner_assembly::NativePhysicalAuthor::Tree),
                                    (845_757,987_673,crate::packed_owner_assembly::NativePhysicalAuthor::Tree),
                                    (845_757,987_898,crate::packed_owner_assembly::NativePhysicalAuthor::Tree),
                                    (845_757,987_899,crate::packed_owner_assembly::NativePhysicalAuthor::Tree),
                                    (845_758,987_672,crate::packed_owner_assembly::NativePhysicalAuthor::Tree),
                                    (845_758,987_673,crate::packed_owner_assembly::NativePhysicalAuthor::Tree),
                                    (845_758,987_898,crate::packed_owner_assembly::NativePhysicalAuthor::Tree),
                                    (845_758,987_899,crate::packed_owner_assembly::NativePhysicalAuthor::Tree),
                                ];
                                for source_owner in [845_757usize,845_758] {
                                    let lease=producer.native_work_local_lease_for_owner(source_owner)
                                        .expect("C432 same-parent native WorkLocal lease");
                                    producer.require_native_work_local_lease_for_owner(&native_parent,
                                        source_owner,&lease).expect("C432 exact WorkLocal parent/owner");
                                    assert_eq!(lease.local().operands().len(),1_184);
                                    let mut observed_work=Vec::with_capacity(224);
                                    for local in 987_674usize..987_898 {
                                        let wire=source_owner*OWNER_ROW_BITS+local;
                                        let raw_value=lease.local().operands().iter()
                                            .find(|(candidate,_)|*candidate==wire)
                                            .expect("C432 complete WorkLocal D overlap").1;
                                        assert!(raw_value==Fr::zero()||raw_value==Fr::one(),
                                            "C432 WorkLocal D overlap is Boolean");
                                        observed_work.push((wire,raw_value==Fr::one()));
                                    }
                                    let expected_work_slice=expected_work.range(
                                        source_owner*OWNER_ROW_BITS+987_674..
                                        source_owner*OWNER_ROW_BITS+987_898)
                                        .map(|(&wire,&value)|(wire,value)).collect::<Vec<_>>();
                                    assert!(c432_work_d_overlap_matches(&expected_work_slice,&observed_work),
                                        "C432 exact 224-cell Work-D overlap including zeros");
                                    let mut wrong_work=observed_work.clone();
                                    wrong_work[0].1=!wrong_work[0].1;
                                    assert!(!c432_work_d_overlap_matches(&expected_work_slice,&wrong_work),
                                        "C432 isolated Work-D overlap value mismatch");
                                    let boundary=producer.c432_worklocal_boundary_authors(
                                        &native_parent,source_owner,&lease,None)
                                        .expect("C433 Tree-author-qualified boundary");
                                    for (wire,author,value) in boundary {
                                        assert!(c432_boundary.insert(wire,(author,value)).is_none(),
                                            "C432 duplicated physical boundary wire");
                                    }
                                    if third_u {
                                        let octet=producer.c434_exponent_tree_octet_authority(
                                            &native_parent,source_owner,&lease,None)
                                            .expect("C434 same-parent Tree-author-qualified octet tail");
                                        for (wire,author,value) in octet {
                                            assert!(c434_tree_tail.insert(wire,(author,value)).is_none(),
                                                "C434 duplicated physical Tree tail wire");
                                        }
                                        if source_owner==845_757 {
                                            producer.c434_exponent_tree_octet_faults_rejected(
                                                &native_parent,source_owner,&lease)
                                                .expect("C434 Tree author/binding/omission/mask/value faults rejected");
                                        }
                                    }
                                    if source_owner==845_757 {
                                        producer.c432_boundary_authority_faults_rejected(
                                            &native_parent,source_owner,&lease)
                                            .expect("C432 isolated author/binding/mask/value faults rejected");
                                        let wrong_owner=producer.c432_worklocal_boundary_authors(
                                            &native_parent,845_758,&lease,None);
                                        assert!(wrong_owner.is_err(),"C432 wrong owner rejected before source read");
                                        let wrong_parent=native_parent.different_cut_for_test();
                                        assert!(producer.require_native_work_local_lease_for_owner(
                                            &wrong_parent,source_owner,&lease).is_err(),
                                            "C432 wrong parent/cut rejected before source read");
                                    }
                                }
                                assert_eq!(c432_boundary.len(),8);
                                for (owner,local,author) in expected_boundary {
                                    let wire=owner*OWNER_ROW_BITS+local;
                                    assert_eq!(c432_boundary.get(&wire).map(|entry|entry.0),Some(author),
                                        "C432 exact physical source author");
                                    let value=c432_boundary[&wire].1;
                                    assert!(work_values.insert(wire,value).is_none(),
                                        "C432 boundary conflicts with DAA Work-D map");
                                }
                                let expected_order=expected_boundary.map(|(owner,local,author)|
                                    (owner*OWNER_ROW_BITS+local,author,c432_boundary[
                                        &(owner*OWNER_ROW_BITS+local)].1));
                                let observed_order=c432_boundary.iter().map(|(&wire,&(author,value))|
                                    (wire,author,value)).collect::<Vec<_>>();
                                assert!(c432_ordered_boundary_matches(&expected_order,&observed_order),
                                    "C432 ordered boundary source coverage baseline");
                                let mut omitted=observed_order.clone();omitted.remove(0);
                                assert!(!c432_ordered_boundary_matches(&expected_order,&omitted),
                                    "C432 omitted boundary rejected before numeric evaluation");
                                let mut duplicated=observed_order.clone();
                                let duplicate=duplicated[0];duplicated.insert(0,duplicate);
                                assert!(!c432_ordered_boundary_matches(&expected_order,&duplicated),
                                    "C432 duplicated boundary rejected before numeric evaluation");
                                println!("C433_WORKLOCAL_TREE_AUTHOR_BOUNDARY_PASS owners=2 work_d_overlap=448 boundary=8 tree_author=8 header_absent=true wrong_tree_author_binding_omission_header_mask_value_rejected=true proof=false client=false");
                                if third_u {
                                    assert_eq!(c434_tree_tail.len(),8);
                                    for owner in [845_757usize,845_758] {
                                        for local in 987_900usize..987_904 {
                                            let wire=owner*OWNER_ROW_BITS+local;
                                            let (author,value)=c434_tree_tail[&wire];
                                            assert_eq!(author,crate::packed_owner_assembly::NativePhysicalAuthor::Tree,
                                                "C434 physical Tree author for p2 octet");
                                            assert!(work_values.insert(wire,value).is_none(),
                                                "C434 Tree tail conflicts with Work-D or C433 boundary");
                                        }
                                    }
                                    println!("C434_WORKLOCAL_TREE_OCTET_PASS owners=2 new_tree=8 header_absent=true isolated_faults_rejected=true proof=false client=false");
                                }
                            }

                            // Match every typed C370 occurrence before using its
                            // value. No descriptor- or row-derived author guesses.
                            let batch=c370.batch();
                            assert!(c431_ordered_terms_match(batch.terms().enumerate(),
                                batch.terms().enumerate()),"C431 source ordinal/relation/term baseline");
                            assert!(!c431_ordered_terms_match(batch.terms().enumerate(),
                                batch.terms().enumerate().skip(1)),
                                "C431 isolated skipped source occurrence must fail before aggregation");
                            let duplicated=batch.terms().enumerate().take(1)
                                .chain(batch.terms().enumerate());
                            assert!(!c431_ordered_terms_match(batch.terms().enumerate(),duplicated),
                                "C431 isolated duplicate source occurrence must fail before aggregation");
                            println!("C431_SOURCE_ORDINAL_COVERAGE_PASS terms=487671 ordered=true skipped_rejected=true duplicated_rejected=true before_numeric=true");
                            let mut active=batch.active_operands();
                            let mut typed_values=BTreeMap::<usize,bool>::new();
                            let mut typed_count=0usize;
                            for read in c370.reads() {
                                let (operand,value)=match *read {
                                    NativeRead::Header{operand,value}
                                    |NativeRead::Daa{operand,value}
                                    |NativeRead::PointMembership{operand,value}
                                    |NativeRead::Cap0{operand,value,..}
                                    |NativeRead::Cap1{operand,value,..}=>(operand,value),
                                    NativeRead::ForeignMax{operand,cell}=>{
                                        assert_eq!(cell.wire,operand.wire);
                                        assert!(cell.context<2);
                                        assert!(( [999_424usize,1_000_097][cell.context]..
                                            [999_424usize,1_000_097][cell.context]+673)
                                            .contains(&(cell.wire%OWNER_ROW_BITS)));
                                        assert_eq!(cell.author,MaxReplayAuthor::Scheduled(
                                            Writer::Max{context:cell.context,end:cell.end}));
                                        assert_eq!(cell.end,844_672);
                                        assert_eq!(max_values.get(&cell.wire),Some(&cell.value));
                                        (operand,cell.value)
                                    }
                                    NativeRead::ForeignDaaLane2{operand,source_owner,wire,value}=>{
                                        assert_eq!(wire,operand.wire);
                                        assert!(matches!(source_owner,845_757|845_758));
                                        assert_eq!(wire/OWNER_ROW_BITS,source_owner);
                                        assert_eq!(work_values.get(&wire),Some(&value));
                                        (operand,value)
                                    }
                                    NativeRead::Unresolved{operand,reason}=>panic!(
                                        "C431 unresolved source occurrence={} relation={:?} wire={} reason={:?}",
                                        operand.occurrence,operand.relation,operand.wire,reason),
                                };
                                let expected=active.next().expect("C431 missing active operand");
                                assert_eq!(operand,expected,"C431 typed occurrence/source order");
                                if !matches!(*read,NativeRead::ForeignMax{..}|NativeRead::ForeignDaaLane2{..}) {
                                    assert_eq!(operand.wire/OWNER_ROW_BITS,C431_OWNER,
                                        "C431 local source must remain owner-qualified");
                                    let local=operand.wire%OWNER_ROW_BITS;
                                    let packed_value=(packed.packed_bytes()[local/8]>>(local%8))&1!=0;
                                    assert_eq!(value,packed_value,"C431 typed local/packed agreement");
                                }
                                if let Some(previous)=typed_values.insert(operand.wire,value) {
                                    assert_eq!(previous,value,"C431 conflicting typed source value");
                                }
                                typed_count+=1;
                            }
                            assert!(active.next().is_none(),"C431 trailing active operand");
                            assert_eq!(typed_count,690_914);

                            let x_value=|wire:usize| -> bool {
                                let owner=wire/OWNER_ROW_BITS;
                                let local=wire%OWNER_ROW_BITS;
                                match owner {
                                    C431_OWNER=>{
                                        let value=(packed.packed_bytes()[local/8]>>(local%8))&1!=0;
                                        if let Some(typed)=typed_values.get(&wire) {
                                            assert_eq!(*typed,value,"C431 local source/packed conflict");
                                        }
                                        value
                                    }
                                    844_670=>*max_values.get(&wire)
                                        .expect("C431 missing scheduled MAX sibling/source"),
                                    845_757|845_758=>*work_values.get(&wire)
                                        .expect("C431 missing checked Work-D sibling/source"),
                                    _=>panic!("C431 wire outside qualified source owners: {owner}"),
                                }
                            };

                            if second_u {
                                let mut actual_boundary=BTreeSet::<usize>::new();
                                for (ordinal,(relation,term)) in batch.terms().enumerate() {
                                    let gate=&term.gate;
                                    if gate.c1.is_zero()&&gate.c3.is_zero(){continue;}
                                    let block=gate.left&!3usize;
                                    for offset in 0..4 {
                                        let wire=block+offset;
                                        let source_owner=wire/OWNER_ROW_BITS;
                                        let local=wire%OWNER_ROW_BITS;
                                        let source_value=match source_owner {
                                            C431_OWNER=>Some((packed.packed_bytes()[local/8] >> (local%8)) & 1 != 0),
                                            844_670=>max_values.get(&wire).copied(),
                                            845_757|845_758=>work_values.get(&wire).copied(),
                                            _=>None,
                                        };
                                        assert!(source_value.is_some(),
                                            "C432 first unqualified source relation={relation:?} ordinal={ordinal} block={block} missing_wire={wire} owner={source_owner}");
                                        if matches!(source_owner,845_757|845_758)
                                            && !(987_674..987_898).contains(&local) {
                                            actual_boundary.insert(wire);
                                        }
                                    }
                                }
                                let expected_boundary_wires=c432_boundary.keys().copied()
                                    .collect::<BTreeSet<_>>();
                                assert_eq!(actual_boundary,expected_boundary_wires,
                                    "C432 exact source-origin boundary set before p1 numeric evaluation");
                            }
                            if third_u {
                                let mut actual_work_boundary=BTreeSet::<usize>::new();
                                let mut actual_max_tail=BTreeSet::<usize>::new();
                                let mut active_octets=BTreeSet::<usize>::new();
                                for (ordinal,(relation,term)) in batch.terms().enumerate() {
                                    let gate=&term.gate;
                                    if gate.c1.is_zero()&&gate.c3.is_zero(){continue;}
                                    let octet=gate.left&!7usize;
                                    active_octets.insert(octet);
                                    for offset in 0..8 {
                                        let wire=octet+offset;
                                        let source_owner=wire/OWNER_ROW_BITS;
                                        let local=wire%OWNER_ROW_BITS;
                                        let source_value=match source_owner {
                                            C431_OWNER=>Some(((packed.packed_bytes()[local/8]>>(local%8))&1)!=0),
                                            844_670=>max_values.get(&wire).copied(),
                                            845_757|845_758=>work_values.get(&wire).copied(),
                                            _=>None,
                                        };
                                        assert!(source_value.is_some(),
                                            "C434 first unqualified source relation={relation:?} ordinal={ordinal} octet={octet} missing_wire={wire} owner={source_owner} local={local}");
                                        if matches!(source_owner,845_757|845_758)
                                            && !(987_674..987_898).contains(&local) {
                                            actual_work_boundary.insert(wire);
                                        }
                                        if source_owner==844_670 && (1_000_324..1_000_328).contains(&local) {
                                            actual_max_tail.insert(wire);
                                        }
                                    }
                                }
                                let expected_work_boundary=c432_boundary.keys().chain(c434_tree_tail.keys())
                                    .copied().collect::<BTreeSet<_>>();
                                assert_eq!(actual_work_boundary,expected_work_boundary,
                                    "C434 actual ordered source Work-D octet closure");
                                let expected_max_tail=(1_000_324usize..1_000_328)
                                    .map(|local|844_670*OWNER_ROW_BITS+local).collect::<BTreeSet<_>>();
                                assert_eq!(actual_max_tail,expected_max_tail,
                                    "C434 exact scheduled context1 MAX octet tail");
                                for &wire in &actual_max_tail {
                                    assert!(max_values.contains_key(&wire),"C434 MAX tail source value");
                                    assert!(valid_max_tag(wire,1,844_672,
                                        MaxReplayAuthor::Scheduled(Writer::Max{context:1,end:844_672})),
                                        "C434 exact scheduled MAX tail author");
                                    assert!(!valid_max_tag(wire,1,844_672,
                                        MaxReplayAuthor::Scheduled(Writer::Max{context:0,end:844_672})),
                                        "C434 wrong MAX tail context tag rejected");
                                }
                                println!("C434_SOURCE_OCTET_CENSUS_PASS active_octets={} work_boundary={} new_tree=8 max_new={} before_numeric=true proof=false client=false",
                                    active_octets.len(),actual_work_boundary.len(),actual_max_tail.len());
                            }

                            // Retain every global pair touched by an occurrence,
                            // including c0-only terms. Pair bases remain global.
                            let mut pair_terms=BTreeMap::<usize,[Fr;4]>::new();
                            let mut odd_active_pairs=BTreeSet::new();
                            let mut c0_only=None;
                            let mut first_occurrence_delta=None;
                            let mut odd_left_delta=None;
                            let mut occurrence_count=0usize;
                            let mut canonical=batch.terms().enumerate();
                            for (ordinal,(relation,term)) in batch.terms().enumerate() {
                                let (canonical_ordinal,(canonical_relation,canonical_term))=
                                    canonical.next().expect("C431 canonical source occurrence exists");
                                assert_eq!(ordinal,canonical_ordinal,
                                    "C431 aggregation source ordinal");
                                assert_eq!(relation,canonical_relation,
                                    "C431 aggregation source relation");
                                assert_eq!(term,canonical_term,
                                    "C431 aggregation complete source term");
                                let q=term.row.checked_sub(C431_OWNER_BASE)
                                    .filter(|q|*q<C431_ROWS)
                                    .expect("C431 source term owner/ROW range");
                                let gate=&term.gate;
                                let pair=gate.left&!1usize;
                                let slot=gate.left&1;
                                if !gate.c1.is_zero()||!gate.c3.is_zero() {
                                    let _required_sibling=x_value(gate.left^1);
                                    if slot==1 {odd_active_pairs.insert(pair);}
                                }
                                let values=pair_terms.entry(pair).or_insert([Fr::zero();4]);
                                let right=if gate.c2.is_zero()&&gate.c3.is_zero(){Fr::zero()}
                                    else {Fr::from(x_value(gate.right) as u64)};
                                let weight=eq_row(q);
                                let delta_a=weight*(gate.c1+gate.c3*right);
                                let delta_b=weight*(gate.c0+gate.c2*right);
                                values[slot]+=delta_a;
                                values[2+slot]+=delta_b;
                                if c0_only.is_none() && !gate.c0.is_zero() && gate.c1.is_zero()
                                    && gate.c2.is_zero() && gate.c3.is_zero() {
                                    let delta=weight*gate.c0;
                                    if !delta.is_zero() {c0_only=Some((pair,slot,delta));}
                                }
                                if first_occurrence_delta.is_none()&&!delta_b.is_zero() {
                                    first_occurrence_delta=Some((pair,slot,delta_a,delta_b));
                                }
                                if odd_left_delta.is_none() && slot==1
                                    && (!delta_a.is_zero()||!delta_b.is_zero()) {
                                    let left_x=Fr::from(x_value(gate.left) as u64);
                                    let sibling_x=Fr::from(x_value(gate.left^1) as u64);
                                    if !delta_b.is_zero() ||
                                        (!delta_a.is_zero()&&left_x!=sibling_x) {
                                        odd_left_delta=Some((pair,delta_a,delta_b));
                                    }
                                }
                                occurrence_count+=1;
                            }
                            assert!(canonical.next().is_none(),
                                "C431 aggregation consumed complete canonical source stream");
                            assert_eq!(occurrence_count,487_671);
                            let claim0=residuals.iter().enumerate().fold(Fr::zero(),
                                |sum,(q,value)|sum+eq_row(q)*value);
                            assert!(claim0.is_zero(),"C431 independently weighted claim0");

                            let mut compact_a=Vec::with_capacity(pair_terms.len()*2);
                            let mut compact_b=Vec::with_capacity(pair_terms.len()*2);
                            let mut compact_x=Vec::with_capacity(pair_terms.len()*2);
                            for (&pair,values) in &pair_terms {
                                assert_eq!(pair&1,0,"C431 global even pair base");
                                compact_a.extend([values[0],values[1]]);
                                compact_b.extend([values[2],values[3]]);
                                if values[0].is_zero()&&values[1].is_zero() {
                                    compact_x.extend([Fr::zero(),Fr::zero()]);
                                } else {
                                    compact_x.push(Fr::from(x_value(pair) as u64));
                                    compact_x.push(Fr::from(x_value(pair+1) as u64));
                                }
                            }
                            let p0=crate::gkr::quadratic_message(&compact_a,&compact_b,&compact_x);
                            assert_eq!(p0.len(),3);
                            let eval_at=|t:Fr| -> Fr {
                                let mut sum=Fr::zero();
                                for (_relation,term) in batch.terms() {
                                    let q=term.row.checked_sub(C431_OWNER_BASE)
                                        .filter(|q|*q<C431_ROWS)
                                        .expect("C431 direct source ROW range");
                                    let gate=&term.gate;
                                    let pair=gate.left&!1usize;
                                    let slot=gate.left&1;
                                    let lambda=if slot==0 {Fr::one()-t} else {t};
                                    let right=if gate.c2.is_zero()&&gate.c3.is_zero() {
                                        Fr::zero()
                                    } else {Fr::from(x_value(gate.right) as u64)};
                                    let (x_even,x_odd)=if gate.c1.is_zero()&&gate.c3.is_zero() {
                                        (Fr::zero(),Fr::zero())
                                    } else {
                                        (Fr::from(x_value(pair) as u64),
                                            Fr::from(x_value(pair+1) as u64))
                                    };
                                    let x_at=(Fr::one()-t)*x_even+t*x_odd;
                                    sum+=eq_row(q)*lambda*((gate.c1+gate.c3*right)*x_at
                                        +gate.c0+gate.c2*right);
                                }
                                sum
                            };
                            let y0=eval_at(Fr::zero());let y1=eval_at(Fr::one());
                            let y2=eval_at(Fr::from(2u64));
                            let half=Fr::from(2u64).inverse().expect("two invertible in Fr");
                            let direct=[y0,y1-y0-(y2-Fr::from(2u64)*y1+y0)*half,
                                (y2-Fr::from(2u64)*y1+y0)*half];
                            assert_eq!(p0,direct,"C431 independent direct interpolation coefficients");
                            assert_eq!(p0[0]+crate::gkr::eval_polynomial(&p0,Fr::one()),claim0,
                                "C431 first-message sumcheck identity");
                            assert_eq!(p0[0]+crate::gkr::eval_polynomial(&p0,Fr::one()),Fr::zero());

                            let pair_indices:BTreeMap<usize,usize>=pair_terms.keys().copied()
                                .enumerate().map(|(index,pair)|(pair,index)).collect();
                            // Isolated numeric/source mutations all retain this
                            // fixed r, immutable source map and baseline p0.
                            let p0_for=|a:&[Fr],b:&[Fr],x:&[Fr]| 
                                crate::gkr::quadratic_message(a,b,x);
                            let mut sibling_mutant=compact_x.clone();
                            let sibling_pair=odd_active_pairs.iter().find(|pair|
                                !pair_terms[pair][1].is_zero())
                                .map(|pair|pair_indices[pair])
                                .expect("C431 active A pair for sibling mutant");
                            assert!(!compact_a[2*sibling_pair+1].is_zero());
                            sibling_mutant[2*sibling_pair]=Fr::one()-sibling_mutant[2*sibling_pair];
                            assert_ne!(p0_for(&compact_a,&compact_b,&sibling_mutant),p0,
                                "C431 isolated required sibling-bit mutant");

                            let (c0_pair,c0_slot,c0_delta)=c0_only
                                .expect("C431 retained c0-only source occurrence");
                            let c0_index=pair_indices[&c0_pair]*2+c0_slot;
                            let mut c0_mutant=compact_b.clone();c0_mutant[c0_index]+=c0_delta;
                            assert_ne!(p0_for(&compact_a,&c0_mutant,&compact_x),p0,
                                "C431 isolated c0-only coefficient mutant");

                            let (drop_pair,drop_slot,drop_a,drop_b)=first_occurrence_delta
                                .expect("C431 nonzero source occurrence for coverage mutants");
                            let drop_index=pair_indices[&drop_pair]*2+drop_slot;
                            let mut dropped_a=compact_a.clone();let mut dropped_b=compact_b.clone();
                            dropped_a[drop_index]-=drop_a;dropped_b[drop_index]-=drop_b;
                            assert_ne!(p0_for(&dropped_a,&dropped_b,&compact_x),p0,
                                "C431 isolated dropped-occurrence mutant");
                            let mut duplicated_a=compact_a.clone();let mut duplicated_b=compact_b.clone();
                            duplicated_a[drop_index]+=drop_a;duplicated_b[drop_index]+=drop_b;
                            assert_ne!(p0_for(&duplicated_a,&duplicated_b,&compact_x),p0,
                                "C431 isolated duplicated-occurrence mutant");

                            let (odd_pair,odd_a,odd_b)=odd_left_delta
                                .expect("C431 odd global wire for parity mutant");
                            let odd_index=pair_indices[&odd_pair]*2+1;
                            let mut parity_a=compact_a.clone();let mut parity_b=compact_b.clone();
                            parity_a[odd_index]-=odd_a;parity_a[odd_index-1]+=odd_a;
                            parity_b[odd_index]-=odd_b;parity_b[odd_index-1]+=odd_b;
                            assert_ne!(p0_for(&parity_a,&parity_b,&compact_x),p0,
                                "C431 isolated global wire parity mutant");
                            crate::gkr::append_usize(&mut transcript,b"gkr-layer-index",0);
                            crate::gkr::append_polynomial(&mut transcript,b"gkr-sumcheck-polynomial",&p0);
                            let challenge=transcript.challenge_scalar(b"gkr-sumcheck-challenge");
                            let claim1=crate::gkr::eval_polynomial(&p0,challenge);
                            let mut replay=crate::transcript::Transcript::new(
                                b"nipopow-c431-h21-owner845759-first-u-diagnostic-v1");
                            replay.append_bytes(b"c431-frame-sha256",&decode32(FRAME_SHA256));
                            replay.append_bytes(b"c431-c430-receipt-sha256",
                                &decode32("618386c36855b629c8913bc32bf7d7bcc744dc4e70d3b5dec3ac4efc09f2de78"));
                            replay.append_bytes(b"c431-owner-u64le",&845_759u64.to_le_bytes());
                            replay.append_bytes(b"c431-rows-u64le",&524_288u64.to_le_bytes());
                            replay.append_bytes(b"c431-terms-u64le",&487_671u64.to_le_bytes());
                            replay.append_bytes(b"c431-reads-u64le",&690_914u64.to_le_bytes());
                            let replay_r=crate::gkr::output_point(C431_ROWS,&mut replay);
                            assert_eq!(replay_r,r,"C431 fixed diagnostic point replay");
                            crate::gkr::append_usize(&mut replay,b"gkr-layer-index",0);
                            crate::gkr::append_polynomial(&mut replay,b"gkr-sumcheck-polynomial",&p0);
                            let replay_challenge=replay.challenge_scalar(b"gkr-sumcheck-challenge");
                            assert_eq!(replay_challenge,challenge,"C431 challenge replay");
                            assert_eq!(crate::gkr::eval_polynomial(&p0,replay_challenge),claim1,
                                "C431 claim1 replay");
                            println!("C431_AUTHENTIC_CARRY_FIRST_U_DIAGNOSTIC owner=845759 terms={occurrence_count} typed_reads={typed_count} pairs={} max_cells={max_count} work_d_cells={} p0={p0:?} claim0_zero=true challenge={challenge:?} claim1={claim1:?} proof=false client=false",
                                pair_terms.len(),expected_work.len());
                            assert_eq!(claim0,Fr::zero());
                            println!("C431_AUTHENTIC_CARRY_FIRST_U_PASS owner=845759 p0_match=true claim0_zero=true proof=false client=false");
                            if second_u {
                                use ark_ff::{Field,One,Zero};
                                use std::str::FromStr;
                                assert_eq!(challenge,Fr::from_str("1873830279740564804834045759928339352542129553512015304682284149059412722691").unwrap(),
                                    "C432 pinned C431 first-U challenge");
                                assert_eq!(claim1,Fr::from_str("6103393472285109332148428565263363228728906058693913018840245196985567336316").unwrap(),
                                    "C432 pinned C431 claim1");
                                let mut blocks=BTreeMap::<usize,[Fr;6]>::new();
                                for (&pair,values) in &pair_terms {
                                    let block=pair&!3usize;
                                    let slot=(pair>>1)&1;
                                    let folded_a=(Fr::one()-challenge)*values[0]+challenge*values[1];
                                    let folded_b=(Fr::one()-challenge)*values[2]+challenge*values[3];
                                    let entry=blocks.entry(block).or_insert([Fr::zero();6]);
                                    entry[slot]+=folded_a;
                                    entry[2+slot]+=folded_b;
                                }
                                for (&block,values) in blocks.iter_mut() {
                                    if !values[0].is_zero()||!values[1].is_zero() {
                                        for slot in 0..2 {
                                            let pair=block+2*slot;
                                            let x0=Fr::from(x_value(pair) as u64);
                                            let x1=Fr::from(x_value(pair+1) as u64);
                                            values[4+slot]=(Fr::one()-challenge)*x0+challenge*x1;
                                        }
                                    }
                                }
                                let mut a1=Vec::with_capacity(blocks.len()*2);
                                let mut b1=Vec::with_capacity(blocks.len()*2);
                                let mut x1=Vec::with_capacity(blocks.len()*2);
                                for (&block,values) in &blocks {
                                    assert_eq!(block&3,0,"C432 globally keyed four-wire block");
                                    a1.extend([values[0],values[1]]);
                                    b1.extend([values[2],values[3]]);
                                    x1.extend([values[4],values[5]]);
                                }
                                let p1=crate::gkr::quadratic_message(&a1,&b1,&x1);
                                assert_eq!(p1.len(),3);
                                let direct_at=|t:Fr| -> Fr {
                                    let chi=|bit:usize| if bit==0 {Fr::one()-challenge} else {challenge};
                                    let lambda=|bit:usize| if bit==0 {Fr::one()-t} else {t};
                                    let mut canonical=batch.terms().enumerate();
                                    let mut total=Fr::zero();
                                    for (ordinal,(relation,term)) in batch.terms().enumerate() {
                                        let (reference_ordinal,(reference_relation,reference_term))=
                                            canonical.next().expect("C432 direct canonical source occurrence");
                                        assert_eq!(ordinal,reference_ordinal,"C432 direct source ordinal");
                                        assert_eq!(relation,reference_relation,"C432 direct source relation");
                                        assert_eq!(term,reference_term,"C432 direct complete source term");
                                        let gate=&term.gate;
                                        let q=term.row.checked_sub(C431_OWNER_BASE)
                                            .filter(|q|*q<C431_ROWS)
                                            .expect("C432 direct original ROW source");
                                        let active=!gate.c1.is_zero()||!gate.c3.is_zero();
                                        let right=if gate.c2.is_zero()&&gate.c3.is_zero(){Fr::zero()}
                                            else{Fr::from(x_value(gate.right) as u64)};
                                        let x_at=if active {
                                            let block=gate.left&!3usize;
                                            let x=[0usize,1,2,3].map(|offset|
                                                Fr::from(x_value(block+offset) as u64));
                                            let low0=(Fr::one()-challenge)*x[0]+challenge*x[1];
                                            let low1=(Fr::one()-challenge)*x[2]+challenge*x[3];
                                            (Fr::one()-t)*low0+t*low1
                                        }else{Fr::zero()};
                                        total+=eq_row(q)*chi(gate.left&1)*lambda((gate.left>>1)&1)
                                            *((gate.c1+gate.c3*right)*x_at+gate.c0+gate.c2*right);
                                    }
                                    assert!(canonical.next().is_none(),"C432 direct complete source sequence");
                                    total
                                };
                                let y0=direct_at(Fr::zero());let y1=direct_at(Fr::one());
                                let y2=direct_at(Fr::from(2u64));
                                let half=Fr::from(2u64).inverse().expect("two invertible in Fr");
                                let direct=[y0,y1-y0-(y2-Fr::from(2u64)*y1+y0)*half,
                                    (y2-Fr::from(2u64)*y1+y0)*half];
                                assert_eq!(p1,direct,"C432 independent original-term p1 oracle");
                                assert_eq!(p1[0]+crate::gkr::eval_polynomial(&p1,Fr::one()),claim1,
                                    "C432 second-message sumcheck identity");
                                let mut parity_rejected=false;
                                for index in (0..a1.len()).step_by(2) {
                                    let mut shifted=a1.clone();shifted.swap(index,index+1);
                                    if crate::gkr::quadratic_message(&shifted,&b1,&x1)!=p1 {
                                        parity_rejected=true;break;
                                    }
                                    let mut shifted_x=x1.clone();shifted_x.swap(index,index+1);
                                    if crate::gkr::quadratic_message(&a1,&b1,&shifted_x)!=p1 {
                                        parity_rejected=true;break;
                                    }
                                }
                                assert!(parity_rejected,"C432 isolated quartet parity shift changes p1");
                                let mut omission_witness=None;
                                for (ordinal,(relation,term)) in batch.terms().enumerate() {
                                    let gate=&term.gate;
                                    if gate.c1.is_zero()&&gate.c3.is_zero(){continue;}
                                    let q=term.row.checked_sub(C431_OWNER_BASE)
                                        .filter(|q|*q<C431_ROWS).expect("C432 omission source ROW");
                                    let right=if gate.c2.is_zero()&&gate.c3.is_zero(){Fr::zero()}
                                        else{Fr::from(x_value(gate.right) as u64)};
                                    let delta_a=eq_row(q)*(gate.c1+gate.c3*right);
                                    if delta_a.is_zero(){continue;}
                                    let pair=gate.left&!1usize;
                                    let block=pair&!3usize;
                                    let block_index=blocks.keys().position(|candidate|*candidate==block)
                                        .expect("C432 omission global block");
                                    let folded_slot=(pair>>1)&1;
                                    if a1[2*block_index+folded_slot].is_zero(){continue;}
                                    let bit0=gate.left&1;
                                    let chi=if bit0==0 {Fr::one()-challenge}else{challenge};
                                    let delta_b=eq_row(q)*(gate.c0+gate.c2*right);
                                    let mut dropped_a=a1.clone();let mut dropped_b=b1.clone();
                                    dropped_a[2*block_index+folded_slot]-=chi*delta_a;
                                    dropped_b[2*block_index+folded_slot]-=chi*delta_b;
                                    if crate::gkr::quadratic_message(&dropped_a,&dropped_b,&x1)!=p1 {
                                        omission_witness=Some((ordinal,format!("{relation:?}"),gate.left,block));
                                        break;
                                    }
                                }
                                let (omitted_ordinal,omitted_relation,omitted_wire,omitted_block)=
                                    omission_witness.expect("C432 source-qualified A-active term whose omission changes p1");
                                println!("C432_OMISSION_MUTANT_REJECTED ordinal={omitted_ordinal} relation={omitted_relation} wire={omitted_wire} block={omitted_block} p1_changed=true");
                                crate::gkr::append_polynomial(&mut transcript,b"gkr-sumcheck-polynomial",&p1);
                                let challenge2=transcript.challenge_scalar(b"gkr-sumcheck-challenge");
                                let claim2=crate::gkr::eval_polynomial(&p1,challenge2);
                                crate::gkr::append_polynomial(&mut replay,b"gkr-sumcheck-polynomial",&p1);
                                assert_eq!(replay.challenge_scalar(b"gkr-sumcheck-challenge"),challenge2,
                                    "C432 transcript p1 challenge replay");
                                assert_eq!(crate::gkr::eval_polynomial(&p1,challenge2),claim2);
                                println!("C432_AUTHENTIC_CARRY_SECOND_U_DIAGNOSTIC owner=845759 blocks={} p1={p1:?} claim1_bound=true challenge2={challenge2:?} claim2={claim2:?} source_boundary=8 proof=false client=false",blocks.len());
                                println!("C433_AUTHENTIC_CARRY_SECOND_U_PASS owner=845759 p1_match=true claim1_bound=true proof=false client=false");
                                if third_u {
                                    assert_eq!(challenge2,Fr::from_str("18185979068642816323475958710870383280070980186994063160243249780362127339059").unwrap(),
                                        "C434 pinned C433 second-U challenge");
                                    assert_eq!(claim2,Fr::from_str("2691867441645394040614662363103885469230274131705693388792379226136983941869").unwrap(),
                                        "C434 pinned C433 claim2");
                                    let mut octets=BTreeMap::<usize,[Fr;6]>::new();
                                    for (&block,values) in &blocks {
                                        let octet=block&!7usize;
                                        let slot=(block>>2)&1;
                                        let entry=octets.entry(octet).or_insert([Fr::zero();6]);
                                        entry[slot]+=(Fr::one()-challenge2)*values[0]+challenge2*values[1];
                                        entry[2+slot]+=(Fr::one()-challenge2)*values[2]+challenge2*values[3];
                                    }
                                    for (&octet,values) in octets.iter_mut() {
                                        if !values[0].is_zero()||!values[1].is_zero() {
                                            let original_x=std::array::from_fn(|offset|
                                                Fr::from(x_value(octet+offset) as u64));
                                            let folded_x=c434_fold_octet(original_x,challenge,challenge2);
                                            values[4]=folded_x[0];values[5]=folded_x[1];
                                        }
                                    }
                                    let mut a2=Vec::with_capacity(octets.len()*2);
                                    let mut b2=Vec::with_capacity(octets.len()*2);
                                    let mut x2=Vec::with_capacity(octets.len()*2);
                                    for (&octet,values) in &octets {
                                        assert_eq!(octet&7,0,"C434 globally keyed eight-wire block");
                                        a2.extend([values[0],values[1]]);
                                        b2.extend([values[2],values[3]]);
                                        x2.extend([values[4],values[5]]);
                                    }
                                    let p2=crate::gkr::quadratic_message(&a2,&b2,&x2);
                                    assert_eq!(p2.len(),3);
                                    let direct_p2_at=|t:Fr| -> Fr {
                                        let chi_alpha=|bit:usize| if bit==0 {Fr::one()-challenge}else{challenge};
                                        let chi_beta=|bit:usize| if bit==0 {Fr::one()-challenge2}else{challenge2};
                                        let chi_t=|bit:usize| if bit==0 {Fr::one()-t}else{t};
                                        let mut canonical=batch.terms().enumerate();
                                        let mut total=Fr::zero();
                                        for (ordinal,(relation,term)) in batch.terms().enumerate() {
                                            let (reference_ordinal,(reference_relation,reference_term))=
                                                canonical.next().expect("C434 direct canonical source occurrence");
                                            assert_eq!(ordinal,reference_ordinal,"C434 direct source ordinal");
                                            assert_eq!(relation,reference_relation,"C434 direct source relation");
                                            assert_eq!(term,reference_term,"C434 direct complete source term");
                                            let gate=&term.gate;
                                            let q=term.row.checked_sub(C431_OWNER_BASE)
                                                .filter(|q|*q<C431_ROWS)
                                                .expect("C434 direct original ROW source");
                                            let active=!gate.c1.is_zero()||!gate.c3.is_zero();
                                            let right=if gate.c2.is_zero()&&gate.c3.is_zero(){Fr::zero()}
                                                else{Fr::from(x_value(gate.right) as u64)};
                                            let x_at=if active {
                                                let octet=gate.left&!7usize;
                                                let mut folded_x=Fr::zero();
                                                for offset in 0..8 {
                                                    let chi_a=if offset&1==0 {Fr::one()-challenge}else{challenge};
                                                    let chi_b=if offset&2==0 {Fr::one()-challenge2}else{challenge2};
                                                    let chi_c=if offset&4==0 {Fr::one()-t}else{t};
                                                    folded_x+=chi_a*chi_b*chi_c
                                                        *Fr::from(x_value(octet+offset) as u64);
                                                }
                                                folded_x
                                            }else{Fr::zero()};
                                            total+=eq_row(q)*chi_alpha(gate.left&1)
                                                *chi_beta((gate.left>>1)&1)*chi_t((gate.left>>2)&1)
                                                *((gate.c1+gate.c3*right)*x_at+gate.c0+gate.c2*right);
                                        }
                                        assert!(canonical.next().is_none(),"C434 direct complete source sequence");
                                        total
                                    };
                                    let y0=direct_p2_at(Fr::zero());
                                    let y1=direct_p2_at(Fr::one());
                                    let y2=direct_p2_at(Fr::from(2u64));
                                    let half=Fr::from(2u64).inverse().expect("two invertible in Fr");
                                    let direct_p2=[y0,y1-y0-(y2-Fr::from(2u64)*y1+y0)*half,
                                        (y2-Fr::from(2u64)*y1+y0)*half];
                                    assert_eq!(p2,direct_p2,"C434 independent original-term p2 oracle");
                                    assert_eq!(p2[0]+crate::gkr::eval_polynomial(&p2,Fr::one()),claim2,
                                        "C434 third-message sumcheck identity");
                                    let mut parity_rejected=false;
                                    for index in (0..a2.len()).step_by(2) {
                                        let mut shifted=a2.clone();shifted.swap(index,index+1);
                                        if crate::gkr::quadratic_message(&shifted,&b2,&x2)!=p2 {
                                            parity_rejected=true;break;
                                        }
                                        let mut shifted_x=x2.clone();shifted_x.swap(index,index+1);
                                        if crate::gkr::quadratic_message(&a2,&b2,&shifted_x)!=p2 {
                                            parity_rejected=true;break;
                                        }
                                    }
                                    assert!(parity_rejected,"C434 isolated octet parity mutation changes p2");
                                    let mut omission_witness=None;
                                    for (ordinal,(relation,term)) in batch.terms().enumerate() {
                                        let gate=&term.gate;
                                        if gate.c1.is_zero()&&gate.c3.is_zero(){continue;}
                                        let q=term.row.checked_sub(C431_OWNER_BASE)
                                            .filter(|q|*q<C431_ROWS).expect("C434 omission source ROW");
                                        let right=if gate.c2.is_zero()&&gate.c3.is_zero(){Fr::zero()}
                                            else{Fr::from(x_value(gate.right) as u64)};
                                        let delta_a=eq_row(q)*(gate.c1+gate.c3*right);
                                        if delta_a.is_zero(){continue;}
                                        let octet=gate.left&!7usize;
                                        let index=octets.keys().position(|candidate|*candidate==octet)
                                            .expect("C434 omission global octet");
                                        let slot=(gate.left>>2)&1;
                                        let chi_alpha=if gate.left&1==0 {Fr::one()-challenge}else{challenge};
                                        let chi_beta=if (gate.left>>1)&1==0 {Fr::one()-challenge2}else{challenge2};
                                        let delta_b=eq_row(q)*(gate.c0+gate.c2*right);
                                        let mut dropped_a=a2.clone();let mut dropped_b=b2.clone();
                                        dropped_a[2*index+slot]-=chi_alpha*chi_beta*delta_a;
                                        dropped_b[2*index+slot]-=chi_alpha*chi_beta*delta_b;
                                        if crate::gkr::quadratic_message(&dropped_a,&dropped_b,&x2)!=p2 {
                                            omission_witness=Some((ordinal,format!("{relation:?}"),gate.left,octet));
                                            break;
                                        }
                                    }
                                    let (omitted_ordinal,omitted_relation,omitted_wire,omitted_octet)=
                                        omission_witness.expect("C434 A-active source term whose omission changes p2");
                                    println!("C434_OMISSION_MUTANT_REJECTED ordinal={omitted_ordinal} relation={omitted_relation} wire={omitted_wire} octet={omitted_octet} p2_changed=true");
                                    crate::gkr::append_polynomial(&mut transcript,b"gkr-sumcheck-polynomial",&p2);
                                    let challenge3=transcript.challenge_scalar(b"gkr-sumcheck-challenge");
                                    let claim3=crate::gkr::eval_polynomial(&p2,challenge3);
                                    crate::gkr::append_polynomial(&mut replay,b"gkr-sumcheck-polynomial",&p2);
                                    assert_eq!(replay.challenge_scalar(b"gkr-sumcheck-challenge"),challenge3,
                                        "C434 transcript p2 challenge replay without new layer index");
                                    assert_eq!(crate::gkr::eval_polynomial(&p2,challenge3),claim3);
                                    println!("C434_AUTHENTIC_CARRY_THIRD_U_DIAGNOSTIC owner=845759 octets={} p2={p2:?} claim2_bound=true challenge3={challenge3:?} claim3={claim3:?} work_new_tree=8 max_new=4 proof=false client=false",octets.len());
                                    println!("C434_AUTHENTIC_CARRY_THIRD_U_PASS owner=845759 p2_match=true claim2_bound=true proof=false client=false");
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(score.closed_owner_cells(845_758).unwrap_err(),
        "Score endpoint replay inactive owner");
    assert_eq!(score.closed_owner_relation(845_758).err().unwrap(),
        "Score relation inactive owner");
    phase("score_replay_and_integer_oracle_verified",started);
    println!("C187_NATIVE_SCORE_PASS max_owners=7683 score_owners=7543 score_roles=15083 payload_bytes={} local_record_lease_capacity_bytes={} terminal_r0={} terminal_r1={} global_x_row=false pcs_proof_client=false",
        score.record_payload_bytes(),score.retained_capacity_bytes(),terminal[0],terminal[1]);
}

//! Generic Eligible08 scheduled MAX/Cap ROW/X admission. This is an opaque,
//! incomplete component: pending foreign authors, other HEADER X sources and
//! the rest of H21 have no finish, packed-witness or proof interface here.
use ark_bn254::Fr;
use ark_ff::Zero;
use std::{collections::{BTreeMap,BTreeSet}, sync::Arc};
use crate::{daa_history_roster::DaaHistoryRoster, header_scheduled_retirement::Merge,
    h21_scheduled_max_cap::{Eligible08NativeSnapshot, Eligible08OwnerLease, NativeParent, Writer},
    packed_owner_assembly::{NativePrefix,NativeOwnerProducer,NativeWorkDLease}, sparse::Term, work_tree_history_plan::WorkTreeHistoryPlan};

const WIDTH:usize=1<<20;
const ROWS:usize=1<<19;

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
enum Author { Header, Scheduled(Writer), NativeWorkD{height:usize} }
#[derive(Clone,Debug,PartialEq,Eq)]
struct Row {author:Author,term:Term}
#[derive(Clone,Debug,PartialEq,Eq)]
struct Cell {wire:usize,writer:Writer,value:Fr}

/// Ownership and unresolved typed imports only; no completed-witness API.
#[derive(Clone,Default,PartialEq,Eq)]
pub(super) struct Destination {
    parent:Option<NativeParent>,
    rows:BTreeMap<usize,Author>,
    cells:BTreeMap<usize,(Author,Fr)>,
    imports:BTreeMap<usize,(Author,Fr)>,
    // Exact active HEADER D coordinates consumed by scheduled MAX. Prepared
    // supplies expected arithmetic, never HEADER D ROW/X authorship.
    external_header_d:BTreeMap<usize,(Author,Fr)>,
}
impl Destination {
    pub(super) fn pending_source_owners(&self)->Vec<usize> {
        self.imports.keys().filter(|wire|!self.cells.contains_key(wire))
            .map(|wire|wire/WIDTH).collect::<std::collections::BTreeSet<_>>().into_iter().collect()
    }
    pub(super) fn pending_header_d(&self)->usize {
        self.external_header_d.keys().filter(|wire|!self.cells.contains_key(wire)).count()
    }
}

#[allow(dead_code)]
pub(super) struct Joined {
    owner:usize,rows:Arc<Vec<Row>>,cells:Arc<Vec<Cell>>,retired:[usize;4],
    replacement_mask:Vec<bool>,
    external_header_d:BTreeMap<usize,(Author,Fr)>,
}

/// Published HEADER/Cap source for the first modern owner. It retains the
/// actual scheduled publisher and its destination; scalar q alone cannot
/// construct this source. Its MAX imports remain unresolved foreign authors.
/// Retained HEADER ROW ownership leaves its active X inputs unauthenticated;
/// those dependencies are not counted by pending_max_read_count.
#[derive(Clone)]
pub(super) struct FirstModernCapPublication {
    root:[u8;32], total:[u8;28], profile:[u8;32], cut:Vec<u8>,
    candidate:Candidate, destination:Arc<Destination>,
}

pub(super) struct CapJoinMaterial {
    // None denotes the retained HEADER writer, Some(c) its Cap writer.
    pub rows:Vec<(Option<usize>,Term)>,
    pub cells:Vec<(usize,usize,bool)>,
    pub q:[Vec<(usize,bool)>;2],
}

impl FirstModernCapPublication {
    fn stage(plan:&WorkTreeHistoryPlan,snapshot:&Eligible08NativeSnapshot,
        roster:&DaaHistoryRoster<'_>,
        first:&crate::h21_scheduled_max_cap::FirstModernCapLease)->Result<Self,String> {
        use blake2::{digest::consts::U32,Blake2b,Digest};
        let lease=snapshot.owner_lease(845_759)?;
        let candidate=Candidate::stage(plan,snapshot,roster,&lease)?;
        let mut destination=Destination::default();
        candidate.clone().publish(&mut destination)?;
        let mut bytes=crate::work_tree_fixed_hash::PROFILE_PREFIX.to_vec();
        bytes.extend_from_slice(&crate::header_order::MAINNET_GENESIS);
        let out=Self {root:plan.descriptor().root,total:plan.work_profile().total_be28,
            profile:Blake2b::<U32>::digest(bytes).into(),
            cut:crate::bank53_map::CutDescriptor::eligible08().canonical_identity(),
            candidate,destination:Arc::new(destination)};
        first.require_stage_identity(out.root,out.total,out.profile,&out.cut)?;
        let material=out.checked_material()?;
        for context in 0..2 {
            let cells=material.cells.iter().filter(|(_,c,_)|*c==context)
                .map(|(wire,_,value)|(wire%WIDTH,*value)).collect::<Vec<_>>();
            let rows=material.rows.iter().filter(|(c,_)|*c==Some(context))
                .map(|(_,term)|term.clone()).collect::<Vec<_>>();
            if first.cap_cells(context)?!=cells || first.cap_rows(context)?!=rows {
                return Err("first Cap publication exact FirstModernCapLease source".into());
            }
        }
        Ok(out)
    }

    pub(super) fn require_binding(&self,root:[u8;32],total:[u8;28],profile:[u8;32],cut:&[u8])
        ->Result<(),String> {
        if self.root!=root || self.total!=total || self.profile!=profile || self.cut!=cut {
            return Err("first Cap publication parent/cut binding".into());
        }
        Ok(())
    }

    /// Revalidate the exact published bytes and ownership before exporting
    /// any material. Each occurrence survives; equal ROW ids are additive.
    pub(super) fn checked_material(&self)->Result<CapJoinMaterial,String> {
        let c=&self.candidate;
        if c.owner!=845_759 || c.retired!=[0,0,2048,2048]
            || c.cells.len()!=4096 || c.imports.len()!=448
            || !c.external_header_d.is_empty() {
            return Err("first Cap publication exact owner/retirement/census".into());
        }
        let mut replay=Destination::default();
        c.clone().publish(&mut replay)?;
        if replay!=*self.destination {return Err("first Cap publication exact published source".into());}
        let mut rows=Vec::with_capacity(c.rows.len());
        let mut cap_terms=[0usize;2];
        for row in c.rows.iter() {
            let context=match row.author {
                Author::Header=>None,
                Author::Scheduled(Writer::Cap{context,origin:845_760}) if context<2=> {
                    cap_terms[context]+=1;Some(context)
                }
                _=>return Err("first Cap publication exact ROW author".into()),
            };
            rows.push((context,row.term.clone()));
        }
        if cap_terms!=[6419,6419] {return Err("first Cap publication exact ROW census".into());}
        let mut cells=Vec::with_capacity(4096);
        let mut q:[Vec<(usize,bool)>;2]=[Vec::new(),Vec::new()];
        let mut domains=[0usize;2];
        for cell in c.cells.iter() {
            let context=match cell.writer {
                Writer::Cap{context,origin:845_760} if context<2=>context,
                _=>return Err("first Cap publication exact X author".into()),
            };
            let local=cell.wire.checked_sub(845_759*WIDTH+[1_000_770,1_002_818][context])
                .filter(|local|*local<2048).ok_or("first Cap publication exact X domain")?;
            if local!=domains[context] || (cell.value!=Fr::zero() && cell.value!=ark_ff::One::one()) {
                return Err("first Cap publication exact ordered Boolean X".into());
            }
            domains[context]+=1;
            cells.push((cell.wire,context,cell.value==ark_ff::One::one()));
            if (740..805).contains(&local) {q[context].push((cell.wire,cell.value==ark_ff::One::one()));}
        }
        if domains!=[2048,2048] || q.iter().any(|bits|bits.len()!=65) {
            return Err("first Cap publication exact X/q census".into());
        }
        for context in 0..2 {
            let imports=c.imports.iter().filter(|cell|cell.writer==Writer::Max{context,end:844_672})
                .collect::<Vec<_>>();
            if imports.len()!=224 || imports.iter().enumerate().any(|(bit,cell)|
                cell.wire!=844_670*WIDTH+[999_424,1_000_097][context]+bit) {
                return Err("first Cap publication exact pending MAX source".into());
            }
        }
        Ok(CapJoinMaterial{rows,cells,q})
    }

    pub(super) fn pending_max_read_count(&self)->usize {self.destination.imports.len()}
    pub(super) fn pending_max_source_owners(&self)->Vec<usize> {self.destination.pending_source_owners()}

    /// Read the first Cap's still-open MAX inputs with their exact native
    /// parent and published owner/writer/wire/value binding intact. This does
    /// not publish the source MAX cells into an X assignment.
    pub(super) fn checked_max_imports(&self,plan:&WorkTreeHistoryPlan,prefix:&NativePrefix,
        snapshot:&Eligible08NativeSnapshot)->Result<Vec<(usize,Writer,Fr)>,String> {
        snapshot.require_native_parent(plan,prefix)?;
        snapshot.require_plan_parent(plan)?;
        let parent=snapshot.parent();
        self.require_binding(plan.descriptor().root,plan.work_profile().total_be28,
            prefix.profile(),&crate::bank53_map::CutDescriptor::eligible08().canonical_identity())?;
        if self.candidate.parent!=parent || self.destination.parent.as_ref()!=Some(&parent) {
            return Err("first Cap MAX import native parent".into());
        }
        self.checked_material()?;
        if self.candidate.imports.len()!=448 || self.destination.imports.len()!=448 {
            return Err("first Cap MAX import exact census".into());
        }
        let mut out=Vec::with_capacity(448);
        for (index,cell) in self.candidate.imports.iter().enumerate() {
            let context=index/224;
            let bit=index%224;
            let writer=Writer::Max{context,end:844_672};
            if context>=2 || cell.writer!=writer
                || cell.wire!=844_670*WIDTH+[999_424,1_000_097][context]+bit
                || (cell.value!=Fr::zero() && cell.value!=Fr::from(1u64))
                || self.destination.imports.get(&cell.wire)
                    !=Some(&(Author::Scheduled(writer),cell.value)) {
                return Err("first Cap MAX import owner/context/wire/value".into());
            }
            out.push((cell.wire,writer,cell.value));
        }
        Ok(out)
    }

    #[cfg(test)]
    pub(super) fn mutate_for_test(&mut self,kind:usize) {
        match kind {
            0=>self.root[0]^=1,
            1=>self.total[0]^=1,
            2=>self.profile[0]^=1,
            3=>self.cut=crate::bank53_map::CutDescriptor::diagnostic08().canonical_identity(),
            4=>self.candidate.owner-=1,
            5=>Arc::make_mut(&mut self.candidate.cells)[0].value+=Fr::from(1u64),
            6=>{Arc::make_mut(&mut self.candidate.cells).pop();},
            7=>{let cell=self.candidate.cells[0].clone();Arc::make_mut(&mut self.candidate.cells).push(cell);},
            8=>Arc::make_mut(&mut self.candidate.rows).iter_mut()
                .find(|row|row.author!=Author::Header).unwrap().term.gate.c0+=Fr::from(1u64),
            9=>{Arc::make_mut(&mut self.candidate.rows).pop();},
            10=>{let row=self.candidate.rows.last().unwrap().clone();Arc::make_mut(&mut self.candidate.rows).push(row);},
            11=>self.candidate.parent=self.candidate.parent.different_cut_for_test(),
            _=>panic!("unknown first Cap source mutation"),
        }
    }

    #[cfg(test)]
    pub(super) fn synthetic_for_test(plan:&WorkTreeHistoryPlan,snapshot:&Eligible08NativeSnapshot,
        first:&crate::h21_scheduled_max_cap::FirstModernCapLease)
        ->Result<Self,String> {
        Self::stage(plan,snapshot,&DaaHistoryRoster::compile(plan)?,first)
    }
}

/// A scheduled Cap publication for a descriptor-selected modern Score owner.
/// It carries the actual scheduled source and its unresolved MAX imports;
/// matching scalar q values alone cannot mint it.
pub(super) struct ScoredOwnerCapPublication {
    binding: crate::packed_owner_assembly::HeaderSourceBinding,
    candidate: Candidate,
    destination: Arc<Destination>,
}

/// Local Cap source plus typed foreign MAX obligations. HEADER rows are
/// retained separately from Cap rows, and no global X/ROW claim is made.
pub(super) struct ScoredOwnerCapMaterial {
    pub(super) rows: Vec<(Option<usize>, Term)>,
    pub(super) cells: Vec<(usize, usize, bool)>,
    pub(super) q: [Vec<(usize, bool)>; 2],
    pub(super) imports: Vec<(usize, Writer, bool)>,
    pub(super) active: [bool; 2],
}

/// Test-only borrow of the already compiled native producer roster. Preserve
/// Admission::new's native-parent check and the exact Cap stage below.
#[cfg(test)]
pub(super) fn scored_owner_cap_publication_from_native_roster(
    plan:&WorkTreeHistoryPlan,prefix:&NativePrefix,snapshot:&Eligible08NativeSnapshot,
    roster:&DaaHistoryRoster<'_>,owner:usize,
) -> Result<ScoredOwnerCapPublication,String> {
    snapshot.require_native_parent(plan,prefix)?;
    if !std::ptr::eq(roster.endpoint_parent(),plan) {
        return Err("C587 borrowed Cap roster has another parent".into());
    }
    ScoredOwnerCapPublication::stage(plan,snapshot,roster,owner)
}

impl ScoredOwnerCapPublication {
    fn stage(plan: &WorkTreeHistoryPlan, snapshot: &Eligible08NativeSnapshot,
        roster: &DaaHistoryRoster<'_>, owner: usize) -> Result<Self, String> {
        use crate::daa_history_roster::OwnerClass;
        snapshot.require_plan_parent(plan)?;
        if owner < 845_759 || roster.owner_class(owner as u64)? != OwnerClass::Carry {
            return Err("scored Cap publication owner/class".into());
        }
        let lease = snapshot.owner_lease(owner)?;
        let candidate = Candidate::stage(plan, snapshot, roster, &lease)?;
        let mut destination = Destination::default();
        candidate.clone().publish(&mut destination)?;
        let out = Self {
            binding: crate::packed_owner_assembly::HeaderSourceBinding::for_plan(plan, owner)?,
            candidate, destination: Arc::new(destination),
        };
        out.checked_material()?;
        Ok(out)
    }

    pub(super) fn binding(&self) -> &crate::packed_owner_assembly::HeaderSourceBinding {
        &self.binding
    }

    /// Replay every ordered source occurrence, then extract exactly the active
    /// Cap domains and MAX imports. Written zeroes are retained as cells.
    pub(super) fn checked_material(&self) -> Result<ScoredOwnerCapMaterial, String> {
        let owner = self.binding.owner();
        let candidate = &self.candidate;
        if candidate.owner != owner || !candidate.external_header_d.is_empty() {
            return Err("scored Cap publication owner/HEADER-D".into());
        }
        let mut replay = Destination::default();
        candidate.clone().publish(&mut replay)?;
        if replay != *self.destination {
            return Err("scored Cap publication exact source replay".into());
        }
        let mut active = [false; 2];
        let mut rows = Vec::with_capacity(candidate.rows.len());
        let mut row_counts = [0usize; 2];
        for row in candidate.rows.iter() {
            let context = match row.author {
                Author::Header => None,
                Author::Scheduled(Writer::Cap { context, origin })
                    if context < 2 && origin == owner + 1 => {
                        row_counts[context] += 1;
                        active[context] = true;
                        Some(context)
                    }
                _ => return Err("scored Cap publication ROW author".into()),
            };
            rows.push((context, row.term.clone()));
        }
        let mut by_context: [BTreeMap<usize, bool>; 2] = std::array::from_fn(|_| BTreeMap::new());
        for cell in candidate.cells.iter() {
            let context = match cell.writer {
                Writer::Cap { context, origin } if context < 2 && origin == owner + 1 => context,
                _ => return Err("scored Cap publication X author".into()),
            };
            let base = owner.checked_mul(WIDTH)
                .and_then(|base| base.checked_add([1_000_770, 1_002_818][context]))
                .ok_or("scored Cap publication X base overflow")?;
            let bit = cell.wire.checked_sub(base).filter(|bit| *bit < 2_048)
                .ok_or("scored Cap publication X coordinate")?;
            if cell.value != Fr::zero() && cell.value != Fr::from(1u64) {
                return Err("scored Cap publication nonboolean X".into());
            }
            if by_context[context].insert(bit, cell.value == Fr::from(1u64)).is_some() {
                return Err("scored Cap publication duplicate X, including zero".into());
            }
        }
        let mut cells = Vec::with_capacity(candidate.cells.len());
        let mut q: [Vec<(usize, bool)>; 2] = std::array::from_fn(|_| Vec::new());
        for context in 0..2 {
            if row_counts[context] != if active[context] { 6_419 } else { 0 }
                || by_context[context].len() != if active[context] { 2_048 } else { 0 }
            {
                return Err("scored Cap publication active ROW/X census".into());
            }
            let base = owner * WIDTH + [1_000_770, 1_002_818][context];
            for bit in 0..if active[context] { 2_048 } else { 0 } {
                let value = *by_context[context].get(&bit)
                    .ok_or("scored Cap publication missing written X zero")?;
                let wire = base + bit;
                cells.push((wire, context, value));
                if (740..805).contains(&bit) { q[context].push((wire, value)); }
            }
            if q[context].len() != if active[context] { 65 } else { 0 } {
                return Err("scored Cap publication q alias census".into());
            }
        }
        if !active.contains(&true)
            || candidate.retired != [0, 0, usize::from(active[0]) * 2_048,
                usize::from(active[1]) * 2_048]
            || candidate.cells.len() != cells.len()
        {
            return Err("scored Cap publication exact active retirement".into());
        }
        let mut imports = Vec::with_capacity(candidate.imports.len());
        let mut import_counts = [0usize; 2];
        for import in candidate.imports.iter() {
            let (context, end) = match import.writer {
                Writer::Max { context, end } if context < 2 => (context, end),
                _ => return Err("scored Cap publication MAX import author".into()),
            };
            let source_owner = end.checked_sub(2).ok_or("scored Cap MAX source underflow")?;
            let base = source_owner.checked_mul(WIDTH)
                .and_then(|base| base.checked_add([999_424, 1_000_097][context]))
                .ok_or("scored Cap MAX source overflow")?;
            let bit = import.wire.checked_sub(base).filter(|bit| *bit < 224)
                .ok_or("scored Cap MAX source coordinate")?;
            if !active[context] || bit != import_counts[context]
                || (import.value != Fr::zero() && import.value != Fr::from(1u64)) {
                return Err("scored Cap MAX exact ordered import".into());
            }
            import_counts[context] += 1;
            imports.push((import.wire, import.writer, import.value == Fr::from(1u64)));
        }
        if import_counts != [usize::from(active[0]) * 224, usize::from(active[1]) * 224] {
            return Err("scored Cap MAX exact import census".into());
        }
        Ok(ScoredOwnerCapMaterial { rows, cells, q, imports, active })
    }
}

#[derive(Clone)]
struct Candidate {
    parent:NativeParent, owner:usize,
    source_rows:Arc<Vec<Row>>,rows:Arc<Vec<Row>>,
    source_cells:Arc<Vec<Cell>>,cells:Arc<Vec<Cell>>,
    source_imports:Arc<Vec<Cell>>,imports:Arc<Vec<Cell>>,
    parent_mask:Arc<Vec<bool>>,replacement_mask:Vec<bool>,retired:[usize;4],
    external_header_d:BTreeMap<usize,(Author,Fr)>,
    source_external_header_d:Arc<BTreeMap<usize,(Author,Fr)>>,
}

fn scheduled_wire(wire:usize)->bool {(999424..1004866).contains(&(wire%WIDTH))}

impl Candidate {
    fn stage(plan:&WorkTreeHistoryPlan,snapshot:&Eligible08NativeSnapshot,roster:&DaaHistoryRoster<'_>,
        lease:&Eligible08OwnerLease)->Result<Self,String> {
        snapshot.require_plan_parent(plan)?;
        lease.check_exact(snapshot)?;
        let owner=lease.owner();
        let cells:Vec<_>=lease.cells().into_iter().map(|(wire,writer,value)|Cell{wire,writer,value}).collect();
        if cells.is_empty() {return Err("scheduled ledger inactive owner".into());}
        let header=Merge::new(roster,snapshot.scheduled_plan())?.header_terms(owner)?;
        let mut rows:Vec<_>=header.terms.into_iter().map(|term|Row{author:Author::Header,term}).collect();
        let mut source_cache:BTreeMap<usize,BTreeMap<usize,(Writer,Fr)>>=BTreeMap::new();
        source_cache.insert(owner,cells.iter().map(|c|(c.wire,(c.writer,c.value))).collect());
        let mut imports=BTreeMap::new();
        let mut external_reads=BTreeSet::new();
        lease.visit_rows(|writer,term| {
            let g=&term.gate;
            for (wire,live) in [(g.left,!g.c1.is_zero()||!g.c3.is_zero()),
                (g.right,!g.c2.is_zero()||!g.c3.is_zero())] {
                if !live {continue;}
                if !scheduled_wire(wire) {
                    if wire/WIDTH!=owner || !(987674..987898).contains(&(wire%WIDTH)) {
                        return Err("scheduled ledger unclassified external read".into());
                    }
                    external_reads.insert(wire);continue;
                }
                let source=wire/WIDTH;
                if !source_cache.contains_key(&source) {
                    let source_lease=snapshot.owner_lease(source)?;
                    source_lease.check_exact(snapshot)?;
                    source_cache.insert(source,source_lease.cells().into_iter()
                        .map(|(wire,writer,value)|(wire,(writer,value))).collect());
                }
                let &(author,value)=source_cache[&source].get(&wire)
                    .ok_or("scheduled ledger missing typed source cell")?;
                if source!=owner {imports.insert(wire,(author,value));}
            }
            rows.push(Row{author:Author::Scheduled(writer),term:term.clone()});Ok(())
        })?;
        let external_header_d=match lease.work_d() {
            Some(expected)=> {
                if expected.owner()!=owner || expected.height()!=owner+2
                    || expected.cells().iter().map(|(wire,_)|*wire).collect::<BTreeSet<_>>()!=external_reads {
                    return Err("scheduled ledger exact Work-D read census".into());
                }
                expected.cells().iter().map(|&(wire,value)|
                    (wire,(Author::NativeWorkD{height:expected.height()},value))).collect()
            }
            None if external_reads.is_empty()=>BTreeMap::new(),
            None=>return Err("scheduled ledger missing Work-D expectation".into()),
        };
        let imports:Vec<_>=imports.into_iter().map(|(wire,(writer,value))|Cell{wire,writer,value}).collect();
        let parent_mask=plan.physical_assignment_replacement_mask(owner as u64)?;
        let mut replacement_mask=parent_mask.clone();
        for cell in &cells {
            if cell.wire/WIDTH!=owner || replacement_mask[cell.wire%WIDTH] {
                return Err("scheduled ledger X parent transfer".into());
            }
            replacement_mask[cell.wire%WIDTH]=true;
        }
        let rows=Arc::new(rows);let cells=Arc::new(cells);let imports=Arc::new(imports);
        Ok(Self{parent:snapshot.parent(),owner,source_rows:rows.clone(),rows,
            source_cells:cells.clone(),cells,source_imports:imports.clone(),imports,
            parent_mask:Arc::new(parent_mask),replacement_mask,retired:header.retired,
            source_external_header_d:Arc::new(external_header_d.clone()),external_header_d})
    }

    fn publish(self,destination:&mut Destination)->Result<Joined,String> {
        if destination.parent.as_ref().is_some_and(|parent|*parent!=self.parent) {
            return Err("scheduled ledger destination parent".into());
        }
        let mut rows=BTreeMap::new();
        for row in self.rows.iter() {
            if row.term.row/ROWS!=self.owner {return Err("scheduled ledger ROW owner".into());}
            if rows.insert(row.term.row,row.author).is_some_and(|prior|prior!=row.author) {
                return Err("scheduled ledger ROW author collision".into());
            }
        }
        let mut cells=BTreeMap::new();let mut mask=(*self.parent_mask).clone();
        for cell in self.cells.iter() {
            if cell.wire/WIDTH!=self.owner || mask[cell.wire%WIDTH]
                || cells.insert(cell.wire,(Author::Scheduled(cell.writer),cell.value)).is_some() {
                return Err("scheduled ledger duplicate X/parent transfer".into());
            }
            mask[cell.wire%WIDTH]=true;
        }
        // Every coefficient, ordered occurrence, source value and typed import
        // must survive intact. Equal ROW ids from one writer are additive terms.
        if self.rows!=self.source_rows {return Err("scheduled ledger exact ROW source".into());}
        if self.cells!=self.source_cells {return Err("scheduled ledger exact X source".into());}
        if self.imports!=self.source_imports {return Err("scheduled ledger exact import source".into());}
        if self.external_header_d!=*self.source_external_header_d {
            return Err("scheduled ledger exact external HEADER D reads".into());
        }
        if mask!=self.replacement_mask {return Err("scheduled ledger exact transfer mask".into());}
        if rows.keys().any(|row|destination.rows.contains_key(row)) {
            return Err("scheduled ledger destination ROW overlap".into());
        }
        if cells.keys().any(|wire|destination.cells.contains_key(wire)) {
            return Err("scheduled ledger destination X overlap".into());
        }
        for (wire,claim) in &cells {
            if destination.imports.get(wire).is_some_and(|expected|expected!=claim) {
                return Err("scheduled ledger incoming source mismatch".into());
            }
        }
        for cell in self.imports.iter() {
            let expected=(Author::Scheduled(cell.writer),cell.value);
            if destination.cells.get(&cell.wire).is_some_and(|actual|*actual!=expected)
                || destination.imports.get(&cell.wire).is_some_and(|prior|*prior!=expected) {
                return Err("scheduled ledger published source mismatch".into());
            }
        }
        for (wire,expected) in &self.external_header_d {
            if destination.cells.get(wire).is_some_and(|actual|actual!=expected)
                || destination.external_header_d.get(wire).is_some_and(|prior|prior!=expected) {
                return Err("scheduled ledger published Work-D source mismatch".into());
            }
        }
        // No returned error follows this publication boundary.
        destination.parent=Some(self.parent);
        destination.rows.extend(rows);destination.cells.extend(cells);
        destination.imports.extend(self.imports.iter().map(|c|(c.wire,(Author::Scheduled(c.writer),c.value))));
        destination.external_header_d.extend(self.external_header_d.iter().map(|(wire,claim)|(*wire,*claim)));
        Ok(Joined{owner:self.owner,rows:self.rows,cells:self.cells,
            retired:self.retired,replacement_mask:self.replacement_mask,external_header_d:self.external_header_d})
    }
}

#[derive(Clone)]
struct DSourceCandidate {
    parent:NativeParent,owner:usize,height:usize,
    source:Arc<Vec<(usize,(Author,Fr))>>,claims:Arc<Vec<(usize,(Author,Fr))>>,
}
impl DSourceCandidate {
    fn stage(plan:&WorkTreeHistoryPlan,snapshot:&Eligible08NativeSnapshot,
        consumer:&Eligible08OwnerLease,source:&NativeWorkDLease)->Result<Self,String> {
        snapshot.require_plan_parent(plan)?;consumer.check_exact(snapshot)?;
        let owner=consumer.owner();
        let expected=consumer.work_d().ok_or("native Work-D source requires active scheduled MAX owner")?;
        let actual=source.checked_cells(&snapshot.parent(),owner)?;
        if expected.owner()!=owner || expected.height()!=owner+2 || actual!=expected.cells() {
            return Err("native Work-D source differs from Prepared D".into());
        }
        let mask=plan.physical_assignment_replacement_mask(owner as u64)?;
        if actual.len()!=224 || actual.iter().any(|(wire,_)|!mask[wire%WIDTH]) {
            return Err("native Work-D must remain parent-owned".into());
        }
        let claims:Arc<Vec<(usize,(Author,Fr))>>=Arc::new(actual.iter().map(|&(wire,value)|
            (wire,(Author::NativeWorkD{height:expected.height()},value))).collect());
        Ok(Self{parent:snapshot.parent(),owner,height:expected.height(),source:claims.clone(),claims})
    }
    fn publish(self,destination:&mut Destination)->Result<(),String> {
        if destination.parent.as_ref().is_some_and(|parent|*parent!=self.parent) {
            return Err("native Work-D destination parent".into());
        }
        if self.claims!=self.source {return Err("native Work-D exact source claims".into());}
        let mut staged=BTreeMap::new();
        for &(wire,(author,value)) in self.claims.iter() {
            if wire/WIDTH!=self.owner || !(987674..987898).contains(&(wire%WIDTH))
                || author!=(Author::NativeWorkD{height:self.height}) || self.height!=self.owner+2
                || (value!=Fr::zero() && value!=ark_ff::One::one()) {
                return Err("native Work-D exact author/domain/value".into());
            }
            if destination.cells.contains_key(&wire) || staged.insert(wire,(author,value)).is_some() {
                return Err("native Work-D duplicate X author".into());
            }
            if destination.external_header_d.get(&wire).is_some_and(|expected|*expected!=(author,value)) {
                return Err("native Work-D pending obligation mismatch".into());
            }
        }
        if staged.len()!=224 {return Err("native Work-D exact publication census".into());}
        // No HEADER ROWs or replacement-mask permissions change here.
        destination.parent=Some(self.parent);destination.cells.extend(staged);Ok(())
    }
}

/// Native production admission is inseparable from exact plan/prefix identity.
/// The plan-bound DAA roster is compiled once and reused for every owner.
pub(super) struct Admission<'a> {
    plan:&'a WorkTreeHistoryPlan,snapshot:&'a Eligible08NativeSnapshot,
    roster:DaaHistoryRoster<'a>,
}
impl<'a> Admission<'a> {
    pub(super) fn new(plan:&'a WorkTreeHistoryPlan,prefix:&NativePrefix,
        snapshot:&'a Eligible08NativeSnapshot)->Result<Self,String> {
        snapshot.require_native_parent(plan,prefix)?;
        Ok(Self{plan,snapshot,roster:DaaHistoryRoster::compile(plan)?})
    }
    pub(super) fn publish(&self,owner:usize,destination:&mut Destination)->Result<Joined,String> {
        let lease=self.snapshot.owner_lease(owner)?;
        Candidate::stage(self.plan,self.snapshot,&self.roster,&lease)?.publish(destination)
    }
    pub(super) fn first_modern_cap_publication(&self,prefix:&NativePrefix)
        ->Result<FirstModernCapPublication,String> {
        let first=self.snapshot.first_modern_cap_lease(self.plan,prefix)?;
        FirstModernCapPublication::stage(self.plan,self.snapshot,&self.roster,&first)
    }
    pub(super) fn scored_owner_cap_publication(&self, owner: usize)
        -> Result<ScoredOwnerCapPublication, String> {
        ScoredOwnerCapPublication::stage(self.plan, self.snapshot, &self.roster, owner)
    }
    pub(super) fn publish_native_work_d(&self,producer:&NativeOwnerProducer<'_>,owner:usize,
        destination:&mut Destination)->Result<(),String> {
        let source=producer.native_work_d_lease(owner)?;
        producer.require_work_d_lease(owner,&source)?;
        let consumer=self.snapshot.owner_lease(owner)?;
        DSourceCandidate::stage(self.plan,self.snapshot,&consumer,&source)?.publish(destination)
    }
}

#[cfg(test)]
#[path="h21_scheduled_family_ledger_tests.rs"]
mod tests;

#[cfg(test)]
#[path="h21_native_work_d_ledger_tests.rs"]
mod native_work_d_tests;

#[cfg(test)]
mod c390_scored_owner_tests {
    use super::*;

    #[test]
    fn c390_owner845887_scheduled_cap_source_is_sealed_and_two_context() {
        use blake2::{digest::consts::U32, Blake2b, Digest};
        let plan = WorkTreeHistoryPlan::compile(1_827_840, 21, [17; 32], [0; 28]).unwrap();
        let mut profile_bytes = crate::work_tree_fixed_hash::PROFILE_PREFIX.to_vec();
        profile_bytes.extend_from_slice(&crate::header_order::MAINNET_GENESIS);
        let profile = Blake2b::<U32>::digest(profile_bytes).into();
        let snapshot = Eligible08NativeSnapshot::constant_d_for_test(
            [17; 32], [0; 28], profile, 16).unwrap();
        let roster = DaaHistoryRoster::compile(&plan).unwrap();
        let source = ScoredOwnerCapPublication::stage(&plan, &snapshot, &roster, 845_887).unwrap();
        let material = source.checked_material().unwrap();
        assert_eq!(material.active, [true; 2]);
        assert_eq!(material.cells.len(), 4_096);
        assert_eq!(material.imports.len(), 448);
        assert_eq!(material.q[0].len(), 65);
        assert_eq!(material.q[1].len(), 65);
        assert!(material.imports.iter().all(|(wire, writer, _)|
            *wire / WIDTH == 844_798
                && matches!(writer, Writer::Max { end: 844_800, .. })));

        let mut changed = source;
        Arc::make_mut(&mut changed.candidate.cells)[0].value += Fr::from(1u64);
        assert!(changed.checked_material().is_err());
    }
}

//! Bounded production ROW/X admission for the first Eligible08 modern owner.
//! This object remains incomplete: no packed bytes, finish, or proof admission.
use super::*;
use std::sync::Arc;

const OWNER: usize = 845_759;
const ROWS: usize = 1 << 19;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Writer { Header, Map(usize), Score(usize), Cap(usize) }

#[derive(Clone, Debug, PartialEq, Eq)]
struct Row { writer: Writer, term: Term }

#[derive(Clone, Debug, PartialEq, Eq)]
struct Cell { writer: Writer, local: usize, value: bool }

/// The destination records ownership only. It cannot publish a packed row.
#[derive(Default, PartialEq, Eq)]
pub(crate) struct FirstModernDestination {
    rows: BTreeMap<usize, Writer>,
    cells: BTreeMap<usize, Writer>,
}

#[allow(dead_code)]
pub(super) struct Joined {
    rows: Vec<Row>,
    cells: Vec<Cell>,
    replacement_mask: Vec<bool>,
}

#[derive(Clone)]
struct Candidate {
    source_rows: Arc<Vec<Row>>,
    rows: Vec<Row>,
    source_cells: Arc<Vec<Cell>>,
    cells: Vec<Cell>,
    parent_mask: Arc<Vec<bool>>,
    replacement_mask: Vec<bool>,
}

fn bank53_read(term: &Term) -> bool {
    let active = |wire: usize| (BANK53_BASE..BANK53_BASE + 2 * BANK53_CONTEXT_BITS).contains(&(wire % WIDTH));
    ((!term.gate.c1.is_zero() || !term.gate.c3.is_zero()) && active(term.gate.left))
        || ((!term.gate.c2.is_zero() || !term.gate.c3.is_zero()) && active(term.gate.right))
}

fn check_header_read(term: &Term) -> Result<(), String> {
    if bank53_read(term) { return Err("first modern HEADER active Bank53 read".into()); }
    for start in [1_000_770, 1_002_818] {
        let active = |wire: usize| (start..start + 2048).contains(&(wire % WIDTH));
        if ((!term.gate.c1.is_zero() || !term.gate.c3.is_zero()) && active(term.gate.left))
            || ((!term.gate.c2.is_zero() || !term.gate.c3.is_zero()) && active(term.gate.right)) {
            return Err("first modern HEADER active Cap read".into());
        }
    }
    Ok(())
}

fn retire_header(owner: usize, source: impl IntoIterator<Item=Term>) -> Result<Vec<Row>, String> {
    let mut seen = [vec![false; 2048], vec![false; 2048]];
    let mut retained = Vec::new();
    for term in source {
        let local = term.row.checked_sub(owner * ROWS).filter(|row| *row < ROWS)
            .ok_or("first modern HEADER ROW owner")?;
        let anchor = [357_978, 360_026].iter().enumerate()
            .find_map(|(context, start)| (local >= *start && local < start + 2048)
                .then_some((context, local.saturating_sub(*start))));
        if let Some((context, bit)) = anchor {
            let expected = crate::gkr::Gate { left: owner * WIDTH + [1_000_770, 1_002_818][context] + bit,
                right: owner * WIDTH, c0: Fr::zero(), c1: Fr::one(), c2: Fr::zero(), c3: Fr::zero() };
            if term.gate != expected || seen[context][bit] {
                return Err("first modern HEADER Cap anchor identity/duplicate".into());
            }
            seen[context][bit] = true;
        } else {
            check_header_read(&term)?;
            retained.push(Row { writer: Writer::Header, term });
        }
    }
    if seen.iter().flatten().any(|present| !present) {
        return Err("first modern HEADER Cap anchor census".into());
    }
    Ok(retained)
}

impl Candidate {
    fn stage(plan: &WorkTreeHistoryPlan, profile: [u8;32], stage: &H21EligibleMapStage)
        -> Result<Self,String> {
        if stage.owner != OWNER || stage.class != crate::daa_history_roster::OwnerClass::Carry
            || plan.headers() != crate::bank53_map::BANK53_N || plan.slot_log() != 21
            || stage.parent_root != plan.descriptor().root
            || stage.parent_total != plan.work_profile().total_be28 || stage.parent_profile != profile
            || stage.cut_identity != H21EligibleMapStage::descriptor().canonical_identity()
            || stage.map_bindings.iter().enumerate().any(|(context,binding)|
                binding.n != H21EligibleMapStage::descriptor().terminals()[context] as u64
                    || binding.h != 21 || binding.parent_root.is_some()) {
            return Err("first modern ledger parent/cut/owner/context".into());
        }
        let parent_mask = plan.physical_assignment_replacement_mask(OWNER as u64)?;
        let mut replacement_mask = parent_mask.clone();
        let mut cells = Vec::new();
        for context in 0..2 {
            for (author,writer,domain) in [
                (H21StageAuthor::Map(context),Writer::Map(context),H21EligibleMapStage::map_live(context)?),
                (H21StageAuthor::ScoreModern(context),Writer::Score(context),H21EligibleMapStage::score_live(context)?),
                (H21StageAuthor::Cap(context),Writer::Cap(context),H21EligibleMapStage::cap_live(context)?)] {
                for local in domain {
                    let Some(&(actual,value)) = stage.claims.get(&local) else {
                        return Err("first modern missing semantic X author".into());
                    };
                    if actual != author || replacement_mask[local] {
                        return Err("first modern semantic X author/HEADER ownership".into());
                    }
                    replacement_mask[local] = true;
                    cells.push(Cell {writer,local,value});
                }
            }
        }
        if cells.len() != stage.claims.len() { return Err("first modern extra semantic X author".into()); }
        let mut header = Vec::new();
        plan.visit_slot_terms(OWNER as u64, |term| {header.push(term);Ok(())})?;
        let mut rows = retire_header(OWNER, header)?;
        for context in 0..2 {
            for (writer,terms) in [(Writer::Map(context),&stage.map_terms[context]),
                (Writer::Score(context),&stage.score_terms[context]),(Writer::Cap(context),&stage.cap_terms[context])] {
                if terms.is_empty() || (writer == Writer::Cap(context) && terms.len()!=6419) {
                    return Err("first modern semantic ROW source census".into());
                }
                rows.extend(terms.iter().cloned().map(|term|Row {writer,term}));
            }
        }
        Ok(Self {source_rows:Arc::new(rows.clone()),rows,
            source_cells:Arc::new(cells.clone()),cells,parent_mask:Arc::new(parent_mask),replacement_mask})
    }

    fn publish(self, destination: &mut FirstModernDestination) -> Result<Joined,String> {
        let mut row_owners = BTreeMap::new();
        for row in &self.rows {
            if row.term.row / ROWS != OWNER { return Err("first modern ROW extent".into()); }
            if row.writer == Writer::Header { check_header_read(&row.term)?; }
            if row_owners.insert(row.term.row,row.writer).is_some_and(|prior|prior!=row.writer) {
                return Err("first modern cross-writer ROW collision".into());
            }
        }
        let mut cell_owners = BTreeMap::new();
        let mut mask = (*self.parent_mask).clone();
        for cell in &self.cells {
            if cell.local >= WIDTH || mask[cell.local]
                || cell_owners.insert(OWNER*WIDTH+cell.local,cell.writer).is_some() {
                return Err("first modern duplicate X writer/parent lease".into());
            }
            mask[cell.local] = true;
        }
        // Ordered source equality preserves every coefficient, wire and term
        // multiplicity; no ROW or X deduplication can hide a missing author.
        if self.cells != *self.source_cells { return Err("first modern exact X source mismatch".into()); }
        if self.rows != *self.source_rows { return Err("first modern exact ROW source mismatch".into()); }
        if mask != self.replacement_mask { return Err("first modern exact transfer mask mismatch".into()); }
        if row_owners.keys().any(|row|destination.rows.contains_key(row)) {
            return Err("first modern destination ROW overlap".into());
        }
        if cell_owners.keys().any(|cell|destination.cells.contains_key(cell)) {
            return Err("first modern destination X overlap".into());
        }
        // No fallible operation follows the destination publication boundary.
        destination.rows.extend(row_owners);
        destination.cells.extend(cell_owners);
        Ok(Joined {rows:self.rows,cells:self.cells,replacement_mask:self.replacement_mask})
    }
}

pub(super) fn publish(plan:&WorkTreeHistoryPlan,profile:[u8;32],stage:&H21EligibleMapStage,
    destination:&mut FirstModernDestination)->Result<Joined,String> {
    Candidate::stage(plan,profile,stage)?.publish(destination)
}

#[cfg(test)]
pub(super) fn exercise_structural_negatives(plan:&WorkTreeHistoryPlan,profile:[u8;32],stage:&H21EligibleMapStage) {
    let candidate=Candidate::stage(plan,profile,stage).unwrap();
    let reject=|candidate:Candidate,expected:&str| {
        let mut destination=FirstModernDestination::default();
        destination.rows.insert(17,Writer::Header);
        destination.cells.insert(18,Writer::Header);
        let before_rows=destination.rows.clone();let before_cells=destination.cells.clone();
        let error=match candidate.publish(&mut destination) {Err(error)=>error,Ok(_)=>panic!("fault admitted")};
        assert_eq!(error,expected);
        assert_eq!(destination.rows,before_rows);
        assert_eq!(destination.cells,before_cells);
    };
    let mut destination=FirstModernDestination::default();
    let joined=candidate.clone().publish(&mut destination).unwrap();
    assert_eq!(joined.cells.len(),19706);
    assert_eq!(destination.cells.len(),19706);
    let parent=plan.physical_assignment_replacement_mask(OWNER as u64).unwrap();
    assert_eq!(parent.iter().zip(&joined.replacement_mask).filter(|(a,b)|a!=b).count(),19706);
    for context in 0..2 {
        for writer in [Writer::Map(context),Writer::Score(context),Writer::Cap(context)] {
            assert!(joined.rows.iter().any(|row|row.writer==writer));
            assert!(joined.cells.iter().any(|cell|cell.writer==writer));
        }
        assert_eq!(joined.rows.iter().filter(|row|row.writer==Writer::Cap(context)).count(),6419);
    }
    let rows_before=destination.rows.clone();let cells_before=destination.cells.clone();
    assert_eq!(candidate.clone().publish(&mut destination).err().unwrap(),"first modern destination ROW overlap");
    assert_eq!(destination.rows,rows_before);assert_eq!(destination.cells,cells_before);

    let mut duplicate=candidate.clone();
    let zero=duplicate.cells.iter().find(|cell|!cell.value).unwrap().clone();
    duplicate.cells.push(zero);
    reject(duplicate,"first modern duplicate X writer/parent lease");

    let mut bit=candidate.clone();
    bit.cells.iter_mut().find(|cell|cell.writer==Writer::Cap(1)).unwrap().value^=true;
    reject(bit,"first modern exact X source mismatch");
    let mut mask=candidate.clone();mask.replacement_mask[1_002_818]^=true;
    reject(mask,"first modern exact transfer mask mismatch");

    let mut wrong_d=candidate.clone();
    wrong_d.rows.iter_mut().find(|row|row.writer==Writer::Cap(0)
        && row.term.gate.left/WIDTH==844_670 && row.term.gate.c1==-Fr::one())
        .unwrap().term.gate.left+=1;
    reject(wrong_d,"first modern exact ROW source mismatch");
    let mut coefficient=candidate.clone();
    coefficient.rows.iter_mut().find(|row|row.writer==Writer::Score(1)).unwrap().term.gate.c0+=Fr::one();
    reject(coefficient,"first modern exact ROW source mismatch");

    for writer in [Writer::Score(0),Writer::Cap(1)] {
        let mut shared=candidate.clone();
        let target=shared.rows.iter().find(|row|row.writer==writer).unwrap().term.row;
        let mut header=shared.rows.iter().find(|row|row.writer==Writer::Header).unwrap().clone();
        header.term.row=target;shared.rows.push(header);
        reject(shared,"first modern cross-writer ROW collision");
    }
    let mut header=candidate.clone();
    let row=header.rows.iter_mut().find(|row|row.writer==Writer::Header).unwrap();
    row.term.gate=crate::gkr::Gate {left:OWNER*WIDTH+677_501,right:OWNER*WIDTH,
        c0:Fr::zero(),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()};
    reject(header,"first modern HEADER active Bank53 read");
    let mut foreign_header=candidate.clone();
    let row=foreign_header.rows.iter_mut().find(|row|row.writer==Writer::Header).unwrap();
    row.term.gate=crate::gkr::Gate {left:844_670*WIDTH+677_501,right:OWNER*WIDTH,
        c0:Fr::zero(),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()};
    reject(foreign_header,"first modern HEADER active Bank53 read");
    // The exact inactive-Score owner counterexample is independent of the
    // owner845759 publication whitelist and fails before anchor census.
    let inactive=844_670;
    let term=Term {row:inactive*ROWS+1,gate:crate::gkr::Gate {
        left:inactive*WIDTH+677_501,right:inactive*WIDTH,c0:Fr::zero(),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()}};
    assert_eq!(retire_header(inactive,[term]).unwrap_err(),"first modern HEADER active Bank53 read");
    let anchor=Term {row:OWNER*ROWS+357_978,gate:crate::gkr::Gate {
        left:OWNER*WIDTH+1_000_770,right:OWNER*WIDTH,c0:Fr::zero(),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()}};
    assert_eq!(retire_header(OWNER,[anchor.clone(),anchor.clone()]).unwrap_err(),
        "first modern HEADER Cap anchor identity/duplicate");
    let mut bad_anchor=anchor;bad_anchor.gate.c0=Fr::one();
    assert_eq!(retire_header(OWNER,[bad_anchor]).unwrap_err(),"first modern HEADER Cap anchor identity/duplicate");
    assert_eq!(retire_header(OWNER,[]).unwrap_err(),"first modern HEADER Cap anchor census");

    for fault in 0..5 {
        let mut wrong=stage.clone();
        match fault {
            0=>wrong.cut_identity=crate::bank53_map::CutDescriptor::diagnostic08().canonical_identity(),
            1=>wrong.parent_root[0]^=1,
            2=>wrong.parent_total[0]^=1,
            3=>wrong.parent_profile[0]^=1,
            4=>wrong.map_bindings.swap(0,1),
            _=>unreachable!(),
        }
        assert_eq!(Candidate::stage(plan,profile,&wrong).err().unwrap(),"first modern ledger parent/cut/owner/context");
    }
    let mut wrong=stage.clone();wrong.owner=844_670;
    assert_eq!(Candidate::stage(plan,profile,&wrong).err().unwrap(),"first modern ledger parent/cut/owner/context");

    let mut overlap=FirstModernDestination::default();
    overlap.cells.insert(OWNER*WIDTH+candidate.cells[0].local,Writer::Header);
    let before=overlap.cells.clone();
    assert_eq!(candidate.publish(&mut overlap).err().unwrap(),"first modern destination X overlap");
    assert!(overlap.rows.is_empty());assert_eq!(overlap.cells,before);
}

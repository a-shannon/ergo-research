//! Public calendar inverse of the canonical H21 structural term stream.
//! Endpoint addresses include dummy operands regardless of coefficient values.
//! No witness, source provenance, GKR admission or history result enters here.
use super::*;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct EndpointCensus {
    pub(crate) family_destinations: [usize; 11],
    pub(crate) family_terms: [usize; 11],
    pub(crate) terms: usize,
}
impl EndpointCensus {
    pub(crate) fn destinations_visited(&self) -> usize { self.family_destinations.iter().sum() }
}

fn families() -> [Family; 11] {
    [Family::Header,Family::Max(0),Family::Max(1),Family::Cap(0),Family::Cap(1),
        Family::Map(0),Family::Map(1),Family::Score(0),Family::Score(1),Family::Slack(0),Family::Slack(1)]
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum DestinationSet { Owners(Vec<usize>), All }
impl DestinationSet {
    fn contains(&self, owner: usize) -> bool {
        owner < SLOTS && match self { Self::All => true, Self::Owners(v) => v.binary_search(&owner).is_ok() }
    }
    fn len(&self) -> usize { match self { Self::All => SLOTS, Self::Owners(v) => v.len() } }
}
fn push_owner(owners: &mut Vec<usize>, owner: usize) {
    if owner < SLOTS { owners.push(owner); }
}
fn plus(a: usize, b: usize) -> Result<usize,String> { a.checked_add(b).ok_or("H21 endpoint calendar addition overflow".into()) }
fn minus(a: usize, b: usize) -> Result<usize,String> { a.checked_sub(b).ok_or("H21 endpoint calendar subtraction overflow".into()) }

// This generates only a small inverse calendar. It never enumerates all
// owners to find a nonzero source. All is reserved for physical right wire0
// in Score/Slack, whose actual output cardinality spans every destination.
fn candidate_destinations(scheduled: &Scheduled, maps: &[Map;2], family: Family,
    left: bool, source_owner: usize) -> Result<DestinationSet,String> {
    let cut = CutDescriptor::eligible08();
    if usize::BITS != 64 || source_owner >= SLOTS || scheduled.descriptor() != cut
        || maps.iter().enumerate().any(|(c,m)| m.h()!=21 || m.n()!=cut.terminals()[c] as u64 || m.slots()!=SLOTS as u64) {
        return Err("H21 endpoint fixed public geometry".into());
    }
    let context = match family { Family::Header => None,
        Family::Max(c)|Family::Cap(c)|Family::Map(c)|Family::Score(c)|Family::Slack(c) => {
            if c>=2 { return Err("H21 endpoint family context".into()); } Some(c)
        } };
    if !left && source_owner==0 && matches!(family,Family::Score(_)|Family::Slack(_)) {
        return Ok(DestinationSet::All);
    }
    if !left && matches!(family,Family::Slack(_)) {
        return Ok(DestinationSet::Owners(Vec::new()));
    }
    let mut owners = vec![source_owner];
    if left {
        match family {
            Family::Header|Family::Slack(_) => {},
            Family::Max(c)|Family::Cap(c) => {
                let (max_active,_) = scheduled.owner_activity(source_owner)?;
                if max_active[c] {
                    let first = minus(cut.modern_start(),cut.offset())?;
                    let first_owner = minus(first,2)?;
                    let terminal = cut.terminals()[c];
                    let regular_end = plus(first,minus(terminal,first)?/128*128)?;
                    if matches!(family,Family::Max(_)) {
                        if source_owner==minus(terminal,2)? && terminal!=regular_end {
                            push_owner(&mut owners,minus(regular_end,2)?);
                        } else if source_owner>first_owner {
                            push_owner(&mut owners,minus(source_owner,128)?);
                        }
                    } else {
                        let guard = cut.guards()[c];
                        let ordinary = plus(plus(source_owner,cut.offset())?,1)?;
                        if ordinary < guard { push_owner(&mut owners,ordinary); }
                        let q = minus(minus(guard,cut.offset())?,first)?;
                        let epochs = plus(q,127)?/128;
                        let clip_end = plus(first,epochs.checked_mul(128).ok_or("H21 clipped Cap epoch overflow")?)?.min(terminal);
                        if source_owner==minus(clip_end,2)? { push_owner(&mut owners,minus(guard,1)?); }
                    }
                }
            },
            Family::Map(c) => {
                let q = source_owner/1024; let low = source_owner%1024;
                let distances: &[usize] = match low { 958=>&[0],1022=>&[1,2,3,4,5,6,7],1023=>&[1,2,3,4,5,6,7,8],_=>&[] };
                for &d in distances {
                    let destination = plus(plus(q,d)?.checked_mul(1024).ok_or("H21 Map endpoint quotient overflow")?,959)?;
                    if destination<SLOTS && maps[c].tier(destination as u64)?.is_some_and(|ell|ell>0) {
                        push_owner(&mut owners,destination);
                    }
                }
            },
            Family::Score(c) => {
                // WorkUpper(o-1), regular previous R(o-128), and the finite
                // anchor/first/clipped exceptions. Exact canonical filtering
                // below removes inactive candidates without changing phases.
                push_owner(&mut owners,plus(source_owner,1)?);
                push_owner(&mut owners,plus(source_owner,128)?);
                if source_owner==ANCHOR_OWNERS[0] {
                    for owner in ANCHOR_OWNERS { push_owner(&mut owners,owner); }
                }
                if source_owner==ANCHOR_OWNERS[1] { push_owner(&mut owners,FIRST_MODERN_OWNER); }
                let clipped = minus(cut.guards()[c],1)?;
                let first = minus(plus(cut.modern_start(),128)?,1)?;
                let previous = plus(first,minus(clipped,first)?/128*128)?;
                if source_owner==previous { push_owner(&mut owners,clipped); }
            },
        }
    }
    let _ = context;
    owners.sort_unstable(); owners.dedup();
    Ok(DestinationSet::Owners(owners))
}

impl H21StructuralRoster<'_> {
    /// Exact inverse by physical input owner. Family terms are emitted by
    /// their canonical producers, then filtered on the actual operand address.
    pub(crate) fn visit_endpoint(&self, left: bool, source_owner: usize,
        sink: impl FnMut(Family,Term)->Result<(),String>) -> Result<EndpointCensus,String> {
        self.visit_endpoint_selected(left,source_owner,None,sink)
    }

    // An internal oracle restriction intersects the SAME inverse calendars.
    // The public endpoint visitor always selects None; this cannot qualify a
    // partial proof or bypass an admission. It avoids whole-global traversals
    // in bounded literal differentials.
    fn visit_endpoint_selected(&self, left: bool, source_owner: usize, destinations: Option<&[usize]>,
        sink: impl FnMut(Family,Term)->Result<(),String>) -> Result<EndpointCensus,String> {
        self.visit_endpoint_families(left,source_owner,destinations,false,false,sink)
    }

    /// Physical complement of the four Score/Slack families at absolute right
    /// wire zero. Left endpoints and nonzero right owners use the full source.
    pub(crate) fn visit_role1_physical_endpoint(&self, left: bool, source_owner: usize,
        sink: impl FnMut(Family,Term)->Result<(),String>) -> Result<EndpointCensus,String> {
        if !left && source_owner == 0 {
            self.visit_endpoint_families(false,0,None,true,false,sink)
        } else {
            self.visit_endpoint(left,source_owner,sink)
        }
    }

    pub(crate) fn role1_complement(&self,left:bool,owner:usize,
        sink:impl FnMut(Family,Term)->Result<(),String>)->Result<EndpointCensus,String> {
        self.visit_endpoint_families(left,owner,None,!left && owner==0,true,sink)
    }

    /// The HEADER emitter is owner-local. Only A4 and the four scheduled
    /// zero-anchor groups are conditionally removed after the common retirement.
    pub(crate) fn header_omissions(&self,owner:usize)->Result<[bool;6],String> {
        use crate::daa_history_roster::OwnerClass;
        let a4=matches!(self.daa.owner_class(owner as u64)?,OwnerClass::Mature(_)|OwnerClass::Short(_));
        let (max,cap)=self.scheduled.owner_activity(owner)?;
        Ok([false,a4,max[0],max[1],cap[0],cap[1]])
    }
    pub(crate) fn full_header_template(&self,mut sink:impl FnMut(Term)->Result<(),String>)->Result<(),String>{
        const OWNER:usize=2;
        if self.header_omissions(OWNER)? != [false;6]{return Err("HEADER template has conditional omissions".into());}
        self.emit_endpoint_family_owner(Family::Header,OWNER,|mut term|{
            if term.row/ROWS!=OWNER || term.gate.left/WIDTH!=OWNER || term.gate.right/WIDTH!=OWNER{
                return Err("non-local canonical HEADER term".into());
            }
            term.row%=ROWS;term.gate.left%=WIDTH;term.gate.right%=WIDTH;
            sink(term)
        })
    }

    pub(crate) fn score_slack_right_zero_d(&self, r: &[Fr], u: &[Fr], left_value: Fr)
        -> Result<Fr,String> {
        score_slack_right_zero_d(&self.maps,r,u,left_value)
    }

    fn visit_endpoint_families(&self, left: bool, source_owner: usize, destinations: Option<&[usize]>,
        contract_right_zero: bool, omit_header:bool,
        mut sink: impl FnMut(Family,Term)->Result<(),String>) -> Result<EndpointCensus,String> {
        if self.parent.headers()!=N as u64 || self.parent.slot_log()!=21 || self.parent.slots()!=SLOTS {
            return Err("H21 endpoint parent geometry".into());
        }
        if let Some(owners)=destinations {
            if owners.iter().any(|o|*o>=SLOTS) || owners.windows(2).any(|p|p[0]>=p[1]) {
                return Err("H21 endpoint destination restriction order/range".into());
            }
        }
        let input_bound = WIDTH.checked_mul(SLOTS).ok_or("H21 endpoint input geometry overflow")?;
        let mut census = EndpointCensus::default();
        for (index,family) in families().into_iter().enumerate() {
            if omit_header && family==Family::Header {continue;}
            if contract_right_zero && !left && source_owner == 0 && matches!(family,Family::Score(_) | Family::Slack(_)) {
                continue;
            }
            let candidates = candidate_destinations(&self.scheduled,&self.maps,family,left,source_owner)?;
            let mut visit = |owner| -> Result<(),String> {
                census.family_destinations[index] = census.family_destinations[index].checked_add(1)
                    .ok_or("H21 endpoint destination census overflow")?;
                self.emit_endpoint_family_owner(family,owner,|term| {
                    if term.row/ROWS!=owner || term.gate.left>=input_bound || term.gate.right>=input_bound {
                        return Err("H21 endpoint canonical term geometry".into());
                    }
                    let endpoint = if left {term.gate.left}else{term.gate.right};
                    if endpoint/WIDTH==source_owner {
                        sink(family,term)?;
                        census.family_terms[index] = census.family_terms[index].checked_add(1)
                            .ok_or("H21 endpoint family term census overflow")?;
                        census.terms = census.terms.checked_add(1).ok_or("H21 endpoint term census overflow")?;
                    }
                    Ok(())
                })
            };
            if let Some(owners)=destinations {
                for &owner in owners { if candidates.contains(owner) { visit(owner)?; } }
            } else {
                match candidates { DestinationSet::All => {for owner in 0..SLOTS {visit(owner)?;}},
                    DestinationSet::Owners(owners) => {for owner in owners {visit(owner)?;}} }
            }
        }
        Ok(census)
    }

    /// Code-owned projected-test source, not a full role or source authority.
    /// Both inverse partitions must reproduce the same two physical terms.
    pub(crate) fn upper_score_edge_fixture(&self)->Result<[Term;2],String> {
        let owner=1_810_841usize;let bit=17usize;
        let row=owner*ROWS+W_ALIAS_ROW[1]+bit;
        let mut right=Vec::new();
        self.visit_endpoint_selected(false,0,Some(&[owner]),|family,term| {
            if family==Family::Score(1) && term.row==row {right.push(term);}Ok(())
        })?;
        let expected=[
            Term {row,gate:Gate {left:owner*WIDTH+SCORE_X[1]+bit,right:0,
                c0:Fr::zero(),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()}},
            Term {row,gate:Gate {left:(owner-1)*WIDTH+UPPER_LOCAL+bit,right:0,
                c0:Fr::zero(),c1:-Fr::one(),c2:Fr::zero(),c3:Fr::zero()}},
        ];
        if right.as_slice()!=expected {return Err("H21 scoped Upper/Score physical fixture changed".into());}
        for (source,index) in [(owner,0),(owner-1,1)] {
            let mut left=Vec::new();
            self.visit_endpoint_selected(true,source,Some(&[owner]),|family,term| {
                if family==Family::Score(1) && term.row==row {left.push(term);}Ok(())
            })?;
            if left.as_slice()!=[expected[index].clone()] {
                return Err("H21 scoped Upper/Score inverse partition changed".into());
            }
        }
        right.try_into().map_err(|_|"H21 scoped Upper/Score fixture arity".into())
    }

    fn emit_endpoint_family_owner(&self, family: Family, owner: usize,
        mut sink: impl FnMut(Term)->Result<(),String>) -> Result<(),String> {
        let base = owner.checked_mul(ROWS).ok_or("H21 endpoint row base overflow")?;
        match family {
            Family::Header => {
                for mut term in Merge::new(&self.daa,&self.scheduled)?.header_terms(owner)?.terms {
                    let local=term.row.checked_sub(base).ok_or("H21 endpoint HEADER row owner")?;
                    term.row=base.checked_add(place_header_row(local)?).ok_or("H21 endpoint HEADER row overflow")?;
                    sink(term)?;
                }
            },
            Family::Max(c)|Family::Cap(c) => {
                self.scheduled.visit_owner(owner,|writer,term| {
                    let actual=match writer {Writer::Max {context,..}=>Family::Max(context),
                        Writer::Cap {context,..}=>Family::Cap(context)};
                    if actual==family {sink(term)}else{Ok(())}
                })?;
                let _=c;
            },
            Family::Map(c) => {
                let old=plus(plus(base,409_600)?,c*32_768)?;
                for mut term in bank53_map::map_owner_terms_for_descriptor(&self.maps[c],owner as u64,c,CutDescriptor::eligible08())? {
                    let local=term.row.checked_sub(old).filter(|q|*q<10_347).ok_or("H21 endpoint Map placement")?;
                    term.row=plus(plus(base,MAP_ROW[c])?,local)?; sink(term)?;
                }
            },
            Family::Score(c) => self.visit_score_owner(owner,c,sink)?,
            Family::Slack(c) => {
                let old=plus(plus(plus(base,409_600)?,c*32_768)?,bank53_slack::SLACK_ROW_OFFSET)?;
                for mut term in bank53_slack::slack_zero_terms(owner,c)? {
                    let local=term.row.checked_sub(old).filter(|q|*q<387).ok_or("H21 endpoint Slack placement")?;
                    term.row=plus(plus(base,SLACK_ROW[c])?,local)?; sink(term)?;
                }
            },
        }
        Ok(())
    }
}

#[path="h21_endpoint_inverse_tests.rs"]
mod tests;

/// Coordinate zero in the 41-dimensional Boolean basis selects only terms
/// whose complete right address is zero. All terminal-score bits address a
/// positive wire at their guard. The two anchor constants remain in K0.
fn score_slack_right_zero_d(maps: &[Map;2], r: &[Fr], u: &[Fr], left_value: Fr)
    -> Result<Fr,String> {
    let v = [Fr::zero();41];
    dimensions(r,u,&v)?;
    let mut k = [Fr::zero();4];
    let owner = wiring::evaluate_shift(&r[19..],&u[20..],&v[20..],
        0,0,SLOTS as u64,0,RightIndex::GlobalZero)?;
    for (context,map) in maps.iter().enumerate() {
        add(&mut k,score_coefficients(context,map,r,u,&v)?);
        for bit in 0..bank53_slack::SLACK_ZERO_COUNT {
            k[1] += owner * eq(&r[..19],SLACK_ROW[context]+bit)
                * eq(&u[..20],671_744+context*8192+bank53_slack::SLACK_INPUT_START+bit);
        }
    }
    if !k[2].is_zero() || !k[3].is_zero() {
        return Err("H21 Score/Slack absolute right zero acquired a right-input coefficient".into());
    }
    Ok(k[0]+k[1]*left_value)
}

#[path="full_structural_terminal_tests.rs"]
mod full_structural_terminal_tests;

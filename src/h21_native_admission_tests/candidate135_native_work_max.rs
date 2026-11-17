//! No-frame structural preflight for the Carry owner 844670 MAX join.
//! The constant D stream is conditional fixture data, not native provenance.

use std::collections::{BTreeMap, BTreeSet};

use ark_bn254::Fr;
use ark_ff::{One, Zero};
use num_bigint::BigUint;

use crate::{
    h21_scheduled_max_cap::{Counts, OwnerCells, Plan, Prepared, Writer},
    sparse::Term,
};

const OWNER: usize = 844_670;
const NEXT_OWNER: usize = 844_798;
const EPOCH_END: usize = 844_672;
const NEXT_END: usize = 844_800;
const MAX_BASE: [usize; 2] = [999_424, 1_000_097];
const MAX_ROWS: [usize; 2] = [356_632, 357_305];
const MAX_LOCAL_BITS: usize = 673;
const MAX_TERMS_PER_CONTEXT: usize = 2_690;
const MAX_EXTRA_ROWS: [usize; 2] = [475_136, 475_585];
const OWNER_BITS: usize = 1 << 20;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Identity {
    owner: usize,
    context: usize,
    end: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct MaxBatch {
    identity: Identity,
    terms: Vec<Term>,
    writes: Vec<(Identity, usize, Fr)>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ReadImport {
    identity: Identity,
    cells: Vec<(usize, Fr)>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Candidate {
    owner: usize,
    batches: Vec<MaxBatch>,
    imports: Vec<ReadImport>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Destination {
    published: bool,
    cells: BTreeMap<usize, Fr>,
    rows: BTreeMap<usize, Identity>,
}

fn x(owner: usize, local: usize) -> usize {
    owner * OWNER_BITS + local
}

fn row(owner: usize, local: usize) -> usize {
    owner * (1 << 19) + local
}

fn build_candidate() -> Candidate {
    let plan = Plan::new();
    let mut terms: BTreeMap<Identity, Vec<Term>> = BTreeMap::new();
    let counts = plan
        .visit_owner(OWNER, |writer, term| {
            let identity = match writer {
                Writer::Max { context, end } => Identity {
                    owner: OWNER,
                    context,
                    end,
                },
                Writer::Cap { .. } => return Err("unexpected scheduled Cap writer".into()),
            };
            terms.entry(identity).or_default().push(term);
            Ok(())
        })
        .expect("source-owned MAX term census");
    assert_eq!(
        counts,
        Counts {
            max: [MAX_TERMS_PER_CONTEXT; 2],
            cap: [0; 2]
        }
    );

    // This conditional fixture exercises the complete Prepared input contract.
    let prepared =
        Prepared::from_d_iter((844_672..=1_827_840).map(|height| (height, BigUint::from(1u8))))
            .expect("conditional complete D fixture");

    let mut batches = Vec::with_capacity(2);
    for context in 0..2 {
        let identity = Identity {
            owner: OWNER,
            context,
            end: EPOCH_END,
        };
        let context_terms = terms.remove(&identity).expect("planned MAX context");
        let mut cells = OwnerCells::new(OWNER).expect("local owner cells");
        prepared
            .owner_patch(OWNER)
            .expect("local owner MAX patch")
            .apply(&mut cells)
            .expect("local MAX patch applies");
        let writes = (0..MAX_LOCAL_BITS)
            .map(|local| {
                (
                    identity,
                    MAX_BASE[context] + local,
                    cells
                        .read(MAX_BASE[context] + local)
                        .expect("all local MAX bits"),
                )
            })
            .collect();
        batches.push(MaxBatch {
            identity,
            terms: context_terms,
            writes,
        });
    }
    assert!(
        terms.is_empty(),
        "no other writer or context is in the candidate"
    );

    let mut imports = Vec::with_capacity(2);
    for context in 0..2 {
        let identity = Identity {
            owner: NEXT_OWNER,
            context,
            end: NEXT_END,
        };
        let mut cells = OwnerCells::new(NEXT_OWNER).expect("foreign owner cells");
        prepared
            .owner_patch(NEXT_OWNER)
            .expect("foreign owner MAX patch")
            .apply(&mut cells)
            .expect("foreign MAX patch applies");
        let imported = (0..224)
            .map(|bit| {
                let local = MAX_BASE[context] + bit;
                (
                    x(NEXT_OWNER, local),
                    cells.read(local).expect("foreign R bit"),
                )
            })
            .collect();
        imports.push(ReadImport {
            identity,
            cells: imported,
        });
    }

    Candidate {
        owner: OWNER,
        batches,
        imports,
    }
}

fn validate(
    candidate: &Candidate,
) -> Result<(BTreeMap<usize, Identity>, BTreeMap<usize, Fr>), String> {
    if candidate.owner != OWNER || candidate.batches.len() != 2 || candidate.imports.len() != 2 {
        return Err("candidate owner/context cardinality".into());
    }
    let mut rows = BTreeMap::new();
    let mut cells = BTreeMap::new();
    for context in 0..2 {
        let identity = Identity {
            owner: OWNER,
            context,
            end: EPOCH_END,
        };
        let batch = candidate
            .batches
            .get(context)
            .ok_or("missing MAX context")?;
        if batch.identity != identity
            || batch.terms.len() != MAX_TERMS_PER_CONTEXT
            || batch.writes.len() != MAX_LOCAL_BITS
        {
            return Err("MAX writer identity or census".into());
        }
        for term in &batch.terms {
            if term.row / (1 << 19) != OWNER {
                return Err("MAX term ROW owner".into());
            }
            let local_row = term.row % (1 << 19);
            let in_max_rows =
                (MAX_ROWS[context]..MAX_ROWS[context] + MAX_LOCAL_BITS).contains(&local_row);
            let in_extra_rows =
                (MAX_EXTRA_ROWS[context]..MAX_EXTRA_ROWS[context] + 449).contains(&local_row);
            if !in_max_rows && !in_extra_rows {
                return Err("MAX term ROW domain".into());
            }
            if rows
                .insert(term.row, identity)
                .is_some_and(|prior| prior != identity)
            {
                return Err("ROW writer collision".into());
            }
        }
        for (writer, local, value) in &batch.writes {
            if *writer != identity
                || !(MAX_BASE[context]..MAX_BASE[context] + MAX_LOCAL_BITS).contains(local)
                || (*value != Fr::zero() && *value != Fr::one())
                || cells.insert(x(OWNER, *local), *value).is_some()
            {
                return Err("MAX write identity, domain, or duplicate".into());
            }
        }
    }

    let mut imported_addresses = BTreeSet::new();
    for context in 0..2 {
        let identity = Identity {
            owner: NEXT_OWNER,
            context,
            end: NEXT_END,
        };
        let import = candidate.imports.get(context).ok_or("missing R import")?;
        if import.identity != identity || import.cells.len() != 224 {
            return Err("foreign R context/end identity or census".into());
        }
        for (address, value) in &import.cells {
            let local = *address % OWNER_BITS;
            if *address / OWNER_BITS != NEXT_OWNER
                || !(MAX_BASE[context]..MAX_BASE[context] + 224).contains(&local)
                || (*value != Fr::zero() && *value != Fr::one())
                || !imported_addresses.insert(*address)
            {
                return Err("foreign R import domain or duplicate".into());
            }
        }
    }
    if imported_addresses.len() != 448 {
        return Err("foreign R import census".into());
    }

    // Each foreign read must be the next-R input to one local MAX equation.
    for context in 0..2 {
        let batch = &candidate.batches[context];
        let used: BTreeSet<_> = batch
            .terms
            .iter()
            .filter_map(|term| {
                let address = term.gate.left;
                (address / OWNER_BITS == NEXT_OWNER).then_some(address)
            })
            .collect();
        let expected: BTreeSet<_> = (0..224)
            .map(|bit| x(NEXT_OWNER, MAX_BASE[context] + bit))
            .collect();
        if used != expected {
            return Err("MAX next-R read set".into());
        }
    }

    Ok((rows, cells))
}

impl Destination {
    fn publish(&mut self, candidate: &Candidate, expected: &Candidate) -> Result<(), String> {
        if self.published {
            return Err("duplicate c135 publication".into());
        }
        let (rows, cells) = validate(candidate)?;
        // The expected candidate is the private source-derived stage. This
        // equality guards against post-stage changes, not native provenance.
        if candidate != expected {
            return Err("source-owned MAX candidate mismatch".into());
        }
        if rows.keys().any(|row| self.rows.contains_key(row)) {
            return Err("destination ROW collision".into());
        }
        if cells.keys().any(|cell| self.cells.contains_key(cell)) {
            return Err("destination X collision".into());
        }
        self.rows.extend(rows);
        self.cells.extend(cells);
        self.published = true;
        Ok(())
    }
}

#[test]
fn c135_carry_max_two_context_no_frame_preflight_and_atomic_mutants() {
    let candidate = build_candidate();
    let (rows, writes) = validate(&candidate).expect("valid scoped candidate");
    assert_eq!(
        candidate.batches.len(),
        2,
        "MAX only; Cap and Score excluded"
    );
    assert_eq!(
        candidate
            .batches
            .iter()
            .map(|b| b.terms.len())
            .collect::<Vec<_>>(),
        vec![MAX_TERMS_PER_CONTEXT; 2]
    );
    assert_eq!(
        candidate
            .batches
            .iter()
            .map(|b| b.writes.len())
            .collect::<Vec<_>>(),
        vec![673; 2]
    );
    assert_eq!(
        candidate
            .imports
            .iter()
            .map(|i| i.cells.len())
            .collect::<Vec<_>>(),
        vec![224; 2]
    );
    assert_eq!(rows.len(), 2_244);
    assert_eq!(writes.len(), 1_346);
    assert_eq!(
        candidate
            .imports
            .iter()
            .map(|i| i.cells.len())
            .sum::<usize>(),
        448
    );
    for context in 0..2 {
        let values: Vec<_> = candidate.batches[context]
            .writes
            .iter()
            .map(|(_, _, value)| *value)
            .collect();
        assert_eq!(values[0], Fr::one(), "R[0]");
        assert_eq!(values[224], Fr::one(), "T[0]");
        assert!(values[448..672].iter().all(Zero::is_zero), "delta bits");
        assert_eq!(values[672], Fr::zero(), "less flag");
        assert_eq!(candidate.batches[context].identity.context, context);
        assert_eq!(candidate.batches[context].identity.end, EPOCH_END);
        assert_eq!(candidate.imports[context].identity.owner, NEXT_OWNER);
        assert_eq!(candidate.imports[context].identity.context, context);
        assert_eq!(candidate.imports[context].identity.end, NEXT_END);
    }

    let mut destination = Destination::default();
    destination.cells.insert(7, Fr::from(9u64));
    destination.rows.insert(
        8,
        Identity {
            owner: 8,
            context: 0,
            end: 10,
        },
    );
    let before = destination.clone();

    let mut omitted = candidate.clone();
    omitted.batches[0].writes.pop();
    assert!(destination.publish(&omitted, &candidate).is_err());
    assert_eq!(destination, before, "omission leaves destination unchanged");

    let mut duplicate = candidate.clone();
    let repeated_write = duplicate.batches[0].writes[0];
    duplicate.batches[0].writes[1] = repeated_write;
    assert_eq!(
        destination.publish(&duplicate, &candidate),
        Err("MAX write identity, domain, or duplicate".into())
    );
    assert_eq!(
        destination, before,
        "duplicate leaves destination unchanged"
    );

    let mut wrong_owner = candidate.clone();
    wrong_owner.owner += 1;
    assert!(destination.publish(&wrong_owner, &candidate).is_err());
    assert_eq!(
        destination, before,
        "wrong owner leaves destination unchanged"
    );

    let mut wrong_context = candidate.clone();
    wrong_context.batches[0].identity.context = 1;
    assert!(destination.publish(&wrong_context, &candidate).is_err());
    assert_eq!(
        destination, before,
        "wrong context leaves destination unchanged"
    );

    let mut changed_term = candidate.clone();
    changed_term.batches[0].terms[0].gate.c1 += Fr::one();
    assert_eq!(
        destination.publish(&changed_term, &candidate).unwrap_err(),
        "source-owned MAX candidate mismatch"
    );
    assert_eq!(
        destination, before,
        "changed Gate leaves destination unchanged"
    );

    let mut changed_import = candidate.clone();
    let value = &mut changed_import.imports[0].cells[0].1;
    *value = Fr::one() - *value;
    assert_eq!(
        destination
            .publish(&changed_import, &candidate)
            .unwrap_err(),
        "source-owned MAX candidate mismatch"
    );
    assert_eq!(
        destination, before,
        "changed R import leaves destination unchanged"
    );

    let collision_cell = candidate.batches[0].writes[0].1;
    destination
        .cells
        .insert(x(OWNER, collision_cell), Fr::from(7u64));
    let collision_before = destination.clone();
    assert!(destination
        .publish(&candidate, &candidate)
        .unwrap_err()
        .contains("X collision"));
    assert_eq!(
        destination, collision_before,
        "collision leaves destination unchanged"
    );

    destination.cells.remove(&x(OWNER, collision_cell));
    let collision_row = candidate.batches[0].terms[0].row;
    destination.rows.insert(
        collision_row,
        Identity {
            owner: 9,
            context: 0,
            end: 11,
        },
    );
    let row_collision_before = destination.clone();
    assert!(destination
        .publish(&candidate, &candidate)
        .unwrap_err()
        .contains("ROW collision"));
    assert_eq!(destination, row_collision_before, "ROW collision is atomic");
    destination.rows.remove(&collision_row);
    destination
        .publish(&candidate, &candidate)
        .expect("single atomic publication");
    let published = destination.clone();
    assert!(destination.publish(&candidate, &candidate).is_err());
    assert_eq!(destination, published, "repeat publication is atomic");
    println!(
        "C135_NOFRAME_MAX_PREFLIGHT_PASS owner={OWNER} max_contexts=2 max_terms=5380 max_rows=2244 max_local_values=1346 foreign_r_reads=448 proof=false"
    );
}

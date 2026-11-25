//! Fixed H4 analytical verifier plan. The producer-only reference still has caps.
//! The work-tree coefficients never enumerate historical slots.
use crate::{
    gkr::{self, GkrProof, InputClaim},
    sparse::{self, Circuit, Term},
    transcript::Transcript,
    work_tree_composition as composition, work_tree_fixed_hash as fixed,
    work_tree_layout as layout, work_tree_leaf_hash as leaf, work_tree_wiring as wiring,
    work_tree_work as work,
};
use ark_bn254::Fr;
use ark_ff::{One, Zero};

const HEADER_TERMS: usize = 211_721;
const TREE_TERMS: usize = 126_573;
const ROW_BITS: usize = 21;
const INPUT_BITS: usize = 22;
const LOCAL_ROW_BITS: usize = 16;
const BASE_FAMILIES: usize = 20;
const DAA_BITS: usize = 224;

pub(crate) struct Plan {
    retained: Circuit,
    retained_hash: String,
    inventory_hash: String,
    engine: &'static fixed::Engine,
    topology: wiring::Topology,
    fixed: fixed::FixedProfile,
    leaf: leaf::Boundary,
    work: work::Boundary,
    work_wires: Vec<usize>,
}

impl Plan {
    pub(crate) fn new(root: [u8; 32], total: [u8; 28]) -> Result<Self, String> {
        let baseline = layout::shared_baseline()?;
        let joined = crate::header_compact_links::build(None)?;
        let old = &joined.base.base.base.boundary;
        if old.input_len != layout::WIDTH
            || old.row_count != 1 << 19
            || old.terms.len() != baseline.inventory.old_boundary_terms
            || layout::hash_terms(&old.terms) != baseline.inventory.old_boundary_blake2b256
        {
            return Err("analytical retained boundary baseline drift".into());
        }
        let mut retired = vec![false; old.row_count];
        for item in &baseline.inventory.retired {
            if item.last_row >= retired.len() {
                return Err("retirement outside local rows".into());
            }
            for row in item.first_row..=item.last_row {
                if retired[row] {
                    return Err("retirement overlap".into());
                }
                retired[row] = true;
            }
        }
        let typed = baseline
            .inventory
            .retired
            .iter()
            .find(|item| item.role == "typed_endpoints")
            .ok_or("missing typed endpoint retirement")?;
        let aux = typed
            .first_row
            .checked_sub(layout::ENDPOINT_BASE - leaf::AUX)
            .ok_or("auxiliary retirement underflow")?;
        for bit in 0..leaf::AUX_BITS {
            let row = aux + bit;
            if row >= retired.len() || retired[row] {
                return Err("auxiliary retirement overlap".into());
            }
            let start = old.terms.partition_point(|t| t.row < row);
            let end = old.terms.partition_point(|t| t.row <= row);
            let expected = Term {
                row,
                gate: gkr::Gate {
                    left: leaf::AUX + bit,
                    right: 0,
                    c0: Fr::zero(),
                    c1: Fr::one(),
                    c2: Fr::zero(),
                    c3: Fr::zero(),
                },
            };
            if old.terms.get(start..end) != Some(std::slice::from_ref(&expected)) {
                return Err("auxiliary retirement gate drift".into());
            }
            retired[row] = true;
        }
        let removed = old.terms.iter().filter(|t| retired[t.row]).count();
        if removed != baseline.inventory.checked_retired_terms + leaf::AUX_BITS
            || removed != 209_632
        {
            return Err("retained boundary removal count drift".into());
        }
        let retained = Circuit {
            input_len: old.input_len,
            row_count: old.row_count,
            terms: old
                .terms
                .iter()
                .filter(|t| !retired[t.row])
                .cloned()
                .collect(),
        };
        if retained.terms.len() != HEADER_TERMS {
            return Err("retained header term count drift".into());
        }
        sparse::validate(&retained, 2).map_err(|e| e.to_string())?;
        let topology = wiring::Topology::new(baseline, 4, root)?;
        let engine = fixed::engine()?;
        let fixed = fixed::FixedProfile::new(4, root)?;
        let leaf = leaf::compile(engine, leaf::LeafProfile::new(4, root)?)?;
        let work = work::compile(baseline, work::WorkProfile::new(4, root, total)?)?;
        if wiring::full_roster_shape(&topology)? != (LOCAL_ROW_BITS, 5, ROW_BITS, INPUT_BITS)
            || topology.families.len() + 6 != BASE_FAMILIES
            || baseline.endpoints.work.len() != DAA_BITS
        {
            return Err("analytical H4 roster shape drift".into());
        }
        let work_wires = baseline.endpoints.work.clone();
        if work_wires.iter().any(|&wire| wire >= layout::WIDTH) {
            return Err("work endpoint outside slot".into());
        }
        Ok(Self {
            retained_hash: layout::hash_terms(&retained.terms),
            retained,
            inventory_hash: baseline.inventory.descriptor_blake2b256.clone(),
            engine,
            topology,
            fixed,
            leaf,
            work,
            work_wires,
        })
    }

    fn daa_term(&self, group: usize, bit: usize) -> Term {
        let wire = self.work_wires[bit];
        let mut gate = gkr::Gate {
            left: wire,
            right: 0,
            c0: Fr::zero(),
            c1: Fr::one(),
            c2: Fr::zero(),
            c3: Fr::zero(),
        };
        if group == 0 {
            let value = if bit < 64 {
                (composition::GENESIS_DIFFICULTY >> bit) & 1
            } else {
                0
            };
            gate.c0 = -Fr::from(value);
        } else {
            gate.left = group * layout::WIDTH + wire;
            gate.right = (group - 1) * layout::WIDTH + wire;
            gate.c2 = -Fr::one();
        }
        Term {
            row: ((BASE_FAMILIES + group) << LOCAL_ROW_BITS) + bit,
            gate,
        }
    }
    fn bind_headers(&self, t: &mut Transcript) {
        t.append_bytes(b"sparse-profile", b"h4-retained-header-template-compact-v3");
        t.append_bytes(b"retained-template-hash", self.retained_hash.as_bytes());
        t.append_bytes(b"retained-inventory-hash", self.inventory_hash.as_bytes());
        t.append_bytes(
            b"retained-contract-hash",
            layout::CONTRACT_SHA256.as_bytes(),
        );
        for (label, value) in [
            (b"input-bits".as_slice(), INPUT_BITS),
            (b"row-bits".as_slice(), ROW_BITS),
            (b"header-copy-log".as_slice(), 2),
            (b"header-template-terms".as_slice(), HEADER_TERMS),
        ] {
            t.append_u64(label, value as u64);
        }
    }
    fn bind_tree(&self, t: &mut Transcript) {
        wiring::bind_full_roster(
            &self.topology,
            &self.fixed,
            &self.leaf.profile,
            self.work.profile(),
            t,
        );
        t.append_bytes(b"early-daa-profile", b"h4-fixed-children-2-3-4-tagged-v3");
        t.append_bytes(
            b"early-daa-order",
            b"genesis;inherit-height3;inherit-height4",
        );
        t.append_u64(b"early-daa-first-tag", BASE_FAMILIES as u64);
        t.append_u64(b"early-daa-tag-count", 3);
        t.append_u64(b"early-daa-rows-per-tag", DAA_BITS as u64);
        t.append_u64(b"final-tree-family-count", (BASE_FAMILIES + 3) as u64);
        t.append_u64(b"final-tree-term-count", TREE_TERMS as u64);
        t.append_u64(
            b"early-daa-initial-numeric",
            composition::GENESIS_DIFFICULTY,
        );
    }
    fn tree_coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
        if r.len() != ROW_BITS || u.len() != INPUT_BITS || v.len() != INPUT_BITS {
            return Err("analytical H4 point dimension".into());
        }
        let mut out = wiring::full_roster_coefficients(
            &self.topology,
            self.engine,
            &self.fixed,
            &self.leaf,
            &self.work,
            r,
            u,
            v,
        )?;
        for group in 0..3 {
            for bit in 0..DAA_BITS {
                let term = self.daa_term(group, bit);
                let gate = term.gate;
                let weight = wiring::eq_index(r, term.row)
                    * wiring::eq_index(u, gate.left)
                    * wiring::eq_index(v, gate.right);
                for (sum, c) in out.iter_mut().zip([gate.c0, gate.c1, gate.c2, gate.c3]) {
                    *sum += weight * c;
                }
            }
        }
        Ok(out)
    }
    #[cfg(test)]
    pub(crate) fn tree_coefficients_for_test(
        &self,
        r: &[Fr],
        u: &[Fr],
        v: &[Fr],
    ) -> Result<[Fr; 4], String> {
        self.tree_coefficients(r, u, v)
    }
    #[cfg(test)]
    pub(crate) fn tree_family_term_counts_for_test(&self) -> Result<Vec<usize>, String> {
        let mut counts = Vec::with_capacity(BASE_FAMILIES + 3);
        for family in &self.topology.families {
            counts.push(family.count(&self.topology.descriptor)?.terms as usize);
        }

        let fixed_terms = fixed::count(self.engine, &self.fixed)?.total_boundary_terms;
        counts.push(
            usize::try_from(fixed_terms).map_err(|_| "H4 fixed family term count overflow")?,
        );

        let leaf_report = leaf::count(self.engine, &self.leaf)?;
        let leaf_terms = leaf_report["new_boundary_terms"]
            .as_u64()
            .ok_or("H4 leaf family term count missing")?;
        counts.push(
            usize::try_from(leaf_terms).map_err(|_| "H4 leaf family term count overflow")?,
        );

        let work_report = work::count(&self.work)?;
        let work_terms = work_report["new_local_terms"]
            .as_u64()
            .ok_or("H4 work family term count missing")?;
        counts.push(
            usize::try_from(work_terms).map_err(|_| "H4 work family term count overflow")?,
        );

        for family in self.work.links() {
            counts.push(family.count(&self.work.profile().tree)?.terms as usize);
        }
        counts.extend([DAA_BITS; 3]);
        if counts.len() != BASE_FAMILIES + 3 {
            return Err("H4 source family census length drift".into());
        }
        Ok(counts)
    }
    /// Bounded producer/reference only; the consumer never calls this emitter.
    pub(crate) fn tree_circuit(&self) -> Result<Circuit, String> {
        let mut circuit = wiring::full_roster_circuit(
            &self.topology,
            self.engine,
            &self.fixed,
            &self.leaf,
            &self.work,
        )?;
        for group in 0..3 {
            for bit in 0..DAA_BITS {
                circuit.terms.push(self.daa_term(group, bit));
            }
        }
        if circuit.terms.len() != TREE_TERMS {
            return Err("H4 tagged tree term count drift".into());
        }
        sparse::validate(&circuit, 0).map_err(|e| e.to_string())?;
        Ok(circuit)
    }
    pub(crate) fn prove_headers(
        &self,
        input: &[Fr],
        t: &mut Transcript,
    ) -> Result<(GkrProof, InputClaim), String> {
        sparse::prove_with_binding(&self.retained, input, 2, t, |t| self.bind_headers(t))
            .map_err(|e| e.to_string())
    }
    pub(crate) fn prove_tree(
        &self,
        input: &[Fr],
        t: &mut Transcript,
    ) -> Result<(GkrProof, InputClaim), String> {
        sparse::prove_with_binding(&self.tree_circuit()?, input, 0, t, |t| self.bind_tree(t))
            .map_err(|e| e.to_string())
    }
    pub(crate) fn decode(&self, bytes: &[u8]) -> Result<GkrProof, String> {
        gkr::decode_dimensions(&[INPUT_BITS], bytes)
    }
    pub(crate) fn verify_headers(
        &self,
        proof: &GkrProof,
        t: &mut Transcript,
    ) -> Result<InputClaim, String> {
        let shape = sparse::validate(&self.retained, 2).map_err(|e| e.to_string())?;
        gkr::verify_with_wiring(
            &[INPUT_BITS],
            1 << ROW_BITS,
            proof,
            t,
            |t| self.bind_headers(t),
            |_, r, u, v| sparse::wiring(&self.retained, &shape, r, u, v),
        )
        .map_err(|e| e.to_string())
    }
    pub(crate) fn verify_tree(
        &self,
        proof: &GkrProof,
        t: &mut Transcript,
    ) -> Result<InputClaim, String> {
        gkr::verify_with_wiring(
            &[INPUT_BITS],
            1 << ROW_BITS,
            proof,
            t,
            |t| self.bind_tree(t),
            |_, r, u, v| {
                self.tree_coefficients(r, u, v)
                    .map_err(|_| gkr::GkrError::PointDimension)
            },
        )
        .map_err(|e| e.to_string())
    }
    #[cfg(test)]
    pub(crate) fn verify_tree_mutant(
        &self,
        proof: &GkrProof,
        t: &mut Transcript,
        mutation: usize,
    ) -> Result<InputClaim, String> {
        if mutation > 2 {
            return Err("unknown wiring mutant".into());
        }
        gkr::verify_with_wiring(
            &[INPUT_BITS],
            1 << ROW_BITS,
            proof,
            t,
            |t| self.bind_tree(t),
            |_, r, u, v| {
                let mut out = if mutation == 0 {
                    wiring::full_roster_coefficients_with_tag(
                        &self.topology,
                        self.engine,
                        &self.fixed,
                        &self.leaf,
                        &self.work,
                        r,
                        u,
                        v,
                        |index| match index {
                            0 => 1,
                            1 => 0,
                            _ => index,
                        },
                    )
                } else {
                    wiring::full_roster_coefficients(
                        &self.topology,
                        self.engine,
                        &self.fixed,
                        &self.leaf,
                        &self.work,
                        r,
                        u,
                        v,
                    )
                }
                .map_err(|_| gkr::GkrError::PointDimension)?;
                for group in 0..3 {
                    for bit in 0..DAA_BITS {
                        if mutation == 1 && group == 2 {
                            continue;
                        }
                        let term = self.daa_term(group, bit);
                        let gate = term.gate;
                        let row_weight = if mutation == 2 {
                            // Deliberately omit the eight zero padding row bits.
                            wiring::eq_index(&r[..8], bit)
                                * wiring::eq_index(&r[LOCAL_ROW_BITS..], BASE_FAMILIES + group)
                        } else {
                            wiring::eq_index(r, term.row)
                        };
                        let weight = row_weight
                            * wiring::eq_index(u, gate.left)
                            * wiring::eq_index(v, gate.right);
                        for (sum, c) in out.iter_mut().zip([gate.c0, gate.c1, gate.c2, gate.c3]) {
                            *sum += weight * c;
                        }
                    }
                }
                Ok(out)
            },
        )
        .map_err(|e| e.to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::Field;
    use std::collections::{BTreeMap, BTreeSet};

    // Compare complete row polynomials independent of row numbering, sign and
    // duplicate copies. A term-only or honest-witness comparison is weaker.
    fn equations(circuit: &Circuit) -> BTreeSet<Vec<u8>> {
        let mut rows = BTreeMap::<usize, BTreeMap<(u8, usize, usize), Fr>>::new();
        for term in &circuit.terms {
            let g = &term.gate;
            let row = rows.entry(term.row).or_default();
            for (key, value) in [
                ((0, 0, 0), g.c0),
                ((1, g.left, 0), g.c1),
                ((1, g.right, 0), g.c2),
                ((2, g.left.min(g.right), g.left.max(g.right)), g.c3),
            ] {
                if !value.is_zero() {
                    *row.entry(key).or_insert(Fr::zero()) += value;
                }
            }
        }
        rows.into_values()
            .filter_map(|mut row| {
                row.retain(|_, c| !c.is_zero());
                let inverse = row.first_key_value()?.1.inverse().unwrap();
                let mut bytes = Vec::new();
                for ((degree, a, b), coefficient) in row {
                    bytes.push(degree);
                    bytes.extend_from_slice(&(a as u64).to_le_bytes());
                    bytes.extend_from_slice(&(b as u64).to_le_bytes());
                    bytes.extend(crate::pcs::encode(&(coefficient * inverse)).unwrap());
                }
                Some(bytes)
            })
            .collect()
    }
    #[test]
    fn h4_analytic_preserves_every_v2_zero_row_and_all_terminal_coefficients() {
        let plan = Plan::new([0x5a; 32], [0; 28]).unwrap();
        let old = composition::h4_early_daa([0x5a; 32], [0; 28]).unwrap();
        let prefix_len = 4 * HEADER_TERMS;
        for slot in 0..4 {
            for (index, term) in plan.retained.terms.iter().enumerate() {
                let mut copy = term.clone();
                copy.row += slot * plan.retained.row_count;
                copy.gate.left += slot * layout::WIDTH;
                copy.gate.right += slot * layout::WIDTH;
                assert_eq!(old.circuit.terms[slot * HEADER_TERMS + index], copy);
            }
        }
        let old_suffix = Circuit {
            input_len: old.circuit.input_len,
            row_count: old.circuit.row_count,
            terms: old.circuit.terms[prefix_len..].to_vec(),
        };
        assert_eq!(old_suffix.terms.len(), 121_453);
        let tree = plan.tree_circuit().unwrap();
        let original_equations = equations(&old_suffix);
        let split_equations = equations(&tree);
        assert_eq!(
            original_equations, split_equations,
            "split/tagged/duplicate equations drifted from v2"
        );
        let tree_shape = sparse::validate(&tree, 0).unwrap();
        let header_shape = sparse::validate(&plan.retained, 2).unwrap();
        let header_literal = Circuit {
            input_len: 1 << INPUT_BITS,
            row_count: 1 << ROW_BITS,
            terms: old.circuit.terms[..prefix_len].to_vec(),
        };
        let header_literal_shape = sparse::validate(&header_literal, 0).unwrap();
        let point = |bits, seed: u64| {
            (0..bits)
                .map(|i| Fr::from(seed + 37 * (i as u64 + 1)))
                .collect::<Vec<_>>()
        };
        for seed in [5, 43, 97] {
            let r = point(ROW_BITS, seed);
            let u = point(INPUT_BITS, seed + 101);
            let v = point(INPUT_BITS, seed + 211);
            assert_eq!(
                plan.tree_coefficients(&r, &u, &v).unwrap(),
                sparse::wiring(&tree, &tree_shape, &r, &u, &v).unwrap()
            );
            assert_eq!(
                sparse::wiring(&plan.retained, &header_shape, &r, &u, &v).unwrap(),
                sparse::wiring(&header_literal, &header_literal_shape, &r, &u, &v).unwrap(),
                "header triple copy factor drift"
            );
        }
        println!("h4_analytic_zero_rows equations={} retained_terms={} tree_terms={} input_bits=22 row_bits=21 result=pass",
            original_equations.len(),HEADER_TERMS,TREE_TERMS);
    }
}

// Test-only access to the ordinary complete binder for an omitted-Term prover.
// No caller-selected relation is exposed by the operational Tree verifier.
#[cfg(test)]
impl Plan {
    pub(crate) fn bind_tree_for_test(&self, transcript: &mut Transcript) -> Result<(), String> {
        if transcript.challenges() != 0 {
            return Err("H4 tree test binding after challenge".into());
        }
        self.bind_tree(transcript);
        if transcript.challenges() != 0 {
            return Err("H4 tree binder derived a challenge".into());
        }
        Ok(())
    }
}

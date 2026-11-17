//! Bounded four-header M2 authentication under one common commitment.
//! This consumer binds expected public IDs, header compression, selected DAA
//! and point membership. It does not prove ancestry, PoW or complete history.
use crate::{
    core_pool,
    gkr::{self, GkrProof, InputClaim},
    header_height_layout::HeaderHeightLayout,
    pcs, point_membership, segment_points, segment_relation,
    short_common_owner::{self as common, Plan as Common},
    sparse::{self, Circuit, Shape, Term},
    transcript::Transcript,
    verifier_key, work_tree_fixed_hash as fixed, work_tree_layout as layout,
};
use ark_bn254::Fr;
use ark_ff::{One, Zero};

pub(crate) const DOMAIN: &[u8] = b"selected-m2-four-header-authentication-v1";
pub(crate) const INPUT_BITS: [usize; 4] = [22, 22, 15, 22];
pub(crate) const ROW_BITS: [usize; 4] = [22, 23, 16, 11];
pub(crate) const ROLES: [&[u8]; 4] = [
    b"eight-header-cores",
    b"selected-m2-relations",
    b"encoded-points",
    b"expected-header-ids-and-heights",
];
pub(crate) const CORE_BANKS: [usize; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
const WIDTH: usize = 1 << 20;

#[derive(Clone)]
pub(crate) struct Artifact {
    pub(crate) commitment: Vec<u8>,
    pub(crate) roles: [Vec<u8>; 4],
    pub(crate) openings: [Vec<u8>; 4],
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum Reject {
    Shape,
    Commitment,
    Role(usize),
    Opening(usize),
}

/// The expected IDs are supplied independently of the proof. All maps and
/// dimensions are code-owned; construction never accepts producer wiring.
pub(crate) struct Plan {
    common: Common,
    engine: &'static fixed::Engine,
    core_shape: Shape,
    core_hash: String,
    points: point_membership::Compiled,
    point_hash: String,
    ids: [[u8; 32]; 4],
    id_circuit: Circuit,
    id_shape: Shape,
    id_hash: String,
    height_hash: String,
}

impl Plan {
    pub(crate) fn new(ids: [[u8; 32]; 4]) -> Result<Self, String> {
        // Reuse exact core/inventory admission, never its eleven-family wiring.
        let admitted_core = core_pool::Plan::new(2)?;
        if admitted_core.input_log() != 22 || admitted_core.row_log() != 23 {
            return Err("canonical core admission geometry drift".into());
        }
        let engine = fixed::engine()?;
        let core_shape = sparse::validate(&engine.core, 0).map_err(|e| e.to_string())?;
        if core_shape.input_bits != 16
            || core_shape.row_bits != 17
            || engine.core.terms.len() != 172_480
            || layout::CORE_OFFSETS[..8] != CORE_BANKS.map(|bank| bank * layout::CORE)
        {
            return Err("eight-header core map drift".into());
        }
        let common = Common::new()?;
        let points = point_membership::build()?;
        if points.circuit.input_len != 8192
            || points.circuit.row_count != 16384
            || points.circuit.terms.len() != 288_158
            || segment_points::POINT_OFFSET != 786_432
            || segment_relation::DIGEST_OFFSET != 655_372
        {
            return Err("selected authentication source geometry drift".into());
        }
        let mut terms: Vec<Term> = (0..4)
            .flat_map(|copy| {
                (0..256).map(move |bit| Term {
                    row: 256 * copy + bit,
                    gate: gkr::Gate {
                        left: WIDTH * copy + segment_relation::DIGEST_OFFSET + bit,
                        right: 0,
                        c0: -Fr::from(((ids[copy][bit / 8] >> (bit % 8)) & 1) as u64),
                        c1: Fr::one(),
                        c2: Fr::zero(),
                        c3: Fr::zero(),
                    },
                })
            })
            .collect();
        let heights = HeaderHeightLayout::compile(3073, 12)?;
        for (copy, logical) in common::LOGICAL_SLOTS.iter().copied().enumerate() {
            let logical_input = logical
                .checked_mul(WIDTH)
                .ok_or("height logical input overflow")?;
            let logical_row = logical
                .checked_mul(32)
                .ok_or("height logical row overflow")?;
            let count = heights.visit_slot_terms(logical as u64, |mut term| {
                let row = term
                    .row
                    .checked_sub(logical_row)
                    .filter(|row| *row < 32)
                    .ok_or("selected height row escapes logical owner")?;
                let left = term
                    .gate
                    .left
                    .checked_sub(logical_input)
                    .filter(|wire| *wire < WIDTH)
                    .ok_or("selected height left escapes logical owner")?;
                let right = term
                    .gate
                    .right
                    .checked_sub(logical_input)
                    .filter(|wire| *wire < WIDTH)
                    .ok_or("selected height right escapes logical owner")?;
                term.row = 1024 + copy * 32 + row;
                term.gate.left = copy * WIDTH + left;
                term.gate.right = copy * WIDTH + right;
                terms.push(term);
                Ok(())
            })?;
            if count != 32 {
                return Err("selected height term inventory drift".into());
            }
        }
        if terms.len() != 1152 {
            return Err("selected ID/height inventory drift".into());
        }
        let id_circuit = Circuit {
            input_len: 1 << 22,
            row_count: 2048,
            terms,
        };
        let id_shape = sparse::validate(&id_circuit, 0).map_err(|e| e.to_string())?;
        let core_hash = engine.base.inventory.core.terms_blake2b256.clone();
        let point_hash = layout::hash_terms(&points.circuit.terms);
        let id_hash = layout::hash_terms(&id_circuit.terms);
        let height_hash = heights.fingerprint().to_owned();
        Ok(Self {
            common,
            engine,
            core_shape,
            core_hash,
            points,
            point_hash,
            ids,
            id_circuit,
            id_shape,
            id_hash,
            height_hash,
        })
    }

    pub(crate) fn common(&self) -> &Common {
        &self.common
    }
    pub(crate) fn core(&self) -> &Circuit {
        &self.engine.core
    }
    pub(crate) fn points(&self) -> &point_membership::Compiled {
        &self.points
    }
    pub(crate) fn ids(&self) -> &Circuit {
        &self.id_circuit
    }

    pub(crate) fn transcript(
        &self,
        role: usize,
        setup_id: &[u8; 32],
        commitment: &[u8],
    ) -> Result<Transcript, Reject> {
        if role >= 4 {
            return Err(Reject::Shape);
        }
        let mut t = Transcript::new(DOMAIN);
        t.append_u64(b"role-count", 4);
        t.append_u64(b"common-input-bits", 22);
        for i in 0..4 {
            t.append_u64(b"role-index-in-roster", i as u64);
            t.append_bytes(b"role-in-roster", ROLES[i]);
            t.append_u64(b"input-bits-in-roster", INPUT_BITS[i] as u64);
            t.append_u64(b"row-bits-in-roster", ROW_BITS[i] as u64);
            t.append_u64(b"physical-copy", i as u64);
            t.append_u64(b"logical-slot", common::LOGICAL_SLOTS[i] as u64);
            t.append_bytes(b"expected-header-id", &self.ids[i]);
        }
        t.append_bytes(b"core-template", self.core_hash.as_bytes());
        t.append_bytes(
            b"core-coordinate-rule",
            b"local16-bank4-copy2-row17-copy2-family3",
        );
        for bank in CORE_BANKS {
            t.append_u64(b"header-core-bank", bank as u64);
        }
        t.append_bytes(b"point-template", self.point_hash.as_bytes());
        t.append_bytes(b"point-embedding", b"low13-bank7-0000011-copy2-lsb");
        t.append_u64(b"point-bank-offset", segment_points::POINT_OFFSET as u64);
        t.append_bytes(b"id-template", self.id_hash.as_bytes());
        t.append_bytes(b"height-source-template", self.height_hash.as_bytes());
        t.append_bytes(
            b"height-projection",
            b"row1024-copy2-bit5-both-endpoints-copy-local20",
        );
        t.append_u64(b"id-bit-offset", segment_relation::DIGEST_OFFSET as u64);
        t.append_bytes(
            b"id-coordinate-rule",
            b"row-copy2-bit8-left-copy2-local20-rightGLOBAL0-lsb",
        );
        self.common.bind(&mut t, setup_id, commitment);
        t.append_u64(b"selected-role-index", role as u64);
        t.append_bytes(b"selected-role-domain", ROLES[role]);
        Ok(t)
    }

    pub(crate) fn bind_role(
        &self,
        role: usize,
        t: &mut Transcript,
        setup_id: &[u8; 32],
        commitment: &[u8],
    ) {
        match role {
            0 => t.append_bytes(b"relation", b"eight-header-core-tensor-v1"),
            1 => self.common.bind(t, setup_id, commitment),
            // sparse::prove/verify own the point circuit binding.
            2 => unreachable!("point binding belongs to sparse"),
            3 => t.append_bytes(
                b"relation",
                b"four-public-header-digest-and-height-equalities-v1",
            ),
            _ => unreachable!("fixed role roster"),
        }
    }

    pub(crate) fn core_coefficients(
        &self,
        r: &[Fr],
        u: &[Fr],
        v: &[Fr],
    ) -> Result<[Fr; 4], gkr::GkrError> {
        if r.len() != 22 || u.len() != 22 || v.len() != 22 {
            return Err(gkr::GkrError::PointDimension);
        }
        let mut coefficients =
            sparse::wiring(self.core(), &self.core_shape, &r[..17], &u[..16], &v[..16])?;
        let copy =
            r[17..19]
                .iter()
                .zip(&u[20..22])
                .zip(&v[20..22])
                .fold(Fr::one(), |acc, ((a, b), c)| {
                    acc * ((Fr::one() - a) * (Fr::one() - b) * (Fr::one() - c) + *a * b * c)
                });
        let banks = CORE_BANKS
            .iter()
            .map(|bank| {
                common::eq(&r[19..22], *bank)
                    * common::eq(&u[16..20], *bank)
                    * common::eq(&v[16..20], *bank)
            })
            .sum::<Fr>();
        for value in &mut coefficients {
            *value *= copy * banks;
        }
        Ok(coefficients)
    }

    pub(crate) fn verify_role(
        &self,
        role: usize,
        proof: &GkrProof,
        setup_id: &[u8; 32],
        commitment: &[u8],
    ) -> Result<(InputClaim, Transcript), Reject> {
        let mut t = self.transcript(role, setup_id, commitment)?;
        let mut claim = match role {
            0 => gkr::verify_with_wiring(
                &[22],
                1 << 22,
                proof,
                &mut t,
                |t| self.bind_role(0, t, setup_id, commitment),
                |_, r, u, v| self.core_coefficients(r, u, v),
            ),
            1 => gkr::verify_with_wiring(
                &[22],
                1 << 23,
                proof,
                &mut t,
                |t| self.bind_role(1, t, setup_id, commitment),
                |_, r, u, v| {
                    self.common
                        .coefficients(r, u, v)
                        .map_err(|_| gkr::GkrError::PointDimension)
                },
            ),
            2 => sparse::verify(&self.points.circuit, 2, proof, &mut t),
            3 => gkr::verify_with_wiring(
                &[22],
                2048,
                proof,
                &mut t,
                |t| self.bind_role(3, t, setup_id, commitment),
                |_, r, u, v| sparse::wiring(&self.id_circuit, &self.id_shape, r, u, v),
            ),
            _ => return Err(Reject::Shape),
        }
        .map_err(|_| Reject::Role(role))?;
        if role == 2 {
            claim.point =
                segment_points::embed(3, 2, &claim.point).map_err(|_| Reject::Role(role))?;
        }
        if claim.point.len() != 22 {
            return Err(Reject::Role(role));
        }
        Ok((claim, t))
    }

    /// Accept only when every fixed role and its continued PCS opening pass.
    pub(crate) fn verify(
        &self,
        artifact: &Artifact,
        key: &verifier_key::AdmittedVerifierKey,
    ) -> Result<[InputClaim; 4], Reject> {
        if key.log_n() != 22
            || artifact
                .roles
                .iter()
                .enumerate()
                .any(|(i, bytes)| bytes.len() != (7 * INPUT_BITS[i] + 3) * 32)
        {
            return Err(Reject::Shape);
        }
        let commitment =
            pcs::decode_commitment(&artifact.commitment).map_err(|_| Reject::Commitment)?;
        let mut claims = Vec::with_capacity(4);
        for role in 0..4 {
            let proof = gkr::decode_dimensions(&[INPUT_BITS[role]], &artifact.roles[role])
                .map_err(|_| Reject::Role(role))?;
            let (claim, mut t) = self.verify_role(role, &proof, key.id(), &artifact.commitment)?;
            let opening = pcs::decode_proof(&artifact.openings[role], 22)
                .map_err(|_| Reject::Opening(role))?;
            pcs::verify_admitted(
                commitment.clone(),
                claim.value,
                &claim.point,
                &opening,
                key,
                &mut t,
            )
            .map_err(|_| Reject::Opening(role))?;
            claims.push(claim);
        }
        claims.try_into().map_err(|_| Reject::Shape)
    }
}

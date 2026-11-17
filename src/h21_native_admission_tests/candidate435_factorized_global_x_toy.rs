//! Four-owner factorization falsifier. The owner/local split is a toy; H21 is not used.

use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
    time::{SystemTime, UNIX_EPOCH},
};

use ark_bn254::Fr;
use ark_ff::{One, Zero};

use crate::{
    gkr::{self, Gate, GkrProof, InputClaim, LayerProof},
    opening_batch::{self, Claim, Statement},
    packed::{self, PackedFile, PackedFileWriter},
    pcs::{self, Setup},
    sparse::{self, Circuit, Term},
    transcript::Transcript,
};

const OWNERS: usize = 4;
const LOCAL: usize = 8;
const LOG_N: usize = 5;
const INPUT_LEN: usize = OWNERS * LOCAL;
const DOMAIN: &[u8] = b"c435-factorized-global-x-toy-gkr-v1";
const PROFILE: &[u8] = b"c435-two-row-domains-one-global-x-v1";
static NEXT_FILE: AtomicU64 = AtomicU64::new(0);

#[derive(Clone, Copy)]
struct RowDomain {
    role: &'static [u8],
    owner: usize,
    stride: usize,
}
const WORK: RowDomain = RowDomain {
    role: b"Work",
    owner: 844_670,
    stride: 2_048,
};
const CROSS: RowDomain = RowDomain {
    role: b"Cross",
    owner: 844_671,
    stride: 8_192,
};

struct TemporaryPacked {
    path: PathBuf,
    source: Option<PackedFile>,
}
impl Drop for TemporaryPacked {
    fn drop(&mut self) {
        self.source.take();
        let _ = fs::remove_file(&self.path);
    }
}
fn toy_bits() -> [u8; 4] {
    [0b0000_0011, 0b1000_0000, 0b0000_0011, 0]
}
fn temporary_packed() -> TemporaryPacked {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("C435 monotone toy filename epoch")
        .as_nanos();
    let path = std::env::temp_dir().join(format!(
        "c435-global-x-{}-{nonce}-{}.bits",
        std::process::id(),
        NEXT_FILE.fetch_add(1, Ordering::Relaxed)
    ));
    let mut writer = PackedFileWriter::create_new(&path, LOG_N).expect("C435 fresh tiny X");
    writer
        .write_bytes(&toy_bits())
        .expect("C435 exact toy bits");
    let source = writer.finish().expect("C435 immutable tiny X");
    TemporaryPacked {
        path,
        source: Some(source),
    }
}
fn gate(left: usize, right: usize, c0: i64, c1: i64, c2: i64, c3: i64) -> Gate {
    let scalar = |n: i64| {
        if n < 0 {
            -Fr::from(n.unsigned_abs())
        } else {
            Fr::from(n as u64)
        }
    };
    Gate {
        left,
        right,
        c0: scalar(c0),
        c1: scalar(c1),
        c2: scalar(c2),
        c3: scalar(c3),
    }
}
fn work_circuit() -> Circuit {
    Circuit {
        input_len: INPUT_LEN,
        row_count: 2,
        terms: vec![
            Term {
                row: 0,
                gate: gate(0, 0, -1, 1, 0, 0),
            },
            Term {
                row: 1,
                gate: gate(1, 15, 0, 0, 0, 1),
            },
            Term {
                row: 1,
                gate: gate(0, 0, 0, -1, 0, 0),
            },
        ],
    }
}
fn cross_circuit() -> Circuit {
    Circuit {
        input_len: INPUT_LEN,
        row_count: 4,
        terms: vec![
            Term {
                row: 0,
                gate: gate(16, 16, -1, 1, 0, 0),
            },
            Term {
                row: 3,
                gate: gate(17, 0, 0, 0, 0, 1),
            },
            Term {
                row: 3,
                gate: gate(16, 16, 0, -1, 0, 0),
            },
        ],
    }
}
fn rows_from_source(source: &PackedFile) -> Vec<Vec<Fr>> {
    (0..OWNERS)
        .map(|owner| {
            source
                .read_copy(LOCAL, owner)
                .expect("C435 same immutable packed X owner row")
        })
        .collect()
}
fn admit_toy_padding(rows: &[Vec<Fr>]) -> Result<(), &'static str> {
    if rows.len() != OWNERS
        || rows.iter().any(|row| row.len() != LOCAL)
        || rows[3].iter().any(|value| !value.is_zero())
    {
        return Err("C435 toy padded owner is nonzero or malformed");
    }
    Ok(())
}
fn bind_role(
    circuit: &Circuit,
    domain: RowDomain,
    setup_id: &[u8; 32],
    commitment: &dory_pcs::backends::arkworks::ArkGT,
    transcript: &mut Transcript,
) {
    transcript.append_bytes(b"c435-profile", PROFILE);
    transcript.append_bytes(b"c435-role", domain.role);
    transcript.append_u64(b"c435-row-owner", domain.owner as u64);
    transcript.append_u64(b"c435-row-stride", domain.stride as u64);
    transcript.append_u64(b"c435-local-row-count", circuit.row_count as u64);
    transcript.append_u64(b"c435-global-owner-count", OWNERS as u64);
    transcript.append_u64(b"c435-local-width", LOCAL as u64);
    transcript.append_bytes(b"c435-setup-id", setup_id);
    transcript.append_bytes(
        b"c435-common-commitment",
        &pcs::encode_commitment(commitment).expect("C435 canonical commitment"),
    );
    sparse::bind(circuit, 0, transcript);
}
fn dense_prove(
    circuit: &Circuit,
    domain: RowDomain,
    input: &[Fr],
    setup: &Setup,
    commitment: &dory_pcs::backends::arkworks::ArkGT,
) -> (GkrProof, InputClaim) {
    let mut transcript = Transcript::new(DOMAIN);
    sparse::prove_with_binding(circuit, input, 0, &mut transcript, |t| {
        bind_role(circuit, domain, &setup.id, commitment, t)
    })
    .expect("C435 dense GKR reference")
}
fn verify_role(
    circuit: &Circuit,
    domain: RowDomain,
    setup_id: &[u8; 32],
    commitment: &dory_pcs::backends::arkworks::ArkGT,
    proof: &GkrProof,
) -> Result<InputClaim, gkr::GkrError> {
    let shape = sparse::validate(circuit, 0)?;
    let mut transcript = Transcript::new(DOMAIN);
    gkr::verify_with_wiring(
        &[shape.input_bits],
        shape.row_count,
        proof,
        &mut transcript,
        |t| bind_role(circuit, domain, setup_id, commitment, t),
        |layer, r, u, v| {
            if layer == 0 {
                sparse::wiring(circuit, &shape, r, u, v)
            } else {
                Err(gkr::GkrError::PointDimension)
            }
        },
    )
}

// The low three coordinates name a cell within an owner; the high two name
// the owner.  This deliberately never constructs a 32-entry equality table.
fn factored_eq(point: &[Fr], wire: usize) -> Fr {
    assert_eq!(point.len(), LOG_N);
    assert!(wire < INPUT_LEN);
    let owner = wire / LOCAL;
    let local = wire % LOCAL;
    let mut weight = Fr::one();
    for (bit, coordinate) in point[..3].iter().enumerate() {
        weight *= if (local >> bit) & 1 == 1 {
            *coordinate
        } else {
            Fr::one() - coordinate
        };
    }
    for (bit, coordinate) in point[3..].iter().enumerate() {
        weight *= if (owner >> bit) & 1 == 1 {
            *coordinate
        } else {
            Fr::one() - coordinate
        };
    }
    weight
}

fn factored_wiring(circuit: &Circuit, r: &[Fr], u: &[Fr], v: &[Fr]) -> [Fr; 4] {
    let row_weights = gkr::eq_weights(r);
    let mut out = [Fr::zero(); 4];
    for term in &circuit.terms {
        let g = &term.gate;
        let weight = row_weights[term.row] * factored_eq(u, g.left) * factored_eq(v, g.right);
        out[0] += weight * g.c0;
        out[1] += weight * g.c1;
        out[2] += weight * g.c2;
        out[3] += weight * g.c3;
    }
    out
}

fn initial_ab(circuit: &Circuit, rows: &[Vec<Fr>], r: &[Fr]) -> (Vec<Vec<Fr>>, Vec<Vec<Fr>>) {
    assert_eq!(rows.len(), OWNERS);
    let row_weights = gkr::eq_weights(r);
    let mut a = vec![vec![Fr::zero(); LOCAL]; OWNERS];
    let mut b = a.clone();
    for term in &circuit.terms {
        let g = &term.gate;
        let left_owner = g.left / LOCAL;
        let right_owner = g.right / LOCAL;
        let right = rows[right_owner][g.right % LOCAL];
        let weight = row_weights[term.row];
        a[left_owner][g.left % LOCAL] += weight * (g.c1 + g.c3 * right);
        b[left_owner][g.left % LOCAL] += weight * (g.c0 + g.c2 * right);
    }
    (a, b)
}

fn right_cd(circuit: &Circuit, r: &[Fr], u: &[Fr], left_value: Fr) -> (Vec<Vec<Fr>>, Vec<Vec<Fr>>) {
    let row_weights = gkr::eq_weights(r);
    let mut c = vec![vec![Fr::zero(); LOCAL]; OWNERS];
    let mut d = c.clone();
    for term in &circuit.terms {
        let g = &term.gate;
        let weight = row_weights[term.row] * factored_eq(u, g.left);
        let owner = g.right / LOCAL;
        c[owner][g.right % LOCAL] += weight * (g.c2 + g.c3 * left_value);
        d[owner][g.right % LOCAL] += weight * (g.c0 + g.c1 * left_value);
    }
    (c, d)
}

fn factorized_phase(
    mut a: Vec<Vec<Fr>>,
    mut b: Vec<Vec<Fr>>,
    source_rows: &[Vec<Fr>],
    claim: &mut Fr,
    rounds: &mut Vec<Vec<Fr>>,
    transcript: &mut Transcript,
    omit_work_sibling: bool,
) -> Result<(Vec<Fr>, Fr), gkr::GkrError> {
    let mut x = source_rows.to_vec();
    if omit_work_sibling {
        x[1][7] = Fr::zero();
    }
    let mut point = Vec::with_capacity(LOG_N);
    for _ in 0..3 {
        let mut polynomial = vec![Fr::zero(); 3];
        for owner in 0..OWNERS {
            let next = gkr::quadratic_message(&a[owner], &b[owner], &x[owner]);
            for degree in 0..3 {
                polynomial[degree] += next[degree];
            }
        }
        if polynomial[0] + gkr::eval_polynomial(&polynomial, Fr::one()) != *claim {
            return Err(gkr::GkrError::SumcheckIdentity);
        }
        gkr::append_polynomial(transcript, b"gkr-sumcheck-polynomial", &polynomial);
        let challenge = transcript.challenge_scalar(b"gkr-sumcheck-challenge");
        *claim = gkr::eval_polynomial(&polynomial, challenge);
        for owner in 0..OWNERS {
            gkr::fold(&mut a[owner], challenge);
            gkr::fold(&mut b[owner], challenge);
            gkr::fold(&mut x[owner], challenge);
        }
        rounds.push(polynomial);
        point.push(challenge);
    }
    let mut a_high = a.iter().map(|row| row[0]).collect::<Vec<_>>();
    let mut b_high = b.iter().map(|row| row[0]).collect::<Vec<_>>();
    let mut x_high = x.iter().map(|row| row[0]).collect::<Vec<_>>();
    for _ in 0..2 {
        let polynomial = gkr::quadratic_message(&a_high, &b_high, &x_high);
        if polynomial[0] + gkr::eval_polynomial(&polynomial, Fr::one()) != *claim {
            return Err(gkr::GkrError::SumcheckIdentity);
        }
        gkr::append_polynomial(transcript, b"gkr-sumcheck-polynomial", &polynomial);
        let challenge = transcript.challenge_scalar(b"gkr-sumcheck-challenge");
        *claim = gkr::eval_polynomial(&polynomial, challenge);
        gkr::fold(&mut a_high, challenge);
        gkr::fold(&mut b_high, challenge);
        gkr::fold(&mut x_high, challenge);
        rounds.push(polynomial);
        point.push(challenge);
    }
    Ok((point, x_high[0]))
}

// Evaluate X on the affine line u+t(v-u) without a global 32-cell table:
// four degree-three local polynomials, followed by the two owner coordinates.
fn factorized_line_polynomial(rows: &[Vec<Fr>], u: &[Fr], v: &[Fr]) -> Vec<Fr> {
    assert_eq!(rows.len(), OWNERS);
    assert_eq!(u.len(), LOG_N);
    assert_eq!(v.len(), LOG_N);
    let mut polynomials = rows
        .iter()
        .map(|row| {
            assert_eq!(row.len(), LOCAL);
            gkr::line_polynomial(row, &u[..3], &v[..3])
        })
        .collect::<Vec<_>>();
    for owner_bit in 0..2 {
        let z0 = u[3 + owner_bit];
        let z1 = v[3 + owner_bit] - z0;
        let mut next = Vec::with_capacity(polynomials.len() / 2);
        for pair in polynomials.chunks_exact(2) {
            let left = &pair[0];
            let right = &pair[1];
            assert_eq!(left.len(), right.len());
            let mut combined = vec![Fr::zero(); left.len() + 1];
            for degree in 0..left.len() {
                let delta = right[degree] - left[degree];
                combined[degree] += left[degree] + z0 * delta;
                combined[degree + 1] += z1 * delta;
            }
            next.push(combined);
        }
        polynomials = next;
    }
    assert_eq!(polynomials.len(), 1);
    assert_eq!(polynomials[0].len(), LOG_N + 1);
    polynomials.remove(0)
}

fn factorized_prove_role(
    circuit: &Circuit,
    domain: RowDomain,
    source: &PackedFile,
    setup: &Setup,
    commitment: &dory_pcs::backends::arkworks::ArkGT,
) -> Result<(GkrProof, InputClaim, Vec<Fr>, Vec<Fr>), gkr::GkrError> {
    let shape = sparse::validate(circuit, 0)?;
    let rows = rows_from_source(source);
    admit_toy_padding(&rows).expect("C435 toy source padding admission");
    let mut residual = vec![Fr::zero(); circuit.row_count];
    for term in &circuit.terms {
        let g = &term.gate;
        let left = rows[g.left / LOCAL][g.left % LOCAL];
        let right = rows[g.right / LOCAL][g.right % LOCAL];
        residual[term.row] += g.c0 + g.c1 * left + g.c2 * right + g.c3 * left * right;
    }
    if residual.iter().any(|value| !value.is_zero()) {
        return Err(gkr::GkrError::NonzeroOutput);
    }
    let mut transcript = Transcript::new(DOMAIN);
    bind_role(circuit, domain, &setup.id, commitment, &mut transcript);
    let r = gkr::output_point(shape.row_count, &mut transcript);
    gkr::append_usize(&mut transcript, b"gkr-layer-index", 0);
    let (a, b) = initial_ab(circuit, &rows, &r);
    let mut claim = Fr::zero();
    let mut rounds = Vec::with_capacity(2 * LOG_N);
    let (u, left_value) =
        factorized_phase(a, b, &rows, &mut claim, &mut rounds, &mut transcript, false)?;
    let (c, d) = right_cd(circuit, &r, &u, left_value);
    let (v, right_value) =
        factorized_phase(c, d, &rows, &mut claim, &mut rounds, &mut transcript, false)?;
    let coefficients = factored_wiring(circuit, &r, &u, &v);
    if coefficients[0]
        + coefficients[1] * left_value
        + coefficients[2] * right_value
        + coefficients[3] * left_value * right_value
        != claim
    {
        return Err(gkr::GkrError::TerminalExpression);
    }
    let line_coefficients = factorized_line_polynomial(&rows, &u, &v);
    transcript.append_scalar(b"gkr-left-value", &left_value);
    transcript.append_scalar(b"gkr-right-value", &right_value);
    gkr::append_polynomial(&mut transcript, b"gkr-line-polynomial", &line_coefficients);
    let line_challenge = transcript.challenge_scalar(b"gkr-line-challenge");
    let point = gkr::line_point(&u, &v, line_challenge);
    let value = gkr::eval_polynomial(&line_coefficients, line_challenge);
    let proof = GkrProof {
        layers: vec![LayerProof {
            rounds,
            left_value,
            right_value,
            line_coefficients,
        }],
    };
    Ok((proof, InputClaim { point, value }, u, v))
}

fn replay_round_challenges(
    circuit: &Circuit,
    domain: RowDomain,
    setup: &Setup,
    commitment: &dory_pcs::backends::arkworks::ArkGT,
    proof: &GkrProof,
) -> (Vec<Fr>, Vec<Fr>) {
    let mut transcript = Transcript::new(DOMAIN);
    bind_role(circuit, domain, &setup.id, commitment, &mut transcript);
    let _r = gkr::output_point(circuit.row_count, &mut transcript);
    gkr::append_usize(&mut transcript, b"gkr-layer-index", 0);
    let rounds = &proof.layers[0].rounds;
    assert_eq!(rounds.len(), 2 * LOG_N);
    let mut points = Vec::with_capacity(2 * LOG_N);
    for polynomial in rounds {
        gkr::append_polynomial(&mut transcript, b"gkr-sumcheck-polynomial", polynomial);
        points.push(transcript.challenge_scalar(b"gkr-sumcheck-challenge"));
    }
    (points[..LOG_N].to_vec(), points[LOG_N..].to_vec())
}

fn repeated_claims(work: &InputClaim, cross: &InputClaim) -> [Claim; opening_batch::CLAIMS] {
    let w = Claim {
        point: work.point.clone(),
        value: work.value,
    };
    let c = Claim {
        point: cross.point.clone(),
        value: cross.value,
    };
    [
        w.clone(),
        c.clone(),
        w.clone(),
        c.clone(),
        w.clone(),
        c.clone(),
        w,
    ]
}

#[test]
fn c435_four_owner_factorized_u_v_matches_dense_common_x() {
    let packed = temporary_packed();
    let source = packed.source.as_ref().expect("C435 packed source");
    let rows = rows_from_source(source);
    admit_toy_padding(&rows).expect("C435 admitted toy padding");
    let dense_input = rows.iter().flatten().copied().collect::<Vec<_>>();
    assert_eq!(dense_input.len(), INPUT_LEN);
    assert_eq!(
        dense_input[15],
        Fr::one(),
        "A-inactive Work sibling has nonzero X"
    );
    let setup = pcs::generate_setup(LOG_N).expect("C435 tiny common Dory setup");
    let committed = packed::commit(source, &setup).expect("C435 one packed X commitment");
    let dense_commitment =
        pcs::commit(&dense_input, &setup).expect("C435 dense reference commitment");
    assert_eq!(
        pcs::encode_commitment(&committed.commitment).unwrap(),
        pcs::encode_commitment(&dense_commitment.commitment).unwrap()
    );

    let work = work_circuit();
    let cross = cross_circuit();
    assert_ne!(WORK.stride, CROSS.stride);
    assert_ne!(WORK.owner, CROSS.owner);
    let mut role_results = Vec::new();
    for (circuit, domain) in [(&work, WORK), (&cross, CROSS)] {
        let (dense_proof, dense_claim) =
            dense_prove(circuit, domain, &dense_input, &setup, &committed.commitment);
        let (factorized_proof, factorized_claim, u, v) =
            factorized_prove_role(circuit, domain, source, &setup, &committed.commitment)
                .expect("C435 factored GKR prover");
        assert_eq!(factorized_proof.layers.len(), 1);
        assert_eq!(factorized_proof.layers[0].rounds.len(), 2 * LOG_N);
        assert_eq!(
            factorized_proof.layers[0].rounds, dense_proof.layers[0].rounds,
            "every U/V polynomial must match the independent dense path"
        );
        assert_eq!(
            factorized_proof.layers[0].left_value,
            dense_proof.layers[0].left_value
        );
        assert_eq!(
            factorized_proof.layers[0].right_value,
            dense_proof.layers[0].right_value
        );
        assert_eq!(
            factorized_proof.layers[0].line_coefficients,
            dense_proof.layers[0].line_coefficients
        );
        let (dense_u, dense_v) =
            replay_round_challenges(circuit, domain, &setup, &committed.commitment, &dense_proof);
        assert_eq!(u, dense_u, "all U challenges match");
        assert_eq!(v, dense_v, "all V challenges match");
        let shape = sparse::validate(circuit, 0).unwrap();
        let mut transcript = Transcript::new(DOMAIN);
        bind_role(
            circuit,
            domain,
            &setup.id,
            &committed.commitment,
            &mut transcript,
        );
        let r = gkr::output_point(circuit.row_count, &mut transcript);
        let coefficients = factored_wiring(circuit, &r, &u, &v);
        assert_eq!(
            coefficients,
            sparse::wiring(circuit, &shape, &r, &u, &v).unwrap()
        );
        assert_eq!(factorized_claim, dense_claim, "same terminal InputClaim");
        assert_eq!(
            gkr::encode_proof(&factorized_proof).unwrap(),
            gkr::encode_proof(&dense_proof).unwrap(),
            "same GKR proof bytes"
        );
        assert_eq!(
            verify_role(
                circuit,
                domain,
                &setup.id,
                &committed.commitment,
                &factorized_proof
            )
            .expect("C435 GKR verifier"),
            factorized_claim
        );
        assert_eq!(
            source.evaluate(&factorized_claim.point).unwrap(),
            factorized_claim.value
        );
        role_results.push((dense_claim, factorized_claim, factorized_proof));
    }
    let (work_dense, work_factored, work_proof) = &role_results[0];
    let (cross_dense, cross_factored, _cross_proof) = &role_results[1];
    let dense_statement = Statement {
        log_n: LOG_N,
        setup_id: setup.id,
        commitment: committed.commitment,
        corpus_id: Some([0x35; 32]),
        claims: repeated_claims(work_dense, cross_dense),
    };
    let factored_statement = Statement {
        log_n: LOG_N,
        setup_id: setup.id,
        commitment: committed.commitment,
        corpus_id: Some([0x35; 32]),
        claims: repeated_claims(work_factored, cross_factored),
    };
    assert_eq!(dense_statement.log_n, factored_statement.log_n);
    assert_eq!(dense_statement.setup_id, factored_statement.setup_id);
    assert_eq!(
        pcs::encode_commitment(&dense_statement.commitment).unwrap(),
        pcs::encode_commitment(&factored_statement.commitment).unwrap()
    );
    assert_eq!(dense_statement.corpus_id, factored_statement.corpus_id);
    assert_eq!(dense_statement.claims, factored_statement.claims);
    let (dense_opening, _, _) = opening_batch::prove(source, &committed, &setup, &dense_statement)
        .expect("C435 dense shared-X opening");
    let (factored_opening, _, _) =
        opening_batch::prove(source, &committed, &setup, &factored_statement)
            .expect("C435 factored shared-X opening");
    assert_eq!(
        opening_batch::encode_proof(&dense_opening, LOG_N).unwrap(),
        opening_batch::encode_proof(&factored_opening, LOG_N).unwrap(),
        "same shared Dory opening bytes"
    );
    opening_batch::verify(&factored_statement, &setup, &factored_opening)
        .expect("C435 one Dory opening binds both role claims");

    // Remove X[15] only from the folded input after constructing authentic
    // Work A/B. Local rounds should agree, while the owner-high round changes.
    let mut transcript = Transcript::new(DOMAIN);
    bind_role(
        &work,
        WORK,
        &setup.id,
        &committed.commitment,
        &mut transcript,
    );
    let r = gkr::output_point(work.row_count, &mut transcript);
    gkr::append_usize(&mut transcript, b"gkr-layer-index", 0);
    let (a, b) = initial_ab(&work, &rows, &r);
    let mut faulty_claim = Fr::zero();
    let mut faulty_rounds = Vec::new();
    factorized_phase(
        a,
        b,
        &rows,
        &mut faulty_claim,
        &mut faulty_rounds,
        &mut transcript,
        true,
    )
    .expect("C435 isolated sibling omission phase remains algebraically formed");
    assert_eq!(&faulty_rounds[..3], &work_proof.layers[0].rounds[..3]);
    assert_ne!(
        faulty_rounds[3], work_proof.layers[0].rounds[3],
        "high owner fold detects X of A-inactive sibling"
    );

    let (u, v) = replay_round_challenges(&work, WORK, &setup, &committed.commitment, work_proof);
    let mut wrong_owner_local = work.clone();
    let original = wrong_owner_local.terms[1].gate.left;
    wrong_owner_local.terms[1].gate.left = (original % OWNERS) * LOCAL + (original / OWNERS);
    assert_ne!(wrong_owner_local.terms[1].gate.left, original);
    assert_ne!(
        factored_wiring(&work, &r, &u, &v),
        factored_wiring(&wrong_owner_local, &r, &u, &v),
        "owner/local wire-index swap changes actual Work terminal wiring"
    );
    let mut wrong_padding = rows.clone();
    wrong_padding[3][7] = Fr::one();
    assert!(
        admit_toy_padding(&wrong_padding).is_err(),
        "toy-source padded owner must be rejected before proof"
    );
    let wrong_role = RowDomain {
        role: b"Cross",
        ..WORK
    };
    assert!(verify_role(
        &work,
        wrong_role,
        &setup.id,
        &committed.commitment,
        work_proof
    )
    .is_err());
    let wrong_stride = RowDomain {
        stride: CROSS.stride,
        ..WORK
    };
    assert!(verify_role(
        &work,
        wrong_stride,
        &setup.id,
        &committed.commitment,
        work_proof
    )
    .is_err());
    let alternate_commitment = pcs::commit(&vec![Fr::zero(); INPUT_LEN], &setup)
        .expect("C435 alternate commitment")
        .commitment;
    assert!(verify_role(&work, WORK, &setup.id, &alternate_commitment, work_proof).is_err());
    let mut one_sided = factored_statement.clone();
    one_sided.commitment = alternate_commitment;
    assert!(opening_batch::verify(&one_sided, &setup, &factored_opening).is_err());
    println!("C435_FACTORIZED_GLOBAL_X_TOY_PASS owners=4 local=8 roles=2 u_v_rounds=10 sibling_x_rejected=true toy=true proof=false client=false");
}

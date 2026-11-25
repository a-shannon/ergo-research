//! Tiny Work/Cross composition falsifier: separate ROW domains, one X and one
//! Dory commitment. This proves only the toy composition, not H21 admission.

use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
    time::{SystemTime, UNIX_EPOCH},
};

use ark_bn254::Fr;
use ark_ff::{One, Zero};

use crate::{
    gkr::{self, Gate, GkrProof, InputClaim},
    opening_batch::{self, Claim, Statement},
    packed::{self, PackedFile, PackedFileWriter},
    pcs::{self, Setup},
    sparse::{self, Circuit, Term},
    transcript::Transcript,
};

const LOG_N: usize = 5;
const INPUT_LEN: usize = 1 << LOG_N;
const WORK_OWNER: usize = 844_670;
const WORK_STRIDE: usize = 2_048;
const CROSS_OWNER: usize = 844_671;
const CROSS_STRIDE: usize = 8_192;
const ROLE_DOMAIN: &[u8] = b"candidate155-work-cross-row-domain-v1";

static NEXT_FILE: AtomicU64 = AtomicU64::new(0);

#[derive(Clone, Copy)]
struct RowDomain {
    role: &'static [u8],
    owner: usize,
    stride: usize,
}

const WORK: RowDomain = RowDomain {
    role: b"Work",
    owner: WORK_OWNER,
    stride: WORK_STRIDE,
};
const CROSS: RowDomain = RowDomain {
    role: b"Cross",
    owner: CROSS_OWNER,
    stride: CROSS_STRIDE,
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

fn temporary_packed() -> TemporaryPacked {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock after epoch")
        .as_nanos();
    let path = std::env::temp_dir().join(format!(
        "candidate155-common-x-{}-{nonce}-{}.bits",
        std::process::id(),
        NEXT_FILE.fetch_add(1, Ordering::Relaxed),
    ));
    let mut writer = PackedFileWriter::create_new(&path, LOG_N).expect("create tiny packed X");
    writer
        .write_bytes(&[0b0011_1111, 0, 0, 0])
        .expect("write tiny packed X");
    let source = writer.finish().expect("finish tiny packed X");
    TemporaryPacked {
        path,
        source: Some(source),
    }
}

fn work_circuit() -> Circuit {
    Circuit {
        input_len: INPUT_LEN,
        row_count: 2,
        terms: vec![
            Term {
                row: 0,
                gate: Gate {
                    left: 0,
                    right: 0,
                    c0: -Fr::one(),
                    c1: Fr::one(),
                    c2: Fr::zero(),
                    c3: Fr::zero(),
                },
            },
            Term {
                row: 1,
                gate: Gate {
                    left: 1,
                    right: 0,
                    c0: Fr::zero(),
                    c1: Fr::one(),
                    c2: Fr::zero(),
                    c3: Fr::zero(),
                },
            },
            Term {
                row: 1,
                gate: Gate {
                    left: 2,
                    right: 0,
                    c0: Fr::zero(),
                    c1: -Fr::one(),
                    c2: Fr::zero(),
                    c3: Fr::zero(),
                },
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
                gate: Gate {
                    left: 3,
                    right: 0,
                    c0: -Fr::one(),
                    c1: Fr::one(),
                    c2: Fr::zero(),
                    c3: Fr::zero(),
                },
            },
            Term {
                row: 3,
                gate: Gate {
                    left: 4,
                    right: 0,
                    c0: Fr::zero(),
                    c1: Fr::one(),
                    c2: Fr::zero(),
                    c3: Fr::zero(),
                },
            },
            Term {
                row: 3,
                gate: Gate {
                    left: 5,
                    right: 0,
                    c0: Fr::zero(),
                    c1: -Fr::one(),
                    c2: Fr::zero(),
                    c3: Fr::zero(),
                },
            },
        ],
    }
}

fn bind_role(
    circuit: &Circuit,
    domain: RowDomain,
    setup_id: &[u8; 32],
    commitment: &dory_pcs::backends::arkworks::ArkGT,
    transcript: &mut Transcript,
) {
    transcript.append_bytes(b"candidate155-profile", ROLE_DOMAIN);
    transcript.append_bytes(b"candidate155-role", domain.role);
    transcript.append_u64(b"candidate155-row-owner", domain.owner as u64);
    transcript.append_u64(b"candidate155-row-stride", domain.stride as u64);
    transcript.append_u64(b"candidate155-local-row-count", circuit.row_count as u64);
    transcript.append_bytes(b"candidate155-setup-id", setup_id);
    transcript.append_bytes(
        b"candidate155-common-commitment",
        &pcs::encode_commitment(commitment).expect("canonical shared commitment"),
    );
    sparse::bind(circuit, 0, transcript);
}

fn prove_role(
    circuit: &Circuit,
    domain: RowDomain,
    input: &[Fr],
    setup: &Setup,
    commitment: &dory_pcs::backends::arkworks::ArkGT,
) -> (GkrProof, InputClaim) {
    let mut transcript = Transcript::new(b"candidate155-two-domain-gkr-v1");
    sparse::prove_with_binding(circuit, input, 0, &mut transcript, |transcript| {
        bind_role(circuit, domain, &setup.id, commitment, transcript)
    })
    .expect("toy role GKR prove")
}

fn verify_role(
    circuit: &Circuit,
    domain: RowDomain,
    setup_id: &[u8; 32],
    commitment: &dory_pcs::backends::arkworks::ArkGT,
    proof: &GkrProof,
) -> Result<InputClaim, gkr::GkrError> {
    let shape = sparse::validate(circuit, 0)?;
    let mut transcript = Transcript::new(b"candidate155-two-domain-gkr-v1");
    gkr::verify_with_wiring(
        &[shape.input_bits],
        shape.row_count,
        proof,
        &mut transcript,
        |transcript| bind_role(circuit, domain, setup_id, commitment, transcript),
        |layer, r, u, v| {
            if layer == 0 {
                sparse::wiring(circuit, &shape, r, u, v)
            } else {
                Err(gkr::GkrError::PointDimension)
            }
        },
    )
}

fn repeated_claims(work: &InputClaim, cross: &InputClaim) -> [Claim; opening_batch::CLAIMS] {
    [
        Claim {
            point: work.point.clone(),
            value: work.value,
        },
        Claim {
            point: cross.point.clone(),
            value: cross.value,
        },
        Claim {
            point: work.point.clone(),
            value: work.value,
        },
        Claim {
            point: cross.point.clone(),
            value: cross.value,
        },
        Claim {
            point: work.point.clone(),
            value: work.value,
        },
        Claim {
            point: cross.point.clone(),
            value: cross.value,
        },
        Claim {
            point: work.point.clone(),
            value: work.value,
        },
    ]
}

#[test]
fn two_tagged_row_domains_share_one_x_commitment_with_isolated_negatives() {
    let mut packed = temporary_packed();
    let source = packed.source.as_ref().expect("live packed X");
    let setup = pcs::generate_setup(LOG_N).expect("toy Dory setup");
    let committed = packed::commit(source, &setup).expect("one commitment for shared X");

    let work = work_circuit();
    let cross = cross_circuit();
    assert_ne!(
        work.row_count, cross.row_count,
        "role ROW domains have distinct extents"
    );
    assert_eq!(
        (WORK.owner * WORK.stride + 1, CROSS.owner * CROSS.stride + 3),
        (1_729_884_161, 6_919_544_835),
        "toy local rows are tagged by the c154 Work/Cross namespace geometry",
    );
    assert_ne!(WORK.stride, CROSS.stride);

    let input = (0..INPUT_LEN)
        .map(|index| {
            if index < 6 && (0b0011_1111u8 >> index) & 1 != 0 {
                Fr::one()
            } else {
                Fr::zero()
            }
        })
        .collect::<Vec<_>>();
    let (work_proof, work_claim) = prove_role(&work, WORK, &input, &setup, &committed.commitment);
    let (cross_proof, cross_claim) =
        prove_role(&cross, CROSS, &input, &setup, &committed.commitment);
    assert_ne!(
        work_claim.point, cross_claim.point,
        "role-bound GKR claims differ"
    );
    assert_ne!(
        work_claim.value, cross_claim.value,
        "toy role claims are distinct"
    );
    assert_eq!(
        source.evaluate(&work_claim.point).unwrap(),
        work_claim.value
    );
    assert_eq!(
        source.evaluate(&cross_claim.point).unwrap(),
        cross_claim.value
    );

    assert_eq!(
        verify_role(&work, WORK, &setup.id, &committed.commitment, &work_proof)
            .expect("Work GKR verifies"),
        work_claim,
    );
    assert_eq!(
        verify_role(
            &cross,
            CROSS,
            &setup.id,
            &committed.commitment,
            &cross_proof
        )
        .expect("Cross GKR verifies"),
        cross_claim,
    );

    let statement = Statement {
        log_n: LOG_N,
        setup_id: setup.id,
        commitment: committed.commitment,
        corpus_id: Some([0x15; 32]),
        claims: repeated_claims(&work_claim, &cross_claim),
    };
    let (opening, _, _) = opening_batch::prove(source, &committed, &setup, &statement)
        .expect("one Dory opening batch for both role claims");
    opening_batch::verify(&statement, &setup, &opening).expect("shared-X Dory opening verifies");

    assert!(
        verify_role(&cross, CROSS, &setup.id, &committed.commitment, &work_proof).is_err(),
        "swapping role GKR proofs must reject",
    );
    let changed_role = RowDomain {
        role: b"Cross",
        ..WORK
    };
    assert!(
        verify_role(
            &work,
            changed_role,
            &setup.id,
            &committed.commitment,
            &work_proof
        )
        .is_err(),
        "changing only the role tag must reject the old GKR proof",
    );
    let changed_stride = RowDomain {
        stride: CROSS_STRIDE,
        ..WORK
    };
    assert!(
        verify_role(
            &work,
            changed_stride,
            &setup.id,
            &committed.commitment,
            &work_proof
        )
        .is_err(),
        "changing only the ROW namespace stride must reject the old GKR proof",
    );
    let alternate_commitment = pcs::commit(&vec![Fr::zero(); INPUT_LEN], &setup)
        .expect("alternate toy commitment")
        .commitment;
    assert!(
        verify_role(&work, WORK, &setup.id, &alternate_commitment, &work_proof).is_err(),
        "GKR proof must bind the common X commitment",
    );

    let mut changed = statement.clone();
    changed.claims.swap(0, 1);
    assert!(
        opening_batch::verify(&changed, &setup, &opening).is_err(),
        "claim-role swap rejects"
    );
    let mut changed = statement.clone();
    changed.claims[1].point[0] += Fr::one();
    assert!(
        opening_batch::verify(&changed, &setup, &opening).is_err(),
        "Cross point mutation rejects"
    );
    let mut changed = statement.clone();
    changed.claims[1].value += Fr::one();
    assert!(
        opening_batch::verify(&changed, &setup, &opening).is_err(),
        "Cross value mutation rejects"
    );
    let mut changed = statement.clone();
    changed.commitment = alternate_commitment;
    assert!(
        opening_batch::verify(&changed, &setup, &opening).is_err(),
        "opening-only C mutation rejects"
    );

    drop(opening);
    drop(committed);
    drop(setup);
    drop(packed);
}
